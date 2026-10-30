"""独立的天地图 WMTS 适配服务，仅使用 Python 标准库；使用方法详见 README.md。"""

from __future__ import annotations

import argparse
import hmac
import html
import json
import math
import os
import re
import struct
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


WMTS = "http://www.opengis.net/wmts/1.0"
OWS = "http://www.opengis.net/ows/1.1"
XLINK = "http://www.w3.org/1999/xlink"
NS = {"w": WMTS, "o": OWS}
LAYERS = {
    "vec": ("矢量底图", "image/png"),
    "cva": ("矢量中文注记", "image/png"),
    "img": ("影像底图", "image/jpeg"),
    "cia": ("影像中文注记", "image/png"),
    "ter": ("地形晕渲底图", "image/jpeg"),
    "cta": ("地形中文注记", "image/png"),
    "ibo": ("境界叠加层", "image/png"),
}
SERVICES = {f"{layer}_{grid}": layer for grid in ("w", "c") for layer in LAYERS}
PIXEL_METRES = 0.00028
METRES_PER_DEGREE = math.pi * 6378137.0 / 180.0
MERCATOR_HALF_WORLD = math.pi * 6378137.0
MERCATOR_MAX_LATITUDE = math.degrees(math.atan(math.sinh(math.pi)))
PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"

ET.register_namespace("", WMTS)
ET.register_namespace("ows", OWS)
ET.register_namespace("xlink", XLINK)


class BadRequest(Exception):
    """An unsupported client request."""


class UpstreamError(Exception):
    """A safe-to-display upstream failure without credential-bearing URLs."""


@dataclass(frozen=True)
class Capabilities:
    xml: bytes
    matrices: dict[str, tuple[int, int]]


def normalize_capabilities(source: bytes, service: str, endpoint: str) -> Capabilities:
    """Describe a supported global tile grid using WMTS reference pixels."""
    try:
        matrix_id = service.rsplit("_", 1)[1]
        geographic = matrix_id == "c"
        if b"<!DOCTYPE" in source.upper():
            raise ValueError("DOCTYPE is not supported")
        root = ET.fromstring(source)
        if root.tag != f"{{{WMTS}}}Capabilities":
            raise ValueError("not a WMTS capabilities document")
        contents = root.find("w:Contents", NS)
        layers = contents.findall("w:Layer", NS)
        sets = contents.findall("w:TileMatrixSet", NS)
        if len(layers) != 1 or len(sets) != 1:
            raise ValueError("expected one layer and one tile matrix set")
        layer, matrix_set = layers[0], sets[0]
        if layer.findtext("o:Identifier", namespaces=NS) != SERVICES[service]:
            raise ValueError("unexpected layer identifier")
        styles = layer.findall("w:Style", NS)
        if len(styles) != 1 or styles[0].findtext("o:Identifier", namespaces=NS) != "default":
            raise ValueError("unexpected upstream style")
        links = layer.findall("w:TileMatrixSetLink", NS)
        if len(links) != 1 or links[0].findtext("w:TileMatrixSet", namespaces=NS) != matrix_id:
            raise ValueError("unexpected layer matrix set link")
        if matrix_set.findtext("o:Identifier", namespaces=NS) != matrix_id:
            raise ValueError("unexpected tile matrix set")
        crs = matrix_set.find("o:SupportedCRS", NS)
        expected_crs = {"urn:ogc:def:crs:EPSG::4490"} if geographic else {
            "urn:ogc:def:crs:EPSG::900913", "urn:ogc:def:crs:EPSG::3857",
        }
        if crs.text not in expected_crs:
            raise ValueError("unexpected coordinate reference system")
        if not geographic:
            crs.text = "urn:ogc:def:crs:EPSG::3857"
        if matrix_set.find("w:WellKnownScaleSet", NS) is not None:
            raise ValueError("an advertised well-known scale set requires separate validation")
        for box in layer.findall("o:WGS84BoundingBox", NS):
            lower = list(map(float, box.findtext("o:LowerCorner", namespaces=NS).split()))
            upper = list(map(float, box.findtext("o:UpperCorner", namespaces=NS).split()))
            bounds = lower + upper
            expected = [-180.0, -90.0, 180.0, 90.0] if geographic else [
                -180.0, -MERCATOR_MAX_LATITUDE, 180.0, MERCATOR_MAX_LATITUDE,
            ]
            accepted = [expected]
            if not geographic:
                accepted.append([-MERCATOR_HALF_WORLD] * 2 + [MERCATOR_HALF_WORLD] * 2)
            if len(bounds) != 4 or not any(
                all(math.isclose(a, b, rel_tol=0, abs_tol=1e-6) for a, b in zip(bounds, candidate))
                for candidate in accepted
            ):
                raise ValueError("unexpected global extent")
            if not geographic:
                box.find("o:LowerCorner", NS).text = f"-180 {-MERCATOR_MAX_LATITUDE:.16g}"
                box.find("o:UpperCorner", NS).text = f"180 {MERCATOR_MAX_LATITUDE:.16g}"
        if not geographic:
            for box in layer.findall("o:BoundingBox", NS):
                bounds = list(map(float, (
                    box.findtext("o:LowerCorner", namespaces=NS) + " "
                    + box.findtext("o:UpperCorner", namespaces=NS)
                ).split()))
                expected = [-MERCATOR_HALF_WORLD] * 2 + [MERCATOR_HALF_WORLD] * 2
                if len(bounds) != 4 or not all(
                    math.isclose(a, b, rel_tol=0, abs_tol=1e-6) for a, b in zip(bounds, expected)
                ):
                    raise ValueError("unexpected projected extent")
                if box.get("crs") not in expected_crs | {None}:
                    raise ValueError("unexpected projected extent CRS")
                box.set("crs", crs.text)

        matrices = {}
        for matrix in matrix_set.findall("w:TileMatrix", NS):
            identifier = matrix.findtext("o:Identifier", namespaces=NS)
            level = int(identifier)
            if not 1 <= level <= 30 or str(level) != identifier or identifier in matrices:
                raise ValueError("unexpected tile matrix identifier")
            width = int(matrix.findtext("w:MatrixWidth", namespaces=NS))
            height = int(matrix.findtext("w:MatrixHeight", namespaces=NS))
            tile_width = int(matrix.findtext("w:TileWidth", namespaces=NS))
            tile_height = int(matrix.findtext("w:TileHeight", namespaces=NS))
            origin = list(map(float, matrix.findtext("w:TopLeftCorner", namespaces=NS).split()))
            # This extra annotation level copies geographic geometry into the projected grid.
            if (
                service == "cva_w" and level == 19 and (width, height) == (524288, 262144)
                and (tile_width, tile_height) == (256, 256) and origin == [90.0, -180.0]
            ):
                matrix_set.remove(matrix)
                for limits in layer.findall("w:TileMatrixSetLink/w:TileMatrixSetLimits", NS):
                    for limit in limits.findall("w:TileMatrixLimits", NS):
                        if limit.findtext("w:TileMatrix", namespaces=NS) == identifier:
                            limits.remove(limit)
                continue
            # cta_w declares Mercator but copies geographic origins and row counts at levels 1-18.
            if (
                service == "cta_w" and level <= 18
                and (width, height) == (2**level, 2 ** (level - 1))
                and (tile_width, tile_height) == (256, 256) and origin == [90.0, -180.0]
            ):
                height = width
                origin = [-MERCATOR_HALF_WORLD, MERCATOR_HALF_WORLD]
                matrix.find("w:MatrixHeight", NS).text = str(height)
            expected_height = 2 ** (level - 1) if geographic else 2**level
            if (width, height) != (2**level, expected_height):
                raise ValueError("the upstream matrix dimensions have changed")
            if (tile_width, tile_height) != (256, 256):
                raise ValueError("the upstream tile size has changed")
            if geographic:
                if origin != [90.0, -180.0]:
                    raise ValueError("the upstream geographic origin has changed")
            else:
                expected_origin = [-MERCATOR_HALF_WORLD, MERCATOR_HALF_WORLD]
                if len(origin) != 2 or not any(
                    all(math.isclose(a, b, rel_tol=0, abs_tol=1e-6) for a, b in zip(origin, candidate))
                    for candidate in (expected_origin, expected_origin[::-1])
                ):
                    raise ValueError("the upstream projected origin has changed")
                matrix.find("w:TopLeftCorner", NS).text = " ".join(format(v, ".16g") for v in expected_origin)
            span = 360.0 if geographic else 2 * MERCATOR_HALF_WORLD
            metres_per_unit = METRES_PER_DEGREE if geographic else 1.0
            resolution = span / (width * tile_width)
            scale = resolution * metres_per_unit / PIXEL_METRES
            legacy_scale = resolution * metres_per_unit * 96.0 / 0.0254
            element = matrix.find("w:ScaleDenominator", NS)
            advertised = float(element.text)
            if not any(math.isclose(advertised, value, rel_tol=1e-7) for value in (scale, legacy_scale)):
                raise ValueError("the upstream scale convention has changed")
            element.text = format(scale, ".16g")
            matrices[identifier] = (width, height)
        if not matrices:
            raise ValueError("no tile matrices")
        for resource in layer.findall("w:ResourceURL", NS):
            layer.remove(resource)
        formats = layer.findall("w:Format", NS)
        if not formats:
            raise ValueError("no tile format")
        formats[0].text = LAYERS[SERVICES[service]][1]
        for extra in formats[1:]:
            layer.remove(extra)

        identification = root.find("o:ServiceIdentification", NS)
        service_type = identification.find("o:ServiceType", NS)
        service_type.text = "OGC WMTS"
        old_operations = root.find("o:OperationsMetadata", NS)
        if old_operations is not None:
            root.remove(old_operations)
        operations = ET.Element(f"{{{OWS}}}OperationsMetadata")
        for name in ("GetCapabilities", "GetTile"):
            operation = ET.SubElement(operations, f"{{{OWS}}}Operation", name=name)
            dcp = ET.SubElement(operation, f"{{{OWS}}}DCP")
            http = ET.SubElement(dcp, f"{{{OWS}}}HTTP")
            get = ET.SubElement(http, f"{{{OWS}}}Get", {f"{{{XLINK}}}href": endpoint})
            constraint = ET.SubElement(get, f"{{{OWS}}}Constraint", name="GetEncoding")
            values = ET.SubElement(constraint, f"{{{OWS}}}AllowedValues")
            ET.SubElement(values, f"{{{OWS}}}Value").text = "KVP"
        root.insert(list(root).index(contents), operations)
        for link in root.findall("w:ServiceMetadataURL", NS):
            link.set(f"{{{XLINK}}}href", endpoint + "SERVICE=WMTS&REQUEST=GetCapabilities&VERSION=1.0.0")
        return Capabilities(ET.tostring(root, encoding="utf-8", xml_declaration=True), matrices)
    except (ET.ParseError, AttributeError, KeyError, TypeError, ValueError):
        raise UpstreamError("上游服务描述或瓦片格网不在已支持的范围内。") from None


def image_dimensions(data: bytes, image_format: str) -> tuple[int, int] | None:
    """Read PNG or JPEG dimensions without decoding or modifying the image."""
    if image_format == "image/png":
        if len(data) >= 33 and data.startswith(PNG_SIGNATURE) and data[12:16] == b"IHDR":
            return struct.unpack(">II", data[16:24])
        return None
    if not data.startswith(b"\xff\xd8"):
        return None
    position = 2
    while position < len(data):
        if data[position] != 0xFF:
            return None
        while position < len(data) and data[position] == 0xFF:
            position += 1
        if position >= len(data):
            return None
        marker = data[position]
        position += 1
        if marker in (0x00, 0xD8, 0xD9, 0xDA):
            return None
        if marker == 0x01 or 0xD0 <= marker <= 0xD7:
            continue
        if position + 2 > len(data):
            return None
        length = int.from_bytes(data[position:position + 2], "big")
        if length < 2 or position + length > len(data):
            return None
        if marker in (0xC0, 0xC1, 0xC2, 0xC3, 0xC5, 0xC6, 0xC7, 0xC9, 0xCA, 0xCB, 0xCD, 0xCE, 0xCF):
            if length < 8:
                return None
            height, width = struct.unpack(">HH", data[position + 3:position + 7])
            return width, height
        position += length
    return None


class NoRedirect(urllib.request.HTTPRedirectHandler):
    """Never forward credential-bearing requests to another endpoint."""

    def redirect_request(self, request, response, code, message, headers, new_url):
        raise UpstreamError("为保护服务 Key，不允许上游重定向。")


class Upstream:
    """Fetch only the supported official HTTPS endpoints."""

    def __init__(self, token: str):
        self.token = token
        self.opener = urllib.request.build_opener(NoRedirect())

    def get(self, service: str, parameters: dict[str, str]) -> bytes:
        if service not in SERVICES:
            raise BadRequest("Unsupported service.")
        query = urllib.parse.urlencode({**parameters, "tk": self.token})
        request = urllib.request.Request(
            f"https://t0.tianditu.gov.cn/{service}/wmts?{query}",
            headers={"User-Agent": "TianDiTu-WMTS-Adapter/1.0"},
        )
        limit = 2 * 1024 * 1024 if parameters["REQUEST"] == "GetCapabilities" else 8 * 1024 * 1024
        try:
            with self.opener.open(request, timeout=20) as response:
                data = response.read(limit + 1)
            if len(data) > limit:
                raise UpstreamError("上游响应超过允许的大小。")
            return data
        except urllib.error.HTTPError as error:
            error.close()
            raise UpstreamError(f"天地图返回 HTTP {error.code}；请检查服务 Key 与所选服务。") from None
        except (urllib.error.URLError, OSError):
            raise UpstreamError("无法连接天地图；请检查网络访问和 TLS 证书。") from None


class Adapter:
    """Normalize descriptors and forward original tile bytes."""

    def __init__(self, token: str, base_url: str, access_token: str = "", fetch=None):
        self.token = token
        self.base_url = base_url.rstrip("/")
        self.access_token = access_token
        self.fetch = fetch or Upstream(token).get
        self.cache: dict[str, tuple[float, Capabilities]] = {}
        self.lock = threading.Lock()

    def endpoint(self, service: str) -> str:
        query = urllib.parse.urlencode({"access_token": self.access_token}) + "&" if self.access_token else ""
        return f"{self.base_url}/{service}/wmts?{query}"

    def capabilities(self, service: str) -> Capabilities:
        with self.lock:
            cached = self.cache.get(service)
            if cached and time.monotonic() - cached[0] < 300:
                return cached[1]
            source = self.fetch(service, {"SERVICE": "WMTS", "REQUEST": "GetCapabilities", "VERSION": "1.0.0"})
            result = normalize_capabilities(source, service, self.endpoint(service))
            if self.token.encode() in result.xml:
                raise UpstreamError("上游服务描述意外包含访问凭证，已拒绝返回。")
            self.cache[service] = (time.monotonic(), result)
            return result

    def tile(self, service: str, parameters: dict[str, str]) -> bytes:
        required = ("LAYER", "STYLE", "TILEMATRIXSET", "FORMAT", "TILEMATRIX", "TILEROW", "TILECOL")
        if any(not parameters.get(key) for key in required):
            raise BadRequest("GetTile requires layer, style, format, matrix set, matrix, row and column.")
        matrix_set = service.rsplit("_", 1)[1]
        if (parameters["LAYER"], parameters["STYLE"], parameters["TILEMATRIXSET"]) != (SERVICES[service], "default", matrix_set):
            raise BadRequest("Unsupported layer, style or tile matrix set.")
        image_format = LAYERS[SERVICES[service]][1]
        if parameters["FORMAT"].lower() not in (image_format, "tiles"):
            raise BadRequest("Request the image format advertised by this layer.")
        matrix = parameters["TILEMATRIX"]
        row, column = parameters["TILEROW"], parameters["TILECOL"]
        if any(not re.fullmatch(r"[0-9]{1,10}", value) for value in (matrix, row, column)):
            raise BadRequest("Tile indices must be nonnegative decimal integers.")
        dimensions = self.capabilities(service).matrices.get(matrix)
        if dimensions is None or int(column) >= dimensions[0] or int(row) >= dimensions[1]:
            raise BadRequest("Tile indices are outside the advertised matrix.")
        upstream = {
            "SERVICE": "WMTS", "REQUEST": "GetTile", "VERSION": "1.0.0",
            **{key: parameters[key] for key in required}, "FORMAT": "tiles",
        }
        data = self.fetch(service, upstream)
        if image_dimensions(data, image_format) != (256, 256):
            raise UpstreamError(f"天地图未返回有效的 256×256 {image_format} 瓦片；请检查服务 Key 与所选服务。")
        return data


class WmtsServer(ThreadingHTTPServer):
    """A loopback listener intended to sit behind a TLS reverse proxy."""

    daemon_threads = True
    request_queue_size = 128

    def __init__(self, port: int, token: str, public_url: str = "", access_token: str = "", fetch=None):
        if not re.fullmatch(r"[A-Za-z0-9_-]{8,256}", token):
            raise ValueError("TIANDITU_TOKEN 必须是符合格式要求的天地图服务 Key。")
        if access_token and (len(access_token) < 24 or not access_token.isascii()):
            raise ValueError("WMTS_ACCESS_TOKEN 至少需要 24 个 ASCII 字符。")
        if public_url:
            parsed = urllib.parse.urlsplit(public_url)
            if (
                parsed.scheme != "https" or not parsed.hostname or parsed.username or parsed.password
                or parsed.path not in ("", "/") or parsed.query or parsed.fragment
            ):
                raise ValueError("PUBLIC_BASE_URL 必须是 HTTPS 域名地址，不能包含额外路径、查询参数或访问凭证。")
            if not access_token:
                raise ValueError("公网模式必须设置独立的客户端令牌 WMTS_ACCESS_TOKEN。")
        super().__init__(("127.0.0.1", port), Handler)
        local_url = f"http://127.0.0.1:{self.server_port}"
        self.adapter = Adapter(token, public_url or local_url, access_token, fetch)
        self.public_mode = bool(public_url)
        self.allowed_hosts = {f"127.0.0.1:{self.server_port}", f"localhost:{self.server_port}"}
        self.allowed_hosts.add(urllib.parse.urlsplit(self.adapter.base_url).netloc.casefold())


class Handler(BaseHTTPRequestHandler):
    """Handle only fixed WMTS KVP routes; never proxy arbitrary URLs."""

    protocol_version = "HTTP/1.1"
    server_version = "TianDiTu-WMTS-Adapter/1.0"

    def handle(self):
        try:
            super().handle()
        except (BrokenPipeError, ConnectionResetError):
            self.close_connection = True

    def setup(self):
        super().setup()
        self.connection.settimeout(30)

    def log_request(self, code="-", size="-"):
        path = self.path.partition("?")[0]
        routes = {"/", "/healthz"} | {f"/{service}/wmts" for service in SERVICES}
        route = path if path in routes else "/unknown"
        self.log_message("%s %s -> %s", self.command, route, code)

    def log_error(self, format, *args):
        self.log_message("请求被拒绝。")

    def _send(self, status: int, body: bytes, content_type: str):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        if self.server.public_mode:
            self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def _exception(self, status: int, code: str, message: str):
        root = ET.Element(f"{{{OWS}}}ExceptionReport", version="1.1.0")
        exception = ET.SubElement(root, f"{{{OWS}}}Exception", exceptionCode=code)
        ET.SubElement(exception, f"{{{OWS}}}ExceptionText").text = message
        self._send(status, ET.tostring(root, encoding="utf-8", xml_declaration=True), "application/xml; charset=utf-8")

    def do_GET(self):
        try:
            adapter = self.server.adapter
            if self.headers.get("Host", "").casefold() not in self.server.allowed_hosts:
                self._send(403, "不接受此 Host 地址。\n".encode(), "text/plain; charset=utf-8")
                return
            if not self.server.public_mode:
                origin = self.headers.get("Origin")
                own_origins = {f"http://{host}" for host in self.server.allowed_hosts}
                if (origin and origin not in own_origins) or self.headers.get("Sec-Fetch-Site") == "cross-site":
                    self._send(403, "本机模式不接受跨站请求。\n".encode(), "text/plain; charset=utf-8")
                    return
            url = urllib.parse.urlsplit(self.path)
            if url.scheme or url.netloc or len(url.query) > 4096:
                raise BadRequest("Invalid request target.")
            if url.path == "/healthz":
                self._send(200, json.dumps({"status": "ok", "services": list(SERVICES)}).encode(), "application/json")
                return
            pairs = urllib.parse.parse_qsl(url.query, keep_blank_values=True, max_num_fields=16)
            parameters = {}
            for key, value in pairs:
                key = key.upper()
                if key in parameters:
                    raise BadRequest("Duplicate query parameter.")
                parameters[key] = value
            supplied = parameters.pop("ACCESS_TOKEN", "")
            if adapter.access_token and not hmac.compare_digest(supplied.encode(), adapter.access_token.encode()):
                self._send(401, "需要有效的客户端令牌 access_token。\n".encode(), "text/plain; charset=utf-8")
                return
            if url.path == "/":
                links = []
                for service in SERVICES:
                    address = adapter.endpoint(service) + "SERVICE=WMTS&REQUEST=GetCapabilities&VERSION=1.0.0"
                    label, image_format = LAYERS[SERVICES[service]]
                    grid = "Web Mercator，EPSG:3857，矩阵集 w" if service.endswith("_w") else "CGCS2000，EPSG:4490，矩阵集 c"
                    links.append(f'<li><a href="{html.escape(address)}">{service}</a>：{label}，{grid}，{image_format}</li>')
                page = (
                    '<!doctype html><html lang="zh-CN"><head><meta charset="utf-8">'
                    "<title>天地图 WMTS 适配服务</title></head><body>"
                    "<h1>天地图 WMTS 适配服务</h1><h2>使用方法</h2>"
                    "<ol><li>客户端使用 Web Mercator（EPSG:3857）切片方案。</li>"
                    "<li>选择一组底图与对应中文注记：矢量 vec_w + cva_w、影像 img_w + cia_w，"
                    "或地形晕渲 ter_w + cta_w；分别添加两个 WMTS 地址。</li>"
                    "<li>选择矩阵集 w、默认样式；影像和地形底图选择 JPEG，其他图层选择 PNG。</li>"
                    "<li>中文注记放在对应底图上方；ibo_w 可作为境界叠加层。客户端无需填写天地图服务 Key。</li>"
                    "<li>更新服务后，如仍有旧的低清粗块，请移除并重新添加相关服务图层。</li></ol>"
                    "<p>地形晕渲是二维地图图片，不是 DEM 高程数据，不能用于驱动三维地表起伏。"
                    "地形底图最高第 14 级，更近距离的放大不会产生新的原始细节。</p><ul>"
                    + "".join(links)
                    + "</ul><h2>为什么需要适配</h2>"
                    "<p>服务会规范已确认的范围、原点、坐标系标识和比例尺描述，保护服务端 Key；"
                    "天地图原始瓦片图片保持不变，不做重投影、重采样或坐标偏移。</p>"
                    "<p>c 系列保留 EPSG:4490，适用于能够绘制该坐标系缓存瓦片的客户端。"
                    "几何坐标可动态投影，不代表每种三维场景都能重投影该瓦片格网。</p>"
                    "<h2>首级分辨率</h2><p>分辨率 = 全球覆盖宽度 ÷（瓦片列数 × 每张瓦片像素宽度）。"
                    "矩阵标识 1 的 c 格网为 360 ÷（2 × 256）= 0.703125 度/像素；"
                    "w 格网为（2 × π × 6378137）÷（2 × 256）≈ 78271.516964 投影米/像素。</p>"
                    "<p>完整使用说明、w/c 选择依据、比例尺换算和公网部署要求，请查看随服务提供的 README.md。</p>"
                    "<p>本服务不是坐标精度或地图合规证明；公开使用前请核实天地图授权、署名、配额和审图要求。</p>"
                    "</body></html>"
                )
                self._send(200, page.encode(), "text/html; charset=utf-8")
                return
            match = re.fullmatch(r"/([a-z]+_[cw])/wmts", url.path)
            if not match or match[1] not in SERVICES:
                self._send(404, "未知的服务地址。\n".encode(), "text/plain; charset=utf-8")
                return
            allowed = {
                "SERVICE", "VERSION", "REQUEST", "LAYER", "STYLE", "TILEMATRIXSET",
                "FORMAT", "TILEMATRIX", "TILEROW", "TILECOL",
            }
            if parameters.keys() - allowed:
                raise BadRequest("Unsupported query parameter; configure the upstream token on the server.")
            if parameters.get("SERVICE", "WMTS").upper() != "WMTS" or parameters.get("VERSION", "1.0.0") != "1.0.0":
                raise BadRequest("Only WMTS 1.0.0 is supported.")
            service = match[1]
            operation = parameters.get("REQUEST", "GetCapabilities").casefold()
            if operation == "getcapabilities":
                self._send(200, adapter.capabilities(service).xml, "application/xml; charset=utf-8")
            elif operation == "gettile":
                self._send(200, adapter.tile(service, parameters), LAYERS[SERVICES[service]][1])
            else:
                raise BadRequest("Only GetCapabilities and GetTile are supported.")
        except (BadRequest, ValueError):
            self._exception(400, "InvalidParameterValue", "无效或不支持的 WMTS 请求。")
        except UpstreamError:
            self._exception(502, "NoApplicableCode", "上游服务或瓦片格网校验失败；请检查服务端 Key 和网络连接。")
        except (BrokenPipeError, ConnectionResetError, TimeoutError):
            pass
        except Exception as error:
            self.log_message("服务内部错误：%s", type(error).__name__)
            self._send(500, "适配服务内部错误。\n".encode(), "text/plain; charset=utf-8")

    do_HEAD = do_GET


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__, add_help=False)
    options = parser.add_argument_group("参数说明")
    options.add_argument("-h", "--help", action="help", help="显示使用说明后退出。")
    options.add_argument("--port", type=int, default=8765, metavar="端口", help="本机监听端口（默认：8765）。")
    args = parser.parse_args()
    token = os.environ.pop("TIANDITU_TOKEN", "").strip()
    access_token = os.environ.pop("WMTS_ACCESS_TOKEN", "").strip()
    public_url = os.environ.get("PUBLIC_BASE_URL", "").strip()
    server = None
    try:
        server = WmtsServer(args.port, token, public_url, access_token)
        for service in SERVICES:
            server.adapter.capabilities(service)
        print(f"服务已启动：http://127.0.0.1:{server.server_port}", flush=True)
        for service in SERVICES:
            url = server.adapter.endpoint(service) + "SERVICE=WMTS&REQUEST=GetCapabilities&VERSION=1.0.0"
            address = url.replace(urllib.parse.quote_plus(access_token), "<客户端令牌>") if access_token else url
            print(f"服务 {service}：{address}", flush=True)
        server.serve_forever()
    except KeyboardInterrupt:
        return 0
    except (ValueError, UpstreamError, OSError) as error:
        print(f"启动失败：{error}", file=sys.stderr)
        return 1
    finally:
        if server is not None:
            server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
