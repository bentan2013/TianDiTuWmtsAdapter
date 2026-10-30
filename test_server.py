"""Offline protocol, forwarding and access-control regression tests."""

import contextlib
import http.client
import io
import math
import os
import struct
import subprocess
import sys
import threading
import unittest
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import zlib
from unittest.mock import patch

import server


TOKEN = "test-upstream-token-not-a-real-key"
CLIENT_TOKEN = "test-client-token-at-least-24-characters"


def capabilities(service="vec_c", standard_scale=False):
    geographic = service.endswith("_c")
    matrix_set = "c" if geographic else "w"
    crs = "4490" if geographic else "900913"
    span = 360 if geographic else 2 * server.MERCATOR_HALF_WORLD
    metres_per_unit = server.METRES_PER_DEGREE if geographic else 1
    origin = "90.0 -180.0" if geographic else f"{server.MERCATOR_HALF_WORLD} {-server.MERCATOR_HALF_WORLD}"
    lower = "-180 -90" if geographic else f"{-server.MERCATOR_HALF_WORLD} {-server.MERCATOR_HALF_WORLD}"
    upper = "180 90" if geographic else f"{server.MERCATOR_HALF_WORLD} {server.MERCATOR_HALF_WORLD}"
    matrices = []
    for level in (1, 2):
        resolution = span / (256 * 2**level)
        scale = resolution * metres_per_unit
        scale *= 1 / server.PIXEL_METRES if standard_scale else 96 / 0.0254
        matrices.append(
            f"<TileMatrix><ows:Identifier>{level}</ows:Identifier>"
            f"<ScaleDenominator>{scale}</ScaleDenominator>"
            f"<TopLeftCorner>{origin}</TopLeftCorner><TileWidth>256</TileWidth><TileHeight>256</TileHeight>"
            f"<MatrixWidth>{2**level}</MatrixWidth><MatrixHeight>{2**(level-1) if geographic else 2**level}</MatrixHeight></TileMatrix>"
        )
    return (
        f'<Capabilities xmlns="{server.WMTS}" xmlns:ows="{server.OWS}" version="1.0.0">'
        "<ows:ServiceIdentification><ows:Title>TianDiTu</ows:Title><ows:ServiceType/>"
        "<ows:ServiceTypeVersion>1.0.0</ows:ServiceTypeVersion></ows:ServiceIdentification>"
        "<ows:ServiceProvider><ows:ProviderName>TianDiTu</ows:ProviderName></ows:ServiceProvider>"
        f"<Contents><Layer><ows:Identifier>{server.SERVICES[service]}</ows:Identifier>"
        f"<ows:WGS84BoundingBox><ows:LowerCorner>{lower}</ows:LowerCorner>"
        f"<ows:UpperCorner>{upper}</ows:UpperCorner></ows:WGS84BoundingBox>"
        "<Style isDefault=\"true\"><ows:Identifier>default</ows:Identifier></Style><Format>tiles</Format>"
        f"<TileMatrixSetLink><TileMatrixSet>{matrix_set}</TileMatrixSet></TileMatrixSetLink></Layer>"
        f"<TileMatrixSet><ows:Identifier>{matrix_set}</ows:Identifier>"
        f"<ows:SupportedCRS>urn:ogc:def:crs:EPSG::{crs}</ows:SupportedCRS>"
        + "".join(matrices) + "</TileMatrixSet></Contents></Capabilities>"
    ).encode()


def png_tile():
    def chunk(name, body):
        return struct.pack(">I", len(body)) + name + body + struct.pack(">I", zlib.crc32(name + body))

    return (
        server.PNG_SIGNATURE + chunk(b"IHDR", struct.pack(">IIBBBBB", 256, 256, 8, 6, 0, 0, 0))
        + chunk(b"IDAT", zlib.compress((b"\0" + b"\0" * 1024) * 256)) + chunk(b"IEND", b"")
    )


def jpeg_tile():
    def segment(marker, body):
        return b"\xff" + bytes([marker]) + struct.pack(">H", len(body) + 2) + body

    # A uniform gray baseline JPEG: one zero DC coefficient and one EOB per 8x8 block.
    huffman = b"\x01" + b"\0" * 15 + b"\0"
    return (
        b"\xff\xd8" + segment(0xDB, b"\0" + b"\x01" * 64)
        + segment(0xC0, struct.pack(">BHHBBBB", 8, 256, 256, 1, 1, 0x11, 0))
        + segment(0xC4, b"\0" + huffman) + segment(0xC4, b"\x10" + huffman)
        + segment(0xDA, b"\x01\x01\0\0\x3f\0") + b"\0" * 256 + b"\xff\xd9"
    )


class FakeUpstream:
    def __init__(self):
        self.requests = []
        self.tile = png_tile()
        self.error = None

    def get(self, service, parameters):
        self.requests.append((service, parameters))
        if self.error:
            raise self.error
        return capabilities(service) if parameters["REQUEST"] == "GetCapabilities" else self.tile


@contextlib.contextmanager
def running_server(**kwargs):
    fake = FakeUpstream()
    instance = server.WmtsServer(0, TOKEN, fetch=fake.get, **kwargs)
    worker = threading.Thread(target=instance.serve_forever, daemon=True)
    worker.start()
    try:
        yield instance, fake, f"http://127.0.0.1:{instance.server_port}"
    finally:
        instance.shutdown()
        instance.server_close()
        worker.join(timeout=3)


class NormalizationTests(unittest.TestCase):
    def test_scale_conversion_preserves_crs_origin_and_matrix_ids(self):
        for service in server.SERVICES:
            with self.subTest(service=service):
                geographic = service.endswith("_c")
                expected_crs = "4490" if geographic else "3857"
                span = 360 if geographic else 2 * server.MERCATOR_HALF_WORLD
                metres_per_unit = server.METRES_PER_DEGREE if geographic else 1
                result = server.normalize_capabilities(capabilities(service), service, "http://127.0.0.1:8765/wmts?")
                root = ET.fromstring(result.xml)
                self.assertEqual(root.findtext("w:Contents/w:TileMatrixSet/o:SupportedCRS", namespaces=server.NS), "urn:ogc:def:crs:EPSG::" + expected_crs)
                matrices = root.findall("w:Contents/w:TileMatrixSet/w:TileMatrix", server.NS)
                self.assertEqual([m.findtext("o:Identifier", namespaces=server.NS) for m in matrices], ["1", "2"])
                for level, matrix in enumerate(matrices, start=1):
                    scale = float(matrix.findtext("w:ScaleDenominator", namespaces=server.NS))
                    self.assertTrue(math.isclose(scale * server.PIXEL_METRES / metres_per_unit, span / (256 * 2**level)))
                    origin = list(map(float, matrix.findtext("w:TopLeftCorner", namespaces=server.NS).split()))
                    expected_origin = [90, -180] if geographic else [-server.MERCATOR_HALF_WORLD, server.MERCATOR_HALF_WORLD]
                    self.assertTrue(all(math.isclose(a, b) for a, b in zip(origin, expected_origin)))
                image_format = "image/jpeg" if server.SERVICES[service] in ("img", "ter") else "image/png"
                self.assertEqual(root.findtext("w:Contents/w:Layer/w:Format", namespaces=server.NS), image_format)
                endpoints = root.findall("o:OperationsMetadata/o:Operation/o:DCP/o:HTTP/o:Get", server.NS)
                self.assertEqual([e.get(f"{{{server.XLINK}}}href") for e in endpoints], ["http://127.0.0.1:8765/wmts?"] * 2)

    def test_already_standard_metadata_is_idempotent(self):
        for service in ("vec_c", "vec_w"):
            with self.subTest(service=service):
                first = server.normalize_capabilities(capabilities(service, standard_scale=True), service, "http://localhost/wmts?")
                second = server.normalize_capabilities(first.xml, service, "http://localhost/wmts?")
                self.assertEqual(first, second)

    def test_projected_meter_values_become_valid_wgs84_bounds(self):
        source = capabilities("vec_w")
        result = server.normalize_capabilities(source, "vec_w", "http://localhost/wmts?")
        root = ET.fromstring(result.xml)
        lower = list(map(float, root.findtext("w:Contents/w:Layer/o:WGS84BoundingBox/o:LowerCorner", namespaces=server.NS).split()))
        upper = list(map(float, root.findtext("w:Contents/w:Layer/o:WGS84BoundingBox/o:UpperCorner", namespaces=server.NS).split()))
        self.assertEqual(lower[0], -180)
        self.assertEqual(upper[0], 180)
        self.assertAlmostEqual(lower[1], -85.0511287798066)
        self.assertAlmostEqual(upper[1], 85.0511287798066)

    def test_projected_grid_must_have_square_matrices(self):
        source = capabilities("vec_w").replace(b"<MatrixHeight>2</MatrixHeight>", b"<MatrixHeight>1</MatrixHeight>")
        with self.assertRaises(server.UpstreamError):
            server.normalize_capabilities(source, "vec_w", "http://localhost/wmts?")

    def test_terrain_annotation_geographic_metadata_is_normalized_only_for_known_grid(self):
        root = ET.fromstring(capabilities("cta_w"))
        for matrix in root.findall("w:Contents/w:TileMatrixSet/w:TileMatrix", server.NS):
            width = int(matrix.findtext("w:MatrixWidth", namespaces=server.NS))
            matrix.find("w:TopLeftCorner", server.NS).text = "90.0 -180.0"
            matrix.find("w:MatrixHeight", server.NS).text = str(width // 2)
        source = ET.tostring(root)
        first = server.normalize_capabilities(source, "cta_w", "http://localhost/wmts?")
        self.assertEqual(first.matrices, {"1": (2, 2), "2": (4, 4)})
        self.assertEqual(first, server.normalize_capabilities(first.xml, "cta_w", "http://localhost/wmts?"))
        for old, new in ((b"90.0 -180.0", b"89.0 -180.0"), (b"<MatrixWidth>2", b"<MatrixWidth>3")):
            with self.subTest(change=new), self.assertRaises(server.UpstreamError):
                server.normalize_capabilities(source.replace(old, new), "cta_w", "http://localhost/wmts?")

    def test_malformed_extra_projected_annotation_level_is_not_advertised(self):
        root = ET.fromstring(capabilities("cva_w"))
        matrix_set = root.find("w:Contents/w:TileMatrixSet", server.NS)
        extra = ET.fromstring(
            f'<TileMatrix xmlns="{server.WMTS}" xmlns:ows="{server.OWS}">'
            "<ows:Identifier>19</ows:Identifier><ScaleDenominator>1128.4994333441375</ScaleDenominator>"
            "<TopLeftCorner>90.0 -180.0</TopLeftCorner><TileWidth>256</TileWidth><TileHeight>256</TileHeight>"
            "<MatrixWidth>524288</MatrixWidth><MatrixHeight>262144</MatrixHeight></TileMatrix>"
        )
        matrix_set.append(extra)
        result = server.normalize_capabilities(ET.tostring(root), "cva_w", "http://localhost/wmts?")
        self.assertEqual(list(result.matrices), ["1", "2"])
        normalized = ET.fromstring(result.xml)
        self.assertEqual(len(normalized.findall("w:Contents/w:TileMatrixSet/w:TileMatrix", server.NS)), 2)
        extra.find("w:TopLeftCorner", server.NS).text = "89.0 -180.0"
        with self.assertRaises(server.UpstreamError):
            server.normalize_capabilities(ET.tostring(root), "cva_w", "http://localhost/wmts?")

    def test_changed_grid_or_crs_fails_closed(self):
        for old, new in (
            (b"EPSG::4490", b"EPSG::4326"),
            (b"90.0 -180.0", b"85.0 -180.0"),
            (b"<MatrixWidth>2</MatrixWidth>", b"<MatrixWidth>3</MatrixWidth>"),
            (b"<TileWidth>256</TileWidth>", b"<TileWidth>512</TileWidth>"),
            (b"<ScaleDenominator>", b"<ScaleDenominator>999"),
            (b"<ows:Identifier>default</ows:Identifier>", b"<ows:Identifier>other</ows:Identifier>"),
            (b"<TileMatrixSet>c</TileMatrixSet>", b"<TileMatrixSet>w</TileMatrixSet>"),
        ):
            with self.subTest(change=new):
                with self.assertRaises(server.UpstreamError):
                    server.normalize_capabilities(capabilities().replace(old, new), "vec_c", "http://localhost/wmts?")

    def test_credential_bearing_metadata_is_not_returned(self):
        fake = FakeUpstream()
        source = capabilities().replace(b"TianDiTu", TOKEN.encode())
        adapter = server.Adapter(TOKEN, "http://localhost", fetch=lambda *_: source)
        with self.assertRaises(server.UpstreamError):
            adapter.capabilities("vec_c")
        self.assertFalse(adapter.cache)

    def test_upstream_values_are_not_echoed_in_normalization_errors(self):
        source = capabilities().replace(b"<ScaleDenominator>", b"<ScaleDenominator>" + TOKEN.encode())
        with self.assertRaises(server.UpstreamError) as caught:
            server.normalize_capabilities(source, "vec_c", "http://localhost/wmts?")
        self.assertNotIn(TOKEN, str(caught.exception))


class HttpTests(unittest.TestCase):
    def request(self, base, path, headers=None):
        request = urllib.request.Request(base + path, headers=headers or {})
        try:
            response = urllib.request.urlopen(request, timeout=3)
        except urllib.error.HTTPError as error:
            response = error
        with response:
            return response.status, response.read(), response.headers

    def test_capabilities_are_cached_and_never_expose_upstream_token(self):
        with running_server() as (_, fake, base):
            for _ in range(2):
                status, body, _ = self.request(base, "/vec_c/wmts?SERVICE=WMTS&REQUEST=GetCapabilities")
                self.assertEqual(status, 200)
                self.assertNotIn(TOKEN.encode(), body)
                self.assertIn((base + "/vec_c/wmts?").encode(), body)
            self.assertEqual(len(fake.requests), 1)

    def test_chinese_guidance_and_errors_use_utf8_byte_lengths(self):
        with running_server() as (_, _, base):
            for path, expected_status, text in (
                ("/", 200, "天地图 WMTS 适配服务"),
                ("/missing", 404, "未知的服务地址"),
                ("/vec_w/wmts?REQUEST=GetFeatureInfo", 400, "无效或不支持的 WMTS 请求"),
            ):
                with self.subTest(path=path):
                    status, body, headers = self.request(base, path)
                    self.assertEqual(status, expected_status)
                    self.assertIn(text, body.decode("utf-8"))
                    self.assertEqual(headers["Content-Length"], str(len(body)))
                    self.assertIn("charset=utf-8", headers["Content-Type"])
                    self.assertNotIn(TOKEN.encode(), body)

    def test_get_head_and_tile_responses_reuse_one_framed_connection(self):
        with running_server() as (instance, fake, _):
            connection = http.client.HTTPConnection("127.0.0.1", instance.server_port, timeout=3)
            tile = (
                "/vec_w/wmts?REQUEST=GetTile&LAYER=vec&STYLE=default&TILEMATRIXSET=w"
                "&FORMAT=image/png&TILEMATRIX=1&TILEROW=0&TILECOL=0"
            )
            try:
                connection.request("GET", "/vec_w/wmts?REQUEST=GetCapabilities")
                response = connection.getresponse()
                self.assertEqual(response.version, 11)
                self.assertEqual(response.status, 200)
                response.read()
                socket = connection.sock
                self.assertIsNotNone(socket)
                for method in ("HEAD", "GET"):
                    connection.request(method, tile)
                    response = connection.getresponse()
                    self.assertEqual(response.status, 200)
                    self.assertEqual(response.getheader("Content-Length"), str(len(fake.tile)))
                    self.assertEqual(response.read(), b"" if method == "HEAD" else fake.tile)
                    self.assertIs(connection.sock, socket)
                fake.tile = jpeg_tile()
                connection.request("GET", tile.replace("vec_w", "img_w").replace("LAYER=vec", "LAYER=img").replace("image/png", "image/jpeg"))
                response = connection.getresponse()
                self.assertEqual(response.version, 11)
                self.assertEqual(response.status, 200)
                self.assertEqual(response.getheader("Content-Type"), "image/jpeg")
                self.assertEqual(response.getheader("Content-Length"), str(len(fake.tile)))
                self.assertEqual(response.read(), fake.tile)
                self.assertIs(connection.sock, socket)
            finally:
                connection.close()

    def test_tile_is_forwarded_unchanged_with_legacy_upstream_format(self):
        for service in server.SERVICES:
            with self.subTest(service=service), running_server() as (_, fake, base):
                matrix_set = service.rsplit("_", 1)[1]
                layer = server.SERVICES[service]
                image_format = "image/jpeg" if layer in ("img", "ter") else "image/png"
                fake.tile = jpeg_tile() if image_format == "image/jpeg" else png_tile()
                status, body, headers = self.request(
                    base, f"/{service}/wmts?SERVICE=WMTS&REQUEST=GetTile&VERSION=1.0.0"
                    f"&LAYER={layer}&STYLE=default&TILEMATRIXSET={matrix_set}&FORMAT={image_format}&TILEMATRIX=2&TILEROW=1&TILECOL=3",
                )
                self.assertEqual(status, 200)
                self.assertEqual(body, fake.tile)
                self.assertEqual(headers["Content-Type"], image_format)
                self.assertEqual(fake.requests[-1][1]["FORMAT"], "tiles")
                self.assertEqual(fake.requests[-1][1]["TILEMATRIXSET"], matrix_set)
                self.assertEqual(fake.requests[-1][0], service)

    def test_jpeg_requests_reject_wrong_formats_sizes_and_truncated_headers(self):
        path = (
            "/img_w/wmts?REQUEST=GetTile&LAYER=img&STYLE=default&TILEMATRIXSET=w"
            "&FORMAT=image/jpeg&TILEMATRIX=1&TILEROW=0&TILECOL=0"
        )
        with running_server() as (_, fake, base):
            status, _, _ = self.request(base, path.replace("image/jpeg", "image/png"))
            self.assertEqual(status, 400)
            self.assertFalse(fake.requests)
            valid = jpeg_tile()
            oversized = valid.replace(b"\xff\xc0\x00\x0b\x08\x01\x00\x01\x00", b"\xff\xc0\x00\x0b\x08\x01\x00\x02\x00")
            for body in (
                png_tile(), b"not an image", b"\xff\xd8\xff", b"\xff\xd8\xff\xe1\xff\xff",
                b"\xff\xd8\xff\xe1\x00\x01", b"\xff\xd8\xff\xc0\x00\x02",
                b"\xff\xd8\xff\xda\x00\x02", oversized,
            ):
                with self.subTest(prefix=body[:16]):
                    fake.tile = body
                    status, _, _ = self.request(base, path)
                    self.assertEqual(status, 502)
            fake.tile = b"\xff\xd8\xff\xe1\x00\x06Exif" + valid[2:]
            status, body, headers = self.request(base, path)
            self.assertEqual(status, 200)
            self.assertEqual(headers["Content-Type"], "image/jpeg")
            self.assertEqual(body, fake.tile)

    def test_invalid_queries_and_tile_indices_are_rejected(self):
        for query in (
            "REQUEST=GetCapabilities&request=GetTile",
            "REQUEST=GetCapabilities&tk=not-accepted-from-clients",
            "REQUEST=GetFeatureInfo",
            "VERSION=2.0.0",
            "REQUEST=GetTile",
            "REQUEST=GetTile&LAYER=vec&STYLE=default&TILEMATRIXSET=c&FORMAT=image/png&TILEMATRIX=1&TILEROW=1&TILECOL=0",
            "REQUEST=GetTile&LAYER=vec&STYLE=default&TILEMATRIXSET=c&FORMAT=image/png&TILEMATRIX=1&TILEROW=-1&TILECOL=0",
        ):
            with self.subTest(query=query), running_server() as (_, fake, base):
                status, _, _ = self.request(base, "/vec_c/wmts?" + query)
                self.assertEqual(status, 400)
                self.assertFalse(any(p["REQUEST"] == "GetTile" for _, p in fake.requests))

    def test_local_listener_rejects_rebinding_and_cross_site_access(self):
        with running_server() as (_, fake, base):
            for headers in ({"Host": "attacker.invalid"}, {"Origin": "https://attacker.invalid"}, {"Sec-Fetch-Site": "cross-site"}):
                status, _, _ = self.request(base, "/vec_c/wmts", headers)
                self.assertEqual(status, 403)
            self.assertFalse(fake.requests)

    def test_public_mode_requires_auth_and_advertises_https_proxy_urls(self):
        with running_server(public_url="https://wmts.example.com", access_token=CLIENT_TOKEN) as (_, fake, base):
            status, _, _ = self.request(base, "/vec_c/wmts")
            self.assertEqual(status, 401)
            self.assertFalse(fake.requests)
            query = urllib.parse.urlencode({"access_token": CLIENT_TOKEN, "REQUEST": "GetCapabilities"})
            status, body, headers = self.request(base, "/vec_c/wmts?" + query, {"Origin": "https://client.example.com"})
            self.assertEqual(status, 200)
            self.assertIn(b"https://wmts.example.com/vec_c/wmts?", body)
            self.assertNotIn(TOKEN.encode(), body)
            self.assertEqual(headers["Access-Control-Allow-Origin"], "*")

    def test_upstream_errors_are_redacted_and_logged_without_query_strings(self):
        with running_server() as (_, fake, base):
            fake.error = server.UpstreamError("Do not expose " + TOKEN)
            capture = io.StringIO()
            with contextlib.redirect_stderr(capture):
                status, body, _ = self.request(base, "/vec_c/wmts?REQUEST=GetCapabilities")
            self.assertEqual(status, 502)
            self.assertNotIn(TOKEN.encode(), body)
            self.assertNotIn(TOKEN, capture.getvalue())
            self.assertNotIn("REQUEST=", capture.getvalue())

    def test_successful_http_response_with_non_tile_body_is_not_forwarded(self):
        with running_server() as (_, fake, base):
            fake.tile = b'{"error":"token expired"}'
            status, body, _ = self.request(
                base, "/vec_c/wmts?REQUEST=GetTile&LAYER=vec&STYLE=default&TILEMATRIXSET=c"
                "&FORMAT=image/png&TILEMATRIX=1&TILEROW=0&TILECOL=0",
            )
            self.assertEqual(status, 502)
            self.assertNotIn(fake.tile, body)
            self.assertEqual(ET.fromstring(body).tag, f"{{{server.OWS}}}ExceptionReport")

    def test_public_configuration_cannot_disable_https_or_authentication(self):
        for url, access_token in (("http://wmts.example.com", CLIENT_TOKEN), ("https://wmts.example.com", ""), ("https://wmts.example.com/path", CLIENT_TOKEN)):
            with self.subTest(url=url), self.assertRaises(ValueError):
                server.WmtsServer(0, TOKEN, url, access_token)


class UpstreamTests(unittest.TestCase):
    def test_network_errors_do_not_include_credential_bearing_urls(self):
        client = server.Upstream(TOKEN)
        error = urllib.error.HTTPError("https://t0.tianditu.gov.cn/?tk=" + TOKEN, 403, "Forbidden", {}, None)
        with patch.object(client.opener, "open", side_effect=error):
            with self.assertRaises(server.UpstreamError) as caught:
                client.get("vec_c", {"REQUEST": "GetCapabilities"})
        self.assertNotIn(TOKEN, str(caught.exception))
        self.assertIn("403", str(caught.exception))

    def test_redirects_are_never_followed(self):
        with self.assertRaises(server.UpstreamError):
            server.NoRedirect().redirect_request(None, None, 302, "", {}, "https://attacker.invalid")


class CommandLineTests(unittest.TestCase):
    def test_chinese_help_uses_utf8_with_a_legacy_redirected_encoding(self):
        result = subprocess.run(
            [sys.executable, "-B", server.__file__, "--help"],
            env={**os.environ, "PYTHONIOENCODING": "cp1252"},
            capture_output=True, timeout=5,
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode("utf-8"))
        self.assertIn("参数说明", result.stdout.decode("utf-8"))
        self.assertIn("本机监听端口", result.stdout.decode("utf-8"))


if __name__ == "__main__":
    unittest.main()
