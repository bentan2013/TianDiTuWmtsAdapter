<#
.SYNOPSIS
启动独立的天地图 WMTS 适配服务。
.DESCRIPTION
需要 Python 3.10 或更新版本。未设置 TIANDITU_TOKEN 时，会提示安全输入天地图服务 Key；
不会把 Key 保存到文件。保持窗口运行，按 Ctrl+C 停止服务。
.PARAMETER Port
本机监听端口，默认为 8765。服务始终只监听 127.0.0.1。
.EXAMPLE
.\start.ps1 -Port 8766
#>
[CmdletBinding()]
param(
    [ValidateRange(1, 65535)]
    [int]$Port = 8765
)

$ErrorActionPreference = 'Stop'
$previousToken = $env:TIANDITU_TOKEN
$secureToken = $null

try {
    if ([string]::IsNullOrWhiteSpace($env:TIANDITU_TOKEN)) {
        $secureToken = Read-Host '请输入天地图服务 Key（输入不显示，也不保存到文件）' -AsSecureString
        $pointer = [Runtime.InteropServices.Marshal]::SecureStringToBSTR($secureToken)
        try {
            $env:TIANDITU_TOKEN = [Runtime.InteropServices.Marshal]::PtrToStringBSTR($pointer)
        }
        finally {
            [Runtime.InteropServices.Marshal]::ZeroFreeBSTR($pointer)
        }
    }

    & python -B (Join-Path $PSScriptRoot 'server.py') --port $Port
    if ($LASTEXITCODE -ne 0) {
        throw "天地图适配服务已退出，退出码：$LASTEXITCODE。"
    }
}
finally {
    $env:TIANDITU_TOKEN = $previousToken
    if ($null -ne $secureToken) {
        $secureToken.Dispose()
    }
}
