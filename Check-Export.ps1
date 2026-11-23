#Requires -Version 7.0
<#
Check the distributed proof export without rebuilding Mathlib.
-LeanBin accepts the bin directory containing Lean's matching checkers.
#>
[CmdletBinding()]
param([string]$LeanBin = '')

$ErrorActionPreference = 'Stop'
if (-not $LeanBin) {
    $leanPath = & elan which lean
    if ($LASTEXITCODE -ne 0) { throw 'Run from the repository root with the pinned Lean toolchain installed, or pass -LeanBin.' }
    $LeanBin = Split-Path ([string]$leanPath) -Parent
}
$record = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'evidence/checker-record.json') -Raw | ConvertFrom-Json
$compressed = Join-Path $PSScriptRoot 'evidence/suite.ndjson.gz'
$temporary = Join-Path ([IO.Path]::GetTempPath()) ('shor-proof-' + [guid]::NewGuid().ToString('N') + '.ndjson')
try {
    $inputProof = [IO.File]::OpenRead($compressed)
    try {
        $inflater = [IO.Compression.GZipStream]::new($inputProof, [IO.Compression.CompressionMode]::Decompress)
        try {
            $expanded = [IO.File]::Open($temporary, [IO.FileMode]::CreateNew)
            try { $inflater.CopyTo($expanded) } finally { $expanded.Dispose() }
        } finally { $inflater.Dispose() }
    } finally { $inputProof.Dispose() }

    $actual = Get-FileHash -LiteralPath $temporary -Algorithm SHA256
    if ($actual.Hash -ne $record.export_sha256) { throw 'The expanded proof differs from the published SHA-256 digest.' }
    Write-Output ('Export SHA-256 ' + $actual.Hash)
    foreach ($name in @('con-leche','con-ron','leanchecker')) {
        $fileName = if ($IsWindows) { "$name.exe" } else { $name }
        $exe = Join-Path $LeanBin $fileName
        $checkArgs = if ($name -eq 'leanchecker') { @('--from-export',$temporary) } else { @('--verified','--jobs=2','--progress=1000',$temporary) }
        & $exe @checkArgs
        if ($LASTEXITCODE -ne 0) { throw "$name failed with exit code $LASTEXITCODE." }
    }
} finally {
    if (Test-Path -LiteralPath $temporary -PathType Leaf) { Remove-Item -LiteralPath $temporary }
}
