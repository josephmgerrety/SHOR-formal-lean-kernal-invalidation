param([string]$DependenciesRoot = '', [string]$LeanBin = '', [string]$ObjectRoot = '')

$ProofSuiteRoot = $PSScriptRoot
$ProofSuiteElanRoot = if ($env:ELAN_HOME) { $env:ELAN_HOME } else { Join-Path $env:USERPROFILE '.elan' }
$ProofSuiteLeanBin = if ($LeanBin) { (Resolve-Path -LiteralPath $LeanBin -ErrorAction Stop).Path } else {
    Join-Path $ProofSuiteElanRoot 'toolchains\leanprover--lean4---v4.36.0\bin'
}
$ProofSuiteLean = Join-Path $ProofSuiteLeanBin 'lean.exe'
if (-not (Test-Path -LiteralPath $ProofSuiteLean -PathType Leaf)) { throw "Lean 4.36.0 was not found at $ProofSuiteLean. Supply -LeanBin." }
if ($DependenciesRoot) {
    $ProofSuiteDependencyRoot = (Resolve-Path -LiteralPath $DependenciesRoot -ErrorAction Stop).Path
    if (-not (Test-Path -LiteralPath (Join-Path $ProofSuiteDependencyRoot 'mathlib'))) {
        $ProofSuiteDependencyRoot = Join-Path $ProofSuiteDependencyRoot '.lake\packages'
    }
} else {
    $ProofSuiteDependencyRoot = @(
        (Join-Path $ProofSuiteRoot '.lake\packages')
    ) | Where-Object { Test-Path -LiteralPath (Join-Path $_ 'mathlib\.lake\build\lib\lean\Mathlib.olean') -PathType Leaf } | Select-Object -First 1
}
if (-not $ProofSuiteDependencyRoot -or -not (Test-Path -LiteralPath (Join-Path $ProofSuiteDependencyRoot 'mathlib\.lake\build\lib\lean\Mathlib.olean') -PathType Leaf)) {
    throw 'Compiled Mathlib dependencies were not found. Supply -DependenciesRoot pointing to .lake\packages.'
}
$ProofSuiteObjectRoot = if ($ObjectRoot) { [System.IO.Path]::GetFullPath($ObjectRoot) } else { Join-Path $ProofSuiteRoot '.build-4.36.0' }
$ProofSuiteLibraries = @(Get-ChildItem -LiteralPath $ProofSuiteDependencyRoot -Directory | ForEach-Object { Join-Path $_.FullName '.lake\build\lib\lean' } | Where-Object { Test-Path -LiteralPath $_ -PathType Container })
$env:LEAN_PATH = (@($ProofSuiteObjectRoot) + $ProofSuiteLibraries) -join ';'
$env:Path = "$ProofSuiteLeanBin;$env:Path"
