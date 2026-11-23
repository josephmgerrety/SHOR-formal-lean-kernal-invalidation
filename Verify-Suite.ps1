#Requires -Version 7.0
<#
Rebuilds all 20 compilation units, exports the listed public declarations with
their dependencies, and checks the exact export with con-leche, con-ron and
Lean's kernel. Each run has fresh objects and its own evidence directory.

Example: pwsh -NoProfile -File .\Verify-Suite.ps1 -DisplaySource -RunNegativeControl
-DependenciesRoot accepts a .lake\packages directory or its owning project.
-ControlOnly tests the small control fixture only; it does not check the suite.
#>
[CmdletBinding()]
param(
    [switch]$DisplaySource,
    [string]$DependenciesRoot = '',
    [string]$LeanBin = '',
    [string]$DeclarationsPath = '',
    [ValidateRange(1, 16)][int]$Jobs = 2,
    [ValidateRange(1, 1000000)][int]$ProgressStride = 1000,
    [switch]$RunNegativeControl,
    [switch]$ControlOnly
)

$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
Set-StrictMode -Version Latest
$utf8 = [System.Text.UTF8Encoding]::new($false)
$OutputEncoding = $utf8
[Console]::OutputEncoding = $utf8
$savedPath = $env:Path
$savedLeanPath = $env:LEAN_PATH
$suiteDirectory = $PSScriptRoot
$runId = (Get-Date -Format 'yyyyMMdd-HHmmss') + '-' + [guid]::NewGuid().ToString('N').Substring(0, 8)
$verificationDirectory = Join-Path $suiteDirectory 'verification'
$runDirectory = Join-Path $verificationDirectory $runId
$buildDirectory = Join-Path $runDirectory 'build'
$logDirectory = Join-Path $runDirectory 'logs'
New-Item -ItemType Directory -Path $buildDirectory, $logDirectory -Force | Out-Null
$resultsFile = Join-Path $runDirectory 'results.json'
$latestFile = Join-Path $verificationDirectory 'latest-verification.json'
$commands = [System.Collections.Generic.List[object]]::new()
$compiledModules = [System.Collections.Generic.List[object]]::new()
$state = [ordered]@{
    status = 'running'; full_suite_checked = $false
    scope = $(if ($ControlOnly) { 'checker-control-only' } else { 'complete-source-suite' })
    started_utc = [DateTimeOffset]::UtcNow.ToString('o')
    source_directory = $suiteDirectory; run_directory = $runDirectory
    commands = @(); modules = @()
}

function Save-Results {
    $state.commands = @($commands.ToArray())
    $state.modules = @($compiledModules.ToArray())
    [System.IO.File]::WriteAllText($resultsFile, ($state | ConvertTo-Json -Depth 12), $utf8)
    [System.IO.File]::WriteAllText($latestFile, ([ordered]@{
        status = $state.status; scope = $state.scope; results_file = $resultsFile
    } | ConvertTo-Json), $utf8)
}

function Show-TextFile {
    param([string]$Path)
    foreach ($line in [System.IO.File]::ReadLines($Path, $utf8)) { Write-Host $line }
}

function Invoke-Recorded {
    param(
        [Parameter(Mandatory)][string]$Name,
        [Parameter(Mandatory)][string]$Executable,
        [string[]]$Arguments = @(),
        [int]$ExpectedExit = 0,
        [string]$StdoutPath = '',
        [switch]$ExportOutput,
        [switch]$ContinueOnFailure
    )
    if (-not $StdoutPath) { $StdoutPath = Join-Path $logDirectory ($Name + '.stdout.txt') }
    $stderrPath = Join-Path $logDirectory ($Name + '.stderr.txt')
    $quotedArguments = @(@($Executable) + $Arguments | ForEach-Object { "'" + $_.Replace("'", "''") + "'" })
    $commandText = '& ' + ($quotedArguments -join ' ')
    Write-Host "COMMAND: $commandText"
    [System.IO.File]::WriteAllText((Join-Path $logDirectory ($Name + '.command.txt')), $commandText, $utf8)
    $startInfo = [System.Diagnostics.ProcessStartInfo]::new()
    $startInfo.FileName = $Executable
    $startInfo.WorkingDirectory = $suiteDirectory
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    foreach ($argument in $Arguments) { $startInfo.ArgumentList.Add($argument) }
    foreach ($setting in @('CON_LECHE_INMODEL', 'CON_LECHE_INMODEL_CENSUS', 'CON_LECHE_INMODEL_DUMP',
        'CON_LECHE_ROUTE_TRACE', 'CON_LECHE_PROJREC_TRACE', 'CON_LECHE_VERBOSE')) {
        $null = $startInfo.Environment.Remove($setting)
    }
    $process = [System.Diagnostics.Process]::new()
    $process.StartInfo = $startInfo
    $started = $false
    $startedUtc = [DateTimeOffset]::UtcNow.ToString('o')
    $timer = [System.Diagnostics.Stopwatch]::StartNew()
    $outputStream = [System.IO.FileStream]::new($StdoutPath, 'Create', 'Write', 'ReadWrite')
    $errorStream = [System.IO.FileStream]::new($stderrPath, 'Create', 'Write', 'ReadWrite')
    try {
        $started = $process.Start()
        if (-not $started) { throw "Could not start $Executable" }
        # Export bytes go directly to disk. No array of proof lines is held in memory.
        $outputCopy = $process.StandardOutput.BaseStream.CopyToAsync($outputStream)
        $errorCopy = $process.StandardError.BaseStream.CopyToAsync($errorStream)
        $nextProgress = 30
        while (-not $process.WaitForExit(1000)) {
            if ($timer.Elapsed.TotalSeconds -ge $nextProgress) {
                Write-Host ("RUNNING: {0}; elapsed {1:N0} seconds" -f $Name, $timer.Elapsed.TotalSeconds)
                Get-Content -LiteralPath $stderrPath -Tail 3 -Encoding utf8 | ForEach-Object { Write-Host $_ }
                $nextProgress += 30
            }
        }
        $null = $outputCopy.GetAwaiter().GetResult()
        $null = $errorCopy.GetAwaiter().GetResult()
        $exitCode = $process.ExitCode
    } finally {
        if ($started -and -not $process.HasExited) { $process.Kill($true); $process.WaitForExit() }
        $outputStream.Dispose(); $errorStream.Dispose(); $process.Dispose(); $timer.Stop()
    }
    if (-not $ExportOutput) { Show-TextFile $StdoutPath }
    Show-TextFile $stderrPath
    Write-Host "RESULT: $Name exit=$exitCode expected=$ExpectedExit elapsed=$($timer.Elapsed.TotalSeconds)"
    $record = [pscustomobject]@{
        name = $Name; executable = $Executable; arguments = @($Arguments); command = $commandText
        started_utc = $startedUtc; completed_utc = [DateTimeOffset]::UtcNow.ToString('o')
        elapsed_seconds = $timer.Elapsed.TotalSeconds
        exit_code = $exitCode; expected_exit_code = $ExpectedExit; expectation_met = ($exitCode -eq $ExpectedExit)
        stdout = $StdoutPath; stderr = $stderrPath
    }
    $commands.Add($record)
    Save-Results
    if ($exitCode -ne $ExpectedExit -and -not $ContinueOnFailure) {
        throw "$Name returned $exitCode; expected $ExpectedExit. See $stderrPath"
    }
    return $record
}

function Read-RootNames {
    param([string]$Path)
    $names = [System.Collections.Generic.List[string]]::new()
    if ([System.IO.Path]::GetExtension($Path) -ieq '.json') {
        $document = [System.IO.File]::ReadAllText($Path, $utf8) | ConvertFrom-Json
        $rows = if ($document.PSObject.Properties['declarations']) { $document.declarations } else { $document }
        foreach ($row in @($rows)) {
            if ($row -is [string]) { $name = $row }
            elseif ($row.PSObject.Properties['name']) { $name = [string]$row.name }
            elseif ($row.PSObject.Properties['fullName']) { $name = [string]$row.fullName }
            else { throw 'Every declaration JSON entry must contain a name.' }
            if ($row -isnot [string] -and $row.PSObject.Properties['private'] -and $row.private) {
                throw "Private declaration listed as a public root: $name"
            }
            $names.Add($name.Trim())
        }
    } else {
        foreach ($line in [System.IO.File]::ReadLines($Path, $utf8)) {
            $name = $line.Trim()
            if ($name -and -not $name.StartsWith('#')) { $names.Add($name) }
        }
    }
    if ($names.Count -eq 0) { throw 'The declaration list is empty.' }
    if (@($names | Where-Object { -not $_ -or $_.Contains("`n") -or $_.Contains("`r") }).Count -ne 0) {
        throw 'Empty or multiline declaration name.'
    }
    if (@($names | Sort-Object -Unique).Count -ne $names.Count) { throw 'Duplicate declaration name.' }
    return $names.ToArray()
}

function Check-Export {
    param([string]$ProofPath, [string]$Prefix)
    $proofHash = (Get-FileHash -LiteralPath $ProofPath -Algorithm SHA256).Hash
    $failedCheckers = [System.Collections.Generic.List[string]]::new()
    foreach ($checker in @('con-leche', 'con-ron', 'leanchecker')) {
        if ((Get-FileHash -LiteralPath $ProofPath -Algorithm SHA256).Hash -cne $proofHash) { throw 'Export changed before checking.' }
        $checkerArguments = if ($checker -eq 'leanchecker') { @('--from-export', $ProofPath) } else {
            @('--verified', "--jobs=$Jobs", "--progress=$ProgressStride", $ProofPath)
        }
        $check = Invoke-Recorded -Name ($Prefix + '-' + $checker) `
            -Executable (Join-Path $ProofSuiteLeanBin ($checker + '.exe')) -Arguments $checkerArguments -ContinueOnFailure
        if ($check.exit_code -ne 0) { $failedCheckers.Add("$checker exit=$($check.exit_code)") }
        if ((Get-FileHash -LiteralPath $ProofPath -Algorithm SHA256).Hash -cne $proofHash) { throw 'Export changed during checking.' }
    }
    if ($failedCheckers.Count -ne 0) { throw ('Export check failed: ' + ($failedCheckers -join '; ')) }
    Write-Host "VERIFIED EXPORT SHA256: $proofHash"
}

function Run-CheckerControl {
    $controlDirectory = Join-Path $runDirectory 'checker-control'
    New-Item -ItemType Directory -Path $controlDirectory -Force | Out-Null
    $controlSource = @'
namespace CheckerControl

theorem add_zero (n : Nat) : n + 0 = n := by rfl

theorem swap_and (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  And.intro h.right h.left

end CheckerControl
'@
    $sourcePath = Join-Path $controlDirectory 'CheckerControl.lean'
    [System.IO.File]::WriteAllText($sourcePath, $controlSource, $utf8)
    if ($DisplaySource) { Write-Host "SOURCE: $sourcePath"; Write-Host $controlSource }
    $null = Invoke-Recorded -Name 'control-compile' -Executable $ProofSuiteLean `
        -Arguments @('-R', $controlDirectory, '-o', (Join-Path $controlDirectory 'CheckerControl.olean'), $sourcePath)
    $controlLeanPath = $env:LEAN_PATH
    try {
        $env:LEAN_PATH = "$controlDirectory;$controlLeanPath"
        $validProof = Join-Path $controlDirectory 'valid-control.ndjson'
        $null = Invoke-Recorded -Name 'control-export' -Executable (Join-Path $ProofSuiteLeanBin 'leanexport.exe') `
            -Arguments @('CheckerControl', '--', 'CheckerControl.add_zero', 'CheckerControl.swap_and') `
            -StdoutPath $validProof -ExportOutput
    } finally { $env:LEAN_PATH = $controlLeanPath }
    Check-Export $validProof 'control-valid'
    # This is only the small control fixture, never the full suite export.
    $lines = [System.IO.File]::ReadAllLines($validProof, $utf8)
    $lastTheoremLine = -1
    for ($index = $lines.Length - 1; $index -ge 0; $index--) {
        if ($lines[$index].StartsWith('{"thm":')) { $lastTheoremLine = $index; break }
    }
    if ($lastTheoremLine -lt 0) { throw 'No theorem record in the control export.' }
    $record = $lines[$lastTheoremLine] | ConvertFrom-Json
    $originalValue = $record.thm.value
    $replacementValue = $record.thm.type
    $record.thm.value = $replacementValue
    $lines[$lastTheoremLine] = $record | ConvertTo-Json -Depth 20 -Compress
    $invalidProof = Join-Path $controlDirectory 'DELIBERATELY-INVALID-control.ndjson'
    [System.IO.File]::WriteAllLines($invalidProof, $lines, $utf8)
    Write-Host "NEGATIVE CONTROL: proof expression $originalValue replaced with type expression $replacementValue."
    foreach ($checker in @('con-leche', 'con-ron')) {
        $rejection = Invoke-Recorded -Name ('control-invalid-' + $checker) `
            -Executable (Join-Path $ProofSuiteLeanBin ($checker + '.exe')) `
            -Arguments @('--verified', "--jobs=$Jobs", "--progress=$ProgressStride", $invalidProof) -ExpectedExit 1
        $rejectionText = [System.IO.File]::ReadAllText($rejection.stdout, $utf8) + [System.IO.File]::ReadAllText($rejection.stderr, $utf8)
        if ($rejectionText -match '(?i)out of memory|memory allocation|panic') { throw "$checker had a runtime failure, not a proof rejection." }
        if ($rejectionText -notmatch 'type mismatch' -or $rejectionText -notmatch 'CheckerControl\.swap_and') {
            throw "$checker did not report the expected damaged-theorem type mismatch."
        }
    }
    $state.negative_control = [ordered]@{
        valid_export = $validProof; valid_sha256 = (Get-FileHash -LiteralPath $validProof -Algorithm SHA256).Hash
        deliberately_invalid_export = $invalidProof
        deliberately_invalid_sha256 = (Get-FileHash -LiteralPath $invalidProof -Algorithm SHA256).Hash
        changed_line = $lastTheoremLine + 1; old_proof_expression = $originalValue; replacement_type_expression = $replacementValue
        both_rejected_with_exit_one = $true
    }
    Save-Results
}

Save-Results
try {
    . (Join-Path $suiteDirectory 'Environment.ps1') -DependenciesRoot $DependenciesRoot -LeanBin $LeanBin -ObjectRoot $buildDirectory
    $state.dependency_root = $ProofSuiteDependencyRoot
    $state.lean_bin = $ProofSuiteLeanBin
    $state.binary_hashes = @(
        foreach ($tool in @('lean', 'lake', 'leanexport', 'leanchecker', 'con-leche', 'con-ron')) {
            $toolPath = Join-Path $ProofSuiteLeanBin ($tool + '.exe')
            if (-not (Test-Path -LiteralPath $toolPath -PathType Leaf)) { throw "Missing tool: $toolPath" }
            [pscustomobject]@{ name = $tool; path = $toolPath; sha256 = (Get-FileHash -LiteralPath $toolPath -Algorithm SHA256).Hash }
        }
    )
    $state.script_hashes = @(
        foreach ($name in @('Verify-Suite.ps1', 'Environment.ps1', 'Generate-Audit.ps1')) {
            $path = Join-Path $suiteDirectory $name
            if (Test-Path -LiteralPath $path) { [pscustomobject]@{ name = $name; sha256 = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash } }
        }
    )
    $versionRecord = Invoke-Recorded -Name 'lean-version' -Executable $ProofSuiteLean -Arguments @('--version')
    $state.lean_version = [System.IO.File]::ReadAllText($versionRecord.stdout, $utf8).Trim()
    if ($state.lean_version -notmatch 'version 4\.36\.0,') { throw "Wrong Lean version: $($state.lean_version)" }
    $mathlibToolchain = [System.IO.File]::ReadAllText((Join-Path $ProofSuiteDependencyRoot 'mathlib\lean-toolchain'), $utf8).Trim()
    if ($mathlibToolchain -cne 'leanprover/lean4:v4.36.0') { throw "Mathlib toolchain mismatch: $mathlibToolchain" }
    $state.mathlib_toolchain = $mathlibToolchain
    $manifestPath = Join-Path $suiteDirectory 'lake-manifest.json'
    $state.manifest_sha256 = (Get-FileHash -LiteralPath $manifestPath -Algorithm SHA256).Hash
    $manifest = [System.IO.File]::ReadAllText($manifestPath, $utf8) | ConvertFrom-Json
    $state.pinned_mathlib_revision = ($manifest.packages | Where-Object name -eq 'mathlib').rev
    if (-not $ControlOnly) {
        $auditGenerator = Join-Path $suiteDirectory 'Generate-Audit.ps1'
        if (Test-Path -LiteralPath $auditGenerator -PathType Leaf) {
            $null = Invoke-Recorded -Name 'generate-audit' -Executable (Get-Process -Id $PID).Path -Arguments @('-NoProfile', '-File', $auditGenerator)
        }
        $modules = @(
            'Shor1994Invalidation', 'ShorGeneratorCertificate', 'ShorPrimorialCertificate',
            'Shor1994Integrated', 'ShorWindowFamily', 'ShorWindowSourceBridge',
            'LeanFiberVariance', 'LeanFourierParseval', 'LeanFiberFourier',
            'LeanFourierNormalization', 'LeanMeasurementNoGo', 'LeanGraphCopies',
            'LeanFiniteCopyNoGo', 'Shor2AdicTorsionHierarchy', 'Shor2AdicQFTBridge',
            'ShorArithmeticStrengthening', 'Shor2AdicMasterBridge', 'ShorResidueWorkspace',
            'ShorSuite', 'AxiomAudit'
        )
        foreach ($module in $modules) {
            $sourcePath = Join-Path $suiteDirectory ($module + '.lean')
            if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) { throw "Missing source: $sourcePath" }
            $sourceHash = (Get-FileHash -LiteralPath $sourcePath -Algorithm SHA256).Hash
            if ($DisplaySource) { Write-Host "SOURCE: $sourcePath"; Show-TextFile $sourcePath }
            $objectPath = Join-Path $buildDirectory ($module + '.olean')
            $compile = Invoke-Recorded -Name ('compile-' + $module) -Executable $ProofSuiteLean `
                -Arguments @('-R', $suiteDirectory, '-o', $objectPath, $sourcePath)
            if ((Get-FileHash -LiteralPath $sourcePath -Algorithm SHA256).Hash -cne $sourceHash) { throw "Source changed during compilation: $module" }
            if (-not (Test-Path -LiteralPath $objectPath -PathType Leaf)) { throw "Missing object: $objectPath" }
            $warnings = 0; $errors = 0
            foreach ($logPath in @($compile.stdout, $compile.stderr)) {
                foreach ($line in [System.IO.File]::ReadLines($logPath, $utf8)) {
                    $warnings += [regex]::Matches($line, '\bwarning:').Count
                    $errors += [regex]::Matches($line, '\berror:').Count
                }
            }
            $compiledModules.Add([pscustomobject]@{
                module = $module; source = $sourcePath; source_sha256 = $sourceHash
                object = $objectPath; object_sha256 = (Get-FileHash -LiteralPath $objectPath -Algorithm SHA256).Hash
                exit_code = $compile.exit_code; warnings = $warnings; errors = $errors
            })
            Save-Results
            if ($errors -ne 0) { throw "Compiler reported errors for $module" }
        }
        if (-not $DeclarationsPath) {
            $DeclarationsPath = Join-Path $suiteDirectory 'declarations.json'
            if (-not (Test-Path -LiteralPath $DeclarationsPath -PathType Leaf)) { $DeclarationsPath = Join-Path $suiteDirectory 'declarations.txt' }
        }
        $DeclarationsPath = (Resolve-Path -LiteralPath $DeclarationsPath -ErrorAction Stop).Path
        $names = @(Read-RootNames $DeclarationsPath)
        $exportArguments = @('ShorSuite', '--') + $names
        $commandLength = ((Join-Path $ProofSuiteLeanBin 'leanexport.exe').Length + 3) + (($exportArguments | ForEach-Object { $_.Length + 3 } | Measure-Object -Sum).Sum)
        if ($commandLength -ge 32000) { throw "Export command length $commandLength exceeds the Windows process command limit." }
        $proofPath = Join-Path $runDirectory 'suite.ndjson'
        $null = Invoke-Recorded -Name 'suite-export' -Executable (Join-Path $ProofSuiteLeanBin 'leanexport.exe') `
            -Arguments $exportArguments -StdoutPath $proofPath -ExportOutput
        if ((Get-Item -LiteralPath $proofPath).Length -eq 0) { throw 'Empty suite export.' }
        $state.export = [ordered]@{
            module = 'ShorSuite'; root_count = $names.Count; declaration_list = $DeclarationsPath
            declaration_list_sha256 = (Get-FileHash -LiteralPath $DeclarationsPath -Algorithm SHA256).Hash
            path = $proofPath; bytes = (Get-Item -LiteralPath $proofPath).Length
            sha256 = (Get-FileHash -LiteralPath $proofPath -Algorithm SHA256).Hash
            command_length_estimate = $commandLength
        }
        Save-Results
        Check-Export $proofPath 'suite'
        foreach ($record in $compiledModules) {
            if ((Get-FileHash -LiteralPath $record.source -Algorithm SHA256).Hash -cne $record.source_sha256) { throw "Source changed after compilation: $($record.module)" }
        }
        $state.full_suite_checked = $true
    }
    if ($RunNegativeControl -or $ControlOnly) { Run-CheckerControl }
    $state.status = 'passed'
    $state.completed_utc = [DateTimeOffset]::UtcNow.ToString('o')
    $state.warning_count = 0
    $state.error_count = 0
    foreach ($compiled in $compiledModules) {
        $state.warning_count += $compiled.warnings
        $state.error_count += $compiled.errors
    }
    Save-Results
    if ($ControlOnly) { Write-Host 'PASS: Small checker control only. The suite was not checked by this run.' }
    else { Write-Host 'PASS: All modules compiled; con-leche, con-ron and the Lean kernel accepted the same suite export.' }
    Write-Host "RESULTS: $resultsFile"
} catch {
    $state.status = 'failed'
    $state.completed_utc = [DateTimeOffset]::UtcNow.ToString('o')
    $state.error_message = $_.Exception.Message
    Save-Results
    Write-Host "FAILED: $($_.Exception.Message)"
    Write-Host "RESULTS: $resultsFile"
    exit 1
} finally {
    $env:Path = $savedPath
    $env:LEAN_PATH = $savedLeanPath
}
