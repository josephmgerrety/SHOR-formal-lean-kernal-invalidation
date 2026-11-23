#Requires -Version 5.1
$ErrorActionPreference = 'Stop'
$auditModules = @(
  'Shor1994Invalidation', 'ShorGeneratorCertificate', 'ShorPrimorialCertificate',
  'Shor1994Integrated', 'ShorWindowFamily', 'ShorWindowSourceBridge',
  'LeanFiberVariance', 'LeanFourierParseval', 'LeanFiberFourier',
  'LeanFourierNormalization', 'LeanMeasurementNoGo', 'LeanGraphCopies',
  'LeanFiniteCopyNoGo', 'Shor2AdicTorsionHierarchy', 'Shor2AdicMasterBridge',
  'Shor2AdicQFTBridge', 'ShorArithmeticStrengthening', 'ShorResidueWorkspace'
)
$declarationRows = [System.Collections.Generic.List[object]]::new()
$privateRows = [System.Collections.Generic.List[object]]::new()
foreach ($moduleName in $auditModules) {
  $sourcePath = Join-Path $PSScriptRoot ($moduleName + '.lean')
  $sourceLines = [System.IO.File]::ReadAllLines($sourcePath)
  $namespaceName = $null
  for ($lineIndex = 0; $lineIndex -lt $sourceLines.Length; $lineIndex++) {
    $sourceLine = $sourceLines[$lineIndex]
    if ($sourceLine -match '^namespace\s+([^\s]+)\s*$') {
      if ($null -ne $namespaceName) { throw "Nested namespace requires explicit handling: $sourcePath" }
      $namespaceName = $Matches[1]
    }
    if ($sourceLine -match '^(private\s+)?(theorem|def|abbrev|structure|lemma)\s+([^\s(:]+)') {
      if ($null -eq $namespaceName) { throw "Missing namespace in $sourcePath" }
      $isPrivate = -not [string]::IsNullOrWhiteSpace($Matches[1])
      $kindName = $Matches[2]
      $localName = $Matches[3]
      $row = [pscustomobject]@{
        name = $namespaceName + '.' + $localName
        module = $moduleName
        kind = $kindName
        line = $lineIndex + 1
        private = $isPrivate
      }
      if ($isPrivate) { $privateRows.Add($row) } else { $declarationRows.Add($row) }
    }
  }
}
$allNames = @($declarationRows | ForEach-Object { $_.name })
if (@($allNames | Select-Object -Unique).Count -ne $allNames.Count) { throw 'Duplicate declaration name' }
$plainUtf8 = [System.Text.UTF8Encoding]::new($false)
[System.IO.File]::WriteAllText((Join-Path $PSScriptRoot 'declarations.json'),
  (ConvertTo-Json -InputObject @($declarationRows.ToArray()) -Depth 5), $plainUtf8)
[System.IO.File]::WriteAllLines((Join-Path $PSScriptRoot 'declarations.txt'), [string[]]$allNames, $plainUtf8)
[System.IO.File]::WriteAllText((Join-Path $PSScriptRoot 'private-declarations.json'),
  (ConvertTo-Json -InputObject @($privateRows.ToArray()) -Depth 5), $plainUtf8)
$auditLines = @('import ShorSuite', '') + @($allNames | ForEach-Object { '#print axioms ' + $_ })
[System.IO.File]::WriteAllLines((Join-Path $PSScriptRoot 'AxiomAudit.lean'), [string[]]$auditLines, $plainUtf8)
Write-Output ('Indexed public declarations: ' + $allNames.Count)
Write-Output ('Private helper declarations: ' + $privateRows.Count)
Write-Output ('Theorems: ' + @($declarationRows | Where-Object { $_.kind -in @('theorem', 'lemma') }).Count)
Write-Output 'Generated declarations.json, declarations.txt, private-declarations.json and AxiomAudit.lean'
