#Requires -Version 7.0
$ErrorActionPreference = 'Stop'
$latest = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'verification\latest-verification.json') -Raw | ConvertFrom-Json
$run = Get-Content -LiteralPath $latest.results_file -Raw | ConvertFrom-Json
if ($run.status -ne 'passed' -or -not $run.full_suite_checked) { throw 'The complete external-checker run has not passed.' }
$auditCommand = @($run.commands | Where-Object { $_.name -eq 'compile-AxiomAudit' })
if ($auditCommand.Count -ne 1 -or $auditCommand[0].exit_code -ne 0) { throw 'Missing successful complete axiom audit.' }
$auditText = [System.IO.File]::ReadAllText($auditCommand[0].stdout)
$pattern = "(?m)^'(?<name>[^']+)' (?:(?:depends on axioms:\s*\[(?<axioms>[^\]]*)\])|(?<none>does not depend on any axioms))"
$reports = [regex]::Matches($auditText, $pattern)
$allowed = @('propext', 'Classical.choice', 'Quot.sound')
$names = @(Get-Content -LiteralPath (Join-Path $PSScriptRoot 'declarations.txt'))
$observed = [System.Collections.Generic.List[string]]::new()
$dependencies = [System.Collections.Generic.HashSet[string]]::new()
foreach ($report in $reports) {
  $name = $report.Groups['name'].Value
  $observed.Add($name)
  if ($report.Groups['axioms'].Success) {
    foreach ($axiomName in ($report.Groups['axioms'].Value -split ',')) {
      $axiomName = $axiomName.Trim()
      if (-not $axiomName) { continue }
      if ($axiomName -notin $allowed) { throw "Unpermitted dependency in ${name}: $axiomName" }
      $null = $dependencies.Add($axiomName)
    }
  }
}
if ($reports.Count -ne $names.Count) { throw "Expected $($names.Count) reports; received $($reports.Count)." }
if (@($observed | Sort-Object -Unique).Count -ne $names.Count) { throw 'Duplicated axiom reports.' }
if (@(Compare-Object -ReferenceObject $names -DifferenceObject @($observed.ToArray())).Count -ne 0) { throw 'The declaration list and axiom reports differ.' }
$forbiddenPattern = '\b(sorry|admit|native_decide|noncomputable|axiom|unsafe|partial|aesop|library_search)\b|\bClassical\.(choose|choose_spec)\b|\b(exact|apply|simp)\?'
$sourceRows = foreach ($module in $run.modules) {
  $sourceText = [System.IO.File]::ReadAllText($module.source)
  $matchesFound = [regex]::Matches($sourceText, $forbiddenPattern)
  if ($matchesFound.Count -ne 0) { throw "Forbidden source construct in $($module.module): $($matchesFound.Value -join ', ')" }
  $hash = (Get-FileHash -LiteralPath $module.source -Algorithm SHA256).Hash
  if ($hash -cne $module.source_sha256) { throw "Source changed after verification: $($module.module)" }
  [pscustomobject]@{ module = $module.module; sha256 = $hash; forbidden_matches = 0 }
}
$summary = [ordered]@{
  status = 'passed'
  public_declaration_audits = $reports.Count
  public_theorems = @((Get-Content -LiteralPath (Join-Path $PSScriptRoot 'declarations.json') -Raw | ConvertFrom-Json) | Where-Object { $_.kind -in @('theorem','lemma') }).Count
  dependencies = @($dependencies | Sort-Object)
  forbidden_source_matches = 0
  source_hashes_match_checked_build = $true
  sources = @($sourceRows)
  checked_export_sha256 = $run.export.sha256
  verification_results = $latest.results_file
}
$outputPath = Join-Path $PSScriptRoot 'verification\axiom-and-source-audit.json'
[System.IO.File]::WriteAllText($outputPath, ($summary | ConvertTo-Json -Depth 6), [System.Text.UTF8Encoding]::new($false))
Write-Output "PASS: $($reports.Count) declaration axiom reports match the complete root list."
Write-Output ('PERMITTED DEPENDENCIES OBSERVED: ' + ($summary.dependencies -join ', '))
Write-Output 'FORBIDDEN SOURCE CONSTRUCTS: 0'
Write-Output 'ALL FINAL SOURCE HASHES MATCH THE CHECKED BUILD.'
Write-Output "AUDIT: $outputPath"
