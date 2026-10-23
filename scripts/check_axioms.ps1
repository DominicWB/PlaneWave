# Elaborates AxiomCheck.lean (after `lake build`) and checks that every axiom report lists only
# propext, Classical.choice and Quot.sound. Writes the full output to axiom_report.txt.
# Usage, from the project root:  .\scripts\check_axioms.ps1
Set-Location (Split-Path -Parent $PSScriptRoot)
lake env lean AxiomCheck.lean 2>&1 | Out-File -Encoding utf8 axiom_report.txt
$leanExit = $LASTEXITCODE
$text = Get-Content -Raw axiom_report.txt
$std = @('propext', 'Classical.choice', 'Quot.sound')
$reports = [regex]::Matches($text, "'(\S+)' depends on axioms: \[([^\]]*)\]")
$noAxioms = [regex]::Matches($text, "'(\S+)' does not depend on any axioms").Count
$bad = @()
foreach ($m in $reports) {
  $axs = $m.Groups[2].Value -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ -ne '' }
  $extra = @($axs | Where-Object { $std -notcontains $_ })
  if ($extra.Count -gt 0) { $bad += "$($m.Groups[1].Value): $($extra -join ', ')" }
}
$errors = [regex]::Matches($text, ': error').Count
$total = $reports.Count + $noAxioms
Write-Output "axiom reports: $total   nonstandard: $($bad.Count)   errors: $errors   lean exit code: $leanExit"
$bad | ForEach-Object { Write-Output "  $_" }
if ($leanExit -ne 0 -or $errors -gt 0 -or $bad.Count -gt 0 -or $total -eq 0) {
  Write-Output 'FAILED (see axiom_report.txt)'
  exit 1
}
Write-Output 'OK: every report lists only propext, Classical.choice and Quot.sound'
