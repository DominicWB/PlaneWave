# Builds the library (all modules) and runs the axiom check. Output of the build: build_log.txt.
# Usage, from the project root:  .\scripts\build.ps1
Set-Location (Split-Path -Parent $PSScriptRoot)
$t0 = Get-Date
lake build 2>&1 | Tee-Object build_log.txt
$buildExit = $LASTEXITCODE
Write-Output ("lake build exit code: {0}   time: {1:N0} min" -f $buildExit, ((Get-Date) - $t0).TotalMinutes)
if ($buildExit -ne 0) { Write-Output 'build FAILED (see build_log.txt)'; exit 1 }
& "$PSScriptRoot\check_axioms.ps1"
exit $LASTEXITCODE
