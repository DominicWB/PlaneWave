#!/usr/bin/env bash
# Elaborates AxiomCheck.lean (after `lake build`) and checks that every axiom report lists only
# propext, Classical.choice and Quot.sound. Writes the full output to axiom_report.txt.
# Usage, from the project root:  bash scripts/check_axioms.sh
cd "$(dirname "$0")/.." || exit 1
lake env lean AxiomCheck.lean > axiom_report.txt 2>&1
lean_exit=$?
# long reports are wrapped over several lines: join the lines before reading them
tr '\n' ' ' < axiom_report.txt | grep -o "'[^ ]*' depends on axioms: \[[^]]*\]" > axiom_reports.txt
reports=$(wc -l < axiom_reports.txt)
none=$(tr '\n' ' ' < axiom_report.txt | grep -o "'[^ ]*' does not depend on any axioms" | wc -l)
bad=$(awk -F'depends on axioms: ' '{
  ax = $2; gsub(/[][]/, "", ax); n = split(ax, a, ",");
  for (i = 1; i <= n; i++) { x = a[i]; gsub(/^ +| +$/, "", x);
    if (x != "" && x != "propext" && x != "Classical.choice" && x != "Quot.sound") print $1 ": " x } }' axiom_reports.txt)
errors=$(grep -c ': error' axiom_report.txt)
nbad=0; [ -n "$bad" ] && nbad=$(printf '%s\n' "$bad" | wc -l)
total=$((reports + none))
echo "axiom reports: $total   nonstandard: $nbad   errors: $errors   lean exit code: $lean_exit"
[ -n "$bad" ] && printf '  %s\n' "$bad"
if [ "$lean_exit" -ne 0 ] || [ "$errors" -ne 0 ] || [ "$nbad" -ne 0 ] || [ "$total" -eq 0 ]; then
  echo "FAILED (see axiom_report.txt)"; exit 1
fi
echo "OK: every report lists only propext, Classical.choice and Quot.sound"
