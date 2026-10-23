#!/usr/bin/env bash
# Builds the library (all modules) and runs the axiom check. Output of the build: build_log.txt.
# Usage, from the project root:  bash scripts/build.sh
cd "$(dirname "$0")/.." || exit 1
t0=$(date +%s)
lake build 2>&1 | tee build_log.txt
build_exit=${PIPESTATUS[0]}
echo "lake build exit code: $build_exit   time: $(( ($(date +%s) - t0) / 60 )) min"
[ "$build_exit" -ne 0 ] && { echo "build FAILED (see build_log.txt)"; exit 1; }
exec bash scripts/check_axioms.sh
