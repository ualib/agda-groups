#!/usr/bin/env bash
# Check every module of the spike afresh, in dependency order, each under
# --profile=definitions, and print each module's evaluation profile.
# Usage, inside `nix develop` at the repository root: bash spike/check.sh
# The modules are checked under the library's flags (each carries
# --without-K --exact-split --safe) with the heap limit of `make check`.
set -u
modules=(
  Spike/Finite
  Spike/Counting
  Spike/SmallExamples
  Spike/A5/Common
  Spike/A5/Given
  Spike/A5/IndexCost
  Spike/Constructions
  Spike/ConstructionExamples
  Spike/SubgroupEnumeration
  Spike/TableGroups
  Spike/A4Examples
  Spike/TableGroupExamples
  Spike/Sylow
  Spike/SylowExamples
  Spike/Rules
  Spike/RulesExamples
  Spike/Oracle
  Spike/Setoid
  Spike/Generated
  Spike/A5/Setoid
  Spike/A5/SetoidNaive
  Spike/A5/Cyclic
  Spike/SetoidRules
  Spike/SetoidRulesExamples
)
status=0
log=$(mktemp)
for m in "${modules[@]}"; do
  if bash spike/time.sh "$m" --profile=definitions > "$log" 2>&1; then :; else status=1; fi
  grep -v '^ *Checking \|^Miscellaneous\|^Total' "$log"
done
rm -f "$log"
exit $status
