#!/usr/bin/env bash
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

config=${1:-comparator.json}
case "$config" in
  comparator.json) challenge=Challenge; solution=Solution; suffix= ;;
  comparator-fixed-source.json) challenge=FixedSourceChallenge; solution=FixedSourceSolution; suffix=-fixed-source ;;
  comparator-alternative.json) challenge=Challenge; solution=AlternativeSolution; suffix=-alternative ;;
  comparator-alternative-fixed-source.json) challenge=FixedSourceChallenge; solution=AlternativeFixedSourceSolution; suffix=-alternative-fixed-source ;;
  *) echo "unsupported Palomar configuration: $config" >&2; exit 2 ;;
esac

# Fail on pin/config drift before building any challenge or solution modules.
python3 scripts/check-palomar-policy.py
bash scripts/bootstrap-palomar-tools.sh
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0-rc3
lean_bin=$(elan which lean)
bin_root=$(cd -- "$(dirname -- "$lean_bin")" && pwd)
export PATH="$bin_root:$PATH"

log_dir=.lake/verification
mkdir -p "$log_dir"
lake build "$challenge" >"$log_dir/challenge$suffix-build.log" 2>&1
lake build "$solution" >"$log_dir/solution$suffix-build.log" 2>&1
bash scripts/check-import-closure.sh "$challenge"
bash scripts/check-import-closure.sh "$solution"
bash scripts/run-palomar-comparator.sh "$config" "$log_dir/comparator$suffix.log"
