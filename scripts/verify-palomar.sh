#!/usr/bin/env bash
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

tool_root=.lake/palomar-tools
bin_root=$tool_root/bin
config=${1:-comparator.json}
case "$config" in
  comparator.json) challenge=Challenge; solution=Solution; suffix= ;;
  comparator-fixed-source.json) challenge=FixedSourceChallenge; solution=FixedSourceSolution; suffix=-fixed-source ;;
  *) echo "unsupported Comparator configuration: $config" >&2; exit 2 ;;
esac
log_dir=.lake/verification
mkdir -p "$log_dir"

for tool in comparator lean4export nanoda landrun; do
  if [ ! -x "$bin_root/$tool" ]; then
    echo "missing $bin_root/$tool; run scripts/bootstrap-palomar-tools.sh" >&2
    exit 1
  fi
done
bin_root=$(cd "$bin_root" && pwd)

expected_revisions='Comparator 575674928e239f5bc452aab72d1dd7b0f1326494
ComparatorLean leanprover/lean4:v4.34.0-rc1
lean4export 15f6055e299ad5b89345e533cc2192f4cc00f659
NanoDa 68d5ca9db226849b41a6fff59d796ff19d0a8840
Landrun 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
Lean leanprover/lean4:v4.33.0'
actual_revisions=$(cat "$tool_root/revisions.txt")
if [ "$actual_revisions" != "$expected_revisions" ]; then
  echo "Palomar tool revision record does not match the release verifier" >&2
  exit 1
fi

python3 - "$config" <<'PY'
import json
import sys
from pathlib import Path

config_path = sys.argv[1]
config = json.loads(Path(config_path).read_text(encoding="utf-8"))
expected = {
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["Stafford38Challenge.universalStatement"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": True,
}
if config_path == "comparator-fixed-source.json":
    expected.update(challenge_module="FixedSourceChallenge",
                    solution_module="FixedSourceSolution",
                    theorem_names=["Stafford38FixedSourceChallenge.universalFixedSourceStatement"])
if config != expected:
    raise SystemExit("comparator.json does not match the audited Palomar configuration")
print("Palomar configuration: exact theorem, three permitted axioms, NanoDa enabled")
PY

lake build "$challenge" >"$log_dir/challenge$suffix-build.log" 2>&1
lake build "$solution" >"$log_dir/solution$suffix-build.log" 2>&1
bash scripts/check-import-closure.sh "$challenge"
bash scripts/check-import-closure.sh "$solution"

PALOMAR_LANDRUN_BIN=$bin_root/landrun \
COMPARATOR_LANDRUN=$repo_root/scripts/landrun-wrapper.sh \
COMPARATOR_LEAN4EXPORT=$bin_root/lean4export \
COMPARATOR_NANODA=$bin_root/nanoda \
lake env "$bin_root/comparator" "$config" \
  >"$log_dir/comparator$suffix.log" 2>&1

grep -Fq 'nanoda kernel accepts the solution' "$log_dir/comparator$suffix.log"
grep -Fq 'Lean default kernel accepts the solution' "$log_dir/comparator$suffix.log"
grep -Fq 'Your solution is okay!' "$log_dir/comparator$suffix.log"

echo "Palomar Comparator, NanoDa, and Lean kernel verification passed"
