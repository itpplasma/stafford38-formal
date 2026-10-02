#!/usr/bin/env bash
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

config=${1:-comparator.json}
log_path=${2:-.lake/verification/comparator.log}
python3 scripts/check-palomar-policy.py --config-only "$config"

expected_toolchain=leanprover/lean4:v4.35.0-rc3
actual_toolchain=$(tr -d '\r\n' < lean-toolchain)
if [ "$actual_toolchain" != "$expected_toolchain" ]; then
  echo "unexpected Lean toolchain $actual_toolchain" >&2
  exit 1
fi
lean_bin=$(ELAN_TOOLCHAIN="$expected_toolchain" elan which lean)
bin_root=$(cd -- "$(dirname -- "$lean_bin")" && pwd)
bwrap_bin=$(command -v bwrap || true)
if [ -z "$bwrap_bin" ] || [ ! -x "$bwrap_bin" ]; then
  echo "bwrap is required; run scripts/bootstrap-palomar-tools.sh" >&2
  exit 1
fi
bwrap_bin=$(cd -- "$(dirname -- "$bwrap_bin")" && pwd)/$(basename -- "$bwrap_bin")
bwrap_version=$("$bwrap_bin" --version)
if [ "$bwrap_version" != "bubblewrap 0.12.0" ]; then
  echo "expected official Palomar bubblewrap 0.12.0, found $bwrap_version" >&2
  exit 1
fi
log_dir=$(dirname -- "$log_path")
mkdir -p "$log_dir"
protected_config=$(mktemp "$log_dir/palomar-protected.XXXXXX")
python3 - "$config" "$protected_config" "$bin_root" <<'PY'
import json
import sys
from pathlib import Path

source, destination, tool_bin = sys.argv[1:]
submitted = json.loads(Path(source).read_text(encoding="utf-8"))
protected = {
    "challenge_module": submitted["challenge_module"],
    "solution_module": submitted["solution_module"],
    "theorem_names": list(submitted["theorem_names"]),
    "definition_names": list(submitted.get("definition_names", [])),
    "permitted_axioms": list(submitted["permitted_axioms"]),
    "external_kernels": {
        "nanoda": [str(Path(tool_bin) / "nanoda_bin")],
        "con-ron": [str(Path(tool_bin) / "con-ron")],
    },
}
Path(destination).write_text(json.dumps(protected, indent=2) + "\n", encoding="utf-8")
PY

printf 'local protected config sha256 %s\n' "$(sha256sum "$protected_config" | cut -d ' ' -f1)"
printf 'local bwrap %s\n' "$bwrap_version"

set +e
PATH="$bin_root:$PATH" \
ELAN_TOOLCHAIN="$expected_toolchain" \
COMPARATOR_BWRAP="$bwrap_bin" \
"$bin_root/lake" comparator --config "$protected_config" >"$log_path" 2>&1
status=$?
set -e
if [ "$status" -ne 0 ]; then
  tail -n 60 "$log_path"
  echo "lake comparator rejected or could not verify the configured solution (exit $status); full log: $log_path" >&2
  exit "$status"
fi
for marker in \
  'con-ron kernel accepts the solution' \
  'nanoda kernel accepts the solution' \
  'Lean default kernel accepts the solution' \
  'Your solution is okay!'; do
  if ! grep -Fxq "$marker" "$log_path"; then
    echo "Comparator exited successfully without required marker: $marker" >&2
    exit 1
  fi
done
printf 'Local source-mode Comparator check passed (not a Palomar service-runner receipt).\n'
