#!/usr/bin/env bash
set -euo pipefail

# Execute only as the child of the accepted Slurm guard inside its srun step.
stafford_run=$1
cd "$stafford_run/project"
stafford_curl="$stafford_run/bootstrap/curl-runtime"
test -x "$stafford_curl/curl"
export CURL_CA_BUNDLE="$stafford_curl/ca-certificates.crt"
export PATH="$stafford_curl:$PATH"
"$stafford_curl/curl" --version | tee "$stafford_run/bootstrap/curl-version.log"
grep -Eq '^curl [0-9]' "$stafford_run/bootstrap/curl-version.log"
grep -Fq 'libcurl/' "$stafford_run/bootstrap/curl-version.log"
export ELAN_HOME="$stafford_run/elan"
export XDG_CACHE_HOME="$stafford_run/xdg-cache"
export MATHLIB_CACHE_DIR="$stafford_run/mathlib-cache"
export GIT_TERMINAL_PROMPT=0
mkdir -p "$ELAN_HOME" "$XDG_CACHE_HOME" "$MATHLIB_CACHE_DIR"
stafford_elan="$stafford_run/bootstrap/elan"
stafford_toolchain=leanprover/lean4:v4.35.0-rc3
stafford_manifest=29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc
test "$(cat lean-toolchain)" = "$stafford_toolchain"
test "$(sha256sum lake-manifest.json | cut -d ' ' -f1)" = "$stafford_manifest"

if ! test -x "$ELAN_HOME/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean"; then
  "$stafford_elan" toolchain install "$stafford_toolchain"
fi
stafford_prefix=$("$stafford_elan" run "$stafford_toolchain" lean --print-prefix)
export PATH="$stafford_prefix/bin:$PATH"
test "$(lean --githash)" = 470d5ce1400764999581fd26d5d72b00d990b0f4
lean --version
lake update
test "$(sha256sum lake-manifest.json | cut -d ' ' -f1)" = "$stafford_manifest"
python3 - <<'PY'
import json, subprocess
from pathlib import Path
manifest = json.loads(Path('lake-manifest.json').read_text())
for package in manifest['packages']:
    path = Path(manifest['packagesDir']) / package['name']
    head = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    if head != package['rev']:
        raise SystemExit(f"Package pin mismatch: {package['name']}: {head}")
    print(f"PIN_OK {package['name']} {head}", flush=True)
PY
lake exe cache get
test "$(sha256sum lake-manifest.json | cut -d ' ' -f1)" = "$stafford_manifest"
lake build Stafford38.Geometry.SameWitness.CommonOpen
lake env lean --trust=0 -M8000 tests/SameWitness/CommonOpenConsumer.lean
printf 'BOOTSTRAP_AND_COMMON_OPEN_PASS\n'
