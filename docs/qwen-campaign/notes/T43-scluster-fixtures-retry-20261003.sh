#!/bin/bash
set -euo pipefail
stafford_run=/home/ert/stafford38-campaign/linux-bootstrap-20261003-0815
export ELAN_HOME="$stafford_run/elan"
export XDG_CACHE_HOME="$stafford_run/xdg-cache"
export MATHLIB_CACHE_DIR="$stafford_run/mathlib-cache"
export CURL_CA_BUNDLE="$stafford_run/bootstrap/curl-runtime/ca-certificates.crt"
export PATH="$ELAN_HOME/toolchains/leanprover--lean4---v4.35.0-rc3/bin:$stafford_run/bootstrap/curl-runtime:$PATH"
cd "$stafford_run/project"
test "$(sha256sum tests/dependency-guard-fixtures/test_behavior.py | cut -d ' ' -f1)" = 0fd88d77f2bf3c1dc2d99feecde793ccdc8c69375c25be9d10cb7a9cbe351271
test "$(lean --githash)" = 470d5ce1400764999581fd26d5d72b00d990b0f4
test "$(sha256sum lake-manifest.json | cut -d ' ' -f1)" = 29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc
python3 tests/dependency-guard-fixtures/test_toolchain_resolution.py
python3 tests/dependency-guard-fixtures/test_behavior.py
