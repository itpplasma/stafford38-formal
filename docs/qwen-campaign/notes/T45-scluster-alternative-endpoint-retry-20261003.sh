#!/bin/bash
set -euo pipefail
stafford_run=/home/ert/stafford38-campaign/linux-bootstrap-20261003-0815
export ELAN_HOME="$stafford_run/elan"
export XDG_CACHE_HOME="$stafford_run/xdg-cache"
export MATHLIB_CACHE_DIR="$stafford_run/mathlib-cache"
export CURL_CA_BUNDLE="$stafford_run/bootstrap/curl-runtime/ca-certificates.crt"
export PATH="$ELAN_HOME/toolchains/leanprover--lean4---v4.35.0-rc3/bin:$stafford_run/bootstrap/curl-runtime:$PATH"
cd "$stafford_run/project"
test "$(lean --githash)" = 470d5ce1400764999581fd26d5d72b00d990b0f4
test "$(sha256sum lake-manifest.json | cut -d ' ' -f1)" = 29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc
test "$(sha256sum Stafford38/Geometry/AlternativeAsymptoticConormal.lean | cut -d ' ' -f1)" = 83f57da539b4a3f0b7bcda00604907c33f3eef5aa96ae7a367776aa62736f8dd
lake build Stafford38.Geometry.AlternativeAsymptoticConormal
printf 'ALTERNATIVE_GEOMETRIC_ENDPOINT_MODULE_PASS\n'
