#!/bin/bash
set -euo pipefail
stafford_run=/home/ert/stafford38-campaign/linux-bootstrap-20261003-0815
export ELAN_HOME="$stafford_run/elan"
export PATH="$ELAN_HOME/toolchains/leanprover--lean4---v4.35.0-rc3/bin:$PATH"
cd "$stafford_run/project"
test "$(lean --githash)" = 470d5ce1400764999581fd26d5d72b00d990b0f4
test "$(sha256sum lake-manifest.json | cut -d ' ' -f1)" = 29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc
test "$(sha256sum .lake/qwen/T36-chart-prefix.lean | cut -d ' ' -f1)" = a45ce88e367248cf107cbcf36bda3d519ea0d085f02aa62d702b03752cc4de83
lake env lean --trust=0 -M8000 .lake/qwen/T36-chart-prefix.lean
