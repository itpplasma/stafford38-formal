#!/bin/bash
set -euo pipefail
stafford_run=/home/ert/stafford38-campaign/linux-bootstrap-20261003-0815
export ELAN_HOME="$stafford_run/elan"
export XDG_CACHE_HOME="$stafford_run/xdg-cache"
export MATHLIB_CACHE_DIR="$stafford_run/mathlib-cache"
export CURL_CA_BUNDLE="$stafford_run/bootstrap/curl-runtime/ca-certificates.crt"
export PATH="$ELAN_HOME/toolchains/leanprover--lean4---v4.35.0-rc3/bin:$stafford_run/bootstrap/curl-runtime:$PATH"
cd "$stafford_run/project"
test "$(sha256sum Stafford38/Geometry/SameWitness/CommonOpenEtale.lean | cut -d ' ' -f1)" = f30d41e2a4db4463c39925858cc8c3d03ed4d11c8d921149cad11f4635eedc93
test "$(sha256sum tests/SameWitness/CommonOpenEtaleConsumer.lean | cut -d ' ' -f1)" = 04cf7171123196848753417fdffa3cdb3eb894fa2f2ca7b4ee8b584eae89131d
test "$(lean --githash)" = 470d5ce1400764999581fd26d5d72b00d990b0f4
test "$(sha256sum lake-manifest.json | cut -d ' ' -f1)" = 29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc
lake build Stafford38.Geometry.SameWitness.CommonOpenArc Stafford38.Geometry.SameWitness.CommonOpenEtale
lake env lean --trust=0 -M8000 tests/SameWitness/CommonOpenEtaleConsumer.lean > ../logs/T35-cluster-consumer.log 2>&1
cat ../logs/T35-cluster-consumer.log
python3 - <<'AXIOMS'
import re
from pathlib import Path
text=Path('../logs/T35-cluster-consumer.log').read_text()
target="Stafford38.Geometry.SameWitness.CommonOpenEtaleConsumer.nonempty_commonOpenEtaleData_consumer"
m=re.search("'"+re.escape(target)+"' depends on axioms:\s*\[(.*?)\]",text,re.S)
if not m or {x.strip() for x in m[1].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
 raise SystemExit('Missing literal T35 consumer or forbidden axioms')
print('T35_MODULE_AND_LITERAL_CONSUMER_PASS')
AXIOMS
