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
python3 - <<'HASHCHECK'
import hashlib
from pathlib import Path
expected = {
 'Stafford38/Geometry/SameWitness/CommonOpen.lean': '8656c5e830bd4326493a866a7272f939aa5dcc0cedd0416a59a755a3fe10fa43',
 'Stafford38/Geometry/SameWitness/CommonOpenArc.lean': '527a8716c913d71245d1affebc0780290f11dc1eba827fda682312f2122f140f',
 'Stafford38/Geometry/SameWitness/CommonOpenPositions.lean': '102983348a569bca588f13d7afb03f3567db4447c20f0bc614034d5b4bbf93a2',
 'tests/SameWitness/CommonOpenPositionsConsumer.lean': '20d586839334f2552e67bdba86630691f95d3fcaecb35424d4bbc3262b039a97',
}
for name, digest in expected.items():
 if hashlib.sha256(Path(name).read_bytes()).hexdigest() != digest:
  raise SystemExit('Frozen input changed: ' + name)
print('T34 frozen positions inputs checked', flush=True)
HASHCHECK
lake build Stafford38.Geometry.SameWitness.CommonOpenPositions
lake env lean --trust=0 -M8000 tests/SameWitness/CommonOpenPositionsConsumer.lean > ../logs/T34-cluster-positions-consumer.log 2>&1
cat ../logs/T34-cluster-positions-consumer.log
python3 - <<'AXIOMS'
import re
from pathlib import Path
text=Path('../logs/T34-cluster-positions-consumer.log').read_text()
m=re.search("'commonOpenPositionData_of_arc_consumer' depends on axioms:\\s*\\[(.*?)\\]",text,re.S)
if not m or {x.strip() for x in m[1].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
 raise SystemExit('Missing literal T34 positions consumer or forbidden axioms')
print('T34_POSITIONS_MODULE_AND_LITERAL_CONSUMER_PASS')
AXIOMS
