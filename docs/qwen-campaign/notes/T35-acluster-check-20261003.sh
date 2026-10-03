#!/bin/bash
set -euo pipefail
stafford_run=/home/ert/stafford38-campaign/linux-bootstrap-20261003-0815
export ELAN_HOME="$stafford_run/elan"
export XDG_CACHE_HOME="$stafford_run/xdg-cache"
export MATHLIB_CACHE_DIR="$stafford_run/mathlib-cache"
export CURL_CA_BUNDLE="$stafford_run/bootstrap/curl-runtime/ca-certificates.crt"
export PATH="$ELAN_HOME/toolchains/leanprover--lean4---v4.35.0-rc3/bin:$stafford_run/bootstrap/curl-runtime:$PATH"
test "$(sha256sum "$stafford_run/candidate-inputs.tar" | cut -d ' ' -f1)" = dcc4836c5da914fec83b297a67c79a55189a0689375cdcd2cc8fd56365b35b91
mkdir -p "$stafford_run/candidate-inputs"
tar -xf "$stafford_run/candidate-inputs.tar" -C "$stafford_run/candidate-inputs"
tar -xf "$stafford_run/candidate-inputs/base-source.tar" -C "$stafford_run/project"
cp -a "$stafford_run/candidate-inputs/overlay/." "$stafford_run/project/"
cd "$stafford_run/project"
python3 - <<'HASHCHECK'
import hashlib,json
from pathlib import Path
metadata=json.loads(Path('../candidate-inputs/inputs.json').read_text())
for name,expected in metadata['overlay_hashes'].items():
    actual=hashlib.sha256(Path(name).read_bytes()).hexdigest()
    if actual!=expected:raise SystemExit('Candidate source mismatch: '+name)
print(json.dumps({'base_commit':metadata['base_commit'],'patch_sha256':metadata['worktree_patch_sha256'],'source_overlay_checked':len(metadata['overlay_hashes'])}),flush=True)
HASHCHECK
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
