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
python3 - <<'CHECK'
import hashlib,json,re,subprocess
from pathlib import Path
metadata=json.loads(Path('../T34-T36-scluster-frozen-inputs-20261003.json').read_text())
for name,digest in metadata['hashes'].items():
 if hashlib.sha256(Path(name).read_bytes()).hexdigest()!=digest:
  raise SystemExit('Frozen input changed: '+name)
out=Path('../logs/T34-T36-scluster-stages');out.mkdir(exist_ok=False)
for label,module,consumer,target in metadata['pairs']:
 for kind,argv in [('module',['lake','build',module]),('consumer',['lake','env','lean','--trust=0','-M8000',consumer])]:
  log=out/f'{label}-{kind}.log'
  with log.open('w') as stream: result=subprocess.run(argv,stdout=stream,stderr=subprocess.STDOUT)
  (out/f'{label}-{kind}.exit').write_text(str(result.returncode)+'\n')
  print(label,kind,'exit',result.returncode,flush=True)
  if result.returncode:
   print('\n'.join(log.read_text().splitlines()[-45:]),flush=True);raise SystemExit(result.returncode)
  if kind=='consumer':
   text=log.read_text();m=re.search("'"+re.escape(target)+"' depends on axioms:\s*\[(.*?)\]",text,re.S)
   if not m or {x.strip() for x in m[1].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
    raise SystemExit('Missing literal consumer or forbidden axioms: '+target)
   print(text,flush=True)
 print(label+'_MODULE_AND_LITERAL_CONSUMER_PASS',flush=True)
CHECK
