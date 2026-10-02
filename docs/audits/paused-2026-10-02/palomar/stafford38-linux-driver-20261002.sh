#!/usr/bin/env bash
set -euo pipefail
# Prepared execution contract. Controller supplies the frozen stage and starts it.
source_root=${1:?fresh source directory}
receipt_root=${2:?receipt directory outside source}
extra_gates=${3:-}
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0-rc3
export GIT_CONFIG_GLOBAL=/dev/null
export PATH=/home/ert/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin:/home/ert/.elan/bin:$PATH
mkdir -p "$receipt_root"
cd "$source_root"
manifest="$(dirname -- "$source_root")/source-manifest.json"
stage=initialization
finish() {
  result=$?
  trap - EXIT
  python3 - "$receipt_root" "$result" "$stage" "$manifest" <<'PY'
import datetime,hashlib,json,os,sys
from pathlib import Path
root=Path(sys.argv[1]); manifest=Path(sys.argv[4])
record={'exit_status':int(sys.argv[2]),'last_stage':sys.argv[3],
        'finished_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_tree':json.loads(manifest.read_text())['tree'],
        'log_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in root.glob('*.log') if p.is_file()}}
temporary=root/'terminal.json.tmp'
temporary.write_text(json.dumps(record,indent=2)+'\n')
os.replace(temporary,root/'terminal.json')
PY
  exit "$result"
}
trap finish EXIT
source_check() {
  python3 - "$source_root" "$manifest" <<'PY'
import hashlib,json,sys
from pathlib import Path
root=Path(sys.argv[1]); record=json.loads(Path(sys.argv[2]).read_text())
for item in record['files']:
    path=root/item['path']
    if not path.is_file() or path.is_symlink():
        raise SystemExit('Frozen source changed shape: '+item['path'])
    if bool(path.stat().st_mode & 0o100)!=(item['mode']=='100755'):
        raise SystemExit('Frozen source executable mode changed: '+item['path'])
    if hashlib.sha256(path.read_bytes()).hexdigest()!=item['sha256']:
        raise SystemExit('Frozen source bytes changed: '+item['path'])
print('Frozen tracked source unchanged:',record['tree'])
PY
}
run_stage() {
  stage=$1
  shift
  printf '%s begin %s\n' "$(date -u +%FT%TZ)" "$stage"
  timeout --kill-after=60s 19800s "$@" >"$receipt_root/$stage.log" 2>&1
  printf '%s passed %s\n' "$(date -u +%FT%TZ)" "$stage"
}
source_check >"$receipt_root/source-before.log"
python3 - "$manifest" <<'PY'
import json,re,sys
from pathlib import Path
record=json.loads(Path(sys.argv[1]).read_text())
tests={x['path'] for x in record['files']
       if x['path'].startswith('tests/') and x['path'].endswith('.lean')}
consumer_source=Path('scripts/check-consumers.sh').read_text()
loops=re.findall(r'for source in\s+(.*?)\s*;\s*do',consumer_source,re.S)
listed=set(re.findall(r'tests/[A-Za-z0-9_./-]+\.lean','\n'.join(loops)))
listed.update(re.findall(r'tests/[A-Za-z0-9_./-]+\.lean',Path('scripts/verify.sh').read_text()))
if tests-listed:raise SystemExit('Uncovered retained tests: '+str(sorted(tests-listed)))
print('Consumer coverage inventory:',len(tests),'tracked files')
PY
run_stage source-policy python3 scripts/check-palomar-policy.py
run_stage tooling bash scripts/bootstrap-palomar-tools.sh
run_stage dependency-materialization lake update
source_check >"$receipt_root/source-after-dependencies.log"
run_stage mathlib-cache lake exe cache get
run_stage full-verifier bash scripts/verify.sh
run_stage retained-proof-library lake build proofs
run_stage comparator-main bash scripts/verify-palomar.sh comparator.json
run_stage comparator-fixed-source bash scripts/verify-palomar.sh comparator-fixed-source.json
if [ -n "$extra_gates" ]; then
  sha256sum "$extra_gates" >"$receipt_root/additional-gates.sha256"
  run_stage additional-gates bash "$extra_gates"
fi
source_check >"$receipt_root/source-after-replay.log"
stage=complete
