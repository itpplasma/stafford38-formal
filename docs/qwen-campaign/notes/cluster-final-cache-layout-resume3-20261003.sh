#!/usr/bin/env bash
set -Eeuo pipefail

# Child command for linux-slurm-guard.py inside an accepted srun allocation.
# It resumes the exact drained comparator mount failure after C2 verifier/library PASS,
# reusing its source/cache and creating only a distinct receipt directory.
[[ $# == 2 ]] || { echo "expected RUN_ROOT and FULL_T70_COMMIT" >&2; exit 2; }
run_root=${1:?usage: cluster-final-replay-20261003.sh RUN_ROOT FULL_T70_COMMIT}
source_commit=${2:?usage: cluster-final-replay-20261003.sh RUN_ROOT FULL_T70_COMMIT}
if [[ ! "$source_commit" =~ ^[0-9a-f]{40}$ ]]; then
  echo "refusing non-full lowercase 40-hex T70 commit" >&2
  exit 2
fi
campaign_root=/home/ert/stafford38-campaign
run_root=$(python3 - "$campaign_root" "$run_root" <<'PYROOT'
import sys
from pathlib import Path
try:
    campaign = Path(sys.argv[1]).resolve(strict=True)
    run = Path(sys.argv[2]).resolve(strict=True)
    if not campaign.is_dir() or not run.is_dir() or not run.is_relative_to(campaign) or run == campaign:
        raise ValueError("run root must be an existing directory beneath campaign root")
except (OSError, RuntimeError, ValueError) as error:
    raise SystemExit(f"invalid run root: {error}")
print(run)
PYROOT
) || exit 2
if [[ ! "${SLURM_CLUSTER_NAME:-}" =~ ^(acluster|scluster)$ ||
      ! "${SLURMD_NODENAME:-}" =~ ^node[1-9][0-9]*$ ||
      "${SLURM_CPUS_PER_TASK:-}" != 2 || "${SLURM_NTASKS:-}" != 1 ||
      "${SLURM_JOB_NUM_NODES:-}" != 1 || ! "${SLURM_JOB_ID:-}" =~ ^[0-9]+$ ||
      ! "${SLURM_STEP_ID:-}" =~ ^[0-9]+$ ]]; then
  echo "refusing replay outside one approved two-CPU Slurm task/step" >&2
  exit 2
fi

bootstrap="$run_root/bootstrap"
curl_runtime="$bootstrap/curl-runtime"
elan_home="$run_root/elan"
source_root="$run_root/final-source-guard-repaired"
receipt_root="$run_root/final-receipts-guard-repaired-resume3"
outer_log=${STAFFORD_OUTER_GUARD_LOG:?outer Linux guard log path required}
toolchain=leanprover/lean4:v4.35.0-rc3
lean_commit=470d5ce1400764999581fd26d5d72b00d990b0f4
manifest_sha=29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc
repo=https://github.com/itpplasma/stafford38-formal.git
stage=preflight
started_utc=$(date -u +%FT%TZ)

# Resume ONLY the exact drained bwrap cache-symlink failure after retained build PASS.
python3 - "$run_root" "$source_commit" <<'PYRESUME'
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path(sys.argv[1]);commit=sys.argv[2]
assert commit=='12ae3cc49152672a48a96f13994314b65ae38197'
prior=root/'final-receipts-guard-repaired-resume2'
t=json.loads((prior/'terminal.json').read_text())
g=json.loads((root/'final-C2-resume2-outer-guard.json').read_text())
assert t['source_commit']==commit and t['exit_status']==1 and t['failed_or_last_stage']=='comparator-main'
assert {x['stage']:x['exit_status'] for x in t['stages']}=={'comparator-main':1,'curl-runtime-probe':0,'lean-githash':0,'lean-version':0,'receipt-filesystem-probe':0,'retained-proof-library':0,'timeout-output-probe':0}
assert t['source_manifest_before_sha256']=='2c697217e318b576775dea866ea45e4e53d1ec3964475953bb4dd5070e08a325'
assert g['slurm_job_id']=='3136492' and g['reason']=='finished' and g['command_exit_code']==g['guard_exit_code']==1
assert not g['live_child_pids_at_exit'] and not g['stop_cause'] and g['peak_swap_growth_bytes']==0
assert g['rss_cap_bytes']==8589934592 and g['threads']==2 and g['timeout_seconds']==21600
for name,digest in [('comparator-main.log','09f9084951e9df8ab05ffbfbd7aa6254ec03ff6bb5d66d3407c70d90105bc9ec'),('retained-proof-library.log','ae4cb0eefad61910d6734ba0df4620d6059d6d1dd791439f818a89b13278dd59')]:
 assert hashlib.sha256((prior/name).read_bytes()).hexdigest()==digest
assert (prior/'retained-proof-library.exit').read_text().strip()=='0'
assert "Can't mount on symlink destination "+str(root/'final-source-guard-repaired/.lake') in (prior/'comparator-main.log').read_text()
for stage in ['comparator-fixed-source','comparator-alternative','comparator-alternative-fixed-source']:
 assert not any(prior.glob(stage+'.*')),stage
passed=root/'final-receipts-guard-repaired-resume1'
p=json.loads((passed/'terminal.json').read_text())
assert p['source_commit']==commit and p['source_manifest_before_sha256']==t['source_manifest_before_sha256']
assert (passed/'full-verifier.exit').read_text().strip()=='0'
assert hashlib.sha256((passed/'full-verifier.log').read_bytes()).hexdigest()=='acfe9dcd8e48105289ebd6555fe90a6c85043ad963409cab66bbe082d13fcea6'
source=root/'final-source-guard-repaired'
assert subprocess.check_output(['git','-C',str(source),'rev-parse','HEAD'],text=True).strip()==commit
assert subprocess.check_output(['git','-C',str(source),'status','--porcelain=v1','--untracked-files=all'],text=True)==''
cache=source/'.lake';donor=root/'final-source/.lake'
assert cache.is_symlink() and donor.is_dir() and not donor.is_symlink()
assert cache.resolve(strict=True)==donor.resolve(strict=True)
assert donor.resolve(strict=True).is_relative_to(root.resolve(strict=True))
assert (donor.stat().st_dev,donor.stat().st_ino)==(46,10611031912501232925)
assert '/.lake' in (source/'.git/info/exclude').read_text().splitlines()
PYRESUME
test ! -e "$receipt_root" || { echo "fresh receipt path already exists: $receipt_root" >&2; exit 2; }
mkdir -m 700 "$receipt_root"

export ELAN_HOME="$elan_home"
export ELAN_TOOLCHAIN="$toolchain"
export XDG_CACHE_HOME="$run_root/xdg-cache"
export MATHLIB_CACHE_DIR="$run_root/mathlib-cache"
export CURL_CA_BUNDLE="$curl_runtime/ca-certificates.crt"
export GIT_CONFIG_GLOBAL=/dev/null
export GIT_TERMINAL_PROMPT=0
export PATH="$curl_runtime:$elan_home/toolchains/leanprover--lean4---v4.35.0-rc3/bin:$elan_home/bin:$bootstrap/bin:$bootstrap:$PATH"

record_command() {
  local name=$1
  shift
  python3 - "$receipt_root/$name.command.json" "$name" "$@" <<'PY'
import json,sys
from pathlib import Path
Path(sys.argv[1]).write_text(json.dumps({"stage":sys.argv[2],"argv":sys.argv[3:]},indent=2)+"\n")
PY
}

run_stage() {
  stage=$1
  shift
  record_command "$stage" timeout --kill-after=60s 19800s "$@"
  printf '%s begin %s\n' "$(date -u +%FT%TZ)" "$stage"
  local rc=0
  timeout --kill-after=60s 19800s "$@" >"$receipt_root/$stage.log" 2>&1 || rc=$?
  printf '%s\n' "$rc" >"$receipt_root/$stage.exit"
  printf '%s exit=%s %s\n' "$(date -u +%FT%TZ)" "$rc" "$stage"
  return "$rc"
}

write_source_manifest() {
  local target=$1 expected=${2:-}
  python3 - "$source_root" "$source_commit" "$target" "$expected" <<'PY'
import hashlib,json,os,stat,subprocess,sys
from pathlib import Path
root=Path(sys.argv[1]); commit=sys.argv[2]; target=Path(sys.argv[3]); expected=sys.argv[4]
tree=subprocess.check_output(["git","-C",str(root),"rev-parse",commit+"^{tree}"],text=True).strip()
raw=subprocess.check_output(["git","-C",str(root),"ls-tree","-rz","-r","--full-tree",commit])
files=[]
for entry in raw.split(b"\0"):
    if not entry: continue
    metadata,path_bytes=entry.split(b"\t",1)
    mode,kind,blob=metadata.decode("ascii").split()
    if kind!="blob" or mode not in ("100644","100755"):
        raise SystemExit(f"unsupported tracked source entry: {path_bytes!r} ({mode} {kind})")
    relative=path_bytes.decode("utf-8")
    path=root/relative
    info=path.lstat()
    if not stat.S_ISREG(info.st_mode) or path.is_symlink():
        raise SystemExit(f"frozen source shape changed: {relative}")
    if bool(info.st_mode & 0o111) != (mode == "100755"):
        raise SystemExit(f"frozen source executable mode changed: {relative} (Git {mode})")
    data=path.read_bytes()
    actual_blob=subprocess.check_output(["git","-C",str(root),"hash-object","--no-filters",str(path)],text=True).strip()
    if actual_blob!=blob:
        raise SystemExit(f"frozen tracked source bytes changed: {relative}")
    digest=hashlib.sha256(data).hexdigest()
    files.append({"path":relative,"mode":mode,"blob":blob,"sha256":digest})
status=subprocess.check_output(["git","-C",str(root),"status","--porcelain=v1","--untracked-files=all"],text=True)
if status:
    raise SystemExit(f"source worktree is not clean: {status[:400]!r}")
record={"commit":commit,"tree":tree,"files":files}
encoded=(json.dumps(record,sort_keys=True,separators=(",",":"))+"\n").encode()
target.write_bytes(encoded)
fingerprint=hashlib.sha256(encoded).hexdigest()
print(f"source_manifest_sha256={fingerprint}; tree={tree}; files={len(files)}")
if expected and fingerprint!=expected:
    raise SystemExit(f"frozen source changed: expected manifest {expected}, got {fingerprint}")
PY
}

verify_manifest_hash() {
  local where=$1 actual
  actual=$(sha256sum lake-manifest.json | cut -d ' ' -f1)
  printf '%s %s\n' "$where" "$actual" >>"$receipt_root/manifest-hashes.txt"
  test "$actual" = "$manifest_sha" || {
    echo "lake-manifest.json hash mismatch at $where: $actual" >&2
    return 1
  }
}

verify_package_heads() {
  local where=$1
  python3 - "$where" "$receipt_root" <<'PY'
import json,subprocess,sys
from pathlib import Path
where,receipt=sys.argv[1:]
manifest=json.loads(Path("lake-manifest.json").read_text())
packages=manifest.get("packages",[])
if len(packages)!=10: raise SystemExit(f"expected 10 pinned packages, found {len(packages)}")
rows=[]
for package in packages:
    name=package["name"]; expected=package.get("rev")
    if not expected or len(expected)!=40 or any(c not in "0123456789abcdef" for c in expected):
        raise SystemExit(f"missing or non-immutable resolved revision: {name}")
    path=Path(".lake/packages")/name
    actual=subprocess.check_output(["git","-C",str(path),"rev-parse","HEAD"],text=True).strip()
    if actual!=expected: raise SystemExit(f"package pin mismatch {name}: {actual} != {expected}")
    rows.append({"name":name,"revision":actual})
Path(receipt,f"package-heads-{where}.json").write_text(json.dumps(rows,indent=2)+"\n")
if not any(p["name"]=="mathlib" and p["rev"]=="c55e6e786f49471c72fbddbec5415808896aec1e" for p in packages):
    raise SystemExit("Mathlib pin mismatch")
if not any(p["name"]=="algebraicAnalysis" and p["rev"]=="bbbbf3fc358ca8100b158cec4cf47f336ab70163" for p in packages):
    raise SystemExit("AlgebraicAnalysis pin mismatch")
print(f"verified {len(rows)} package HEADs at {where}")
PY
}

finish() {
  local rc=$?
  trap - EXIT
  python3 - "$receipt_root" "$rc" "$stage" "$source_commit" "$started_utc" "$outer_log" <<'PY'
import datetime,hashlib,json,os,sys
from pathlib import Path
root=Path(sys.argv[1]); rc=int(sys.argv[2]); stage=sys.argv[3]
def read_text(name):
    p=root/name
    return p.read_text().strip() if p.is_file() else None
def sha(path):
    h=hashlib.sha256()
    with path.open("rb") as f:
        for b in iter(lambda:f.read(1024*1024),b""):h.update(b)
    return h.hexdigest()
stages=[]
for command in sorted(root.glob("*.command.json")):
    record=json.loads(command.read_text())
    status=command.with_name(command.name.replace(".command.json",".exit"))
    record["exit_status"]=int(status.read_text()) if status.is_file() else None
    log=command.with_name(command.name.replace(".command.json",".log"))
    if log.is_file(): record["log_sha256"]=sha(log)
    stages.append(record)
context={}
try:
    context={"cluster":os.environ.get("SLURM_CLUSTER_NAME"),
      "slurm_job_id":os.environ.get("SLURM_JOB_ID"),
      "slurm_step_id":os.environ.get("SLURM_STEP_ID"),
      "slurm_node":os.environ.get("SLURMD_NODENAME"),
      "cgroup":Path("/proc/self/cgroup").read_text().strip(),
      "cpu_affinity":sorted(os.sched_getaffinity(0))}
except OSError as e: context={"metadata_error":str(e)}
manifest=root/"source-manifest-before.json"
outer=Path(sys.argv[6])
record={"exit_status":rc,"failed_or_last_stage":stage,
 "source_commit":sys.argv[4],"started_at_utc":sys.argv[5],
 "finished_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "lean_version":read_text("lean-version.txt"),"lean_githash":read_text("lean-commit.txt"),
 "curl_runtime_manifest_sha256":read_text("curl-runtime-manifest.sha256"),
 "source_manifest_before_sha256":sha(manifest) if manifest.is_file() else None,
 "source_manifest_after_sha256":sha(root/"source-manifest-after.json") if (root/"source-manifest-after.json").is_file() else None,
 "lake_manifest_hashes":read_text("manifest-hashes.txt"),"package_heads":{p.stem:json.loads(p.read_text()) for p in root.glob("package-heads-*.json")},
 "stages":stages,"allocation":context,
 "outer_guard":{"log":str(outer),"summary":str(outer.with_suffix(".json")),"progress":str(outer.with_suffix(".progress.json")),"expected_exit_status":0,"drained_children_required":True}}
tmp=root/"terminal.json.tmp"; tmp.write_text(json.dumps(record,indent=2)+"\n"); os.replace(tmp,root/"terminal.json")
PY
  exit "$rc"
}
trap finish EXIT

for path in "$bootstrap/elan" "$curl_runtime/curl" "$curl_runtime/runtime-manifest.json" \
  "$elan_home/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean" \
  "$run_root/xdg-cache" "$run_root/mathlib-cache"; do
  test -e "$path" || { echo "missing prepared isolated input: $path" >&2; exit 2; }
done
sha256sum "$curl_runtime/runtime-manifest.json" | cut -d ' ' -f1 >"$receipt_root/curl-runtime-manifest.sha256"

stage=toolchain-pin
lean_version=$(lean --version)
lean_actual_commit=$(lean --githash)
test "$lean_actual_commit" = "$lean_commit" || {
  echo "wrong Lean commit: $lean_actual_commit" >&2; exit 1;
}
test "$(command -v lean)" = "$elan_home/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean" || {
  echo "Lean resolved outside isolated ELAN_HOME" >&2; exit 1;
}
printf '%s\n' "$lean_version" >"$receipt_root/lean-version.txt"
printf '%s\n' "$lean_actual_commit" >"$receipt_root/lean-commit.txt"

cd "$source_root"
write_source_manifest "$receipt_root/source-manifest-before.json" \
  2c697217e318b576775dea866ea45e4e53d1ec3964475953bb4dd5070e08a325
verify_manifest_hash before-update
verify_package_heads before-remaining-gates
# Relocate only the existing generated cache; preserve identity and old donor access.
stage=cache-layout-relocation
python3 - "$run_root" "$receipt_root" <<'PYMOVE'
import json,os,sys
from pathlib import Path
root=Path(sys.argv[1]);receipt=Path(sys.argv[2])
donor=root/'final-source/.lake';target=root/'final-source-guard-repaired/.lake'
assert target.is_symlink() and donor.is_dir() and not donor.is_symlink()
assert target.resolve(strict=True)==donor.resolve(strict=True)
assert donor.resolve(strict=True).is_relative_to(root.resolve(strict=True))
identity=(donor.stat().st_dev,donor.stat().st_ino)
assert identity==(46,10611031912501232925)
assert target.parent.stat().st_dev==identity[0]
old_link=os.readlink(target)
journal={'donor':str(donor),'target':str(target),'old_target_link':old_link,'device':identity[0],'inode':identity[1],'steps':[]}
p=receipt/'cache-relocation.json'
def record(step):
 journal['steps'].append(step)
 with p.open('w') as f:json.dump(journal,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
record('validated exact contained donor and destination symlink')
target.unlink();record('removed only validated destination symlink')
try:
 os.rename(donor,target)
except BaseException:
 target.symlink_to(old_link,target_is_directory=True)
 record('rename failed; original destination symlink restored')
 raise
record('atomic directory rename completed; no copy')
assert target.is_dir() and not target.is_symlink()
assert (target.stat().st_dev,target.stat().st_ino)==identity
donor.symlink_to(target,target_is_directory=True)
record('old donor path preserved as backlink')
assert donor.resolve(strict=True)==target.resolve(strict=True)
assert (donor.stat().st_dev,donor.stat().st_ino)==identity
for child in [target/'build',target/'packages',*sorted((target/'packages').iterdir())]:
 assert child.is_dir() and not child.is_symlink() and child.resolve(strict=True).is_relative_to(target.resolve(strict=True))
record('real mount destination and contained package/build roots verified')
print('cache relocation preserves exact inode; real .lake mount destination ready')
PYMOVE
verify_package_heads after-cache-relocation
write_source_manifest "$receipt_root/source-manifest-after-relocation.json" \
  2c697217e318b576775dea866ea45e4e53d1ec3964475953bb4dd5070e08a325
run_stage comparator-main bash scripts/verify-palomar.sh comparator.json
run_stage comparator-fixed-source bash scripts/verify-palomar.sh comparator-fixed-source.json
run_stage comparator-alternative bash scripts/verify-palomar.sh comparator-alternative.json
run_stage comparator-alternative-fixed-source bash scripts/verify-palomar.sh comparator-alternative-fixed-source.json

stage=final-source-integrity
write_source_manifest "$receipt_root/source-manifest-after.json" \
  "$(python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$receipt_root/source-manifest-before.json")"
verify_manifest_hash final
verify_package_heads final
stage=complete
