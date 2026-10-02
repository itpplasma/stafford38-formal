#!/usr/bin/env bash
set -euo pipefail

# Export an exact committed tree or an exact base plus frozen complete patch.
# Source worktree/index are never modified. No replay or transfer is started.
repo=${1:?repository path}
base=${2:?full commit}
patch=${3:-}
expected_patch_hash=${4:-}
[[ "$base" =~ ^[0-9a-f]{40}$ ]] || exit 2
if [ -n "$patch" ]; then
  [[ "$expected_patch_hash" =~ ^[0-9a-f]{64}$ ]] || exit 2
fi
stage=$(mktemp -d /tmp/stafford38-linux-input.XXXXXX)
export GIT_CONFIG_GLOBAL=/dev/null
git clone --bare --shared --no-hardlinks "$repo" "$stage/snapshot.git" >/dev/null
[ "$(git --git-dir="$stage/snapshot.git" rev-parse "$base^{commit}")" = "$base" ] || exit 1
export GIT_INDEX_FILE="$stage/frozen.index"
git --git-dir="$stage/snapshot.git" read-tree "$base"
if [ -n "$patch" ]; then
  actual_patch_hash=$(python3 - "$patch" <<'PY'
import hashlib,sys
print(hashlib.sha256(open(sys.argv[1],'rb').read()).hexdigest())
PY
)
  [ "$actual_patch_hash" = "$expected_patch_hash" ] || exit 1
  git --git-dir="$stage/snapshot.git" apply --cached --binary --check "$patch"
  git --git-dir="$stage/snapshot.git" apply --cached --binary "$patch"
fi
tree=$(git --git-dir="$stage/snapshot.git" write-tree)
git --git-dir="$stage/snapshot.git" archive --mtime=1970-01-01T00:00:00Z \
  --format=tar "$tree" >"$stage/source.tar"
python3 - "$stage" "$base" "$tree" "$expected_patch_hash" <<'PY'
import hashlib,json,subprocess,sys,tarfile
from pathlib import Path
stage=Path(sys.argv[1]); base,tree,patch_hash=sys.argv[2:]
git=['git','--git-dir='+str(stage/'snapshot.git')]
index=subprocess.check_output(git+['ls-tree','-rz','--full-tree',tree])
files=[]
for record in index.split(b'\0'):
    if not record:continue
    meta,path=record.split(b'\t',1)
    mode,kind,blob=meta.decode().split()
    name=path.decode('utf-8')
    if mode not in {'100644','100755'} or kind!='blob':
        raise SystemExit('Snapshot requires review of nonregular entry: '+name)
    content=subprocess.check_output(git+['cat-file','blob',blob])
    files.append({'path':name,'mode':mode,'blob':blob,
                  'sha256':hashlib.sha256(content).hexdigest(),'bytes':len(content)})
expected={x['path']:x for x in files}
with tarfile.open(stage/'source.tar') as archive:
    actual={m.name:m for m in archive.getmembers() if not m.isdir()}
    if set(actual)!=set(expected):
        raise SystemExit('Archive differs from tracked tree (export attributes or omission)')
    for name,member in actual.items():
        if not member.isfile():raise SystemExit('Archive contains nonregular source: '+name)
        data=archive.extractfile(member).read()
        if hashlib.sha256(data).hexdigest()!=expected[name]['sha256']:
            raise SystemExit('Archive substituted tracked source bytes: '+name)
receipt={'base_commit':base,'tree':tree,'patch_sha256':patch_hash or None,
         'source_tar_sha256':hashlib.sha256((stage/'source.tar').read_bytes()).hexdigest(),
         'files':files}
(stage/'source-manifest.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'snapshot_directory':str(stage),'tree':tree,
                  'source_tar_sha256':receipt['source_tar_sha256'],
                  'tracked_files':len(files)},indent=2))
PY
