#!/usr/bin/env python3
"""Run the replay driver against disposable fake Git/Lean/Lake tools."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
DRIVER = HERE / "cluster-final-replay-20261003.sh"
REPO = DRIVER.parents[3]
COMMIT = "0123456789abcdef0123456789abcdef01234567"
TREE = "abcdef0123456789abcdef0123456789abcdef01"
PINS = {
    "algebraicAnalysis": "bbbbf3fc358ca8100b158cec4cf47f336ab70163",
    "mathlib": "c55e6e786f49471c72fbddbec5415808896aec1e",
    "plausible": "fb13df72ecefd8ddbf9291021d7f33a8673eb57b",
    "LeanSearchClient": "29ff470276c725ae01505d55b17148c18fc7dfd3",
    "importGraph": "7e81a29bda33a6b257bd37557a6aa6aebe175d96",
    "proofwidgets": "c643bbb3c24f8a25f9c14e3a6b1ceb13d01f3de1",
    "aesop": "a90fbf7b02ff06a0deebf74088dff9e5fe02c9ea",
    "Qq": "37b0ba0b26109cf9f9c541f0f9557e50cfa1a3b9",
    "batteries": "3b7c8101932390d60e92a3f3d917901d5b5a773b",
    "Cli": "843844fa601dd56767b1eb22b7ada5b64d5e567a",
}
LEAN = "leanprover/lean4:v4.35.0-rc3"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"


def executable(path: Path, body: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("#!/usr/bin/env python3\n" + body)
    path.chmod(0o755)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="stafford-final-replay-test-") as td:
        root = Path(td)
        allowed = root / "campaign"
        run = allowed / "run"
        project = root / "frozen-project"
        bin_dir = root / "fake-bin"
        (project / "scripts").mkdir(parents=True)
        shutil.copyfile(REPO / "lake-manifest.json", project / "lake-manifest.json")
        (project / "lean-toolchain").write_text(LEAN + "\n")
        (project / ".gitignore").write_text(".lake/\n")
        (project / "Challenge.lean").write_text("-- fixed tracked source\n")
        (project / "scripts/check-palomar-policy.py").write_text("pass\n")
        (project / "scripts/bootstrap-palomar-tools.sh").write_text("#!/bin/sh\nexit 0\n")
        verify = project / "scripts/verify.sh"
        verify.write_text("#!/bin/sh\nif [ \"${MUTATE_AFTER_VERIFY:-0}\" = 1 ]; then echo changed >> Challenge.lean; fi\nif [ \"${MUTATE_MODE:-0}\" = 1 ]; then chmod +x Challenge.lean; fi\nif [ \"${REMOVE_MODE:-0}\" = 1 ]; then chmod -x scripts/verify.sh; fi\n")
        comparator = project / "scripts/verify-palomar.sh"
        comparator.write_text("#!/bin/sh\nprintf '%s\\n' \"$1\" >> \"$COMPARATOR_LOG\"\n")
        for p in (project / "scripts/bootstrap-palomar-tools.sh", verify, comparator):
            p.chmod(0o755)

        git_body = r'''import hashlib,json,os,shutil,sys
from pathlib import Path
a=sys.argv[1:]
if a[0]=="-C": base=Path(a[1]); a=a[2:]
else: base=Path.cwd()
if a[0]=="init" or a[0]=="remote" or a[0]=="fetch": sys.exit(0)
if a[0]=="checkout":
    shutil.copytree(os.environ["FAKE_PROJECT"],base,dirs_exist_ok=True); sys.exit(0)
if a[0]=="rev-parse":
    target=a[-1]
    if target=="HEAD":
        name=base.name
        if name in json.loads(os.environ["FAKE_PINS"]): print(json.loads(os.environ["FAKE_PINS"])[name])
        else: print(os.environ["FAKE_COMMIT"])
    elif target.endswith("^{tree}"): print(os.environ["FAKE_TREE"])
    else: sys.exit(3)
    sys.exit(0)
if a[0]=="ls-tree":
    top=Path(os.environ["FAKE_PROJECT"])
    out=[]
    for p in sorted(x for x in top.rglob("*") if x.is_file() and ".git" not in x.parts):
        rel=p.relative_to(top).as_posix(); data=p.read_bytes()
        oid=hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
        mode="100755" if p.stat().st_mode & 0o111 else "100644"
        out.append(f"{mode} blob {oid}\t{rel}".encode()+b"\0")
    sys.stdout.buffer.write(b"".join(out)); sys.exit(0)
if a[0]=="status":
    top=Path(os.environ["FAKE_PROJECT"]); dirty=[]
    for p in top.rglob("*"):
        if not p.is_file(): continue
        rel=p.relative_to(top)
        q=base/rel
        if not q.is_file() or q.read_bytes()!=p.read_bytes() : dirty.append(str(rel))
    print("".join(" M "+x+"\\n" for x in dirty),end="")
    sys.exit(0)
sys.exit(4)
'''
        executable(bin_dir / "git", git_body)
        fake_lake = r'''import json,os,sys
from pathlib import Path
a=sys.argv[1:]
if a[:1]==["update"]:
    pins=json.loads(os.environ["FAKE_PINS"])
    for name in pins: (Path(".lake/packages")/name/".git").mkdir(parents=True,exist_ok=True)
if " ".join(a)==os.environ.get("FAIL_LAKE_MATCH"): sys.exit(41)
sys.exit(0)
'''
        executable(bin_dir / "lake", fake_lake)
        driver_text = DRIVER.read_text()
        original_case = "campaign_root=/home/ert/stafford38-campaign"
        assert original_case in driver_text
        test_driver = root / "driver.sh"
        test_driver.write_text(driver_text.replace(original_case, f"campaign_root={allowed}"))
        test_driver.chmod(0o755)

        # These cases execute the real driver preflight against actual directories
        # and symlinks, before fake tool setup or any receipt/source writes.
        allowed.mkdir()
        outside = root / "outside"
        outside.mkdir()
        (allowed / "escape").symlink_to(outside, target_is_directory=True)
        file_root = allowed / "file"
        file_root.write_text("not a directory")
        good_root = allowed / "argument-test"
        good_root.mkdir()
        negatives = [
            [], [str(good_root)], [str(good_root), COMMIT, "extra"],
            [str(good_root), "short"], [str(good_root), "A" * 40],
            [str(allowed / "missing"), COMMIT], [str(file_root), COMMIT],
            [str(allowed), COMMIT], [str(outside), COMMIT],
            [str(allowed / ".." / "outside"), COMMIT],
            [str(allowed / "escape"), COMMIT],
        ]
        for arguments in negatives:
            result = subprocess.run(["bash", str(test_driver), *arguments],
                                    cwd=root, text=True, capture_output=True)
            assert result.returncode == 2, (arguments, result.stderr)
            assert not list(allowed.rglob("final-receipts"))
            assert not list(outside.rglob("final-receipts"))
            assert not list(allowed.rglob("final-source"))
            assert not list(outside.rglob("final-source"))

        def run_case(name: str, *, checkout_commit=COMMIT, lean_commit=LEAN_COMMIT, fail_lake="", mutate=False, mutate_mode=False, remove_mode=False):
            case_root = allowed / name
            case_root.mkdir(parents=True)
            for d in (case_root / "xdg-cache", case_root / "mathlib-cache"):
                d.mkdir()
            runtime=case_root/"bootstrap/curl-runtime"
            executable(runtime/"curl", 'print("curl 8.0 libcurl/8.0")\n')
            (runtime/"runtime-manifest.json").write_text('{"test":"stub"}\n')
            executable(case_root/"bootstrap/elan", 'pass\n')
            lean_path=case_root/"elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean"
            executable(lean_path, 'import os,sys\nprint("Lean (version 4.35.0-rc3)") if sys.argv[1:]==["--version"] else None\nprint(os.environ.get("FAKE_LEAN_COMMIT", "'+LEAN_COMMIT+'")) if sys.argv[1:]==["--githash"] else None\n')
            receipts = case_root / "final-receipts"
            env = os.environ.copy()
            env.update({
                "FAKE_PROJECT": str(project), "FAKE_PINS": json.dumps(PINS),
                "FAKE_COMMIT": checkout_commit, "FAKE_TREE": TREE, "FAKE_LEAN_COMMIT": lean_commit,
                "FAIL_LAKE_MATCH": fail_lake, "MUTATE_AFTER_VERIFY": "1" if mutate else "0",
                "MUTATE_MODE": "1" if mutate_mode else "0",
                "REMOVE_MODE": "1" if remove_mode else "0",
                "COMPARATOR_LOG": str(case_root / "comparators.txt"),
                "STAFFORD_OUTER_GUARD_LOG": str(case_root / "outer.log"),
                "SLURM_CLUSTER_NAME": "acluster", "SLURMD_NODENAME": "node1",
                "SLURM_CPUS_PER_TASK": "2", "SLURM_NTASKS": "1", "SLURM_JOB_NUM_NODES": "1",
                "SLURM_JOB_ID": "123", "SLURM_STEP_ID": "0",
                "PATH": str(bin_dir)+":"+env["PATH"],
            })
            p = subprocess.run(["bash", str(test_driver), str(case_root), COMMIT],
                               cwd=root, env=env, text=True, capture_output=True)
            rec=json.loads((receipts/"terminal.json").read_text())
            return p,rec,case_root

        p,rec,_=run_case("wrong-source",checkout_commit="f"*40)
        assert p.returncode != 0 and rec["failed_or_last_stage"]=="source-checkout" and rec["exit_status"]==1, (p.stderr,rec)
        p,rec,_=run_case("wrong-lean",lean_commit="0"*40)
        assert p.returncode != 0 and rec["failed_or_last_stage"]=="lean-githash" and rec["exit_status"]==1, (p.stderr,rec)
        p,rec,_=run_case("lake-failure",fail_lake="exe cache get")
        assert p.returncode==41 and rec["failed_or_last_stage"]=="mathlib-cache" and rec["exit_status"]==41, (p.stderr,rec)
        p,rec,_=run_case("source-mutated",mutate=True)
        assert p.returncode != 0 and rec["failed_or_last_stage"]=="final-source-integrity" and rec["exit_status"]==1, (p.stderr,rec)
        p,rec,_=run_case("mode-mutated",mutate_mode=True)
        assert p.returncode != 0 and rec["failed_or_last_stage"]=="final-source-integrity" and rec["exit_status"]==1, (p.stderr,rec)
        assert "executable mode changed" in p.stderr, p.stderr
        p,rec,_=run_case("executable-mode-removed",remove_mode=True)
        assert p.returncode != 0 and rec["failed_or_last_stage"]=="final-source-integrity", (p.stderr,rec)
        assert "executable mode changed" in p.stderr, p.stderr
        p,rec,case=run_case("success")
        assert p.returncode==0 and rec["failed_or_last_stage"]=="complete" and rec["exit_status"]==0, (p.stderr,rec)
        before=rec["source_manifest_before_sha256"]
        after=rec["source_manifest_after_sha256"]
        assert before and before==after
        before_manifest=json.loads((case/"final-receipts/source-manifest-before.json").read_text())
        after_manifest=json.loads((case/"final-receipts/source-manifest-after.json").read_text())
        assert before_manifest==after_manifest
        assert all({'mode','blob','sha256','path'} <= set(entry) for entry in before_manifest['files'])
        expected=["comparator.json","comparator-fixed-source.json","comparator-alternative.json","comparator-alternative-fixed-source.json"]
        assert (case/"comparators.txt").read_text().splitlines()==expected
        assert len(rec["package_heads"]["package-heads-final"])==10
        print("fake driver behavioral oracles passed: invalid arguments, missing/file/root-equal/outside/traversal/symlink roots before writes; mode mutation with Git status ignoring executable bits; wrong source commit, wrong Lean pin, failing cache stage, post-verify tracked-content and mode mutations, clean tree/file/mode identity, four ordered comparators")


if __name__ == "__main__":
    main()
