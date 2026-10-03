#!/usr/bin/env python3
"""Stage a trusted login-host curl runtime into one isolated campaign run tree.

This stages files only. It never runs curl, changes system files, contacts the
network, or submits a job. The controller runs the generated wrapper only
inside a separately approved, guarded Slurm allocation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


CA_BUNDLE = Path("/etc/ssl/certs/ca-certificates.crt")
CURL_BINARY = Path("/usr/bin/curl")
LDD_BINARY = Path("/usr/bin/ldd")
DEPENDENCY = re.compile(r"^\s*(\S+)\s+=>\s+(\S+)\s+\(0x[0-9a-fA-F]+\)\s*$")
DIRECT = re.compile(r"^\s*(/\S+)\s+\(0x[0-9a-fA-F]+\)\s*$")
UNRESOLVED = re.compile(r"^\s*(\S+)\s+=>\s+not found\s*$")
SAFE_BASENAME = re.compile(r"^[A-Za-z0-9._+-]+$")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_ldd(text: str) -> tuple[dict[str, Path], Path]:
    dependencies: dict[str, Path] = {}
    loaders: list[Path] = []
    unresolved: list[str] = []
    for line in text.splitlines():
        missing = UNRESOLVED.match(line)
        if missing:
            unresolved.append(missing.group(1))
            continue
        dependency = DEPENDENCY.match(line)
        if dependency:
            soname, location = dependency.groups()
            dependencies[soname] = Path(location)
            continue
        direct = DIRECT.match(line)
        if direct:
            path = Path(direct.group(1))
            basename = path.name
            if basename.startswith("ld-linux") or basename.startswith("ld-"):
                loaders.append(path)
    if unresolved:
        raise ValueError("ldd reported unresolved dependencies: " + ", ".join(unresolved))
    if not dependencies:
        raise ValueError("ldd reported no shared-library closure for curl")
    if len(loaders) != 1:
        raise ValueError(f"expected exactly one ldd-reported ELF loader, found {len(loaders)}")
    return dependencies, loaders[0]


def copy_payload(source: Path, destination: Path, *, executable: bool = False) -> dict[str, str]:
    source = source.resolve(strict=True)
    if not source.is_file():
        raise ValueError(f"not a regular file: {source}")
    shutil.copyfile(source, destination)
    mode = source.stat().st_mode & 0o777
    destination.chmod(mode | (0o111 if executable else 0))
    return {"source": str(source), "sha256": sha256(destination)}


def wrapper_text(loader_name: str) -> str:
    if not SAFE_BASENAME.fullmatch(loader_name):
        raise ValueError(f"unsafe ELF loader basename: {loader_name!r}")
    return f'''#!/bin/sh
set -eu
bundle=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
export CURL_CA_BUNDLE="$bundle/ca-certificates.crt"
exec "$bundle/{loader_name}" --library-path "$bundle" "$bundle/curl.bin" "$@"
'''


def stage(run_dir: Path, curl: Path, ca_bundle: Path) -> Path:
    curl = curl.resolve(strict=True)
    ca_bundle = ca_bundle.resolve(strict=True)
    ldd = LDD_BINARY
    if not ldd.is_file():
        raise ValueError(f"system ldd is missing: {ldd}")
    if not os.access(curl, os.X_OK):
        raise ValueError(f"login-host curl is not executable: {curl}")
    ldd_result = subprocess.run(
        [str(ldd), str(curl)], stdin=subprocess.DEVNULL, text=True,
        capture_output=True, check=False,
    )
    if ldd_result.returncode != 0:
        raise ValueError(f"ldd failed for trusted curl: {ldd_result.stderr.strip()}")
    dependencies, loader = parse_ldd(ldd_result.stdout)

    destination = run_dir / "bootstrap" / "curl-runtime"
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        raise FileExistsError(f"refusing to replace existing runtime bundle: {destination}")
    with tempfile.TemporaryDirectory(prefix=".curl-runtime-", dir=destination.parent) as tmp_name:
        temporary = Path(tmp_name)
        records: dict[str, dict[str, str]] = {}
        records["curl.bin"] = copy_payload(curl, temporary / "curl.bin", executable=True)
        records[loader.name] = copy_payload(loader, temporary / loader.name, executable=True)
        for soname, source in sorted(dependencies.items()):
            if not SAFE_BASENAME.fullmatch(soname):
                raise ValueError(f"unsafe shared-library basename from ldd: {soname!r}")
            if soname == loader.name:
                continue
            prior = records.get(soname)
            record = copy_payload(source, temporary / soname)
            if prior is not None and prior["sha256"] != record["sha256"]:
                raise ValueError(f"different dependencies share bundle basename {soname}")
            records[soname] = record
        records["ca-certificates.crt"] = copy_payload(ca_bundle, temporary / "ca-certificates.crt")
        wrapper = temporary / "curl"
        wrapper.write_text(wrapper_text(loader.name), encoding="utf-8")
        wrapper.chmod(0o755)
        (temporary / "runtime-manifest.json").write_text(
            json.dumps({
                "source_curl": str(curl),
                "source_ldd": str(ldd),
                "elf_loader": loader.name,
                "ca_bundle_source": str(ca_bundle),
                "files": records,
                "wrapper": "curl",
                "wrapper_probe_required_in_allocation": ["--version"],
            }, indent=2) + "\n",
            encoding="utf-8",
        )
        temporary.rename(destination)
    return destination


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_dir", type=Path, help="unique per-run directory on the login host")
    args = parser.parse_args()
    try:
        result = stage(args.run_dir, CURL_BINARY, CA_BUNDLE)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"curl runtime staging refused: {error}", file=sys.stderr)
        return 1
    print(f"staged curl runtime files at {result}")
    print("staging did not execute curl; run the --version probe inside the guarded allocation")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
