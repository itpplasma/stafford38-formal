#!/usr/bin/env python3
"""Run the RC3 dependency-closure checker without modifying the formal build."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
VERSION_PREFIX = "Lean (version 4.35.0-rc3,"
LEAN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean"
ROOT_MODULES = (
    "Solution",
    "FixedSourceSolution",
)
INCOMPLETE = re.compile(
    r"^STAFFORD_DEPENDENCY_GUARD_INCOMPLETE\t([^\t]+)\t([^\t]+)\t([^\t]+)\t([^\t]+)$",
    re.MULTILINE,
)


def display_output(output: str) -> str:
    lines = output.splitlines()
    if len(lines) <= 240:
        return output
    shown = lines[:180] + [f"... {len(lines) - 240} intermediate lines omitted ..."] + lines[-59:]
    return "\n".join(shown) + "\n"


def check_lean() -> str:
    if not LEAN.is_file():
        raise SystemExit(f"explicit RC3 Lean binary is missing: {LEAN}")
    result = subprocess.run([str(LEAN), "--version"], text=True, capture_output=True)
    if result.returncode or not result.stdout.startswith(VERSION_PREFIX):
        raise SystemExit(f"wrong Lean binary: {result.stdout.strip()} {result.stderr.strip()}")
    return result.stdout.strip()


def project_search_path(root: Path) -> list[Path]:
    manifest_path = root / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    paths = [root / ".lake/build/lib/lean"]
    for package in manifest["packages"]:
        if package["type"] == "path":
            package_root = (root / package["dir"]).resolve()
        else:
            package_root = root / ".lake/packages" / package["name"]
        paths.append(package_root / ".lake/build/lib/lean")
    paths.append(LEAN.parent.parent / "lib/lean")
    return [p.resolve() for p in paths if p.is_dir()]


def find_project_root() -> Path:
    candidates = (Path.cwd().resolve(), *Path(__file__).resolve().parents)
    for candidate in candidates:
        if (candidate / "lean-toolchain").is_file() and (candidate / "lake-manifest.json").is_file():
            return candidate
    raise SystemExit("pass --root; no Lean/Lake project root contains both pin files")


def make_header(base_modules: list[str], extra_modules: list[str], *, fixture: bool, root_name: str | None,
                forbidden_name: str | None, production_fixture: bool) -> str:
    lines = ["module", "public import DependencyClosureCore", "import all DependencyClosureCore"]
    for module in base_modules:
        lines.extend((f"public import {module}", f"import all {module}"))
    for module in extra_modules:
        lines.append(f"import all {module}")
    lines.append("")
    if production_fixture:
        lines.append("#auditStaffordTerminalDeps")
    elif fixture:
        assert root_name is not None and forbidden_name is not None
        lines.append(f"#auditDependencyClosure {root_name} forbidden {forbidden_name}")
    else:
        lines.append("#auditStaffordTerminalDeps")
    return "\n".join(lines) + "\n"


def run_checker(env: dict[str, str], cwd: Path, checker: Path,
                core_olean_dir: Path, timeout_seconds: int) -> tuple[int, str]:
    local_env = env.copy()
    paths = [str(core_olean_dir)]
    if local_env.get("LEAN_PATH"):
        paths.append(local_env["LEAN_PATH"])
    local_env["LEAN_PATH"] = os.pathsep.join(paths)
    proc = subprocess.run(
        [str(LEAN), "--trust=0", "-j", "1", str(checker)],
        cwd=cwd, env=local_env, text=True, capture_output=True,
        timeout=timeout_seconds,
    )
    return proc.returncode, proc.stdout + proc.stderr


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path)
    parser.add_argument("--allow-old-route", action="store_true",
                        help="diagnostic only; never suppress unavailable-body failures")
    parser.add_argument("--max-expansions", type=int, default=64)
    parser.add_argument("--timeout-seconds", type=int, default=300)
    parser.add_argument("--fixture", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--fixture-production", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--fixture-root-name", help=argparse.SUPPRESS)
    parser.add_argument("--forbidden-name", help=argparse.SUPPRESS)
    parser.add_argument("--base-module", action="append", default=[], help=argparse.SUPPRESS)
    parser.add_argument("--extra-lean-path", action="append", default=[], type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.timeout_seconds < 1 or args.max_expansions < 0:
        parser.error("timeout must be positive and max-expansions must be nonnegative")
    version = check_lean()

    if args.fixture or args.fixture_production:
        if args.fixture == args.fixture_production:
            parser.error("choose exactly one fixture mode")
        if args.fixture and (not args.fixture_root_name or not args.forbidden_name):
            parser.error("generic fixture mode requires a root name and forbidden name")
        if not args.base_module:
            parser.error("fixture mode requires at least one base module")
        root = Path.cwd().resolve()
        search = [p.resolve(strict=True) for p in args.extra_lean_path]
        search.append(LEAN.parent.parent / "lib/lean")
        fixture_mode = True
        production_fixture = args.fixture_production
        base_modules = list(dict.fromkeys(args.base_module))
    else:
        root = (args.root if args.root is not None else find_project_root()).resolve(strict=True)
        actual_toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
        if actual_toolchain != TOOLCHAIN:
            raise SystemExit(f"expected {TOOLCHAIN}, found {actual_toolchain!r}")
        search = project_search_path(root)
        fixture_mode = False
        production_fixture = False
        base_modules = list(ROOT_MODULES)

    candidate = Path(__file__).resolve().parent
    core_source = candidate / "DependencyClosureCore.lean"
    if not core_source.is_file():
        raise SystemExit(f"guard core is missing: {core_source}")
    env = os.environ.copy()
    env.pop("STAFFORD_ALLOW_OLD_ROUTE", None)
    if args.allow_old_route and not fixture_mode:
        env["STAFFORD_ALLOW_OLD_ROUTE"] = "1"
    if search:
        env["LEAN_PATH"] = os.pathsep.join(str(p) for p in search)
    else:
        env.pop("LEAN_PATH", None)

    print(f"lean={LEAN}; {version}")
    print(f"scope={'fixture behavior test' if fixture_mode else f'RC3 source tree {root}'}")
    print(f"mode={'old-route diagnostic only' if args.allow_old_route else 'strict'}")

    with tempfile.TemporaryDirectory(prefix="stafford-dependency-guard-") as temporary:
        temp = Path(temporary)
        core_out = temp / "core"
        core_out.mkdir()
        try:
            core_build = subprocess.run(
                [str(LEAN), "--trust=0", "-j", "1", "--root", str(candidate),
                 "-o", str(core_out / "DependencyClosureCore.olean"), str(core_source)],
                cwd=root, env=env, text=True, capture_output=True,
                timeout=min(args.timeout_seconds, 120),
            )
        except subprocess.TimeoutExpired:
            print("fail-closed: dependency-guard core compile exceeded its time cap", file=sys.stderr)
            return 1
        if core_build.returncode:
            sys.stderr.write(core_build.stdout + core_build.stderr)
            return core_build.returncode

        loaded = list(dict.fromkeys(base_modules))
        seen_owner_additions: set[str] = set()
        for attempt in range(args.max_expansions + 1):
            checker = temp / f"DependencyClosureRun{attempt}.lean"
            checker.write_text(
                make_header(base_modules, [m for m in loaded if m not in base_modules], fixture=fixture_mode,
                            root_name=args.fixture_root_name,
                            forbidden_name=args.forbidden_name,
                            production_fixture=production_fixture),
                encoding="utf-8",
            )
            try:
                rc, output = run_checker(env, root, checker, core_out, args.timeout_seconds)
            except subprocess.TimeoutExpired as error:
                print(f"fail-closed: Lean dependency inspection exceeded {args.timeout_seconds}s", file=sys.stderr)
                if error.stdout:
                    sys.stderr.write(error.stdout.decode(errors="replace") if isinstance(error.stdout, bytes) else error.stdout)
                if error.stderr:
                    sys.stderr.write(error.stderr.decode(errors="replace") if isinstance(error.stderr, bytes) else error.stderr)
                return 1
            print(f"body_load_round={attempt}; import_all={len(loaded)}")
            sys.stdout.write(display_output(output))
            missing = INCOMPLETE.findall(output)
            if not missing:
                return rc

            new_owners = []
            for _, _name, owner, kind in missing:
                if owner == "none":
                    print(f"fail-closed: unavailable dependency has no module owner ({kind})", file=sys.stderr)
                    return 1
                if owner not in loaded and owner not in seen_owner_additions:
                    new_owners.append(owner)
                    seen_owner_additions.add(owner)
            if not new_owners:
                print("fail-closed: body unavailable after its owner module was import-all'd", file=sys.stderr)
                return 1
            if attempt >= args.max_expansions:
                print("fail-closed: exceeded import-all expansion limit", file=sys.stderr)
                return 1
            loaded.extend(sorted(set(new_owners)))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
