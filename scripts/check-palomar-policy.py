#!/usr/bin/env python3
"""Check the exact release pins and Palomar theorem contract before any build."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tomllib
from pathlib import Path

LEAN_TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB_COMMIT = "c55e6e786f49471c72fbddbec5415808896aec1e"
AA_URL = "https://github.com/itpplasma/algebraic-analysis.git"
AA_COMMIT = "bbbbf3fc358ca8100b158cec4cf47f336ab70163"
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
ROOT = Path(__file__).resolve().parents[1]
PALOMAR_POLICY_COMMIT = "65f0154ed776cd26c224254aa57b379137f28b0d"
# These byte-pinned upstream policy modules are vendored for the local preflight.
# Their upstream MIT notice is preserved in scripts/palomar-policy-LICENSE.
PALOMAR_POLICY_FILES = {
    "scripts/source_requirements.py": "971950a45500ad8ba8c9061eb51716bc1c38f411ff877c447b6de527b23d2c6d",
    "scripts/verification_errors.py": "ce58c4adc2f896a8ce69961d1f49ada7f571d86f9638a196f34197e3293cc776",
}
PALOMAR_POLICY_LICENSE_SHA256 = "10321b0cca2b8025d4b5065dd20e22c1f74da2e872c12363e3601974e093bc21"


def check_pinned_source_policy() -> None:
    for relative, expected in PALOMAR_POLICY_FILES.items():
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(
                f"vendored Palomar source policy {relative} changed: {actual}; "
                f"expected policy commit {PALOMAR_POLICY_COMMIT} SHA-256 {expected}"
            )
    license_path = ROOT / "scripts/palomar-policy-LICENSE"
    license_hash = hashlib.sha256(license_path.read_bytes()).hexdigest()
    if license_hash != PALOMAR_POLICY_LICENSE_SHA256:
        raise SystemExit(
            f"vendored Palomar policy license changed: {license_hash}; "
            f"expected SHA-256 {PALOMAR_POLICY_LICENSE_SHA256}"
        )


check_pinned_source_policy()
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scripts.source_requirements import inspect_lean_sources  # noqa: E402


def check_config(path: Path) -> None:
    expected = {
        "comparator.json": {
            "challenge_module": "Challenge",
            "solution_module": "Solution",
            "theorem_names": ["Stafford38Challenge.universalStatement"],
            "permitted_axioms": AXIOMS,
        },
        "comparator-fixed-source.json": {
            "challenge_module": "FixedSourceChallenge",
            "solution_module": "FixedSourceSolution",
            "theorem_names": ["Stafford38FixedSourceChallenge.universalFixedSourceStatement"],
            "permitted_axioms": AXIOMS,
        },
        "comparator-alternative.json": {
            "challenge_module": "Challenge",
            "solution_module": "AlternativeSolution",
            "theorem_names": ["Stafford38Challenge.universalStatement"],
            "permitted_axioms": AXIOMS,
        },
        "comparator-alternative-fixed-source.json": {
            "challenge_module": "FixedSourceChallenge",
            "solution_module": "AlternativeFixedSourceSolution",
            "theorem_names": ["Stafford38FixedSourceChallenge.universalFixedSourceStatement"],
            "permitted_axioms": AXIOMS,
        },
    }
    if path.name not in expected:
        raise SystemExit(f"unsupported Palomar config: {path}")
    try:
        actual = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SystemExit(f"cannot read {path}: {exc}") from exc
    if actual != expected[path.name]:
        raise SystemExit(
            f"{path.name} must use the accepted Palomar config keys and exact theorem/axiom contract"
        )


def check_project() -> None:
    toolchain = Path("lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != LEAN_TOOLCHAIN:
        raise SystemExit(f"unexpected Lean toolchain {toolchain!r}; expected {LEAN_TOOLCHAIN}")

    with Path("lakefile.toml").open("rb") as handle:
        lakefile = tomllib.load(handle)
    with Path("lake-manifest.json").open(encoding="utf-8") as handle:
        manifest = json.load(handle)

    requires = {item["name"]: item for item in lakefile.get("require", [])}
    packages = {item["name"]: item for item in manifest.get("packages", [])}
    for name in ("mathlib", "algebraicAnalysis"):
        if name not in requires or name not in packages:
            raise SystemExit(f"missing required dependency {name} in lakefile or manifest")

    mathlib_req = requires["mathlib"]
    mathlib_pkg = packages["mathlib"]
    if mathlib_req.get("git") != "https://github.com/leanprover-community/mathlib4":
        raise SystemExit("unexpected Mathlib repository URL")
    if mathlib_req.get("rev") != MATHLIB_COMMIT:
        raise SystemExit("lakefile.toml does not pin the frozen RC3 Mathlib commit")
    if mathlib_pkg.get("rev") != MATHLIB_COMMIT or mathlib_pkg.get("inputRev") != MATHLIB_COMMIT:
        raise SystemExit("lake-manifest.json does not resolve the frozen RC3 Mathlib commit")

    if not re.fullmatch(r"[0-9a-f]{40}", AA_COMMIT):
        raise SystemExit("AA_COMMIT must be one full lowercase commit hash")
    aa_req = requires["algebraicAnalysis"]
    aa_pkg = packages["algebraicAnalysis"]
    if aa_req.get("git") != AA_URL or aa_req.get("rev") != AA_COMMIT:
        raise SystemExit("lakefile.toml does not pin the frozen AlgebraicAnalysis commit")
    if aa_pkg.get("url") != AA_URL or aa_pkg.get("rev") != AA_COMMIT or aa_pkg.get("inputRev") != AA_COMMIT:
        raise SystemExit("lake-manifest.json does not resolve the frozen AlgebraicAnalysis commit")


def check_lean_source_requirements() -> None:
    report, issues = inspect_lean_sources(ROOT)
    if issues:
        for issue in issues:
            location = f"{issue.path}:{issue.line}" if issue.path and issue.line else issue.path or "Lean source"
            print(f"ERROR [{issue.code}] {location}: {issue}", file=sys.stderr)
        raise SystemExit(
            f"local preflight against Palomar Lean source requirements failed for {len(issues)} file(s) "
            f"(policy commit {PALOMAR_POLICY_COMMIT}; this is not a Palomar service-runner receipt)"
        )
    print(
        f"Local preflight against Palomar source policy {PALOMAR_POLICY_COMMIT}: "
        f"{report['files_checked']} Lean files satisfy "
        f"module-header, UTF-8, symlink, and {report['maximum_lines']}-line checks "
        "(not a Palomar service-runner receipt)"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config-only", metavar="CONFIG", help="check one exact Palomar config only")
    args = parser.parse_args()
    if args.config_only:
        check_config(Path(args.config_only))
        print(f"{args.config_only}: accepted config schema and exact theorem/axiom contract passed")
        return 0
    check_lean_source_requirements()
    check_project()
    check_config(Path("comparator.json"))
    check_config(Path("comparator-fixed-source.json"))
    check_config(Path("comparator-alternative.json"))
    check_config(Path("comparator-alternative-fixed-source.json"))
    print(
        f"pins: Lean {LEAN_TOOLCHAIN} ({LEAN_COMMIT}), Mathlib {MATHLIB_COMMIT}, "
        f"AlgebraicAnalysis {AA_COMMIT}; both Palomar configs passed"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
