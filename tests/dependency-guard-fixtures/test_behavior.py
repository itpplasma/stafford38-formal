#!/usr/bin/env python3
"""Independent fixture oracle for fail-closed RC3 dependency loading."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
FIXTURE_SOURCES = HERE / "sources"
RUNNER = HERE.parents[1] / "scripts/dependency-guard/run_guard.py"
_runner_spec = importlib.util.spec_from_file_location("dependency_guard_runner", RUNNER)
assert _runner_spec is not None and _runner_spec.loader is not None
_guard_runner = importlib.util.module_from_spec(_runner_spec)
_runner_spec.loader.exec_module(_guard_runner)
LEAN = _guard_runner.lean_binary()
LEAN_LIB = LEAN.parent.parent / "lib/lean"


def run(command: list[str], *, cwd: Path, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)


def compile_module(name: str, source: Path, fixture_root: Path, out: Path,
                  env: dict[str, str]) -> None:
    target = out.joinpath(*name.split(".")).with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    result = run(
        [str(LEAN), "--trust=0", "-j", "1", "--root", str(fixture_root),
         "-o", str(target), str(source)],
        cwd=fixture_root, env=env,
    )
    if result.returncode:
        raise RuntimeError(f"fixture compile failed for {name}:\n{result.stdout}{result.stderr}")


def run_fixture(out: Path, root: str, producer: str, module: str) -> subprocess.CompletedProcess[str]:
    return run(
        ["python3", str(RUNNER), "--fixture", "--fixture-root-name", root,
         "--forbidden-name", producer, "--base-module", module,
         "--extra-lean-path", str(out)],
        cwd=HERE, env=os.environ.copy(),
    )


def run_production_fixture(out: Path) -> subprocess.CompletedProcess[str]:
    return run(
        ["python3", str(RUNNER), "--fixture-production",
         "--base-module", "Solution", "--base-module", "FixedSourceSolution",
         "--extra-lean-path", str(out)],
        cwd=HERE, env=os.environ.copy(),
    )


def run_route_fixture(out: Path, root: str, required: str, forbidden: str,
                      module: str = "GuardFixtureRoute") -> subprocess.CompletedProcess[str]:
    return run(
        ["python3", str(RUNNER), "--fixture-route", "--fixture-root-name", root,
         "--required-name", required, "--forbidden-name", forbidden,
         "--base-module", module, "--extra-lean-path", str(out)],
        cwd=HERE, env=os.environ.copy(),
    )


def run_challenge_placeholder(out: Path, root: str, module: str) -> subprocess.CompletedProcess[str]:
    return run(
        ["python3", str(RUNNER), "--fixture", "--fixture-root-name", root,
         "--forbidden-name", "GuardFixture.neverForbidden", "--base-module", module,
         "--extra-lean-path", str(out)],
        cwd=HERE, env=os.environ.copy(),
    )


def main() -> int:
    # Validate the exact pinned version and commit before compiling any fixture.
    _guard_runner.check_lean()
    with tempfile.TemporaryDirectory(prefix="stafford-guard-fixtures-") as temporary:
        out = Path(temporary).resolve()
        fixture_root = out / "sources"
        fixture_root.mkdir()
        for source in FIXTURE_SOURCES.rglob("*.lean.txt"):
            relative = source.relative_to(FIXTURE_SOURCES)
            materialized = (fixture_root / relative).with_suffix("")
            materialized.parent.mkdir(parents=True, exist_ok=True)
            materialized.write_bytes(source.read_bytes())
        env = os.environ.copy()
        build = out / "build"
        build.mkdir()
        env["LEAN_PATH"] = os.pathsep.join((str(build), str(LEAN_LIB)))

        core = RUNNER.parent / "DependencyClosureCore.lean"
        core_build = run(
            [str(LEAN), "--trust=0", "-j", "1", "--root", str(RUNNER.parent),
             "-o", str(build / "DependencyClosureCore.olean"), str(core)],
            cwd=RUNNER.parent, env=env,
        )
        if core_build.returncode:
            raise RuntimeError(f"core compile failed:\n{core_build.stdout}{core_build.stderr}")

        for name in ("GuardFixtureSafe", "GuardFixtureMissingBody", "GuardFixtureBad",
                     "GuardFixtureBannedOwner", "GuardFixtureRelay", "GuardFixtureBadRoot",
                     "GuardFixtureRoute"):
            compile_module(name, fixture_root / f"{name}.lean", fixture_root, build, env)
        production_modules = (
            "Stafford38.Geometry.GeneralAsymptoticLaurentAxis",
            "Stafford38.Geometry.GeneralConormalAxis",
            "Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof",
            "Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction",
            "Stafford38.FoundationClosure",
            "Challenge", "Solution", "FixedSourceSolution", "FixedSourceChallenge",
        )
        for name in production_modules:
            compile_module(name, fixture_root.joinpath(*name.split(".")).with_suffix(".lean"),
                           fixture_root, build, env)

        positive = run_fixture(
            build, "GuardFixture.safeTerminal", "GuardFixture.forbiddenProducer", "GuardFixtureSafe"
        )
        if positive.returncode != 0 or "forbidden hits: 0" not in positive.stdout + positive.stderr:
            raise RuntimeError(f"safe positive fixture failed:\n{positive.stdout}{positive.stderr}")

        negative = run_fixture(
            build, "GuardFixture.transitiveBadTerminal",
            "GuardFixture.transitiveForbiddenProducer", "GuardFixtureBadRoot",
        )
        negative_output = negative.stdout + negative.stderr
        if negative.returncode == 0 or "transitiveForbiddenProducer" not in negative_output:
            raise RuntimeError(f"transitive forbidden producer escaped:\n{negative_output}")
        if "body_load_round=1" not in negative_output or "GuardFixtureRelay" not in negative_output:
            raise RuntimeError(f"runner did not expand missing opaque-body owner:\n{negative_output}")

        routed = run_route_fixture(
            build, "GuardFixtureRoute.goodRoot", "GuardFixtureRoute.requiredToken",
            "GuardFixtureRoute.forbiddenToken",
        )
        routed_output = routed.stdout + routed.stderr
        if routed.returncode != 0 or "dependency route passed" not in routed_output:
            raise RuntimeError(f"valid required/excluded dependency route failed:\n{routed_output}")

        opaque_route = run_route_fixture(
            build, "GuardFixtureRoute.opaqueRoot", "GuardFixtureRoute.opaqueToken",
            "GuardFixtureRoute.forbiddenToken",
        )
        opaque_output = opaque_route.stdout + opaque_route.stderr
        if opaque_route.returncode != 0 or "dependency route passed" not in opaque_output:
            raise RuntimeError(f"complete opaque-body route failed:\n{opaque_output}")

        missing_required = run_route_fixture(
            build, "GuardFixtureRoute.noRequiredRoot", "GuardFixtureRoute.requiredToken",
            "GuardFixtureRoute.forbiddenToken",
        )
        missing_output = missing_required.stdout + missing_required.stderr
        if missing_required.returncode == 0 or "did not reach required endpoint" not in missing_output:
            raise RuntimeError(f"route checker accepted a missing required endpoint:\n{missing_output}")

        reached_forbidden = run_route_fixture(
            build, "GuardFixtureRoute.badRoot", "GuardFixtureRoute.requiredToken",
            "GuardFixtureRoute.forbiddenToken",
        )
        forbidden_output = reached_forbidden.stdout + reached_forbidden.stderr
        if reached_forbidden.returncode == 0 or "reached forbidden endpoint" not in forbidden_output:
            raise RuntimeError(f"route checker accepted a reached forbidden endpoint:\n{forbidden_output}")

        incomplete_route = run_route_fixture(
            build, "GuardFixtureMissing.terminal", "GuardFixtureMissing.terminal",
            "GuardFixtureMissing.unavailableProducer", "GuardFixtureMissingBody",
        )
        incomplete_output = incomplete_route.stdout + incomplete_route.stderr
        if incomplete_route.returncode == 0 or "was incomplete" not in incomplete_output:
            raise RuntimeError(f"route checker accepted unavailable dependency bodies:\n{incomplete_output}")

        unavailable = run_fixture(
            build, "GuardFixtureMissing.terminal", "GuardFixture.forbiddenProducer",
            "GuardFixtureMissingBody",
        )
        unavailable_output = unavailable.stdout + unavailable.stderr
        if unavailable.returncode == 0 or "bodyless axiom is not on the explicit standard-axiom allowlist" not in unavailable_output:
            raise RuntimeError(f"unapproved bodyless axiom was not rejected:\n{unavailable_output}")

        production = run_production_fixture(build)
        production_output = production.stdout + production.stderr
        if production.returncode == 0:
            raise RuntimeError(f"production guard accepted fixture's forbidden old route:\n{production_output}")
        if "GeneralAsymptoticLaurentAxis" not in production_output:
            raise RuntimeError(f"production guard missed forbidden old module owner:\n{production_output}")
        if "exists_groundConormalAxis_of_minimalPrime_unit_transcendental" not in production_output:
            raise RuntimeError(f"production guard missed the exact banned producer:\n{production_output}")
        if "exists_groundConormalAxis_of_regularizedOneRowConormalData" not in production_output:
            raise RuntimeError(f"production guard missed the fixed-source banned producer:\n{production_output}")
        if "exists_finiteGradientBoundaryCertificateOver_of_hasVisibleDivisorFrame" not in production_output:
            raise RuntimeError(f"production guard missed the visible-divisor-frame baseline producer:\n{production_output}")
        if "sorryAx" in production_output:
            raise RuntimeError(f"production guard imported a Challenge placeholder:\n{production_output}")
        production_roots = (
            "Stafford38.universalStatement",
            "Stafford38Challenge.universalStatement",
            "Stafford38.universalFixedSourceStatement",
            "Stafford38FixedSourceChallenge.universalFixedSourceStatement",
        )
        for root in production_roots:
            if f"root: {root};" not in production_output:
                raise RuntimeError(f"production guard omitted terminal root {root}:\n{production_output}")

        for root, module in (
            ("Stafford38Challenge.universalStatement", "Challenge"),
            ("Stafford38FixedSourceChallenge.universalFixedSourceStatement", "FixedSourceChallenge"),
        ):
            placeholder = run_challenge_placeholder(build, root, module)
            placeholder_output = placeholder.stdout + placeholder.stderr
            if placeholder.returncode == 0 or "sorryAx" not in placeholder_output:
                raise RuntimeError(f"challenge placeholder escaped the sorryAx check ({module}):\n{placeholder_output}")

    print("PASS: safe closure accepted; transitive opaque/private producer rejected after owner expansion; required route accepted; missing required, reached forbidden, and incomplete route closures rejected; unapproved axiom fails closed; Solution roots reject the exact banned route; Challenge placeholder roots reject sorryAx")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
