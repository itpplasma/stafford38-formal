#!/usr/bin/env python3
"""Behavior oracle for strict Lean resolution under default and isolated ELAN_HOME."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import tempfile
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
RUNNER_PATH = ROOT / "scripts/dependency-guard/run_guard.py"
SPEC = importlib.util.spec_from_file_location("stafford_run_guard", RUNNER_PATH)
assert SPEC is not None and SPEC.loader is not None
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)

PINNED_VERSION = (
    "Lean (version 4.35.0-rc3, x86_64-unknown-linux-gnu, "
    "commit 470d5ce1400764999581fd26d5d72b00d990b0f4, Release)"
)
WRONG_VERSION = PINNED_VERSION.replace(
    "470d5ce1400764999581fd26d5d72b00d990b0f4", "1" * 40
)


def install_fake_lean(elan_home: Path, version: str) -> Path:
    executable = elan_home / RUNNER.ELAN_TOOLCHAIN_PATH
    executable.parent.mkdir(parents=True, exist_ok=True)
    executable.write_text(
        "#!/bin/sh\nprintf '%s\\n' '" + version + "'\n", encoding="utf-8"
    )
    executable.chmod(0o755)
    return executable


with tempfile.TemporaryDirectory(prefix="stafford-elan-resolution-") as temporary:
    scratch = Path(temporary)
    isolated = scratch / "cluster" / "elan"
    expected = install_fake_lean(isolated, PINNED_VERSION)
    with patch.dict(os.environ, {"ELAN_HOME": str(isolated)}):
        assert RUNNER.lean_binary() == expected
        assert "commit 470d5ce1400764999581fd26d5d72b00d990b0f4" in RUNNER.check_lean()

    default_home = scratch / "default-home"
    default = install_fake_lean(default_home / ".elan", PINNED_VERSION)
    with patch.dict(os.environ):
        os.environ.pop("ELAN_HOME", None)
        with patch("pathlib.Path.home", return_value=default_home):
            assert RUNNER.lean_binary() == default
            assert RUNNER.check_lean().startswith("Lean (version 4.35.0-rc3,")

    wrong_root = scratch / "wrong-elan"
    path_lean = scratch / "path-bin" / "lean"
    path_lean.parent.mkdir()
    path_lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    path_lean.chmod(0o755)
    with patch.dict(os.environ, {"ELAN_HOME": str(wrong_root), "PATH": str(path_lean.parent)}):
        try:
            RUNNER.check_lean()
        except SystemExit as error:
            assert "pinned RC3 Lean binary is missing" in str(error)
        else:
            raise AssertionError("missing isolated toolchain fell through to PATH")

    wrong_version_home = scratch / "wrong-version"
    install_fake_lean(wrong_version_home, WRONG_VERSION)
    with patch.dict(os.environ, {"ELAN_HOME": str(wrong_version_home)}):
        try:
            RUNNER.check_lean()
        except SystemExit as error:
            assert "expected leanprover/lean4:v4.35.0-rc3 commit" in str(error)
        else:
            raise AssertionError("wrong RC3 commit passed the pinned toolchain check")

print("PASS: isolated and default ELAN_HOME resolve the exact pinned Lean; missing binaries do not fall through to PATH; wrong commits are rejected")
