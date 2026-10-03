#!/usr/bin/env python3
"""Small policy-checker oracle; no Lean build or network access is needed."""
from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SOURCE_ROOT = Path(__file__).resolve().parents[1]
LEAN = "leanprover/lean4:v4.35.0-rc3"
MATHLIB_URL = "https://github.com/leanprover-community/mathlib4"
MATHLIB = "c55e6e786f49471c72fbddbec5415808896aec1e"
AA_URL = "https://github.com/itpplasma/algebraic-analysis.git"
AA = "bbbbf3fc358ca8100b158cec4cf47f336ab70163"


with tempfile.TemporaryDirectory(prefix="palomar-pin-check-") as temp:
    project = Path(temp)
    (project / "scripts").mkdir()
    for name in ("check-palomar-policy.py", "source_requirements.py", "verification_errors.py", "palomar-policy-LICENSE"):
        shutil.copy2(SOURCE_ROOT / "scripts" / name, project / "scripts" / name)
    configs = (
        "comparator.json", "comparator-fixed-source.json",
        "comparator-alternative.json", "comparator-alternative-fixed-source.json",
    )
    for name in configs:
        shutil.copy2(SOURCE_ROOT / name, project / name)
    (project / "lean-toolchain").write_text(LEAN + "\n", encoding="utf-8")
    (project / "lakefile.toml").write_text(
        f'[[require]]\nname = "mathlib"\ngit = "{MATHLIB_URL}"\nrev = "{MATHLIB}"\n\n'
        f'[[require]]\nname = "algebraicAnalysis"\ngit = "{AA_URL}"\nrev = "{AA}"\n',
        encoding="utf-8",
    )
    (project / "lake-manifest.json").write_text(json.dumps({"packages": [
        {"name": "mathlib", "url": MATHLIB_URL, "rev": MATHLIB, "inputRev": MATHLIB},
        {"name": "algebraicAnalysis", "url": AA_URL, "rev": AA, "inputRev": AA},
    ]}), encoding="utf-8")
    (project / "Challenge.lean").write_text("module Challenge\n", encoding="utf-8")
    (project / "Solution.lean").write_text("module Solution\n", encoding="utf-8")

    command = [sys.executable, "scripts/check-palomar-policy.py"]
    good = subprocess.run(command, cwd=project, text=True, capture_output=True, check=False)
    assert good.returncode == 0, good.stdout + good.stderr
    assert "2 Lean files satisfy" in good.stdout
    assert AA in good.stdout

    for name in configs:
        accepted = subprocess.run(
            [*command, "--config-only", name], cwd=project,
            text=True, capture_output=True, check=False,
        )
        assert accepted.returncode == 0, accepted.stdout + accepted.stderr
        assert "exact theorem/axiom contract passed" in accepted.stdout

    alt_config = project / "comparator-alternative.json"
    original_alt_config = alt_config.read_text(encoding="utf-8")
    alt_config.write_text(
        original_alt_config.replace("AlternativeSolution", "Solution"), encoding="utf-8"
    )
    mismatched_variant = subprocess.run(
        [*command, "--config-only", "comparator-alternative.json"], cwd=project,
        text=True, capture_output=True, check=False,
    )
    assert mismatched_variant.returncode != 0
    assert "exact theorem/axiom contract" in mismatched_variant.stderr
    alt_config.write_text(original_alt_config, encoding="utf-8")

    manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest["packages"][1]["inputRev"] = "1" * 40
    (project / "lake-manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
    bad = subprocess.run(command, cwd=project, text=True, capture_output=True, check=False)
    assert bad.returncode != 0
    assert "lake-manifest.json does not resolve the frozen AlgebraicAnalysis commit" in bad.stderr

    manifest["packages"][1]["inputRev"] = AA
    (project / "lake-manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
    policy_source = project / "scripts/source_requirements.py"
    original_policy_source = policy_source.read_bytes()
    policy_source.write_bytes(original_policy_source + b"\n# modified\n")
    tampered = subprocess.run(command, cwd=project, text=True, capture_output=True, check=False)
    assert tampered.returncode != 0
    assert "vendored Palomar source policy scripts/source_requirements.py changed" in tampered.stderr

    policy_source.write_bytes(original_policy_source)
    license_file = project / "scripts/palomar-policy-LICENSE"
    license_file.write_bytes(license_file.read_bytes() + b"\n")
    tampered_license = subprocess.run(command, cwd=project, text=True, capture_output=True, check=False)
    assert tampered_license.returncode != 0
    assert "vendored Palomar policy license changed" in tampered_license.stderr

print("PASS: exact release pins and all four main/alternative comparator contracts accepted; variant mixing, altered dependency lock, and modified vendored policy source/license rejected before any build")
