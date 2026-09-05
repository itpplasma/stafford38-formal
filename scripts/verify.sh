#!/usr/bin/env bash
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

log_dir=.lake/verification
mkdir -p "$log_dir"

python3 scripts/check-layout.py >"$log_dir/layout.log" 2>&1

python3 - <<'PY'
import json
import re
import tomllib
from pathlib import Path

expected_toolchain = "leanprover/lean4:v4.33.0"
expected_mathlib = "db584cd6d46c92f209a44c0f1c829460d327499d"
expected_aa_url = "https://github.com/itpplasma/algebraic-analysis.git"
expected_aa = "dfdd2da091a9d67e7a29cc7914f192d746a2400d"

toolchain = Path("lean-toolchain").read_text(encoding="utf-8").strip()
if toolchain != expected_toolchain:
    raise SystemExit(f"unexpected Lean toolchain: {toolchain!r}")

with Path("lakefile.toml").open("rb") as handle:
    lakefile = tomllib.load(handle)
requires = {item["name"]: item for item in lakefile.get("require", [])}
with Path("lake-manifest.json").open(encoding="utf-8") as handle:
    manifest = json.load(handle)
packages = {item["name"]: item for item in manifest.get("packages", [])}

for name in ("mathlib", "algebraicAnalysis"):
    if name not in requires or name not in packages:
        raise SystemExit(f"missing required dependency: {name}")

mathlib = packages["mathlib"]
if requires["mathlib"].get("rev") != expected_mathlib:
    raise SystemExit("lakefile.toml does not pin the expected Mathlib commit")
if mathlib.get("rev") != expected_mathlib:
    raise SystemExit(f"unexpected resolved Mathlib commit: {mathlib.get('rev')!r}")

aa_request = requires["algebraicAnalysis"]
aa_manifest = packages["algebraicAnalysis"]
aa_rev = aa_request.get("rev", "")
if aa_request.get("git") != expected_aa_url:
    raise SystemExit(f"unexpected AlgebraicAnalysis URL: {aa_request.get('git')!r}")
if not re.fullmatch(r"[0-9a-f]{40}", aa_rev):
    raise SystemExit("AlgebraicAnalysis must be pinned by a full lowercase commit")
if aa_rev != expected_aa:
    raise SystemExit(f"unexpected AlgebraicAnalysis commit: {aa_rev!r}")
if aa_manifest.get("rev") != aa_rev or aa_manifest.get("inputRev") != aa_rev:
    raise SystemExit("AlgebraicAnalysis lakefile and manifest revisions differ")

print(f"pins: Lean 4.33.1, Mathlib {expected_mathlib}, AlgebraicAnalysis {aa_rev}")
PY

python3 tests/noncharacteristic_pages_oracle.py >"$log_dir/pages-oracle.log" 2>&1
python3 tests/operator_projection_oracle.py >"$log_dir/pbw-oracle.log" 2>&1

# Explicitly build retained compatibility modules as well as the aggregate.
mapfile -t retained_modules < <(python3 - <<'PY'
from pathlib import Path
for path in sorted(Path('Stafford38').rglob('*.lean')):
    print('.'.join(path.with_suffix('').parts))
PY
)
lake build "${retained_modules[@]}" \
  Stafford38 \
  Stafford38.FoundationClosure \
  Stafford38.LocalizationCorollaries \
  Stafford38.LeftHandedCorollary \
  Stafford38.LocalizedDifferentialCorollaries \
  Stafford38.EvolutionaryCorollary \
  Stafford38.Geometry.GeneralTangentLimitCriterion \
  Stafford38.Geometry.GeneralAsymptoticConormal \
  Stafford38.Geometry.GeneralCoisotropicSets \
  Stafford38.Geometry.GeneralCoisotropicCanonicalAdapter \
  Solution \
  >"$log_dir/build.log" 2>&1

bash scripts/check-consumers.sh

python3 - <<'PY'
import re
from pathlib import Path

def code_without_comments_or_strings(text: str) -> str:
    out = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                out.append(" ")
                in_string = False
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                out.extend(" " * (len(text) - i))
                break
            out.extend(" " * (end - i))
            i = end
        elif text.startswith("/-", i):
            out.extend("  ")
            block_depth = 1
            i += 2
        elif text[i] == '"':
            out.append(" ")
            in_string = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    if block_depth or in_string:
        raise SystemExit("unterminated Lean comment or string during source audit")
    return "".join(out)

excluded_parts = {".git", ".lake"}
challenge = Path("Challenge.lean")
if not challenge.is_file():
    raise SystemExit("Challenge.lean is missing")

challenge_code = code_without_comments_or_strings(challenge.read_text(encoding="utf-8"))
challenge_holes = re.findall(r"\b(?:sorry|admit)\b", challenge_code)
if challenge_holes != ["sorry"]:
    raise SystemExit("Challenge.lean must contain exactly one deliberate sorry and no admit")
imports = re.findall(r"(?m)^\s*import\s+([^\s]+)\s*$", challenge_code)
expected_imports = [
    "Mathlib.Algebra.RingQuot",
    "Mathlib.Algebra.FreeAlgebra",
    "Mathlib.LinearAlgebra.SymplecticGroup",
]
if imports != expected_imports:
    raise SystemExit(f"unexpected Challenge imports: {imports!r}")

solution = Path("Solution.lean")
if not solution.is_file():
    raise SystemExit("Solution.lean is missing")
solution_code = code_without_comments_or_strings(solution.read_text(encoding="utf-8"))
solution_imports = re.findall(r"(?m)^\s*import\s+([^\s]+)\s*$", solution_code)
if any(name == "Challenge" or name.startswith("Challenge.") for name in solution_imports):
    raise SystemExit("Solution.lean must not import Challenge or a Challenge submodule")

for path in Path(".").rglob("*.lean"):
    if path == challenge or any(part in excluded_parts for part in path.parts):
        continue
    code = code_without_comments_or_strings(path.read_text(encoding="utf-8"))
    hole = re.search(r"\b(?:sorry|admit)\b", code)
    if hole:
        line = code.count("\n", 0, hole.start()) + 1
        raise SystemExit(f"proof hole in {path}:{line}: {hole.group(0)}")
    axiom = re.search(r"(?m)^\s*axiom\s+", code)
    if axiom:
        line = code.count("\n", 0, axiom.start()) + 1
        raise SystemExit(f"project axiom declaration in {path}:{line}")

print("source audit: one Challenge placeholder; Solution is independent of Challenge; no other sorry, admit, or axiom declaration")
PY

cat >"$log_dir/AxiomAudit.lean" <<'LEAN'
import Stafford38
import Stafford38.Geometry.GeneralTangentLimitCriterion
import Stafford38.Geometry.GeneralAsymptoticConormal
import Stafford38.Geometry.GeneralCoisotropicSets
import Stafford38.Geometry.GeneralCoisotropicCanonicalAdapter
import Stafford38.Geometry.GeneralCoisotropicSetsTest
import Stafford38.Geometry.GeneralTangentLimitCriterionTest

#print axioms Stafford38.universalStatement
#print axioms Stafford38.universalFixedSourceStatement
#print axioms Stafford38.LocalizationCorollaries.s38_rightOreLocalization
#print axioms Stafford38.LeftHandedCorollary.leftHanded_of_universalStatement
#print axioms Stafford38.LocalizedDifferentialCorollaries.s38_unconditional_localized_differential
#print axioms Stafford38.LocalizedDifferentialCorollaries.s38_principal_open_differential
#print axioms Stafford38.LocalizedDifferentialCorollaries.s38_partial_laurent_differential
#print axioms Stafford38.LocalizedDifferentialCorollaries.s38_fraction_ring_differential
#print axioms Stafford38.Evolution.evolutionaryCorollary
#print axioms Stafford38.Evolution.tensorEvolutionaryCorollary
#print axioms Stafford38.Geometry.GeneralTangentLimitCriterion.tangent_limit_criterion_of_directSummand
#print axioms Stafford38.Geometry.GeneralAsymptoticConormal.coordinate_axis_mem_projective_conormal_directions
#print axioms Stafford38.Geometry.GeneralCoisotropicSets.exists_zero_base_coordinate_of_isFibreConical
#print axioms Stafford38.Geometry.GeneralCoisotropicSets.smoothConormalClosure_minimalPrime_subset_of_isFibreConical
#print axioms Stafford38.Geometry.GeneralCoisotropicCanonicalAdapter.algebraicallyClosedCanonicalSupportVanishing_of_generalCoisotropic
#print axioms Stafford38.Geometry.GeneralTangentLimitCriterionTest.paper_shape_consumer
#print axioms Stafford38.Geometry.GeneralCoisotropicSetsTest.exact_complex_manuscript_coisotropic_consumer
#print axioms Stafford38.Geometry.GeneralCoisotropicSetsTest.zeroSectionIdealOne_isInvolutive
#print axioms Stafford38.Geometry.GeneralCoisotropicSetsTest.zeroSectionIdealOne_not_isPoisson
LEAN

lake env lean --trust=0 "$log_dir/AxiomAudit.lean" \
  >"$log_dir/axioms.log" 2>&1

python3 - "$log_dir/axioms.log" <<'PY'
import re
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text(encoding="utf-8")
expected = {
    "Stafford38.universalStatement",
    "Stafford38.universalFixedSourceStatement",
    "Stafford38.LocalizationCorollaries.s38_rightOreLocalization",
    "Stafford38.LeftHandedCorollary.leftHanded_of_universalStatement",
    "Stafford38.LocalizedDifferentialCorollaries.s38_unconditional_localized_differential",
    "Stafford38.LocalizedDifferentialCorollaries.s38_principal_open_differential",
    "Stafford38.LocalizedDifferentialCorollaries.s38_partial_laurent_differential",
    "Stafford38.LocalizedDifferentialCorollaries.s38_fraction_ring_differential",
    "Stafford38.Evolution.evolutionaryCorollary",
    "Stafford38.Evolution.tensorEvolutionaryCorollary",
    "Stafford38.Geometry.GeneralTangentLimitCriterion.tangent_limit_criterion_of_directSummand",
    "Stafford38.Geometry.GeneralAsymptoticConormal.coordinate_axis_mem_projective_conormal_directions",
    "Stafford38.Geometry.GeneralCoisotropicSets.exists_zero_base_coordinate_of_isFibreConical",
    "Stafford38.Geometry.GeneralCoisotropicSets.smoothConormalClosure_minimalPrime_subset_of_isFibreConical",
    "Stafford38.Geometry.GeneralCoisotropicCanonicalAdapter.algebraicallyClosedCanonicalSupportVanishing_of_generalCoisotropic",
    "Stafford38.Geometry.GeneralTangentLimitCriterionTest.paper_shape_consumer",
    "Stafford38.Geometry.GeneralCoisotropicSetsTest.exact_complex_manuscript_coisotropic_consumer",
    "Stafford38.Geometry.GeneralCoisotropicSetsTest.zeroSectionIdealOne_isInvolutive",
    "Stafford38.Geometry.GeneralCoisotropicSetsTest.zeroSectionIdealOne_not_isPoisson",
}
allowed = {"propext", "Quot.sound", "Classical.choice"}
found = {}
for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", text, re.S):
    found[name] = {item.strip() for item in body.split(",") if item.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    found[name] = set()

missing = expected - found.keys()
if missing:
    raise SystemExit("missing axiom reports: " + ", ".join(sorted(missing)))
for name in sorted(expected):
    extra = found[name] - allowed
    if extra:
        raise SystemExit(f"{name} uses forbidden axioms: {sorted(extra)}")
if re.search(r"sorryAx|admitAx|Lean\.ofReduceBool", text):
    raise SystemExit("axiom log contains a forbidden proof mechanism")
print(f"axiom audit: {len(expected)} declarations use only {sorted(allowed)}")
PY

lake build Challenge >"$log_dir/challenge-build.log" 2>&1
bash scripts/check-import-closure.sh Challenge
bash scripts/check-import-closure.sh Solution

lake env lean --trust=0 Solution.lean >"$log_dir/solution.log" 2>&1

if grep -Eq "sorryAx|admitAx|Lean\.ofReduceBool|declaration uses 'sorry'|(^|:) error:" \
    "$log_dir/build.log" "$log_dir/axioms.log" "$log_dir/solution.log"; then
  echo "compiled verification logs contain a forbidden marker or Lean error" >&2
  exit 1
fi

echo "Stafford38 verification passed"
