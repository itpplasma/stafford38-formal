#!/usr/bin/env bash
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

log_dir=.lake/verification
mkdir -p "$log_dir"

python3 scripts/check-layout.py >"$log_dir/layout.log" 2>&1

python3 tests/palomar-source-requirements-behavior.py >"$log_dir/source-policy-behavior.log" 2>&1
python3 tests/palomar-policy-pin-behavior.py >"$log_dir/policy-pin-behavior.log" 2>&1
python3 tests/dependency-guard-fixtures/test_toolchain_resolution.py \
  >"$log_dir/dependency-guard-toolchain-resolution.log" 2>&1
python3 scripts/check-palomar-policy.py
bash scripts/bootstrap-palomar-tools.sh
bash tests/palomar-comparator-behavior.sh >"$log_dir/palomar-behavior.log" 2>&1

python3 tests/dependency-guard-fixtures/test_behavior.py \
  >"$log_dir/dependency-guard-behavior.log" 2>&1

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
  Stafford38.PaperClaimDefinitions \
  Stafford38.Paper.Section7 \
  Stafford38.Geometry.GeneralTangentLimitCriterion \
  Stafford38.Geometry.GeneralAsymptoticConormal \
  Stafford38.Geometry.GeneralCoisotropicSets \
  Stafford38.Geometry.GeneralCoisotropicCanonicalAdapter \
  Solution FixedSourceSolution AlternativeSolution AlternativeFixedSourceSolution \
  CorollaryChallenge PaperPairChallenge \
  >"$log_dir/build.log" 2>&1

python3 scripts/dependency-guard/run_guard.py \
  --base-module AlternativeSolution \
  --base-module AlternativeFixedSourceSolution \
  >"$log_dir/terminal-dependency-guard.log" 2>&1

# Stafford38Challenge.evolutionaryIdentity is left out of the two guards below:
# its certificate reaches Mathlib's complex analysis, whose bodies the guard
# cannot load within its time cap. It does not use Theorem 1.1, and the axiom
# audit and Comparator cover it. The added roots import more owner modules in
# each body-loading round, so these two guards run with a longer cap.
python3 scripts/dependency-guard/run_guard.py --timeout-seconds 1500 \
  --base-module Solution \
  --base-module FixedSourceSolution \
  --terminal-root Stafford38.Paper.theorem_1_1 \
  --terminal-root Stafford38.Paper.theorem_1_1_fixedSource \
  --terminal-root Stafford38.Paper.corollary_6_3 \
  --terminal-root Stafford38.Paper.corollary_6_3_stablyCyclic \
  --terminal-root Stafford38.Paper.Section7.leftHandedIdentity \
  --terminal-root Stafford38.Paper.Section7.corollary_6_3_left \
  --terminal-root Stafford38.Paper.Section7.localizedDifferentialIdentity \
  --terminal-root Stafford38Challenge.universalStatement \
  --terminal-root Stafford38Challenge.theorem_1_1 \
  --terminal-root Stafford38Challenge.corollary_6_3 \
  --terminal-root Stafford38Challenge.corollary_6_3_stablyCyclic \
  --terminal-root Stafford38Challenge.leftHandedIdentity \
  --terminal-root Stafford38Challenge.corollary_6_3_left \
  --terminal-root Stafford38Challenge.localizedDifferentialIdentity \
  --terminal-root Stafford38Challenge.principalOpenDifferentialIdentity \
  --terminal-root Stafford38Challenge.laurentDifferentialIdentity \
  --terminal-root Stafford38Challenge.fractionFieldDifferentialIdentity \
  --terminal-root Stafford38FixedSourceChallenge.universalFixedSourceStatement \
  >"$log_dir/paper-terminal-dependency-guard.log" 2>&1

python3 scripts/dependency-guard/run_guard.py --timeout-seconds 1500 \
  --base-module Solution \
  --base-module FixedSourceSolution \
  --route Stafford38Challenge.universalStatement Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.universalStatement Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.theorem_1_1 Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.theorem_1_1 Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38FixedSourceChallenge.universalFixedSourceStatement Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38FixedSourceChallenge.universalFixedSourceStatement Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.universalStatement Stafford38.Paper.theorem_1_1 Stafford38.universalStatement \
  --route Stafford38Challenge.theorem_1_1 Stafford38.Paper.theorem_1_1 Stafford38.universalStatement \
  --route Stafford38Challenge.corollary_6_3 Stafford38.Paper.theorem_1_1 Stafford38.universalStatement \
  --route Stafford38Challenge.corollary_6_3_stablyCyclic Stafford38.Paper.theorem_1_1 Stafford38.universalStatement \
  --route Stafford38Challenge.leftHandedIdentity Stafford38.Paper.theorem_1_1 Stafford38.universalStatement \
  --route Stafford38Challenge.corollary_6_3_left Stafford38.Paper.theorem_1_1 Stafford38.universalStatement \
  --route Stafford38Challenge.localizedDifferentialIdentity Stafford38.Paper.theorem_1_1 Stafford38.universalStatement \
  --route Stafford38Challenge.principalOpenDifferentialIdentity Stafford38.Paper.theorem_1_1 Stafford38.universalStatement \
  --route Stafford38Challenge.laurentDifferentialIdentity Stafford38.Paper.theorem_1_1 Stafford38.universalStatement \
  --route Stafford38Challenge.fractionFieldDifferentialIdentity Stafford38.Paper.theorem_1_1 Stafford38.universalStatement \
  --route Stafford38Challenge.corollary_6_3 Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.corollary_6_3_stablyCyclic Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.leftHandedIdentity Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.corollary_6_3_left Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.localizedDifferentialIdentity Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.principalOpenDifferentialIdentity Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.laurentDifferentialIdentity Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.fractionFieldDifferentialIdentity Stafford38.Paper.Section5.theorem_5_8 Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38Challenge.corollary_6_3 Stafford38.Paper.Section6.corollary_6_3_of Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion \
  --route Stafford38Challenge.corollary_6_3_stablyCyclic Stafford38.Paper.Section6.corollary_6_3_of Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion \
  --route Stafford38Challenge.corollary_6_3_left Stafford38.Paper.Section6.corollary_6_3_of Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion \
  >"$log_dir/main-solution-dependency-routes.log" 2>&1

python3 scripts/dependency-guard/run_guard.py \
  --base-module AlternativeSolution \
  --base-module AlternativeFixedSourceSolution \
  --route Stafford38Challenge.universalStatement Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure Stafford38.Paper.Section5.theorem_5_8 \
  --route Stafford38FixedSourceChallenge.universalFixedSourceStatement Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure Stafford38.Paper.Section5.theorem_5_8 \
  >"$log_dir/alternative-solution-dependency-routes.log" 2>&1

lake env lean --trust=0 tests/PaperAdaptersConsumer.lean >"$log_dir/paper-adapters.log" 2>&1
lake env lean --trust=0 tests/PaperPairConsumer.lean >"$log_dir/paper-pair.log" 2>&1
python3 - <<'PYPAIR'
import re
from pathlib import Path
text = Path('.lake/verification/paper-pair.log').read_text()
m = re.search(r"'Stafford38PaperPairChallenge.pairGeneratorStatement_consumer' depends on axioms:\s*\[(.*?)\]", text, re.S)
if not m or {x.strip() for x in m[1].split(',') if x.strip()} - {'propext', 'Quot.sound', 'Classical.choice'}:
    raise SystemExit('Supplementary pair consumer has a missing or forbidden axiom report')
print('Supplementary literal pair consumer: exact statement and permitted axioms passed')
PYPAIR
bash scripts/check-consumers.sh
bash scripts/check-paper-declarations.sh

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
if challenge_holes != ["sorry"] * 11:
    raise SystemExit("Challenge.lean must contain exactly eleven deliberate sorries and no admit")
imports = re.findall(r"(?m)^\s*(?:public\s+)?import\s+([^\s]+)\s*$", challenge_code)
expected_imports = [
    "Mathlib.Algebra.RingQuot",
    "Mathlib.Algebra.FreeAlgebra",
    "Mathlib.LinearAlgebra.SymplecticGroup",
    "Mathlib.Order.Lattice.Nat",
]
expected_challenge_imports = expected_imports + [
    "Mathlib.RingTheory.Localization.FractionRing",
    "Mathlib.RingTheory.Localization.Away.Basic",
]
if imports != expected_challenge_imports:
    raise SystemExit(f"unexpected Challenge imports: {imports!r}")

strong_challenge = Path("FixedSourceChallenge.lean")
if not strong_challenge.is_file():
    raise SystemExit("FixedSourceChallenge.lean is missing")
strong_code = code_without_comments_or_strings(strong_challenge.read_text(encoding="utf-8"))
if re.findall(r"\b(?:sorry|admit)\b", strong_code) != ["sorry"]:
    raise SystemExit("FixedSourceChallenge.lean must contain exactly one deliberate sorry and no admit")
strong_imports = re.findall(r"(?m)^\s*(?:public\s+)?import\s+([^\s]+)\s*$", strong_code)
expected_strong_imports = expected_imports
if strong_imports != expected_strong_imports:
    raise SystemExit(f"unexpected FixedSourceChallenge imports: {strong_imports!r}")

# Both comparison inputs share this one definition owner. Its exact direct
# imports and the loaded-environment scans below keep the owner Mathlib-only;
# the source audit includes it and rejects any proof placeholder or axiom.
owner_code = code_without_comments_or_strings(
    Path("Stafford38/ChallengeDefinitions.lean").read_text(encoding="utf-8"))
owner_imports = re.findall(r"(?m)^\s*(?:public\s+)?import\s+([^\s]+)\s*$", owner_code)
expected_owner_imports = [
    "Mathlib.Algebra.RingQuot",
    "Mathlib.Algebra.FreeAlgebra",
    "Mathlib.LinearAlgebra.SymplecticGroup",
    "Mathlib.Order.Lattice.Nat",
]
if owner_imports != expected_owner_imports:
    raise SystemExit(f"unexpected challenge definition owner imports: {owner_imports!r}")

# The selected Challenge cannot import a project-local owner under current
# Palomar policy. Keep its inlined definitions byte-for-byte equivalent at
# the code level; Comparator independently checks the reached declarations.
owner_definitions = owner_code[owner_code.index("namespace Stafford\n"):].strip()
# The further paper claims have a second owner, repeated in Challenge.lean
# right after the first.
claims_code = code_without_comments_or_strings(
    Path("Stafford38/PaperClaimDefinitions.lean").read_text(encoding="utf-8"))
claims_imports = re.findall(r"(?m)^\s*(?:public\s+)?import\s+([^\s]+)\s*$", claims_code)
if claims_imports != ["Stafford38.ChallengeDefinitions",
                      "Mathlib.RingTheory.Localization.FractionRing",
                      "Mathlib.RingTheory.Localization.Away.Basic"]:
    raise SystemExit(f"unexpected paper-claim definition owner imports: {claims_imports!r}")
claims_definitions = claims_code[claims_code.index("namespace Stafford38Challenge\n"):].strip()
challenge_rest = challenge_code[challenge_code.index("namespace Stafford\n"):].strip()
if not challenge_rest.startswith(owner_definitions + "\n"):
    raise SystemExit("Challenge.lean inlined definitions differ from the solution's definition owner")
if not challenge_rest[len(owner_definitions):].strip().startswith(claims_definitions + "\n"):
    raise SystemExit("Challenge.lean inlined paper-claim definitions differ from Stafford38.PaperClaimDefinitions")
for label, code in (("Challenge.lean", challenge_code),
                    ("FixedSourceChallenge.lean", strong_code)):
    definitions_and_statement = code[code.index("namespace Stafford\n"):].strip()
    if not definitions_and_statement.startswith(owner_definitions + "\n"):
        raise SystemExit(f"{label} inlined definitions differ from the solution's definition owner")

# The two intentional theorem placeholders are permitted, but neither
# comparison input may introduce an additional project axiom.
for label, code in (("Challenge.lean", challenge_code),
                    ("FixedSourceChallenge.lean", strong_code)):
    if re.search(r"(?m)^\s*axiom\s+", code):
        raise SystemExit(f"project axiom declaration in {label}")

# Neither Solution may import either Challenge, at source level; the loaded
# environment audit below repeats this for the transitive closure.
challenge_roots = {"Challenge", "FixedSourceChallenge"}
for solution_name in ("Solution.lean", "FixedSourceSolution.lean",
                      "AlternativeSolution.lean", "AlternativeFixedSourceSolution.lean"):
    solution = Path(solution_name)
    if not solution.is_file():
        raise SystemExit(f"{solution_name} is missing")
    solution_code = code_without_comments_or_strings(solution.read_text(encoding="utf-8"))
    solution_imports = re.findall(r"(?m)^\s*(?:public\s+)?import\s+([^\s]+)\s*$", solution_code)
    if any(name.split(".")[0] in challenge_roots for name in solution_imports):
        raise SystemExit(f"{solution_name} must not import Challenge, FixedSourceChallenge, or a submodule")

for path in Path(".").rglob("*.lean"):
    if path in {challenge, Path('FixedSourceChallenge.lean')} or any(part in excluded_parts for part in path.parts):
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

print("source audit: only the deliberate placeholders of the compared theorems in each Challenge; neither Solution imports either Challenge; no other sorry, admit, or axiom declaration")
PY

cat >"$log_dir/AxiomAudit.lean" <<'LEAN'
import Stafford38
import FixedSourceSolution
import Stafford38.Geometry.GeneralTangentLimitCriterion
import Stafford38.Geometry.GeneralAsymptoticConormal
import Stafford38.Geometry.GeneralCoisotropicSets
import Stafford38.Geometry.GeneralCoisotropicCanonicalAdapter
import Stafford38.Geometry.GeneralCoisotropicSetsTest
import Stafford38.Geometry.GeneralTangentLimitCriterionTest

#print axioms Stafford38.Weyl.EulerProductIdentities.eval_fallingEulerProduct
#print axioms Stafford38.Weyl.EulerProductIdentities.eval_risingEulerProduct
#print axioms Stafford38.NoncharacteristicHypersurface.normalMomentumPolynomialEquiv_normalCoordinate
#print axioms Stafford38.NoncharacteristicHypersurface.normalMomentumPolynomialEquiv_tangentialMap
#print axioms Stafford38.NoncharacteristicHypersurface.canonical_principal_hypersurface_finite
#print axioms Stafford38.WeylDomain.mul_ne_zero
#print axioms Stafford38.TorsionCyclicity.exists_span_singleton_eq_span_pair
#print axioms Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion
#print axioms Stafford38.NoncharacteristicHyperplane.canonical_isNoncharacteristic_annihilator
#print axioms Stafford38.NoncharacteristicHyperplane.canonicalSupport_conormal_subset_zeroSection
#print axioms Stafford38.NoncharacteristicHyperplane.cokerToRestrictedCoordinateRing_surjective
#print axioms Stafford38.NoncharacteristicHyperplane.canonical_finite_restrictedCoordinateQuotient
#print axioms Stafford38.NoncharacteristicHyperplane.cokerToRestrictedCoordinateRing_mk
#print axioms Stafford38.NoncharacteristicHyperplane.cokerToRestrictedCoordinateRing_injective
#print axioms Stafford38.NoncharacteristicHyperplane.cokerToRestrictedCoordinateRingEquiv
#print axioms Stafford38.NoncharacteristicHyperplane.isNoncharacteristic_iff_finite_restrictedCoordinateQuotient
#print axioms Stafford38.universalStatement
#print axioms Stafford38.universalFixedSourceStatement
#print axioms Stafford38FixedSourceChallenge.universalFixedSourceStatement
#print axioms Stafford38.Paper.theorem_1_1
#print axioms Stafford38.Paper.theorem_1_1_fixedSource
#print axioms Stafford38.Paper.corollary_6_3
#print axioms Stafford38.Paper.corollary_6_3_stablyCyclic
#print axioms Stafford38.Paper.Section7.leftHandedIdentity
#print axioms Stafford38.Paper.Section7.corollary_6_3_left
#print axioms Stafford38.Paper.Section7.localizedDifferentialIdentity
#print axioms Stafford38.Paper.Section7.evolutionaryIdentity
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
#print axioms Stafford38.TorsionCyclicity.span_adjusted_pair_eq_span_pair
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
    "Stafford38.NoncharacteristicHypersurface.normalMomentumPolynomialEquiv_normalCoordinate",
    "Stafford38.NoncharacteristicHypersurface.normalMomentumPolynomialEquiv_tangentialMap",
    "Stafford38.NoncharacteristicHypersurface.canonical_principal_hypersurface_finite",
    "Stafford38.Weyl.EulerProductIdentities.eval_fallingEulerProduct",
    "Stafford38.Weyl.EulerProductIdentities.eval_risingEulerProduct",
    "Stafford38.NoncharacteristicHyperplane.cokerToRestrictedCoordinateRing_mk",
    "Stafford38.NoncharacteristicHyperplane.cokerToRestrictedCoordinateRing_injective",
    "Stafford38.NoncharacteristicHyperplane.cokerToRestrictedCoordinateRingEquiv",
    "Stafford38.NoncharacteristicHyperplane.isNoncharacteristic_iff_finite_restrictedCoordinateQuotient",
    "Stafford38.NoncharacteristicHyperplane.cokerToRestrictedCoordinateRing_surjective",
    "Stafford38.NoncharacteristicHyperplane.canonical_finite_restrictedCoordinateQuotient",
    "Stafford38.WeylDomain.mul_ne_zero",
    "Stafford38.TorsionCyclicity.exists_span_singleton_eq_span_pair",
    "Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion",
    "Stafford38.NoncharacteristicHyperplane.canonical_isNoncharacteristic_annihilator",
    "Stafford38.NoncharacteristicHyperplane.canonicalSupport_conormal_subset_zeroSection",
    "Stafford38.universalStatement",
    "Stafford38.universalFixedSourceStatement",
    "Stafford38FixedSourceChallenge.universalFixedSourceStatement",
    "Stafford38.Paper.theorem_1_1",
    "Stafford38.Paper.theorem_1_1_fixedSource",
    "Stafford38.Paper.corollary_6_3",
    "Stafford38.Paper.corollary_6_3_stablyCyclic",
    "Stafford38.Paper.Section7.leftHandedIdentity",
    "Stafford38.Paper.Section7.corollary_6_3_left",
    "Stafford38.Paper.Section7.localizedDifferentialIdentity",
    "Stafford38.Paper.Section7.evolutionaryIdentity",
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
    "Stafford38.TorsionCyclicity.span_adjusted_pair_eq_span_pair",
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

lake build Challenge FixedSourceChallenge CorollaryChallenge >"$log_dir/challenge-build.log" 2>&1
bash scripts/check-import-closure.sh Challenge
bash scripts/check-import-closure.sh CorollaryChallenge
bash scripts/check-import-closure.sh Solution
bash scripts/check-import-closure.sh FixedSourceChallenge
bash scripts/check-import-closure.sh FixedSourceSolution
bash scripts/check-import-closure.sh AlternativeSolution
bash scripts/check-import-closure.sh AlternativeFixedSourceSolution

lake env lean --trust=0 Solution.lean >"$log_dir/solution.log" 2>&1
lake env lean --trust=0 FixedSourceSolution.lean >>"$log_dir/solution.log" 2>&1
lake env lean --trust=0 AlternativeSolution.lean >>"$log_dir/solution.log" 2>&1
lake env lean --trust=0 AlternativeFixedSourceSolution.lean >>"$log_dir/solution.log" 2>&1

if grep -Eq "sorryAx|admitAx|Lean\.ofReduceBool|declaration uses 'sorry'|(^|:) error(\([^)]*\))?:" \
    "$log_dir/build.log" "$log_dir/axioms.log" "$log_dir/solution.log"; then
  echo "compiled verification logs contain a forbidden marker or Lean error" >&2
  exit 1
fi

echo "Stafford38 verification passed"
