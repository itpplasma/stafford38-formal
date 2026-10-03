module
public import Stafford38.Geometry.EtaleProjectiveTangentComparison
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
namespace FiniteParameterTangentConsumer
noncomputable section
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.EtaleCotangentBasis

variable {k : Type*} [Field k] {n d : ℕ}
variable {I : Ideal (MvPolynomial (Fin n) k)}
variable {C L : Type*} [CommRing C] [Field L]
variable [Algebra k C] [Algebra k L]
variable [Algebra (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra (MvPolynomial (Fin n) k ⧸ I) L]
variable [Algebra C L] [Algebra (MvPolynomial (Fin n) k) C]
variable [Algebra (MvPolynomial (Fin n) k) L]
variable [Algebra (MvPolynomial (Option (Fin d)) k) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) L]
variable [IsScalarTower k (MvPolynomial (Fin n) k) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k) L]
variable [IsScalarTower k (MvPolynomial (Option (Fin d)) k) C]
variable [IsScalarTower k C L]
variable [IsScalarTower (MvPolynomial (Fin n) k)
  (MvPolynomial (Fin n) k ⧸ I) C]
variable [IsScalarTower (MvPolynomial (Fin n) k)
  (MvPolynomial (Fin n) k ⧸ I) L]
variable [IsScalarTower (MvPolynomial (Fin n) k) C L]
variable [IsScalarTower (MvPolynomial (Fin n) k ⧸ I) C L]
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) C]

theorem optionChart_generates_actualCone
    (q : Fin (n + 1) → C) (h0 : algebraMap C L (q 0) ≠ 0)
    (hfactor : ∀ i, q i.succ = q 0 *
      algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i))) :
    projectiveTangentCone (fun i => algebraMap C L (q i))
      (zariskiTangentSpace (dehomogenizedPoint (fun i => algebraMap C L (q i)))
        (I.map (MvPolynomial.map (algebraMap k L)))) =
      Submodule.span L (Set.range fun j : Option (Option (Fin d)) => fun i =>
        match j with
        | none => algebraMap C L (q i)
        | some j => coordinateDerivation
            (k := k) (σ := Option (Fin d)) (B := C) (L := L) j (q i))  := by
  convert Stafford38.Geometry.EtaleProjectiveTangentComparison.FiniteParameters.projectiveTangentCone_eq_span_chartDerivation_columns
    (σ := Option (Fin d)) q h0 hfactor using 1
  congr 2
  funext j i
  cases j <;> rfl

/-- Independent one-parameter oracle: the radial and parameter generators
are both present for the nested Option index, even with no transverse rows. -/
def oneParameterColumns : Option (Option (Fin 0)) → Fin 2 → ℚ
  | none => ![1, 0]
  | some none => ![0, 1]
  | some (some i) => Fin.elim0 i

theorem oneParameter_span :
    Submodule.span ℚ (Set.range oneParameterColumns) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro v
  have h0 := Submodule.subset_span (R := ℚ) (s := Set.range oneParameterColumns)
    (Set.mem_range_self (f := oneParameterColumns) none)
  have h1 := Submodule.subset_span (R := ℚ) (s := Set.range oneParameterColumns)
    (Set.mem_range_self (f := oneParameterColumns) (some none))
  have hv := Submodule.add_mem _
    (Submodule.smul_mem _ (v 0) h0) (Submodule.smul_mem _ (v 1) h1)
  have heq : v 0 • oneParameterColumns none +
      v 1 • oneParameterColumns (some none) = v := by
    ext i
    fin_cases i <;> simp [oneParameterColumns]
  exact heq ▸ hv

#print axioms optionChart_generates_actualCone
#print axioms oneParameter_span
#print axioms Stafford38.Geometry.EtaleTangentChartSpan.FiniteParameters.tangentVector_eq_sum_parameterDerivations
#print axioms Stafford38.Geometry.EtaleTangentChartSpan.FiniteParameters.zariskiTangentSpace_eq_span_parameterDerivations
end
end FiniteParameterTangentConsumer
