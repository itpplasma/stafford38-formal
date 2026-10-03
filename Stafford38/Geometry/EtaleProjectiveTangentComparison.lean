module
public import Stafford38.Geometry.EtaleTangentChartSpan
public import Stafford38.Geometry.PaperDivisorTangent

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Stafford38.Geometry.EtaleProjectiveTangentComparison

noncomputable section
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.PaperDivisorTangent
open Stafford38.Geometry.EtaleCotangentBasis

namespace FiniteParameters

variable {k : Type*} [Field k] {n : ℕ}
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {I : Ideal (MvPolynomial (Fin n) k)}
variable {C L : Type*} [CommRing C] [Field L]
variable [Algebra k C] [Algebra k L]
variable [Algebra (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra (MvPolynomial (Fin n) k ⧸ I) L]
variable [Algebra C L] [Algebra (MvPolynomial (Fin n) k) C]
variable [Algebra (MvPolynomial (Fin n) k) L]
variable [Algebra (MvPolynomial (σ) k) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) L]
variable [IsScalarTower k (MvPolynomial (Fin n) k) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k) L]
variable [IsScalarTower k (MvPolynomial (σ) k) C]
variable [IsScalarTower k C L]
variable [IsScalarTower (MvPolynomial (Fin n) k)
  (MvPolynomial (Fin n) k ⧸ I) C]
variable [IsScalarTower (MvPolynomial (Fin n) k)
  (MvPolynomial (Fin n) k ⧸ I) L]
variable [IsScalarTower (MvPolynomial (Fin n) k) C L]
variable [IsScalarTower (MvPolynomial (Fin n) k ⧸ I) C L]
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra.FormallyEtale (MvPolynomial (σ) k) C]

/-- Actual local projective functions and the parameter derivations of one
common étale chart generate exactly the projective tangent cone of the
original affine presentation. The cone equality is proved, not supplied. -/
theorem projectiveTangentCone_eq_span_chartDerivation_columns
    (q : Fin (n + 1) → C) (h0 : algebraMap C L (q 0) ≠ 0)
    (hfactor : ∀ i, q i.succ = q 0 *
      algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i))) :
    projectiveTangentCone (fun i => algebraMap C L (q i))
      (zariskiTangentSpace (dehomogenizedPoint (fun i => algebraMap C L (q i)))
        (I.map (MvPolynomial.map (algebraMap k L)))) =
      Submodule.span L (Set.range fun j : Option (σ) => fun i =>
        match j with
        | none => algebraMap C L (q i)
        | some j => coordinateDerivation
            (k := k) (σ := σ) (B := C) (L := L) j (q i)) := by
  classical
  let y : Fin n → C := fun i =>
    algebraMap (MvPolynomial (Fin n) k ⧸ I) C
      (Ideal.Quotient.mk I (MvPolynomial.X i))
  let B : Matrix (Fin (n + 1)) (Option (σ)) L := fun i j =>
    match j with
    | none => algebraMap C L (q i)
    | some j => coordinateDerivation
        (k := k) (σ := σ) (B := C) (L := L) j (q i)
  have hpoint : ∀ i, dehomogenizedPoint (fun i => algebraMap C L (q i)) i =
      algebraMap C L (y i) := by
    intro i
    change algebraMap C L (q i.succ) / algebraMap C L (q 0) = _
    rw [hfactor i, map_mul]
    field_simp [h0]
    rfl
  have hcols : ∀ j, dehomogenizedTangentColumn
      (fun i => algebraMap C L (q i)) (fun i => B i j) =
      match j with
      | none => 0
      | some j => fun i => coordinateDerivation
          (k := k) (σ := σ) (B := C) (L := L) j (y i) := by
    intro j
    cases j with
    | none =>
        ext i
        simp [B]
    | some j =>
        exact dehomogenizedTangentColumn_derivation
          (coordinateDerivation (k := k) (σ := σ) (B := C) (L := L) j)
          q y h0 hfactor
  have hspan : zariskiTangentSpace
        (dehomogenizedPoint (fun i => algebraMap C L (q i)))
        (I.map (MvPolynomial.map (algebraMap k L))) =
      dehomogenizedTangentSpan (fun i => algebraMap C L (q i)) B := by
    rw [Stafford38.Geometry.EtaleTangentChartSpan.FiniteParameters.zariskiTangentSpace_eq_span_parameterDerivations
      (σ := σ) _ hpoint]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change (fun i => coordinateDerivation j (y i)) ∈ _
      exact Submodule.subset_span ⟨some j, hcols (some j)⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      dsimp only
      rw [hcols j]
      cases j with
      | none => exact Submodule.zero_mem _
      | some j => exact Submodule.subset_span ⟨j, rfl⟩
  apply projectiveTangentCone_eq_span_of_position_and_tangent
    (fun i => algebraMap C L (q i)) h0 _ B _ hspan
  exact Submodule.subset_span ⟨none, rfl⟩

end FiniteParameters

variable {k : Type*} [Field k] {n r : ℕ}
variable {I : Ideal (MvPolynomial (Fin n) k)}
variable {C L : Type*} [CommRing C] [Field L]
variable [Algebra k C] [Algebra k L]
variable [Algebra (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra (MvPolynomial (Fin n) k ⧸ I) L]
variable [Algebra C L] [Algebra (MvPolynomial (Fin n) k) C]
variable [Algebra (MvPolynomial (Fin n) k) L]
variable [Algebra (MvPolynomial (Fin r) k) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) L]
variable [IsScalarTower k (MvPolynomial (Fin n) k) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k) L]
variable [IsScalarTower k (MvPolynomial (Fin r) k) C]
variable [IsScalarTower k C L]
variable [IsScalarTower (MvPolynomial (Fin n) k)
  (MvPolynomial (Fin n) k ⧸ I) C]
variable [IsScalarTower (MvPolynomial (Fin n) k)
  (MvPolynomial (Fin n) k ⧸ I) L]
variable [IsScalarTower (MvPolynomial (Fin n) k) C L]
variable [IsScalarTower (MvPolynomial (Fin n) k ⧸ I) C L]
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra.FormallyEtale (MvPolynomial (Fin r) k) C]

/-- Finite-index compatibility specialization of the canonical arbitrary-parameter theorem. -/
theorem projectiveTangentCone_eq_span_chartDerivation_columns
    (q : Fin (n + 1) → C) (h0 : algebraMap C L (q 0) ≠ 0)
    (hfactor : ∀ i, q i.succ = q 0 *
      algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i))) :
    projectiveTangentCone (fun i => algebraMap C L (q i))
      (zariskiTangentSpace (dehomogenizedPoint (fun i => algebraMap C L (q i)))
        (I.map (MvPolynomial.map (algebraMap k L)))) =
      Submodule.span L (Set.range fun j : Option (Fin r) => fun i =>
        match j with
        | none => algebraMap C L (q i)
        | some j => coordinateDerivation
            (k := k) (σ := Fin r) (B := C) (L := L) j (q i)) := by
  convert FiniteParameters.projectiveTangentCone_eq_span_chartDerivation_columns
    (σ := Fin r) q h0 hfactor using 1
  congr 2
  funext j i
  cases j <;> rfl

end
end Stafford38.Geometry.EtaleProjectiveTangentComparison
