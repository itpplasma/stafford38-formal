import Stafford38.Geometry.PaperDivisorTangent
import Stafford38.Geometry.CorrectedVelocitySpan

namespace Stafford38.Geometry.CorrectedNormalizedTangentLattice

open Stafford38.GeometryFormalDivisorTangent

noncomputable section

set_option autoImplicit false

variable {k : Type*} [Field k]

/-- After extending to Laurent series, replacing the normalized transverse
column by the raw derivative preserves the span with the position and
selected divisor-tangent columns. The correction identity is first mapped
from power series, and the nonzero power of `X` is used as a Laurent scalar. -/
theorem mapped_formalTangentColumns_span_eq_of_corrected_derivative
    {n : ℕ} {κ : Type*} [Fintype κ]
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (lambda : κ → PowerSeries k) (c : ℕ)
    (hfactor : ∀ i,
      PowerSeries.derivative k (q i) - Z.mulVec lambda i =
        (PowerSeries.X : PowerSeries k) ^ c * tau i) :
    Submodule.span (LaurentSeries k)
        (Set.range (fun j : FormalTangentColumn κ =>
          fun i => algebraMap (PowerSeries k) (LaurentSeries k)
            (formalTangentMatrix q Z tau i j))) =
      Submodule.span (LaurentSeries k)
        (Set.range (fun j : FormalTangentColumn κ =>
          fun i => algebraMap (PowerSeries k) (LaurentSeries k)
            (formalTangentMatrix q Z (fun i => PowerSeries.derivative k (q i)) i j))) := by
  classical
  let A := algebraMap (PowerSeries k) (LaurentSeries k)
  let fixed : Option κ → (Fin (n + 1) → LaurentSeries k) := fun a =>
    match a with
    | none => fun i => A (q i)
    | some j => fun i => A (Z i j)
  let coeff : Option κ → LaurentSeries k := fun a =>
    match a with
    | none => 0
    | some j => A (lambda j)
  let corrected : Fin (n + 1) → LaurentSeries k := fun i => A (tau i)
  let raw : Fin (n + 1) → LaurentSeries k :=
    fun i => A (PowerSeries.derivative k (q i))
  have hx : A (PowerSeries.X : PowerSeries k) ≠ 0 := by
    simpa [A] using
      (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).ne
        (PowerSeries.X_ne_zero (R := k))
  have hc : A ((PowerSeries.X : PowerSeries k) ^ c) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero c hx
  have hfactorL : raw - (∑ a, coeff a • fixed a) =
      A ((PowerSeries.X : PowerSeries k) ^ c) • corrected := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    change A (PowerSeries.derivative k (q i)) -
        (∑ a, coeff a * fixed a i) =
      A ((PowerSeries.X : PowerSeries k) ^ c) * A (tau i)
    have hi := congrArg A (hfactor i)
    simpa [coeff, fixed, Matrix.mulVec, dotProduct, map_sum, map_mul,
      mul_comm] using hi
  have hspan :=
    Stafford38.Geometry.CorrectedVelocitySpan.span_map_range_union_singleton_eq_of_corrected_velocity
      (LinearMap.id) fixed coeff corrected raw
      (A ((PowerSeries.X : PowerSeries k) ^ c)) hc hfactorL
  have hcolsTau :
      Set.range (fun j : FormalTangentColumn κ =>
        fun i => A (formalTangentMatrix q Z tau i j)) =
        Set.range fixed ∪ {corrected} := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | inl u => exact Or.inl ⟨none, rfl⟩
      | inr j =>
        cases j with
        | inl j => exact Or.inl ⟨some j, rfl⟩
        | inr u => exact Or.inr (Set.mem_singleton _)
    · intro hv
      rcases hv with ⟨a, ha⟩ | hv
      · rcases a with _ | j
        · exact ⟨Sum.inl (), ha⟩
        · exact ⟨Sum.inr (Sum.inl j), ha⟩
      · rcases Set.mem_singleton_iff.mp hv with rfl
        exact ⟨Sum.inr (Sum.inr ()), rfl⟩
  have hcolsRaw :
      Set.range (fun j : FormalTangentColumn κ =>
        fun i => A (formalTangentMatrix q Z
          (fun i => PowerSeries.derivative k (q i)) i j)) =
        Set.range fixed ∪ {raw} := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | inl u => exact Or.inl ⟨none, rfl⟩
      | inr j =>
        cases j with
        | inl j => exact Or.inl ⟨some j, rfl⟩
        | inr u => exact Or.inr (Set.mem_singleton _)
    · intro hv
      rcases hv with ⟨a, ha⟩ | hv
      · rcases a with _ | j
        · exact ⟨Sum.inl (), ha⟩
        · exact ⟨Sum.inr (Sum.inl j), ha⟩
      · rcases Set.mem_singleton_iff.mp hv with rfl
        exact ⟨Sum.inr (Sum.inr ()), rfl⟩
  rw [hcolsTau, hcolsRaw]
  exact hspan

/-- The corrected transverse generator and raw derivative give the same
Laurent generic fibre: this composes the column-span replacement with the
canonical generic-fibre/column dictionary. -/
theorem genericFibre_normalizedTangentLattice_eq_span_derivative
    {n : ℕ} {κ : Type*} [Fintype κ]
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (lambda : κ → PowerSeries k) (c : ℕ)
    (hfactor : ∀ i,
      PowerSeries.derivative k (q i) - Z.mulVec lambda i =
        (PowerSeries.X : PowerSeries k) ^ c * tau i) :
    Stafford38.Geometry.GeneralTangentLimitCriterion.genericFibre
        (K := LaurentSeries k)
        (Stafford38.Geometry.PaperDivisorTangent.normalizedTangentLattice q Z tau) =
      Submodule.span (LaurentSeries k)
        (Set.range (fun j : FormalTangentColumn κ =>
          fun i => algebraMap (PowerSeries k) (LaurentSeries k)
            (formalTangentMatrix q Z
              (fun i => PowerSeries.derivative k (q i)) i j))) := by
  let B := formalTangentMatrix q Z tau
  have hsourceSpan :
      Submodule.span (PowerSeries k)
          (Set.range (fun j : FormalTangentColumn κ => fun i => B i j)) =
        Stafford38.Geometry.PaperDivisorTangent.normalizedTangentLattice q Z tau := by
    change Submodule.span (PowerSeries k)
        (Set.range (fun j : FormalTangentColumn κ => fun i => B i j)) =
      LinearMap.range B.mulVecLin
    exact (Matrix.range_mulVecLin B).symm
  have hgeneric :=
    Stafford38.Geometry.GeneralTangentLimitCriterion.genericFibre_eq_span_matrixColumns
      (K := LaurentSeries k)
      (L := Stafford38.Geometry.PaperDivisorTangent.normalizedTangentLattice q Z tau)
      B hsourceSpan
  rw [hgeneric]
  exact mapped_formalTangentColumns_span_eq_of_corrected_derivative
    q Z tau lambda c hfactor


end

end Stafford38.Geometry.CorrectedNormalizedTangentLattice
