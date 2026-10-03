module
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

/-!
An elementary span identity used when a raw velocity differs from a corrected
velocity by a linear combination of transverse columns and a nonzero scalar.
This file is intentionally independent of the projective and tangent-cone
constructions.
-/

namespace Stafford38.Geometry.CorrectedVelocitySpan

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}
variable [Field K] [AddCommGroup V] [Module K V]

/-- Replacing one vector by a nonzero scalar multiple of itself plus a linear
combination of a fixed finite family does not change the span with that family.
The convention in `h` is `raw - Σ λᵢ zᵢ = c • corrected`. -/
theorem span_range_union_singleton_eq_of_corrected_velocity
    {ι : Type*} [Fintype ι]
    (z : ι → V) (coeff : ι → K) (corrected raw : V) (c : K)
    (hc : c ≠ 0)
    (h : raw - (∑ i, coeff i • z i) = c • corrected) :
    Submodule.span K (Set.range z ∪ {corrected}) =
      Submodule.span K (Set.range z ∪ {raw}) := by
  let S₀ : Submodule K V := Submodule.span K (Set.range z ∪ {corrected})
  let S₁ : Submodule K V := Submodule.span K (Set.range z ∪ {raw})
  have hcorrected_mem₀ : corrected ∈ S₀ :=
    Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _))
  have hsum : (∑ i, coeff i • z i) ∈ S₀ := by
    apply S₀.sum_smul_mem coeff
    intro i hi
    exact Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)
  have hraw_mem : raw ∈ S₁ :=
    Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _))
  have hsum₁ : (∑ i, coeff i • z i) ∈ S₁ := by
    apply S₁.sum_smul_mem coeff
    intro i hi
    exact Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)
  have hcorrected_mem : corrected ∈ S₁ := by
    have hsub : raw - (∑ i, coeff i • z i) ∈ S₁ :=
      S₁.sub_mem hraw_mem hsum₁
    have hscaled : c • corrected ∈ S₁ := by rwa [← h]
    have hinv : c⁻¹ • (c • corrected) ∈ S₁ := S₁.smul_mem c⁻¹ hscaled
    have hc' : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
    simpa [smul_smul, hc'] using hinv
  have hraw_from_corrected : raw ∈ S₀ := by
    have hscaled : c • corrected ∈ S₀ := S₀.smul_mem c hcorrected_mem₀
    have hrepr : raw = (∑ i, coeff i • z i) + c • corrected := by
      calc
        raw = (raw - (∑ i, coeff i • z i)) + (∑ i, coeff i • z i) :=
          (sub_add_cancel _ _).symm
        _ = c • corrected + (∑ i, coeff i • z i) := by rw [h]
        _ = (∑ i, coeff i • z i) + c • corrected := add_comm _ _
    rw [hrepr]
    exact S₀.add_mem hsum hscaled
  have h01 : S₀ ≤ S₁ := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨i, rfl⟩
      exact Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact hcorrected_mem
  have h10 : S₁ ≤ S₀ := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨i, rfl⟩
      exact Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact hraw_from_corrected
  exact le_antisymm h01 h10

/-- The same replacement identity after applying a linear observation map.
This form is convenient for tangent coordinates, where the vectors are first
dehomogenized by a fixed linear map. -/
theorem span_map_range_union_singleton_eq_of_corrected_velocity
    [AddCommGroup W] [Module K W]
    (φ : V →ₗ[K] W) {ι : Type*} [Fintype ι]
    (z : ι → V) (coeff : ι → K) (corrected raw : V) (c : K)
    (hc : c ≠ 0)
    (h : raw - (∑ i, coeff i • z i) = c • corrected) :
    Submodule.span K (Set.range (fun i => φ (z i)) ∪ {φ corrected}) =
      Submodule.span K (Set.range (fun i => φ (z i)) ∪ {φ raw}) := by
  have hφ : φ raw - (∑ i, coeff i • φ (z i)) = c • φ corrected := by
    calc
      φ raw - (∑ i, coeff i • φ (z i)) =
          φ (raw - (∑ i, coeff i • z i)) := by
        simp only [map_sub, map_sum, map_smul]
      _ = c • φ corrected := by rw [h, map_smul]
  exact span_range_union_singleton_eq_of_corrected_velocity
    (fun i => φ (z i)) coeff (φ corrected) (φ raw) c hc hφ

end Stafford38.Geometry.CorrectedVelocitySpan
