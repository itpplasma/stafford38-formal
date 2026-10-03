module
public import Stafford38.Geometry.FormalDivisorAxisLift
public import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.SelectedCorrectionConsumer

open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometrySplitTangentMatrix
open Stafford38.GeometryFormalDivisorAxisLift
open Stafford38.GeometryResidueMinorSelection

noncomputable section

private abbrev S := PowerSeries ℚ
private def q : Fin 4 → S := ![PowerSeries.X ^ 2, PowerSeries.X ^ 3,
  PowerSeries.C 1 + PowerSeries.C 2 * PowerSeries.X, 1]
private def Z : Matrix (Fin 4) (Fin 1) S := ![![0], ![0], ![1], ![0]]
private def rows : Fin 1 ↪ Fin 4 :=
  ⟨fun _ => 2, fun _ _ _ => Subsingleton.elim _ _⟩
private def lambda : Fin 1 → S := fun _ => PowerSeries.C 2

/-- Literal tilted coordinates with a nonzero constant correction. The
normalized column still has the expected leading entries 2X and 3X², kills
the selected row, and vanishes on the axis after reduction. -/
theorem constant_correction_preserves_explicit_orders :
    ∃ (c : ℕ) (tau : Fin 4 → S), c ≤ 1 ∧
      PowerSeries.X ^ c * tau 0 = 2 * PowerSeries.X ∧
      PowerSeries.X ^ c * tau 1 = 3 * PowerSeries.X ^ 2 ∧
      tau 2 = 0 ∧ PowerSeries.constantCoeff (tau 1) = 0 ∧
      ∃ i, PowerSeries.constantCoeff (tau i) ≠ 0 := by
  have hselected : ∀ j, PowerSeries.derivative ℚ (q (rows j)) =
      Z.mulVec lambda (rows j) := by
    intro j
    change PowerSeries.derivative ℚ (q 2) = Z.mulVec lambda 2
    simp [q, Z, lambda, Matrix.mulVec, dotProduct]
  have hminor : PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0 := by
    have hmatrix : selectedMinor Z rows = 1 := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i
      subst j
      rfl
    rw [hmatrix, Matrix.det_one]
    simp
  obtain ⟨c, tau, C, ell, htauchart, htauselected, hc, hfactor, hprimitive,
      htauaxis, haxiscolumns, hCB, hell, hresidue⟩ :=
    exists_formalDivisorAxisLift_of_selected_correction q Z rows 3 0 1 2 3
      1 1 lambda (by simp [q]) (by intro j; simp [Z]) (by norm_num)
      (by norm_num) (by simp [q]) (by simp)
      (by intro j; exact ⟨0, by simp [Z]⟩) (by simp [q])
      (by intro j; exact ⟨0, by simp [Z]⟩) hselected hminor
  refine ⟨c, tau, ?_, ?_, ?_, ?_, htauaxis, hprimitive⟩
  · simpa using hc
  · simpa [q, Z, lambda, Matrix.mulVec, dotProduct] using (hfactor 0).symm
  · simpa [q, Z, lambda, Matrix.mulVec, dotProduct] using (hfactor 1).symm
  · exact htauselected 0

#print axioms constant_correction_preserves_explicit_orders
#print axioms Stafford38.GeometryFormalDivisorTangent.exists_primitive_formalDivisorTangent_of_selected_correction
#print axioms Stafford38.GeometryFormalDivisorTangent.exists_formalDivisorTangent_residue_injective_of_selected_correction
#print axioms Stafford38.GeometryFormalDivisorAxisLift.exists_formalDivisorAxisLift_of_selected_correction

end
end Stafford38.Geometry.SelectedCorrectionConsumer
