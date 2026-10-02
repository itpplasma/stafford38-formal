import Stafford38.Geometry.PaperResidueDerivationFrame

/-!
# Completed columns from residue coordinates

This small interface separates the coefficientwise Kähler frame construction
from the retained divisor record.  A retained chart consumer supplies only a
completed column, its identified residue coordinates, and algebraicity.
-/

namespace Stafford38.Geometry.PaperCompletedResidueDerivationFrame

open Stafford38.GeometryResidueMinorSelection
open Stafford38.GeometrySplitTangentMatrix
open Stafford38.Geometry.KaehlerVisibleDerivationFrame
open Stafford38.Geometry.PaperResidueDerivationFrame

universe u v

variable {k κ : Type u} [Field k] [Field κ] [Algebra k κ] [CharZero k]

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

/-- A residue frame selected on the affine tail of a projective column embeds
into the full homogeneous row index without changing its minor. -/
theorem tail_residue_frame_embeds_projective_rows
    {m d : ℕ}
    (q : Fin (m + 1) → PowerSeries κ)
    (D : Fin d → Derivation k κ κ)
    (rows : Fin d ↪ Fin m)
    (hdual : ∀ i j,
      D j (PowerSeries.constantCoeff (q (Fin.succ (rows i)))) =
        if i = j then 1 else 0)
    (hminor : PowerSeries.constantCoeff
      (selectedMinor
        (coefficientwiseTangentMatrix
          (fun j : Fin m ↦ q (Fin.succ j)) D) rows).det = 1) :
    ∃ rowsFull : Fin d ↪ Fin (m + 1),
      (∀ i j, D j (PowerSeries.constantCoeff (q (rowsFull i))) =
        if i = j then 1 else 0) ∧
      PowerSeries.constantCoeff
        (selectedMinor (coefficientwiseTangentMatrix q D) rowsFull).det = 1 := by
  let rowsFull : Fin d ↪ Fin (m + 1) :=
    ⟨fun i ↦ Fin.succ (rows i), fun i j hij ↦
      rows.injective (Fin.succ_injective m hij)⟩
  refine ⟨rowsFull, ?_, ?_⟩
  · intro i j
    change D j (PowerSeries.constantCoeff (q (Fin.succ (rows i)))) = _
    exact hdual i j
  · have hmatrix :
        selectedMinor (coefficientwiseTangentMatrix q D) rowsFull =
          selectedMinor
            (coefficientwiseTangentMatrix
              (fun j : Fin m ↦ q (Fin.succ j)) D) rows := by
      ext i j
      rfl
    rw [hmatrix]
    exact hminor

/-- An abstract completed column with identified residue coordinates admits
an actual dual derivation frame and a unit selected coefficientwise minor. -/
theorem exists_completed_derivation_frame_of_residue_coordinates
    {ι : Type v} [Fintype ι]
    (q : ι → PowerSeries κ) (qbar : ι → κ)
    (hcoeff : ∀ i, PowerSeries.constantCoeff (q i) = qbar i)
    (halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range qbar) : IntermediateField k κ)
      κ) :
    ∃ (rows : Fin (Module.finrank κ (Ω[κ⁄k])) ↪ ι)
      (D : Fin (Module.finrank κ (Ω[κ⁄k])) → Derivation k κ κ),
      (∀ i j, D j (qbar (rows i)) = if i = j then 1 else 0) ∧
      PowerSeries.constantCoeff
        (selectedMinor (coefficientwiseTangentMatrix q D) rows).det = 1 := by
  have hrange : Set.range (fun i => PowerSeries.constantCoeff (q i)) =
      Set.range qbar := by
    congr 1
    funext i
    exact hcoeff i
  have hgenerated : Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun i => PowerSeries.constantCoeff (q i)) :
          IntermediateField k κ) κ := by
    rw [hrange]
    exact halg
  obtain ⟨rows, D, hdual, hminor⟩ :=
    exists_coefficientwise_residue_minor_eq_one (k := k) (κ := κ) q hgenerated
  refine ⟨rows, D, ?_, hminor⟩
  intro i j
  rw [← hcoeff (rows i)]
  exact hdual i j

/-- Residue coordinates on the affine tail construct derivation columns and a
unit selected minor on the full homogeneous completed projective column. -/
theorem exists_projective_derivation_frame_of_residue_coordinates
    {m : ℕ}
    (q : Fin (m + 1) → PowerSeries κ) (qbar : Fin m → κ)
    (hcoeff : ∀ j, PowerSeries.constantCoeff (q (Fin.succ j)) = qbar j)
    (halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range qbar) : IntermediateField k κ)
      κ) :
    ∃ (rows : Fin (Module.finrank κ (Ω[κ⁄k])) ↪ Fin (m + 1))
      (D : Fin (Module.finrank κ (Ω[κ⁄k])) → Derivation k κ κ),
      (∀ i j, D j (PowerSeries.constantCoeff (q (rows i))) =
        if i = j then 1 else 0) ∧
      PowerSeries.constantCoeff
        (selectedMinor (coefficientwiseTangentMatrix q D) rows).det = 1 := by
  let qtail : Fin m → PowerSeries κ := fun j ↦ q (Fin.succ j)
  obtain ⟨rows, D, hdual, hminor⟩ :=
    exists_completed_derivation_frame_of_residue_coordinates
      qtail qbar hcoeff halg
  have hdualTail : ∀ i j,
      D j (PowerSeries.constantCoeff (qtail (rows i))) =
        if i = j then 1 else 0 := by
    intro i j
    rw [hcoeff (rows i)]
    exact hdual i j
  obtain ⟨rowsFull, hdualFull, hminorFull⟩ :=
    tail_residue_frame_embeds_projective_rows q D rows hdualTail
      (by simpa [qtail] using hminor)
  exact ⟨rowsFull, D, hdualFull, hminorFull⟩

end Stafford38.Geometry.PaperCompletedResidueDerivationFrame
