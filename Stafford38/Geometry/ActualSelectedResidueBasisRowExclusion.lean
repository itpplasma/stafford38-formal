import Stafford38.Geometry.ActualSelectedResidueBasis
import Stafford38.Geometry.GeneralDivisorialVisibleFrameResidueSupport

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualSelectedResidueBasisRowExclusion

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RetainedGroundMapIdentification

universe u

/-- A residue transcendence basis cannot contain zero: injective multivariate
evaluation sends its variable to the selected element. -/
theorem transcendenceBasis_value_ne_zero
    {k κ : Type u} [Field k] [Field κ] [Algebra k κ]
    {t : Set κ}
    (ht : IsTranscendenceBasis k ((↑) : t → κ)) (z : t) :
    (z : κ) ≠ 0 := by
  intro hz
  have hinj : Function.Injective
      (MvPolynomial.aeval (fun i : t => (i : κ)) : MvPolynomial t k →ₐ[k] κ) :=
    (algebraicIndependent_iff_injective_aeval).mp ht.1
  have hX : (MvPolynomial.X z : MvPolynomial t k) ≠ 0 :=
    MvPolynomial.X_ne_zero z
  apply hX
  apply hinj
  simp [hz]

/-- If the row-zero and row-one coordinates both have zero residue, rows
representing a residue transcendence basis avoid both. The chart row is
excluded by the complement subtype itself. -/
theorem selected_basis_rows_avoid_zero_one_chart
    {k κ : Type u} [Field k] [Field κ] [Algebra k κ]
    {m : ℕ} (hm : 0 < m) (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (value : Fin (m + 1) → κ) (t : Set κ)
    (ht : IsTranscendenceBasis k ((↑) : t → κ))
    (index : t → Fin m)
    (hrep : ∀ z : t, value ((e (index z)).1) = (z : κ))
    (hzero : value 0 = 0)
    (hone : value (Fin.succ ⟨0, hm⟩) = 0) :
    ∀ z : t,
      (e (index z)).1 ≠ 0 ∧
      (e (index z)).1 ≠ Fin.succ ⟨0, hm⟩ ∧
      (e (index z)).1 ≠ chart := by
  intro z
  have hz0 : (z : κ) ≠ 0 := transcendenceBasis_value_ne_zero ht z
  refine ⟨?_, ?_, (e (index z)).2⟩
  · intro hrow
    apply hz0
    calc
      (z : κ) = value ((e (index z)).1) := (hrep z).symm
      _ = value 0 := congrArg value hrow
      _ = 0 := hzero
  · intro hrow
    apply hz0
    calc
      (z : κ) = value ((e (index z)).1) := (hrep z).symm
      _ = value (Fin.succ ⟨0, hm⟩) := congrArg value hrow
      _ = 0 := hone

/-- The actual retained witness also makes the first two homogeneous
coordinates vanish in the same residue field. The second vanishing follows
from the stored relation `q₁ = q₀ * parameter`; it does not identify `q₀` with
the parameter. -/
theorem witness_q1_residue_eq_zero
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
        (ComponentFractionField P) := w.column.W.ambientAlgebra
    let V := w.column.W.place.valuation.toSubring
    letI : IsLocalRing V := w.column.W.place.isDiscrete.toIsLocalRing
    residue V (w.column.q (Fin.succ ⟨0, hm⟩)) = 0 := by
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  change residue V (C.q (Fin.succ ⟨0, hm⟩)) = 0
  apply (IsLocalRing.residue_eq_zero_iff _).2
  have hq0 : C.q 0 ∈ maximalIdeal V :=
    GeneralDivisorialVisibleFrame.witness_q0_mem_maximal hm P w
  rw [C.q_parameter]
  exact Ideal.mul_mem_right _ _ hq0


end Stafford38.Geometry.ActualSelectedResidueBasisRowExclusion
