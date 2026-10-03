module
public import Stafford38.Geometry.SameWitness.AffineFibreClosure
public import Stafford38.Geometry.OriginalPrimeCoordinateAvoidanceWitness
public import Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
public import Stafford38.Geometry.GenericSmoothOpen

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.ProjectiveConormalDirections

universe u

/-- The original-prime coordinate axis lies in the smooth conormal fibre closure
by splitting into the direct algebraic case and the retained-witness route. -/
theorem coordinate_axis_mem_smooth_fibre_closure
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal)) := by
  rcases Stafford38.Geometry.OriginalPrimeCoordinateAvoidanceWitness.coordinate_axis_or_visible_frame_of_avoidance
      hm I havoid with h | ⟨w⟩
  · exact h
  · exact axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput hm I w
      (Stafford38.Geometry.ActualSameWitnessGroundPointCompletion.exists_actual_same_witness_groundpoint_chart hm I w)
      (Stafford38.Geometry.exists_nonzero_smooth_away_quotient I.asIdeal)

end Stafford38.Geometry.SameWitness
end
