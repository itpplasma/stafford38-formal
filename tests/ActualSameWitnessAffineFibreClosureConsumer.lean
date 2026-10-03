module
public import Stafford38.Geometry.SameWitness.AffineFibreClosure
public import Stafford38.Geometry.GenericSmoothOpen

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness.AffineFibreClosureConsumer

open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.SameWitness

universe u

/-- A retained visible-frame witness gives the literal affine-conormal closure
conclusion without assuming the ground-point output or smooth-open input. -/
theorem axis_in_original_affine_conormal_fibre_closure
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : Stafford38.Geometry.GeneralDivisorialVisibleFrame.GeneralDivisorialVisibleFrameWitness
      hm P) :
    (fun i : Fin m => if i = (⟨0, hm⟩ : Fin m) then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection
            P.asIdeal)) := by
  exact Stafford38.Geometry.SameWitness.axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput
    hm P w
    (Stafford38.Geometry.ActualSameWitnessGroundPointCompletion.exists_actual_same_witness_groundpoint_chart
      hm P w)
    (Stafford38.Geometry.exists_nonzero_smooth_away_quotient P.asIdeal)

#print axioms axis_in_original_affine_conormal_fibre_closure
#print axioms Stafford38.Geometry.SameWitness.axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput

end Stafford38.Geometry.SameWitness.AffineFibreClosureConsumer
end
