module
public import Stafford38.Geometry.SameWitness.AffineFibreClosure
public import Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
public import Stafford38.Geometry.GenericSmoothOpen

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.SameWitness.AffineFibreClosureConsumer

universe u

/-- An external consumer states the affine-conormal conclusion without
assuming a smooth chart or any column, derivative, numerator, or closure
identity. It obtains the ground-point output from the retained witness. -/
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
