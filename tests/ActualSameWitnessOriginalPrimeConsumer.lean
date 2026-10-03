module
public import Stafford38.Geometry.SameWitness.OriginalPrimeAxis
public import Stafford38.Geometry.GeneralAsymptoticConormal

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38IndependentOriginalPrimeConsumer

universe u

-- The literal affine endpoint has only the original prime and coordinate-
-- avoidance hypotheses. No ground-point, completion, smooth-open, tangent-
-- column, or closure certificate is an input to this consumer.
theorem original_prime_coordinate_avoidance_affine_endpoint
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k P.asIdeal,
      y (⟨0, hm⟩ : Fin m) ≠ 0) :
    (fun i : Fin m => if i = (⟨0, hm⟩ : Fin m) then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection
            P.asIdeal)) := by
  exact Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure
    hm P havoid

-- This is the printed projective-direction conclusion over the original
-- algebraically closed field; no residue-field extension remains in it.
theorem original_prime_coordinate_avoidance_projective_endpoint
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k P.asIdeal,
      y (⟨0, hm⟩ : Fin m) ≠ 0) :
    Projectivization.mk k
        (fun i : Fin m => if i = (⟨0, hm⟩ : Fin m) then (1 : k) else 0)
        (by
          intro h
          have hzero := congrFun h (⟨0, hm⟩ : Fin m)
          simpa using hzero) ∈
      Stafford38.Geometry.ProjectiveConormalDirections.projectiveHomogeneousClosure
        (Stafford38.Geometry.ProjectiveConormalDirections.projectivizedDirectionSet
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalDirectionSet
            P.asIdeal)) := by
  exact Stafford38.Geometry.GeneralAsymptoticConormal.coordinate_axis_mem_projective_conormal_directions
    hm P havoid

#print axioms original_prime_coordinate_avoidance_affine_endpoint
#print axioms Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure
#print axioms original_prime_coordinate_avoidance_projective_endpoint

end Stafford38IndependentOriginalPrimeConsumer
