import Stafford38.Geometry.ActualSameWitnessAffineFibreClosure
import Stafford38.Geometry.GeneralConstantCoordinateAxis
import Stafford38.Geometry.GeneralCoordinateAvoidance
import Stafford38.Geometry.GenericSmoothOpen

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

namespace Stafford38.Geometry.ActualSameWitnessAsymptoticConormal

open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
open Stafford38.Geometry.ActualSameWitnessAffineFibreClosure
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.GeneralConstantCoordinateAxis
open Stafford38.Geometry.GeneralCoordinateAvoidance
open Stafford38.Geometry.ProjectiveConormalDirections

universe u

/-- The normalized-divisor and closed-point route for an invertible
transcendental coordinate. Every geometric endpoint input is supplied by
the same retained witness and its ground-point completion output. -/
theorem coordinate_axis_mem_smooth_fibre_closure_of_prime_unit_transcendental
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal)
    (htrans : Transcendental k (componentCoordinate P ⟨0, hm⟩)) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection P.asIdeal)) := by
  obtain ⟨w⟩ :=
    generalDivisorialVisibleFrameWithResidueAlgebraicity hm P hunit htrans
  have hpoint := exists_actual_same_witness_groundpoint_chart hm P w
  letI : P.asIdeal.IsPrime := P.isPrime
  exact axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput
    hm P w hpoint (exists_nonzero_smooth_away_quotient P.asIdeal)

/-- Original-prime coordinate avoidance feeds the printed geometric route.
The algebraic-coordinate branch contributes the axis directly; otherwise
one normalized divisor, one ground point, and one tilt supply the endpoint. -/
theorem coordinate_axis_mem_smooth_fibre_closure_of_prime_coordinate_avoidance
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k P.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection P.asIdeal)) := by
  by_cases halg : IsAlgebraic k (componentCoordinate P ⟨0, hm⟩)
  · exact coordinate_axis_mem_smooth_fibre_closure_of_coordinate_algebraic hm P halg
  · exact coordinate_axis_mem_smooth_fibre_closure_of_prime_unit_transcendental hm P
      (exists_coordinate_inverse_of_avoidance P.asIdeal ⟨0, hm⟩ havoid) halg

end Stafford38.Geometry.ActualSameWitnessAsymptoticConormal
