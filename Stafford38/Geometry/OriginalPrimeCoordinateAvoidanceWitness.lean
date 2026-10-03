module
public import Stafford38.Geometry.GeneralCoordinateAvoidance
public import Stafford38.Geometry.GeneralDivisorialVisibleFrame
public import Stafford38.Geometry.GeneralConstantCoordinateAxis

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Stafford38.Geometry.OriginalPrimeCoordinateAvoidanceWitness

open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.GeneralCoordinateAvoidance
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.GeneralConstantCoordinateAxis

noncomputable section

universe u

/-- On the transcendental-coordinate branch, the original geometric
avoidance hypothesis supplies exactly the polynomial inverse required by
the retained visible-frame producer. The witness is produced from that same
inverse and the same original prime. -/
theorem exists_inverse_and_visible_frame_of_coordinate_avoidance
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k P.asIdeal,
      y ⟨0, hm⟩ ≠ 0)
    (htrans : Transcendental k (componentCoordinate P ⟨0, hm⟩)) :
    ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal ∧
      Nonempty (GeneralDivisorialVisibleFrameWitness hm P) := by
  obtain ⟨g, hg⟩ :=
    exists_coordinate_inverse_of_avoidance P.asIdeal ⟨0, hm⟩ havoid
  exact ⟨g, hg,
      generalDivisorialVisibleFrameWithResidueAlgebraicity hm P ⟨g, hg⟩ htrans⟩

/-- Separate the direct constant-coordinate case from the transcendental
retained-witness case using only the original prime and zero-locus avoidance.
This is the pre-endpoint split consumed by the same-witness affine-fibre
producer. -/
theorem coordinate_axis_or_visible_frame_of_avoidance
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k P.asIdeal,
      y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection
            P.asIdeal)) ∨
      Nonempty (GeneralDivisorialVisibleFrameWitness hm P) := by
  by_cases halg : IsAlgebraic k (componentCoordinate P ⟨0, hm⟩)
  · exact Or.inl
      (coordinate_axis_mem_smooth_fibre_closure_of_coordinate_algebraic
        hm P halg)
  · have htrans : Transcendental k (componentCoordinate P ⟨0, hm⟩) := halg
    obtain ⟨g, hg, hw⟩ :=
      exists_inverse_and_visible_frame_of_coordinate_avoidance
        hm P havoid htrans
    exact Or.inr hw

#print axioms exists_inverse_and_visible_frame_of_coordinate_avoidance
#print axioms coordinate_axis_or_visible_frame_of_avoidance

end
end Stafford38.Geometry.OriginalPrimeCoordinateAvoidanceWitness
