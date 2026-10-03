import Stafford38.Geometry.ActualSameWitnessAsymptoticConormal

/-!
# Asymptotic conormal directions of coordinate-avoiding varieties

The nonconstant branch uses one normalized divisor, one closed ground point,
and its canonical completion. One tilt and the actual derivative columns
produce the smooth affine conormal fibre closure, then its projective direction.
-/

namespace Stafford38.Geometry.GeneralAsymptoticConormal

open Stafford38.Geometry.ActualSameWitnessAsymptoticConormal
open Stafford38.Geometry.ProjectiveConormalDirections

noncomputable section

universe u

theorem coordinate_axis_mem_smooth_fibre_closure
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal)) := by
  exact coordinate_axis_mem_smooth_fibre_closure_of_prime_coordinate_avoidance hm I havoid

theorem coordinate_axis_mem_projective_conormal_directions
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    Projectivization.mk k
        (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0)
        (by intro h; have := congrFun h ⟨0, hm⟩; simpa using this) ∈
      projectiveHomogeneousClosure
        (projectivizedDirectionSet (smoothConormalDirectionSet I.asIdeal)) := by
  exact mk_mem_projectiveHomogeneousClosure_of_fibre_zeroLocus I.asIdeal _ _
    (coordinate_axis_mem_smooth_fibre_closure hm I havoid)

#print axioms coordinate_axis_mem_smooth_fibre_closure
#print axioms coordinate_axis_mem_projective_conormal_directions

end
end Stafford38.Geometry.GeneralAsymptoticConormal
