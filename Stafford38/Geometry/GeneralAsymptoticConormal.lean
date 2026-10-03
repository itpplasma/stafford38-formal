module
public import Stafford38.Geometry.GeneralAsymptoticLaurentAxis
public import Stafford38.Geometry.SmoothConormalFibreVanishing
public import Stafford38.Geometry.ConormalScalarExtensionVanishing
public import Stafford38.Geometry.SameWitness.OriginalPrimeAxis

@[expose] public section

/-!
# Asymptotic conormal directions of coordinate-avoiding varieties

The boundary witness specializes only in the fibre coordinates. Its base
coordinates may have poles. Smooth-locus density and scalar-extension
vanishing relate that witness to the ground-field projective direction set.
-/

namespace Stafford38.Geometry.GeneralAsymptoticConormal

open Stafford38.Geometry.GeneralAsymptoticLaurentAxis
open Stafford38.Geometry.SmoothConormalFibreVanishing
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.ConormalScalarExtensionVanishing
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization

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
  exact Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure hm I havoid

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
