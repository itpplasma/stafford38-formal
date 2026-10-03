module
public import Stafford38.Geometry.GeneralAsymptoticLaurentAxis
public import Stafford38.Geometry.SmoothConormalFibreVanishing
public import Stafford38.Geometry.ConormalScalarExtensionVanishing

@[expose] public section

/-!
# Generic/Laurent proof of the coordinate-axis closure

This separately named result preserves the verified generic-prime and Laurent
residue argument. The main theorem remains in `GeneralAsymptoticConormal` and
uses the retained-witness route.
-/

namespace Stafford38.Geometry.AlternativeAsymptoticConormal

open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.GeneralAsymptoticLaurentAxis
open Stafford38.Geometry.SmoothConormalFibreVanishing
open Stafford38.Geometry.ConormalScalarExtensionVanishing
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

/-- The historical generic-prime/Laurent proof, retained as a separately
named route for the unchanged Stafford challenge. -/
theorem coordinate_axis_mem_smooth_fibre_closure
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal)) := by
  obtain ⟨K, hK, hAlg, y, xi, hgeneric, hres⟩ :=
    exists_groundConormalAxis_of_prime_coordinate_avoidance hm I havoid
  letI := hK
  letI := hAlg
  intro P hP
  have hfull := fibreLift_mem_vanishingIdeal_equationConormal I.asIdeal I.isPrime P hP
  have hvan : ∀ q ∈ groundEquationConormalLocus (k := k) (K := K) I.asIdeal,
      MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) q (fibreLift P) = 0 := by
    letI : Algebra k (LaurentSeries K) :=
      (groundLaurentMap (k := k) (K := K)).toAlgebra
    intro q hq
    exact scalarExtension_vanishing I.asIdeal (fibreLift P) hfull q hq
  have hpoly := residueFibreLift_mem_extensionValuedVanishingIdeal_of_ground_vanishing
    I.asIdeal P hvan
  have hclosure := residue_mem_residueExtensionFibreClosure_of_laurent_generic
    (K := K) (groundEquationConormalLocus (k := k) (K := K) I.asIdeal) y xi hgeneric
  have hzero := hclosure _ hpoly
  have hzero' : MvPolynomial.eval₂ (algebraMap k K) (residueColumn xi) P = 0 := by
    simpa [residuePolynomialMap, scalarPolynomialMap] using hzero
  rw [hres] at hzero'
  apply (FaithfulSMul.algebraMap_injective k K)
  rw [map_zero]
  change (algebraMap k K) (MvPolynomial.eval
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) P) = 0
  rw [MvPolynomial.eval₂_comp]
  simpa [Function.comp_def] using hzero'

#print axioms coordinate_axis_mem_smooth_fibre_closure

end
end Stafford38.Geometry.AlternativeAsymptoticConormal
