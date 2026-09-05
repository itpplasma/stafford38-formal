import Stafford38.Geometry.GeneralDivisorialVisibleFrame
import Stafford38.Geometry.FiniteGradientResidueExtension

/-!
# Laurent conormal axes for arbitrary affine components

The prime-component visible frame passes through the generic finite-gradient
adapter to a Laurent equation-conormal point with the prescribed residue.
This is an algebraic witness; the comparison with smooth projective conormal
directions is a separate statement.
-/

namespace Stafford38.Geometry.GeneralConormalAxis

open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ExactVisibleDivisorFrameInterface
open Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction
open Stafford38.Geometry.FiniteGradientResidueExtension
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

theorem exists_groundConormalAxis_of_minimalPrime_unit_transcendental
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsRadical)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hP : P.asIdeal ∈ I.minimalPrimes)
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal)
    (htrans : Transcendental k (componentCoordinate P ⟨0, hm⟩)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (y : Fin m → LaurentSeries K) (xi : Fin m → PowerSeries K),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K) I ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  have hframe := hasVisibleDivisorFrame_of_normalizedCompatibleVisibleFrame P hm
    (generalDivisorialVisibleFrameExistence hm P hunit htrans)
  obtain ⟨K, hK, hAlg, ⟨W⟩⟩ :=
    exists_finiteGradientBoundaryCertificateOver_of_hasVisibleDivisorFrame
      I hI P hP hm hframe
  letI := hK
  letI := hAlg
  obtain ⟨y, xi, hmem, hres⟩ :=
    exists_groundConormalAxis_of_finiteGradientBoundaryCertificateOver hm I W
  exact ⟨K, hK, hAlg, y, xi, hmem, hres⟩

#print axioms exists_groundConormalAxis_of_minimalPrime_unit_transcendental

end
end Stafford38.Geometry.GeneralConormalAxis
