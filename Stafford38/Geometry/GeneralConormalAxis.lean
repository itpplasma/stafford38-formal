module
public import Stafford38.Geometry.GeneralDivisorialVisibleFrame
public import Stafford38.Geometry.FiniteGradientResidueExtension
public import Stafford38.Geometry.PaperActualWitnessConormalData
public import Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof
public import Stafford38.Geometry.RetainedPlaceConormalTransport
public import Stafford38.Geometry.RetainedProjectiveCompletion

@[expose] public section

/-!
# Laurent conormal axes for arbitrary affine components

The prime-component visible frame passes through the generic finite-gradient
adapter to a Laurent equation-conormal point with the prescribed residue.
This is an algebraic witness; the comparison with smooth projective conormal
directions is a separate statement.


## References and proof context

[HTT08] Ryoshi Hotta, Kiyoshi Takeuchi, and Toshiyuki Tanisaki, *D-Modules, Perverse Sheaves, and Representation Theory*, Progress in Mathematics 236, Birkhäuser, 2008.
https://doi.org/10.1007/978-0-8176-4523-6

Chapters 1–2 supply characteristic-variety context. The visible-frame and finite-gradient construction is project mathematics, not a cited theorem from this book. See docs/literature.md.
-/

namespace Stafford38.Geometry.GeneralConormalAxis

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ExactVisibleDivisorFrameInterface
open Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction
open Stafford38.Geometry.FiniteGradientResidueExtension
open Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof
open Stafford38.Geometry.PaperActualWitnessConormalData
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
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
  classical
  obtain ⟨w⟩ :=
    generalDivisorialVisibleFrameWithResidueAlgebraicity hm P hunit htrans
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  letI : CharZero κ :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k κ)
  let q : Fin (m + 1) → PowerSeries κ :=
    fun a ↦ retainedToCompletedPowerSeries W (C.q a)
  obtain ⟨data⟩ :=
    exists_regularizedOneRowConormalData_of_actual_witness
      hm I hI P hP w hunit
  obtain ⟨certificate⟩ :=
    finiteGradientBoundaryCertificateOver_of_regularizedOneRowConormalData
      (k := k) (K := κ) hm I q data
  obtain ⟨y, xi, hmem, hres⟩ :=
    exists_groundConormalAxis_of_finiteGradientBoundaryCertificateOver
      (k := k) (K := κ) hm I certificate
  exact ⟨κ, inferInstance, inferInstance, y, xi, hmem, hres⟩

#print axioms exists_groundConormalAxis_of_minimalPrime_unit_transcendental

end
end Stafford38.Geometry.GeneralConormalAxis
