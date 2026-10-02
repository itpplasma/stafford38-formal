import Stafford38.Geometry.ActualWitnessConormalAssembly
import Stafford38.Geometry.PaperSameWitnessTangentDimension
import Stafford38.Geometry.PaperRetainedChartAssembly
import Stafford38.Geometry.PaperRetainedChartWitnessColumns
import Stafford38.Geometry.PaperActualDivisorTangent
import Stafford38.Geometry.RetainedPlaceConormalTransport

/-!
# Actual-witness regularized conormal data

This production adapter discharges the conditional one-row matrix theorem
from one retained divisor witness.  It derives the chart columns, order gap,
generic-point equations, and tangent bound before constructing the data.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace Stafford38.Geometry.PaperActualWitnessConormalData

open IsLocalRing
open Stafford38.Geometry.ActualWitnessConormalAssembly
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveOrder
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.PaperActualDivisorTangent
open Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof
open Stafford38.Geometry.KaehlerVisibleDerivationFrame
open Stafford38.Geometry.PaperRetainedChartAssembly
open Stafford38.Geometry.PaperRetainedChartWitnessColumns
open Stafford38.Geometry.PaperSameWitnessTangentDimension
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.GeometrySplitTangentMatrix

noncomputable section
universe u

set_option maxHeartbeats 12000000
/-- Assemble the actual retained witness into the conditional matrix theorem.
The tangent bound, point kernel, base equations, derivative columns, and strict
order gap are all derived from this same witness. -/
theorem exists_regularizedOneRowConormalData_of_actual_witness
    {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsRadical)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hP : P.asIdeal ∈ I.minimalPrimes)
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal) :
    let C := w.column
    let W := C.W
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    Nonempty (RegularizedOneRowConormalData (k := k) (K := κ) hm I
      (fun a ↦ retainedToCompletedPowerSeries W (C.q a))) := by
  classical
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
  let E := LaurentSeries κ
  letI : Algebra k E := (groundLaurentMap (k := k) (K := κ)).toAlgebra
  let i : Fin m := ⟨0, hm⟩
  let q : Fin (m + 1) → PowerSeries κ :=
    fun a ↦ retainedToCompletedPowerSeries W (C.q a)
  let ell := retainedLaurentLift P i W
  let y : Fin m → E := dehomogenizedPoint (laurentColumn q)
  obtain ⟨rows, D, _hdual, hminorCoeff⟩ :=
    columns_of_visible_witness hm P w
  let Z := coefficientwiseTangentMatrix q D
  have hZ : Z = coefficientwiseTangentMatrix q D := rfl
  have hqchart : q C.chart = 1 := by
    dsimp [q]
    rw [C.chart_one]
    exact map_one (retainedToCompletedPowerSeries W)
  obtain ⟨a, b, u₀, u₁, ha, hab, hqzero, hu₀, hqaxis⟩ :=
    order_gap_of_actual_witness hm P w hunit
  have hminor : PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0 := by
    change PowerSeries.constantCoeff
      (selectedMinor (coefficientwiseTangentMatrix q D) rows).det ≠ 0
    rw [hminorCoeff]
    norm_num
  have hground := retainedLaurentLift_comp_algebraMap P i W
  have hpoint := retainedLaurentLift_componentCoordinate P i W C.q C.scale
    C.q_commonScale C.q0_ne
  have hychart : y = dehomogenizedPoint (laurentColumn q) := rfl
  have hbaseP : ∀ f ∈ P.asIdeal,
      MvPolynomial.eval₂ (algebraMap k E)
        (dehomogenizedPoint (laurentColumn q)) f = 0 := by
    intro f hf
    have hvanish := component_equations_vanish_after_point_transport
      P ell hground y hpoint (f := f) hf
    simpa [y] using hvanish
  have hkernel := component_generic_kernel_after_point_transport
    P ell (RingHom.injective ell) hground y hpoint
  have hy : ∀ f,
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q))
        (MvPolynomial.map (algebraMap k E) f) = 0 ↔ f ∈ P.asIdeal := by
    intro f
    rw [← hychart]
    exact hkernel f
  have hbound : Module.finrank E
      (zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (P.asIdeal.map (MvPolynomial.map (algebraMap k E)))) ≤
      Module.finrank κ (Ω[κ⁄k]) + 1 := by
    change tangent_finrank_goal hm P w
    exact tangent_finrank_le_residue_add_one_of_witness hm P w
  exact exists_regularizedOneRowConormalData_of_actual_columns
    hm I hI P hP q Z rows C.chart a b u₀ u₁ D hZ hqchart ha hab
    hqzero hu₀ hqaxis hminor hbaseP hbound hy

set_option maxHeartbeats 4000000

end

end Stafford38.Geometry.PaperActualWitnessConormalData
