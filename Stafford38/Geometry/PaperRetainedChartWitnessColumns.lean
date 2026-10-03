module
public import Stafford38.Geometry.GeneralDivisorialVisibleFrame
public import Stafford38.Geometry.PaperRetainedChartAssembly
public import Stafford38.Geometry.FormalDivisorLaurentConormal
public import Stafford38.Geometry.ComponentProjectiveClosureNormalization

@[expose] public section

/-!
# Coefficient columns from the actual retained divisorial witness

This adapter specializes the retained chart-column result to the same `W`,
normalized `q`, and residue algebraicity carried by the Lane-C witness.
-/

namespace Stafford38.Geometry.PaperRetainedChartWitnessColumns

open IsLocalRing
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.PaperRetainedChartAssembly
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.RetainedDVR
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.GeometryResidueMinorSelection
open Stafford38.GeometrySplitTangentMatrix
open Stafford38.Geometry.KaehlerVisibleDerivationFrame
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ComponentProjectiveClosureNormalization

universe u

variable {k : Type u} [Field k] [CharZero k] {m : ℕ}

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

/-- The witness's own normalized projective column and residue algebraicity
yield the actual completed coefficientwise derivation columns. -/
theorem columns_of_visible_witness
    (hm : 0 < m) (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
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
    ∃ (rows : Fin (Module.finrank κ (Ω[κ⁄k])) ↪ Fin (m + 1))
      (D : Fin (Module.finrank κ (Ω[κ⁄k])) → Derivation k κ κ),
      (∀ i j, D j (PowerSeries.constantCoeff
        (retainedToCompletedPowerSeries W (C.q (rows i)))) =
          if i = j then 1 else 0) ∧
      PowerSeries.constantCoeff
        (selectedMinor
          (coefficientwiseTangentMatrix
            (fun a ↦ retainedToCompletedPowerSeries W (C.q a)) D) rows).det = 1 := by
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
  dsimp only
  exact exists_retained_projective_derivation_columns P ⟨0, hm⟩
    W C.q w.halg


end Stafford38.Geometry.PaperRetainedChartWitnessColumns
