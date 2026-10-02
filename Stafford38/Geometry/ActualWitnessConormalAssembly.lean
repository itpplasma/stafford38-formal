import Stafford38.Geometry.GeneralDivisorialVisibleFrame
import Stafford38.Geometry.PaperActualDivisorTangent
import Stafford38.Geometry.ComponentProjectiveOrder
import Stafford38.Geometry.ProjectiveDivisorOrderGap
import Stafford38.Geometry.CompletedDVRPowerSeriesEquiv

/-!
# Actual retained-witness order gap

The generic strict-DVR factorization is kept separate from witness-specific
extraction.  The specialization proves the strict denominator/axis order gap
in the chosen completed chart of the same retained divisor witness.
-/

namespace Stafford38.Geometry.ActualWitnessConormalAssembly

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveOrder
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ProjectiveDivisorOrderGap
open Stafford38.Geometry.PaperActualDivisorTangent
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.LaurentConormalResidueExtension

noncomputable section

universe u
variable {k : Type u} [Field k] [CharZero k] {m : ℕ}

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

/-- A strict DVR order gap remains strict in its chosen power-series
completion. The witness-specific dependent local algebra is kept out of this
generic step. -/
theorem completed_order_gap
    {R κ : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field κ]
    (ret : R →+* PowerSeries κ) (t : R)
    (ht : ret t = (PowerSeries.X : PowerSeries κ))
    (huniformizer : Irreducible t)
    (q₀ ratio q₁ : R) (hq₀_ne : q₀ ≠ 0) (hratio_ne : ratio ≠ 0)
    (hq₀_vanish : q₀ ∈ maximalIdeal R)
    (hratio_vanish : ratio ∈ maximalIdeal R)
    (hq₁ : q₁ = q₀ * ratio) :
    ∃ (a b : ℕ) (u₀ u₁ : PowerSeries κ),
      0 < a ∧ a < b ∧
      ret q₀ = (PowerSeries.X : PowerSeries κ) ^ a * u₀ ∧
      PowerSeries.constantCoeff u₀ ≠ 0 ∧
      ret q₁ = (PowerSeries.X : PowerSeries κ) ^ b * u₁ := by
  obtain ⟨a, _r, b, u₀v, _ur, u₁v, ha, _hr, _hb, hab,
      hq₀v, _hratio, _hu₁, hq₁v⟩ :=
    exists_uniformizer_strict_orderGap t huniformizer q₀ ratio q₁
      hq₀_ne hratio_ne hq₀_vanish hratio_vanish hq₁
  let u₀ : PowerSeries κ := ret (u₀v : R)
  let u₁ : PowerSeries κ := ret (u₁v : R)
  have hq₀series : ret q₀ = PowerSeries.X ^ a * u₀ := by
    calc
      ret q₀ = ret ((u₀v : R) * t ^ a) := congrArg ret hq₀v
      _ = ret (u₀v : R) * PowerSeries.X ^ a := by rw [map_mul, map_pow, ht]
      _ = PowerSeries.X ^ a * u₀ := by simp [u₀, mul_comm]
  have hu₀unit : IsUnit u₀ := by
    change IsUnit (ret (u₀v : R))
    exact u₀v.isUnit.map ret
  have hu₀coeff : PowerSeries.constantCoeff u₀ ≠ 0 :=
    (PowerSeries.isUnit_iff_constantCoeff.mp hu₀unit).ne_zero
  have hq₁series : ret q₁ = PowerSeries.X ^ b * u₁ := by
    calc
      ret q₁ = ret ((u₁v : R) * t ^ b) := congrArg ret hq₁v
      _ = ret (u₁v : R) * PowerSeries.X ^ b := by rw [map_mul, map_pow, ht]
      _ = PowerSeries.X ^ b * u₁ := by simp [u₁, mul_comm]
  exact ⟨a, b, u₀, u₁, ha, hab, hq₀series, hu₀coeff, hq₁series⟩

/-- The same normalized retained column has the strict denominator/axis
order gap in its completed chart. -/
theorem order_gap_of_actual_witness
    (hm : 0 < m) (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal) :
    letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
      (ComponentFractionField P) := w.column.W.ambientAlgebra
    letI : IsDiscreteValuationRing
      w.column.W.place.valuation.toSubring := w.column.W.place.isDiscrete
    ∃ (a b : ℕ)
      (u₀ u₁ : PowerSeries
        (ResidueField (w.column.W.place.valuation.toSubring))),
      0 < a ∧ a < b ∧
      retainedToCompletedPowerSeries w.column.W (w.column.q 0) =
        (PowerSeries.X : PowerSeries
          (ResidueField (w.column.W.place.valuation.toSubring))) ^ a * u₀ ∧
      PowerSeries.constantCoeff u₀ ≠ 0 ∧
      retainedToCompletedPowerSeries w.column.W
        (w.column.q (Fin.succ ⟨0, hm⟩)) =
        (PowerSeries.X : PowerSeries
          (ResidueField (w.column.W.place.valuation.toSubring))) ^ b * u₁ := by
  let i : Fin m := ⟨0, hm⟩
  let C := w.column
  let W := C.W
  let K := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P i W
  obtain ⟨g, hg⟩ := hunit
  let phi : MvPolynomial (Fin m) k →+* K :=
    (algebraMap (MvPolynomial (Fin m) k ⧸ P.asIdeal) K).comp
      (Ideal.Quotient.mk P.asIdeal)
  have hphiC : phi.comp MvPolynomial.C = algebraMap k K := by
    ext c
    exact IsScalarTower.algebraMap_apply k
      (MvPolynomial (Fin m) k ⧸ P.asIdeal) K c
  have hphiX : ∀ j, phi (MvPolynomial.X j) = componentCoordinate P j := by
    intro j
    rfl
  have hpoly : phi g = MvPolynomial.eval₂ (algebraMap k K)
      (fun j ↦ componentCoordinate P j) g := by
    rw [MvPolynomial.map_mvPolynomial_eq_eval₂ phi g]
    change MvPolynomial.eval₂Hom (phi.comp MvPolynomial.C)
        (fun j ↦ phi (MvPolynomial.X j)) g =
      MvPolynomial.eval₂Hom (algebraMap k K)
        (fun j ↦ componentCoordinate P j) g
    apply MvPolynomial.eval₂Hom_congr hphiC
    · funext j
      exact hphiX j
    · rfl
  have hinverse : componentCoordinate P i *
      MvPolynomial.eval₂ (algebraMap k K)
        (fun j ↦ componentCoordinate P j) g = 1 := by
    have hzero : phi (MvPolynomial.X i * g - 1) = 0 := by
      have hmk : Ideal.Quotient.mk P.asIdeal
          (MvPolynomial.X i * g - 1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hg
      simpa [phi] using (congrArg
        (algebraMap (MvPolynomial (Fin m) k ⧸ P.asIdeal) K) hmk)
    rw [map_sub, map_mul, map_one, sub_eq_zero, hphiX, hpoly] at hzero
    exact hzero
  have hq₀nonunit : ¬ IsUnit (C.q 0) :=
    normalized_denominator_nonunit_of_polynomial_inverse
      (V := W.place.valuation) (coeff := C.groundCoeff)
      C.groundCoeff_commutes
      (x := fun j ↦ componentCoordinate P j)
      (qzero := C.q 0) (q := fun j ↦ C.q (Fin.succ j))
      (scale := C.scale) (i := i) (parameter := W.place.parameter) (g := g)
      (by simpa [componentProjectivePoint] using C.q_commonScale 0)
      (by intro j; simpa [componentProjectivePoint] using
        C.q_commonScale (Fin.succ j))
      W.parameter_eq_coordinate W.place.parameter_nonunit hinverse
  have hq₀max : C.q 0 ∈ maximalIdeal V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hq₀nonunit
  have hparammax : W.place.parameter ∈ maximalIdeal V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact W.place.parameter_nonunit
  have hcompleted := completed_order_gap
    (retainedToCompletedPowerSeries W) (chosenUniformizer V)
    (retainedToCompletedPowerSeries_chosenUniformizer W)
    (chosenUniformizer_irreducible V)
    (C.q 0) W.place.parameter (C.q (Fin.succ i)) C.q0_ne
    W.place.parameter_ne hq₀max hparammax C.q_parameter
  simpa [C, W, i, V, κ] using hcompleted

end

end Stafford38.Geometry.ActualWitnessConormalAssembly
