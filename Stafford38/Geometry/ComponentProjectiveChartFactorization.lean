import Stafford38.Geometry.ComponentProjectiveClosureNormalization
import Stafford38.Geometry.ProjectiveChartCoordinates

set_option autoImplicit false

/-! Affine-chart ring factorization for the homogeneous component equations.
The quotient coordinate map retains the selected projective coordinates
and their common scaling in the function field. -/

namespace Stafford38.Geometry.ComponentProjectiveChartFactorization

open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.ProjectiveChartCoordinates

noncomputable section

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000

universe u

variable {k : Type u} [Field k] {m : ℕ}

/-- Indices for all homogeneous equations of the generic projective component. -/
abbrev ProjectiveEquationIndex
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :=
  {H : MvPolynomial (Fin (m + 1)) k //
    ∃ d, H.IsHomogeneous d ∧ H ∈ componentProjectiveClosureIdeal P}

/-- The selected affine-chart equation family, using the shared chart
dehomogenization owner. -/
def componentChartEquations
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (_chart : Fin (m + 1)) :
    ProjectiveEquationIndex P → MvPolynomial (Fin (m + 1)) k :=
  fun H ↦ H.1

/-- The chart ideal is the shared dehomogenized equation ideal of the
homogeneous component ideal. -/
def componentChartEquationIdeal
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart) :
    Ideal (MvPolynomial (Fin m) k) :=
  dehomogenizedEquationIdeal chart e (componentChartEquations P chart)

/-- Dehomogenized homogeneous component equations vanish under every
normalized common-scale lift into an injective coefficient subring. -/
theorem eval₂_ker_contains_componentChartEquationIdeal
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {V : Type u} [CommRing V]
    (coeff : k →+* V)
    (ι : V →+* ComponentFractionField P)
    (hι : Function.Injective ι)
    (hcoeff : ι.comp coeff = algebraMap k (ComponentFractionField P))
    (q : Fin (m + 1) → V) (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hqchart : q chart = 1)
    (scale : ComponentFractionField P)
    (hq : ∀ a, ι (q a) = scale * componentProjectivePoint P a) :
    componentChartEquationIdeal P chart e ≤
      RingHom.ker (MvPolynomial.eval₂Hom coeff
        (fun i ↦ q (e i).1)) := by
  change Ideal.span (Set.range fun H : ProjectiveEquationIndex P ↦
      dehomogenizeProjectiveChart chart e H.1) ≤
    RingHom.ker (MvPolynomial.eval₂Hom coeff (fun i ↦ q (e i).1))
  apply Ideal.span_le.mpr
  rintro _ ⟨H, rfl⟩
  obtain ⟨d, hhomogeneous, hH⟩ := H.2
  change MvPolynomial.eval₂Hom coeff (fun i ↦ q (e i).1)
      (dehomogenizeProjectiveChart chart e H.1) = 0
  have hprojective :=
    eval₂_eq_zero_of_commonScale_componentProjectivePoint
      P coeff ι hι hcoeff hhomogeneous hH q scale hq
  have hdehom :
      MvPolynomial.eval₂Hom coeff (fun i ↦ q (e i).1)
        (dehomogenizeProjectiveChart chart e H.1) =
        MvPolynomial.eval₂Hom coeff q H.1 := by
    change ((MvPolynomial.eval₂Hom coeff (fun i ↦ q (e i).1)).comp
        (MvPolynomial.eval₂Hom MvPolynomial.C
          (fun a ↦ if h : a = chart then 1
            else MvPolynomial.X (e.symm ⟨a, h⟩)))) H.1 = _
    rw [MvPolynomial.comp_eval₂Hom]
    have hC :
        (MvPolynomial.eval₂Hom coeff (fun i ↦ q (e i).1)).comp
            MvPolynomial.C = coeff :=
      MvPolynomial.eval₂Hom_comp_C coeff (fun i ↦ q (e i).1)
    rw [hC]
    have hvars :
        (fun a ↦ MvPolynomial.eval₂Hom coeff (fun i ↦ q (e i).1)
          (if h : a = chart then 1 else MvPolynomial.X (e.symm ⟨a, h⟩))) = q := by
      funext a
      by_cases h : a = chart
      · subst a
        simp [hqchart]
      · simp only [h, ↓reduceDIte, MvPolynomial.eval₂Hom_X']
        have he : e (e.symm ⟨a, h⟩) = ⟨a, h⟩ := Equiv.apply_symm_apply e ⟨a, h⟩
        exact congrArg (fun z : ChartAffineIndex (Fin (m + 1)) chart ↦
          q z.1) he
    rw [hvars]
  rw [hdehom]
  exact hprojective

/-- The normalized projective coordinate column induces a genuine ring map
from the affine chart equation quotient to its valuation ring. -/
def componentChartEquationQuotientMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {V : Type u} [CommRing V]
    (coeff : k →+* V)
    (ι : V →+* ComponentFractionField P)
    (hι : Function.Injective ι)
    (hcoeff : ι.comp coeff = algebraMap k (ComponentFractionField P))
    (q : Fin (m + 1) → V) (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hqchart : q chart = 1)
    (scale : ComponentFractionField P)
    (hq : ∀ a, ι (q a) = scale * componentProjectivePoint P a) :
    MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e →+* V :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom coeff
    (fun i ↦ q (e i).1))
    (eval₂_ker_contains_componentChartEquationIdeal
      P coeff ι hι hcoeff q chart e hqchart scale hq)

/-- The retained Lane-C DVR witness supplies the coefficient map, injective
valuation-ring inclusion, and scalar compatibility needed by the chart
factorization. -/
def retainedComponentChartEquationQuotientMap
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Stafford38.Geometry.RelativeRetainedBoundaryPlace.Data k
      (ComponentFractionField P) (componentCoordinate P i))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart) :
    letI : Algebra (CoordinateZeroLocalRing
        W.coefficientField) (ComponentFractionField P) := W.ambientAlgebra
    letI : IsDiscreteValuationRing W.place.valuation.toSubring :=
      W.place.isDiscrete
    letI : Algebra W.coefficientField W.place.valuation.toSubring :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ (q : Fin (m + 1) → W.place.valuation.toSubring)
      (hqchart : q chart = 1)
      (scale : ComponentFractionField P)
      (hq : ∀ a, (q a : ComponentFractionField P) =
        scale * componentProjectivePoint P a),
      MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e →+*
        W.place.valuation.toSubring := by
  letI : Algebra (CoordinateZeroLocalRing
      W.coefficientField) (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : IsScalarTower W.coefficientField
      (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.coefficientTower
  intro q hqchart scale hq
  let coeff : k →+* V := retainedComponentCoefficientMap P i W
  have hcoeff : V.subtype.comp coeff =
      algebraMap k (ComponentFractionField P) := by
    ext c
    change ((relativeCoefficientMap
        W.coefficientField W.place (algebraMap k W.coefficientField c) : V) :
        ComponentFractionField P) =
      algebraMap k (ComponentFractionField P) c
    calc
      ((relativeCoefficientMap
          W.coefficientField W.place (algebraMap k W.coefficientField c) : V) :
          ComponentFractionField P) =
          algebraMap W.coefficientField (ComponentFractionField P)
            (algebraMap k W.coefficientField c) :=
        DFunLike.congr_fun
          (relativeCoefficientMap_commutes W.coefficientField W.place)
          (algebraMap k W.coefficientField c)
      _ = algebraMap k (ComponentFractionField P) c :=
        IsScalarTower.algebraMap_apply k W.coefficientField
          (ComponentFractionField P) c
  exact componentChartEquationQuotientMap
    (P := P) (V := V) (coeff := coeff) (ι := V.subtype)
    (hι := Subtype.val_injective) (hcoeff := hcoeff)
    (q := q) (chart := chart) (e := e)
    (hqchart := hqchart) (scale := scale) (hq := hq)

/-- On the generic point, the chart coordinates supplied by the valuation
ring are exactly the ratios of the original projective component point. -/
theorem chart_coordinates_agree_with_generic_point
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {V : Type u} [CommRing V]
    (ι : V →+* ComponentFractionField P)
    (q : Fin (m + 1) → V) (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hqchart : q chart = 1)
    (scale : ComponentFractionField P)
    (hq : ∀ a, ι (q a) = scale * componentProjectivePoint P a) :
    ∀ i, ι (q (e i).1) =
      componentProjectivePoint P (e i).1 /
        componentProjectivePoint P chart := by
  intro i
  have hscale : scale * componentProjectivePoint P chart = 1 := by
    simpa [hqchart] using (hq chart).symm
  have hchart : componentProjectivePoint P chart ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hscale
    exact one_ne_zero hscale.symm
  rw [hq]
  calc
    scale * componentProjectivePoint P (e i).1 =
        (scale * componentProjectivePoint P chart) *
          (componentProjectivePoint P (e i).1 /
            componentProjectivePoint P chart) := by
      field_simp [hchart]
    _ = componentProjectivePoint P (e i).1 /
        componentProjectivePoint P chart := by
      rw [hscale, one_mul]

end

end Stafford38.Geometry.ComponentProjectiveChartFactorization

#print axioms Stafford38.Geometry.ComponentProjectiveChartFactorization.eval₂_ker_contains_componentChartEquationIdeal
#print axioms Stafford38.Geometry.ComponentProjectiveChartFactorization.componentChartEquationQuotientMap
#print axioms Stafford38.Geometry.ComponentProjectiveChartFactorization.retainedComponentChartEquationQuotientMap
#print axioms Stafford38.Geometry.ComponentProjectiveChartFactorization.chart_coordinates_agree_with_generic_point
