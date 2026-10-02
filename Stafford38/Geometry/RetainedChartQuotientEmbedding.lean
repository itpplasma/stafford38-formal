import Stafford38.Geometry.ComponentProjectiveChartKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000

namespace Stafford38.Geometry.RetainedChartQuotientEmbedding

open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.RelativeCoefficientDVR

universe u

variable {k : Type u} [Field k] {m : ℕ}

/-- Evaluating the retained normalized chart map and then including its values
in the component function field gives exactly the generic chart-ratio map. -/
theorem componentChartEquationQuotientMap_mk_comp_genericEval
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
    ∀ a : MvPolynomial (Fin m) k,
      ι (componentChartEquationQuotientMap P coeff ι hι hcoeff q chart e
        hqchart scale hq (Ideal.Quotient.mk (componentChartEquationIdeal P chart e) a)) =
        MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
          (chartGenericPoint P chart e) a := by
  let qaff : Fin m → V := fun i ↦ q (e i).1
  let evalV : MvPolynomial (Fin m) k →+* V := MvPolynomial.eval₂Hom coeff qaff
  let evalF : MvPolynomial (Fin m) k →+* ComponentFractionField P :=
    MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
      (chartGenericPoint P chart e)
  have hcoords : ∀ i, ι (qaff i) = chartGenericPoint P chart e i := by
    intro i
    simpa [qaff, chartGenericPoint] using
      chart_coordinates_agree_with_generic_point P ι q chart e hqchart scale hq i
  have heval : ∀ a, ι (evalV a) = evalF a := by
    intro a
    calc
      ι (evalV a) = (ι.comp evalV) a := rfl
      _ = (MvPolynomial.eval₂Hom (ι.comp coeff) (fun i ↦ ι (qaff i))) a := by
        rw [MvPolynomial.comp_eval₂Hom]
      _ = evalF a := by
        rw [hcoeff, funext hcoords]
  intro a
  calc
    ι (componentChartEquationQuotientMap P coeff ι hι hcoeff q chart e
        hqchart scale hq (Ideal.Quotient.mk (componentChartEquationIdeal P chart e) a)) =
        ι (evalV a) := rfl
    _ = evalF a := heval a

/-- The retained normalized chart map into a subring of the component function field
is injective: after inclusion into the function field it is the generic chart evaluation,
whose kernel is exactly the dehomogenized homogeneous component ideal. -/
theorem componentChartEquationQuotientMap_injective
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
    Function.Injective
      (componentChartEquationQuotientMap P coeff ι hι hcoeff q chart e
        hqchart scale hq) := by
  let I := componentChartEquationIdeal P chart e
  let qaff : Fin m → V := fun i ↦ q (e i).1
  let evalV : MvPolynomial (Fin m) k →+* V := MvPolynomial.eval₂Hom coeff qaff
  let evalF : MvPolynomial (Fin m) k →+* ComponentFractionField P :=
    MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
      (chartGenericPoint P chart e)
  let f : MvPolynomial (Fin m) k ⧸ I →+* V :=
    componentChartEquationQuotientMap P coeff ι hι hcoeff q chart e hqchart scale hq
  have hchart : componentProjectivePoint P chart ≠ 0 := by
    have hscale : scale * componentProjectivePoint P chart = 1 := by
      simpa [hqchart] using (hq chart).symm
    intro hz
    rw [hz, mul_zero] at hscale
    exact one_ne_zero hscale.symm
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hxyV : evalV a = evalV b := by
    have hma : f (Ideal.Quotient.mk I a) = evalV a := by
      rfl
    have hmb : f (Ideal.Quotient.mk I b) = evalV b := by
      rfl
    change f (Ideal.Quotient.mk I a) = f (Ideal.Quotient.mk I b) at hxy
    rw [hma, hmb] at hxy
    exact hxy
  have hxyF : evalF a = evalF b := by
    calc
      evalF a = ι (f (Ideal.Quotient.mk I a)) := by
        exact (componentChartEquationQuotientMap_mk_comp_genericEval
          P coeff ι hι hcoeff q chart e hqchart scale hq a).symm
      _ = ι (f (Ideal.Quotient.mk I b)) := congrArg ι hxy
      _ = evalF b :=
        componentChartEquationQuotientMap_mk_comp_genericEval
          P coeff ι hι hcoeff q chart e hqchart scale hq b
  have hdiff : evalF (a - b) = 0 := by
    rw [map_sub, hxyF, sub_self]
  have hmem : a - b ∈ I := by
    change a - b ∈ componentChartEquationIdeal P chart e
    rw [componentChartEquationIdeal_eq_genericEvalKer P chart e hchart]
    exact RingHom.mem_ker.mpr hdiff
  exact Ideal.Quotient.eq.mpr hmem

/-- The quotient map built from a retained Lane-C witness is injective for every
normalized projective coordinate column. -/
theorem retainedComponentChartEquationQuotientMap_injective
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Stafford38.Geometry.RelativeRetainedBoundaryPlace.Data k
      (ComponentFractionField P) (componentCoordinate P i))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    letI : IsDiscreteValuationRing W.place.valuation.toSubring := W.place.isDiscrete
    letI : Algebra W.coefficientField W.place.valuation.toSubring :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ (q : Fin (m + 1) → W.place.valuation.toSubring)
      (hqchart : q chart = 1) (scale : ComponentFractionField P)
      (hq : ∀ a, (q a : ComponentFractionField P) =
        scale * componentProjectivePoint P a),
      Function.Injective
        (retainedComponentChartEquationQuotientMap P i W chart e q
          hqchart scale hq) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : IsScalarTower W.coefficientField
      (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.coefficientTower
  intro q hqchart scale hq
  let coeff : k →+* V :=
    ComponentProjectiveClosureNormalization.retainedComponentCoefficientMap P i W
  have hcoeff : V.subtype.comp coeff =
      algebraMap k (ComponentFractionField P) := by
    ext c
    change ((relativeCoefficientMap
        W.coefficientField W.place (algebraMap k W.coefficientField c) : V) :
        ComponentFractionField P) = algebraMap k (ComponentFractionField P) c
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
  simpa [retainedComponentChartEquationQuotientMap] using
    (componentChartEquationQuotientMap_injective P coeff V.subtype
      Subtype.val_injective hcoeff q chart e hqchart scale hq)

#print axioms componentChartEquationQuotientMap_mk_comp_genericEval
#print axioms componentChartEquationQuotientMap_injective
#print axioms retainedComponentChartEquationQuotientMap_injective

end Stafford38.Geometry.RetainedChartQuotientEmbedding
