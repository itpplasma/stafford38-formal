import Stafford38.Geometry.ProjectiveChartNormalizationCenter
import Stafford38.Geometry.NormalizationHeightOne
import Stafford38.Geometry.ProjectiveDVRCenter
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.DiscreteValuationRing.Basic

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.IntegralClosureCenterDVR

universe u

variable {K : Type u} [Field K]

local instance subringAlgebra (A : Subring K) : Algebra A K := A.subtype.toAlgebra

/-- Passing from a domain to its integral closure in the same fraction-field
model does not change the fraction field. -/
theorem integralClosure_isFractionRing
    (R : Subring K)
    [IsFractionRing R K] :
    IsFractionRing (integralClosure R K).toSubring K := by
  let B := (integralClosure R K).toSubring
  have hRB : R ≤ B := by
    intro r hr
    change IsIntegral R (algebraMap R K ⟨r, hr⟩)
    exact isIntegral_algebraMap
  let f : R →+* B := Subring.inclusion hRB
  have hcomp : B.subtype.comp f = R.subtype := by
    ext r
    rfl
  letI : FaithfulSMul B K :=
    (faithfulSMul_iff_algebraMap_injective B K).mpr Subtype.val_injective
  apply IsFractionRing.of_field B K
  intro z
  obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective R z
  refine ⟨f a, f b, ?_⟩
  calc
    z = algebraMap R K a / algebraMap R K b := hz.symm
    _ = algebraMap B K (f a) / algebraMap B K (f b) := by
      change R.subtype a / R.subtype b = B.subtype (f a) / B.subtype (f b)
      simpa only [RingHom.comp_apply] using
        congrArg (fun g : R →+* K => g a / g b) hcomp.symm

/-- Once the center of a valuation ring on a noetherian normal affine
normalization has height one, its local ring is the same valuation ring.
This is the local-algebra endpoint only; the height-one premise is supplied
by the residue-basis localization argument. -/
theorem localNormalizationCenter_eq_valuationSubring
    (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring)
    [IsNoetherianRing (integralClosure R K).toSubring]
    [IsIntegrallyClosed (integralClosure R K).toSubring]
    [IsFractionRing (integralClosure R K).toSubring K]
    [hCenterPrime : (Stafford38.Geometry.ProjectiveChartNormalizationCenter.integralClosureCenter
      R V hRV).IsPrime]
    (hh : (Stafford38.Geometry.ProjectiveChartNormalizationCenter.integralClosureCenter
      R V hRV).height = 1) :
    (@LocalSubring.ofPrime K _ (integralClosure R K).toSubring
      (Stafford38.Geometry.ProjectiveChartNormalizationCenter.integralClosureCenter
        R V hRV) hCenterPrime).toSubring = V.toSubring := by
  let B : Subring K := (integralClosure R K).toSubring
  letI : IsNoetherianRing B := inferInstance
  letI : IsIntegrallyClosed B := inferInstance
  letI : IsFractionRing B K := inferInstance
  let p : Ideal B := Stafford38.Geometry.ProjectiveChartNormalizationCenter.integralClosureCenter
    R V hRV
  letI : p.IsPrime := hCenterPrime
  have hlocDVR : IsDiscreteValuationRing (Localization.AtPrime p) :=
    Stafford38.Geometry.NormalizationHeightOne.isDiscreteValuationRing_localization_of_height_eq_one
      p hh
  letI : IsDiscreteValuationRing (Localization.AtPrime p) := hlocDVR
  let hle : B ≤ (LocalSubring.ofPrime B p).toSubring :=
    LocalSubring.le_ofPrime B p
  letI : Algebra B (LocalSubring.ofPrime B p).toSubring :=
    (Subring.inclusion hle).toAlgebra
  let e := LocalSubring.ofPrimeEquiv B p
  letI : IsDiscreteValuationRing (LocalSubring.ofPrime B p).toSubring :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.toRingEquiv
  let S : Subring K := (@LocalSubring.ofPrime K _ B p hCenterPrime).toSubring
  letI : Algebra B S := (Subring.inclusion hle).toAlgebra
  letI : IsScalarTower B S K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsLocalization.AtPrime S p := inferInstance
  letI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl S K
  have hdom :=
    Stafford38.Geometry.ProjectiveChartNormalizationCenter.localRing_at_integralClosureCenter_le_valuationSubring
      R V hRV hCenterPrime
  have hfr : IsFractionRing S K := inferInstance
  exact @Stafford38.Geometry.ProjectiveDVRCenter.dvr_eq_of_dominated_by_valuationSubring
    K inferInstance S inferInstance hfr V hdom

#print axioms localNormalizationCenter_eq_valuationSubring
#print axioms integralClosure_isFractionRing

end Stafford38.Geometry.IntegralClosureCenterDVR
