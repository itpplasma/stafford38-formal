import Stafford38.Geometry.IntegralClosureCenterDVR
import Mathlib.RingTheory.LocalRing.LocalSubring

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.LocalNormalizationCenterEquivalence

universe u

variable {K : Type u} [Field K]

private def subringEquivOfEq {A B : Subring K} (h : A = B) : A ≃+* B :=
  h ▸ RingEquiv.refl A

private theorem subringEquivOfEq_coe {A B : Subring K} (h : A = B) (x : A) :
    ((subringEquivOfEq h x : B) : K) = (x : K) := by
  cases h
  rfl

/-- If a height-one center on an integral closure has already been established,
the canonical localization at that center is the original valuation subring.
The final field identity records that this is the localization's canonical map,
not a field automorphism. -/
theorem exists_localization_equiv_of_height_one
    (R : Subring K) (V : ValuationSubring K) (hRV : R ≤ V.toSubring)
    [hNoeth : IsNoetherianRing (integralClosure R K).toSubring]
    [hIntegrallyClosed : IsIntegrallyClosed (integralClosure R K).toSubring]
    [hFractionRing : IsFractionRing (integralClosure R K).toSubring K]
    (hp : (Stafford38.Geometry.ProjectiveChartNormalizationCenter.integralClosureCenter
      R V hRV).IsPrime)
    (hh : (Stafford38.Geometry.ProjectiveChartNormalizationCenter.integralClosureCenter
      R V hRV).height = 1) :
    let B : Subring K := (integralClosure R K).toSubring
    let p : Ideal B := Stafford38.Geometry.ProjectiveChartNormalizationCenter.integralClosureCenter
      R V hRV
    ∃ e : Localization.AtPrime p ≃+* V.toSubring,
      ∀ b : B,
        ((e (algebraMap B (Localization.AtPrime p) b) : V.toSubring) : K) = (b : K) := by
  dsimp only
  let B : Subring K := (integralClosure R K).toSubring
  let p : Ideal B := Stafford38.Geometry.ProjectiveChartNormalizationCenter.integralClosureCenter
    R V hRV
  letI : p.IsPrime := hp
  have hlocal : (LocalSubring.ofPrime B p).toSubring = V.toSubring :=
    @Stafford38.Geometry.IntegralClosureCenterDVR.localNormalizationCenter_eq_valuationSubring
      K inferInstance R V hRV hNoeth hIntegrallyClosed hFractionRing hp hh
  let e0 : Localization.AtPrime p ≃ₐ[B] (LocalSubring.ofPrime B p).toSubring :=
    LocalSubring.ofPrimeEquiv B p
  let e : Localization.AtPrime p ≃+* V.toSubring :=
    e0.toRingEquiv.trans (subringEquivOfEq hlocal)
  refine ⟨e, ?_⟩
  intro b
  change ((subringEquivOfEq hlocal
      (e0 (algebraMap B (Localization.AtPrime p) b)) : V.toSubring) : K) = (b : K)
  rw [subringEquivOfEq_coe]
  change ((e0 (algebraMap B (Localization.AtPrime p) b) : (LocalSubring.ofPrime B p).toSubring) : K) =
    (b : K)
  rw [e0.commutes]
  rfl

#print axioms exists_localization_equiv_of_height_one

end Stafford38.Geometry.LocalNormalizationCenterEquivalence
