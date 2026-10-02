import Stafford38.Geometry.ActualCenterParameterTransport
import Stafford38.Geometry.ActualDivisorUniformizerNumerator
import Mathlib.RingTheory.LocalRing.RingHom.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualSameWitnessDivisorNumerator

open IsLocalRing

universe u v

/-- Transport an already identified local normalization across the canonical
subalgebra/subring carrier equivalence, then extract its one numerator and
transport both retained order factorizations. -/
theorem exists_numerator_across_carrier_equiv
    {K : Type u} [Field K]
    {B : Type v} [CommRing B] [IsDomain B]
    {S : Type v} [CommRing S]
    {V : Type v} [CommRing V]
    (coB : B →+* K) (coS : S →+* K) (coV : V →+* K)
    (eB : B ≃+* S) (P : Ideal S) [P.IsPrime]
    (PB : Ideal B) (hPB : PB = P.comap eB.toRingHom) [PB.IsPrime]
    (eC : Localization.AtPrime P ≃+* V)
    (heC : ∀ c : S,
      coV (eC (algebraMap S (Localization.AtPrime P) c)) = coS c)
    (heB : ∀ b : B, coS (eB b) = coB b)
    [IsDomain V] [hDVR : IsDiscreteValuationRing V]
    (π : V) (hπ : Irreducible π)
    (q₀ q₁ : B) (n₀ n₁ : ℕ) (v₀ v₁ : V)
    (h₀ : eC (algebraMap S (Localization.AtPrime P) (eB q₀)) = π ^ n₀ * v₀)
    (h₁ : eC (algebraMap S (Localization.AtPrime P) (eB q₁)) = π ^ n₁ * v₁)
    (hv₀ : IsUnit v₀) (hv₁ : IsUnit v₁) :
    ∃ (e : Localization.AtPrime PB ≃+* V) (s : B)
      (den : PB.primeCompl) (u₀ u₁ : Localization.AtPrime PB),
      (∀ b : B, coV (e (algebraMap B _ b)) = coB b) ∧
      s ≠ 0 ∧ s ∈ PB ∧
      IsLocalization.mk' _ s den = e.symm π ∧
      Ideal.span {algebraMap B (Localization.AtPrime PB) s} =
        maximalIdeal (Localization.AtPrime PB) ∧
      IsUnit u₀ ∧ IsUnit u₁ ∧
      algebraMap B _ q₀ = (algebraMap B _ s) ^ n₀ * u₀ ∧
      algebraMap B _ q₁ = (algebraMap B _ s) ^ n₁ * u₁ := by
  classical
  let eLoc := ActualCenterParameterTransport.atPrimeEquiv eB PB P hPB
  let e : Localization.AtPrime PB ≃+* V := eLoc.trans eC
  have heLocalF : ∀ b : B, coV (e (algebraMap B _ b)) = coB b := by
    intro b
    change coV (eC (eLoc (algebraMap B _ b))) = coB b
    have hmap := ActualCenterParameterTransport.atPrimeEquiv_algebraMap
      eB PB P hPB b
    have hmap' : eLoc (algebraMap B _ b) = algebraMap S _ (eB b) := by
      simpa [eLoc] using hmap
    rw [hmap']
    exact (heC (eB b)).trans (heB b)
  have hmap₀ : eLoc (algebraMap B _ q₀) = algebraMap S _ (eB q₀) := by
    simpa [eLoc] using
      ActualCenterParameterTransport.atPrimeEquiv_algebraMap eB PB P hPB q₀
  have hmap₁ : eLoc (algebraMap B _ q₁) = algebraMap S _ (eB q₁) := by
    simpa [eLoc] using
      ActualCenterParameterTransport.atPrimeEquiv_algebraMap eB PB P hPB q₁
  have hq₀ : e (algebraMap B _ q₀) = π ^ n₀ * v₀ := by
    change eC (eLoc (algebraMap B _ q₀)) = _
    rw [hmap₀]
    exact h₀
  have hq₁ : e (algebraMap B _ q₁) = π ^ n₁ * v₁ := by
    change eC (eLoc (algebraMap B _ q₁)) = _
    rw [hmap₁]
    exact h₁
  letI : IsPrincipalIdealRing (Localization.AtPrime PB) :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
  letI : IsLocalRing (Localization.AtPrime PB) :=
    IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  letI : IsDiscreteValuationRing (Localization.AtPrime PB) := by
    refine IsDiscreteValuationRing.mk ?_
    intro hbot
    have hmax := IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective
    have hVbot : maximalIdeal V = ⊥ := by
      rw [← hmax, hbot, Ideal.map_bot]
    exact IsDiscreteValuationRing.not_a_field V hVbot
  obtain ⟨s, den, u₀, u₁, hs0, hsP, hmk, hspan, hu₀, hu₁, hfactor₀, hfactor₁⟩ :=
    Stafford38.Geometry.ActualDivisorUniformizerNumerator.exists_numerator_with_two_unit_power_factorizations_and_span
      PB e π hπ q₀ q₁ n₀ n₁ v₀ v₁ hq₀ hq₁ hv₀ hv₁
  exact ⟨e, s, den, u₀, u₁, heLocalF, hs0, hsP, hmk, hspan,
    hu₀, hu₁, hfactor₀, hfactor₁⟩

end Stafford38.Geometry.ActualSameWitnessDivisorNumerator
