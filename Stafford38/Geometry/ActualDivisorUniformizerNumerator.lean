import Stafford38.Geometry.DVRUniformizerNumerator

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.ActualDivisorUniformizerNumerator

open IsLocalRing

universe u

/-- Transport the numerator of a prescribed uniformizer across an actual
local-ring equivalence. The denominator remains explicit, so the numerator is
known to map to that uniformizer times a unit. -/
theorem exists_numerator_of_local_equiv_with_span
    {B V : Type u} [CommRing B] [IsDomain B] [CommRing V]
    (P : Ideal B) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)]
    (e : Localization.AtPrime P ≃+* V)
    (π : V) (hπ : Irreducible π) :
    ∃ a : B, ∃ b : P.primeCompl,
      a ≠ 0 ∧ a ∈ P ∧
      IsLocalization.mk' (Localization.AtPrime P) a b = e.symm π ∧
      Ideal.span {algebraMap B (Localization.AtPrime P) a} =
        maximalIdeal (Localization.AtPrime P) ∧
      IsUnit (e (algebraMap B (Localization.AtPrime P) (b : B))) ∧
      e (algebraMap B (Localization.AtPrime P) a) =
        π * e (algebraMap B (Localization.AtPrime P) (b : B)) := by
  let πP : Localization.AtPrime P := e.symm π
  have hπP : Irreducible πP := hπ.map e.symm
  obtain ⟨a, b, ha0, haP, hrep, hspan⟩ :=
    Stafford38.Geometry.DVRUniformizerNumerator.exists_numerator_of_dvr_localization_of_irreducible
      P πP hπP
  have hbunit : IsUnit (algebraMap B (Localization.AtPrime P) (b : B)) :=
    IsLocalization.map_units (Localization.AtPrime P) b
  have hmapa : algebraMap B (Localization.AtPrime P) a =
      πP * algebraMap B (Localization.AtPrime P) (b : B) := by
    calc
      algebraMap B (Localization.AtPrime P) a =
          IsLocalization.mk' (Localization.AtPrime P) a b *
            algebraMap B (Localization.AtPrime P) (b : B) :=
        (IsLocalization.mk'_spec (Localization.AtPrime P) a b).symm
      _ = πP * algebraMap B (Localization.AtPrime P) (b : B) := by rw [hrep]
  refine ⟨a, b, ha0, haP, hrep, hspan, ?_, ?_⟩
  · exact IsUnit.map e.toMonoidHom hbunit
  · calc
      e (algebraMap B (Localization.AtPrime P) a) =
          e (πP * algebraMap B (Localization.AtPrime P) (b : B)) :=
        congrArg e hmapa
      _ = π * e (algebraMap B (Localization.AtPrime P) (b : B)) := by
        simp [πP]

/-- Backwards-compatible projection of the local numerator data without its
maximal-ideal generator identity. -/
theorem exists_numerator_of_local_equiv
    {B V : Type u} [CommRing B] [IsDomain B] [CommRing V]
    (P : Ideal B) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)]
    (e : Localization.AtPrime P ≃+* V)
    (π : V) (hπ : Irreducible π) :
    ∃ a : B, ∃ b : P.primeCompl,
      a ≠ 0 ∧ a ∈ P ∧
      IsLocalization.mk' (Localization.AtPrime P) a b = e.symm π ∧
      IsUnit (e (algebraMap B (Localization.AtPrime P) (b : B))) ∧
      e (algebraMap B (Localization.AtPrime P) a) =
        π * e (algebraMap B (Localization.AtPrime P) (b : B)) := by
  obtain ⟨a, b, ha0, haP, hrep, _hspan, hden, hfactor⟩ :=
    exists_numerator_of_local_equiv_with_span P e π hπ
  exact ⟨a, b, ha0, haP, hrep, hden, hfactor⟩

/-- Replace a local uniformizer by its global numerator in two power
factorizations. The unit correction is explicit and is transported back
through the local equivalence. -/
theorem transfer_two_unit_power_factorizations
    {B V : Type u} [CommRing B] [CommRing V]
    (P : Ideal B) [P.IsPrime]
    (e : Localization.AtPrime P ≃+* V)
    (s q₀ q₁ : B) (π : V) (d : Vˣ)
    (n₀ n₁ : ℕ) (v₀ v₁ : V)
    (hs : e (algebraMap B (Localization.AtPrime P) s) = π * d)
    (h₀ : e (algebraMap B (Localization.AtPrime P) q₀) = π ^ n₀ * v₀)
    (h₁ : e (algebraMap B (Localization.AtPrime P) q₁) = π ^ n₁ * v₁)
    (hv₀ : IsUnit v₀) (hv₁ : IsUnit v₁) :
    ∃ u₀ u₁ : Localization.AtPrime P,
      IsUnit u₀ ∧ IsUnit u₁ ∧
      algebraMap B (Localization.AtPrime P) q₀ =
        (algebraMap B (Localization.AtPrime P) s) ^ n₀ * u₀ ∧
      algebraMap B (Localization.AtPrime P) q₁ =
        (algebraMap B (Localization.AtPrime P) s) ^ n₁ * u₁ := by
  let u₀V : V := v₀ * ((d⁻¹ : Vˣ) : V) ^ n₀
  let u₁V : V := v₁ * ((d⁻¹ : Vˣ) : V) ^ n₁
  have hu₀V : IsUnit u₀V := hv₀.mul ((Units.isUnit (d⁻¹ : Vˣ)).pow n₀)
  have hu₁V : IsUnit u₁V := hv₁.mul ((Units.isUnit (d⁻¹ : Vˣ)).pow n₁)
  let u₀ : Localization.AtPrime P := e.symm u₀V
  let u₁ : Localization.AtPrime P := e.symm u₁V
  have hu₀ : IsUnit u₀ := IsUnit.map e.symm.toMonoidHom hu₀V
  have hu₁ : IsUnit u₁ := IsUnit.map e.symm.toMonoidHom hu₁V
  have hdCancel₀ : (d : V) ^ n₀ * ((d⁻¹ : Vˣ) : V) ^ n₀ = 1 := by
    rw [← mul_pow]
    simp
  have hdCancel₁ : (d : V) ^ n₁ * ((d⁻¹ : Vˣ) : V) ^ n₁ = 1 := by
    rw [← mul_pow]
    simp
  have hcancel₀ : π ^ n₀ * v₀ = (π * d) ^ n₀ * u₀V := by
    calc
      π ^ n₀ * v₀ = π ^ n₀ * (v₀ * 1) := by simp
      _ = π ^ n₀ * (v₀ *
          ((d : V) ^ n₀ * ((d⁻¹ : Vˣ) : V) ^ n₀)) := by
        rw [hdCancel₀]
      _ = π ^ n₀ * (d : V) ^ n₀ *
          (v₀ * ((d⁻¹ : Vˣ) : V) ^ n₀) := by ring
      _ = (π * d) ^ n₀ * u₀V := by
        rw [mul_pow]
  have hcancel₁ : π ^ n₁ * v₁ = (π * d) ^ n₁ * u₁V := by
    calc
      π ^ n₁ * v₁ = π ^ n₁ * (v₁ * 1) := by simp
      _ = π ^ n₁ * (v₁ *
          ((d : V) ^ n₁ * ((d⁻¹ : Vˣ) : V) ^ n₁)) := by
        rw [hdCancel₁]
      _ = π ^ n₁ * (d : V) ^ n₁ *
          (v₁ * ((d⁻¹ : Vˣ) : V) ^ n₁) := by ring
      _ = (π * d) ^ n₁ * u₁V := by
        rw [mul_pow]
  refine ⟨u₀, u₁, hu₀, hu₁, ?_, ?_⟩
  · apply e.injective
    calc
      e (algebraMap B (Localization.AtPrime P) q₀) = π ^ n₀ * v₀ := h₀
      _ = (π * d) ^ n₀ * u₀V := hcancel₀
      _ = e ((algebraMap B (Localization.AtPrime P) s) ^ n₀ * u₀) := by
        simp [hs, u₀, u₀V]
  · apply e.injective
    calc
      e (algebraMap B (Localization.AtPrime P) q₁) = π ^ n₁ * v₁ := h₁
      _ = (π * d) ^ n₁ * u₁V := hcancel₁
      _ = e ((algebraMap B (Localization.AtPrime P) s) ^ n₁ * u₁) := by
        simp [hs, u₁, u₁V]

/-- Actual numerator plus the transferred q₀/q₁ order factorizations. The
only input about the numerator is the equivalence of the given local ring with
the DVR; no numerator or unit-power conclusion is assumed. -/
theorem exists_numerator_with_two_unit_power_factorizations_and_span
    {B V : Type u} [CommRing B] [IsDomain B] [CommRing V]
    (P : Ideal B) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)]
    (e : Localization.AtPrime P ≃+* V)
    (π : V) (hπ : Irreducible π)
    (q₀ q₁ : B) (n₀ n₁ : ℕ) (v₀ v₁ : V)
    (h₀ : e (algebraMap B (Localization.AtPrime P) q₀) = π ^ n₀ * v₀)
    (h₁ : e (algebraMap B (Localization.AtPrime P) q₁) = π ^ n₁ * v₁)
    (hv₀ : IsUnit v₀) (hv₁ : IsUnit v₁) :
    ∃ s : B, ∃ b : P.primeCompl, ∃ u₀ u₁ : Localization.AtPrime P,
      s ≠ 0 ∧ s ∈ P ∧
      IsLocalization.mk' (Localization.AtPrime P) s b = e.symm π ∧
      Ideal.span {algebraMap B (Localization.AtPrime P) s} =
        maximalIdeal (Localization.AtPrime P) ∧
      IsUnit u₀ ∧ IsUnit u₁ ∧
      algebraMap B (Localization.AtPrime P) q₀ =
        (algebraMap B (Localization.AtPrime P) s) ^ n₀ * u₀ ∧
      algebraMap B (Localization.AtPrime P) q₁ =
        (algebraMap B (Localization.AtPrime P) s) ^ n₁ * u₁ := by
  obtain ⟨s, b, hs0, hsP, hmk, hspan, hden, hfactor⟩ :=
    exists_numerator_of_local_equiv_with_span P e π hπ
  let d : Vˣ := hden.unit
  obtain ⟨u₀, u₁, hu₀, hu₁, hq₀, hq₁⟩ :=
    transfer_two_unit_power_factorizations P e s q₀ q₁ π
      d
      n₀ n₁ v₀ v₁ hfactor h₀ h₁ hv₀ hv₁
  exact ⟨s, b, u₀, u₁, hs0, hsP, hmk, hspan, hu₀, hu₁, hq₀, hq₁⟩

/-- Backwards-compatible projection omitting the maximal-ideal identity. -/
theorem exists_numerator_with_two_unit_power_factorizations
    {B V : Type u} [CommRing B] [IsDomain B] [CommRing V]
    (P : Ideal B) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)]
    (e : Localization.AtPrime P ≃+* V)
    (π : V) (hπ : Irreducible π)
    (q₀ q₁ : B) (n₀ n₁ : ℕ) (v₀ v₁ : V)
    (h₀ : e (algebraMap B (Localization.AtPrime P) q₀) = π ^ n₀ * v₀)
    (h₁ : e (algebraMap B (Localization.AtPrime P) q₁) = π ^ n₁ * v₁)
    (hv₀ : IsUnit v₀) (hv₁ : IsUnit v₁) :
    ∃ s : B, ∃ b : P.primeCompl, ∃ u₀ u₁ : Localization.AtPrime P,
      s ≠ 0 ∧ s ∈ P ∧
      IsLocalization.mk' (Localization.AtPrime P) s b = e.symm π ∧
      IsUnit u₀ ∧ IsUnit u₁ ∧
      algebraMap B (Localization.AtPrime P) q₀ =
        (algebraMap B (Localization.AtPrime P) s) ^ n₀ * u₀ ∧
      algebraMap B (Localization.AtPrime P) q₁ =
        (algebraMap B (Localization.AtPrime P) s) ^ n₁ * u₁ := by
  obtain ⟨s, b, u₀, u₁, hs0, hsP, hmk, _hspan, hu₀, hu₁, hq₀, hq₁⟩ :=
    exists_numerator_with_two_unit_power_factorizations_and_span
      P e π hπ q₀ q₁ n₀ n₁ v₀ v₁ h₀ h₁ hv₀ hv₁
  exact ⟨s, b, u₀, u₁, hs0, hsP, hmk, hu₀, hu₁, hq₀, hq₁⟩

end Stafford38.Geometry.ActualDivisorUniformizerNumerator
