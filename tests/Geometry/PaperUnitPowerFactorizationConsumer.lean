module
public import Stafford38.Geometry.PaperUnitPowerFactorization

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.PaperUnitPowerFactorizationConsumer

open Stafford38.Geometry.PaperUnitPowerFactorization

/-- A concrete positive-order-gap case: the local units are 3 and 5, and the
single common open may invert their product. -/
theorem concrete_common_open_factorization :
    ∃ (d₀ n₀ d₁ n₁ f : ℤ),
      d₀ ≠ 0 ∧ n₀ ≠ 0 ∧ d₁ ≠ 0 ∧ n₁ ≠ 0 ∧ f ≠ 0 ∧
      12 * d₀ = (2 : ℤ) ^ 2 * n₀ ∧ 40 * d₁ = (2 : ℤ) ^ 3 * n₁ ∧
      ∃ v₀ v₁ : Localization.Away f,
        IsUnit v₀ ∧ IsUnit v₁ ∧
        algebraMap ℤ (Localization.Away f) 12 =
          (algebraMap ℤ (Localization.Away f) 2) ^ 2 * v₀ ∧
        algebraMap ℤ (Localization.Away f) 40 =
          (algebraMap ℤ (Localization.Away f) 2) ^ 3 * v₁ := by
  let V := Localization.AtPrime (⊥ : Ideal ℤ)
  let u₀ : V := algebraMap ℤ V 3
  let u₁ : V := algebraMap ℤ V 5
  have hu₀ : IsUnit u₀ := by
    dsimp [u₀]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff V (⊥ : Ideal ℤ) 3).2 (by simp)
  have hu₁ : IsUnit u₁ := by
    dsimp [u₁]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff V (⊥ : Ideal ℤ) 5).2 (by simp)
  have h₀ : algebraMap ℤ V 12 = (algebraMap ℤ V 2) ^ 2 * u₀ := by
    dsimp [u₀]
    rw [show (12 : ℤ) = 2 ^ 2 * 3 by norm_num, map_mul, map_pow]
  have h₁ : algebraMap ℤ V 40 = (algebraMap ℤ V 2) ^ 3 * u₁ := by
    dsimp [u₁]
    rw [show (40 : ℤ) = 2 ^ 3 * 5 by norm_num, map_mul, map_pow]
  obtain ⟨d₀, n₀, d₁, n₁, f, hd₀, hn₀, hd₁, hn₁, hf, hq₀, hq₁,
      v₀, v₁, hv₀, hv₁, hfactor₀, hfactor₁⟩ :=
    exists_common_away_unit_power_factorizations (⊥ : Ideal ℤ) 2 12 40 2 3
      u₀ u₁ hu₀ hu₁ h₀ h₁
  refine ⟨d₀, n₀, d₁, n₁, f, ?_, ?_, ?_, ?_, ?_, hq₀, hq₁,
    v₀, v₁, hv₀, hv₁, hfactor₀, hfactor₁⟩
  · simpa using hd₀
  · simpa using hn₀
  · simpa using hd₁
  · simpa using hn₁
  · simpa using hf

/-- Independent direct oracle: inverting 15 makes both nontrivial local unit
factors 3 and 5 regular at once. -/
theorem explicit_common_open_oracle :
    IsUnit (algebraMap ℤ (Localization.Away (15 : ℤ)) 3) ∧
    IsUnit (algebraMap ℤ (Localization.Away (15 : ℤ)) 5) ∧
    algebraMap ℤ (Localization.Away (15 : ℤ)) 12 =
      (algebraMap ℤ (Localization.Away (15 : ℤ)) 2) ^ 2 *
        algebraMap ℤ (Localization.Away (15 : ℤ)) 3 ∧
    algebraMap ℤ (Localization.Away (15 : ℤ)) 40 =
      (algebraMap ℤ (Localization.Away (15 : ℤ)) 2) ^ 3 *
        algebraMap ℤ (Localization.Away (15 : ℤ)) 5 := by
  let W := Localization.Away (15 : ℤ)
  have hf : IsUnit (algebraMap ℤ W 15) :=
    IsLocalization.Away.algebraMap_isUnit (15 : ℤ)
  have h3 : (3 : ℤ) ∣ 15 := ⟨5, by norm_num⟩
  have h5 : (5 : ℤ) ∣ 15 := ⟨3, by norm_num⟩
  have h3unit : IsUnit (algebraMap ℤ W 3) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap ℤ W) h3) hf
  have h5unit : IsUnit (algebraMap ℤ W 5) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap ℤ W) h5) hf
  refine ⟨h3unit, h5unit, ?_, ?_⟩
  · rw [show (12 : ℤ) = 2 ^ 2 * 3 by norm_num, map_mul, map_pow]
  · rw [show (40 : ℤ) = 2 ^ 3 * 5 by norm_num, map_mul, map_pow]

#print axioms concrete_common_open_factorization
#print axioms explicit_common_open_oracle
#print axioms exists_common_away_unit_power_factorizations

end Stafford38.Geometry.PaperUnitPowerFactorizationConsumer
