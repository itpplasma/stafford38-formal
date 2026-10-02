module
public import Stafford38.Geometry.PaperUnitPowerFactorization
public import Mathlib.RingTheory.Ideal.NatInt

@[expose] public section

set_option autoImplicit false

open Stafford38.Geometry.PaperUnitPowerFactorization

namespace Stafford38.Geometry.UnitPowerNonzeroPrimeOracle

abbrev P : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)

theorem primeP : P.IsPrime := by
  dsimp [P]
  exact Ideal.isPrime_span_singleton_of_prime
    (Nat.prime_iff_prime_int.1 Nat.prime_two)

local instance : P.IsPrime := primeP

/-- The factor-clearing theorem at a genuinely nonzero prime: the 3- and
5-factors are units at (2), whereas 2 remains a nonunit. -/
theorem nonzero_prime_common_open :
    0 < 2 ∧ 2 < 3 ∧
    ∃ d₀ n₀ d₁ n₁ f : ℤ,
      d₀ ∉ P ∧ n₀ ∉ P ∧ d₁ ∉ P ∧ n₁ ∉ P ∧ f ∉ P ∧
      12 * d₀ = (2 : ℤ) ^ 2 * n₀ ∧ 40 * d₁ = (2 : ℤ) ^ 3 * n₁ ∧
      ∃ v₀ v₁ : Localization.Away f,
        IsUnit v₀ ∧ IsUnit v₁ ∧
        algebraMap ℤ (Localization.Away f) 12 =
          (algebraMap ℤ (Localization.Away f) 2) ^ 2 * v₀ ∧
        algebraMap ℤ (Localization.Away f) 40 =
          (algebraMap ℤ (Localization.Away f) 2) ^ 3 * v₁ ∧
        ¬ IsUnit (algebraMap ℤ (Localization.AtPrime P) 2) := by
  let V := Localization.AtPrime P
  let u₀ : V := algebraMap ℤ V 3
  let u₁ : V := algebraMap ℤ V 5
  have h3 : (3 : ℤ) ∉ P := by
    dsimp [P]
    rw [Ideal.mem_span_singleton]
    norm_num
  have h5 : (5 : ℤ) ∉ P := by
    dsimp [P]
    rw [Ideal.mem_span_singleton]
    norm_num
  have hu₀ : IsUnit u₀ := by
    dsimp [u₀]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff V P 3).2 h3
  have hu₁ : IsUnit u₁ := by
    dsimp [u₁]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff V P 5).2 h5
  have h₀ : algebraMap ℤ V 12 = (algebraMap ℤ V 2) ^ 2 * u₀ := by
    dsimp [u₀]
    rw [show (12 : ℤ) = 2 ^ 2 * 3 by norm_num, map_mul, map_pow]
  have h₁ : algebraMap ℤ V 40 = (algebraMap ℤ V 2) ^ 3 * u₁ := by
    dsimp [u₁]
    rw [show (40 : ℤ) = 2 ^ 3 * 5 by norm_num, map_mul, map_pow]
  have h2mem : (2 : ℤ) ∈ P := by
    exact Ideal.subset_span (by simp)
  have h2nonunit : ¬ IsUnit (algebraMap ℤ V (2 : ℤ)) := by
    intro hunit
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff V P 2).mp hunit) h2mem
  obtain ⟨d₀, n₀, d₁, n₁, f, hd₀, hn₀, hd₁, hn₁, hf, hq₀, hq₁,
      v₀, v₁, hv₀, hv₁, hfactor₀, hfactor₁⟩ :=
    exists_common_away_unit_power_factorizations P 2 12 40 2 3
      u₀ u₁ hu₀ hu₁ h₀ h₁
  refine ⟨by norm_num, by norm_num, d₀, n₀, d₁, n₁, f,
    hd₀, hn₀, hd₁, hn₁, hf, hq₀, hq₁, v₀, v₁, hv₀, hv₁,
    hfactor₀, hfactor₁, h2nonunit⟩

#print axioms nonzero_prime_common_open

end Stafford38.Geometry.UnitPowerNonzeroPrimeOracle
