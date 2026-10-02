module
public import Stafford38.Geometry.SameWitness.AwayFactorToAtPrime

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.SameWitness.AwayFactorToAtPrimeConsumer

open Stafford38.Geometry.SameWitness

universe u

/-- Consumer for the away-to-at-prime transport of one unit-power
factorization: the conclusion is restated literally and proved by applying
`Stafford38.Geometry.SameWitness.factorization_to_atPrime`. -/
theorem factorization_to_atPrime_consumer
    {B : Type u} [CommRing B] (M : Ideal B) [M.IsPrime]
    (f : B) (hf : f ∉ M) (q s : B) (n : ℕ)
    (v : Localization.Away f) (hv : IsUnit v)
    (h : algebraMap B (Localization.Away f) q =
      (algebraMap B (Localization.Away f) s) ^ n * v) :
    ∃ u : Localization.AtPrime M, IsUnit u ∧
      algebraMap B (Localization.AtPrime M) q =
        (algebraMap B (Localization.AtPrime M) s) ^ n * u := by
  exact factorization_to_atPrime M f hf q s n v hv h

/-- Consumer for the paired divisor-order transport: the conclusion is
restated literally and proved by applying
`Stafford38.Geometry.SameWitness.pair_factorizations_to_atPrime`. -/
theorem pair_factorizations_to_atPrime_consumer
    {B : Type u} [CommRing B] (M : Ideal B) [M.IsPrime]
    (f : B) (hf : f ∉ M) (s q₀ q₁ : B) (e₀ e₁ : ℕ)
    (v₀ v₁ : Localization.Away f)
    (hv₀ : IsUnit v₀) (hv₁ : IsUnit v₁)
    (h₀ : algebraMap B (Localization.Away f) q₀ =
      (algebraMap B (Localization.Away f) s) ^ e₀ * v₀)
    (h₁ : algebraMap B (Localization.Away f) q₁ =
      (algebraMap B (Localization.Away f) s) ^ e₁ * v₁) :
    ∃ u₀ u₁ : Localization.AtPrime M,
      IsUnit u₀ ∧ IsUnit u₁ ∧
      algebraMap B (Localization.AtPrime M) q₀ =
        (algebraMap B (Localization.AtPrime M) s) ^ e₀ * u₀ ∧
      algebraMap B (Localization.AtPrime M) q₁ =
        (algebraMap B (Localization.AtPrime M) s) ^ e₁ * u₁ := by
  exact pair_factorizations_to_atPrime M f hf s q₀ q₁ e₀ e₁ v₀ v₁ hv₀ hv₁ h₀ h₁

#print axioms factorization_to_atPrime_consumer
#print axioms pair_factorizations_to_atPrime_consumer

end Stafford38.Geometry.SameWitness.AwayFactorToAtPrimeConsumer
