module
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.AwayFactorToAtPrime

noncomputable section

universe u

/-- Transport a unit-power factorization from an away localization to the
localization at a prime avoiding its denominator. -/
theorem factorization_to_atPrime
    {B : Type u} [CommRing B] (M : Ideal B) [M.IsPrime]
    (f : B) (hf : f ∉ M) (q s : B) (n : ℕ)
    (v : Localization.Away f) (hv : IsUnit v)
    (h : algebraMap B (Localization.Away f) q =
      (algebraMap B (Localization.Away f) s) ^ n * v) :
    ∃ u : Localization.AtPrime M, IsUnit u ∧
      algebraMap B (Localization.AtPrime M) q =
        (algebraMap B (Localization.AtPrime M) s) ^ n * u := by
  let ψ : Localization.Away f →+* Localization.AtPrime M :=
    IsLocalization.Away.lift f
      (IsLocalization.map_units (Localization.AtPrime M)
        (M := M.primeCompl) ⟨f, hf⟩)
  have hψ : ψ.comp (algebraMap B (Localization.Away f)) =
      algebraMap B (Localization.AtPrime M) := by
    ext b
    simp [ψ]
  have hψb (b : B) :
      ψ (algebraMap B (Localization.Away f) b) =
        algebraMap B (Localization.AtPrime M) b := by
    exact DFunLike.congr_fun hψ b
  refine ⟨ψ v, hv.map ψ, ?_⟩
  have hh := congrArg ψ h
  calc
    algebraMap B (Localization.AtPrime M) q =
        ψ (algebraMap B (Localization.Away f) q) := (hψb q).symm
    _ = ψ ((algebraMap B (Localization.Away f) s) ^ n * v) := hh
    _ = algebraMap B (Localization.AtPrime M) s ^ n * ψ v := by
      rw [map_mul, map_pow, hψb]

/-- Transport both divisor-order factorizations from the one ground-point
away open to its local ring. -/
theorem pair_factorizations_to_atPrime
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
  obtain ⟨u₀, hu₀, hq₀⟩ := factorization_to_atPrime M f hf q₀ s e₀ v₀ hv₀ h₀
  obtain ⟨u₁, hu₁, hq₁⟩ := factorization_to_atPrime M f hf q₁ s e₁ v₁ hv₁ h₁
  exact ⟨u₀, u₁, hu₀, hu₁, hq₀, hq₁⟩

end

end Stafford38.Geometry.AwayFactorToAtPrime

#print axioms Stafford38.Geometry.AwayFactorToAtPrime.factorization_to_atPrime
#print axioms Stafford38.Geometry.AwayFactorToAtPrime.pair_factorizations_to_atPrime
