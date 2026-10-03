module
public import Stafford38.Characteristic.PostScalarExtensionPoisson
public import Stafford38.Characteristic.LocalizedPartialDerivation
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

@[expose] public section

/-!
# Localization proof of componentwise involutivity

This file formalizes the localization route in the paper's proof of
componentwise involutivity.  First extend each polynomial partial derivative
to fractions by the quotient rule, and use these derivations to define the
localized Poisson bracket.  Then localize the involutive radical, identify it
with the maximal ideal at a minimal prime, and contract bracket membership
using primeness.
-/

namespace Stafford38.Characteristic.PaperLocalizedInvolutivity

open Stafford38.Characteristic
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.Characteristic.LocalizedPartialDerivation

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

def localizedPoissonBracket (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (f g : AtPrime P) : AtPrime P :=
  ∑ i : Fin n,
    (localizedPDeriv P (Sum.inl i) f * localizedPDeriv P (Sum.inr i) g -
      localizedPDeriv P (Sum.inr i) f * localizedPDeriv P (Sum.inl i) g)

theorem localizedPoissonBracket_add_left
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (f₁ f₂ g : AtPrime P) :
    localizedPoissonBracket P (f₁ + f₂) g =
      localizedPoissonBracket P f₁ g + localizedPoissonBracket P f₂ g := by
  unfold localizedPoissonBracket
  simp only [localizedPDeriv_add, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem localizedPoissonBracket_add_right
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (f g₁ g₂ : AtPrime P) :
    localizedPoissonBracket P f (g₁ + g₂) =
      localizedPoissonBracket P f g₁ + localizedPoissonBracket P f g₂ := by
  unfold localizedPoissonBracket
  simp only [localizedPDeriv_add, mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem localizedPoissonBracket_mul_left
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (a f g : AtPrime P) :
    localizedPoissonBracket P (a * f) g =
      a * localizedPoissonBracket P f g + f * localizedPoissonBracket P a g := by
  simp only [localizedPoissonBracket, localizedPDeriv_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem localizedPoissonBracket_mul_right
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (f a g : AtPrime P) :
    localizedPoissonBracket P f (a * g) =
      a * localizedPoissonBracket P f g + g * localizedPoissonBracket P f a := by
  simp only [localizedPoissonBracket, localizedPDeriv_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem localizedPoissonBracket_algebraMap
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (f g : R (k := k) (n := n)) :
    localizedPoissonBracket (k := k) (n := n) P
        (algebraMap (R (k := k) (n := n)) (AtPrime P) f)
        (algebraMap (R (k := k) (n := n)) (AtPrime P) g) =
      algebraMap (R (k := k) (n := n)) (AtPrime P) (poissonBracket f g) := by
  simp [localizedPoissonBracket, localizedPDeriv_algebraMap, poissonBracket,
    map_sum, map_sub, map_mul]

theorem localizedPDeriv_zero
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (i : PhaseVar n) :
    localizedPDeriv P i (0 : AtPrime P) = 0 :=
  Derivation.map_zero (localizedPDeriv P i)

theorem localizedPoissonBracket_zero_left
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (g : AtPrime P) :
    localizedPoissonBracket P 0 g = 0 := by
  simp [localizedPoissonBracket, localizedPDeriv_zero]

theorem localizedPoissonBracket_zero_right
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (f : AtPrime P) :
    localizedPoissonBracket P f 0 = 0 := by
  simp [localizedPoissonBracket, localizedPDeriv_zero]

/-- The involutive condition survives localization.  This is proved by
induction on the localized ideal's generators; the product identities are
the biderivation rules for the fraction-extended bracket above. -/
theorem localizedMap_isInvolutive
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (I : Ideal (R (k := k) (n := n))) (hI : IsInvolutive I) :
    ∀ f ∈ I.map (algebraMap (R (k := k) (n := n)) (AtPrime P)),
      ∀ g ∈ I.map (algebraMap (R (k := k) (n := n)) (AtPrime P)),
        localizedPoissonBracket P f g ∈
          I.map (algebraMap (R (k := k) (n := n)) (AtPrime P)) := by
  let M : Ideal (AtPrime P) :=
    I.map (algebraMap (R (k := k) (n := n)) (AtPrime P))
  intro f hf
  change f ∈ I.map (algebraMap (R (k := k) (n := n)) (AtPrime P)) at hf
  rw [Ideal.map] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨f₀, hf₀, rfl⟩
      intro g hg
      change g ∈ I.map (algebraMap (R (k := k) (n := n)) (AtPrime P)) at hg
      rw [Ideal.map] at hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
          rcases hg with ⟨g₀, hg₀, rfl⟩
          change localizedPoissonBracket P
            (algebraMap (R (k := k) (n := n)) (AtPrime P) f₀)
            (algebraMap (R (k := k) (n := n)) (AtPrime P) g₀) ∈ M
          rw [localizedPoissonBracket_algebraMap]
          exact Ideal.mem_map_of_mem _ (hI f₀ hf₀ g₀ hg₀)
      | zero =>
          rw [localizedPoissonBracket_zero_right]
          exact M.zero_mem
      | add g₁ g₂ _ _ hg₁ hg₂ =>
          rw [localizedPoissonBracket_add_right]
          exact M.add_mem hg₁ hg₂
      | smul a g hgm hg =>
          rw [smul_eq_mul, localizedPoissonBracket_mul_right]
          exact M.add_mem (M.mul_mem_left _ hg) (M.mul_mem_right _ hgm)
  | zero =>
      intro g hg
      rw [localizedPoissonBracket_zero_left]
      exact M.zero_mem
  | add f₁ f₂ _ _ hf₁ hf₂ =>
      intro g hg
      rw [localizedPoissonBracket_add_left]
      exact M.add_mem (hf₁ g hg) (hf₂ g hg)
  | smul a f hfm hf =>
      intro g hg
      rw [smul_eq_mul, localizedPoissonBracket_mul_left]
      exact M.add_mem (M.mul_mem_left _ (hf g hg)) (M.mul_mem_right _ hfm)

/-- At a prime minimal over `J`, the radical of the localized ideal is the
localized prime.  The first equality is the general localization-radical
identity; the second is the minimal-prime theorem for localization. -/
theorem radical_map_eq_prime_map_of_minimal
    (J P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (hP : P ∈ J.minimalPrimes) :
    J.radical.map (algebraMap (R (k := k) (n := n)) (AtPrime P)) =
      P.map (algebraMap (R (k := k) (n := n)) (AtPrime P)) := by
  rw [IsLocalization.map_radical (P.primeCompl) (AtPrime P)]
  exact IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := AtPrime P) P J hP

/-- The localized radical is exactly the maximal ideal of the local ring at
the minimal prime. -/
theorem radical_map_eq_maximalIdeal_of_minimal
    (J P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (hP : P ∈ J.minimalPrimes) :
    J.radical.map (algebraMap (R (k := k) (n := n)) (AtPrime P)) =
      IsLocalRing.maximalIdeal (AtPrime P) := by
  rw [radical_map_eq_prime_map_of_minimal J P hP]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal P (AtPrime P)

/-- Localization proof of the componentwise statement: involutivity of
`√J` implies involutivity of each minimal prime over `J`.  Unlike the
saturation proof in `RadicalMinimalPrimeInvolutivity`, this follows the paper's
argument through the localized Poisson structure, its maximal ideal, and
contraction by primeness. -/
theorem minimalPrimes_isInvolutive_of_radical_isInvolutive_viaLocalization
    (J : Ideal (R (k := k) (n := n))) (hJ : IsInvolutive J.radical) :
    ∀ P ∈ J.minimalPrimes, IsInvolutive P := by
  intro P hP
  letI : P.IsPrime := hP.1.1
  intro f hf g hg
  let φ := algebraMap (R (k := k) (n := n)) (AtPrime P)
  have hrad := radical_map_eq_prime_map_of_minimal J P hP
  have hfLoc : φ f ∈ P.map φ := Ideal.mem_map_of_mem φ hf
  have hgLoc : φ g ∈ P.map φ := Ideal.mem_map_of_mem φ hg
  rw [← hrad] at hfLoc hgLoc
  have hbrLoc := localizedMap_isInvolutive P J.radical hJ (φ f) hfLoc (φ g) hgLoc
  rw [localizedPoissonBracket_algebraMap] at hbrLoc
  rw [hrad] at hbrLoc
  obtain ⟨s, hs, hmul⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl
      (AtPrime P) P (poissonBracket f g)).mp hbrLoc
  have hprime : P.IsPrime := hP.1.1
  rcases hprime.mem_or_mem hmul with hsP | hbr
  · exact (hs hsP).elim
  · exact hbr

#print axioms localizedPDeriv
#print axioms localizedPDeriv_mul
#print axioms localizedPoissonBracket_mul_left
#print axioms localizedMap_isInvolutive
#print axioms radical_map_eq_prime_map_of_minimal
#print axioms radical_map_eq_maximalIdeal_of_minimal
#print axioms minimalPrimes_isInvolutive_of_radical_isInvolutive_viaLocalization

end
end Stafford38.Characteristic.PaperLocalizedInvolutivity
