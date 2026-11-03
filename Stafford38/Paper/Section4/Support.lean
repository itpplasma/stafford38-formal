module

public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Exact

@[expose] public section

/-!
# Definitions 4.4–4.6 and Lemma 4.7

The paper's localization, support and length are Mathlib's
`Localization S` / `LocalizedModule S N`, `Module.support` and `Module.length`.
Each `definition_4_*` below proves that the printed definition agrees with the
Mathlib one where the wording differs; the later proofs use these lemmas.
-/

namespace Stafford38.Paper.Section4

noncomputable section

universe v

variable {R : Type*} [CommRing R]

/-- **Definition 4.4 (localization).**  Mathlib's `Localization S` and
`LocalizedModule S N` are the rings and modules of fractions with
`a/s = a'/s' ↔ t(s'a − sa') = 0` and `y/s = y'/s' ↔ t(s'y − sy') = 0` for some
`t ∈ S`, and localization is exact. -/
theorem definition_4_4 (S : Submonoid R) {N : Type v} [AddCommGroup N] [Module R N] :
    (∀ (a a' : R) (s s' : S),
        Localization.mk a s = Localization.mk a' s' ↔
          ∃ t : S, (t : R) * ((s' : R) * a - (s : R) * a') = 0) ∧
      (∀ (y y' : N) (s s' : S),
        LocalizedModule.mk y s = LocalizedModule.mk y' s' ↔
          ∃ t : S, t • (s' • y - s • y') = 0) ∧
      ∀ {N₀ N₂ : Type v} [AddCommGroup N₀] [Module R N₀] [AddCommGroup N₂] [Module R N₂]
        (g : N₀ →ₗ[R] N) (h : N →ₗ[R] N₂), Function.Exact g h →
          Function.Exact (LocalizedModule.map S g) (LocalizedModule.map S h) := by
  refine ⟨fun a a' s s' => ?_, fun y y' s s' => ?_, fun g h ex => ?_⟩
  · rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    simp only [mul_sub, sub_eq_zero]
  · rw [LocalizedModule.mk_eq]
    simp only [smul_sub, sub_eq_zero]
  · exact LocalizedModule.map_exact S g h ex

/-- **Definition 4.5 (support).**  `Supp_R(M) = {𝔭 | M_𝔭 ≠ 0}`. -/
theorem definition_4_5 {M : Type*} [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    p ∈ Module.support R M ↔
      ∃ z : LocalizedModule p.asIdeal.primeCompl M, z ≠ 0 := by
  rw [Module.mem_support_iff]
  exact nontrivial_iff_exists_ne 0

/-- **Definition 4.6 (length).**  `Module.length` is the number of steps of a
composition series `0 = N₀ ⊊ ⋯ ⊊ N_ℓ = N` (successive steps are coverings,
i.e. have simple quotients, `covBy_iff_quot_is_simple`), independent of the
series, and length is additive on short exact sequences. -/
theorem definition_4_6 {T : Type*} {M : Type v} [Ring T] [AddCommGroup M] [Module T M] :
    (∀ s : CompositionSeries (Submodule T M), s.head = ⊥ → s.last = ⊤ →
        (s.length : ℕ∞) = Module.length T M) ∧
      ∀ {N P : Type v} [AddCommGroup N] [Module T N] [AddCommGroup P] [Module T P]
        (f : N →ₗ[T] M) (g : M →ₗ[T] P), Function.Injective f → Function.Surjective g →
          Function.Exact f g → Module.length T M = Module.length T N + Module.length T P :=
  ⟨fun s h₁ h₂ => Module.length_compositionSeries s h₁ h₂,
    fun f g hf hg H => Module.length_eq_add_of_exact f g hf hg H⟩

/-! ## Lemma 4.7 -/

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- In `N_𝔭`, `y/1 = 0` iff some `u ∉ 𝔭` kills `y`, i.e. iff
`Ann_R(y) ⊄ 𝔭`. -/
theorem step_4_7_mk_one_eq_zero_iff (p : PrimeSpectrum R) (y : N) :
    LocalizedModule.mk y (1 : p.asIdeal.primeCompl) = 0 ↔
      ¬ (R ∙ y).annihilator ≤ p.asIdeal := by
  rw [← LocalizedModule.zero_mk (1 : p.asIdeal.primeCompl),
    (definition_4_4 p.asIdeal.primeCompl (N := N)).2.1]
  simp only [one_smul, smul_zero, sub_zero, IsConcreteLE.le_iff,
    Submodule.mem_annihilator_span_singleton, not_forall]
  constructor
  · rintro ⟨⟨u, hu⟩, h⟩
    exact ⟨u, h, hu⟩
  · rintro ⟨u, h, hu⟩
    exact ⟨⟨u, hu⟩, h⟩

/-- The contrapositive: `y/1 ≠ 0 ↔ Ann_R(y) ⊆ 𝔭`. -/
theorem step_4_7_mk_one_ne_zero_iff (p : PrimeSpectrum R) (y : N) :
    LocalizedModule.mk y (1 : p.asIdeal.primeCompl) ≠ 0 ↔
      (R ∙ y).annihilator ≤ p.asIdeal := by
  rw [ne_eq, step_4_7_mk_one_eq_zero_iff, not_not]

/-- `s ∉ 𝔭` is invertible in `N_𝔭`, so `y/s = 0 ↔ y/1 = 0`. -/
theorem step_4_7_mk_eq_zero_iff (p : PrimeSpectrum R) (y : N) (s : p.asIdeal.primeCompl) :
    LocalizedModule.mk y s = 0 ↔ LocalizedModule.mk y (1 : p.asIdeal.primeCompl) = 0 := by
  have h : LocalizedModule.mk y s =
      (IsLocalization.mk' (Localization p.asIdeal.primeCompl) (1 : R) s) •
        LocalizedModule.mk y (1 : p.asIdeal.primeCompl) := by
    rw [← Localization.mk_eq_mk', LocalizedModule.mk_smul_mk, one_smul, mul_one]
  rw [h]
  constructor
  · intro h0
    have := congrArg (fun z => (algebraMap R (Localization p.asIdeal.primeCompl) s) • z) h0
    simp only [smul_zero, smul_smul] at this
    rwa [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self,
      one_smul] at this
  · intro h0
    rw [h0, smul_zero]

/-- **Lemma 4.7.** `𝔭 ∈ Supp_R(N)` iff there is `y ∈ N` with `Ann_R(y) ⊆ 𝔭`. -/
theorem lemma_4_7 (p : PrimeSpectrum R) :
    p ∈ Module.support R N ↔ ∃ y : N, (R ∙ y).annihilator ≤ p.asIdeal := by
  rw [definition_4_5]
  constructor
  · -- (⇒) a nonzero `y/s` gives `y/1 ≠ 0`
    rintro ⟨z, hz⟩
    induction z using LocalizedModule.induction_on with
    | h y s =>
        refine ⟨y, (step_4_7_mk_one_ne_zero_iff p y).1 ?_⟩
        rwa [ne_eq, ← step_4_7_mk_eq_zero_iff p y s]
  · -- (⇐) `y/1 ≠ 0`
    rintro ⟨y, hy⟩
    exact ⟨_, (step_4_7_mk_one_ne_zero_iff p y).2 hy⟩

#print axioms definition_4_4
#print axioms definition_4_5
#print axioms definition_4_6
#print axioms step_4_7_mk_one_eq_zero_iff
#print axioms step_4_7_mk_eq_zero_iff
#print axioms lemma_4_7

end

end Stafford38.Paper.Section4
