module

public import Stafford38.Paper.Section2.Filtration
public import Mathlib.RingTheory.Nullstellensatz

@[expose] public section

/-!
# Section 2 of the paper: Definitions 2.5–2.7 and Theorem 2.12

Definition 2.5 (the cotangent bundle `T^*X = Spec k[x, ξ]`, its closed points
`(y, ξ)`, the projection and the fibres), Definition 2.6 (`Spec`, `V(J)`,
`V_K(J)`, `I(S)`, `𝔪_a`), Definition 2.7 (the characteristic variety
`Char(M) = V(Ann gr M)`) and Theorem 2.12 (Hilbert's Nullstellensatz).

Points of `K^{2n} = K^n × (K^n)^*` are functions `PhaseVar n → K`; `Sum.inl i`
is the base coordinate `x_{i+1}`, `Sum.inr i` the fibre coordinate `ξ_{i+1}`.
-/

namespace Stafford38.Paper.Section2

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u v

section Spec

variable {S : Type u} [CommRing S]

/-- **Definition 2.6 (vanishing locus).** `V(J) = {𝔭 ∈ Spec S : 𝔭 ⊇ J}`, the
Mathlib `PrimeSpectrum.zeroLocus`. -/
abbrev V (J : Ideal S) : Set (PrimeSpectrum S) :=
  PrimeSpectrum.zeroLocus (J : Set S)

theorem mem_V_iff (J : Ideal S) (P : PrimeSpectrum S) : P ∈ V J ↔ J ≤ P.asIdeal :=
  PrimeSpectrum.mem_zeroLocus P J

end Spec

section Classical

variable (K : Type u) [Field K] {σ : Type v}

/-- **Definition 2.6 (classical zero set).**
`V_K(J) = {a ∈ K^N : f(a) = 0 ∀ f ∈ J}`. -/
def VK (J : Ideal (MvPolynomial σ K)) : Set (σ → K) :=
  {a | ∀ f ∈ J, MvPolynomial.eval a f = 0}

theorem VK_eq_zeroLocus (J : Ideal (MvPolynomial σ K)) :
    VK K J = MvPolynomial.zeroLocus K J := by
  ext a
  simp [VK, MvPolynomial.aeval_eq_eval]

/-- **Definition 2.6 (vanishing ideal).** `I(S) = {f : f(a) = 0 ∀ a ∈ S}`. -/
def vanishingIdealOf (T : Set (σ → K)) : Ideal (MvPolynomial σ K) :=
  MvPolynomial.vanishingIdeal K T

theorem mem_vanishingIdealOf (T : Set (σ → K)) (f : MvPolynomial σ K) :
    f ∈ vanishingIdealOf K T ↔ ∀ a ∈ T, MvPolynomial.eval a f = 0 := by
  simp [vanishingIdealOf, MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.aeval_eq_eval]

/-- **Definition 2.6.** `𝔪_a = (z_1 - a_1, …, z_N - a_N)`. -/
def maxIdealAt (a : σ → K) : Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range fun i => MvPolynomial.X i - MvPolynomial.C (a i))

/-- `f ∈ 𝔪_a` iff `f(a) = 0`. -/
theorem mem_maxIdealAt_iff (a : σ → K) (f : MvPolynomial σ K) :
    f ∈ maxIdealAt K a ↔ MvPolynomial.eval a f = 0 := by
  constructor
  · intro hf
    refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy => by simp [hx, hy])
      (fun r x _ hx => by simp [hx]) hf
    rintro _ ⟨i, rfl⟩
    simp
  · intro hf
    let q := Ideal.Quotient.mk (maxIdealAt K a)
    have hred : ∀ g : MvPolynomial σ K, q g = q (MvPolynomial.C (MvPolynomial.eval a g)) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C c => simp
      | add g h hg hh => rw [map_add, hg, hh, map_add, map_add, map_add]
      | mul_X g i hg =>
          have hX : q (MvPolynomial.X i) = q (MvPolynomial.C (a i)) := by
            rw [Ideal.Quotient.eq]
            exact Ideal.subset_span ⟨i, rfl⟩
          rw [map_mul, hg, hX, ← map_mul, ← map_mul]
          simp
    have h0 := hred f
    rw [hf, map_zero, map_zero] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0

theorem maxIdealAt_eq_vanishingIdeal (a : σ → K) :
    maxIdealAt K a = MvPolynomial.vanishingIdeal K {a} := by
  ext f
  rw [mem_maxIdealAt_iff, MvPolynomial.mem_vanishingIdeal_singleton_iff,
    MvPolynomial.aeval_eq_eval]

instance (a : σ → K) : (maxIdealAt K a).IsMaximal := by
  rw [maxIdealAt_eq_vanishingIdeal]
  infer_instance

/-- `𝔪_a` as a point of `Spec K[z]`. -/
def closedPoint (a : σ → K) : PrimeSpectrum (MvPolynomial σ K) :=
  ⟨maxIdealAt K a, Ideal.IsMaximal.isPrime inferInstance⟩

/-- **Definition 2.6, last sentence.** `a ∈ V_K(J)` iff `𝔪_a ∈ V(J)`. -/
theorem mem_VK_iff_closedPoint_mem_V (J : Ideal (MvPolynomial σ K)) (a : σ → K) :
    a ∈ VK K J ↔ closedPoint K a ∈ V J := by
  rw [mem_V_iff]
  change (∀ f ∈ J, MvPolynomial.eval a f = 0) ↔ J ≤ maxIdealAt K a
  exact ⟨fun h f hf => (mem_maxIdealAt_iff K a f).mpr (h f hf),
    fun h f hf => (mem_maxIdealAt_iff K a f).mp (h hf)⟩

/-- **Theorem 2.12 (Hilbert's Nullstellensatz).** Let `K` be algebraically
closed and `J ⊆ K[z_1, …, z_N]` an ideal (the variables indexed by any
finite type `σ`, e.g. `PhaseVar n` for `K[x, ξ]`).
(a) The maximal ideals of `K[z]` are exactly the `𝔪_a`, `a ↦ 𝔪_a` is
injective, and `V_K(J)` corresponds to the closed points of `V(J)`;
(b) `V_K(J) = ∅` iff `1 ∈ J`;
(c) `I(V_K(J)) = √J`. -/
theorem theorem_2_12 [IsAlgClosed K] [Finite σ] (J : Ideal (MvPolynomial σ K)) :
    ((∀ M : Ideal (MvPolynomial σ K), M.IsMaximal ↔ ∃ a, M = maxIdealAt K a) ∧
      Function.Injective (maxIdealAt K (σ := σ)) ∧
      ∀ a, a ∈ VK K J ↔ closedPoint K a ∈ V J) ∧
    (VK K J = ∅ ↔ (1 : MvPolynomial σ K) ∈ J) ∧
    vanishingIdealOf K (VK K J) = J.radical := by
  have hc : vanishingIdealOf K (VK K J) = J.radical := by
    rw [vanishingIdealOf, VK_eq_zeroLocus, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
  refine ⟨⟨fun M => ?_, ?_, mem_VK_iff_closedPoint_mem_V K J⟩, ⟨fun h => ?_, fun h => ?_⟩, hc⟩
  · simp only [maxIdealAt_eq_vanishingIdeal]
    exact MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton
  · intro a b hab
    funext i
    have hmem : MvPolynomial.X i - MvPolynomial.C (a i) ∈ maxIdealAt K b :=
      hab ▸ Ideal.subset_span ⟨i, rfl⟩
    rw [mem_maxIdealAt_iff] at hmem
    simpa [sub_eq_zero, eq_comm] using hmem
  · have h1 : (1 : MvPolynomial σ K) ∈ J.radical := by
      rw [← hc, h, mem_vanishingIdealOf]
      simp
    exact (Ideal.radical_eq_top.mp ((Ideal.eq_top_iff_one _).mpr h1)).symm ▸ Submodule.mem_top
  · ext a
    simp only [Set.mem_empty_iff_false, iff_false]
    intro ha
    simpa using ha 1 h

end Classical

variable (k : Type u) [Field k]

/-- **Definition 2.5 (cotangent bundle).** `T^*X = Spec k[x, ξ]` for
`X = 𝔸^n_k`. -/
abbrev CotangentBundle (n : ℕ) := PrimeSpectrum (SymbolRing k n)

/-- **Definition 2.5 (projection on closed points).** `π(y, ξ) = y`. -/
def proj {K : Type v} {n : ℕ} (z : PhaseVar n → K) : Fin n → K :=
  fun i => z (Sum.inl i)

/-- **Definition 2.5 (fibre).** `T^*_y X = π^{-1}(y) ≅ (K^n)^*`. -/
def fibre {K : Type v} {n : ℕ} (y : Fin n → K) : Set (PhaseVar n → K) :=
  proj ⁻¹' {y}

/-- **Definition 2.7 (characteristic variety)** of `M = A_n(k)/I` with the good
order filtration `M_m = qF_m`: `Char(M) = V(Ann_{k[x,ξ]} gr M) ⊆ T^*X`.  The
paper defines `Char` for every finitely generated module; Sections 3–7 use it
only for such cyclic quotients. -/
def Char {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) : Set (CotangentBundle k n) :=
  V (Module.annihilator (SymbolRing k n) (grCyclic k I))

end

end Stafford38.Paper.Section2
