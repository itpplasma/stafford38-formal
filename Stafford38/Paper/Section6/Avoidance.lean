module

public import Stafford38.Paper.Section2
public import Stafford38.Paper.Section3
public import Stafford38.Paper.Section4

@[expose] public section

/-!
# Proposition 6.1: `Char(Q) ∩ V(x₁) = ∅`

Notation of Sections 3 and 4: `d̃` is in the normal form (3.1) with `N ≥ 1`,
`𝓘 = d̃A_n + x₁^N d̃A_n` is `Section3.idealI k N d̃`, `Q = A_n/𝓘`,
`M = gr Q` is `Section3.grQ k N d̃` (the same type as Section 4's `GrQ`), and
`Char(Q) = V(Ann_{k[x,ξ]} M)` is `Section2.Char`.  Lean indexes the
coordinates from `0`, so paper `n` is Lean `n + 1` and `x₁` is
`X (Sum.inl 0)`.
-/

namespace Stafford38.Paper.Section6

open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.Paper.Section2
open Stafford38.Paper.Section3

noncomputable section

universe u

variable {k : Type u} [Field k]

/-- The symbol `x₁ ∈ k[x, ξ]`. -/
abbrev x₁Symbol (k : Type u) [Field k] (n : ℕ) : SymbolRing k (n + 1) :=
  MvPolynomial.X (.inl (0 : Fin (n + 1)))

/-- `V(x₁) ⊆ Spec k[x, ξ]`, the primes containing `x₁`. -/
abbrev Vx₁ (k : Type u) [Field k] (n : ℕ) : Set (CotangentBundle k (n + 1)) :=
  V (Ideal.span {x₁Symbol k n})

/-- `M = gr Q` is finite over `k[x, ξ]` (it is cyclic, Proposition 3.6). -/
theorem step_6_1_finite {n N : ℕ} (dt : PresentedWeyl k (n + 1)) :
    Module.Finite (SymbolRing k (n + 1)) (grQ k N dt) :=
  (step_3_6_generated k dt).2.1

/-- Since `M` is finite, `Supp(M/x₁M) = Supp(M) ∩ V(x₁)` (Stacks 00L3). -/
theorem step_6_1_support_quotient {n N : ℕ} (dt : PresentedWeyl k (n + 1)) :
    Module.support (SymbolRing k (n + 1)) (QuotSMulTop (x₁Symbol k n) (grQ k N dt)) =
      Module.support (SymbolRing k (n + 1)) (grQ k N dt) ∩ Vx₁ k n := by
  have := step_6_1_finite (N := N) dt
  rw [Module.support_quotSMulTop, Vx₁, V, Ideal.span, PrimeSpectrum.zeroLocus_span]

/-- By Corollary 4.11, `M/x₁M = 0`, so `Supp(M) ∩ V(x₁) = ∅`. -/
theorem step_6_1_support_avoids [CharZero k] {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (hN : 0 < N) (hform : IsMonicNormalForm k N dt) :
    Module.support (SymbolRing k (n + 1)) (grQ k N dt) ∩ Vx₁ k n = ∅ := by
  have hU := Stafford38.Paper.Section4.corollary_4_11_quotSMulTop (k := k) hN
    (isPBWMonicAt_of_isMonicNormalForm k hform)
  rw [← step_6_1_support_quotient]
  exact Module.support_eq_empty

/-- Since `M` is finitely generated, `Char(Q) = V(Ann M) = Supp(M)`
(Stacks 00L2). -/
theorem step_6_1_char_eq_support {n N : ℕ} (dt : PresentedWeyl k (n + 1)) :
    Section2.Char k (idealI k N dt) = Module.support (SymbolRing k (n + 1)) (grQ k N dt) := by
  have := step_6_1_finite (N := N) dt
  rw [Section2.Char, Module.support_eq_zeroLocus]

/-- **Proposition 6.1.** `Char(Q) ∩ V(x₁) = ∅`, where `V(x₁) ⊆ Spec k[x, ξ]`
is the set of primes containing `x₁`. -/
theorem proposition_6_1 [CharZero k] {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (hN : 0 < N) (hform : IsMonicNormalForm k N dt) :
    Section2.Char k (idealI k N dt) ∩ Vx₁ k n = ∅ := by
  rw [step_6_1_char_eq_support]
  exact step_6_1_support_avoids hN hform

#print axioms step_6_1_finite
#print axioms step_6_1_support_quotient
#print axioms step_6_1_support_avoids
#print axioms step_6_1_char_eq_support
#print axioms proposition_6_1

end

end Stafford38.Paper.Section6
