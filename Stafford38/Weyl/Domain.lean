import Stafford38.Statement
import Stafford38.Weyl.MonicNormalization

/-!
# The presented Weyl algebra is a domain

The Bernstein principal component is multiplicative. A nonzero element has a
nonzero top Bernstein component, so the product of two nonzero elements cannot
vanish.
-/

namespace Stafford38.WeylDomain

open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylMonicNormalization

universe u

/-- The product of two nonzero elements of a Weyl algebra is nonzero. -/
theorem mul_ne_zero {k : Type u} [Field k] {n : ℕ}
    {a b : Stafford38.WeylAlg k n} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  obtain ⟨N, haN, hsa⟩ := exists_top_bernstein_piece k ha
  obtain ⟨M, hbM, hsb⟩ := exists_top_bernstein_piece k hb
  have htop := presentedPrincipalComponent_mul_bernstein k haN hbM
  have hsymbol :
      presentedPrincipalComponent k (@bernsteinWeight n) N a *
          presentedPrincipalComponent k (@bernsteinWeight n) M b ≠ 0 :=
    _root_.mul_ne_zero hsa hsb
  intro hab
  have hzero :
      presentedPrincipalComponent k (@bernsteinWeight n) (N + M) (a * b) = 0 := by
    simp [hab]
  rw [htop] at hzero
  exact hsymbol hzero

#print axioms mul_ne_zero

end Stafford38.WeylDomain
