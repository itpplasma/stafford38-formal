import Stafford38.Weyl.MonicNormalization

/-!
# The Weyl algebra has no zero divisors

The Bernstein principal component of a product is the product of the
principal components (`presentedPrincipalComponent_mul_bernstein`), and every
nonzero element has a nonzero principal component at its top Bernstein degree
(`exists_top_bernstein_piece`). The symbol ring is a polynomial ring over a
field, hence a domain, so a product of nonzero Weyl elements is nonzero.
-/

namespace Stafford38.WeylDomain

open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylMonicNormalization
open Stafford38.WeylPBW

universe u

variable (k : Type u) [Field k]

/-- A product of nonzero presented Weyl elements is nonzero. -/
theorem mul_ne_zero {n : ℕ} {x y : PresentedWeyl k n} (hx : x ≠ 0) (hy : y ≠ 0) :
    x * y ≠ 0 := by
  obtain ⟨N, hxN, hxP⟩ := exists_top_bernstein_piece k hx
  obtain ⟨M, hyM, hyP⟩ := exists_top_bernstein_piece k hy
  intro hxy
  have h := presentedPrincipalComponent_mul_bernstein k hxN hyM
  rw [hxy, map_zero] at h
  exact _root_.mul_ne_zero hxP hyP h.symm

instance instNontrivial (n : ℕ) : Nontrivial (PresentedWeyl k n) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h' := congrArg (presentedNormalFormLinearEquiv k n) h
  rw [presentedNormalFormLinearEquiv_one, map_zero] at h'
  exact one_ne_zero h'

instance instNoZeroDivisors (n : ℕ) : NoZeroDivisors (PresentedWeyl k n) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    by_contra hc
    rw [not_or] at hc
    exact mul_ne_zero k hc.1 hc.2 h

instance instIsDomain (n : ℕ) : IsDomain (PresentedWeyl k n) :=
  NoZeroDivisors.to_isDomain _

#print axioms mul_ne_zero

end Stafford38.WeylDomain
