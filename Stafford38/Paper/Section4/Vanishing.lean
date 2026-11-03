module

public import Stafford38.Paper.Section4.PageInequality
public import Stafford38.Paper.Section4.StrictInequality

@[expose] public section

/-!
# Corollary 4.11: `U = M/x₁M = 0`, i.e. `gr Q = (gr Q) x₁`
-/

namespace Stafford38.Paper.Section4

open scoped Pointwise
open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

variable {k : Type*} [Field k] [CharZero k] [Algebra ℚ k] {n N : ℕ}
  {d : PresentedWeyl k (n + 1)}

attribute [local instance] Characteristic.CanonicalKoszulContradiction.gradedModule
  Characteristic.CanonicalKoszulContradiction.coefficientAlgebra
  Characteristic.CanonicalKoszulContradiction.coefficientTower

/-- **Proof of Corollary 4.11.**  If `U ≠ 0` it has a minimal support prime `𝔮`;
Lemma 4.8 makes the lengths finite, and Lemmas 4.9 and 4.10 contradict one
another.  Hence `U = M/x₁M = 0`. -/
theorem step_4_11_cokernel_zero (hN : 0 < N)
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Subsingleton (cokernelU k n N d) := by
  obtain ⟨hU, -, -, -⟩ := lemma_4_8 hd
  by_contra h
  have : Nontrivial (cokernelU k n N d) := not_subsingleton_iff_nontrivial.mp h
  obtain ⟨q, hqmem, hqmin⟩ :=
    AlgebraicAnalysis.MinimalSupportExistence.exists_minimal_support_prime
      (R := Tangential k n) (U := cokernelU k n N d)
  exact not_lt_of_ge (lemma_4_9 hd q hqmem hqmin) (lemma_4_10 hN hd q hqmem hqmin)

/-- **Corollary 4.11.** Multiplication by `x₁` on `gr Q` is surjective, i.e.
`gr Q = (gr Q) x₁`. -/
theorem corollary_4_11 (hN : 0 < N) (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Function.Surjective (fun z : GrQ k n N d => symbolCoordinate k n • z) := by
  have hU := step_4_11_cokernel_zero hN hd
  have htop : LinearMap.range (coordinateMap k n N d) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hU
  intro z
  obtain ⟨w, hw⟩ := LinearMap.range_eq_top.mp htop z
  exact ⟨w, (setup_coordinateMap_apply k n N d w).symm.trans hw⟩

/-- Corollary 4.11 in the form `M/x₁M = 0` over `k[x,ξ]` (`QuotSMulTop`), as
consumed by the support-avoidance argument of Section 6. -/
theorem corollary_4_11_quotSMulTop (hN : 0 < N)
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Subsingleton (QuotSMulTop (symbolCoordinate k n) (GrQ k n N d)) := by
  have hsurj := corollary_4_11 hN hd
  change Subsingleton (GrQ k n N d ⧸ symbolCoordinate k n • (⊤ : Submodule (Symbol k n) _))
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro z _
  obtain ⟨w, rfl⟩ := hsurj z
  exact Submodule.smul_mem_pointwise_smul w _ ⊤ trivial

#print axioms step_4_11_cokernel_zero
#print axioms corollary_4_11
#print axioms corollary_4_11_quotSMulTop

end

end Stafford38.Paper.Section4
