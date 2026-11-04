module

public import Stafford38.Paper.Section4.Euler
public import Stafford38.Paper.Section2.Weyl
public import Stafford38.Paper.Section3.Transport

@[expose] public section

/-!
# Lemma 4.2: the Euler residue `1 + u₀ x₁ ∈ 𝓘`

The proof of Lemma 4.2 has three paragraphs: the Bezout identity for the
Euler products `R_±` of Lemma 4.1, the expansion `d̃ = p^N + Σ` giving
`1 + w ∈ 𝓘`, and the positivity `w ∈ A_{≥0} x₁`.  Each is a declaration below,
first for an arbitrary ring with a Weyl pair, then for the presented Weyl
algebra.
-/

namespace Stafford38.Paper.Section4

open Stafford
open Stafford38.EulerSurjectivity
open Stafford38.WeylEulerSubring
open Stafford38.WeylEulerResidue
open Stafford38.WeylEulerRemainder
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport
open Stafford38.OrePairStage
open Stafford38.OreIteratedPairStage

noncomputable section

section Generic

/-- Products over lists of pairwise coprime factors are coprime. -/
theorem isCoprime_list_prod {R : Type*} [CommRing R] (l₁ l₂ : List R)
    (h : ∀ a ∈ l₁, ∀ b ∈ l₂, IsCoprime a b) : IsCoprime l₁.prod l₂.prod := by
  induction l₁ with
  | nil => exact isCoprime_one_left
  | cons a l₁ ih =>
      rw [List.prod_cons]
      refine IsCoprime.mul_left ?_ (ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
      have ha := h a List.mem_cons_self
      clear ih h
      induction l₂ with
      | nil => exact isCoprime_one_right
      | cons b l₂ ih₂ =>
          rw [List.prod_cons]
          exact (ha b List.mem_cons_self).mul_right
            (ih₂ fun b' hb' => ha b' (List.mem_cons_of_mem _ hb'))

/-- `R_+(E) = ∏_{r=1}^N (E+r)` and `R_-(E) = ∏_{r=0}^{N-1}(E−r)` have the disjoint
root sets `{−1,…,−N}` and `{0,…,N−1}`, so `gcd(R_+, R_-) = 1` in `ℚ[E]`. -/
theorem step_4_2_coprime (N : ℕ) :
    IsCoprime
      ((List.range' 1 N).map fun r : ℕ => (Polynomial.X + Polynomial.C (r : ℚ))).prod
      ((List.range N).map fun r : ℕ => (Polynomial.X - Polynomial.C (r : ℚ))).prod := by
  apply isCoprime_list_prod
  intro a ha b hb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hb
  have hr1 : 1 ≤ r := (List.mem_range'_1.mp hr).1
  have hunit : IsUnit (-(r : ℚ) - s) := by
    apply isUnit_iff_ne_zero.mpr
    have : (1 : ℚ) ≤ r := by exact_mod_cast hr1
    have : (0 : ℚ) ≤ s := by positivity
    linarith
  have := Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit
  simpa [sub_eq_add_neg] using this

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Evaluating `R_±` at `E` gives the products of Lemma 4.1. -/
theorem step_4_2_eval_products (x p : A) (N : ℕ) :
    eulerPolynomialEval x p
        ((List.range' 1 N).map fun r : ℕ => (Polynomial.X + Polynomial.C (r : ℚ))).prod =
      ((List.range' 1 N).map fun i : ℕ => eulerElement x p + i).prod ∧
    eulerPolynomialEval x p
        ((List.range N).map fun r : ℕ => (Polynomial.X - Polynomial.C (r : ℚ))).prod =
      ((List.range N).map fun i : ℕ => eulerElement x p - i).prod := by
  constructor <;>
  · rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    simp [eulerElement]

/-- **First paragraph of the proof of Lemma 4.2.**  By Lemma 4.1 (the
hypothesis `h41`, the product identities for `m = N`) and the extended Euclidean
algorithm in `ℚ[E]` there are `u, v ∈ ℚ[E]` with
`p^N x₁^N u(E) + x₁^N p^N v(E) = 1`. -/
theorem step_4_2_bezout (x p : A) (N : ℕ)
    (h41 : 1 ≤ N →
      x ^ N * p ^ N = ((List.range N).map fun i : ℕ => eulerElement x p - i).prod ∧
        p ^ N * x ^ N = ((List.range' 1 N).map fun i : ℕ => eulerElement x p + i).prod) :
    ∃ u v : Polynomial ℚ,
      (p ^ N * x ^ N) * eulerPolynomialEval x p u +
        (x ^ N * p ^ N) * eulerPolynomialEval x p v = 1 := by
  obtain ⟨u, v, huv⟩ := step_4_2_coprime N
  refine ⟨u, v, ?_⟩
  rw [mul_comm u, mul_comm v] at huv
  have h := congrArg (eulerPolynomialEval x p) huv
  rw [map_add, map_mul, map_mul, map_one] at h
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa [add_comm] using h
  obtain ⟨hminus, hplus⟩ := h41 hN
  rw [(step_4_2_eval_products x p N).1, (step_4_2_eval_products x p N).2,
    ← hplus, ← hminus] at h
  exact h

/-- **Second paragraph.**  With `d̃ = p^N + Σ`,
`(d̃ x₁^N) u(E) + (x₁^N d̃) v(E) = 1 + w ∈ 𝓘`, where
`w = Σ x₁^N u(E) + x₁^N Σ v(E)` and `𝓘 = d̃A + x₁^N d̃A`. -/
theorem step_4_2_residue (x p d sigma : A) (N : ℕ) (u v : Polynomial ℚ)
    (hd : d = p ^ N + sigma)
    (hbezout : (p ^ N * x ^ N) * eulerPolynomialEval x p u +
        (x ^ N * p ^ N) * eulerPolynomialEval x p v = 1) :
    (d * x ^ N) * eulerPolynomialEval x p u + (x ^ N * d) * eulerPolynomialEval x p v =
        1 + ((sigma * x ^ N) * eulerPolynomialEval x p u +
          (x ^ N * sigma) * eulerPolynomialEval x p v) ∧
      1 + ((sigma * x ^ N) * eulerPolynomialEval x p u +
          (x ^ N * sigma) * eulerPolynomialEval x p v) ∈ canonicalRightIdeal x d N := by
  have hid := positiveEulerResidue_identity x p d sigma
    (eulerPolynomialEval x p u) (eulerPolynomialEval x p v) N hd hbezout
  rw [← mul_assoc] at hid
  refine ⟨hid, ?_⟩
  rw [← hid]
  refine (canonicalRightIdeal x d N).add_mem ?_ ?_
  · rw [mul_assoc]
    change MulOpposite.op (x ^ N * eulerPolynomialEval x p u) • d ∈
      canonicalRightIdeal x d N
    exact (canonicalRightIdeal x d N).smul_mem _ (firstGenerator_mem x d N)
  · change MulOpposite.op (eulerPolynomialEval x p v) • (x ^ N * d) ∈
      canonicalRightIdeal x d N
    exact (canonicalRightIdeal x d N).smul_mem _ (secondGenerator_mem x d N)

/-- `u(E)` and `v(E)` depend only on `E`, so they have Euler degree `0`. -/
theorem step_4_2_eulerPolynomial_degree_zero (x p : A) (f : Polynomial ℚ) :
    eulerPolynomialEval x p f ∈ eulerDegree x p 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      rw [map_add]
      exact add_mem hf hg
  | monomial l q =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, eulerPolynomialEval_C,
        eulerPolynomialEval_X]
      have hq : algebraMap ℚ A q ∈ eulerDegree x p 0 :=
        mem_eulerDegree_zero_of_commute (Algebra.commutes q x) (Algebra.commutes q p)
      simpa using eulerDegree_mul hq (eulerDegree_pow (euler_mem_eulerDegree x p) l)

/-- **Third paragraph.**  `Σ x₁^N` and `x₁^N Σ` have positive Euler degree
(`step_4_2_presented_remainder` for the presented `d̃`) and `u(E), v(E)` have
degree `0`, so every term of `w = Σ x₁^N u(E) + x₁^N Σ v(E)` has positive Euler
degree; hence `w ∈ A_{≥0} x₁` (the hypothesis `hpos`, which is
`step_positive_mem_nonnegative_mul_coordinate` for `A_n`). -/
theorem step_4_2_positive (x p sigma : A) (N : ℕ)
    (hright : sigma * x ^ N ∈ positivePart x p) (hleft : x ^ N * sigma ∈ positivePart x p)
    (hpos : ∀ z ∈ positivePart x p, ∃ u₀ ∈ nonnegativePart x p, z = u₀ * x)
    (u v : Polynomial ℚ) :
    ∃ u₀ ∈ nonnegativePart x p,
      (sigma * x ^ N) * eulerPolynomialEval x p u +
        (x ^ N * sigma) * eulerPolynomialEval x p v = u₀ * x :=
  hpos _ (add_mem
    (positivePart_mul_eulerDegree_zero hright (step_4_2_eulerPolynomial_degree_zero x p u))
    (positivePart_mul_eulerDegree_zero hleft (step_4_2_eulerPolynomial_degree_zero x p v)))

/-- Lemma 4.2 for a Weyl pair, assembled from the three paragraphs, given the
identities of Lemma 4.1 for `m = N`. -/
theorem lemma_4_2_of_positive (x p d sigma : A) (N : ℕ)
    (h41 : 1 ≤ N →
      x ^ N * p ^ N = ((List.range N).map fun i : ℕ => eulerElement x p - i).prod ∧
        p ^ N * x ^ N = ((List.range' 1 N).map fun i : ℕ => eulerElement x p + i).prod)
    (hd : d = p ^ N + sigma)
    (hright : sigma * x ^ N ∈ positivePart x p) (hleft : x ^ N * sigma ∈ positivePart x p)
    (hpos : ∀ z ∈ positivePart x p, ∃ u₀ ∈ nonnegativePart x p, z = u₀ * x) :
    ∃ u₀ ∈ nonnegativePart x p, 1 + u₀ * x ∈ canonicalRightIdeal x d N := by
  obtain ⟨u, v, hbez⟩ := step_4_2_bezout x p N h41
  obtain ⟨-, hmem⟩ := step_4_2_residue x p d sigma N u v hd hbez
  obtain ⟨u₀, hu₀, hw⟩ := step_4_2_positive x p sigma N hright hleft hpos u v
  exact ⟨u₀, hu₀, hw ▸ hmem⟩

end Generic

/-! ## The presented Weyl algebra -/

section Presented

universe u

variable (k : Type u) [Field k] [Algebra ℚ k] (n : ℕ)

variable {k n}

/-- **Positivity of the remainder for `d̃`.**  Write `Σ = d̃ − p^N` in PBW form:
a sum of terms `b x₁^a p^j` with `j < N` (`presentedRemainder_outer_support_lt`).
Such a term has Euler degree `a − j`, so multiplied by `x₁^N` on either side it has
Euler degree `a + N − j ≥ N − j > 0`.  Hence `Σ x₁^N` and `x₁^N Σ` have positive
Euler degree. -/
theorem step_4_2_presented_remainder {N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (d - presentedMomentum k n ^ N) * presentedCoordinate k n ^ N ∈
        presentedPositivePart k n ∧
      presentedCoordinate k n ^ N * (d - presentedMomentum k n ^ N) ∈
        presentedPositivePart k n := by
  have hxN := eulerDegree_pow (coordinate_mem_eulerDegree
    (pairMomentum_mul_coordinate (B := IteratedPairStage k n))) N
  have hpair := pairStage_pbw_induction (IteratedPairStage k n) (· < N)
    (fun z => z * pairCoordinate ^ N ∈ positivePart pairCoordinate pairMomentum ∧
      pairCoordinate ^ N * z ∈ positivePart pairCoordinate pairMomentum)
    ⟨by simp, by simp⟩
    (fun y z hy hz => ⟨by rw [add_mul]; exact add_mem hy.1 hz.1,
      by rw [mul_add]; exact add_mem hy.2 hz.2⟩)
    (fun b a j hj => by
      have hmono := pairMonomial_mem_eulerDegree (IteratedPairStage k n) b a j
      exact ⟨mem_positivePart_of_mem (by omega) (eulerDegree_mul hmono hxN),
        mem_positivePart_of_mem (by omega) (eulerDegree_mul hxN hmono)⟩)
    (presentedToIterated k (n + 1) d - stageMomentum k n ^ N)
    (presentedRemainder_outer_support_lt k n N hd)
  have hσ : fromIterated k n (presentedToIterated k (n + 1) d - stageMomentum k n ^ N) =
      d - presentedMomentum k n ^ N := by
    change (presentedIteratedEquiv k (n + 1)).symm
      (presentedIteratedEquiv k (n + 1) d - stageMomentum k n ^ N) = _
    rw [map_sub, AlgEquiv.symm_apply_apply, map_pow]
    congr 2
    exact fromIterated_momentum k n
  have hright := map_mem_positivePart (fromIterated k n) (fromIterated_coordinate k n)
    (fromIterated_momentum k n) hpair.1
  have hleft := map_mem_positivePart (fromIterated k n) (fromIterated_coordinate k n)
    (fromIterated_momentum k n) hpair.2
  rw [RingHom.map_mul (fromIterated k n)
      (presentedToIterated k (n + 1) d - stageMomentum k n ^ N),
    RingHom.map_pow (fromIterated k n) pairCoordinate N, hσ, fromIterated_coordinate] at hright
  rw [RingHom.map_mul (fromIterated k n) (pairCoordinate ^ N)
      (presentedToIterated k (n + 1) d - stageMomentum k n ^ N),
    RingHom.map_pow (fromIterated k n) pairCoordinate N, hσ, fromIterated_coordinate] at hleft
  exact ⟨hright, hleft⟩

/-- **Lemma 4.2.** For `d̃` in the form (3.1) and `𝓘 = d̃A_n + x₁^N d̃A_n`
(Equation (3.2)), there is `u₀ ∈ A_{≥0}` with `1 + u₀ x₁ ∈ 𝓘`.  The proof uses
(3.1) only through its consequence `IsPBWMonicAt`
(`Section3.isPBWMonicAt_of_isMonicNormalForm`), and cites Lemma 4.1 for `m = N`. -/
theorem lemma_4_2 {N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hform : Stafford38.Paper.Section3.IsMonicNormalForm k N d) :
    ∃ u₀ ∈ presentedNonnegativePart k n,
      1 + u₀ * presentedCoordinate k n ∈ Stafford38.Paper.Section3.idealI k N d := by
  let := presentedRatAlgebra k n
  have hd := Stafford38.Paper.Section3.isPBWMonicAt_of_isMonicNormalForm k hform
  obtain ⟨hright, hleft⟩ := step_4_2_presented_remainder hd
  exact lemma_4_2_of_positive (presentedCoordinate k n) (presentedMomentum k n) d
    (d - presentedMomentum k n ^ N) N
    (fun hN => ⟨(lemma_4_1 k n N hN).1, (lemma_4_1 k n N hN).2.1⟩)
    (by abel) hright hleft (step_positive_mem_nonnegative_mul_coordinate k n)

end Presented

#print axioms step_4_2_coprime
#print axioms step_4_2_bezout
#print axioms step_4_2_eulerPolynomial_degree_zero
#print axioms step_4_2_residue
#print axioms step_4_2_positive
#print axioms lemma_4_2_of_positive
#print axioms step_4_2_presented_remainder
#print axioms lemma_4_2

end

end Stafford38.Paper.Section4
