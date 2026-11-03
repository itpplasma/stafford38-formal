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

/-- **Third paragraph.**  Every term of `w` has positive Euler degree, hence
`w = u₀ x₁` with `u₀ ∈ A_{≥0}`.  The input is that `Σ x₁^N` and `x₁^N Σ` lie in
`A_{≥0} x₁` (positive Euler degree of `Σ x₁^N` and `x₁^N Σ`, supplied for the
presented `d̃` by `step_4_2_presented_remainder`); `u(E), v(E)` have degree zero
and pass to the left of `x₁` by normality. -/
theorem step_4_2_positive (C : Subring A) (x p sigma : A) (N : ℕ)
    (hweyl : p * x = x * p + 1)
    (hcomm : ∀ c : C, x * (c : A) = (c : A) * x)
    (hscalar : ∀ q : ℚ, algebraMap ℚ A q ∈ C)
    (U V : A) (hU : U ∈ nonnegativePart C x p) (hV : V ∈ nonnegativePart C x p)
    (hright : sigma * x ^ N = U * x) (hleft : x ^ N * sigma = V * x)
    (u v : Polynomial ℚ) :
    ∃ u₀ ∈ nonnegativePart C x p,
      (sigma * x ^ N) * eulerPolynomialEval x p u +
        (x ^ N * sigma) * eulerPolynomialEval x p v = u₀ * x := by
  obtain ⟨su, hsu⟩ := coordinate_mul_eulerPolynomial C x p hweyl hcomm hscalar u
  obtain ⟨sv, hsv⟩ := coordinate_mul_eulerPolynomial C x p hweyl hcomm hscalar v
  refine ⟨U * su + V * sv,
    Subring.add_mem _ (Subring.mul_mem _ hU su.2) (Subring.mul_mem _ hV sv.2), ?_⟩
  rw [hright, hleft, mul_assoc, mul_assoc, hsu, hsv]
  noncomm_ring

/-- Lemma 4.2 for a Weyl pair, assembled from the three paragraphs, given the
identities of Lemma 4.1 for `m = N`. -/
theorem lemma_4_2_of_positive (C : Subring A) (x p d sigma : A) (N : ℕ)
    (hweyl : p * x = x * p + 1)
    (h41 : 1 ≤ N →
      x ^ N * p ^ N = ((List.range N).map fun i : ℕ => eulerElement x p - i).prod ∧
        p ^ N * x ^ N = ((List.range' 1 N).map fun i : ℕ => eulerElement x p + i).prod)
    (hcomm : ∀ c : C, x * (c : A) = (c : A) * x)
    (hscalar : ∀ q : ℚ, algebraMap ℚ A q ∈ C)
    (hd : d = p ^ N + sigma)
    (U V : A) (hU : U ∈ nonnegativePart C x p) (hV : V ∈ nonnegativePart C x p)
    (hright : sigma * x ^ N = U * x) (hleft : x ^ N * sigma = V * x) :
    ∃ u₀ ∈ nonnegativePart C x p, 1 + u₀ * x ∈ canonicalRightIdeal x d N := by
  obtain ⟨u, v, hbez⟩ := step_4_2_bezout x p N h41
  obtain ⟨-, hmem⟩ := step_4_2_residue x p d sigma N u v hd hbez
  obtain ⟨u₀, hu₀, hw⟩ :=
    step_4_2_positive C x p sigma N hweyl hcomm hscalar U V hU hV hright hleft u v
  exact ⟨u₀, hu₀, hw ▸ hmem⟩

end Generic

/-! ## The presented Weyl algebra -/

section Presented

universe u

variable (k : Type u) [Field k] [Algebra ℚ k] (n : ℕ)

/-- The transverse Weyl algebra `A_{n-1}` inside `A_n`. -/
abbrev transverse : Subring (PresentedWeyl k (n + 1)) :=
  (previousWeylEmbedding k n).range.toSubring

/-- `A_{≥0}` in the presented Weyl algebra: generated by `A_{n-1}`, `x₁` and
`E = x₁ ∂₁`. -/
abbrev presentedNonnegativePart : Subring (PresentedWeyl k (n + 1)) :=
  nonnegativePart (transverse k n) (presentedCoordinate k n) (presentedMomentum k n)

omit [Algebra ℚ k] in
/-- The transverse algebra commutes with `x₁` (Convention 2.2). -/
theorem transverse_commutes_coordinate (c : transverse k n) :
    presentedCoordinate k n * (c : PresentedWeyl k (n + 1)) =
      (c : PresentedWeyl k (n + 1)) * presentedCoordinate k n :=
  ((Stafford38.Paper.Section2.convention_2_2_relations k n).2.2 c c.2).1.symm

/-- The rational scalars of `A_n`, through `ℚ → k`. -/
abbrev presentedRatAlgebra : Algebra ℚ (PresentedWeyl k (n + 1)) :=
  Algebra.compHom _ (algebraMap ℚ k)

theorem rat_mem_transverse (q : ℚ) :
    @algebraMap ℚ _ _ _ (presentedRatAlgebra k n) q ∈ transverse k n := by
  refine ⟨algebraMap k (PresentedWeyl k n) (algebraMap ℚ k q), ?_⟩
  exact (previousWeylEmbedding k n).commutes _

omit [Algebra ℚ k] in
/-- The inverse of `A_n ≃ PairStage(A_{n-1})`, as a ring map. -/
abbrev fromIterated : PairStage (B := IteratedPairStage k n) →+* PresentedWeyl k (n + 1) :=
  (presentedIteratedEquiv k (n + 1)).symm.toRingEquiv.toRingHom

omit [Algebra ℚ k] in
theorem fromIterated_coordinate :
    fromIterated k n pairCoordinate = presentedCoordinate k n := by
  apply (presentedIteratedEquiv k (n + 1)).injective
  exact ((presentedIteratedEquiv k (n + 1)).apply_symm_apply _).trans
    (presentedToIterated_coordinate k n).symm

omit [Algebra ℚ k] in
theorem fromIterated_momentum :
    fromIterated k n pairMomentum = presentedMomentum k n := by
  apply (presentedIteratedEquiv k (n + 1)).injective
  exact ((presentedIteratedEquiv k (n + 1)).apply_symm_apply _).trans
    (presentedToIterated_momentum k n).symm

omit [Algebra ℚ k] in
theorem fromIterated_toIterated (d : PresentedWeyl k (n + 1)) :
    fromIterated k n (presentedToIterated k (n + 1) d) = d :=
  (presentedIteratedEquiv k (n + 1)).symm_apply_apply d

omit [Algebra ℚ k] in
/-- The Ore-tower transverse coefficients are the transverse algebra `A_{n-1}`. -/
theorem fromIterated_coefficient_mem_transverse (b : IteratedPairStage k n) :
    fromIterated k n (pairCoefficient b) ∈ transverse k n := by
  refine ⟨(presentedIteratedEquiv k n).symm b, ?_⟩
  change previousWeylEmbedding k n _ = fromIterated k n (pairCoefficient b)
  apply (presentedIteratedEquiv k (n + 1)).injective
  refine Eq.trans ?_ ((presentedIteratedEquiv k (n + 1)).apply_symm_apply _).symm
  have h := congrArg (fun g => g ((presentedIteratedEquiv k n).symm b))
    (presentedToIterated_previous k n)
  simp only [AlgHom.comp_apply] at h
  refine h.trans ?_
  change stageAlgHom k n (presentedIteratedEquiv k n
    ((presentedIteratedEquiv k n).symm b)) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

omit [Algebra ℚ k] in
/-- The equivalence `A_n ≃ PairStage(A_{n-1})` sends the Ore-tower Euler subring
into `A_{≥0}`. -/
theorem iterated_eulerSubring_le (z : PairStage (B := IteratedPairStage k n))
    (hz : z ∈ pairEulerSubring (IteratedPairStage k n)) :
    fromIterated k n z ∈ presentedNonnegativePart k n := by
  have hle : pairEulerSubring (IteratedPairStage k n) ≤
      (presentedNonnegativePart k n).comap (fromIterated k n) := by
    apply Subring.closure_le.2
    intro a ha
    rcases ha with ⟨b, rfl⟩ | ha
    · exact Subring.subset_closure (Or.inl (fromIterated_coefficient_mem_transverse k n b))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · rw [SetLike.mem_coe, Subring.mem_comap, fromIterated_coordinate]
        exact coordinate_mem_eulerSubring _ _ _
      · rw [SetLike.mem_coe, Subring.mem_comap, map_mul, fromIterated_coordinate,
          fromIterated_momentum]
        exact euler_mem_eulerSubring _ _ _
  exact hle hz

variable {k n}

set_option maxHeartbeats 2000000 in
/-- **Positivity of the remainder for `d̃`.**  For the normalized `d̃` with
`d̃ = p^N + Σ`, both `Σ x₁^N` and `x₁^N Σ` lie in `A_{≥0} x₁`.  The paper argues by
Euler degree of the terms `p^j x₁^l b` (`j < N`); Lean writes `Σ` in the PBW
basis of the Ore tower and factors each monomial `b x₁^a p^j` with `j < N`
(`presentedRemainder_hasPositiveCoordinateFactor`), then transports back. -/
theorem step_4_2_presented_remainder {N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    ∃ U ∈ presentedNonnegativePart k n, ∃ V ∈ presentedNonnegativePart k n,
      (d - presentedMomentum k n ^ N) * presentedCoordinate k n ^ N =
          U * presentedCoordinate k n ∧
        presentedCoordinate k n ^ N * (d - presentedMomentum k n ^ N) =
          V * presentedCoordinate k n := by
  obtain ⟨U, V, hU, hV⟩ := presentedRemainder_hasPositiveCoordinateFactor k n N hd
  obtain ⟨σ, hσdef⟩ : ∃ σ : PairStage (B := IteratedPairStage k n),
      σ = presentedToIterated k (n + 1) d - stageMomentum k n ^ N := ⟨_, rfl⟩
  have hU' : σ * pairCoordinate ^ N = (U : PairStage (B := IteratedPairStage k n)) *
      pairCoordinate := by rw [hσdef]; exact hU
  have hV' : pairCoordinate ^ N * σ = (V : PairStage (B := IteratedPairStage k n)) *
      pairCoordinate := by rw [hσdef]; exact hV
  have hσ : fromIterated k n σ = d - presentedMomentum k n ^ N := by
    rw [hσdef]
    change (presentedIteratedEquiv k (n + 1)).symm
      (presentedIteratedEquiv k (n + 1) d - stageMomentum k n ^ N) = _
    rw [map_sub, AlgEquiv.symm_apply_apply, map_pow]
    congr 2
    exact fromIterated_momentum k n
  refine ⟨fromIterated k n U, iterated_eulerSubring_le k n U U.2,
    fromIterated k n V, iterated_eulerSubring_le k n V V.2, ?_, ?_⟩
  · have h := congrArg (fromIterated k n) hU'
    rw [RingHom.map_mul (fromIterated k n) σ] at h
    rw [RingHom.map_mul (fromIterated k n) (U : PairStage (B := IteratedPairStage k n))] at h
    rw [RingHom.map_pow (fromIterated k n) pairCoordinate N] at h
    rw [hσ, fromIterated_coordinate] at h
    exact h
  · have h := congrArg (fromIterated k n) hV'
    rw [RingHom.map_mul (fromIterated k n) _ σ] at h
    rw [RingHom.map_mul (fromIterated k n) (V : PairStage (B := IteratedPairStage k n))] at h
    rw [RingHom.map_pow (fromIterated k n) pairCoordinate N] at h
    rw [hσ, fromIterated_coordinate] at h
    exact h

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
  obtain ⟨U, hU, V, hV, hright, hleft⟩ := step_4_2_presented_remainder hd
  exact lemma_4_2_of_positive (transverse k n) (presentedCoordinate k n)
    (presentedMomentum k n) d (d - presentedMomentum k n ^ N) N
    (Stafford38.Paper.Section2.convention_2_2_relations k n).1
    (fun hN => ⟨(lemma_4_1 k n N hN).1, (lemma_4_1 k n N hN).2.1⟩)
    (transverse_commutes_coordinate k n) (rat_mem_transverse k n) (by abel) U V hU hV hright hleft

end Presented

#print axioms step_4_2_coprime
#print axioms step_4_2_bezout
#print axioms step_4_2_residue
#print axioms step_4_2_positive
#print axioms lemma_4_2_of_positive
#print axioms step_4_2_presented_remainder
#print axioms lemma_4_2

end

end Stafford38.Paper.Section4
