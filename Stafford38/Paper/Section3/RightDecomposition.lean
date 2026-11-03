module

public import Stafford38.Paper.Section2.Filtration

@[expose] public section

/-!
# The decomposition `d = ∑_j p^j a_j` is compatible with `B_•`

Proof of Proposition 3.2, paragraph 5, first sentences: in the normal form
`A_n(k) = ⊕_j p^j C` of Convention 2.2, an element `d ∈ B_N` has
`d = ∑_{j ≤ N} p^j a_j` with `a_j ∈ C` and `deg_B a_j ≤ N - j`.

The bounds are read through the coefficient-left normal form of the iterated
Ore presentation and its change to right coefficients.  The argument is that of
`WeylPaperRightMonic.presentedOuterRightBernsteinBound`, which is stated only
for PBW-monic elements although it uses only `d ∈ B_N`; its private helpers are
repeated here with that weaker hypothesis.
-/

namespace Stafford38.Paper.Section3

open AlgebraicAnalysis
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreRightPBW
open AlgebraicAnalysis.OreRightQuotient
open Stafford38.Characteristic
open Stafford38.OreCoordinateStage
open Stafford38.OreIteratedPairStage
open Stafford38.OrePairStage
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylOuterOreMonic
open Stafford38.WeylPaperRightMonic
open Stafford38.WeylPBW
open Stafford38.WeylPBWMonicBridge
open Stafford38.Paper.Section2

noncomputable section

universe u

variable (k : Type u) [Field k]

local instance (n : ℕ) : Algebra k (IteratedPairStage k n) :=
  iteratedPairStageAlgebra k n

local instance (n : ℕ) :
    Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
  coordinateStageAlgebra

local instance (n : ℕ) :
    Algebra k (PairStage (B := IteratedPairStage k n)) :=
  pairStageAlgebra

local instance (n : ℕ) : Nontrivial (IteratedPairStage k n) := by
  induction n with
  | zero =>
      change Nontrivial k
      infer_instance
  | succ n ih =>
      have : Nontrivial (IteratedPairStage k n) := ih
      change Nontrivial (PairStage (B := IteratedPairStage k n))
      unfold PairStage CoordinateStage
      infer_instance

local instance (n : ℕ) : Nontrivial (CoordinateStage (B := IteratedPairStage k n)) := by
  unfold CoordinateStage
  infer_instance

private theorem outer_coeff_zero_of_mem (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : d ∈ bernsteinPiece k (n + 1) N) {q : ℕ} (hq : N < q) :
    (presentedOuterPolynomial k n d).coeff q = 0 := by
  have h : (presentedNestedNormalForm k n d).coeff q = 0 := by
    ext a m
    simp only [Polynomial.coeff_zero]
    change AddMonoidAlgebra.coeff (((presentedNestedNormalForm k n d).coeff q).coeff a) m = 0
    rw [← coeff_flattenPairSymbols k n a q m, flatten_presentedNestedNormalForm]
    exact coeff_normalForm_eq_zero_of_exponent_gt k
      (t := .inr (0 : Fin (n + 1))) (m := pairExponent n a q m) hd (by simpa using hq)
  rw [presentedNestedNormalForm_coeff] at h
  apply (coordinateCoefficientNormalForm k n).injective
  exact h.trans (LinearMap.map_zero (coordinateCoefficientNormalForm k n).toLinearMap).symm

private theorem rightBernsteinBound_sum' (n N : ℕ) {α : Type*} (s : Finset α)
    (f : α → ℕ →₀ (CoordinateStage (B := IteratedPairStage k n))ᵐᵒᵖ)
    (hf : ∀ a ∈ s, rightBernsteinBound k n N (f a)) :
    rightBernsteinBound k n N (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rightBernsteinBound_zero k n N
  | @insert a s has ih =>
      rw [Finset.sum_insert has]
      exact rightBernsteinBound_add k n N (hf a (Finset.mem_insert_self a s))
        (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

private theorem rightPBWBasis_repr_single' {B : Type*} [Ring B] [Nontrivial B]
    (D : OreDivisionDerivation B) (j : ℕ) (b : B) :
    (rightOrePBWBasis D).repr (MulOpposite.op b • rightPBWMonomial D j) =
      Finsupp.single j (MulOpposite.op b) := by
  rw [← rightOrePBWBasis_repr_symm_single D j (MulOpposite.op b)]
  exact LinearEquiv.apply_symm_apply _ _

private theorem rightPBWBasis_repr_monomial' {B : Type*} [Ring B] [Nontrivial B]
    (D : OreDivisionDerivation B) (l : ℕ) (b : B) :
    (rightOrePBWBasis D).repr (normalForm D (Polynomial.monomial l b)) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal l,
        l.choose ij.1 •
          (if Even ij.1 then Finsupp.single ij.2 (MulOpposite.op ((D^[ij.1]) b))
          else -Finsupp.single ij.2 (MulOpposite.op ((D^[ij.1]) b))) := by
  rw [normalForm_monomial_reverse]
  simp only [map_sum, map_nsmul]
  apply Finset.sum_congr rfl
  intro ij _
  by_cases he : Even ij.1
  · rw [he.neg_one_pow, one_mul]
    change l.choose ij.1 •
      (rightOrePBWBasis D).repr
        (MulOpposite.op ((D^[ij.1]) b) • rightPBWMonomial D ij.2) = _
    rw [rightPBWBasis_repr_single', ite_eq_left he]
  · have ho : Odd ij.1 := Nat.not_even_iff_odd.mp he
    rw [ho.neg_one_pow, neg_one_mul, map_neg]
    change l.choose ij.1 • -((rightOrePBWBasis D).repr
      (MulOpposite.op ((D^[ij.1]) b) • rightPBWMonomial D ij.2)) = _
    rw [rightPBWBasis_repr_single', ite_eq_right he]

private theorem rightPBWBasis_repr_monomial_coeff_zero_of_lt' {B : Type*} [Ring B]
    [Nontrivial B] (D : OreDivisionDerivation B) (l j : ℕ) (b : B) (hlj : l < j) :
    ((rightOrePBWBasis D).repr (normalForm D (Polynomial.monomial l b))) j = 0 := by
  rw [rightPBWBasis_repr_monomial', Finset.sum_apply']
  apply Finset.sum_eq_zero
  intro ij hij
  have hadd : ij.1 + ij.2 = l := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hsecond : ij.2 ≠ j := by omega
  by_cases he : Even ij.1
  · rw [ite_eq_left he, Finsupp.smul_single]
    simp [hsecond]
  · rw [ite_eq_right he]
    simp only [smul_neg]
    rw [Finsupp.smul_single]
    simp [hsecond]

private theorem pairRightBasis_repr_monomial_bound' (n N l : ℕ)
    (b : CoordinateStage (B := IteratedPairStage k n)) (hl : l ≤ N)
    (hb : b ∈ coordinateBernsteinPiece k n (N - l)) :
    rightBernsteinBound k n N
      ((pairStage_rightOrePBWBasis (B := IteratedPairStage k n)).repr
        (normalForm (coordinateDerivation :
          OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)))
          (Polynomial.monomial l b))) := by
  change rightBernsteinBound k n N
    ((rightOrePBWBasis (coordinateDerivation :
      OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)))).repr
      (normalForm (coordinateDerivation :
        OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)))
        (Polynomial.monomial l b)))
  rw [rightPBWBasis_repr_monomial']
  apply rightBernsteinBound_sum' k n N
  intro ij hij
  have hadd : ij.1 + ij.2 = l := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hderiv : (((coordinateDerivation :
      OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)))^[ij.1]) b) ∈
      coordinateBernsteinPiece k n (N - ij.2) :=
    coordinateBernsteinPiece_mono k n (N - l) (N - ij.2) (by omega)
      (coordinateDerivation_iterate_mem_coordinateBernsteinPiece k hb)
  have hsingle := rightBernsteinBound_single k n N ij.2 (b := MulOpposite.op
    (((coordinateDerivation :
      OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)))^[ij.1]) b))
    (by simpa using hderiv)
  have hsign : rightBernsteinBound k n N
      (if Even ij.1 then Finsupp.single ij.2 (MulOpposite.op
          (((coordinateDerivation :
            OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)))^[ij.1]) b))
       else -Finsupp.single ij.2 (MulOpposite.op
          (((coordinateDerivation :
            OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)))^[ij.1]) b))) := by
    split_ifs
    · exact hsingle
    · exact rightBernsteinBound_neg k n N hsingle
  exact rightBernsteinBound_nsmul k n N (Nat.choose l ij.1) hsign

/-- Right coefficients of `d ∈ B_N`: their Bernstein bounds and their vanishing
above `N`. -/
private theorem right_repr_bounds (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : d ∈ bernsteinPiece k (n + 1) N) :
    rightBernsteinBound k n N
        ((pairStage_rightOrePBWBasis (B := IteratedPairStage k n)).repr
          (presentedToIterated k (n + 1) d)) ∧
      ∀ q, N < q → ((pairStage_rightOrePBWBasis (B := IteratedPairStage k n)).repr
          (presentedToIterated k (n + 1) d)) q = 0 := by
  let H := presentedOuterPolynomial k n d
  let D : OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateDerivation
  have hnormal : normalForm D H = presentedToIterated k (n + 1) d := by
    dsimp [D, H, presentedOuterPolynomial]
    exact (normalFormAddEquiv coordinateDerivation).apply_symm_apply _
  have hsum : H = ∑ l ∈ H.support, Polynomial.monomial l (H.coeff l) := by
    simpa [Polynomial.sum_def] using (Polynomial.sum_monomial_eq H).symm
  have hrepr : (rightOrePBWBasis D).repr (normalForm D H) =
      ∑ l ∈ H.support, (rightOrePBWBasis D).repr
        (normalForm D (Polynomial.monomial l (H.coeff l))) := by
    conv_lhs => rw [hsum]
    change (rightOrePBWBasis D).repr
        ((normalFormAddEquiv D) (∑ l ∈ H.support, Polynomial.monomial l (H.coeff l))) = _
    rw [map_sum, map_sum]
    rfl
  have hlN : ∀ l ∈ H.support, l ≤ N := by
    intro l hl
    by_contra h
    exact (Polynomial.mem_support_iff.mp hl) (outer_coeff_zero_of_mem k n N hd (by omega))
  rw [← hnormal]
  refine ⟨?_, fun q hq => ?_⟩
  · change rightBernsteinBound k n N ((rightOrePBWBasis D).repr (normalForm D H))
    rw [hrepr]
    apply rightBernsteinBound_sum' k n N
    intro l hl
    exact pairRightBasis_repr_monomial_bound' k n N l (H.coeff l) (hlN l hl)
      (presentedOuterCoefficient_mem_coordinateBernsteinPiece k n N l d hd)
  · change ((rightOrePBWBasis D).repr (normalForm D H)) q = 0
    rw [hrepr, Finset.sum_apply']
    exact Finset.sum_eq_zero fun l hl =>
      rightPBWBasis_repr_monomial_coeff_zero_of_lt' D l q (H.coeff l)
        (lt_of_le_of_lt (hlN l hl) hq)

/-- The PBW coefficients of `d ∈ B_N` in `A_n(k) = ⊕_j p^j C` satisfy
`deg_B a_j ≤ N - j`. -/
theorem step_bounded_coefficients (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : d ∈ bernsteinPiece k (n + 1) N) :
    ∃ a : ℕ → PresentedWeyl k (n + 1),
      (∀ j, a j ∈ C k n ∧ bernsteinDegree k (a j) ≤ N - j) ∧
        d = ∑ j ∈ Finset.range (N + 1), p k n ^ j * a j := by
  let b := pairStage_rightOrePBWBasis (B := IteratedPairStage k n)
  let c := b.repr (presentedToIterated k (n + 1) d)
  obtain ⟨hbound, hzero⟩ := right_repr_bounds k n N hd
  have hsub : c.support ⊆ Finset.range (N + 1) := by
    intro j hj
    by_contra h
    exact (Finsupp.mem_support_iff.mp hj) (hzero j (by simp at h; omega))
  refine ⟨fun j => coordinateStageToPresented k n (c j).unop, fun j => ⟨?_, ?_⟩, ?_⟩
  · rw [C_eq_range]
    exact ⟨_, rfl⟩
  · rw [bernsteinDegree_le_iff]
    exact hbound j
  · have hd' : presentedToIterated k (n + 1) d =
        ∑ j ∈ Finset.range (N + 1), c j • rightPBWMonomial (coordinateDerivation :
          OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n))) j := by
      conv_lhs => rw [← b.linearCombination_repr (presentedToIterated k (n + 1) d)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hsub _ (by simp)]
      apply Finset.sum_congr rfl
      intro j _
      simp [b, pairStage_rightOrePBWBasis]
      rfl
    have hback : d = stageToPresented k n (presentedToIterated k (n + 1) d) :=
      (DFunLike.congr_fun (iteratedToPresented_comp_presentedToIterated k (n + 1)) d).symm
    rw [hback, hd', map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact stageToPresented_rightTerm k n j (c j).unop


omit [Field k] in
theorem sum_range_pad {R : Type*} [Ring R] (x : R) (a : ℕ → R) {L M : ℕ} (h : L ≤ M) :
    ∑ j ∈ Finset.range M, x ^ j * (if j < L then a j else 0) =
      ∑ j ∈ Finset.range L, x ^ j * a j := by
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono h)
  · intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hj
    simp [not_lt.mpr hj.2]
  · intro j hj
    simp [Finset.mem_range.mp hj]

/-- **Proposition 3.2, paragraph 5 (the decomposition).** Using
`A_n(k) = ⊕_j p^j C` (Convention 2.2: existence and uniqueness of the normal
form), `d ∈ B_N` is `d = ∑_{j=0}^N p^j a_j` with `a_j ∈ C`; the Bernstein
filtration is compatible with the decomposition, so `deg_B a_j ≤ N - j`. -/
theorem exists_bounded_decomposition (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : d ∈ bernsteinPiece k (n + 1) N) :
    ∃ a : ℕ → PresentedWeyl k (n + 1),
      (∀ j, a j ∈ C k n ∧ bernsteinDegree k (a j) ≤ N - j) ∧
        d = ∑ j ∈ Finset.range (N + 1), p k n ^ j * a j := by
  -- The normal form of Convention 2.2.
  obtain ⟨L, a, haC, hda⟩ := convention_2_2_exists k n d
  -- Its coefficients are those bounded by the Bernstein filtration.
  obtain ⟨b, hb, hdb⟩ := step_bounded_coefficients k n N hd
  let M := max L (N + 1)
  let a' : ℕ → PresentedWeyl k (n + 1) := fun j => if j < L then a j else 0
  let b' : ℕ → PresentedWeyl k (n + 1) := fun j => if j < N + 1 then b j else 0
  have ha'C : ∀ j, a' j ∈ C k n := fun j => by
    by_cases hj : j < L
    · simp only [a', hj, ↓reduceIte]; exact haC j
    · simp only [a', hj, ↓reduceIte]; exact Subalgebra.zero_mem _
  have hb'C : ∀ j, b' j ∈ C k n := fun j => by
    by_cases hj : j < N + 1
    · simp only [b', hj, ↓reduceIte]; exact (hb j).1
    · simp only [b', hj, ↓reduceIte]; exact Subalgebra.zero_mem _
  have hsum : ∑ j ∈ Finset.range M, p k n ^ j * (a' j - b' j) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [sum_range_pad _ a (le_max_left L (N + 1)), sum_range_pad _ b (le_max_right L (N + 1)),
      ← hda, ← hdb, sub_self]
  have huniq := convention_2_2_unique k n M (fun j => a' j - b' j)
    (fun j => Subalgebra.sub_mem _ (ha'C j) (hb'C j)) hsum
  have hab : ∀ j, a' j = b' j := fun j => by
    by_cases hj : j < M
    · exact sub_eq_zero.mp (huniq j hj)
    · have h1 : ¬ j < L := fun h => hj (lt_of_lt_of_le h (le_max_left _ _))
      have h2 : ¬ j < N + 1 := fun h => hj (lt_of_lt_of_le h (le_max_right _ _))
      simp only [a', b', h1, h2, ↓reduceIte]
  refine ⟨a', fun j => ⟨ha'C j, ?_⟩, ?_⟩
  · rw [hab j]
    by_cases hj : j < N + 1
    · simp only [b', hj, ↓reduceIte]; exact (hb j).2
    · simp only [b', hj, ↓reduceIte]
      exact (bernsteinDegree_le_iff k 0).mpr (Submodule.zero_mem _)
  · rw [hdb]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hab j]
    simp only [b', Finset.mem_range.mp hj, ↓reduceIte]

#print axioms exists_bounded_decomposition

end

end Stafford38.Paper.Section3
