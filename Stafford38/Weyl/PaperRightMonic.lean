import Stafford38.Weyl.OuterOreMonic
import AlgebraicAnalysis.Ore.RightPBW

set_option maxHeartbeats 1000000

/-!
# Paper-facing right-coefficient monic normal form

This file connects the checked PBW monicity statement to the right-coefficient
normal form used in the paper.  In particular, coefficient bounds are proved
through the change from coefficient-left Ore form, rather than assumed.
-/

namespace Stafford38.WeylPaperRightMonic

open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreRightPBW
open AlgebraicAnalysis.OreRightQuotient
open Stafford38.Characteristic
open Stafford38.OreCoordinateStage
open Stafford38.OreIteratedPairStage
open Stafford38.OreLinearNormalForm
open Stafford38.OrePairStage
open Stafford38.OreScalarAlgebra
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylOuterOreMonic
open Stafford38.WeylPBW
open Stafford38.WeylPBWMonicBridge

universe u
variable {k : Type u} [Field k]

private theorem polynomialMapRangeLinearEquiv_derivative
    {R S : Type u} [Ring R] [CommRing S] [Algebra k R] [Algebra k S]
    (e : R ≃ₗ[k] S) (q : Polynomial R) :
    polynomialMapRangeLinearEquiv e q.derivative =
      (polynomialMapRangeLinearEquiv e q).derivative := by
  apply Polynomial.ext
  intro a
  calc
    _ = e ((q.derivative).coeff a) :=
      coeff_polynomialMapRangeLinearEquiv k e q.derivative a
    _ = e (q.coeff (a + 1) * (a + 1)) := by
      rw [Polynomial.coeff_derivative]
    _ = e (q.coeff (a + 1)) * (a + 1) := by
      calc
            _ = e ((a + 1) • q.coeff (a + 1)) := by
              rw [← Nat.cast_smul_eq_nsmul R (a + 1) (q.coeff (a + 1)), smul_eq_mul]
              congr 1
              simpa only [Nat.cast_succ] using
                (Nat.cast_commute (a + 1) (q.coeff (a + 1))).eq.symm
        _ = (a + 1) • e (q.coeff (a + 1)) := map_nsmul e _ _
        _ = _ := by
              rw [← Nat.cast_smul_eq_nsmul S (a + 1) (e (q.coeff (a + 1))), smul_eq_mul]
              simpa only [Nat.cast_succ] using
                (Nat.cast_commute (a + 1) (e (q.coeff (a + 1)))).eq
    _ = _ := by
      rw [Polynomial.coeff_derivative,
        coeff_polynomialMapRangeLinearEquiv k]

noncomputable section
variable (k : Type u) [Field k]

local instance (n : ℕ) : Algebra k (IteratedPairStage k n) :=
  iteratedPairStageAlgebra k n

local instance (n : ℕ) :
    Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
  coordinateStageAlgebra

local instance (n : ℕ) :
    Algebra k (PairStage (B := IteratedPairStage k n)) :=
  pairStageAlgebra

local instance (n : ℕ) :
    Nontrivial (IteratedPairStage k n) := by
  induction n with
  | zero =>
      change Nontrivial k
      infer_instance
  | succ n ih =>
      letI : Nontrivial (IteratedPairStage k n) := ih
      change Nontrivial (PairStage (B := IteratedPairStage k n))
      unfold PairStage CoordinateStage
      infer_instance

local instance (n : ℕ) :
    Nontrivial (CoordinateStage (B := IteratedPairStage k n)) := by
  unfold CoordinateStage
  infer_instance

/-- The coefficient ring of the newest momentum maps to the iterated pair
stage by the checked coefficient inclusion. -/
def coordinateStageToIterated (n : ℕ) :
    CoordinateStage (B := IteratedPairStage k n) →ₐ[k]
      IteratedPairStage k (n + 1) := by
  letI : Algebra k (IteratedPairStage k n) := iteratedPairStageAlgebra k n
  letI : Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateStageAlgebra
  letI : Algebra k (PairStage (B := IteratedPairStage k n)) := pairStageAlgebra
  exact
    { toRingHom := normalCoefficient coordinateDerivation
      commutes' := by
        intro c
        rfl }

theorem coordinateStageToIterated_injective (n : ℕ) :
    Function.Injective (coordinateStageToIterated k n) := by
  intro x y h
  exact normalCoefficient_injective coordinateDerivation h

/-- The coefficient ring embeds into the presented Weyl algebra through the
checked iterated-Ore/presented equivalence. -/
def coordinateStageToPresented (n : ℕ) :
    CoordinateStage (B := IteratedPairStage k n) →ₐ[k]
      PresentedWeyl k (n + 1) :=
  (iteratedToPresented k (n + 1)).comp (coordinateStageToIterated k n)

theorem coordinateStageToPresented_normalForm (n : ℕ)
    (z : CoordinateStage (B := IteratedPairStage k n)) :
    presentedNormalFormLinearEquiv k (n + 1)
        (coordinateStageToPresented k n z) =
      flattenPairSymbols k n
        (Polynomial.C (coordinateCoefficientNormalForm k n z)) := by
  have hpair :
      iteratedNormalFormLinearEquiv k (n + 1)
          (coordinateStageToIterated k n z) =
        flattenPairSymbols k n
          (Polynomial.C (coordinateCoefficientNormalForm k n z)) := by
    rw [iteratedNormalFormLinearEquiv]
    let hInner : algebraMap k (CoordinateStage (B := IteratedPairStage k n)) =
        (normalCoefficient zeroDerivation).comp
          (algebraMap k (IteratedPairStage k n)) :=
      normalOreAlgebra_algebraMap zeroDerivation (fun c => by
        exact zeroDerivation_apply (algebraMap k (IteratedPairStage k n) c))
    let hOuter : algebraMap k (PairStage (B := IteratedPairStage k n)) =
        (normalCoefficient coordinateDerivation).comp
          (algebraMap k (CoordinateStage (B := IteratedPairStage k n))) :=
      normalOreAlgebra_algebraMap coordinateDerivation
        (coordinateDerivation_algebraMap (B := IteratedPairStage k n))
    change flattenPairSymbols k n
        (pairNormalFormLinearEquiv hInner hOuter
          (iteratedNormalFormLinearEquiv k n)
          (normalCoefficient (coordinateDerivation
            (B := IteratedPairStage k n)) z)) = _
    simp [pairNormalFormLinearEquiv, coordinateCoefficientNormalForm,
      normalFormLinearEquiv_symm_coefficient]
    rfl
  simp only [presentedNormalFormLinearEquiv, LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply, coordinateStageToPresented,
    presentedIteratedEquiv, AlgHom.comp_apply]
  change iteratedNormalFormLinearEquiv k (n + 1)
    (presentedToIterated k (n + 1)
      (iteratedToPresented k (n + 1) (coordinateStageToIterated k n z))) = _
  rw [← AlgHom.comp_apply,
    presentedToIterated_comp_iteratedToPresented k (n + 1)]
  exact hpair

/-- The coefficient ring of the newest momentum inherits the canonical
rank-`n+1` Bernstein filtration along its checked Weyl-algebra inclusion. -/
def coordinateBernsteinPiece (n L : ℕ) :
    Submodule k (CoordinateStage (B := IteratedPairStage k n)) :=
  (Stafford38.WeylFiltration.bernsteinPiece k (n + 1) L).comap
    (coordinateStageToPresented k n).toLinearMap

@[simp] theorem mem_coordinateBernsteinPiece (n L : ℕ)
    (z : CoordinateStage (B := IteratedPairStage k n)) :
    z ∈ coordinateBernsteinPiece k n L ↔
      ∀ a m,
        MvPolynomial.coeff m
          ((coordinateCoefficientNormalForm k n z).coeff a) ≠ 0 →
          a + monomialWeight (@bernsteinWeight n) m ≤ L := by
  change coordinateStageToPresented k n z ∈
    Stafford38.WeylFiltration.bernsteinPiece k (n + 1) L ↔ _
  rw [Stafford38.WeylFiltration.bernsteinPiece, mem_presentedWeightPiece,
    coordinateStageToPresented_normalForm]
  constructor
  · intro h a m hm
    have hnonzero : MvPolynomial.coeff (pairExponent n a 0 m)
        (flattenPairSymbols k n
          (Polynomial.C (coordinateCoefficientNormalForm k n z))) ≠ 0 := by
      rw [coeff_flattenPairSymbols]
      simpa [Polynomial.coeff_C] using hm
    have hbound := h (pairExponent n a 0 m) hnonzero
    have hweight : monomialWeight (@bernsteinWeight (n + 1))
        (pairExponent n a 0 m) =
          monomialWeight (@bernsteinWeight n) m + a := by
      simpa [pairExponent, extendPhaseExponent, add_comm, add_left_comm,
        add_assoc] using
          (monomialWeight_extend_bernstein n a 0 m).symm
    omega
  · intro h q hq
    let aq : Fin (n + 1) → ℕ := fun i => q (.inl i)
    let pq : Fin (n + 1) → ℕ := fun i => q (.inr i)
    let old : PhaseVar n →₀ ℕ :=
      phaseExponent (fun i => aq i.succ) (fun i => pq i.succ)
    have hqsplit : q = pairExponent n (aq 0) (pq 0) old := by
      have hphase : phaseExponent aq pq = q := by
        ext i <;> cases i <;> simp [phaseExponent, aq, pq]
      rw [← hphase, phaseExponent_succ]
      rfl
    have hpzero : pq 0 = 0 := by
      by_contra hp
      have hz : MvPolynomial.coeff q
          (flattenPairSymbols k n
            (Polynomial.C (coordinateCoefficientNormalForm k n z))) = 0 := by
        rw [hqsplit, coeff_flattenPairSymbols]
        simp [Polynomial.coeff_C, hp]
      exact hq hz
    have hsource : MvPolynomial.coeff old
        ((coordinateCoefficientNormalForm k n z).coeff (aq 0)) ≠ 0 := by
      have := hq
      rw [hqsplit, coeff_flattenPairSymbols] at this
      simpa [Polynomial.coeff_C, hpzero] using this
    have hbound := h (aq 0) old hsource
    have hweight : monomialWeight (@bernsteinWeight (n + 1)) q =
        monomialWeight (@bernsteinWeight n) old + aq 0 := by
      rw [hqsplit]
      simpa [pairExponent, extendPhaseExponent, hpzero, add_comm,
        add_left_comm, add_assoc] using
          (monomialWeight_extend_bernstein n (aq 0) 0 old).symm
    omega

theorem coordinateBernsteinPiece_mono (n L M : ℕ) (hLM : L ≤ M)
    {z : CoordinateStage (B := IteratedPairStage k n)}
    (hz : z ∈ coordinateBernsteinPiece k n L) :
    z ∈ coordinateBernsteinPiece k n M := by
  rw [mem_coordinateBernsteinPiece] at hz ⊢
  intro a m hm
  exact (hz a m hm).trans hLM

theorem coordinateCoefficientNormalForm_derivative (n : ℕ)
    (z : CoordinateStage (B := IteratedPairStage k n)) :
    coordinateCoefficientNormalForm k n (coordinateDerivation z) =
      (coordinateCoefficientNormalForm k n z).derivative := by
  let D : OreDivisionDerivation (IteratedPairStage k n) := zeroDerivation
  let hAlg : algebraMap k (NormalOre D) =
      (normalCoefficient D).comp (algebraMap k (IteratedPairStage k n)) :=
    normalOreAlgebra_algebraMap D (fun c => by
      exact zeroDerivation_apply (algebraMap k (IteratedPairStage k n) c))
  change (polynomialMapRangeLinearEquiv
      (iteratedNormalFormLinearEquiv k n))
      ((normalFormLinearEquiv D hAlg).symm
        (normalForm D (Polynomial.derivative
          ((normalFormAddEquiv D).symm z)))) = _
  have hsymm : (normalFormLinearEquiv D hAlg).symm z =
      (normalFormAddEquiv D).symm z := rfl
  rw [normalFormLinearEquiv_symm_normalForm]
  rw [← hsymm]
  change (polynomialMapRangeLinearEquiv
      (iteratedNormalFormLinearEquiv k n))
      (Polynomial.derivative ((normalFormLinearEquiv D hAlg).symm z)) =
    (polynomialMapRangeLinearEquiv
      (iteratedNormalFormLinearEquiv k n)
        ((normalFormLinearEquiv D hAlg).symm z)).derivative
  exact (polynomialMapRangeLinearEquiv_derivative
    (k := k) (iteratedNormalFormLinearEquiv k n)
      ((normalFormLinearEquiv D hAlg).symm z))

theorem coordinateDerivation_mem_coordinateBernsteinPiece {n L : ℕ}
    {z : CoordinateStage (B := IteratedPairStage k n)}
    (hz : z ∈ coordinateBernsteinPiece k n L) :
    coordinateDerivation z ∈ coordinateBernsteinPiece k n L := by
  rw [mem_coordinateBernsteinPiece] at hz
  rw [mem_coordinateBernsteinPiece, coordinateCoefficientNormalForm_derivative]
  intro a m hm
  have hsource : MvPolynomial.coeff m
      ((coordinateCoefficientNormalForm k n z).coeff (a + 1)) ≠ 0 := by
    intro hzero
    apply hm
    rw [Polynomial.coeff_derivative]
    have hcast : ((coordinateCoefficientNormalForm k n z).coeff (a + 1)) *
        (↑(a + 1) : SymbolRing k n) = (a + 1 : k) •
          ((coordinateCoefficientNormalForm k n z).coeff (a + 1)) := by
      rw [mul_comm, Algebra.smul_def]
      congr 1
      simp
    rw [← Nat.cast_succ, hcast, MvPolynomial.coeff_smul, hzero]
    simp
  have hbound := hz (a + 1) m hsource
  simp only [monomialWeight, bernsteinWeight] at hbound ⊢
  omega

theorem coordinateDerivation_iterate_mem_coordinateBernsteinPiece
    {n L r : ℕ} {z : CoordinateStage (B := IteratedPairStage k n)}
    (hz : z ∈ coordinateBernsteinPiece k n L) :
    (coordinateDerivation^[r]) z ∈ coordinateBernsteinPiece k n L := by
  induction r with
  | zero => simpa using hz
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact coordinateDerivation_mem_coordinateBernsteinPiece (k := k) ih

theorem presentedOuterCoefficient_mem_coordinateBernsteinPiece
    (n N p : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : d ∈ bernsteinPiece k (n + 1) N) :
    (presentedOuterPolynomial k n d).coeff p ∈
      coordinateBernsteinPiece k n (N - p) := by
  rw [mem_coordinateBernsteinPiece]
  intro a m hm
  have hnested : MvPolynomial.coeff m
      (((presentedNestedNormalForm k n d).coeff p).coeff a) ≠ 0 := by
    simpa only [presentedNestedNormalForm_coeff] using hm
  have hfull : MvPolynomial.coeff (pairExponent n a p m)
      (presentedNormalFormLinearEquiv k (n + 1) d) ≠ 0 := by
    rw [← flatten_presentedNestedNormalForm k n d,
      coeff_flattenPairSymbols]
    exact hnested
  have htotal : monomialWeight (@bernsteinWeight (n + 1))
      (pairExponent n a p m) ≤ N := by
    exact (mem_presentedWeightPiece k (@bernsteinWeight (n + 1)) N d).mp
      (by simpa [bernsteinPiece] using hd) _ hfull
  have hweight : monomialWeight (@bernsteinWeight n) m + a + p ≤ N := by
    have hEq : monomialWeight (@bernsteinWeight (n + 1))
          (pairExponent n a p m) =
        monomialWeight (@bernsteinWeight n) m + a + p := by
      simpa [pairExponent, extendPhaseExponent, add_comm, add_left_comm,
        add_assoc] using
        (monomialWeight_extend_bernstein n a p m).symm
    rw [hEq] at htotal
    exact htotal
  omega

def rightBernsteinBound (n N : ℕ)
    (c : ℕ →₀ (CoordinateStage (B := IteratedPairStage k n))ᵐᵒᵖ) : Prop :=
  ∀ j, MulOpposite.unop (c j) ∈ coordinateBernsteinPiece k n (N - j)

theorem rightBernsteinBound_zero (n N : ℕ) :
    rightBernsteinBound k n N 0 := by
  intro j
  exact (coordinateBernsteinPiece k n (N - j)).zero_mem

theorem rightBernsteinBound_add (n N : ℕ)
    {c d : ℕ →₀ (CoordinateStage (B := IteratedPairStage k n))ᵐᵒᵖ}
    (hc : rightBernsteinBound k n N c)
    (hd : rightBernsteinBound k n N d) :
    rightBernsteinBound k n N (c + d) := by
  intro j
  change MulOpposite.unop (c j + d j) ∈ _
  rw [MulOpposite.unop_add]
  exact (coordinateBernsteinPiece k n (N - j)).add_mem (hc j) (hd j)

theorem rightBernsteinBound_nsmul (n N r : ℕ)
    {c : ℕ →₀ (CoordinateStage (B := IteratedPairStage k n))ᵐᵒᵖ}
    (hc : rightBernsteinBound k n N c) :
    rightBernsteinBound k n N (r • c) := by
  intro j
  change MulOpposite.unop (r • c j) ∈ _
  induction r with
  | zero => simp
  | succ r ih =>
      rw [succ_nsmul, MulOpposite.unop_add]
      exact (coordinateBernsteinPiece k n (N - j)).add_mem ih (hc j)

theorem rightBernsteinBound_neg (n N : ℕ)
    {c : ℕ →₀ (CoordinateStage (B := IteratedPairStage k n))ᵐᵒᵖ}
    (hc : rightBernsteinBound k n N c) :
    rightBernsteinBound k n N (-c) := by
  intro j
  change MulOpposite.unop (-c j) ∈ _
  rw [MulOpposite.unop_neg]
  exact (coordinateBernsteinPiece k n (N - j)).neg_mem (hc j)

theorem rightBernsteinBound_single (n N j : ℕ)
    {b : (CoordinateStage (B := IteratedPairStage k n))ᵐᵒᵖ}
    (hb : MulOpposite.unop b ∈ coordinateBernsteinPiece k n (N - j)) :
    rightBernsteinBound k n N (Finsupp.single j b) := by
  intro q
  by_cases hq : q = j
  · subst q
    simpa using hb
  · simp [Finsupp.single_apply, hq]

private theorem rightBernsteinBound_sum (n N : ℕ) {α : Type*}
    (s : Finset α)
    (f : α → ℕ →₀ (CoordinateStage (B := IteratedPairStage k n))ᵐᵒᵖ)
    (hf : ∀ a ∈ s, rightBernsteinBound k n N (f a)) :
    rightBernsteinBound k n N (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using rightBernsteinBound_zero k n N
  | @insert a s has ih =>
      rw [Finset.sum_insert has]
      apply rightBernsteinBound_add k n N
      · exact hf a (Finset.mem_insert_self a s)
      · apply ih
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb)

private theorem rightPBWBasis_repr_single
    {B : Type*} [Ring B] [Nontrivial B]
    (D : OreDivisionDerivation B) (j : ℕ) (b : B) :
    (rightOrePBWBasis D).repr
        (MulOpposite.op b • rightPBWMonomial D j) =
      Finsupp.single j (MulOpposite.op b) := by
  rw [← rightOrePBWBasis_repr_symm_single D j (MulOpposite.op b)]
  exact LinearEquiv.apply_symm_apply _ _

private theorem rightPBWBasis_repr_monomial
    {B : Type*} [Ring B] [Nontrivial B]
    (D : OreDivisionDerivation B) (l : ℕ) (b : B) :
    (rightOrePBWBasis D).repr (normalForm D (Polynomial.monomial l b)) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal l,
        l.choose ij.1 •
          (if Even ij.1 then Finsupp.single ij.2 (MulOpposite.op
              ((D^[ij.1]) b))
          else -Finsupp.single ij.2 (MulOpposite.op
              ((D^[ij.1]) b))) := by
  rw [normalForm_monomial_reverse]
  simp only [map_sum, map_nsmul]
  apply Finset.sum_congr rfl
  intro ij hij
  by_cases he : Even ij.1
  · rw [he.neg_one_pow, one_mul]
    change l.choose ij.1 •
      (rightOrePBWBasis D).repr
        (MulOpposite.op ((D^[ij.1]) b) • rightPBWMonomial D ij.2) = _
    rw [rightPBWBasis_repr_single, if_pos he]
  · have ho : Odd ij.1 := Nat.not_even_iff_odd.mp he
    rw [ho.neg_one_pow, neg_one_mul, map_neg]
    change l.choose ij.1 • -((rightOrePBWBasis D).repr
      (MulOpposite.op ((D^[ij.1]) b) • rightPBWMonomial D ij.2)) = _
    rw [rightPBWBasis_repr_single, if_neg he]

private theorem rightPBWBasis_repr_monomial_coeff_top
    {B : Type*} [Ring B] [Nontrivial B]
    (D : OreDivisionDerivation B) (l : ℕ) (b : B) :
    ((rightOrePBWBasis D).repr
      (normalForm D (Polynomial.monomial l b))) l = MulOpposite.op b := by
  rw [rightPBWBasis_repr_monomial]
  have hmem : (0, l) ∈ Finset.HasAntidiagonal.antidiagonal l := by
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single (0, l)]
  · simp [Nat.choose_zero_right]
  · intro ij hij hne
    have hadd := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hsecond : ij.2 ≠ l := by
      intro h
      apply hne
      apply Prod.ext
      · omega
      · exact h
    by_cases he : Even ij.1
    · simp [he, hsecond]
    · simp [he, hsecond]
  · intro hnot
    exact (hnot hmem).elim

private theorem rightPBWBasis_repr_monomial_coeff_zero_of_lt
    {B : Type*} [Ring B] [Nontrivial B]
    (D : OreDivisionDerivation B) (l j : ℕ) (b : B) (hlj : l < j) :
    ((rightOrePBWBasis D).repr
      (normalForm D (Polynomial.monomial l b))) j = 0 := by
  rw [rightPBWBasis_repr_monomial, Finset.sum_apply']
  apply Finset.sum_eq_zero
  intro ij hij
  have hadd : ij.1 + ij.2 = l :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hsecond : ij.2 ≠ j := by
    intro h
    subst j
    omega
  by_cases he : Even ij.1
  · rw [if_pos he]
    rw [Finsupp.smul_single]
    simp [Finsupp.single_apply, hsecond]
  · rw [if_neg he]
    simp only [smul_neg]
    rw [Finsupp.smul_single]
    simp [Finsupp.single_apply, hsecond]

private theorem pairRightBasis_repr_monomial_bound (n N l : ℕ)
    (b : CoordinateStage (B := IteratedPairStage k n))
    (hl : l ≤ N)
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
  rw [rightPBWBasis_repr_monomial]
  apply rightBernsteinBound_sum k n N
  intro ij hij
  have hadd : ij.1 + ij.2 = l :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hderiv : (((coordinateDerivation :
      OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)))^[ij.1]) b) ∈
      coordinateBernsteinPiece k n (N - ij.2) := by
    apply coordinateBernsteinPiece_mono k n (N - l) (N - ij.2) (by omega)
    exact coordinateDerivation_iterate_mem_coordinateBernsteinPiece k hb
  have hsingle : rightBernsteinBound k n N
      (Finsupp.single ij.2 (MulOpposite.op
        (((coordinateDerivation :
          OreDivisionDerivation (CoordinateStage
            (B := IteratedPairStage k n)))^[ij.1]) b))) := by
    apply rightBernsteinBound_single k n N ij.2
    simpa using hderiv
  have hsign : rightBernsteinBound k n N
      (if Even ij.1 then Finsupp.single ij.2 (MulOpposite.op
          (((coordinateDerivation :
            OreDivisionDerivation (CoordinateStage
              (B := IteratedPairStage k n)))^[ij.1]) b))
       else -Finsupp.single ij.2 (MulOpposite.op
          (((coordinateDerivation :
            OreDivisionDerivation (CoordinateStage
              (B := IteratedPairStage k n)))^[ij.1]) b))) := by
    split_ifs with he
    · exact hsingle
    · exact rightBernsteinBound_neg k n N hsingle
  exact rightBernsteinBound_nsmul k n N (Nat.choose l ij.1) hsign

theorem presentedOuterRightBernsteinBound (n N : ℕ)
    (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    rightBernsteinBound k n N
      ((pairStage_rightOrePBWBasis (B := IteratedPairStage k n)).repr
        (presentedToIterated k (n + 1) d)) := by
  let H := presentedOuterPolynomial k n d
  let D : OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateDerivation
  have hnormal : normalForm D H = presentedToIterated k (n + 1) d := by
    dsimp [D, H, presentedOuterPolynomial]
    exact (normalFormAddEquiv coordinateDerivation).apply_symm_apply _
  rw [← hnormal]
  change rightBernsteinBound k n N
    ((rightOrePBWBasis D).repr (normalForm D H))
  have hsum : H = ∑ l ∈ H.support, Polynomial.monomial l (H.coeff l) := by
    simpa [Polynomial.sum_def] using (Polynomial.sum_monomial_eq H).symm
  rw [hsum]
  have hrepr :
      (rightOrePBWBasis D).repr
          (normalForm D (∑ l ∈ H.support, Polynomial.monomial l (H.coeff l))) =
        ∑ l ∈ H.support,
          (rightOrePBWBasis D).repr (normalForm D (Polynomial.monomial l (H.coeff l))) := by
    change (rightOrePBWBasis D).repr
        ((normalFormAddEquiv D)
          (∑ l ∈ H.support, Polynomial.monomial l (H.coeff l))) = _
    rw [map_sum]
    rw [map_sum]
    rfl
  rw [hrepr]
  apply rightBernsteinBound_sum k n N
  intro l hl
  have hcoeff : H.coeff l ≠ 0 := (Polynomial.mem_support_iff.mp hl)
  have hlN : l ≤ N := by
    by_contra h
    have hzero := outer_coeff_eq_zero_of_exponent_gt k n N hd (by omega : N < l)
    exact hcoeff (by simpa [H] using hzero)
  exact pairRightBasis_repr_monomial_bound k n N l (H.coeff l) hlN
    (presentedOuterCoefficient_mem_coordinateBernsteinPiece k n N l d hd.1)

/-- Right-momentum coefficients above the outer monic degree vanish. -/
theorem presentedOuterRightBasis_coeff_zero_of_gt (n N p : ℕ)
    (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) (hp : N < p) :
    ((pairStage_rightOrePBWBasis (B := IteratedPairStage k n)).repr
      (presentedToIterated k (n + 1) d)) p = 0 := by
  let D : OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateDerivation
  let H := presentedOuterPolynomial k n d
  have hnormal : normalForm D H = presentedToIterated k (n + 1) d := by
    dsimp [D, H, presentedOuterPolynomial]
    exact (normalFormAddEquiv coordinateDerivation).apply_symm_apply _
  rw [← hnormal]
  change ((rightOrePBWBasis D).repr (normalForm D H)) p = 0
  have hsum : H = ∑ l ∈ H.support, Polynomial.monomial l (H.coeff l) := by
    simpa [Polynomial.sum_def] using (Polynomial.sum_monomial_eq H).symm
  rw [hsum]
  have hrepr :
      (rightOrePBWBasis D).repr
          (normalForm D (∑ l ∈ H.support, Polynomial.monomial l (H.coeff l))) =
        ∑ l ∈ H.support,
          (rightOrePBWBasis D).repr (normalForm D (Polynomial.monomial l (H.coeff l))) := by
    change (rightOrePBWBasis D).repr
        ((normalFormAddEquiv D)
          (∑ l ∈ H.support, Polynomial.monomial l (H.coeff l))) = _
    rw [map_sum]
    rw [map_sum]
    rfl
  rw [hrepr, Finset.sum_apply']
  apply Finset.sum_eq_zero
  intro l hl
  have hlN : l ≤ N := by
    by_contra h
    have hzero := outer_coeff_eq_zero_of_exponent_gt k n N hd (by omega : N < l)
    exact (Polynomial.mem_support_iff.mp hl) (by simpa [H] using hzero)
  exact rightPBWBasis_repr_monomial_coeff_zero_of_lt D l p (H.coeff l)
    (lt_of_le_of_lt hlN hp)

/-- The coefficient at the outer degree is exactly one in right PBW normal form. -/
theorem presentedOuterRightBasis_coeff_at_bound (n N : ℕ)
    (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    ((pairStage_rightOrePBWBasis (B := IteratedPairStage k n)).repr
      (presentedToIterated k (n + 1) d)) N = MulOpposite.op (1 : CoordinateStage
        (B := IteratedPairStage k n)) := by
  let D : OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateDerivation
  let H := presentedOuterPolynomial k n d
  have hnormal : normalForm D H = presentedToIterated k (n + 1) d := by
    dsimp [D, H, presentedOuterPolynomial]
    exact (normalFormAddEquiv coordinateDerivation).apply_symm_apply _
  rw [← hnormal]
  change ((rightOrePBWBasis D).repr (normalForm D H)) N =
    MulOpposite.op (1 : CoordinateStage (B := IteratedPairStage k n))
  have hNcoeff : H.coeff N = 1 := by
    dsimp [H]
    exact outer_coeff_eq_one_at_bound k n N hd
  have hNmem : N ∈ H.support := by
    rw [Polynomial.mem_support_iff, hNcoeff]
    exact one_ne_zero
  have hsum : H = ∑ l ∈ H.support, Polynomial.monomial l (H.coeff l) := by
    simpa [Polynomial.sum_def] using (Polynomial.sum_monomial_eq H).symm
  rw [hsum]
  have hrepr :
      (rightOrePBWBasis D).repr
          (normalForm D (∑ l ∈ H.support, Polynomial.monomial l (H.coeff l))) =
        ∑ l ∈ H.support,
          (rightOrePBWBasis D).repr (normalForm D (Polynomial.monomial l (H.coeff l))) := by
    change (rightOrePBWBasis D).repr
        ((normalFormAddEquiv D)
          (∑ l ∈ H.support, Polynomial.monomial l (H.coeff l))) = _
    rw [map_sum]
    rw [map_sum]
    rfl
  rw [hrepr, Finset.sum_apply']
  rw [Finset.sum_eq_single N]
  · rw [rightPBWBasis_repr_monomial_coeff_top, hNcoeff]
  · intro l hl hne
    have hlN : l ≤ N := by
      by_contra h
      have hzero := outer_coeff_eq_zero_of_exponent_gt k n N hd (by omega : N < l)
      exact (Polynomial.mem_support_iff.mp hl) (by simpa [H] using hzero)
    have hlt : l < N := by omega
    exact rightPBWBasis_repr_monomial_coeff_zero_of_lt D l N (H.coeff l) hlt
  · intro hnot
    exact (hnot hNmem).elim

/-- The PBW monic normal form with right coefficients, including the degree
bound on every lower coefficient. -/
theorem presentedOuter_right_monic_decomposition (n N : ℕ)
    (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    ∃ a : ℕ → CoordinateStage (B := IteratedPairStage k n),
      (∀ j, j < N → a j ∈ coordinateBernsteinPiece k n (N - j)) ∧
      presentedToIterated k (n + 1) d =
        rightPBWMonomial (coordinateDerivation :
          OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n))) N +
        ∑ j ∈ Finset.range N,
          MulOpposite.op (a j) • rightPBWMonomial (coordinateDerivation :
            OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n))) j := by
  let D : OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateDerivation
  let b := pairStage_rightOrePBWBasis (B := IteratedPairStage k n)
  let c := b.repr (normalForm D (presentedOuterPolynomial k n d))
  have hnormal : normalForm D (presentedOuterPolynomial k n d) =
      presentedToIterated k (n + 1) d := by
    dsimp [D, presentedOuterPolynomial]
    exact (normalFormAddEquiv coordinateDerivation).apply_symm_apply _
  have hcTop : c N = MulOpposite.op (1 : CoordinateStage
      (B := IteratedPairStage k n)) := by
    simpa [c, b, D, hnormal, pairStage_rightOrePBWBasis] using
      presentedOuterRightBasis_coeff_at_bound k n N d hd
  have hcAbove (j : ℕ) (hNj : N < j) : c j = 0 := by
    simpa [c, b, D, hnormal, pairStage_rightOrePBWBasis] using
      presentedOuterRightBasis_coeff_zero_of_gt k n N j d hd hNj
  have heraseSupport : (Finsupp.erase N c).support ⊆ Finset.range N := by
    intro j hj
    rw [Finsupp.support_erase, Finset.mem_erase] at hj
    rcases hj with ⟨hne, hmem⟩
    have hcnz : c j ≠ 0 := Finsupp.mem_support_iff.mp hmem
    have hjN : j < N := by
      by_contra hjN
      have hNj : N < j := by omega
      exact hcnz (hcAbove j hNj)
    exact Finset.mem_range.mpr hjN
  have heraseSum :
      Finsupp.sum (Finsupp.erase N c) (fun j a => a • b j) =
        ∑ j ∈ Finset.range N, (Finsupp.erase N c) j • b j := by
    exact Finsupp.sum_of_support_subset (Finsupp.erase N c) heraseSupport
      (fun j a => a • b j) (by intro j hj; simp)
  have hdecomp : b.repr.symm c = c N • b N +
      ∑ j ∈ Finset.range N, c j • b j := by
    have hsingle : (Finsupp.linearCombination
        (MulOpposite (CoordinateStage (B := IteratedPairStage k n))) b
        (Finsupp.single N (c N))) = c N • b N := by
      rw [Finsupp.linearCombination_apply]
      exact Finsupp.sum_single_index (by simp)
    calc
      b.repr.symm c = Finsupp.linearCombination
          (MulOpposite (CoordinateStage (B := IteratedPairStage k n))) b c :=
            b.repr_symm_apply c
      _ = Finsupp.linearCombination
          (MulOpposite (CoordinateStage (B := IteratedPairStage k n))) b
          (Finsupp.single N (c N) + Finsupp.erase N c) := by
            rw [Finsupp.single_add_erase]
      _ = _ := by
            rw [map_add]
            rw [hsingle]
            rw [Finsupp.linearCombination_apply]
            rw [heraseSum]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finsupp.erase_apply]
            have hjlt : j < N := Finset.mem_range.mp hj
            have hjne : j ≠ N := by omega
            simp [hjne]
  have hback : presentedToIterated k (n + 1) d = b.repr.symm c := by
    dsimp [c]
    rw [← hnormal]
    exact (b.repr.symm_apply_apply _).symm
  have hbasis (j : ℕ) : b j = rightPBWMonomial D j := by
    simp [b, D, pairStage_rightOrePBWBasis]
  have hdecomp' : b.repr.symm c = c N • rightPBWMonomial D N +
      ∑ j ∈ Finset.range N, c j • rightPBWMonomial D j := by
    calc
      b.repr.symm c = c N • b N + ∑ j ∈ Finset.range N, c j • b j := hdecomp
      _ = c N • rightPBWMonomial D N +
          ∑ j ∈ Finset.range N, c j • rightPBWMonomial D j := by
            rw [hbasis N]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [hbasis j]
  let a : ℕ → CoordinateStage (B := IteratedPairStage k n) :=
    fun j => MulOpposite.unop (c j)
  refine ⟨a, ?_, ?_⟩
  · intro j hj
    dsimp [a]
    simpa [c, b, D, hnormal, pairStage_rightOrePBWBasis] using
      (presentedOuterRightBernsteinBound k n N d hd) j
  · rw [hback, hdecomp', hcTop]
    simp [a, D] <;> rfl

end

end Stafford38.WeylPaperRightMonic
