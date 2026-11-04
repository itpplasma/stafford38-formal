module

public import Stafford38.Weyl.QuotientTransport
public import Stafford38.Weyl.EulerRemainder
public import Stafford38.Weyl.EulerSubring
public import Stafford38.Weyl.PaperEulerGrading
public import Stafford38.Paper.Section2.Weyl
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

/-!
# Section 4, first part: the Euler grading, Lemmas 4.1, 4.2 and Proposition 4.3

`E = x₁ p` with `p = ∂₁`.  The paragraph before Lemma 4.1 introduces the
Euler grading, the nonnegative part `A_{≥0}` and the normality of `x₁` in it.
Lemma 4.1 computes `x₁^m p^m` and `p^m x₁^m` as products of Euler factors,
Lemma 4.2 produces `1 + u₀ x₁ ∈ 𝓘`, and Proposition 4.3 proves `Q = Q x₁`.

The ring-theoretic paragraphs are stated for an arbitrary ring `A` with
`p x₁ = x₁ p + 1`; the paper's statements are their specializations to the
presented Weyl algebra `A_n = PresentedWeyl k (n+1)` (Lean indexes the
coordinates from `0`, so the paper's `x₁` is `presentedCoordinate k n` and the
transverse algebra `A_{n-1}` is the image of `previousWeylEmbedding k n`), the
normalized element `d̃` (`IsPBWMonicAt … N d`) and the right ideal
`𝓘 = d̃ A_n + x₁^N d̃ A_n` (`presentedCanonicalRightIdeal n N d`).

The Euler grading is defined as in the paper, by the eigenspaces of the
commutator with `E` (`eulerDegree`), and `A_{≥0}` is its nonnegative part
(`nonnegativePart`).  The PBW description of `A_{≥0}` and the statement that
elements of Euler degree `≥ 1` lie in `A_{≥0} x₁` need the PBW basis and are
proved for `A_n` through one Ore pair stage `A_n ≃ PairStage(A_{n-1})`.
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

/-! ## The Euler grading paragraph (tex 523–543) -/

section Grading

variable {A : Type*} [Ring A]

/-- The Euler element `E = x₁ p`. -/
abbrev eulerElement (x p : A) : A := x * p

/-- The commutator `[E, ·]` with `E = x₁ p`, an additive endomorphism of `A`. -/
def eulerCommutator (x p : A) : Module.End ℤ A :=
  LinearMap.mulLeft ℤ (eulerElement x p) - LinearMap.mulRight ℤ (eulerElement x p)

/-- The part of Euler degree `m` of the grading defined by the commutator of `E`:
the elements `z` with `[E, z] = m z`. -/
def eulerDegree (x p : A) (m : ℤ) : Submodule ℤ A :=
  Module.End.eigenspace (eulerCommutator x p) m

theorem mem_eulerDegree {x p z : A} {m : ℤ} :
    z ∈ eulerDegree x p m ↔ eulerElement x p * z - z * eulerElement x p = m • z := by
  rw [eulerDegree, Module.End.mem_eigenspace_iff]
  rfl

/-- The grading is multiplicative: `[E, ·]` is a derivation. -/
theorem eulerDegree_mul {x p y z : A} {m m' : ℤ} (hy : y ∈ eulerDegree x p m)
    (hz : z ∈ eulerDegree x p m') : y * z ∈ eulerDegree x p (m + m') := by
  rw [mem_eulerDegree] at hy hz ⊢
  calc eulerElement x p * (y * z) - y * z * eulerElement x p
      = (eulerElement x p * y - y * eulerElement x p) * z +
          y * (eulerElement x p * z - z * eulerElement x p) := by noncomm_ring
    _ = (m + m') • (y * z) := by rw [hy, hz, smul_mul_assoc, mul_smul_comm, add_smul]

theorem eulerDegree_pow {x p z : A} {m : ℤ} (hz : z ∈ eulerDegree x p m) :
    ∀ l : ℕ, z ^ l ∈ eulerDegree x p (l * m)
  | 0 => by rw [pow_zero, mem_eulerDegree]; simp
  | l + 1 => by
      rw [pow_succ]
      convert eulerDegree_mul (eulerDegree_pow hz l) hz using 2
      push_cast
      ring

/-- Elements commuting with `x₁` and `p` have Euler degree `0`. -/
theorem mem_eulerDegree_zero_of_commute {x p c : A} (hx : c * x = x * c)
    (hp : c * p = p * c) : c ∈ eulerDegree x p 0 := by
  rw [mem_eulerDegree, zero_smul, sub_eq_zero, eulerElement, mul_assoc, ← hp, ← mul_assoc,
    ← hx, mul_assoc]

/-- `x₁` has Euler degree `1`. -/
theorem coordinate_mem_eulerDegree {x p : A} (hweyl : p * x = x * p + 1) :
    x ∈ eulerDegree x p 1 := by
  rw [mem_eulerDegree, eulerElement, mul_assoc, hweyl]
  noncomm_ring

/-- `E` has Euler degree `0`. -/
theorem euler_mem_eulerDegree (x p : A) : eulerElement x p ∈ eulerDegree x p 0 := by
  rw [mem_eulerDegree]
  simp

/-- `A_{≥0}`, the nonnegative part of `A` in the Euler grading: the sum of the
parts of Euler degree `m ≥ 0`.  It is a subring because the grading is
multiplicative. -/
def nonnegativePart (x p : A) : Subring A :=
  { (⨆ m : ℕ, eulerDegree x p m).toAddSubgroup with
    one_mem' := Submodule.mem_iSup_of_mem 0 (by
      rw [mem_eulerDegree]; simp)
    mul_mem' := by
      intro a b ha hb
      change a * b ∈ ⨆ m : ℕ, eulerDegree x p m
      refine Submodule.iSup_induction _ (motive := fun a => a * b ∈ ⨆ m : ℕ, eulerDegree x p m)
        ha (fun m a ha => ?_) (by simp) (fun a a' h h' => by rw [add_mul]; exact add_mem h h')
      refine Submodule.iSup_induction _ (motive := fun b => a * b ∈ ⨆ m : ℕ, eulerDegree x p m)
        hb (fun m' b hb => ?_) (by simp) (fun b b' h h' => by rw [mul_add]; exact add_mem h h')
      exact Submodule.mem_iSup_of_mem (m + m')
        (by simpa only [Nat.cast_add] using eulerDegree_mul ha hb) }

theorem mem_nonnegativePart {x p z : A} :
    z ∈ nonnegativePart x p ↔ z ∈ ⨆ m : ℕ, eulerDegree x p m := Iff.rfl

/-- The elements of Euler degree `≥ 1`: the sum of the parts of degree `m ≥ 1`. -/
def positivePart (x p : A) : Submodule ℤ A :=
  ⨆ m : ℕ, eulerDegree x p (m + 1 : ℕ)

theorem mem_positivePart_of_mem {x p z : A} {m : ℤ} (hm : 1 ≤ m)
    (hz : z ∈ eulerDegree x p m) : z ∈ positivePart x p := by
  obtain ⟨l, rfl⟩ : ∃ l : ℕ, m = (l + 1 : ℕ) := ⟨m.toNat - 1, by omega⟩
  exact Submodule.mem_iSup_of_mem l hz

/-- Multiplying an element of degree `≥ 1` by one of degree `0` keeps degree `≥ 1`. -/
theorem positivePart_mul_eulerDegree_zero {x p z y : A} (hz : z ∈ positivePart x p)
    (hy : y ∈ eulerDegree x p 0) : z * y ∈ positivePart x p := by
  refine Submodule.iSup_induction _ (motive := fun z => z * y ∈ positivePart x p) hz
    (fun m z hz => ?_) (by simp) (fun z z' h h' => by rw [add_mul]; exact add_mem h h')
  exact Submodule.mem_iSup_of_mem m (by simpa only [add_zero] using eulerDegree_mul hz hy)

/-- `x₁` and `E` lie in `A_{≥0}`. -/
theorem coordinate_mem_nonnegativePart {x p : A} (hweyl : p * x = x * p + 1) :
    x ∈ nonnegativePart x p :=
  Submodule.mem_iSup_of_mem 1 (by simpa using coordinate_mem_eulerDegree hweyl)

theorem euler_mem_nonnegativePart (x p : A) : eulerElement x p ∈ nonnegativePart x p :=
  Submodule.mem_iSup_of_mem 0 (by simpa using euler_mem_eulerDegree x p)

/-- The transverse algebra `C`, `E` and `x₁` lie in `A_{≥0}`, hence so does the
subring they generate. -/
theorem eulerSubring_le_nonnegativePart (C : Subring A) (x p : A)
    (hweyl : p * x = x * p + 1)
    (hcomm : ∀ c ∈ C, c * x = x * c ∧ c * p = p * c) :
    eulerSubring C x p ≤ nonnegativePart x p := by
  apply Subring.closure_le.2
  rintro a (ha | ha)
  · exact Submodule.mem_iSup_of_mem 0
      (by simpa using mem_eulerDegree_zero_of_commute (hcomm a ha).1 (hcomm a ha).2)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact coordinate_mem_nonnegativePart hweyl
    · exact euler_mem_nonnegativePart _ _

/-- A ring map sending `x₁, p` to `x₁', p'` preserves Euler degrees. -/
theorem map_mem_eulerDegree {A' : Type*} [Ring A'] (φ : A →+* A') {x p : A} {x' p' : A'}
    (hx : φ x = x') (hp : φ p = p') {m : ℤ} {z : A} (hz : z ∈ eulerDegree x p m) :
    φ z ∈ eulerDegree x' p' m := by
  subst hx hp
  rw [mem_eulerDegree] at hz ⊢
  simpa only [eulerElement, map_sub, map_mul, map_zsmul] using congrArg φ hz

theorem map_mem_nonnegativePart {A' : Type*} [Ring A'] (φ : A →+* A') {x p : A}
    {x' p' : A'} (hx : φ x = x') (hp : φ p = p') {z : A} (hz : z ∈ nonnegativePart x p) :
    φ z ∈ nonnegativePart x' p' := by
  refine Submodule.iSup_induction _ (motive := fun z => φ z ∈ nonnegativePart x' p')
    (mem_nonnegativePart.mp hz) (fun m z hz => ?_) (by simp)
    (fun z z' h h' => by rw [map_add]; exact add_mem h h')
  exact Submodule.mem_iSup_of_mem m (map_mem_eulerDegree φ hx hp hz)

theorem map_mem_positivePart {A' : Type*} [Ring A'] (φ : A →+* A') {x p : A}
    {x' p' : A'} (hx : φ x = x') (hp : φ p = p') {z : A} (hz : z ∈ positivePart x p) :
    φ z ∈ positivePart x' p' := by
  refine Submodule.iSup_induction _ (motive := fun z => φ z ∈ positivePart x' p')
    hz (fun m z hz => ?_) (by simp) (fun z z' h h' => by rw [map_add]; exact add_mem h h')
  exact Submodule.mem_iSup_of_mem m (map_mem_eulerDegree φ hx hp hz)

/-- **Equation (nonnegative-pbw).**  `E x₁ = x₁(E+1)`, `x₁E = (E−1)x₁`,
`Ep = p(E−1)`, `pE = (E+1)p`, from `p x₁ = x₁ p + 1`. -/
theorem eq_nonnegative_pbw (x p : A) (hweyl : p * x = x * p + 1) :
    eulerElement x p * x = x * (eulerElement x p + 1) ∧
      x * eulerElement x p = (eulerElement x p - 1) * x ∧
      eulerElement x p * p = p * (eulerElement x p - 1) ∧
      p * eulerElement x p = (eulerElement x p + 1) * p := by
  simp only [eulerElement]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, hweyl]
  · rw [sub_mul, one_mul, mul_assoc x p x, hweyl]
    noncomm_ring
  · rw [mul_sub, mul_one, ← mul_assoc p x p, hweyl]
    noncomm_ring
  · rw [← mul_assoc, hweyl]

/-- **Normality of `x₁` in `A_{≥0}`.**  `x₁` commutes with the transverse
algebra `C`; once `A_{≥0}` is known to be generated by `C`, `E` and `x₁`
(`step_nonnegative_pbw` for `A_n`), for every `r ∈ A_{≥0}` there is
`r' ∈ A_{≥0}` with `x₁ r = r' x₁`.  Only this one-sided normality is used later. -/
theorem step_coordinate_normal (C : Subring A) (x p : A)
    (hweyl : p * x = x * p + 1)
    (hcomm : ∀ c : C, x * (c : A) = (c : A) * x)
    (hpbw : nonnegativePart x p = eulerSubring C x p) :
    ∀ r ∈ nonnegativePart x p, ∃ r' ∈ nonnegativePart x p, x * r = r' * x := by
  rw [hpbw]
  intro r hr
  obtain ⟨s, hs⟩ := coordinate_normal_eulerSubring C x p hweyl hcomm ⟨r, hr⟩
  exact ⟨s, s.property, hs⟩

end Grading

/-! ## Lemma 4.1 (tex 544–566) -/

section Lemma41

variable {A : Type*} [Ring A]

/-- The factors `E − i` and `E + i` are polynomials in the single element `E`,
hence commute with one another. -/
theorem step_4_1_factors_commute (x p : A) :
    (∀ i j : ℕ, Commute (eulerElement x p - i) (eulerElement x p - j)) ∧
      ∀ i j : ℕ, Commute (eulerElement x p + i) (eulerElement x p + j) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · exact ((Commute.refl _).sub_right (Nat.cast_commute j _).symm).sub_left
      ((Nat.cast_commute i _).sub_right (Nat.cast_commute i (j : A)))
  · exact ((Commute.refl _).add_right (Nat.cast_commute j _).symm).add_left
      ((Nat.cast_commute i _).add_right (Nat.cast_commute i (j : A)))

/-- `x₁ ∏(E − c) = ∏(E − 1 − c) x₁` for any list of shifts, from
`x₁E = (E−1)x₁`. -/
theorem step_4_1_coordinate_shift (x p : A) (hweyl : p * x = x * p + 1)
    (l : List ℕ) :
    x * (l.map fun i : ℕ => eulerElement x p - i).prod =
      (l.map fun i : ℕ => eulerElement x p - 1 - i).prod * x := by
  have hxE := (eq_nonnegative_pbw x p hweyl).2.1
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← mul_assoc, mul_sub, hxE, ← (Nat.cast_commute a x).eq, ← sub_mul,
        mul_assoc, ih, mul_assoc]

/-- `p ∏(E + c) = ∏(E + 1 + c) p` for any list of shifts, from `pE = (E+1)p`. -/
theorem step_4_1_momentum_shift (x p : A) (hweyl : p * x = x * p + 1)
    (l : List ℕ) :
    p * (l.map fun i : ℕ => eulerElement x p + i).prod =
      (l.map fun i : ℕ => eulerElement x p + 1 + i).prod * p := by
  have hpE := (eq_nonnegative_pbw x p hweyl).2.2.2
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← mul_assoc, mul_add, hpE, ← (Nat.cast_commute a p).eq, ← add_mul,
        mul_assoc, ih, mul_assoc]

/-- Induction step of the first identity:
`x₁^{m+1}p^{m+1} = x₁(∏_{i<m}(E−i))p = (∏_{i<m}(E−1−i))x₁p = ∏_{i≤m}(E−i)`. -/
theorem step_4_1_falling_succ (x p : A) (hweyl : p * x = x * p + 1) (m : ℕ)
    (ih : x ^ m * p ^ m = ((List.range m).map fun i : ℕ => eulerElement x p - i).prod) :
    x ^ (m + 1) * p ^ (m + 1) =
      ((List.range (m + 1)).map fun i : ℕ => eulerElement x p - i).prod := by
  calc x ^ (m + 1) * p ^ (m + 1) = x * (x ^ m * p ^ m) * p := by
        rw [pow_succ', pow_succ]; simp only [mul_assoc]
    _ = ((List.range m).map fun i : ℕ => eulerElement x p - 1 - i).prod * eulerElement x p := by
        rw [ih, step_4_1_coordinate_shift x p hweyl, mul_assoc]
    _ = eulerElement x p * ((List.range m).map fun i : ℕ => eulerElement x p - 1 - i).prod := by
        refine (Commute.list_prod_left _ _ fun y hy => ?_).eq
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
        exact ((Commute.refl _).sub_left (Commute.one_left _)).sub_left
          (Nat.cast_commute i _)
    _ = ((List.range (m + 1)).map fun i : ℕ => eulerElement x p - i).prod := by
        rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
        congr 1
        · simp
        · congr 1
          refine List.map_congr_left fun i _ => ?_
          simp only [Function.comp_apply, Nat.succ_eq_add_one]
          push_cast
          abel

/-- Induction step of the second identity, from `Ep = p(E−1)`, i.e.
`pE = (E+1)p`:
`p^{m+1}x₁^{m+1} = p(∏_{i=1}^m(E+i))x₁ = (∏_{i=1}^m(E+1+i))px₁ = ∏_{i=1}^{m+1}(E+i)`. -/
theorem step_4_1_rising_succ (x p : A) (hweyl : p * x = x * p + 1) (m : ℕ)
    (ih : p ^ m * x ^ m = ((List.range' 1 m).map fun i : ℕ => eulerElement x p + i).prod) :
    p ^ (m + 1) * x ^ (m + 1) =
      ((List.range' 1 (m + 1)).map fun i : ℕ => eulerElement x p + i).prod := by
  have hpx : p * x = eulerElement x p + 1 := hweyl
  calc p ^ (m + 1) * x ^ (m + 1) = p * (p ^ m * x ^ m) * x := by
        rw [pow_succ', pow_succ]; simp only [mul_assoc]
    _ = ((List.range' 1 m).map fun i : ℕ => eulerElement x p + 1 + i).prod *
          (eulerElement x p + 1) := by
        rw [ih, step_4_1_momentum_shift x p hweyl, mul_assoc, hpx]
    _ = (eulerElement x p + 1) *
          ((List.range' 1 m).map fun i : ℕ => eulerElement x p + 1 + i).prod := by
        refine (Commute.list_prod_left _ _ fun y hy => ?_).eq
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
        exact (Commute.refl (eulerElement x p + 1)).add_left (Nat.cast_commute i _)
    _ = ((List.range' 1 (m + 1)).map fun i : ℕ => eulerElement x p + i).prod := by
        rw [List.range'_succ, List.map_cons, List.prod_cons]
        congr 1
        · simp
        · rw [List.range'_eq_map_range, List.range'_eq_map_range, List.map_map,
            List.map_map]
          congr 1
          refine List.map_congr_left fun i _ => ?_
          simp only [Function.comp_apply]
          push_cast
          rw [add_assoc _ 1, ← add_assoc 1 1, one_add_one_eq_two]

/-- Lemma 4.1 for any ring with elements `x, p` satisfying `p x = x p + 1`:
for every `m ≥ 1`, `x^m p^m = ∏_{i=0}^{m-1}(E−i)` and `p^m x^m = ∏_{i=1}^{m}(E+i)`
with `E = x p`, the factors in each product commuting with one another.  The
products are taken in the listed order of `i`; by the last two clauses the order
does not matter. -/
theorem lemma_4_1_of_weylPair (x p : A) (hweyl : p * x = x * p + 1) (m : ℕ) (hm : 1 ≤ m) :
    x ^ m * p ^ m = ((List.range m).map fun i : ℕ => eulerElement x p - i).prod ∧
      p ^ m * x ^ m = ((List.range' 1 m).map fun i : ℕ => eulerElement x p + i).prod ∧
      (∀ i j : ℕ, Commute (eulerElement x p - i) (eulerElement x p - j)) ∧
      ∀ i j : ℕ, Commute (eulerElement x p + i) (eulerElement x p + j) := by
  refine ⟨?_, ?_, step_4_1_factors_commute x p⟩
  · -- induction from the trivial case `m = 1`
    induction m, hm using Nat.le_induction with
    | base => simp [eulerElement]
    | succ m _ ih => exact step_4_1_falling_succ x p hweyl m ih
  · induction m, hm using Nat.le_induction with
    | base => simp [eulerElement, hweyl]
    | succ m _ ih => exact step_4_1_rising_succ x p hweyl m ih

end Lemma41

open Stafford38.Paper.Section2 in
/-- **Lemma 4.1.** For `x₁, p = ∂₁ ∈ A_n(k)` and `E = x₁p`, for every `m ≥ 1`,
`x₁^m p^m = ∏_{i=0}^{m-1}(E−i)` and `p^m x₁^m = ∏_{i=1}^{m}(E+i)`, the factors in
each product commuting with one another.  The products are taken in the listed
order of `i` (`A_n(k)` is not commutative); by the last two clauses the order
does not matter.  Paper `n` is Lean `n + 1`. -/
theorem lemma_4_1 (k : Type*) [Field k] (n m : ℕ) (hm : 1 ≤ m) :
    x₁ k n ^ m * p k n ^ m =
        ((List.range m).map fun i : ℕ => eulerElement (x₁ k n) (p k n) - i).prod ∧
      p k n ^ m * x₁ k n ^ m =
        ((List.range' 1 m).map fun i : ℕ => eulerElement (x₁ k n) (p k n) + i).prod ∧
      (∀ i j : ℕ, Commute (eulerElement (x₁ k n) (p k n) - i)
        (eulerElement (x₁ k n) (p k n) - j)) ∧
      ∀ i j : ℕ, Commute (eulerElement (x₁ k n) (p k n) + i)
        (eulerElement (x₁ k n) (p k n) + j) :=
  lemma_4_1_of_weylPair _ _ (convention_2_2_relations k n).1 m hm

/-! ## The PBW form at one Ore pair stage

Every element of `PairStage B` is a sum of PBW monomials `b x^a p^c`
(coefficient on the left; `b x^a p^c` and `p^c x^a b` have the same Euler
degree `a − c`).  This section proves that the part of Euler degree `m` is
spanned by the monomials of degree `m`. -/

section PairStagePBW

open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open Stafford38.OreCoordinateStage

variable (B : Type*) [Ring B]

/-- Induction over the PBW form `∑ b x^a p^j` of a pair-stage element whose
outer exponents `j` satisfy `S`. -/
theorem pairStage_pbw_induction (S : ℕ → Prop) (P : PairStage (B := B) → Prop)
    (h0 : P 0) (hadd : ∀ y z, P y → P z → P (y + z))
    (hmono : ∀ (b : B) (a j : ℕ), S j →
      P (pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ j))
    (z : PairStage (B := B))
    (hS : ∀ j ∈ ((normalFormAddEquiv coordinateDerivation).symm z).support, S j) :
    P z := by
  have hcoeff : ∀ (c : CoordinateStage (B := B)) (j : ℕ), S j →
      P (normalCoefficient coordinateDerivation c * pairMomentum ^ j) := by
    intro c j hj
    let r := (normalFormAddEquiv (zeroDerivation (B := B))).symm c
    have hc : c = normalForm (zeroDerivation (B := B)) r :=
      ((normalFormAddEquiv (zeroDerivation (B := B))).apply_symm_apply c).symm
    rw [hc]
    induction r using Polynomial.induction_on' with
    | add r s hr hs =>
        rw [normalForm_add,
          (normalCoefficient (coordinateDerivation (B := B))).map_add, add_mul]
        exact hadd _ _ hr hs
    | monomial a b =>
        rw [normalForm_monomial,
          (normalCoefficient (coordinateDerivation (B := B))).map_mul,
          (normalCoefficient (coordinateDerivation (B := B))).map_pow]
        exact hmono b a j hj
  let q := (normalFormAddEquiv coordinateDerivation).symm z
  have hz : z = normalForm coordinateDerivation q :=
    ((normalFormAddEquiv coordinateDerivation).apply_symm_apply z).symm
  rw [hz, ← Polynomial.sum_monomial_eq q]
  change P (normalFormAddHom (coordinateDerivation (B := B))
    (∑ j ∈ q.support, Polynomial.monomial j (q.coeff j)))
  rw [map_sum]
  refine Finset.sum_induction _ P hadd h0 fun j hj => ?_
  change P (normalForm (coordinateDerivation (B := B))
    (Polynomial.monomial j (q.coeff j)))
  rw [normalForm_monomial]
  exact hcoeff (q.coeff j) j (hS j hj)

/-- The PBW monomial `b x^a p^c` has Euler degree `a − c`. -/
theorem pairMonomial_mem_eulerDegree (b : B) (a c : ℕ) :
    pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ c ∈
      eulerDegree (pairCoordinate (B := B)) pairMomentum ((a : ℤ) - c) :=
  mem_eulerDegree.mpr (Stafford38.PaperEulerGrading.orderedPBWMonomial_eulerWeight B b a c)

/-- The span of the PBW monomials of Euler degree `m`. -/
def pairWeightSpan (m : ℤ) : Submodule ℤ (PairStage (B := B)) :=
  Submodule.span ℤ {z | ∃ (b : B) (a c : ℕ), (a : ℤ) - c = m ∧
    z = pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ c}

theorem pairWeightSpan_le (m : ℤ) :
    pairWeightSpan B m ≤ eulerDegree (pairCoordinate (B := B)) pairMomentum m := by
  rw [pairWeightSpan, Submodule.span_le]
  rintro _ ⟨b, a, c, rfl, rfl⟩
  exact pairMonomial_mem_eulerDegree B b a c

/-- PBW: every element is a sum of homogeneous PBW monomials. -/
theorem mem_iSup_pairWeightSpan (z : PairStage (B := B)) :
    z ∈ ⨆ m, pairWeightSpan B m := by
  refine pairStage_pbw_induction B (fun _ => True) (fun z => z ∈ ⨆ m, pairWeightSpan B m)
    (zero_mem _) (fun _ _ hy hz => add_mem hy hz) (fun b a c _ => ?_) z fun _ _ => trivial
  exact Submodule.mem_iSup_of_mem ((a : ℤ) - c) (Submodule.subset_span ⟨b, a, c, rfl, rfl⟩)

/-- An element of Euler degree `m` is a sum of PBW monomials of degree `m`: the
parts of different degree are independent (eigenspaces of `[E, ·]`, the pair
stage being torsion-free as a `ℚ`-algebra). -/
theorem mem_pairWeightSpan_of_mem_eulerDegree [Algebra ℚ B] {m : ℤ}
    {z : PairStage (B := B)} (hz : z ∈ eulerDegree pairCoordinate pairMomentum m) :
    z ∈ pairWeightSpan B m := by
  let : Algebra ℚ (CoordinateStage (B := B)) := coordinateStageAlgebra
  let : Algebra ℚ (PairStage (B := B)) := pairStageAlgebra
  have : IsAddTorsionFree (PairStage (B := B)) := .of_module_rat _
  have hsplit := mem_iSup_pairWeightSpan B z
  rw [iSup_split_single _ m, Submodule.mem_sup] at hsplit
  obtain ⟨y, hy, r, hr, hyr⟩ := hsplit
  have hr' : r ∈ ⨆ (ν : ℤ) (_ : ν ≠ m),
      Module.End.eigenspace (eulerCommutator (pairCoordinate (B := B)) pairMomentum) ν :=
    iSup₂_mono (fun j _ => pairWeightSpan_le B j) hr
  have hrm : r ∈ Module.End.eigenspace (eulerCommutator (pairCoordinate (B := B)) pairMomentum) m := by
    have hr_eq : r = z - y := by rw [← hyr]; abel
    rw [hr_eq]
    exact sub_mem hz (pairWeightSpan_le B m hy)
  have h0 := Submodule.disjoint_def.mp
    (Module.End.eigenspaces_iSupIndep (eulerCommutator (pairCoordinate (B := B)) pairMomentum) m) r hrm hr'
  rw [← hyr, h0, add_zero]
  exact hy

variable [Algebra ℚ B]

/-- Monomials of Euler degree `≥ 0` lie in the subring generated by the
coefficients, `x` and `E`. -/
theorem pairWeightSpan_le_eulerSubring {m : ℤ} (hm : 0 ≤ m) {z : PairStage (B := B)}
    (hz : z ∈ pairWeightSpan B m) : z ∈ pairEulerSubring B := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨b, a, c, hac, rfl⟩ := hz
      exact pairOrderedMonomial_mem_eulerSubring B b a c (by omega)
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul l z _ hz => exact zsmul_mem hz l

/-- Monomials of Euler degree `≥ 1` have a right factor `x` with cofactor in
that subring, by normality of `x` (`pairOrderedMonomial_eq_eulerSubring_mul_coordinate`). -/
theorem pairWeightSpan_eq_mul_coordinate {m : ℤ} (hm : 1 ≤ m) {z : PairStage (B := B)}
    (hz : z ∈ pairWeightSpan B m) :
    ∃ U ∈ pairEulerSubring B, z = U * pairCoordinate := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨b, a, c, hac, rfl⟩ := hz
      obtain ⟨U, hU⟩ := pairOrderedMonomial_eq_eulerSubring_mul_coordinate B b a c (by omega)
      exact ⟨U, U.2, hU⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
      obtain ⟨U, hU, rfl⟩ := hy
      obtain ⟨V, hV, rfl⟩ := hz
      exact ⟨U + V, add_mem hU hV, by rw [add_mul]⟩
  | smul l z _ hz =>
      obtain ⟨U, hU, rfl⟩ := hz
      exact ⟨l • U, zsmul_mem hU l, by rw [smul_mul_assoc]⟩

/-- At the pair stage, `A_{≥0}` lies in the subring generated by the
coefficients, `x` and `E`. -/
theorem pair_nonnegativePart_le :
    nonnegativePart (pairCoordinate (B := B)) pairMomentum ≤ pairEulerSubring B := by
  intro z hz
  exact Submodule.iSup_induction _ (motive := fun z => z ∈ pairEulerSubring B)
    (mem_nonnegativePart.mp hz)
    (fun m z hz => pairWeightSpan_le_eulerSubring B (Int.natCast_nonneg m)
      (mem_pairWeightSpan_of_mem_eulerDegree B hz))
    (zero_mem _) (fun _ _ => add_mem)

/-- At the pair stage, elements of Euler degree `≥ 1` lie in `R x` for the
subring `R` generated by the coefficients, `x` and `E`. -/
theorem pair_positivePart_eq_mul_coordinate {z : PairStage (B := B)}
    (hz : z ∈ positivePart (pairCoordinate (B := B)) pairMomentum) :
    ∃ U ∈ pairEulerSubring B, z = U * pairCoordinate := by
  refine Submodule.iSup_induction _
    (motive := fun z => ∃ U ∈ pairEulerSubring B, z = U * pairCoordinate) hz
    (fun m z hz => pairWeightSpan_eq_mul_coordinate B (by omega)
      (mem_pairWeightSpan_of_mem_eulerDegree B hz))
    ⟨0, zero_mem _, by simp⟩ ?_
  rintro _ _ ⟨U, hU, rfl⟩ ⟨V, hV, rfl⟩
  exact ⟨U + V, add_mem hU hV, by rw [add_mul]⟩

end PairStagePBW

/-! ## The grading paragraph for `A_n` -/

section Presented

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- The transverse Weyl algebra `A_{n-1}` inside `A_n`. -/
abbrev transverse : Subring (PresentedWeyl k (n + 1)) :=
  (previousWeylEmbedding k n).range.toSubring

/-- `A_{≥0}` in `A_n`: the nonnegative part of the Euler grading. -/
abbrev presentedNonnegativePart : Subring (PresentedWeyl k (n + 1)) :=
  nonnegativePart (presentedCoordinate k n) (presentedMomentum k n)

/-- The elements of `A_n` of Euler degree `≥ 1`. -/
abbrev presentedPositivePart : Submodule ℤ (PresentedWeyl k (n + 1)) :=
  positivePart (presentedCoordinate k n) (presentedMomentum k n)

/-- The transverse algebra commutes with `x₁` (Convention 2.2). -/
theorem transverse_commutes_coordinate (c : transverse k n) :
    presentedCoordinate k n * (c : PresentedWeyl k (n + 1)) =
      (c : PresentedWeyl k (n + 1)) * presentedCoordinate k n :=
  ((Stafford38.Paper.Section2.convention_2_2_relations k n).2.2 c c.2).1.symm

/-- The rational scalars of `A_n`, through `ℚ → k`. -/
abbrev presentedRatAlgebra [Algebra ℚ k] : Algebra ℚ (PresentedWeyl k (n + 1)) :=
  Algebra.compHom _ (algebraMap ℚ k)

theorem rat_mem_transverse [Algebra ℚ k] (q : ℚ) :
    @algebraMap ℚ _ _ _ (presentedRatAlgebra k n) q ∈ transverse k n := by
  refine ⟨algebraMap k (PresentedWeyl k n) (algebraMap ℚ k q), ?_⟩
  exact (previousWeylEmbedding k n).commutes _

/-- The equivalence `A_n ≃ PairStage(A_{n-1})`, as a ring map. -/
abbrev toIterated : PresentedWeyl k (n + 1) →+* PairStage (B := IteratedPairStage k n) :=
  (presentedIteratedEquiv k (n + 1)).toRingEquiv.toRingHom

/-- The inverse of `A_n ≃ PairStage(A_{n-1})`, as a ring map. -/
abbrev fromIterated : PairStage (B := IteratedPairStage k n) →+* PresentedWeyl k (n + 1) :=
  (presentedIteratedEquiv k (n + 1)).symm.toRingEquiv.toRingHom

theorem fromIterated_coordinate :
    fromIterated k n pairCoordinate = presentedCoordinate k n := by
  apply (presentedIteratedEquiv k (n + 1)).injective
  exact ((presentedIteratedEquiv k (n + 1)).apply_symm_apply _).trans
    (presentedToIterated_coordinate k n).symm

theorem fromIterated_momentum :
    fromIterated k n pairMomentum = presentedMomentum k n := by
  apply (presentedIteratedEquiv k (n + 1)).injective
  exact ((presentedIteratedEquiv k (n + 1)).apply_symm_apply _).trans
    (presentedToIterated_momentum k n).symm

theorem fromIterated_toIterated (d : PresentedWeyl k (n + 1)) :
    fromIterated k n (presentedToIterated k (n + 1) d) = d :=
  (presentedIteratedEquiv k (n + 1)).symm_apply_apply d

theorem fromIterated_toIterated_ringHom (d : PresentedWeyl k (n + 1)) :
    fromIterated k n (toIterated k n d) = d :=
  (presentedIteratedEquiv k (n + 1)).symm_apply_apply d

theorem toIterated_coordinate :
    toIterated k n (presentedCoordinate k n) = pairCoordinate := by
  rw [← fromIterated_coordinate k n]
  exact (presentedIteratedEquiv k (n + 1)).apply_symm_apply _

theorem toIterated_momentum :
    toIterated k n (presentedMomentum k n) = pairMomentum := by
  rw [← fromIterated_momentum k n]
  exact (presentedIteratedEquiv k (n + 1)).apply_symm_apply _

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

/-- The equivalence `A_n ≃ PairStage(A_{n-1})` sends the Ore-tower Euler subring
into the subring of `A_n` generated by `A_{n-1}`, `x₁` and `E`. -/
theorem iterated_eulerSubring_le (z : PairStage (B := IteratedPairStage k n))
    (hz : z ∈ pairEulerSubring (IteratedPairStage k n)) :
    fromIterated k n z ∈
      eulerSubring (transverse k n) (presentedCoordinate k n) (presentedMomentum k n) := by
  have hle : pairEulerSubring (IteratedPairStage k n) ≤
      (eulerSubring (transverse k n) (presentedCoordinate k n)
        (presentedMomentum k n)).comap (fromIterated k n) := by
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

/-- **`A_{≥0}` in PBW form.**  `A_{≥0}` is generated by the transverse algebra,
`E` and `x₁`: these have Euler degree `0, 0, 1`; conversely an element of Euler
degree `m ≥ 0` is, in PBW form, a sum of monomials `b x₁^a p^c` with
`a − c = m ≥ 0`, and each is `b x₁^{a−c} (x₁^c p^c)` with `x₁^c p^c` a
polynomial in `E`. -/
theorem step_nonnegative_pbw [Algebra ℚ k] :
    presentedNonnegativePart k n =
      eulerSubring (transverse k n) (presentedCoordinate k n) (presentedMomentum k n) := by
  let := Stafford38.WeylEulerRemainder.iteratedRatAlgebra k n
  apply le_antisymm
  · intro z hz
    have h := pair_nonnegativePart_le (IteratedPairStage k n)
      (map_mem_nonnegativePart (toIterated k n) (toIterated_coordinate k n)
        (toIterated_momentum k n) hz)
    have h' := iterated_eulerSubring_le k n _ h
    rwa [fromIterated_toIterated_ringHom] at h'
  · exact eulerSubring_le_nonnegativePart _ _ _
      (Stafford38.Paper.Section2.convention_2_2_relations k n).1
      (fun c hc => (Stafford38.Paper.Section2.convention_2_2_relations k n).2.2 c hc)

/-- **Normality of `x₁` in `A_{≥0}` for `A_n`.** -/
theorem presented_coordinate_normal [Algebra ℚ k] :
    ∀ r ∈ presentedNonnegativePart k n, ∃ r' ∈ presentedNonnegativePart k n,
      presentedCoordinate k n * r = r' * presentedCoordinate k n :=
  step_coordinate_normal _ _ _ (Stafford38.Paper.Section2.convention_2_2_relations k n).1
    (transverse_commutes_coordinate k n) (step_nonnegative_pbw k n)

/-- **Elements of Euler degree `≥ 1` lie in `A_{≥0} x₁`.**  In PBW form such an
element is a sum of monomials `b x₁^a p^c` with `a > c`, and
`b x₁^a p^c = b x₁^{a−c−1} · x₁ (x₁^c p^c)`, where `x₁` crosses the
polynomial `x₁^c p^c` in `E` to the right by normality. -/
theorem step_positive_mem_nonnegative_mul_coordinate [Algebra ℚ k] :
    ∀ z ∈ presentedPositivePart k n, ∃ u₀ ∈ presentedNonnegativePart k n,
      z = u₀ * presentedCoordinate k n := by
  let := Stafford38.WeylEulerRemainder.iteratedRatAlgebra k n
  intro z hz
  obtain ⟨U, hU, hzU⟩ := pair_positivePart_eq_mul_coordinate (IteratedPairStage k n)
    (map_mem_positivePart (toIterated k n) (toIterated_coordinate k n)
      (toIterated_momentum k n) hz)
  refine ⟨fromIterated k n U, ?_, ?_⟩
  · rw [step_nonnegative_pbw k n]
    exact iterated_eulerSubring_le k n U hU
  · have h := congrArg (fromIterated k n) hzU
    rwa [map_mul, fromIterated_coordinate, fromIterated_toIterated_ringHom] at h

end Presented

#print axioms eq_nonnegative_pbw
#print axioms step_coordinate_normal
#print axioms mem_pairWeightSpan_of_mem_eulerDegree
#print axioms step_nonnegative_pbw
#print axioms presented_coordinate_normal
#print axioms step_positive_mem_nonnegative_mul_coordinate
#print axioms lemma_4_1_of_weylPair
#print axioms lemma_4_1

end

end Stafford38.Paper.Section4
