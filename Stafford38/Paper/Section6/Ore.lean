module

public import Stafford38.Weyl.Domain
public import Stafford38.Weyl.Filtration
public import AlgebraicAnalysis.Ore.RightIntersection
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# `A_n(k)` is a right Ore domain

The proof of Corollary 6.3 cites [Björk, Prop. 1.8.4]: for nonzero `d₁, d₂`
there are `r₁, r₂` with `d₁r₁ = d₂r₂ ≠ 0`.  We prove it by the growth argument:
if `d₁A ∩ d₂A = 0`, then `(x, y) ↦ d₁x + d₂y` embeds `B_m ⊕ B_m` into `B_{m+N}`
(`N` bounding the Bernstein degrees of `d₁, d₂`), so `dim B_{kN} ≥ 2^k`, while
`dim B_m ≤ (m + 1)^{2n}` grows polynomially.
-/

namespace Stafford38.Paper.Section6

open Stafford38.Characteristic
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBW

noncomputable section

universe u

variable {k : Type u} [Field k]

omit [Field k] in
theorem card_bounded_exponents_le {σ : Type*} [Fintype σ] (m : ℕ) (S : Set (σ →₀ ℕ))
    (hS : ∀ s ∈ S, ∀ i, s i ≤ m) :
    Finite S ∧ Nat.card S ≤ (m + 1) ^ Fintype.card σ := by
  classical
  let f : S → (σ → Fin (m + 1)) := fun s i => ⟨s.1 i, Nat.lt_succ_of_le (hS s.1 s.2 i)⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun hst i)
  refine ⟨Finite.of_injective f hf, ?_⟩
  calc Nat.card S ≤ Nat.card (σ → Fin (m + 1)) := Nat.card_le_card_of_injective f hf
    _ = (m + 1) ^ Fintype.card σ := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

/-- `B_m` is finite-dimensional with `dim B_m ≤ (m + 1)^{2n}`. -/
theorem bernsteinPiece_finite_finrank_le (n m : ℕ) :
    Module.Finite k (bernsteinPiece k n m) ∧
      Module.finrank k (bernsteinPiece k n m) ≤ (m + 1) ^ Fintype.card (PhaseVar n) := by
  classical
  let S : Set (PhaseVar n →₀ ℕ) := {s | ∀ i, s i ≤ m}
  obtain ⟨hSfin, hScard⟩ := card_bounded_exponents_le m S fun s hs => hs
  let P := MvPolynomial.restrictSupport k S
  let b := MvPolynomial.basisRestrictSupport k S
  have hPfin : Module.Finite k P := Module.Finite.of_basis b
  let e := presentedNormalFormLinearEquiv k n
  have hmem : ∀ x : bernsteinPiece k n m, e x ∈ P := by
    intro x
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro s hs i
    have h := x.2 s (MvPolynomial.mem_support_iff.mp hs)
    simp only [monomialWeight, bernsteinWeight, mul_one, Finsupp.sum] at h
    by_cases hi : i ∈ s.support
    · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (s j)) hi).trans h
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact Nat.zero_le m
  let φ : bernsteinPiece k n m →ₗ[k] P :=
    LinearMap.codRestrict P (e.toLinearMap.comp (bernsteinPiece k n m).subtype) hmem
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hxy)
  have hfin : Module.Finite k (bernsteinPiece k n m) := Module.Finite.of_injective φ hφ
  refine ⟨hfin, (LinearMap.finrank_le_finrank_of_injective hφ).trans ?_⟩
  rw [Module.finrank_eq_nat_card_basis b]
  exact hScard

/-- If `aA ∩ bA = 0` for nonzero `a, b ∈ B_N`, then `aB_m ⊕ bB_m ⊆ B_{N+m}`,
so `2 dim B_m ≤ dim B_{N+m}`. -/
theorem two_mul_finrank_le {n : ℕ} {a b : PresentedWeyl k n} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ∀ x y : PresentedWeyl k n, a * x = b * y → a * x = 0) {N : ℕ}
    (haN : a ∈ bernsteinPiece k n N) (hbN : b ∈ bernsteinPiece k n N) (m : ℕ) :
    2 * Module.finrank k (bernsteinPiece k n m) ≤
      Module.finrank k (bernsteinPiece k n (N + m)) := by
  have hBm := (bernsteinPiece_finite_finrank_le (k := k) n m).1
  have hBNm := (bernsteinPiece_finite_finrank_le (k := k) n (N + m)).1
  let La := LinearMap.mulLeft k a
  let Lb := LinearMap.mulLeft k b
  have hLa : Function.Injective La := fun x y hxy => by
    by_contra hne
    exact Stafford38.WeylDomain.mul_ne_zero ha (sub_ne_zero.mpr hne)
      (by rw [mul_sub]; exact sub_eq_zero.mpr hxy)
  have hLb : Function.Injective Lb := fun x y hxy => by
    by_contra hne
    exact Stafford38.WeylDomain.mul_ne_zero hb (sub_ne_zero.mpr hne)
      (by rw [mul_sub]; exact sub_eq_zero.mpr hxy)
  let U := (bernsteinPiece k n m).map La
  let V := (bernsteinPiece k n m).map Lb
  have hU : Module.finrank k U = Module.finrank k (bernsteinPiece k n m) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective La hLa _)).symm
  have hV : Module.finrank k V = Module.finrank k (bernsteinPiece k n m) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Lb hLb _)).symm
  have hUfin : FiniteDimensional k U := Module.Finite.map _ _
  have hVfin : FiniteDimensional k V := Module.Finite.map _ _
  have hinf : U ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨x, -, rfl⟩, ⟨y, -, hy⟩⟩
    exact hab x y hy.symm
  have hsup : U ⊔ V ≤ bernsteinPiece k n (N + m) := sup_le
    (by rintro _ ⟨x, hx, rfl⟩; exact mul_mem_bernsteinPiece k haN hx)
    (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_bernsteinPiece k hbN hy)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hinf, finrank_bot, add_zero, hU, hV] at h1
  have h2 := Submodule.finrank_mono hsup
  omega

omit [Field k] in
theorem exists_pow_lt_two_pow (N r : ℕ) : ∃ j : ℕ, (j * N + 1) ^ r < 2 ^ j := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt r (by norm_num : (1 : ℝ) < 2)).const_mul
    (((N : ℝ) + 1) ^ r)
  rw [mul_zero] at h
  obtain ⟨j, hj⟩ := ((h.eventually (gt_mem_nhds zero_lt_one)).and
    (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨hlt, hj1⟩ := hj
  refine ⟨j, ?_⟩
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hle : ((j * N + 1 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * j := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    push_cast
    nlinarith
  have hlt' : ((N : ℝ) + 1) ^ r * (j : ℝ) ^ r < 2 ^ j := by
    rw [← mul_div_assoc, div_lt_one hpos] at hlt
    exact hlt
  have hpow : ((j * N + 1 : ℕ) : ℝ) ^ r ≤ ((N : ℝ) + 1) ^ r * (j : ℝ) ^ r := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle r
  exact_mod_cast hpow.trans_lt hlt'


theorem one_mem_bernsteinPiece_zero (n : ℕ) : (1 : PresentedWeyl k n) ∈ bernsteinPiece k n 0 := by
  rw [bernsteinPiece, mem_presentedWeightPiece]
  intro m hm
  rw [presentedNormalFormLinearEquiv_one] at hm
  have hm0 : m = 0 := by
    symm
    simpa [MvPolynomial.coeff_one] using hm
  subst m
  simp [monomialWeight]

/-- **`A_n(k)` is a right Ore domain** [Björk, Prop. 1.8.4]: nonzero `d₁, d₂`
have `r₁, r₂` with `d₁r₁ = d₂r₂ ≠ 0`. -/
theorem weyl_rightOreCondition (n : ℕ) :
    AlgebraicAnalysis.OreRightIntersection.RightOreCondition (PresentedWeyl k n) := by
  intro a b ha hb
  by_contra hcon
  have hab : ∀ x y : PresentedWeyl k n, a * x = b * y → a * x = 0 := by
    intro x y hxy
    by_contra hne
    exact hcon ⟨x, y, hxy, hne⟩
  obtain ⟨Na, hNa⟩ := exists_mem_bernsteinPiece k a
  obtain ⟨Nb, hNb⟩ := exists_mem_bernsteinPiece k b
  let N := max Na Nb
  have haN : a ∈ bernsteinPiece k n N :=
    presentedWeightPiece_mono k bernsteinWeight (le_max_left Na Nb) hNa
  have hbN : b ∈ bernsteinPiece k n N :=
    presentedWeightPiece_mono k bernsteinWeight (le_max_right Na Nb) hNb
  have h10 : (1 : PresentedWeyl k n) ≠ 0 := fun h => ha (by rw [← mul_one a, h, mul_zero])
  have hgrow : ∀ j : ℕ, 2 ^ j ≤ Module.finrank k (bernsteinPiece k n (j * N)) := by
    intro j
    induction j with
    | zero =>
        have hfin := (bernsteinPiece_finite_finrank_le (k := k) n 0).1
        rw [pow_zero, zero_mul, Nat.one_le_iff_ne_zero]
        intro h0
        rw [Submodule.finrank_eq_zero] at h0
        have h1 := one_mem_bernsteinPiece_zero (k := k) n
        rw [h0, Submodule.mem_bot] at h1
        exact h10 h1
    | succ j ih =>
        have h := two_mul_finrank_le ha hb hab haN hbN (j * N)
        rw [show (j + 1) * N = N + j * N by ring, pow_succ]
        omega
  obtain ⟨j, hj⟩ := exists_pow_lt_two_pow N (Fintype.card (PhaseVar n))
  have hle := (bernsteinPiece_finite_finrank_le (k := k) n (j * N)).2
  have := hgrow j
  omega

#print axioms bernsteinPiece_finite_finrank_le
#print axioms two_mul_finrank_le
#print axioms exists_pow_lt_two_pow
#print axioms weyl_rightOreCondition

end

end Stafford38.Paper.Section6
