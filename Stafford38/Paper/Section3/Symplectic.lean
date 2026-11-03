module

public import Stafford38.Paper.Section2.Symplectic

@[expose] public section

/-!
# Lemma 3.1: symplectic completion

Symplectic bases and the standard form `ω` are those of Definition 2.8
(`Stafford38.Paper.Section2.IsSymplecticBasis`, `Section2.omega`).  Lemma 3.1 completes a nonzero vector
`v` to a symplectic basis and produces an `ω`-preserving automorphism `g` with
`g(e) = v`.  Its proof is split into the five paragraphs of the paper.

Indexing: a basis of `𝕍` is indexed by `Fin n ⊕ Fin n`; `Sum.inl i` is `e_{i+1}`
and `Sum.inr i` is `f_{i+1}`.  On `𝕍 = PhaseVar n → k`, `Sum.inl i` is the
coefficient of `x_{i+1}` and `Sum.inr i` that of `∂_{i+1}`.
-/

open LinearMap (BilinForm)
open Module

namespace Stafford38.Paper.Section3

open Stafford38.Characteristic
open Stafford38.CharacteristicSymplecticCompletion
open Stafford38.Paper.Section2

noncomputable section

universe u v

section Abstract

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

/-- **Lemma 3.1, paragraph 1.** As `ω` is nondegenerate and `v ≠ 0`, some `w'`
has `ω(v, w') = c ≠ 0`; `w := w'/c` has `ω(v, w) = 1`. -/
theorem step_lemma_3_1_partner (ω : BilinForm k V) (hnd : ω.Nondegenerate)
    {v : V} (hv : v ≠ 0) : ∃ w : V, ω v w = 1 := by
  have hpair : ∃ w', ω v w' ≠ 0 := by
    by_contra h
    exact hv (hnd.1 v fun y => by_contra fun hy => h ⟨y, hy⟩)
  obtain ⟨w', hw'⟩ := hpair
  refine ⟨(ω v w')⁻¹ • w', ?_⟩
  rw [BilinForm.smul_right]
  exact inv_mul_cancel₀ hw'

/-- **Lemma 3.1, paragraph 2.** On `U = span(v, w)`: for `av + bw ≠ 0`, if
`a ≠ 0` then `ω(av + bw, w) = a ≠ 0`, and if `b ≠ 0` then
`ω(av + bw, v) = -b ≠ 0`; so `ω|_U` is nondegenerate. -/
theorem step_lemma_3_1_plane (ω : BilinForm k V) (hAlt : ∀ x, ω x x = 0)
    {v w : V} (hvw : ω v w = 1) (a b : k) :
    ω (a • v + b • w) w = a ∧ ω (a • v + b • w) v = -b := by
  have hwv : ω w v = -1 := by
    have h := BilinForm.IsAlt.neg_eq (show ω.IsAlt from hAlt) v w
    simpa [hvw] using h.symm
  constructor
  · rw [BilinForm.add_left, BilinForm.smul_left, BilinForm.smul_left, hvw, hAlt w]
    ring
  · rw [BilinForm.add_left, BilinForm.smul_left, BilinForm.smul_left, hAlt v, hwv]
    ring

/-- **Lemma 3.1, paragraph 3.** `U ∩ U^⊥ = 0` because `ω|_U` is nondegenerate
(paragraph 2); with `dim U + dim U^⊥ = 2n` this gives `𝕍 = U ⊕ U^⊥`, and
`ω|_{U^⊥}` is nondegenerate.  The intersection is computed from paragraph 2;
the dimension count and the nondegeneracy of `ω|_{U^⊥}` are
`SymplecticComplement.pairComplementData`. -/
theorem step_lemma_3_1_complement [Module.Finite k V] (ω : BilinForm k V)
    (hAlt : ∀ x, ω x x = 0) (hnd : ω.Nondegenerate) {v w : V} (hvw : ω v w = 1) :
    let U : Submodule k V := Submodule.span k {v, w}
    Disjoint U (ω.orthogonal U) ∧ IsCompl U (ω.orthogonal U) ∧
      (ω.restrict (ω.orthogonal U)).Nondegenerate ∧
      Module.finrank k (ω.orthogonal U) + 2 = Module.finrank k V := by
  intro U
  have hdata :=
    Stafford38.LinearAlgebra.SymplecticComplement.pairComplementData ω hAlt hnd v w hvw
  refine ⟨?_, hdata.2.1, hdata.2.2.1, hdata.2.2.2⟩
  rw [Submodule.disjoint_def]
  intro x hxU hxO
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hxU
  have hvU : v ∈ U := Submodule.subset_span (by simp)
  have hwU : w ∈ U := Submodule.subset_span (by simp)
  have hskew (x y : V) : ω x y = -ω y x :=
    ((show ω.IsAlt from hAlt).neg_eq y x).symm
  have hw0 : ω (a • v + b • w) w = 0 := by rw [hskew]; simp [hxO w hwU]
  have hv0 : ω (a • v + b • w) v = 0 := by rw [hskew]; simp [hxO v hvU]
  obtain ⟨ha, hb⟩ := step_lemma_3_1_plane ω hAlt hvw a b
  have ha0 : a = 0 := by rw [← ha, hw0]
  have hb0 : b = 0 := by rw [← neg_neg b, ← hb, hv0, neg_zero]
  simp [ha0, hb0]

private def pairVectors (v w : V) : Fin 2 → V := ![v, w]

private def onePlusEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) where
  toFun
    | .inl _ => 0
    | .inr i => i.succ
  invFun := Fin.cases (Sum.inl 0) (fun i => Sum.inr i)
  left_inv x := by
    cases x with
    | inl i => have : i = 0 := Subsingleton.elim _ _; subst i; rfl
    | inr i => rfl
  right_inv i := by
    refine Fin.cases ?_ ?_ i <;> simp

private def rearrangePairIndex (n : ℕ) :
    (Fin 1 ⊕ Fin 1) ⊕ (Fin n ⊕ Fin n) ≃
      (Fin 1 ⊕ Fin n) ⊕ (Fin 1 ⊕ Fin n) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr i) => .inr (.inl i)
    | .inr (.inl i) => .inl (.inr i)
    | .inr (.inr i) => .inr (.inr i)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr i) => .inr (.inl i)
    | .inr (.inl i) => .inl (.inr i)
    | .inr (.inr i) => .inr (.inr i)
  left_inv x := by cases x with
    | inl x => cases x <;> rfl
    | inr x => cases x <;> rfl
  right_inv x := by cases x with
    | inl x => cases x <;> rfl
    | inr x => cases x <;> rfl

private def symplecticPairIndex (n : ℕ) :
    Fin 2 ⊕ (Fin n ⊕ Fin n) ≃ Fin (n + 1) ⊕ Fin (n + 1) :=
  (Equiv.sumCongr (finSumFinEquiv (m := 1) (n := 1)).symm (Equiv.refl _)).trans
    ((rearrangePairIndex n).trans
      (Equiv.sumCongr (onePlusEquiv n) (onePlusEquiv n)))

private theorem pairIndex_left0 (n : ℕ) :
    (symplecticPairIndex n).symm (Sum.inl (0 : Fin (n + 1))) = Sum.inl (0 : Fin 2) := by
  simp [symplecticPairIndex, rearrangePairIndex, onePlusEquiv,
    Equiv.sumCongr_symm, finSumFinEquiv]

private theorem pairIndex_right0 (n : ℕ) :
    (symplecticPairIndex n).symm (Sum.inr (0 : Fin (n + 1))) = Sum.inl (1 : Fin 2) := by
  simp [symplecticPairIndex, rearrangePairIndex, onePlusEquiv,
    Equiv.sumCongr_symm, finSumFinEquiv]

private theorem pairIndex_left_succ (n : ℕ) (i : Fin n) :
    (symplecticPairIndex n).symm (Sum.inl i.succ) = Sum.inr (Sum.inl i) := by
  simp [symplecticPairIndex, rearrangePairIndex, onePlusEquiv,
    Equiv.sumCongr_symm, finSumFinEquiv]

private theorem pairIndex_right_succ (n : ℕ) (i : Fin n) :
    (symplecticPairIndex n).symm (Sum.inr i.succ) = Sum.inr (Sum.inr i) := by
  simp [symplecticPairIndex, rearrangePairIndex, onePlusEquiv,
    Equiv.sumCongr_symm, finSumFinEquiv]

/-- **Lemma 3.1, paragraph 4.** By induction on `n`, `U^⊥` has a symplectic
basis `e_2, …, f_n`; with `e_1 := v`, `f_1 := w` this is a symplectic basis of
`𝕍 = U ⊕ U^⊥`, since cross pairings between `U` and `U^⊥` vanish.  The
induction is `CharacteristicPaperSymplecticBasis.exists_symplectic_basis`
applied to `U^⊥` with the data of paragraph 3. -/
theorem step_lemma_3_1_basis [Module.Finite k V] (n : ℕ) (ω : BilinForm k V)
    (hAlt : ∀ x, ω x x = 0) {v w : V} (hvw : ω v w = 1)
    (hcompl : IsCompl (Submodule.span k {v, w}) (ω.orthogonal (Submodule.span k {v, w})))
    (hWnd : (ω.restrict (ω.orthogonal (Submodule.span k {v, w}))).Nondegenerate)
    (hWdim : Module.finrank k (ω.orthogonal (Submodule.span k {v, w})) = 2 * n) :
    ∃ b : Basis (Fin (n + 1) ⊕ Fin (n + 1)) k V,
      IsSymplecticBasis ω b ∧ b (Sum.inl 0) = v ∧ b (Sum.inr 0) = w := by
  let U : Submodule k V := Submodule.span k {v, w}
  let W : Submodule k V := ω.orthogonal U
  have hAltW : ∀ x : W, (ω.restrict W) x x = 0 := fun x => hAlt x
  obtain ⟨bW, hbWcross, hbWleft, hbWright⟩ :=
    Stafford38.CharacteristicPaperSymplecticBasis.exists_symplectic_basis n
      (ω.restrict W) hAltW hWnd hWdim
  have hUmemV : v ∈ U := Submodule.subset_span (by simp)
  have hUmemW : w ∈ U := Submodule.subset_span (by simp)
  have hli : LinearIndependent k (pairVectors v w) := by
    change LinearIndependent k ![v, w]
    rw [LinearIndependent.pair_iff]
    intro a b hab
    obtain ⟨ha, hb⟩ := step_lemma_3_1_plane ω hAlt hvw a b
    rw [hab, BilinForm.zero_left] at ha hb
    exact ⟨ha.symm, by simpa using hb.symm⟩
  have hspan : Submodule.span k (Set.range (pairVectors v w)) = U := by
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [pairVectors]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [pairVectors]⟩
      · exact ⟨1, by simp [pairVectors]⟩
  let bU : Basis (Fin 2) k U := (Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hbU0 : bU 0 = ⟨v, hUmemV⟩ := by
    apply Subtype.ext
    dsimp [bU]
    rw [Module.Basis.coe_span_apply]
    simp [pairVectors]
  have hbU1 : bU 1 = ⟨w, hUmemW⟩ := by
    apply Subtype.ext
    dsimp [bU]
    rw [Module.Basis.coe_span_apply]
    simp [pairVectors]
  let b : Basis (Fin (n + 1) ⊕ Fin (n + 1)) k V :=
    ((bU.prod bW).map (Submodule.prodEquivOfIsCompl U W hcompl)).reindex
      (symplecticPairIndex n)
  have hbE0 : b (Sum.inl (0 : Fin (n + 1))) = v := by
    simp only [b, Module.Basis.reindex_apply, pairIndex_left0, Module.Basis.map_apply]
    simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl', hbU0]
  have hbF0 : b (Sum.inr (0 : Fin (n + 1))) = w := by
    simp only [b, Module.Basis.reindex_apply, pairIndex_right0, Module.Basis.map_apply]
    simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl', hbU1]
  have hbEs (i : Fin n) : b (Sum.inl i.succ) = (bW (Sum.inl i) : V) := by
    simp only [b, Module.Basis.reindex_apply, pairIndex_left_succ, Module.Basis.map_apply]
    simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hbFs (i : Fin n) : b (Sum.inr i.succ) = (bW (Sum.inr i) : V) := by
    simp only [b, Module.Basis.reindex_apply, pairIndex_right_succ, Module.Basis.map_apply]
    simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hskew (x y : V) : ω x y = -ω y x :=
    ((show ω.IsAlt from hAlt).neg_eq y x).symm
  refine ⟨b, ⟨?_, ?_, ?_⟩, hbE0, hbF0⟩
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa [hbE0, hbF0] using hvw
      · simp only [eq_comm, Fin.succ_ne_zero, ite_false]
        rw [hbE0, hbFs]
        exact ((bW (Sum.inr j)).property v hUmemV).symm
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.succ_ne_zero, ite_false]
        rw [hbEs, hbF0, hskew]
        simp [(bW (Sum.inl i)).property w hUmemW]
      · simpa [hbEs, hbFs] using hbWcross i j
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hbE0]; exact hAlt v
      · rw [hbE0, hbEs]; exact (bW (Sum.inl j)).property v hUmemV
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hbEs, hbE0, hskew]
        simp [(bW (Sum.inl i)).property v hUmemV]
      · simpa [hbEs] using hbWleft i j
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hbF0]; exact hAlt w
      · rw [hbF0, hbFs]; simp [(bW (Sum.inr j)).property w hUmemW]
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hbFs, hbF0, hskew]
        simp [(bW (Sum.inr i)).property w hUmemW]
      · simpa [hbFs] using hbWright i j

/-- **Lemma 3.1, paragraph 5.** The linear map sending one symplectic basis to
another, vector by vector, preserves all pairwise values of `ω` on basis
vectors, hence by bilinearity preserves `ω`. -/
theorem step_lemma_3_1_transport {m : ℕ} (ω : BilinForm k V) (hAlt : ∀ x, ω x x = 0)
    (b₁ b₂ : Basis (Fin m ⊕ Fin m) k V) (h₁ : IsSymplecticBasis ω b₁)
    (h₂ : IsSymplecticBasis ω b₂) :
    (∀ x y, ω (b₁.equiv b₂ (Equiv.refl _) x) (b₁.equiv b₂ (Equiv.refl _) y) = ω x y) ∧
      ∀ i, b₁.equiv b₂ (Equiv.refl _) (b₁ i) = b₂ i := by
  have hg := Stafford38.CharacteristicPaperSymplecticBasis.symplectic_basis_equiv m ω ω
    b₁ b₂ hAlt hAlt h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
  refine ⟨fun x y => ?_, fun i => Basis.equiv_apply b₁ i b₂ (Equiv.refl _)⟩
  have h := congrArg (fun f : BilinForm k V => f x y) hg
  simpa [LinearMap.BilinForm.comp_apply] using h

/-- **Lemma 3.1.** Let `(𝕍, ω)` be a symplectic `k`-space of dimension `2n`
(`ω` antisymmetric and nondegenerate) and `0 ≠ v ∈ 𝕍`.  Then `v` is the first
vector `e_1` of a symplectic basis of `𝕍`; consequently, for every nonzero
`e ∈ 𝕍` there is a `k`-linear automorphism `g` preserving `ω` with
`g(e) = v`. -/
theorem lemma_3_1 [CharZero k] [Module.Finite k V] (n : ℕ) (ω : BilinForm k V)
    (hanti : ∀ x y, ω x y = -ω y x) (hnd : ω.Nondegenerate)
    (hdim : Module.finrank k V = 2 * n) {v : V} (hv : v ≠ 0) :
    (∃ (hn : 0 < n) (b : Basis (Fin n ⊕ Fin n) k V),
        IsSymplecticBasis ω b ∧ b (Sum.inl ⟨0, hn⟩) = v) ∧
      ∀ e : V, e ≠ 0 →
        ∃ g : V ≃ₗ[k] V, (∀ x y, ω (g x) (g y) = ω x y) ∧ g e = v := by
  have hAlt := alternating_of_antisymmetric ω hanti
  -- every nonzero vector is the first vector of a symplectic basis
  have hcomplete : ∀ u : V, u ≠ 0 → ∃ m : ℕ, n = m + 1 ∧
      ∃ b : Basis (Fin (m + 1) ⊕ Fin (m + 1)) k V,
        IsSymplecticBasis ω b ∧ b (Sum.inl 0) = u := by
    intro u hu
    obtain ⟨w, huw⟩ := step_lemma_3_1_partner ω hnd hu
    obtain ⟨-, hcompl, hWnd, hWdim⟩ := step_lemma_3_1_complement ω hAlt hnd huw
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨m, rfl, ?_⟩
    obtain ⟨b, hb, hb0, -⟩ :=
      step_lemma_3_1_basis m ω hAlt huw hcompl hWnd (by omega)
    exact ⟨b, hb, hb0⟩
  obtain ⟨m, rfl, b, hb, hb0⟩ := hcomplete v hv
  refine ⟨⟨Nat.succ_pos m, b, hb, hb0⟩, fun e he => ?_⟩
  obtain ⟨m', hm', b', hb', hb'0⟩ := hcomplete e he
  obtain rfl : m' = m := by omega
  obtain ⟨hpres, happ⟩ := step_lemma_3_1_transport ω hAlt b' b hb' hb
  exact ⟨b'.equiv b (Equiv.refl _), hpres, by rw [← hb'0, happ, hb0]⟩

end Abstract

#print axioms lemma_3_1

end

end Stafford38.Paper.Section3
