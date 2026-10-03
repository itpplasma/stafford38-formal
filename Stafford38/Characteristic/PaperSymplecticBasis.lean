module
public import Stafford38.LinearAlgebra.SymplecticComplement
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

/-!
# Paper-facing symplectic basis completion

Inductively split off a normalized symplectic plane and complete its
nondegenerate orthogonal complement.  The result is for an arbitrary finite
dimensional alternating nondegenerate space, not only the standard model.
-/

open LinearMap (BilinForm)
open Module

namespace Stafford38.CharacteristicPaperSymplecticBasis

universe u v
variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

private def pairVectors (v w : V) : Fin 2 → V := ![v, w]

private def splitTwo : Fin 2 ≃ Fin 1 ⊕ Fin 1 :=
  (finSumFinEquiv (m := 1) (n := 1)).symm

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

@[simp] private theorem onePlusEquiv_symm_zero (n : ℕ) :
    (onePlusEquiv n).symm (0 : Fin (n + 1)) = Sum.inl 0 := by
  simp [onePlusEquiv, finSumFinEquiv]

@[simp] private theorem onePlusEquiv_symm_succ (n : ℕ) (i : Fin n) :
    (onePlusEquiv n).symm i.succ = Sum.inr i := by
  simp [onePlusEquiv, finSumFinEquiv]

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
  (Equiv.sumCongr splitTwo (Equiv.refl _)).trans
    ((rearrangePairIndex n).trans
      (Equiv.sumCongr (onePlusEquiv n) (onePlusEquiv n)))

private theorem pairVectors_range (v w : V) :
    Set.range (pairVectors v w) = ({v, w} : Set V) := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [pairVectors]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [pairVectors]⟩
    · exact ⟨1, by simp [pairVectors]⟩

private theorem normalized_pair_linearIndependent (B : BilinForm k V)
    (hAlt : ∀ x, B x x = 0) (v w : V) (hvw : B v w = 1) :
    LinearIndependent k (pairVectors v w) := by
  change LinearIndependent k ![v, w]
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hwv : B w v = -1 := by
    have h := BilinForm.IsAlt.neg_eq (show B.IsAlt from hAlt) v w
    simpa [hvw] using h.symm
  have hvsum : B (a • v + b • w) w = 0 := by
    rw [hab, BilinForm.zero_left]
  have hwsum : B (a • v + b • w) v = 0 := by
    rw [hab, BilinForm.zero_left]
  rw [BilinForm.add_left, BilinForm.smul_left, BilinForm.smul_left,
    hvw, hAlt w] at hvsum
  rw [BilinForm.add_left, BilinForm.smul_left, BilinForm.smul_left,
    hAlt v, hwv] at hwsum
  constructor
  · simpa using hvsum
  · simpa [mul_comm] using hwsum

private theorem pairIndex_left0 (n : ℕ) :
    (symplecticPairIndex n).symm (Sum.inl (0 : Fin (n + 1))) =
      Sum.inl (0 : Fin 2) := by
  simp [symplecticPairIndex, splitTwo, rearrangePairIndex,
    Equiv.symm_trans_apply, Equiv.sumCongr_symm, finSumFinEquiv]

private theorem pairIndex_right0 (n : ℕ) :
    (symplecticPairIndex n).symm (Sum.inr (0 : Fin (n + 1))) =
      Sum.inl (1 : Fin 2) := by
  simp [symplecticPairIndex, splitTwo, rearrangePairIndex,
    Equiv.symm_trans_apply, Equiv.sumCongr_symm, finSumFinEquiv]

private theorem pairIndex_left_succ (n : ℕ) (i : Fin n) :
    (symplecticPairIndex n).symm (Sum.inl i.succ) =
      Sum.inr (Sum.inl i) := by
  simp [symplecticPairIndex, splitTwo, rearrangePairIndex,
    Equiv.symm_trans_apply, Equiv.sumCongr_symm, finSumFinEquiv]

private theorem pairIndex_right_succ (n : ℕ) (i : Fin n) :
    (symplecticPairIndex n).symm (Sum.inr i.succ) =
      Sum.inr (Sum.inr i) := by
  simp [symplecticPairIndex, splitTwo, rearrangePairIndex,
    Equiv.symm_trans_apply, Equiv.sumCongr_symm, finSumFinEquiv]

theorem exists_symplectic_basis (n : ℕ) (B : BilinForm k V)
    [Module.Finite k V] (hAlt : ∀ x, B x x = 0) (hB : B.Nondegenerate)
    (hdim : Module.finrank k V = 2 * n) :
    ∃ b : Basis (Fin n ⊕ Fin n) k V,
      (∀ i j, B (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) ∧
      (∀ i j, B (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
      (∀ i j, B (b (Sum.inr i)) (b (Sum.inr j)) = 0) := by
  induction n generalizing V B with
  | zero =>
      have hdim0 : Module.finrank k V = 0 := by simpa using hdim
      letI : Subsingleton V := Module.finrank_zero_iff.mp hdim0
      letI : IsEmpty (Fin 0 ⊕ Fin 0) := inferInstance
      refine ⟨Module.Basis.empty V, ?_, ?_, ?_⟩
      · intro i j
        exact isEmptyElim i
      · intro i j
        exact isEmptyElim i
      · intro i j
        exact isEmptyElim i
  | succ n ih =>
      have hdimV : Module.finrank k V = 2 * (n + 1) := hdim
      have hpos : 0 < Module.finrank k V := by rw [hdimV]; omega
      obtain ⟨v, hvne⟩ :=
        (Module.finrank_pos_iff_exists_ne_zero (R := k) (M := V)).mp hpos
      have hpair : ∃ w, B v w ≠ 0 := by
        by_contra h
        push_neg at h
        exact hvne (hB.1 v h)
      obtain ⟨w₀, hw₀⟩ := hpair
      let w : V := (B v w₀)⁻¹ • w₀
      have hvw : B v w = 1 := by
        dsimp [w]
        rw [BilinForm.smul_right]
        exact inv_mul_cancel₀ hw₀
      let U : Submodule k V := Submodule.span k {v, w}
      let W : Submodule k V := B.orthogonal U
      have hdata :=
        Stafford38.LinearAlgebra.SymplecticComplement.pairComplementData B hAlt hB v w hvw
      have hcompl : IsCompl U W := hdata.2.1
      have hWnondeg : (B.restrict W).Nondegenerate := hdata.2.2.1
      have hWdim : Module.finrank k W = 2 * n := by
        have hdrop : Module.finrank k W + 2 = Module.finrank k V := hdata.2.2.2
        rw [hdimV] at hdrop
        omega
      have hAltW : ∀ x : W, (B.restrict W) x x = 0 := by
        intro x
        exact hAlt x
      obtain ⟨bW, hbWcross, hbWleft, hbWright⟩ :=
        ih (V := W) (B := B.restrict W) hAltW hWnondeg hWdim
      have hUmemV : v ∈ U := Submodule.subset_span (by simp [U])
      have hUmemW : w ∈ U := Submodule.subset_span (by simp [U])
      let hli := normalized_pair_linearIndependent B hAlt v w hvw
      have hspan : Submodule.span k (Set.range (pairVectors v w)) = U := by
        rw [pairVectors_range]
      let bUraw : Basis (Fin 2) k (Submodule.span k (Set.range (pairVectors v w))) :=
        Basis.span hli
      let eU : (Submodule.span k (Set.range (pairVectors v w))) ≃ₗ[k] U :=
        LinearEquiv.ofEq _ _ hspan
      let bU : Basis (Fin 2) k U := bUraw.map eU
      have hbU0 : bU 0 = ⟨v, hUmemV⟩ := by
        apply Subtype.ext
        dsimp [bU, bUraw, eU]
        rw [Module.Basis.coe_span_apply]
        simp [pairVectors]
      have hbU1 : bU 1 = ⟨w, hUmemW⟩ := by
        apply Subtype.ext
        dsimp [bU, bUraw, eU]
        rw [Module.Basis.coe_span_apply]
        simp [pairVectors]
      let eCompl := Submodule.prodEquivOfIsCompl U W hcompl
      let bProd : Basis (Fin 2 ⊕ (Fin n ⊕ Fin n)) k (U × W) := bU.prod bW
      let bBase := bProd.map eCompl
      let b : Basis (Fin (n + 1) ⊕ Fin (n + 1)) k V :=
        bBase.reindex (symplecticPairIndex n)
      have hbE0 : b (Sum.inl (0 : Fin (n + 1))) = v := by
        change (bBase.reindex (symplecticPairIndex n)) (Sum.inl 0) = v
        rw [Module.Basis.reindex_apply, pairIndex_left0, Module.Basis.map_apply]
        change (Submodule.prodEquivOfIsCompl U W hcompl)
          ((bU.prod bW) (Sum.inl (0 : Fin 2))) = v
        simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl', hbU0]
      have hbF0 : b (Sum.inr (0 : Fin (n + 1))) = w := by
        change (bBase.reindex (symplecticPairIndex n)) (Sum.inr 0) = w
        rw [Module.Basis.reindex_apply, pairIndex_right0, Module.Basis.map_apply]
        change (Submodule.prodEquivOfIsCompl U W hcompl)
          ((bU.prod bW) (Sum.inl (1 : Fin 2))) = w
        simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl', hbU1]
      have hbEs (i : Fin n) : b (Sum.inl i.succ) = (bW (Sum.inl i) : V) := by
        change (bBase.reindex (symplecticPairIndex n)) (Sum.inl i.succ) = _
        rw [Module.Basis.reindex_apply, pairIndex_left_succ, Module.Basis.map_apply]
        change (Submodule.prodEquivOfIsCompl U W hcompl)
          ((bU.prod bW) (Sum.inr (Sum.inl i))) = _
        simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
      have hbFs (i : Fin n) : b (Sum.inr i.succ) = (bW (Sum.inr i) : V) := by
        change (bBase.reindex (symplecticPairIndex n)) (Sum.inr i.succ) = _
        rw [Module.Basis.reindex_apply, pairIndex_right_succ, Module.Basis.map_apply]
        change (Submodule.prodEquivOfIsCompl U W hcompl)
          ((bU.prod bW) (Sum.inr (Sum.inr i))) = _
        simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
      have hAlt' : B.IsAlt := hAlt
      have hskew (x y : V) : B x y = -B y x := (hAlt'.neg_eq y x).symm
      refine ⟨b, ?_, ?_, ?_⟩
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases ?_ (fun j => ?_) j
          · simpa [hbE0, hbF0] using hvw
          ·
            simp only [ne_eq, eq_comm, Fin.succ_ne_zero, if_false]
            rw [hbE0, hbFs]
            exact ((bW (Sum.inr j)).property v hUmemV).symm
        ·
          refine Fin.cases ?_ (fun j => ?_) j
          · simp only [Fin.succ_ne_zero, if_false]
            rw [hbEs, hbF0, hskew]
            simp [(bW (Sum.inl i)).property w hUmemW]
          ·
            have h := hbWcross i j
            simpa [hbEs, hbFs] using h
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases ?_ (fun j => ?_) j
          · rw [hbE0]
            exact hAlt v
          ·
            rw [hbE0, hbEs]
            exact (bW (Sum.inl j)).property v hUmemV
        ·
          refine Fin.cases ?_ (fun j => ?_) j
          · rw [hbEs, hbE0, hskew]
            simp [(bW (Sum.inl i)).property v hUmemV]
          ·
            have h := hbWleft i j
            simpa [hbEs] using h
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases ?_ (fun j => ?_) j
          · rw [hbF0]
            exact hAlt w
          ·
            rw [hbF0, hbFs]
            simp [(bW (Sum.inr j)).property w hUmemW]
        ·
          refine Fin.cases ?_ (fun j => ?_) j
          · rw [hbFs, hbF0, hskew]
            simp [(bW (Sum.inr i)).property w hUmemW]
          ·
            have h := hbWright i j
            simpa [hbFs] using h

/-- Complete a prescribed normalized pair to a symplectic basis. -/
theorem exists_symplectic_basis_with_pair (n : ℕ) (B : BilinForm k V)
    [Module.Finite k V] (hAlt : ∀ x, B x x = 0) (hB : B.Nondegenerate)
    (hdim : Module.finrank k V = 2 * (n + 1)) (v w : V)
    (hvw : B v w = 1) :
    ∃ b : Basis (Fin (n + 1) ⊕ Fin (n + 1)) k V,
      (∀ i j, B (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) ∧
      (∀ i j, B (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
      (∀ i j, B (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
      b (Sum.inl 0) = v ∧ b (Sum.inr 0) = w := by
  let U : Submodule k V := Submodule.span k {v, w}
  let W : Submodule k V := B.orthogonal U
  have hdata :=
    Stafford38.LinearAlgebra.SymplecticComplement.pairComplementData B hAlt hB v w hvw
  have hcompl : IsCompl U W := hdata.2.1
  have hWnondeg : (B.restrict W).Nondegenerate := hdata.2.2.1
  have hWdim : Module.finrank k W = 2 * n := by
    have hdrop : Module.finrank k W + 2 = Module.finrank k V := hdata.2.2.2
    rw [hdim] at hdrop
    omega
  have hAltW : ∀ x : W, (B.restrict W) x x = 0 := by
    intro x
    exact hAlt x
  obtain ⟨bW, hbWcross, hbWleft, hbWright⟩ :=
    exists_symplectic_basis n (B.restrict W) hAltW hWnondeg hWdim
  have hUmemV : v ∈ U := Submodule.subset_span (by simp [U])
  have hUmemW : w ∈ U := Submodule.subset_span (by simp [U])
  let hli := normalized_pair_linearIndependent B hAlt v w hvw
  have hspan : Submodule.span k (Set.range (pairVectors v w)) = U := by
    rw [pairVectors_range]
  let bUraw : Basis (Fin 2) k (Submodule.span k (Set.range (pairVectors v w))) :=
    Basis.span hli
  let eU : (Submodule.span k (Set.range (pairVectors v w))) ≃ₗ[k] U :=
    LinearEquiv.ofEq _ _ hspan
  let bU : Basis (Fin 2) k U := bUraw.map eU
  have hbU0 : bU 0 = ⟨v, hUmemV⟩ := by
    apply Subtype.ext
    dsimp [bU, bUraw, eU]
    rw [Module.Basis.coe_span_apply]
    simp [pairVectors]
  have hbU1 : bU 1 = ⟨w, hUmemW⟩ := by
    apply Subtype.ext
    dsimp [bU, bUraw, eU]
    rw [Module.Basis.coe_span_apply]
    simp [pairVectors]
  let eCompl := Submodule.prodEquivOfIsCompl U W hcompl
  let bProd : Basis (Fin 2 ⊕ (Fin n ⊕ Fin n)) k (U × W) := bU.prod bW
  let bBase := bProd.map eCompl
  let b : Basis (Fin (n + 1) ⊕ Fin (n + 1)) k V :=
    bBase.reindex (symplecticPairIndex n)
  have hbE0 : b (Sum.inl (0 : Fin (n + 1))) = v := by
    change (bBase.reindex (symplecticPairIndex n)) (Sum.inl 0) = v
    rw [Module.Basis.reindex_apply, pairIndex_left0, Module.Basis.map_apply]
    change (Submodule.prodEquivOfIsCompl U W hcompl)
      ((bU.prod bW) (Sum.inl (0 : Fin 2))) = v
    simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl', hbU0]
  have hbF0 : b (Sum.inr (0 : Fin (n + 1))) = w := by
    change (bBase.reindex (symplecticPairIndex n)) (Sum.inr 0) = w
    rw [Module.Basis.reindex_apply, pairIndex_right0, Module.Basis.map_apply]
    change (Submodule.prodEquivOfIsCompl U W hcompl)
      ((bU.prod bW) (Sum.inl (1 : Fin 2))) = w
    simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl', hbU1]
  have hbEs (i : Fin n) : b (Sum.inl i.succ) = (bW (Sum.inl i) : V) := by
    change (bBase.reindex (symplecticPairIndex n)) (Sum.inl i.succ) = _
    rw [Module.Basis.reindex_apply, pairIndex_left_succ, Module.Basis.map_apply]
    change (Submodule.prodEquivOfIsCompl U W hcompl)
      ((bU.prod bW) (Sum.inr (Sum.inl i))) = _
    simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hbFs (i : Fin n) : b (Sum.inr i.succ) = (bW (Sum.inr i) : V) := by
    change (bBase.reindex (symplecticPairIndex n)) (Sum.inr i.succ) = _
    rw [Module.Basis.reindex_apply, pairIndex_right_succ, Module.Basis.map_apply]
    change (Submodule.prodEquivOfIsCompl U W hcompl)
      ((bU.prod bW) (Sum.inr (Sum.inr i))) = _
    simp [Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hAlt' : B.IsAlt := hAlt
  have hskew (x y : V) : B x y = -B y x := (hAlt'.neg_eq y x).symm
  refine ⟨b, ?_, ?_, ?_, hbE0, hbF0⟩
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa [hbE0, hbF0] using hvw
      · simp only [ne_eq, eq_comm, Fin.succ_ne_zero, if_false]
        rw [hbE0, hbFs]
        exact ((bW (Sum.inr j)).property v hUmemV).symm
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.succ_ne_zero, if_false]
        rw [hbEs, hbF0, hskew]
        simp [(bW (Sum.inl i)).property w hUmemW]
      · have h := hbWcross i j
        simpa [hbEs, hbFs] using h
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hbE0]
        exact hAlt v
      · rw [hbE0, hbEs]
        exact (bW (Sum.inl j)).property v hUmemV
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hbEs, hbE0, hskew]
        simp [(bW (Sum.inl i)).property v hUmemV]
      · have h := hbWleft i j
        simpa [hbEs] using h
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hbF0]
        exact hAlt w
      · rw [hbF0, hbFs]
        simp [(bW (Sum.inr j)).property w hUmemW]
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hbFs, hbF0, hskew]
        simp [(bW (Sum.inr i)).property w hUmemW]
      · have h := hbWright i j
        simpa [hbFs] using h

/-- The linear equivalence matching two symplectic bases preserves their forms. -/
theorem symplectic_basis_equiv (n : ℕ) (B₁ B₂ : BilinForm k V)
    (b₁ b₂ : Basis (Fin n ⊕ Fin n) k V)
    (hAlt₁ : ∀ x, B₁ x x = 0) (hAlt₂ : ∀ x, B₂ x x = 0)
    (hcross₁ : ∀ i j, B₁ (b₁ (Sum.inl i)) (b₁ (Sum.inr j)) =
      if i = j then 1 else 0)
    (hleft₁ : ∀ i j, B₁ (b₁ (Sum.inl i)) (b₁ (Sum.inl j)) = 0)
    (hright₁ : ∀ i j, B₁ (b₁ (Sum.inr i)) (b₁ (Sum.inr j)) = 0)
    (hcross₂ : ∀ i j, B₂ (b₂ (Sum.inl i)) (b₂ (Sum.inr j)) =
      if i = j then 1 else 0)
    (hleft₂ : ∀ i j, B₂ (b₂ (Sum.inl i)) (b₂ (Sum.inl j)) = 0)
    (hright₂ : ∀ i j, B₂ (b₂ (Sum.inr i)) (b₂ (Sum.inr j)) = 0) :
    B₂.comp (b₁.equiv b₂ (Equiv.refl _)).toLinearMap
      (b₁.equiv b₂ (Equiv.refl _)).toLinearMap = B₁ := by
  let e := b₁.equiv b₂ (Equiv.refl _)
  have hs₁ : ∀ x y, B₁ x y = -B₁ y x := by
    intro x y
    exact ((show B₁.IsAlt from hAlt₁).neg_eq y x).symm
  have hs₂ : ∀ x y, B₂ x y = -B₂ y x := by
    intro x y
    exact ((show B₂.IsAlt from hAlt₂).neg_eq y x).symm
  change B₂.comp e.toLinearMap e.toLinearMap = B₁
  apply (LinearMap.BilinForm.ext_iff_basis b₁).2
  intro i j
  rw [LinearMap.BilinForm.comp_apply]
  have heq (i : Fin n ⊕ Fin n) : e (b₁ i) = b₂ i := by
    dsimp [e]
    exact Basis.equiv_apply b₁ i b₂ (Equiv.refl _)
  change B₂ (e (b₁ i)) (e (b₁ j)) = B₁ (b₁ i) (b₁ j)
  rw [heq i, heq j]
  cases i with
  | inl i =>
      cases j with
      | inl j => rw [hleft₁ i j, hleft₂ i j]
      | inr j => rw [hcross₁ i j, hcross₂ i j]
  | inr i =>
      cases j with
      | inl j => rw [hs₁, hs₂, hcross₁ j i, hcross₂ j i]
      | inr j => rw [hright₁ i j, hright₂ i j]

/-- Given one nonzero vector in each space of the same symplectic dimension,
there is a form-preserving linear automorphism taking the first to the second. -/
theorem exists_symplectic_equiv_sending_nonzero (n : ℕ) (B : BilinForm k V)
    [Module.Finite k V] (hAlt : ∀ x, B x x = 0) (hB : B.Nondegenerate)
    (hdim : Module.finrank k V = 2 * (n + 1)) (v e₀ : V)
    (hv : v ≠ 0) (he : e₀ ≠ 0) :
    ∃ g : V ≃ₗ[k] V,
      (∀ x y, B (g x) (g y) = B x y) ∧ g v = e₀ := by
  have findPartner (x : V) (hx : x ≠ 0) : ∃ y, B x y = 1 := by
    have hpair : ∃ y, B x y ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (hB.1 x h)
    obtain ⟨y₀, hy₀⟩ := hpair
    refine ⟨(B x y₀)⁻¹ • y₀, ?_⟩
    rw [BilinForm.smul_right]
    exact inv_mul_cancel₀ hy₀
  obtain ⟨vPartner, hvPair⟩ := findPartner v hv
  obtain ⟨ePartner, hePair⟩ := findPartner e₀ he
  obtain ⟨b₁, hc₁, hl₁, hr₁, hfirst₁, hsecond₁⟩ :=
    exists_symplectic_basis_with_pair n B hAlt hB hdim v vPartner hvPair
  obtain ⟨b₂, hc₂, hl₂, hr₂, hfirst₂, hsecond₂⟩ :=
    exists_symplectic_basis_with_pair n B hAlt hB hdim e₀ ePartner hePair
  let g : V ≃ₗ[k] V := b₁.equiv b₂ (Equiv.refl _)
  have hg := symplectic_basis_equiv (n + 1) B B b₁ b₂ hAlt hAlt
    hc₁ hl₁ hr₁ hc₂ hl₂ hr₂
  change B.comp g.toLinearMap g.toLinearMap = B at hg
  refine ⟨g, ?_, ?_⟩
  · intro x y
    have h := congrArg (fun f : BilinForm k V => f x y) hg
    simpa [LinearMap.BilinForm.comp_apply] using h
  · calc
      g v = g (b₁ (Sum.inl (0 : Fin (n + 1)))) := by rw [hfirst₁]
      _ = b₂ (Sum.inl 0) :=
        Basis.equiv_apply b₁ (Sum.inl (0 : Fin (n + 1))) b₂ (Equiv.refl _)
      _ = e₀ := hfirst₂

end Stafford38.CharacteristicPaperSymplecticBasis
