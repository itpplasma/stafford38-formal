module

public import Stafford38.Paper.Support.GabberGraded

@[expose] public section

/-!
# Good filtrations: shift comparison and independence of `√Ann gr M`

Two facts about compatible order filtrations of a right `A_n(K)`-module `M`:

* a good filtration `M_•` is dominated by every compatible exhaustive filtration
  `M'_•` up to a shift, `M_i ⊆ M'_{i+c}`;
* if two compatible filtrations dominate each other up to shifts, the radicals
  of the annihilators of their associated graded modules agree.

Hence `√(Ann_{K[x,ξ]} gr M)` does not depend on the good filtration
[HTT, Lemma D.3.1].  Both rest on writing the action of `f ∈ K[x, ξ]` on
`gr M` through finitely many `b_e ∈ F_e` (`exists_lift`).
-/

namespace Stafford38.Paper.Support.Gabber

open Stafford38.Paper.Section2
open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration

noncomputable section

universe u w w' w₁

variable {K : Type u} [Field K] {n : ℕ}
variable {M : Type w} [AddCommGroup M] [Module (PresentedWeyl K n)ᵐᵒᵖ M] [Module K M]
  [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M]

section Lift

theorem sum_range_ite {X : Type*} [AddCommMonoid X] {D₁ D : ℕ} (h : D₁ ≤ D) (g : ℕ → X) :
    ∑ e ∈ Finset.range D, (if e < D₁ then g e else 0) = ∑ e ∈ Finset.range D₁, g e := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

omit [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M] in
theorem cls_ite_smul {Γ : ℕ → Submodule K M} (p : Prop) [Decidable p] (i : ℕ)
    (a : PresentedWeyl K n) (x : M) :
    cls Γ i (MulOpposite.op (if p then a else 0) • x) =
      if p then cls Γ i (MulOpposite.op a • x) else 0 := by
  split_ifs
  · rfl
  · rw [MulOpposite.op_zero, zero_smul, cls_zero]

/-- The action of `f ∈ K[x, ξ]` on `gr M` is right multiplication by finitely
many `b_e ∈ F_e`, the same for every compatible filtration:
`f · [x]_d = Σ_{e<D} [x b_e]_{d+e}`. -/
theorem exists_lift (f : SymbolRing K n) :
    ∃ (D : ℕ) (b : ℕ → PresentedWeyl K n), (∀ e, b e ∈ orderFiltration K n e) ∧
      ∀ (Γ : ℕ → Submodule K M), IsCompatibleFiltration (orderFiltration K n) Γ →
        ∀ d x, x ∈ Γ d →
          f • cls Γ d x = ∑ e ∈ Finset.range D, cls Γ (d + e) (MulOpposite.op (b e) • x) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c =>
      refine ⟨1, fun e => if e = 0 then algebraMap K _ c else 0, ?_, ?_⟩
      · intro e
        dsimp only
        split_ifs with he
        · subst he; exact algebraMap_mem_order c
        · exact zero_mem _
      · intro Γ hΓ d x hx
        dsimp only
        rw [Finset.sum_range_one, ite_eq_left rfl, add_zero, C_smul, ← cls_smul hx]
        congr 1
        rw [← MulOpposite.algebraMap_apply, algebraMap_smul]
  | add p q hp hq =>
      obtain ⟨D₁, b₁, hb₁, h₁⟩ := hp
      obtain ⟨D₂, b₂, hb₂, h₂⟩ := hq
      refine ⟨max D₁ D₂, fun e => (if e < D₁ then b₁ e else 0) + (if e < D₂ then b₂ e else 0),
        fun e => add_mem (by split_ifs <;> simp [hb₁ e, zero_mem])
          (by split_ifs <;> simp [hb₂ e, zero_mem]), ?_⟩
      intro Γ hΓ d x hx
      have hmem : ∀ (p : Prop) [Decidable p] (b : ℕ → PresentedWeyl K n),
          (∀ e, b e ∈ orderFiltration K n e) → ∀ e,
          MulOpposite.op (if p then b e else 0) • x ∈ Γ (d + e) := by
        intro p _ b hb e
        split_ifs
        · exact hΓ.smul_mem hx (hb e)
        · simp [zero_mem]
      rw [add_smul, h₁ Γ hΓ d x hx, h₂ Γ hΓ d x hx]
      simp_rw [MulOpposite.op_add, add_smul]
      rw [Finset.sum_congr rfl fun e _ => cls_add (hmem (e < D₁) b₁ hb₁ e)
        (hmem (e < D₂) b₂ hb₂ e), Finset.sum_add_distrib]
      simp_rw [cls_ite_smul]
      rw [sum_range_ite (le_max_left _ _), sum_range_ite (le_max_right _ _)]
  | mul_X p v hp =>
      obtain ⟨D, b, hb, h⟩ := hp
      let w := orderWeight v
      refine ⟨w + D, fun e => if w ≤ e then gen K n v * b (e - w) else 0, ?_, ?_⟩
      · intro e
        dsimp only
        split_ifs with he
        · have := mul_mem_orderPiece K (gen_mem v) (hb (e - w))
          rwa [show orderWeight v + (e - w) = e by omega] at this
        · exact zero_mem _
      · intro Γ hΓ d x hx
        dsimp only
        rw [mul_smul, X_smul_cls hΓ v hx,
          h Γ hΓ _ _ (hΓ.smul_mem hx (gen_mem v)), Finset.sum_range_add]
        rw [Finset.sum_eq_zero (s := Finset.range w) (fun e he => by
          rw [ite_eq_right (by simp at he; omega), MulOpposite.op_zero, zero_smul, cls_zero]),
          zero_add]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [ite_eq_left (Nat.le_add_right _ _), show w + e - w = e by omega,
          cls_congr (show d + (w + e) = d + orderWeight v + e by omega),
          MulOpposite.op_mul, mul_smul]

#print axioms exists_lift

end Lift

section Comparison

variable {Γ Γ' : ℕ → Submodule K M}

/-- Classes `[x]_i` with `x ∈ M_i ∩ M'_{i+c}`. -/
def boundedSpan (Γ Γ' : ℕ → Submodule K M) (c : ℕ) : Submodule K (GrModule Γ) :=
  Submodule.span K {z | ∃ i x, x ∈ Γ i ∧ x ∈ Γ' (i + c) ∧ z = cls Γ i x}

theorem symbol_smul_mem_boundedSpan (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
    (hΓ' : IsCompatibleFiltration (orderFiltration K n) Γ') (c : ℕ) (f : SymbolRing K n)
    {z : GrModule Γ} (hz : z ∈ boundedSpan Γ Γ' c) : f • z ∈ boundedSpan Γ Γ' c := by
  obtain ⟨D, b, hb, hlift⟩ := exists_lift (M := M) f
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, x, hx, hx', rfl⟩ := hz
      rw [hlift Γ hΓ i x hx]
      refine Submodule.sum_mem _ fun e _ => Submodule.subset_span ⟨i + e, _,
        hΓ.smul_mem hx (hb e), ?_, rfl⟩
      have := hΓ'.smul_mem hx' (hb e)
      rwa [show i + c + e = i + e + c by omega] at this
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b' _ _ ha hb' => rw [smul_add]; exact add_mem ha hb'
  | smul a z _ hz =>
      rw [smul_def, map_smul, ← smul_def]
      exact Submodule.smul_mem _ a hz

omit [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M] in
theorem boundedSpan_mono {c c' : ℕ} (hΓ' : IsCompatibleFiltration (orderFiltration K n) Γ')
    (h : c ≤ c') : boundedSpan Γ Γ' c ≤ boundedSpan Γ Γ' c' := by
  apply Submodule.span_mono
  rintro _ ⟨i, x, hx, hx', rfl⟩
  exact ⟨i, x, hx, hΓ'.mono (by omega) hx', rfl⟩

omit [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M] in
theorem exists_mem_boundedSpan (hΓ' : IsCompatibleFiltration (orderFiltration K n) Γ')
    (z : GrModule Γ) : ∃ c, z ∈ boundedSpan Γ Γ' c := by
  induction z using gr_induction with
  | h0 => exact ⟨0, zero_mem _⟩
  | hcls i x hx =>
      obtain ⟨e, he⟩ := hΓ'.exhaustive x
      exact ⟨e, Submodule.subset_span ⟨i, x, hx, hΓ'.mono (by omega) he, rfl⟩⟩
  | hadd a b ha hb =>
      obtain ⟨c₁, h₁⟩ := ha
      obtain ⟨c₂, h₂⟩ := hb
      exact ⟨max c₁ c₂, add_mem (boundedSpan_mono hΓ' (le_max_left _ _) h₁)
        (boundedSpan_mono hΓ' (le_max_right _ _) h₂)⟩

theorem ev_of_mem_boundedSpan {c : ℕ} {z : GrModule Γ} (hz : z ∈ boundedSpan Γ Γ' c)
    (j : ℕ) : ∃ y ∈ Γ' (j + c), ev Γ j z = Submodule.Quotient.mk y := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, x, hx, hx', rfl⟩ := hz
      rw [ev_cls j hx]
      split_ifs with hij
      · subst hij; exact ⟨x, hx', rfl⟩
      · exact ⟨0, zero_mem _, (Submodule.Quotient.mk_zero _).symm⟩
  | zero => exact ⟨0, zero_mem _, by rw [map_zero, Submodule.Quotient.mk_zero]⟩
  | add a b _ _ ha hb =>
      obtain ⟨y₁, hy₁, e₁⟩ := ha
      obtain ⟨y₂, hy₂, e₂⟩ := hb
      exact ⟨y₁ + y₂, add_mem hy₁ hy₂, by rw [map_add, e₁, e₂, Submodule.Quotient.mk_add]⟩
  | smul a z _ hz =>
      obtain ⟨y, hy, e⟩ := hz
      exact ⟨a • y, Submodule.smul_mem _ a hy, by rw [map_smul, e, Submodule.Quotient.mk_smul]⟩

/-- A good filtration is dominated, up to a shift, by every compatible
exhaustive filtration: `M_i ⊆ M'_{i+c}`. -/
theorem exists_shift_le (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
    (hgood : Module.Finite (SymbolRing K n) (GrModule Γ))
    (hΓ' : IsCompatibleFiltration (orderFiltration K n) Γ') :
    ∃ c, ∀ i, Γ i ≤ Γ' (i + c) := by
  classical
  obtain ⟨s, hs⟩ := hgood.fg_top
  choose cz hcz using exists_mem_boundedSpan (Γ := Γ) hΓ'
  let C := s.sup cz
  let W : Submodule (SymbolRing K n) (GrModule Γ) :=
    { boundedSpan Γ Γ' C with
      smul_mem' := fun f _ hz => symbol_smul_mem_boundedSpan hΓ hΓ' C f hz }
  have htop : W = ⊤ := by
    rw [eq_top_iff, ← hs, Submodule.span_le]
    intro z hz
    exact boundedSpan_mono hΓ' (Finset.le_sup (f := cz) hz) (hcz z)
  refine ⟨C, fun i => ?_⟩
  induction i with
  | zero =>
      intro x hx
      have hmem : cls Γ 0 x ∈ W := htop ▸ Submodule.mem_top
      obtain ⟨y, hy, hev⟩ := ev_of_mem_boundedSpan hmem 0
      rw [ev_cls 0 hx, ite_eq_left rfl, Submodule.Quotient.eq] at hev
      have : x = y := sub_eq_zero.mp ((Submodule.mem_bot K).mp hev)
      rwa [this]
  | succ i ih =>
      intro x hx
      have hmem : cls Γ (i + 1) x ∈ W := htop ▸ Submodule.mem_top
      obtain ⟨y, hy, hev⟩ := ev_of_mem_boundedSpan hmem (i + 1)
      rw [ev_cls _ hx, ite_eq_left rfl, Submodule.Quotient.eq] at hev
      have hlow : x - y ∈ Γ' (i + C) := ih hev
      have : x = (x - y) + y := by abel
      rw [this]
      exact add_mem (hΓ'.mono (by omega) hlow) hy

#print axioms exists_shift_le

end Comparison

section Independence

variable {Γ Γ' : ℕ → Submodule K M}

/-- `M_z` for an integer index `z`, zero for `z < 0`. -/
def zPiece (Γ : ℕ → Submodule K M) (z : ℤ) : Submodule K M :=
  if 0 ≤ z then Γ z.toNat else ⊥

theorem zPiece_nat (i : ℕ) : zPiece Γ i = Γ i := by
  simp [zPiece]

theorem lowerPiece_eq_zPiece (i : ℕ) : lowerPiece Γ i = zPiece Γ ((i : ℤ) - 1) := by
  cases i with
  | zero => simp [lowerPiece, zPiece]
  | succ i =>
      simp only [lowerPiece, zPiece]
      rw [ite_eq_left (by omega)]
      congr 1
      omega

theorem zPiece_le_shift {c : ℕ} (h : ∀ i, Γ' i ≤ Γ (i + c)) (z : ℤ) :
    zPiece Γ' z ≤ zPiece Γ (z + c) := by
  unfold zPiece
  split_ifs with h₁ h₂
  · have := h z.toNat
    rwa [show z.toNat + c = (z + c).toNat by omega] at this
  · omega
  · exact bot_le
  · exact bot_le

/-- The classes `[x]_j`, `x ∈ M'_j ∩ M_{j+c-N}`. -/
def loweredSpan (Γ Γ' : ℕ → Submodule K M) (c : ℕ) (N : ℕ) : Submodule K (GrModule Γ') :=
  Submodule.span K {z | ∃ j x, x ∈ Γ' j ∧ x ∈ zPiece Γ ((j : ℤ) + c - N) ∧ z = cls Γ' j x}

/-- If `M'_i ⊆ M_{i+c}` and `M_i ⊆ M'_{i+c'}`, then
`Ann gr_M ⊆ √(Ann gr_{M'})`. -/
theorem annihilator_le_radical (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
    (hΓ' : IsCompatibleFiltration (orderFiltration K n) Γ') {c c' : ℕ}
    (h₁ : ∀ i, Γ' i ≤ Γ (i + c)) (h₂ : ∀ i, Γ i ≤ Γ' (i + c')) :
    Module.annihilator (SymbolRing K n) (GrModule Γ) ≤
      (Module.annihilator (SymbolRing K n) (GrModule Γ')).radical := by
  intro f hf
  obtain ⟨D, b, hb, hlift⟩ := exists_lift (M := M) f
  -- `f` annihilates `gr_M`, so every `b_e` lowers the `M`-degree by one.
  have hlower : ∀ e, e < D → ∀ (z : ℤ) x, x ∈ zPiece Γ z →
      MulOpposite.op (b e) • x ∈ zPiece Γ (z + e - 1) := by
    intro e he z x hx
    by_cases hz : 0 ≤ z
    · have hx' : x ∈ Γ z.toNat := by simpa [zPiece, hz] using hx
      have hzero := (Module.mem_annihilator.mp hf) (cls Γ z.toNat x)
      rw [hlift Γ hΓ _ x hx'] at hzero
      have hev := congrArg (ev Γ (z.toNat + e)) hzero
      rw [map_sum, map_zero, Finset.sum_eq_single e] at hev
      · rw [ev_cls _ (hΓ.smul_mem hx' (hb e)), ite_eq_left rfl,
          Submodule.Quotient.mk_eq_zero, lowerPiece_eq_zPiece] at hev
        convert hev using 2
        omega
      · intro e' _ he'
        rw [ev_cls _ (hΓ.smul_mem hx' (hb e')), ite_eq_right (by omega)]
      · intro h; exact absurd (Finset.mem_range.mpr he) h
    · have : x = 0 := by simpa [zPiece, hz] using hx
      subst this
      rw [smul_zero]
      exact zero_mem _
  have hstep : ∀ N, ∀ z ∈ loweredSpan Γ Γ' c N, f • z ∈ loweredSpan Γ Γ' c (N + 1) := by
    intro N z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨j, x, hx', hx, rfl⟩ := hz
        rw [hlift Γ' hΓ' j x hx']
        refine Submodule.sum_mem _ fun e he => Submodule.subset_span
          ⟨j + e, _, hΓ'.smul_mem hx' (hb e), ?_, rfl⟩
        have := hlower e (Finset.mem_range.mp he) _ x hx
        convert this using 2
        push_cast
        ring
    | zero => rw [smul_zero]; exact zero_mem _
    | add a b' _ _ ha hb' => rw [smul_add]; exact add_mem ha hb'
    | smul a z _ hz =>
        rw [smul_def, map_smul, ← smul_def]
        exact Submodule.smul_mem _ a hz
  have hpow : ∀ N d x, x ∈ Γ' d → f ^ N • cls Γ' d x ∈ loweredSpan Γ Γ' c N := by
    intro N
    induction N with
    | zero =>
        intro d x hx
        rw [pow_zero, one_smul]
        refine Submodule.subset_span ⟨d, x, hx, ?_, rfl⟩
        rw [show (d : ℤ) + c - ((0 : ℕ) : ℤ) = ((d + c : ℕ) : ℤ) by push_cast; ring, zPiece_nat]
        exact h₁ d hx
    | succ N ih =>
        intro d x hx
        rw [pow_succ', mul_smul]
        exact hstep N _ (ih d x hx)
  have hvanish : ∀ z ∈ loweredSpan Γ Γ' c (c + c' + 1), z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨j, x, hx', hx, rfl⟩ := hz
        apply cls_eq_zero_of_mem_lower
        rw [lowerPiece_eq_zPiece]
        have := zPiece_le_shift h₂ _ hx
        convert this using 2
        push_cast
        ring
    | zero => rfl
    | add a b _ _ ha hb => rw [ha, hb, add_zero]
    | smul a z _ hz => rw [hz, smul_zero]
  refine ⟨c + c' + 1, ?_⟩
  rw [Module.mem_annihilator]
  intro z
  induction z using gr_induction with
  | h0 => exact smul_zero _
  | hcls d x hx => exact hvanish _ (hpow _ d x hx)
  | hadd a b ha hb => rw [smul_add, ha, hb, add_zero]

/-- Shift-comparable compatible filtrations have the same `√(Ann gr M)`. -/
theorem radical_annihilator_eq_of_shift (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
    (hΓ' : IsCompatibleFiltration (orderFiltration K n) Γ') {c c' : ℕ}
    (h₁ : ∀ i, Γ' i ≤ Γ (i + c)) (h₂ : ∀ i, Γ i ≤ Γ' (i + c')) :
    (Module.annihilator (SymbolRing K n) (GrModule Γ)).radical =
      (Module.annihilator (SymbolRing K n) (GrModule Γ')).radical :=
  le_antisymm (Ideal.radical_le_radical_iff.mpr (annihilator_le_radical hΓ hΓ' h₁ h₂))
    (Ideal.radical_le_radical_iff.mpr (annihilator_le_radical hΓ' hΓ h₂ h₁))

/-- **`√(Ann gr M)` is independent of the good filtration** [HTT, Lemma D.3.1]. -/
theorem radical_annihilator_eq_of_good (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
    (hΓ' : IsCompatibleFiltration (orderFiltration K n) Γ')
    (hgood : Module.Finite (SymbolRing K n) (GrModule Γ))
    (hgood' : Module.Finite (SymbolRing K n) (GrModule Γ')) :
    (Module.annihilator (SymbolRing K n) (GrModule Γ)).radical =
      (Module.annihilator (SymbolRing K n) (GrModule Γ')).radical := by
  obtain ⟨c, hc⟩ := exists_shift_le hΓ' hgood' hΓ
  obtain ⟨c', hc'⟩ := exists_shift_le hΓ hgood hΓ'
  exact radical_annihilator_eq_of_shift hΓ hΓ' hc hc'

#print axioms radical_annihilator_eq_of_shift
#print axioms radical_annihilator_eq_of_good

end Independence

end

end Stafford38.Paper.Support.Gabber
