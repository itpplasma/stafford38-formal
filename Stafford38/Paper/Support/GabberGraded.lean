module

public import Stafford38.Paper.Section2.Filtration
public import Stafford38.Characteristic.CommutingPolynomialAction

@[expose] public section

/-!
# The associated graded `k[x, ξ]`-module of a filtered right `A_n(K)`-module

For a right `A_n(K)`-module `M` with a compatible order filtration `M_•`
(Definition 2.4, `IsCompatibleFiltration`), `gr M = ⊕_i M_i/M_{i-1}` (`gr`)
is a module over `gr A_n = K[x, ξ]`: the variable `x_j` acts by right
multiplication with the generator `x_j ∈ F_0` and `ξ_j` by right
multiplication with `∂_j ∈ F_1`, each raising the degree by its order weight.
The two actions commute on `gr M` because the commutators of the generators
are scalars, of lower order.
-/

namespace Stafford38.Paper.Support.Gabber

open Stafford38.Paper.Section2
open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration
open Stafford38.WeylPBW
open Stafford38.EulerSurjectivity

noncomputable section

universe u v w w' w₁

section Generators

variable (K : Type u) [Field K] (n : ℕ)

/-- The generator `x_j` (`v = inl j`) or `∂_j` (`v = inr j`) of `A_n(K)`. -/
abbrev gen (v : PhaseVar n) : PresentedWeyl K n :=
  Stafford38Challenge.generator K n v

variable {K n}

theorem gen_mem (v : PhaseVar n) : gen K n v ∈ orderFiltration K n (orderWeight v) := by
  change Stafford.freeWeylGenerator (Matrix.J (Fin n) K) v ∈ orderPiece K n (orderWeight v)
  rw [orderPiece, mem_presentedWeightPiece, presentedNormalFormLinearEquiv_generator]
  intro m hm
  simp only [MvPolynomial.coeff_X] at hm
  split at hm
  · subst m
    simp [monomialWeight]
  · exact absurd rfl hm

theorem gen_commutator (v w : PhaseVar n) :
    gen K n v * gen K n w - gen K n w * gen K n v =
      algebraMap K (PresentedWeyl K n) (Matrix.J (Fin n) K v w) := by
  have h := RingQuot.mkAlgHom_rel K
    (s := Stafford.freeWeylRelation (Matrix.J (Fin n) K)) ⟨v, w, rfl, rfl⟩
  rw [map_sub, map_mul, map_mul, AlgHom.commutes] at h
  exact h

theorem algebraMap_mem_order (c : K) :
    algebraMap K (PresentedWeyl K n) c ∈ orderFiltration K n 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ c (orderPieceOne (n := n) K).property

/-- The commutator of two generators lies in `F_{w(v)+w(w)-1}`; for two
coordinates it is zero. -/
theorem gen_commutator_mem_lower (v w : PhaseVar n) :
    gen K n v * gen K n w - gen K n w * gen K n v ∈
      lowerPiece (orderFiltration K n) (orderWeight v + orderWeight w) := by
  rw [gen_commutator]
  have hmono := (isFiltration_order K n).mono
  rcases v with a | a <;> rcases w with b | b
  · simp [Matrix.J, orderWeight, fibreWeight, lowerPiece]
  · exact algebraMap_mem_order _
  · exact algebraMap_mem_order _
  · exact hmono (Nat.zero_le 1) (algebraMap_mem_order _)

end Generators

section Construction

variable {K : Type u} [Field K] {n : ℕ}
variable {M : Type w} [AddCommGroup M] [Module (PresentedWeyl K n)ᵐᵒᵖ M] [Module K M]
  [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M]

/-- `gr M = ⊕_i M_i/M_{i-1}` with its `K[x, ξ]`-module structure (below). -/
def GrModule (Γ : ℕ → Submodule K M) : Type w := gr Γ

instance (Γ : ℕ → Submodule K M) : AddCommGroup (GrModule Γ) :=
  inferInstanceAs (AddCommGroup (gr Γ))

instance (Γ : ℕ → Submodule K M) : Module K (GrModule Γ) :=
  inferInstanceAs (Module K (gr Γ))

open scoped Classical in
/-- The class of `x` in `M_i/M_{i-1}` (zero when `x ∉ M_i`). -/
def cls (Γ : ℕ → Submodule K M) (i : ℕ) (x : M) : GrModule Γ :=
  if h : x ∈ Γ i then DirectSum.of (grPiece Γ) i (Submodule.Quotient.mk ⟨x, h⟩) else 0

variable {Γ : ℕ → Submodule K M}

theorem cls_of_mem {i : ℕ} {x : M} (h : x ∈ Γ i) :
    cls Γ i x = DirectSum.of (grPiece Γ) i (Submodule.Quotient.mk ⟨x, h⟩) := by
  unfold cls
  exact dite_eq_left h

theorem cls_add {i : ℕ} {x y : M} (hx : x ∈ Γ i) (hy : y ∈ Γ i) :
    cls Γ i (x + y) = cls Γ i x + cls Γ i y := by
  rw [cls_of_mem hx, cls_of_mem hy, cls_of_mem (add_mem hx hy)]
  change _ = DirectSum.of (grPiece Γ) i _ + DirectSum.of (grPiece Γ) i _
  rw [← map_add]
  rfl

theorem cls_smul {i : ℕ} {x : M} (hx : x ∈ Γ i) (c : K) :
    cls Γ i (c • x) = c • cls Γ i x := by
  rw [cls_of_mem hx, cls_of_mem (Submodule.smul_mem _ c hx)]
  change DirectSum.lof K ℕ (grPiece Γ) i _ = c • DirectSum.lof K ℕ (grPiece Γ) i _
  rw [← map_smul]
  rfl

theorem cls_zero (i : ℕ) : cls Γ i (0 : M) = 0 := by
  rw [cls_of_mem (zero_mem _)]
  exact (DirectSum.of (grPiece Γ) i).map_zero

theorem cls_neg {i : ℕ} {x : M} (hx : x ∈ Γ i) : cls Γ i (-x) = -cls Γ i x := by
  have h := cls_add hx (neg_mem hx)
  rw [add_neg_cancel, cls_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem cls_sub {i : ℕ} {x y : M} (hx : x ∈ Γ i) (hy : y ∈ Γ i) :
    cls Γ i (x - y) = cls Γ i x - cls Γ i y := by
  rw [sub_eq_add_neg, cls_add hx (neg_mem hy), cls_neg hy, ← sub_eq_add_neg]

theorem cls_eq_zero_of_mem_lower {i : ℕ} {x : M} (h : x ∈ lowerPiece Γ i) :
    cls Γ i x = 0 := by
  by_cases hx : x ∈ Γ i
  · have h0 : (Submodule.Quotient.mk ⟨x, hx⟩ : grPiece Γ i) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr h
    rw [cls_of_mem hx, h0, map_zero]
    rfl
  · unfold cls
    exact dite_eq_right hx

/-- `gr M` is spanned by the classes `cls i x`, `x ∈ M_i`. -/
theorem gr_induction {P : GrModule Γ → Prop} (z : GrModule Γ) (h0 : P 0)
    (hcls : ∀ i x, x ∈ Γ i → P (cls Γ i x)) (hadd : ∀ a b, P a → P b → P (a + b)) : P z := by
  change gr Γ at z
  induction z using DirectSum.induction_on with
  | zero => exact h0
  | of i y =>
      induction y using Submodule.Quotient.induction_on with
      | H y =>
          obtain ⟨x, hx⟩ := y
          have := hcls i x hx
          rwa [cls_of_mem hx] at this
  | add a b ha hb => exact hadd a b ha hb

theorem gr_ext {X : Type*} [AddCommGroup X] [Module K X] {f g : GrModule Γ →ₗ[K] X}
    (h : ∀ i x, x ∈ Γ i → f (cls Γ i x) = g (cls Γ i x)) : f = g := by
  ext z
  induction z using gr_induction with
  | h0 => simp
  | hcls i x hx => exact h i x hx
  | hadd a b ha hb => rw [map_add, map_add, ha, hb]

/-- Evaluation at degree `j`: `gr M → M/M_{j-1}`, the `j`-th component. -/
def ev (Γ : ℕ → Submodule K M) (j : ℕ) : GrModule Γ →ₗ[K] M ⧸ lowerPiece Γ j :=
  (Submodule.mapQ _ _ (Γ j).subtype le_rfl).comp (DirectSum.component K ℕ (grPiece Γ) j)

theorem ev_cls (j : ℕ) {i : ℕ} {x : M} (hx : x ∈ Γ i) :
    ev Γ j (cls Γ i x) = if i = j then Submodule.Quotient.mk x else 0 := by
  rw [cls_of_mem hx]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    change Submodule.mapQ _ _ (Γ i).subtype le_rfl
      (DirectSum.component K ℕ (grPiece Γ) i (DirectSum.lof K ℕ (grPiece Γ) i _)) = _
    rw [DirectSum.component.lof_self]
    rfl
  · rw [ite_eq_right hij]
    change Submodule.mapQ _ _ (Γ j).subtype le_rfl
      (DirectSum.component K ℕ (grPiece Γ) j (DirectSum.lof K ℕ (grPiece Γ) i _)) = _
    rw [DirectSum.component.of, dite_eq_right hij, map_zero]

theorem cls_congr {i j : ℕ} (h : i = j) (x : M) : cls Γ i x = cls Γ j x := by
  subst h; rfl

/-- The degree-`i` component `gr M → M_i/M_{i-1}`. -/
def comp (Γ : ℕ → Submodule K M) (i : ℕ) : GrModule Γ →ₗ[K] grPiece Γ i :=
  DirectSum.component K ℕ (grPiece Γ) i

/-- The inclusion `M_i/M_{i-1} → gr M`. -/
def ofG (Γ : ℕ → Submodule K M) (i : ℕ) : grPiece Γ i →ₗ[K] GrModule Γ :=
  DirectSum.lof K ℕ (grPiece Γ) i

theorem ext_comp {z₁ z₂ : GrModule Γ} (h : ∀ i, comp Γ i z₁ = comp Γ i z₂) : z₁ = z₂ :=
  DirectSum.ext_component K h

open scoped Classical in
theorem sum_ofG_comp (z : GrModule Γ) :
    ∃ s : Finset ℕ, z = ∑ i ∈ s, ofG Γ i (comp Γ i z) :=
  ⟨DFinsupp.support (show gr Γ from z), (DirectSum.sum_support_of (show gr Γ from z)).symm⟩

variable (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
include hΓ

omit [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M] in
theorem smul_mem_lowerPiece {i j : ℕ} {x : M} {a : PresentedWeyl K n} (hx : x ∈ Γ i)
    (ha : a ∈ lowerPiece (orderFiltration K n) j) :
    MulOpposite.op a • x ∈ lowerPiece Γ (i + j) := by
  cases j with
  | zero =>
      have : a = 0 := (Submodule.mem_bot K).mp ha
      subst this
      simp [MulOpposite.op_zero, zero_smul, zero_mem]
  | succ j => exact hΓ.smul_mem hx ha

omit [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M] in
theorem lowerPiece_smul_mem {i j : ℕ} {x : M} {a : PresentedWeyl K n}
    (hx : x ∈ lowerPiece Γ i) (ha : a ∈ orderFiltration K n j) :
    MulOpposite.op a • x ∈ lowerPiece Γ (i + j) := by
  cases i with
  | zero =>
      have : x = 0 := (Submodule.mem_bot K).mp hx
      subst this
      simp [smul_zero, zero_mem]
  | succ i =>
      rw [show i + 1 + j = (i + j) + 1 by omega]
      exact hΓ.smul_mem hx ha

omit hΓ in
/-- Right multiplication by `a` as a `K`-linear map of `M`. -/
def actL (a : PresentedWeyl K n) : M →ₗ[K] M where
  toFun x := MulOpposite.op a • x
  map_add' x y := smul_add _ x y
  map_smul' c x := (smul_comm c (MulOpposite.op a) x).symm

/-- Right multiplication by `a ∈ F_j`, from `M_i/M_{i-1}` to `M_{i+j}/M_{i+j-1}`. -/
def pieceShift {a : PresentedWeyl K n} {j : ℕ} (ha : a ∈ orderFiltration K n j) (i : ℕ) :
    grPiece Γ i →ₗ[K] grPiece Γ (i + j) :=
  Submodule.mapQ _ _ ((actL a).restrict (p := Γ i) (q := Γ (i + j))
    fun _ hx => hΓ.smul_mem hx ha) (by
      rintro ⟨x, hx⟩ hlow
      exact lowerPiece_smul_mem hΓ hlow ha)

/-- Right multiplication by `a ∈ F_j` on `gr M`, raising degrees by `j`. -/
def shiftOp {a : PresentedWeyl K n} {j : ℕ} (ha : a ∈ orderFiltration K n j) :
    GrModule Γ →ₗ[K] GrModule Γ :=
  DirectSum.toModule K ℕ (gr Γ) fun i =>
    (DirectSum.lof K ℕ (grPiece Γ) (i + j)).comp (pieceShift hΓ ha i)

theorem shiftOp_cls {a : PresentedWeyl K n} {j : ℕ} (ha : a ∈ orderFiltration K n j)
    {i : ℕ} {x : M} (hx : x ∈ Γ i) :
    shiftOp hΓ ha (cls Γ i x) = cls Γ (i + j) (MulOpposite.op a • x) := by
  rw [cls_of_mem hx, cls_of_mem (hΓ.smul_mem hx ha)]
  change DirectSum.toModule K ℕ (gr Γ) _ (DirectSum.lof K ℕ (grPiece Γ) i _) = _
  rw [DirectSum.toModule_lof]
  rfl

/-- `T_v`: right multiplication by the generator `v` on `gr M`. -/
def genOp (v : PhaseVar n) : GrModule Γ →ₗ[K] GrModule Γ :=
  shiftOp hΓ (gen_mem v)

theorem genOp_cls (v : PhaseVar n) {i : ℕ} {x : M} (hx : x ∈ Γ i) :
    genOp hΓ v (cls Γ i x) =
      cls Γ (i + orderWeight v) (MulOpposite.op (gen K n v) • x) :=
  shiftOp_cls hΓ _ hx

/-- On `gr M` the generators commute: their commutators are scalars, which
lower the degree. -/
theorem genOp_commute (v w : PhaseVar n) : Commute (genOp hΓ v) (genOp hΓ w) := by
  change genOp hΓ v * genOp hΓ w = genOp hΓ w * genOp hΓ v
  apply gr_ext
  intro i x hx
  have hw := hΓ.smul_mem hx (gen_mem w)
  have hv := hΓ.smul_mem hx (gen_mem v)
  have hvw := hΓ.smul_mem hw (gen_mem v)
  have hwv := hΓ.smul_mem hv (gen_mem w)
  rw [Module.End.mul_apply, Module.End.mul_apply, genOp_cls hΓ w hx, genOp_cls hΓ v hw,
    genOp_cls hΓ v hx, genOp_cls hΓ w hv,
    cls_congr (show i + orderWeight v + orderWeight w = i + orderWeight w + orderWeight v by
      omega), ← sub_eq_zero, ← cls_sub hvw (by rwa [show i + orderWeight w + orderWeight v =
        i + orderWeight v + orderWeight w by omega])]
  apply cls_eq_zero_of_mem_lower
  have hcomm := smul_mem_lowerPiece hΓ hx (gen_commutator_mem_lower w v)
  rw [← add_assoc] at hcomm
  convert hcomm using 1
  rw [MulOpposite.op_sub, sub_smul, MulOpposite.op_mul, MulOpposite.op_mul, mul_smul, mul_smul]

end Construction

section Action

variable {K : Type u} [Field K] {n : ℕ}
variable {M : Type w} [AddCommGroup M] [Module (PresentedWeyl K n)ᵐᵒᵖ M] [Module K M]
  [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M]
variable (Γ : ℕ → Submodule K M)

open scoped Classical in
/-- The action of the variable `v` on `gr M` (`T_v` for a compatible filtration). -/
def genAct (v : PhaseVar n) : Module.End K (GrModule Γ) :=
  if hΓ : IsCompatibleFiltration (orderFiltration K n) Γ then genOp hΓ v else 0

theorem genAct_commute (v w : PhaseVar n) : Commute (genAct Γ v) (genAct Γ w) := by
  unfold genAct
  split_ifs with h
  · exact genOp_commute h v w
  · exact Commute.zero_left _

/-- `K[x, ξ] → End_K(gr M)`, sending `x_j, ξ_j` to `T_{x_j}, T_{ξ_j}`. -/
def symbolAction : SymbolRing K n →ₐ[K] Module.End K (GrModule Γ) :=
  commutingPolynomialAction (genAct Γ) (genAct_commute Γ)

/-- **Definition 2.4 (`gr M` as a `gr A_n = K[x, ξ]`-module).** -/
instance : Module (SymbolRing K n) (GrModule Γ) :=
  Module.compHom (GrModule Γ) (symbolAction Γ).toRingHom

variable {Γ}

theorem smul_def (f : SymbolRing K n) (z : GrModule Γ) : f • z = symbolAction Γ f z :=
  rfl

instance : IsScalarTower K (SymbolRing K n) (GrModule Γ) :=
  ⟨fun c f z => by
    rw [smul_def, smul_def, map_smul]
    rfl⟩

theorem X_smul_cls (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ) (v : PhaseVar n)
    {i : ℕ} {x : M} (hx : x ∈ Γ i) :
    (MvPolynomial.X v : SymbolRing K n) • cls Γ i x =
      cls Γ (i + orderWeight v) (MulOpposite.op (gen K n v) • x) := by
  rw [smul_def, symbolAction, commutingPolynomialAction_apply_X, genAct, dite_eq_left hΓ,
    genOp_cls hΓ v hx]

theorem C_smul (c : K) (z : GrModule Γ) :
    (MvPolynomial.C c : SymbolRing K n) • z = c • z := by
  rw [smul_def, symbolAction, commutingPolynomialAction_apply_C]
  rfl

#print axioms X_smul_cls

end Action

section Functoriality

variable {K : Type u} [Field K] {n : ℕ}
variable {M : Type w} [AddCommGroup M] [Module (PresentedWeyl K n)ᵐᵒᵖ M] [Module K M]
  [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M]
variable {M' : Type w'} [AddCommGroup M'] [Module (PresentedWeyl K n)ᵐᵒᵖ M'] [Module K M']
  [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M']
variable {Γ : ℕ → Submodule K M} {Γ' : ℕ → Submodule K M'}
variable (φ : M →ₗ[(PresentedWeyl K n)ᵐᵒᵖ] M') (hφ : ∀ i, ∀ x ∈ Γ i, φ x ∈ Γ' i)

omit [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M]
  [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M'] in
include hφ in
theorem map_mem_lowerPiece {i : ℕ} {x : M} (hx : x ∈ lowerPiece Γ i) :
    φ x ∈ lowerPiece Γ' i := by
  cases i with
  | zero =>
      have : x = 0 := (Submodule.mem_bot K).mp hx
      subst this
      simp [zero_mem]
  | succ i => exact hφ i x hx

/-- `M_i/M_{i-1} → M'_i/M'_{i-1}` induced by a filtered map. -/
def pieceMap (i : ℕ) : grPiece Γ i →ₗ[K] grPiece Γ' i :=
  Submodule.mapQ _ _ ((φ.restrictScalars K).restrict (p := Γ i) (q := Γ' i) (hφ i)) (by
    rintro ⟨x, hx⟩ hlow
    exact map_mem_lowerPiece φ hφ hlow)

/-- `gr φ : gr M → gr M'`. -/
def grMap : GrModule Γ →ₗ[K] GrModule Γ' :=
  DFinsupp.mapRange.linearMap (pieceMap φ hφ)

theorem grMap_apply (z : GrModule Γ) (i : ℕ) :
    comp Γ' i (grMap φ hφ z) = pieceMap φ hφ i (comp Γ i z) :=
  DFinsupp.mapRange_apply _ (fun i => (pieceMap φ hφ i).map_zero) _ _

theorem grMap_cls {i : ℕ} {x : M} (hx : x ∈ Γ i) :
    grMap φ hφ (cls Γ i x) = cls Γ' i (φ x) := by
  rw [cls_of_mem hx, cls_of_mem (hφ i x hx)]
  change DFinsupp.mapRange (fun i => pieceMap φ hφ i) (fun i => (pieceMap φ hφ i).map_zero)
    (DFinsupp.single i _) = DFinsupp.single i _
  rw [DFinsupp.mapRange_single]
  rfl

theorem grMap_smul (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
    (hΓ' : IsCompatibleFiltration (orderFiltration K n) Γ') (f : SymbolRing K n)
    (z : GrModule Γ) : grMap φ hφ (f • z) = f • grMap φ hφ z := by
  have h := commutingPolynomialAction_intertwines (genAct Γ) (genAct Γ') (genAct_commute Γ)
    (genAct_commute Γ') (grMap φ hφ) (fun v => by
      apply gr_ext
      intro i x hx
      simp only [LinearMap.comp_apply, genAct, dite_eq_left hΓ, dite_eq_left hΓ']
      rw [genOp_cls hΓ v hx, grMap_cls φ hφ (hΓ.smul_mem hx (gen_mem v)), grMap_cls φ hφ hx,
        genOp_cls hΓ' v (hφ i x hx), map_smul]) f
  exact congrArg (fun g => g z) h

/-- `gr φ` as a `K[x, ξ]`-linear map. -/
def grMapS (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
    (hΓ' : IsCompatibleFiltration (orderFiltration K n) Γ') :
    GrModule Γ →ₗ[SymbolRing K n] GrModule Γ' where
  toFun := grMap φ hφ
  map_add' := map_add _
  map_smul' := grMap_smul φ hφ hΓ hΓ'

end Functoriality

section SubQuotient

variable {K : Type u} [Field K] {n : ℕ}
variable {M : Type w} [AddCommGroup M] [Module (PresentedWeyl K n)ᵐᵒᵖ M] [Module K M]
  [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M]
variable {M₁ : Type w₁} [AddCommGroup M₁] [Module (PresentedWeyl K n)ᵐᵒᵖ M₁] [Module K M₁]
  [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M₁]
variable (Γ : ℕ → Submodule K M) (ι : M₁ →ₗ[(PresentedWeyl K n)ᵐᵒᵖ] M)

/-- The filtration `ι⁻¹(M_i)` induced on a submodule `ι : M₁ ↪ M`. -/
def subFilt (i : ℕ) : Submodule K M₁ :=
  (Γ i).comap (ι.restrictScalars K)

/-- The image filtration `(M_i + N)/N` on the quotient `M/N`, `N = ι(M₁)`. -/
def quotFilt (i : ℕ) : Submodule K (M ⧸ LinearMap.range ι) :=
  (Γ i).map ((LinearMap.range ι).mkQ.restrictScalars K)

variable {Γ ι}

theorem subFilt_isCompatible (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ) :
    IsCompatibleFiltration (orderFiltration K n) (subFilt Γ ι) where
  mono _ _ h _ hx := hΓ.mono h hx
  smul_mem := by
    intro i j x a hx ha
    change ι (MulOpposite.op a • x) ∈ Γ (i + j)
    rw [map_smul]
    exact hΓ.smul_mem hx ha
  exhaustive x := hΓ.exhaustive (ι x)

omit [Module K M₁] [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M₁] in
theorem quotFilt_isCompatible (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ) :
    IsCompatibleFiltration (orderFiltration K n) (quotFilt Γ ι) where
  mono _ _ h := Submodule.map_mono (hΓ.mono h)
  smul_mem := by
    rintro i j _ a ⟨x, hx, rfl⟩ ha
    exact ⟨MulOpposite.op a • x, hΓ.smul_mem hx ha, by simp⟩
  exhaustive y := by
    obtain ⟨x, rfl⟩ := (LinearMap.range ι).mkQ_surjective y
    obtain ⟨i, hi⟩ := hΓ.exhaustive x
    exact ⟨i, x, hi, rfl⟩

theorem subFilt_map : ∀ i, ∀ x ∈ subFilt Γ ι i, ι x ∈ Γ i :=
  fun _ _ h => h

omit [Module K M₁] [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M₁] in
theorem quotFilt_map : ∀ i, ∀ x ∈ Γ i, (LinearMap.range ι).mkQ x ∈ quotFilt Γ ι i :=
  fun _ x h => ⟨x, h, rfl⟩

theorem mem_lowerPiece_subFilt (hι : Function.Injective ι) {i : ℕ} {x : M₁} :
    x ∈ lowerPiece (subFilt Γ ι) i ↔ ι x ∈ lowerPiece Γ i := by
  cases i with
  | zero =>
      simp only [lowerPiece, Submodule.mem_bot]
      exact ⟨fun h => by rw [h, map_zero], fun h => hι (by rw [h, map_zero])⟩
  | succ i => exact Iff.rfl

omit [Module K M₁] [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M₁] in
theorem mem_lowerPiece_quotFilt {i : ℕ} {y : M ⧸ LinearMap.range ι} :
    y ∈ lowerPiece (quotFilt Γ ι) i ↔
      ∃ x ∈ lowerPiece Γ i, (LinearMap.range ι).mkQ x = y := by
  cases i with
  | zero =>
      simp only [lowerPiece, Submodule.mem_bot]
      constructor
      · rintro rfl; exact ⟨0, rfl, map_zero _⟩
      · rintro ⟨x, rfl, rfl⟩; exact map_zero _
  | succ i => exact Iff.rfl

omit [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M] in
theorem lowerPiece_le (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ) (i : ℕ) :
    lowerPiece Γ i ≤ Γ i := by
  cases i with
  | zero => exact bot_le
  | succ i => exact hΓ.mono (Nat.le_succ i)

omit [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M₁] in
theorem grMap_of {M' : Type w'} [AddCommGroup M'] [Module (PresentedWeyl K n)ᵐᵒᵖ M']
    [Module K M'] [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M'] {Γ' : ℕ → Submodule K M'}
    (φ : M →ₗ[(PresentedWeyl K n)ᵐᵒᵖ] M') (hφ : ∀ i, ∀ x ∈ Γ i, φ x ∈ Γ' i) (i : ℕ)
    (y : grPiece Γ i) :
    grMap φ hφ (ofG Γ i y) = ofG Γ' i (pieceMap φ hφ i y) := by
  change DFinsupp.mapRange (fun i => pieceMap φ hφ i) (fun i => (pieceMap φ hφ i).map_zero)
    (DFinsupp.single i _) = DFinsupp.single i _
  rw [DFinsupp.mapRange_single]

theorem pieceMap_sub_injective (hι : Function.Injective ι) (i : ℕ) :
    Function.Injective (pieceMap ι (subFilt_map (Γ := Γ)) i) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  induction y using Submodule.Quotient.induction_on with
  | H y =>
      obtain ⟨x, hx⟩ := y
      rw [LinearMap.mem_ker, pieceMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
        at hy
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact (mem_lowerPiece_subFilt hι).mpr hy

theorem grSub_injective (hι : Function.Injective ι) :
    Function.Injective (grMap ι (subFilt_map (Γ := Γ))) := by
  intro z₁ z₂ hz
  apply ext_comp
  intro i
  apply pieceMap_sub_injective (Γ := Γ) hι i
  rw [← grMap_apply, ← grMap_apply, hz]

omit [Module K M₁] [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M₁] in
theorem grQuot_surjective :
    Function.Surjective (grMap (LinearMap.range ι).mkQ (quotFilt_map (Γ := Γ))) := by
  intro z
  induction z using gr_induction with
  | h0 => exact ⟨0, map_zero _⟩
  | hcls i y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨cls Γ i x, grMap_cls _ _ hx⟩
  | hadd a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩

theorem pieceMap_quot_exact (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ) (i : ℕ)
    (q : grPiece Γ i) (hq : pieceMap (LinearMap.range ι).mkQ (quotFilt_map (Γ := Γ)) i q = 0) :
    ∃ y, pieceMap ι (subFilt_map (Γ := Γ)) i y = q := by
  induction q using Submodule.Quotient.induction_on with
  | H q =>
      obtain ⟨x, hx⟩ := q
      rw [pieceMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      obtain ⟨x', hx', hxx'⟩ := mem_lowerPiece_quotFilt.mp hq
      have hN : x - x' ∈ LinearMap.range ι := by
        rw [← Submodule.Quotient.eq]
        exact hxx'.symm
      obtain ⟨x₁, hx₁⟩ := hN
      have hΓx : ι x₁ ∈ Γ i := hx₁ ▸ sub_mem hx (lowerPiece_le hΓ i hx')
      refine ⟨Submodule.Quotient.mk ⟨x₁, hΓx⟩, ?_⟩
      rw [pieceMap, Submodule.mapQ_apply, Submodule.Quotient.eq]
      change ι x₁ - x ∈ lowerPiece Γ i
      rw [hx₁, sub_sub_cancel_left]
      exact neg_mem hx'

theorem grQuot_exact (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ) (z : GrModule Γ)
    (hz : grMap (LinearMap.range ι).mkQ (quotFilt_map (Γ := Γ)) z = 0) :
    ∃ y, grMap ι (subFilt_map (Γ := Γ)) y = z := by
  classical
  have hpiece : ∀ i, ∃ y, pieceMap ι (subFilt_map (Γ := Γ)) i y = comp Γ i z := by
    intro i
    refine pieceMap_quot_exact hΓ i _ ?_
    rw [← grMap_apply, hz, map_zero]
  choose y hy using hpiece
  obtain ⟨s, hs⟩ := sum_ofG_comp z
  refine ⟨∑ i ∈ s, ofG (subFilt Γ ι) i (y i), ?_⟩
  rw [map_sum, hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [grMap_of, hy]

variable (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ) (hι : Function.Injective ι)
include hΓ

include hι in
theorem annihilator_le_sub :
    Module.annihilator (SymbolRing K n) (GrModule Γ) ≤
      Module.annihilator (SymbolRing K n) (GrModule (subFilt Γ ι)) :=
  (grMapS ι subFilt_map (subFilt_isCompatible hΓ) hΓ).annihilator_le_of_injective
    (grSub_injective hι)

omit [Module K M₁] [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M₁] in
theorem annihilator_le_quot :
    Module.annihilator (SymbolRing K n) (GrModule Γ) ≤
      Module.annihilator (SymbolRing K n) (GrModule (quotFilt Γ ι)) :=
  (grMapS _ quotFilt_map hΓ (quotFilt_isCompatible hΓ)).annihilator_le_of_surjective
    grQuot_surjective

theorem annihilator_mul_le :
    Module.annihilator (SymbolRing K n) (GrModule (subFilt Γ ι)) *
        Module.annihilator (SymbolRing K n) (GrModule (quotFilt Γ ι)) ≤
      Module.annihilator (SymbolRing K n) (GrModule Γ) := by
  rw [Ideal.mul_le]
  intro r hr s hs
  rw [Module.mem_annihilator] at hr hs ⊢
  intro z
  have hker : grMap (LinearMap.range ι).mkQ (quotFilt_map (Γ := Γ)) (s • z) = 0 := by
    rw [grMap_smul _ _ hΓ (quotFilt_isCompatible hΓ), hs]
  obtain ⟨y, hy⟩ := grQuot_exact hΓ _ hker
  rw [mul_smul, ← hy, ← grMap_smul _ _ (subFilt_isCompatible hΓ) hΓ, hr, map_zero]

include hι in
/-- `√Ann gr M = √Ann gr N ∩ √Ann gr(M/N)` for the induced filtrations. -/
theorem radical_annihilator_eq :
    (Module.annihilator (SymbolRing K n) (GrModule Γ)).radical =
      (Module.annihilator (SymbolRing K n) (GrModule (subFilt Γ ι))).radical ⊓
        (Module.annihilator (SymbolRing K n) (GrModule (quotFilt Γ ι))).radical := by
  apply le_antisymm
  · exact le_inf (Ideal.radical_mono (annihilator_le_sub hΓ hι))
      (Ideal.radical_mono (annihilator_le_quot hΓ))
  · rw [← Ideal.radical_mul]
    exact Ideal.radical_mono (annihilator_mul_le hΓ)

omit hΓ in
include hι in
/-- The induced filtration on a submodule of a module with a good filtration is
good, `K[x, ξ]` being Noetherian. -/
theorem subFilt_good (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
    [Module.Finite (SymbolRing K n) (GrModule Γ)] :
    Module.Finite (SymbolRing K n) (GrModule (subFilt Γ ι)) :=
  Module.Finite.of_injective (grMapS ι subFilt_map (subFilt_isCompatible hΓ) hΓ)
    (grSub_injective hι)

omit [Module K M₁] [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M₁] in
/-- The image filtration on a quotient of a module with a good filtration is
good. -/
theorem quotFilt_good [Module.Finite (SymbolRing K n) (GrModule Γ)] :
    Module.Finite (SymbolRing K n) (GrModule (quotFilt Γ ι)) :=
  Module.Finite.of_surjective (grMapS _ quotFilt_map hΓ (quotFilt_isCompatible hΓ))
    grQuot_surjective

#print axioms grMap_smul
#print axioms radical_annihilator_eq
#print axioms subFilt_good
#print axioms quotFilt_good

end SubQuotient

end

end Stafford38.Paper.Support.Gabber
