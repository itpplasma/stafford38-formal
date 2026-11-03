module

public import Stafford38.Paper.Section2.Weyl
public import Stafford38.FixedSourceChallengeTransport
public import Stafford38.Characteristic.AssociatedGradedModule

@[expose] public section

/-!
# Section 2 of the paper: Definitions 2.3 and 2.4

Definition 2.3: filtrations of an algebra, the associated graded algebra
`gr^F = ⊕_j F_j/F_{j-1}`, the filtration degree and the symbol; the Bernstein
filtration `B_•` and the order filtration `F_•` of `A_n(k)`, the Bernstein
degree `deg_B`, and `gr A_n(k) = k[x, ξ]`.

Definition 2.4: filtrations of a right module compatible with a filtration of
the algebra, the cyclic example `M_i = qF_i`, and goodness of that example for
`Q = A_n/I`.

Filtrations are indexed by `ℕ`; the paper's `F_{-1} = 0` is `lowerPiece F 0 = ⊥`.
The repository's pieces are spans of ordered PBW words of bounded weight
(`WeylFiltration.presentedWeightPiece`); `B_m` uses weight `1` on every
generator and `F_m` weight `0` on `x_i`, `1` on `∂_i`.
-/

namespace Stafford38.Paper.Section2

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBW

noncomputable section

universe u v w

section Graded

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]

/-- `F_{j-1}`, with `F_{-1} = 0`. -/
def lowerPiece (F : ℕ → Submodule k M) : ℕ → Submodule k M
  | 0 => ⊥
  | j + 1 => F j

/-- The graded piece `F_j/F_{j-1}`. -/
abbrev grPiece (F : ℕ → Submodule k M) (j : ℕ) :=
  F j ⧸ (lowerPiece F j).comap (F j).subtype

instance (priority := 10000) grPieceAddCommMonoid (F : ℕ → Submodule k M) (j : ℕ) :
    AddCommMonoid (grPiece F j) :=
  AddCommGroup.toAddCommMonoid

instance (priority := 10000) grPieceModule (F : ℕ → Submodule k M) (j : ℕ) :
    Module k (grPiece F j) :=
  Submodule.Quotient.module _

/-- **Definition 2.3 (associated graded).** `gr^F = ⊕_{j ≥ 0} F_j/F_{j-1}`
as a `k`-module, for a filtration of an algebra or (Definition 2.4) of a
module. -/
abbrev gr (F : ℕ → Submodule k M) :=
  DirectSum ℕ (grPiece F)

end Graded

section General

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

/-- **Definition 2.3 (filtration).** `F_0 ⊆ F_1 ⊆ … ⊆ A` linear subspaces with
`F_i F_j ⊆ F_{i+j}` and `A = ⋃_j F_j`. -/
structure IsFiltration (F : ℕ → Submodule k A) : Prop where
  mono : Monotone F
  mul_mem : ∀ {i j : ℕ} {a b : A}, a ∈ F i → b ∈ F j → a * b ∈ F (i + j)
  exhaustive : ∀ a : A, ∃ j, a ∈ F j

/-- **Definition 2.3 (filtration degree).** `deg_F a` is the smallest `j` with
`a ∈ F_j`. -/
def filtrationDegree (F : ℕ → Submodule k A) (a : A) : ℕ :=
  sInf {j | a ∈ F j}

theorem mem_filtrationDegree {F : ℕ → Submodule k A} (hF : IsFiltration F) (a : A) :
    a ∈ F (filtrationDegree F a) :=
  Nat.sInf_mem (hF.exhaustive a)

/-- **Definition 2.3 (symbol).** `σ_j(a)` is the class of `a` in `F_j/F_{j-1}`
for `j = deg_F a`. -/
def symbol {F : ℕ → Submodule k A} (hF : IsFiltration F) (a : A) :
    grPiece F (filtrationDegree F a) :=
  Submodule.Quotient.mk ⟨a, mem_filtrationDegree hF a⟩

end General

variable (k : Type u) [Field k]

/-- **The Bernstein filtration `B_•`**: degree `1` on every `x_i` and `∂_i`. -/
abbrev bernsteinFiltration (n : ℕ) : ℕ → Submodule k (PresentedWeyl k n) :=
  bernsteinPiece k n

/-- **The order filtration `F_•`**: degree `0` on `x_i`, `1` on `∂_i`;
`F_m` is spanned by the `x^α ∂^β` with `|β| ≤ m`. -/
abbrev orderFiltration (n : ℕ) : ℕ → Submodule k (PresentedWeyl k n) :=
  orderPiece k n

theorem isFiltration_bernstein (n : ℕ) : IsFiltration (bernsteinFiltration k n) :=
  ⟨fun _ _ h => presentedWeightPiece_mono k _ h, mul_mem_bernsteinPiece k,
    exists_mem_bernsteinPiece k⟩

theorem isFiltration_order (n : ℕ) : IsFiltration (orderFiltration k n) :=
  ⟨fun _ _ h => presentedWeightPiece_mono k _ h, mul_mem_orderPiece k,
    exists_mem_orderPiece k⟩

/-- **The Bernstein degree** `deg_B d`, the filtration degree for `B_•`. -/
def bernsteinDegree {n : ℕ} (d : PresentedWeyl k n) : ℕ :=
  filtrationDegree (bernsteinFiltration k n) d

/-- The printed Bernstein degree is the repository's intrinsic
`Stafford38FixedSourceChallenge.bernsteinDegree`. -/
theorem bernsteinDegree_eq {n : ℕ} (d : PresentedWeyl k n) :
    bernsteinDegree k d = Stafford38FixedSourceChallenge.bernsteinDegree k d := by
  simp only [bernsteinDegree, filtrationDegree, Stafford38FixedSourceChallenge.bernsteinDegree,
    Stafford38FixedSourceChallengeTransport.bernsteinPiece_eq]

/-- `deg_B a ≤ L` exactly when `a ∈ B_L`. -/
theorem bernsteinDegree_le_iff {n L : ℕ} (a : PresentedWeyl k n) :
    bernsteinDegree k a ≤ L ↔ a ∈ bernsteinPiece k n L := by
  rw [bernsteinDegree_eq, Stafford38FixedSourceChallengeTransport.bernsteinDegree_eq,
    Stafford38.FixedSource.bernsteinDegree, bernsteinPiece, mem_presentedWeightPiece]
  constructor
  · intro h m hm
    exact (MvPolynomial.le_weightedTotalDegree _ (MvPolynomial.mem_support_iff.mpr hm)).trans h
  · intro h
    apply Finset.sup_le
    intro m hm
    exact h m (MvPolynomial.mem_support_iff.mp hm)

/-- `deg_B d = N` once `d ∈ B_N` has nonzero degree-`N` Bernstein symbol. -/
theorem bernsteinDegree_eq_of_principal_ne_zero {n N : ℕ} {d : PresentedWeyl k n}
    (hd : d ∈ bernsteinPiece k n N)
    (hP : presentedPrincipalComponent k (@bernsteinWeight n) N d ≠ 0) :
    bernsteinDegree k d = N := by
  rw [bernsteinDegree_eq, Stafford38FixedSourceChallengeTransport.bernsteinDegree_eq]
  exact Stafford38.FixedSource.bernsteinDegree_eq_of_piece_of_principal_ne_zero k hd hP

theorem lowerPiece_weight {n : ℕ} (w : PhaseVar n → ℕ) (j : ℕ) :
    lowerPiece (presentedWeightPiece k w) j = presentedStrictLowerPiece k w j := by
  cases j <;> rfl

/-- For both filtrations of `A_n(k)`, the class of `a ∈ F_j` in `F_j/F_{j-1}`
is the degree-`j` homogeneous component of the PBW normal form of `a`, the
repository's principal symbol: the class vanishes exactly when that component
does. -/
theorem grPiece_mk_eq_zero_iff {n : ℕ} (w : PhaseVar n → ℕ) {j : ℕ}
    (a : presentedWeightPiece k w j) :
    (Submodule.Quotient.mk a : grPiece (presentedWeightPiece k w) j) = 0 ↔
      presentedPrincipalComponent k w j a = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    lowerPiece_weight, presentedPrincipalComponent_eq_zero_iff_mem_strictLower k w _ a.2]

/-- The graded piece `F_j/F_{j-1}` is the space of weighted-homogeneous symbols of
degree `j`, through the principal symbol. -/
def grPieceEquiv {n : ℕ} (w : PhaseVar n → ℕ) (j : ℕ) :
    grPiece (presentedWeightPiece k w) j ≃ₗ[k]
      MvPolynomial.weightedHomogeneousSubmodule k w j :=
  (Submodule.quotEquivOfEq _ _ (by
      ext a
      rw [Submodule.mem_comap, Submodule.coe_subtype, lowerPiece_weight, LinearMap.mem_ker,
        ← presentedPrincipalComponent_eq_zero_iff_mem_strictLower k w _ a.2]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)).trans
    (LinearMap.quotKerEquivOfSurjective _ (principalComponentOnPiece_surjective k w))

/-- **`gr A_n(k) = k[x, ξ]`** for the Bernstein and the order filtration
(any weight): `⊕_j F_j/F_{j-1}` is identified with the polynomial ring by
summing the homogeneous symbols.  Multiplication of classes is the product of
symbols, `σ_{i+j}(ab) = σ_i(a)σ_j(b)`
(`WeylLeadingSymbol.presentedPrincipalComponent_mul_bernstein`,
`presentedPrincipalComponent_mul_order`), so `gr A_n(k)` is commutative. -/
def grEquivSymbolRing {n : ℕ} (w : PhaseVar n → ℕ) :
    gr (presentedWeightPiece k w) ≃ₗ[k] SymbolRing k n := by
  letI := MvPolynomial.weightedDecomposition k w
  exact (DFinsupp.mapRange.linearEquiv fun j => grPieceEquiv k w j).trans
    (DirectSum.decomposeLinearEquiv (MvPolynomial.weightedHomogeneousSubmodule k w)).symm

section ModuleFiltration

variable {k}
variable {A : Type v} [Ring A] [Algebra k A]
variable {M : Type w} [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module k M]
  [IsScalarTower k Aᵐᵒᵖ M]

/-- **Definition 2.4 (compatible filtration).** An exhaustive increasing chain
`M_0 ⊆ M_1 ⊆ …` of `k`-subspaces (`M_i = 0` for `i < 0`) with
`M_i F_j ⊆ M_{i+j}`. -/
structure IsCompatibleFiltration (F : ℕ → Submodule k A) (Mf : ℕ → Submodule k M) :
    Prop where
  mono : Monotone Mf
  smul_mem : ∀ {i j : ℕ} {m : M} {a : A}, m ∈ Mf i → a ∈ F j →
    MulOpposite.op a • m ∈ Mf (i + j)
  exhaustive : ∀ m : M, ∃ i, m ∈ Mf i

/-- `a ↦ qa`. -/
def orbitMap (q : M) : A →ₗ[k] M where
  toFun a := MulOpposite.op a • q
  map_add' a b := by rw [MulOpposite.op_add, add_smul]
  map_smul' c a := show MulOpposite.op (c • a) • q = c • (MulOpposite.op a • q) by
    rw [MulOpposite.op_smul, smul_assoc]

/-- The filtration `M_i = qF_i` induced by an element `q`. -/
def cyclicFiltration (F : ℕ → Submodule k A) (q : M) (i : ℕ) : Submodule k M :=
  (F i).map (orbitMap q)

/-- **Definition 2.4, example.** For a cyclic module `M = qA` and a filtration
`F_•` of `A`, `M_i = qF_i` is a compatible filtration. -/
theorem cyclicFiltration_isCompatible {F : ℕ → Submodule k A} (hF : IsFiltration F) (q : M)
    (hq : ∀ x : M, ∃ a : A, x = MulOpposite.op a • q) :
    IsCompatibleFiltration F (cyclicFiltration F q) := by
  refine ⟨fun i j hij => Submodule.map_mono (f := orbitMap q) (hF.mono hij), ?_, ?_⟩
  · rintro i j _ a ⟨b, hb, rfl⟩ ha
    refine ⟨b * a, hF.mul_mem hb ha, ?_⟩
    change MulOpposite.op (b * a) • q = MulOpposite.op a • MulOpposite.op b • q
    rw [smul_smul, MulOpposite.op_mul]
  · intro x
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨i, hi⟩ := hF.exhaustive a
    exact ⟨i, a, hi, rfl⟩

end ModuleFiltration

/-- **Definition 2.4 for `Q = A_n/I`.** The order filtration `Q_m = qF_m`
induced by `q = [1]` is the image of `F_m`; its associated graded module
`gr Q = ⊕_m Q_m/Q_{m-1}` with its `k[x, ξ]`-module structure is the
repository's `OrderAssociatedGradedModule`. -/
abbrev grCyclic {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) :=
  OrderAssociatedGradedModule k I

/-- `Q_m = qF_m`: the repository's quotient pieces are the images of `F_m`. -/
theorem quotientOrderPiece_eq {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) (m : ℕ) :
    quotientOrderPiece k I m = (orderFiltration k n m).map (rightIdealKSubmodule k I).mkQ :=
  rfl

/-- The class `q̄ ∈ Q_0/Q_{-1}` of `q = [1]`. -/
abbrev qBar {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) : grCyclic k I :=
  orderAssociatedGradedOneClass k I

/-- `gr Q` is generated over `k[x, ξ]` by `q̄`. -/
theorem grCyclic_generated {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) (m : grCyclic k I) :
    ∃ f : SymbolRing k n, f • qBar k I = m := by
  rw [qBar, ← orderAssociatedGradedGenerator_eq_oneClass]
  exact exists_smul_orderAssociatedGradedGenerator k _ m

/-- **Definition 2.4, example: goodness.** `gr Q` is finitely generated over
`gr A_n = k[x, ξ]`, being generated by `q̄`. -/
theorem grCyclic_good {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) :
    Module.Finite (SymbolRing k n) (grCyclic k I) := by
  refine ⟨⟨{qBar k I}, eq_top_iff.mpr fun m _ => ?_⟩⟩
  obtain ⟨f, rfl⟩ := grCyclic_generated k I m
  exact Submodule.smul_mem _ f (Submodule.subset_span (by simp))


section CyclicGraded

variable {k}

/-- A linear equivalence carrying `F` to `F'` and `G` to `G'` identifies
`F/(G ∩ F)` with `F'/(G' ∩ F')`. -/
def quotientMapEquiv {P P' : Type*} [AddCommGroup P] [Module k P] [AddCommGroup P']
    [Module k P'] (e : P ≃ₗ[k] P') (F G : Submodule k P) :
    (F ⧸ G.comap F.subtype) ≃ₗ[k] (F.map e.toLinearMap ⧸ (G.map e.toLinearMap).comap
      (F.map e.toLinearMap).subtype) :=
  Submodule.Quotient.equiv _ _ (e.submoduleMap F) (by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨⟨y, hyF⟩, hyG, hxy⟩
      refine ⟨y, hyG, ?_⟩
      have := congrArg Subtype.val hxy
      simpa using this
    · rintro ⟨y, hyG, rfl⟩
      obtain ⟨z, hzF, hz⟩ := hx
      have hzy : z = y := e.injective hz
      subst hzy
      exact ⟨⟨z, hzF⟩, hyG, rfl⟩)

end CyclicGraded

/-- `q = [1] ∈ Q = A_n/I`, the cyclic generator. -/
abbrev qClass {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) : RightQuotient I :=
  Submodule.Quotient.mk 1

theorem orbitMap_qClass {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) (a : PresentedWeyl k n) :
    orbitMap (k := k) (qClass k I) a = Submodule.Quotient.mk a := by
  change MulOpposite.op a • (Submodule.Quotient.mk 1 : RightQuotient I) = _
  rw [← Submodule.Quotient.mk_smul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul]

/-- Every element of `Q` is `qa`: `Q` is cyclic, generated by `q`. -/
theorem qClass_generates {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) (x : RightQuotient I) :
    ∃ a : PresentedWeyl k n, x = MulOpposite.op a • qClass k I := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨a, (orbitMap_qClass k I a).symm⟩

/-- **Definition 2.4 for `Q = A_n/I`.** `M_i = qF_i` is a compatible filtration
of `Q` (`cyclicFiltration_isCompatible`). -/
theorem cyclicFiltration_order_isCompatible {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) :
    IsCompatibleFiltration (orderFiltration k n) (cyclicFiltration (orderFiltration k n)
      (qClass k I)) :=
  cyclicFiltration_isCompatible (isFiltration_order k n) _ (qClass_generates k I)

/-- `Q_m = qF_m` is the repository's quotient piece, transported to `Q`. -/
theorem cyclicFiltration_order_eq {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) (m : ℕ) :
    cyclicFiltration (orderFiltration k n) (qClass k I) m =
      (quotientOrderPiece k I m).map
        (filteredRightQuotientEquivRightQuotient k I).toLinearMap := by
  rw [quotientOrderPiece_eq, ← Submodule.map_comp, cyclicFiltration]
  congr 1
  ext a
  exact (orbitMap_qClass k I a).trans rfl

theorem lowerPiece_cyclicFiltration_order_eq {n : ℕ} (I : RightIdeal (PresentedWeyl k n))
    (m : ℕ) :
    lowerPiece (cyclicFiltration (orderFiltration k n) (qClass k I)) m =
      (quotientOrderStrictLowerPiece k I m).map
        (filteredRightQuotientEquivRightQuotient k I).toLinearMap := by
  cases m with
  | zero =>
      have h0 : presentedStrictLowerPiece k (@orderWeight n) 0 = ⊥ :=
        (lowerPiece_weight k _ 0).symm
      rw [quotientOrderStrictLowerPiece, h0, Submodule.map_bot, Submodule.map_bot]
      rfl
  | succ m =>
      rw [quotientOrderStrictLowerPiece, ← lowerPiece_weight]
      exact cyclicFiltration_order_eq k I m

/-- **Definition 2.4, `gr Q`.** The associated graded module
`⊕_m Q_m/Q_{m-1}` of the filtration `Q_m = qF_m` (Definition 2.3, `gr`) is
`grCyclic`, the module on which `k[x, ξ]` acts. -/
def grCyclicEquiv {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) :
    grCyclic k I ≃ₗ[k] gr (cyclicFiltration (orderFiltration k n) (qClass k I)) :=
  DFinsupp.mapRange.linearEquiv fun m =>
    (quotientMapEquiv (filteredRightQuotientEquivRightQuotient k I) _ _).trans
      (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (cyclicFiltration_order_eq k I m).symm)
        (by
          rw [lowerPiece_cyclicFiltration_order_eq]
          ext ⟨x, hx⟩
          simp [Submodule.mem_comap]))

#print axioms grCyclicEquiv

end

end Stafford38.Paper.Section2
