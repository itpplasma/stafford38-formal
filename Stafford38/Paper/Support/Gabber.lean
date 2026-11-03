module

public import Stafford38.Paper.Support.GabberGood
public import Stafford38.Characteristic.GabberGlobalAssembly

@[expose] public section

/-!
# Theorem 2.11 (Gabber) for finitely generated modules with a good filtration

**Theorem 2.11.** Let `K` be a field of characteristic zero and `M` a finitely
generated right `A_n(K)`-module with a good order filtration `M_•`.  Then
`J = √(Ann_{K[x,ξ]} gr M)` is involutive, `{J, J} ⊆ J`.

The theorem is cited from the literature [Gab81]; the proof here reduces it to
the cyclic case `M = A_n(K)/I` with the filtration `qF_m`, which the repository
proves (`GabberGlobalAssembly.associatedGraded_radical_isInvolutive`):

1. `√Ann gr M` does not depend on the good filtration (`GabberGood`), so for a
   cyclic module any good filtration may be replaced by `qF_m`, whose `gr` is
   the repository's `grCyclic` as a `K[x, ξ]`-module (`grCyclicEquivS`).
2. For `0 → N → M → M/N → 0` with induced filtrations, `gr N → gr M → gr(M/N)`
   is exact, so `√Ann gr M = √Ann gr N ∩ √Ann gr(M/N)`; both induced filtrations
   are good because `K[x, ξ]` is Noetherian.
3. Induction on the number of generators, splitting off a cyclic submodule;
   an intersection of involutive ideals is involutive.

[Gab81] O. Gabber, *The integrability of the characteristic variety*,
Amer. J. Math. 103 (1981), 445–468.
-/

namespace Stafford38.Paper.Support.Gabber

open Stafford38.Paper.Section2
open Stafford38.Characteristic
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylPBW
open Stafford38.EulerSurjectivity

noncomputable section

universe u w w' w₁

section Cyclic

variable (K : Type u) [Field K] {n : ℕ} (I : RightIdeal (PresentedWeyl K n))

/-- The filtration `Q_m = qF_m` of `Q = A_n/I`. -/
abbrev qFilt : ℕ → Submodule K (RightQuotient I) :=
  cyclicFiltration (orderFiltration K n) (qClass K I)

/-- `grCyclicEquiv` with codomain `GrModule (qFilt K I)`. -/
def grCyclicEquivG : grCyclic K I ≃ₗ[K] GrModule (qFilt K I) :=
  grCyclicEquiv K I

theorem principal_gen (v : PhaseVar n) :
    (principalComponentOnPiece K (@orderWeight n) (orderWeight v)
      ⟨gen K n v, gen_mem v⟩ : SymbolRing K n) = MvPolynomial.X v := by
  classical
  change MvPolynomial.weightedHomogeneousComponent orderWeight (orderWeight v)
    (presentedNormalFormLinearEquiv K n
      (Stafford.freeWeylGenerator (Matrix.J (Fin n) K) v)) = _
  rw [presentedNormalFormLinearEquiv_generator,
    MvPolynomial.weightedHomogeneousComponent_of_mem
      (MvPolynomial.isWeightedHomogeneous_X K orderWeight v), ite_eq_left rfl]

theorem grCyclicEquiv_of (N : ℕ) (z : orderPiece K n N) :
    grCyclicEquivG K I
        (orderAssociatedGradedOf K I N (orderPieceToQuotientGraded K I N z)) =
      cls (qFilt K I) N (Submodule.Quotient.mk (z : PresentedWeyl K n)) := by
  have hz : (Submodule.Quotient.mk (z : PresentedWeyl K n) : RightQuotient I) ∈ qFilt K I N :=
    ⟨z, z.property, orbitMap_qClass K I z⟩
  rw [cls_of_mem hz]
  unfold grCyclicEquivG grCyclicEquiv orderAssociatedGradedOf
  change (DFinsupp.mapRange.linearEquiv _ : (Π₀ i, QuotientOrderGradedPiece K I i) ≃ₗ[K] _)
    (DFinsupp.single N _) = DFinsupp.single N _
  rw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_single]
  rfl

theorem grCyclic_induction {P : grCyclic K I → Prop} (y : grCyclic K I) (h0 : P 0)
    (hof : ∀ N (z : orderPiece K n N),
      P (orderAssociatedGradedOf K I N (orderPieceToQuotientGraded K I N z)))
    (hadd : ∀ a b, P a → P b → P (a + b)) : P y :=
  DirectSum.induction_on (motive := fun y => P y) y h0
    (fun N q => by
      obtain ⟨z, rfl⟩ := orderPieceToQuotientGraded_surjective K I N q
      exact hof N z)
    (fun a b ha hb => hadd a b ha hb)

theorem grCyclicEquiv_X_smul (v : PhaseVar n) (y : grCyclic K I) :
    grCyclicEquivG K I ((MvPolynomial.X v : SymbolRing K n) • y) =
      (MvPolynomial.X v : SymbolRing K n) • grCyclicEquivG K I y := by
  induction y using grCyclic_induction with
  | h0 => rw [smul_zero, map_zero, smul_zero]
  | hof N z =>
      have h := smul_orderAssociatedGradedOf_mk_eq_of_mul K I z ⟨gen K n v, gen_mem v⟩
      rw [principal_gen] at h
      rw [h, grCyclicEquiv_of, grCyclicEquiv_of]
      have hz : (Submodule.Quotient.mk (z : PresentedWeyl K n) : RightQuotient I) ∈
          qFilt K I N := ⟨z, z.property, orbitMap_qClass K I z⟩
      rw [X_smul_cls (cyclicFiltration_order_isCompatible K I) v hz]
      rfl
  | hadd a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]

/-- `gr Q` for `Q_m = qF_m`, with the `K[x, ξ]`-structure of `GrModule`, is the
repository's `grCyclic` (`OrderAssociatedGradedModule`). -/
def grCyclicEquivS : grCyclic K I ≃ₗ[SymbolRing K n] GrModule (qFilt K I) :=
  { grCyclicEquivG K I with
    map_smul' := by
      intro f y
      change grCyclicEquivG K I (f • y) = f • grCyclicEquivG K I y
      induction f using MvPolynomial.induction_on generalizing y with
      | C c =>
          rw [C_smul, ← MvPolynomial.algebraMap_eq, algebraMap_smul, map_smul]
      | add p q hp hq => rw [add_smul, map_add, hp, hq, add_smul]
      | mul_X p v hp => rw [mul_smul, hp, grCyclicEquiv_X_smul, mul_smul] }

theorem annihilator_qFilt :
    Module.annihilator (SymbolRing K n) (GrModule (qFilt K I)) =
      Module.annihilator (SymbolRing K n) (grCyclic K I) :=
  (grCyclicEquivS K I).annihilator_eq.symm

/-- `Q_m = qF_m` is good: `gr Q` is generated by `q̄` (Definition 2.4). -/
theorem qFilt_good : Module.Finite (SymbolRing K n) (GrModule (qFilt K I)) := by
  have := grCyclic_good K I
  exact Module.Finite.equiv (grCyclicEquivS K I)

variable [CharZero K]

/-- Theorem 2.11 for a cyclic module `A_n/I` with an arbitrary good filtration. -/
theorem cyclic_isInvolutive {Γ : ℕ → Submodule K (RightQuotient I)}
    (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
    (hgood : Module.Finite (SymbolRing K n) (GrModule Γ)) :
    IsInvolutive (Module.annihilator (SymbolRing K n) (GrModule Γ)).radical := by
  rw [radical_annihilator_eq_of_good hΓ (cyclicFiltration_order_isCompatible K I) hgood
    (qFilt_good K I), annihilator_qFilt]
  exact GabberGlobalAssembly.associatedGraded_radical_isInvolutive K I

#print axioms grCyclicEquivS
#print axioms cyclic_isInvolutive

end Cyclic

section General

variable {K : Type u} [Field K] {n : ℕ}

theorem isInvolutive_inf {J₁ J₂ : Ideal (SymbolRing K n)} (h₁ : IsInvolutive J₁)
    (h₂ : IsInvolutive J₂) : IsInvolutive (J₁ ⊓ J₂) :=
  fun f hf g hg => ⟨h₁ f hf.1 g hg.1, h₂ f hf.2 g hg.2⟩

variable {M : Type w} [AddCommGroup M] [Module (PresentedWeyl K n)ᵐᵒᵖ M] [Module K M]
  [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M]

omit [Module K M] [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M] in
theorem subsingleton_of_span_eq_top_empty
    (h : (⊥ : Submodule (PresentedWeyl K n)ᵐᵒᵖ M) = ⊤) : Subsingleton M :=
  ⟨fun a b => by
    have ha : a ∈ (⊥ : Submodule (PresentedWeyl K n)ᵐᵒᵖ M) := h ▸ Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule (PresentedWeyl K n)ᵐᵒᵖ M) := h ▸ Submodule.mem_top
    rw [(Submodule.mem_bot _).mp ha, (Submodule.mem_bot _).mp hb]⟩

theorem isInvolutive_of_subsingleton [Subsingleton M] (Γ : ℕ → Submodule K M) :
    IsInvolutive (Module.annihilator (SymbolRing K n) (GrModule Γ)).radical := by
  have hsub : Subsingleton (GrModule Γ) := by
    refine ⟨fun a b => ?_⟩
    have h0 : ∀ z : GrModule Γ, z = 0 := fun z => by
      induction z using gr_induction with
      | h0 => rfl
      | hcls i x _ => rw [Subsingleton.elim x 0, cls_zero]
      | hadd a b ha hb => rw [ha, hb, add_zero]
    rw [h0 a, h0 b]
  rw [Module.annihilator_eq_top_iff.mpr hsub, Ideal.radical_top]
  exact fun _ _ _ _ => Submodule.mem_top

/-- `a ↦ m a`, the orbit map of `m` as a map of right modules. -/
def orbitHom (m : M) : PresentedWeyl K n →ₗ[(PresentedWeyl K n)ᵐᵒᵖ] M where
  toFun a := MulOpposite.op a • m
  map_add' a b := by rw [MulOpposite.op_add, add_smul]
  map_smul' c a := by
    change MulOpposite.op (a * c.unop) • m = c • MulOpposite.op a • m
    rw [MulOpposite.op_mul, MulOpposite.op_unop, mul_smul]

/-- `A_n/ann(m) ≅ mA ⊆ M`, `[a] ↦ m a`. -/
def cyclicInclusion (m : M) :
    RightQuotient (LinearMap.ker (orbitHom (K := K) (n := n) m)) →ₗ[(PresentedWeyl K n)ᵐᵒᵖ] M :=
  (LinearMap.ker (orbitHom m)).liftQ (orbitHom m) le_rfl

omit [Module K M] [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M] in
theorem cyclicInclusion_injective (m : M) :
    Function.Injective (cyclicInclusion (K := K) (n := n) m) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

omit [Module K M] [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M] in
theorem mem_range_cyclicInclusion (m : M) :
    m ∈ LinearMap.range (cyclicInclusion (K := K) (n := n) m) :=
  ⟨Submodule.Quotient.mk 1, by
    change MulOpposite.op (1 : PresentedWeyl K n) • m = m
    rw [MulOpposite.op_one, one_smul]⟩

variable [CharZero K]

theorem isInvolutive_of_card (r : ℕ) :
    ∀ {M : Type w} [AddCommGroup M] [Module (PresentedWeyl K n)ᵐᵒᵖ M] [Module K M]
      [IsScalarTower K (PresentedWeyl K n)ᵐᵒᵖ M] (s : Finset M), s.card ≤ r →
      Submodule.span (PresentedWeyl K n)ᵐᵒᵖ (s : Set M) = ⊤ →
      ∀ Γ : ℕ → Submodule K M, IsCompatibleFiltration (orderFiltration K n) Γ →
        Module.Finite (SymbolRing K n) (GrModule Γ) →
        IsInvolutive (Module.annihilator (SymbolRing K n) (GrModule Γ)).radical := by
  classical
  induction r with
  | zero =>
      intro M _ _ _ _ s hs hspan Γ _ _
      have : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
      subst this
      rw [Finset.coe_empty, Submodule.span_empty] at hspan
      have : Subsingleton M := subsingleton_of_span_eq_top_empty hspan
      exact isInvolutive_of_subsingleton Γ
  | succ r ih =>
      intro M _ _ _ _ s hs hspan Γ hΓ hgood
      by_cases hne : s = ∅
      · subst hne
        rw [Finset.coe_empty, Submodule.span_empty] at hspan
        have : Subsingleton M := subsingleton_of_span_eq_top_empty hspan
        exact isInvolutive_of_subsingleton Γ
      obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨ι, hι, hmι⟩ : ∃ ι : RightQuotient (LinearMap.ker (orbitHom (K := K) (n := n) m))
          →ₗ[(PresentedWeyl K n)ᵐᵒᵖ] M, Function.Injective ι ∧ m ∈ LinearMap.range ι :=
        ⟨_, cyclicInclusion_injective m, mem_range_cyclicInclusion m⟩
      rw [radical_annihilator_eq hΓ hι]
      apply isInvolutive_inf
      · exact cyclic_isInvolutive K _ (subFilt_isCompatible hΓ) (subFilt_good hι hΓ)
      · have hgoodq : Module.Finite (SymbolRing K n) (GrModule (quotFilt Γ ι)) :=
          quotFilt_good hΓ
        refine ih ((s.erase m).image (LinearMap.range ι).mkQ) ?_ ?_ _
          (quotFilt_isCompatible hΓ) hgoodq
        · have := Finset.card_erase_of_mem hm
          have := Finset.card_image_le (s := s.erase m) (f := (LinearMap.range ι).mkQ)
          omega
        · rw [Finset.coe_image, Submodule.span_image, eq_top_iff]
          rintro y -
          obtain ⟨x, rfl⟩ := (LinearMap.range ι).mkQ_surjective y
          have hx : x ∈ Submodule.span (PresentedWeyl K n)ᵐᵒᵖ
              (insert m ((s.erase m : Finset M) : Set M)) := by
            rw [← Finset.coe_insert, Finset.insert_erase hm, hspan]
            exact Submodule.mem_top
          obtain ⟨a, z, hz, rfl⟩ := Submodule.mem_span_insert.mp hx
          refine ⟨z, hz, ?_⟩
          have hm0 : (LinearMap.range ι).mkQ m = 0 :=
            (Submodule.Quotient.mk_eq_zero _).mpr hmι
          rw [map_add, map_smul, hm0, smul_zero, zero_add]

#print axioms isInvolutive_of_card

end General

/-- **Theorem 2.11 (Gabber).** Let `K` be a field of characteristic zero and `M`
a finitely generated right `A_n(K)`-module with a good order filtration `M_•`
(Definition 2.4: compatible, exhaustive, `gr M` finitely generated over
`K[x, ξ]`).  Then `J = √(Ann_{K[x,ξ]} gr M)` is involutive, `{J, J} ⊆ J`.

The proof reduces to the cyclic case proved in the repository
(`GabberGlobalAssembly.associatedGraded_radical_isInvolutive`); see the module
docstring. -/
theorem theorem_2_11_general (K : Type u) [Field K] [CharZero K] (n : ℕ)
    {M : Type w} [AddCommGroup M] [Module (Stafford38Challenge.WeylAlg K n)ᵐᵒᵖ M] [Module K M]
    [IsScalarTower K (Stafford38Challenge.WeylAlg K n)ᵐᵒᵖ M]
    [Module.Finite (Stafford38Challenge.WeylAlg K n)ᵐᵒᵖ M]
    (Γ : ℕ → Submodule K M) (hΓ : IsCompatibleFiltration (orderFiltration K n) Γ)
    (hgood : Module.Finite (SymbolRing K n) (GrModule Γ)) :
    IsInvolutive (Module.annihilator (SymbolRing K n) (GrModule Γ)).radical := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := (PresentedWeyl K n)ᵐᵒᵖ) (M := M)
  exact isInvolutive_of_card s.card s le_rfl hs Γ hΓ hgood

#print axioms theorem_2_11_general

theorem rightQuotient_finite {K : Type u} [Field K] {n : ℕ} (I : RightIdeal (PresentedWeyl K n)) :
    Module.Finite (PresentedWeyl K n)ᵐᵒᵖ (RightQuotient I) := by
  have : Module.Finite (PresentedWeyl K n)ᵐᵒᵖ (PresentedWeyl K n) :=
    Module.Finite.of_surjective (LinearMap.toSpanSingleton _ _ (1 : PresentedWeyl K n))
      fun a => ⟨MulOpposite.op a, by
        rw [LinearMap.toSpanSingleton_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
          one_mul]⟩
  infer_instance


end

end Stafford38.Paper.Support.Gabber
