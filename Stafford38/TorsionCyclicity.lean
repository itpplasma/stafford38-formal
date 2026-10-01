import Stafford38.FoundationClosure
import Stafford38.Weyl.Domain

/-!
# Finitely generated torsion right Weyl modules are cyclic

Stafford (J. London Math. Soc. (2) 18 (1978), pp. 437–438) observes that
Conjecture 3.8 implies cyclicity of torsion modules. We prove the general
algebraic implication for any ring `A` without zero divisors in which every
nonzero `d` admits `1 = d * R + F * d * S`, and specialize it to the Weyl
algebra with `Stafford38.universalStatement`.

Right `A`-modules are modules over `Aᵐᵒᵖ`; `MulOpposite.op a • m` is the right
action `m a`. The proof inducts on a finite generating set. The two-generator
step is the manuscript's argument: a common nonzero annihilator `d` of `t₁`
and `t₂` exists because `A` has no zero divisors (no Ore condition and no
two-generator theorem are used), and then `g = t₁ - t₂ F` generates.
-/

namespace Stafford38.TorsionCyclicity

universe u v

/-- Every element of the right module has a nonzero right annihilator. -/
def IsRightTorsion (A : Type u) [Ring A] (M : Type v) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] : Prop :=
  ∀ m : M, ∃ a : A, a ≠ 0 ∧ MulOpposite.op a • m = 0

/-- Stafford's identity for every nonzero element, with the written order. -/
def HasStaffordCertificates (A : Type u) [Ring A] : Prop :=
  ∀ d : A, d ≠ 0 → ∃ F R S : A, (1 : A) = d * R + F * d * S

section General

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module Aᵐᵒᵖ M]

/-- Right actions compose in written order: `m (a b) = (m a) b`. -/
theorem op_mul_smul (a b : A) (m : M) :
    MulOpposite.op (a * b) • m = MulOpposite.op b • MulOpposite.op a • m := by
  rw [MulOpposite.op_mul, mul_smul]

/-- Two elements of a torsion right module generate a cyclic submodule. -/
theorem exists_span_singleton_eq_span_pair [NoZeroDivisors A]
    (hA : HasStaffordCertificates A) (hM : IsRightTorsion A M) (t₁ t₂ : M) :
    ∃ g : M, Submodule.span Aᵐᵒᵖ {g} = Submodule.span Aᵐᵒᵖ {t₁, t₂} := by
  obtain ⟨d₂, hd₂, ht₂⟩ := hM t₂
  obtain ⟨e, he, hte⟩ := hM (MulOpposite.op d₂ • t₁)
  have hd : d₂ * e ≠ 0 := mul_ne_zero hd₂ he
  have h₁ : MulOpposite.op (d₂ * e) • t₁ = 0 := by
    rw [op_mul_smul]
    exact hte
  have h₂ : MulOpposite.op (d₂ * e) • t₂ = 0 := by
    rw [op_mul_smul, ht₂, smul_zero]
  obtain ⟨F, R, S, hFRS⟩ := hA (d₂ * e) hd
  set d := d₂ * e with hd_def
  set g : M := t₁ - MulOpposite.op F • t₂ with hg_def
  have hself : t₂ = MulOpposite.op (F * d * S) • t₂ := by
    have h := congrArg (fun a : A => MulOpposite.op a • t₂) hFRS
    simp only [MulOpposite.op_one, one_smul, MulOpposite.op_add, add_smul] at h
    rw [op_mul_smul d R, h₂, smul_zero, zero_add] at h
    exact h
  have hg : MulOpposite.op (d * S) • g = -t₂ := by
    rw [hg_def, smul_sub, ← op_mul_smul F (d * S), op_mul_smul d S, h₁, smul_zero,
      zero_sub, ← mul_assoc, ← hself]
  have ht₂mem : t₂ ∈ Submodule.span Aᵐᵒᵖ {g} := by
    have hneg : -t₂ ∈ Submodule.span Aᵐᵒᵖ {g} := by
      rw [← hg]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)
    simpa using Submodule.neg_mem _ hneg
  have ht₁mem : t₁ ∈ Submodule.span Aᵐᵒᵖ {g} := by
    have : t₁ = g + MulOpposite.op F • t₂ := by
      rw [hg_def, sub_add_cancel]
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_span_singleton_self g)
      (Submodule.smul_mem _ _ ht₂mem)
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ht₁mem
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ht₂mem

/-- Every finitely generated submodule of a torsion right module is cyclic. -/
theorem exists_span_singleton_eq_span_finset [NoZeroDivisors A]
    (hA : HasStaffordCertificates A) (hM : IsRightTorsion A M) (s : Finset M) :
    ∃ g : M, Submodule.span Aᵐᵒᵖ {g} = Submodule.span Aᵐᵒᵖ (s : Set M) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert t s _ ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨g', hg'⟩ := exists_span_singleton_eq_span_pair hA hM t g
    refine ⟨g', ?_⟩
    rw [hg', Finset.coe_insert, Submodule.span_insert, Submodule.span_insert, hg]

/-- A finitely generated torsion right module over a ring with Stafford
certificates and no zero divisors is cyclic. -/
theorem isCyclic_of_isRightTorsion [NoZeroDivisors A]
    (hA : HasStaffordCertificates A) [Module.Finite Aᵐᵒᵖ M]
    (hM : IsRightTorsion A M) :
    ∃ g : M, Submodule.span Aᵐᵒᵖ {g} = ⊤ := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule Aᵐᵒᵖ M).FG)
  obtain ⟨g, hg⟩ := exists_span_singleton_eq_span_finset hA hM s
  exact ⟨g, hg.trans hs⟩

end General

/-- Stafford's identity holds in every Weyl algebra over a field of
characteristic zero. -/
theorem weyl_hasStaffordCertificates (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    HasStaffordCertificates (Stafford38.WeylAlg k n) :=
  fun d hd => Stafford38.universalStatement k n d hd

/-- Every finitely generated torsion right module over `Aₙ(k)`, `k` a field of
characteristic zero, is cyclic. -/
theorem weyl_isCyclic_of_isRightTorsion (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (M : Type v) [AddCommGroup M] [Module (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    [Module.Finite (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    (hM : IsRightTorsion (Stafford38.WeylAlg k n) M) :
    ∃ g : M, Submodule.span (Stafford38.WeylAlg k n)ᵐᵒᵖ {g} = ⊤ :=
  isCyclic_of_isRightTorsion (weyl_hasStaffordCertificates k n) hM

#print axioms isCyclic_of_isRightTorsion
#print axioms weyl_isCyclic_of_isRightTorsion

end Stafford38.TorsionCyclicity
