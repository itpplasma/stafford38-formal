import Stafford38.FoundationClosure
import Stafford38.Weyl.Domain
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Cyclicity of finitely generated torsion right Weyl modules

Right modules are represented as left modules over the opposite ring. The
pair argument uses only the Stafford identity and the domain property; induction
on a finite generating set then gives a cyclic module.
-/

namespace Stafford38.TorsionCyclicity

universe u v

/-- Every element of a right module is killed by some nonzero right scalar. -/
def IsRightTorsion {A : Type u} {M : Type v} [Ring A]
    [AddCommGroup M] [Module Aᵐᵒᵖ M] : Prop :=
  ∀ m : M, ∃ d : A, d ≠ 0 ∧ (MulOpposite.op d : Aᵐᵒᵖ) • m = 0

variable {A : Type u} {M : Type v} [Ring A]
  [AddCommGroup M] [Module Aᵐᵒᵖ M]

/-- The paper's generator calculation for a specified common annihilator
and a specified Stafford certificate. No Ore or finite-generation hypothesis
is needed for this algebraic step. -/
theorem span_adjusted_pair_eq_span_pair
    (x y : M) (d F R S : A)
    (hxann : (MulOpposite.op d : Aᵐᵒᵖ) • x = 0)
    (hyann : (MulOpposite.op d : Aᵐᵒᵖ) • y = 0)
    (hcert : (1 : A) = d * R + F * d * S) :
    Submodule.span Aᵐᵒᵖ ({x - (MulOpposite.op F : Aᵐᵒᵖ) • y} : Set M) =
      Submodule.span Aᵐᵒᵖ ({x, y} : Set M) := by
  classical
  let g : M := x - (MulOpposite.op F : Aᵐᵒᵖ) • y
  let P : Submodule Aᵐᵒᵖ M := Submodule.span Aᵐᵒᵖ ({x, y} : Set M)
  let G : Submodule Aᵐᵒᵖ M := Submodule.span Aᵐᵒᵖ ({g} : Set M)
  have hy_dR : (MulOpposite.op (d * R) : Aᵐᵒᵖ) • y = 0 := by
    change (MulOpposite.op R * MulOpposite.op d) • y = 0
    rw [← smul_smul, hyann, smul_zero]
  have hy_FdS : (MulOpposite.op (F * d * S) : Aᵐᵒᵖ) • y = y := by
    have hsum : y =
        (MulOpposite.op (d * R) : Aᵐᵒᵖ) • y +
          (MulOpposite.op (F * d * S) : Aᵐᵒᵖ) • y := by
      calc
        y = (MulOpposite.op (1 : A) : Aᵐᵒᵖ) • y := by simp
        _ = (MulOpposite.op (d * R + F * d * S) : Aᵐᵒᵖ) • y := by
          rw [hcert]
        _ = (MulOpposite.op (d * R) : Aᵐᵒᵖ) • y +
            (MulOpposite.op (F * d * S) : Aᵐᵒᵖ) • y := by
          rw [MulOpposite.op_add, add_smul]
    simpa only [hy_dR, zero_add] using hsum.symm
  have hleft : (MulOpposite.op (d * S) : Aᵐᵒᵖ) • x = 0 := by
    change (MulOpposite.op S * MulOpposite.op d) • x = 0
    rw [← smul_smul, hxann, smul_zero]
  change (MulOpposite.op S * MulOpposite.op d) • x = 0 at hleft
  have hcoeff :
      (MulOpposite.op (d * S) : Aᵐᵒᵖ) * MulOpposite.op F =
        (MulOpposite.op (F * d * S) : Aᵐᵒᵖ) := by
    simp [MulOpposite.op_mul, mul_assoc]
  have hright :
      (MulOpposite.op (d * S) : Aᵐᵒᵖ) •
          ((MulOpposite.op F : Aᵐᵒᵖ) • y) = y := by
    calc
      _ = ((MulOpposite.op (d * S) : Aᵐᵒᵖ) * MulOpposite.op F) • y := by
        rw [smul_smul]
      _ = (MulOpposite.op (F * d * S) : Aᵐᵒᵖ) • y := by rw [hcoeff]
      _ = y := hy_FdS
  change (MulOpposite.op S * MulOpposite.op d) •
    ((MulOpposite.op F : Aᵐᵒᵖ) • y) = y at hright
  have hresidue :
      (MulOpposite.op (d * S) : Aᵐᵒᵖ) • g = -y := by
    change (MulOpposite.op S * MulOpposite.op d) •
      (x - (MulOpposite.op F : Aᵐᵒᵖ) • y) = -y
    rw [smul_sub, hleft, hright]
    simp
  have hxP : x ∈ P := Submodule.subset_span (by simp)
  have hyP : y ∈ P := Submodule.subset_span (by simp)
  have hgP : g ∈ P := by
    dsimp [g]
    exact P.sub_mem hxP (P.smul_mem _ hyP)
  have hgG : g ∈ G := by
    dsimp [G]
    exact Submodule.subset_span (by simp)
  have hGP : G ≤ P := by
    dsimp [G]
    apply Submodule.span_le.2
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact hgP
  have hyG : y ∈ G := by
    have hmem := G.smul_mem (MulOpposite.op (d * S)) hgG
    rw [hresidue] at hmem
    simpa using G.neg_mem hmem
  have hxG : x ∈ G := by
    have hx : x = g + (MulOpposite.op F : Aᵐᵒᵖ) • y := by
      simp [g]
    rw [hx]
    exact G.add_mem hgG (G.smul_mem _ hyG)
  have hPG : P ≤ G := by
    dsimp [P, G]
    apply Submodule.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxG
    · exact hyG
  exact le_antisymm hGP hPG

/-- Under the two-generator identity, the paper generator collapses every pair. -/
theorem exists_span_adjusted_pair
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : IsRightTorsion (A := A) (M := M)) (x y : M) :
    ∃ F : A,
      Submodule.span Aᵐᵒᵖ ({x - (MulOpposite.op F : Aᵐᵒᵖ) • y} : Set M) =
        Submodule.span Aᵐᵒᵖ ({x, y} : Set M) := by
  classical
  obtain ⟨d₂, hd₂, hdy⟩ := htorsion y
  obtain ⟨e, he, hdx⟩ := htorsion ((MulOpposite.op d₂ : Aᵐᵒᵖ) • x)
  let d : A := d₂ * e
  have hd : d ≠ 0 := hmul d₂ e hd₂ he
  have hxann : (MulOpposite.op d : Aᵐᵒᵖ) • x = 0 := by
    change (MulOpposite.op e * MulOpposite.op d₂) • x = 0
    rw [← smul_smul]
    exact hdx
  have hyann : (MulOpposite.op d : Aᵐᵒᵖ) • y = 0 := by
    change (MulOpposite.op e * MulOpposite.op d₂) • y = 0
    rw [← smul_smul, hdy, smul_zero]
  obtain ⟨F, R, S, hcert⟩ := hone d hd
  exact ⟨F, span_adjusted_pair_eq_span_pair x y d F R S hxann hyann hcert⟩

/-- The adjusted generator has the paper's explicit form `x - yF`.
Forgetting its coefficient recovers the original cyclicity interface. -/
theorem exists_span_singleton_eq_span_pair
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : IsRightTorsion (A := A) (M := M)) (x y : M) :
    ∃ z : M,
      Submodule.span Aᵐᵒᵖ ({z} : Set M) =
        Submodule.span Aᵐᵒᵖ ({x, y} : Set M) := by
  obtain ⟨F, hF⟩ := exists_span_adjusted_pair hmul hone htorsion x y
  exact ⟨x - (MulOpposite.op F : Aᵐᵒᵖ) • y, hF⟩

private theorem finite_span_is_cyclic
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : IsRightTorsion (A := A) (M := M))
    [Module.Finite Aᵐᵒᵖ M] :
    ∃ z : M, Submodule.span Aᵐᵒᵖ ({z} : Set M) = ⊤ := by
  classical
  have hfg : (⊤ : Submodule Aᵐᵒᵖ M).FG := Module.Finite.fg_top
  obtain ⟨s, hs⟩ := hfg
  have hcollapse (s : Finset M) :
      ∃ z : M, Submodule.span Aᵐᵒᵖ (s : Set M) =
        Submodule.span Aᵐᵒᵖ ({z} : Set M) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert x s hxs ih =>
        obtain ⟨y, hy⟩ := ih
        obtain ⟨z, hpair⟩ :=
          exists_span_singleton_eq_span_pair hmul hone htorsion x y
        refine ⟨z, ?_⟩
        have hpairSet :
            ({x, y} : Set M) = ({x} : Set M) ∪ {y} := by
          ext w
          simp [or_comm]
        calc
          Submodule.span Aᵐᵒᵖ ((insert x s : Finset M) : Set M) =
              Submodule.span Aᵐᵒᵖ {x} ⊔ Submodule.span Aᵐᵒᵖ (s : Set M) := by
                rw [Finset.coe_insert, Submodule.span_insert]
          _ = Submodule.span Aᵐᵒᵖ {x} ⊔ Submodule.span Aᵐᵒᵖ {y} := by rw [hy]
          _ = Submodule.span Aᵐᵒᵖ ({x, y} : Set M) := by
                rw [hpairSet, Submodule.span_union]
          _ = Submodule.span Aᵐᵒᵖ {z} := hpair.symm
  obtain ⟨z, hz⟩ := hcollapse s
  exact ⟨z, hz.symm.trans hs⟩

/-- Every finitely generated torsion right module over a Weyl algebra is
cyclic. The two-generator identity is the already-proved Stafford theorem. -/
theorem weyl_isCyclic_of_isRightTorsion
    (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (M : Type v) [AddCommGroup M]
    [Module (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    [Module.Finite (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    (hM : IsRightTorsion (A := Stafford38.WeylAlg k n) (M := M)) :
    ∃ z : M,
      Submodule.span (Stafford38.WeylAlg k n)ᵐᵒᵖ ({z} : Set M) = ⊤ := by
  exact finite_span_is_cyclic
    (A := Stafford38.WeylAlg k n) (M := M)
    (fun a b ha hb => Stafford38.WeylDomain.mul_ne_zero ha hb)
    (Stafford38.universalStatement (k := k) n)
    hM

#print axioms span_adjusted_pair_eq_span_pair
#print axioms exists_span_adjusted_pair
#print axioms exists_span_singleton_eq_span_pair
#print axioms weyl_isCyclic_of_isRightTorsion

end Stafford38.TorsionCyclicity
