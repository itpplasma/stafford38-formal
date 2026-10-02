import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Tactic.NoncommRing

/-!
# Generic pair replacement for right modules

The matrix calculation behind Stafford's cyclicity argument uses only a ring,
a right module, torsion of the two chosen elements, and the coefficient
identity `1 = d * R + F * d * S`. These results are kept independent of the
Weyl algebra and its application-specific certificate.
-/

namespace Stafford38.LinearAlgebra.PairReplacement

universe u v

variable {A : Type u} [Ring A]

/-- The two displayed vectors generate the free rank-two right module. Right
coordinates are represented as a left module over the opposite ring. -/
theorem matrix_pair_spans (a F : A) :
    Submodule.span Aᵐᵒᵖ
      ({(a, 1 - F * a), (1, -F)} : Set (A × A)) = ⊤ := by
  classical
  let P : Submodule Aᵐᵒᵖ (A × A) :=
    Submodule.span Aᵐᵒᵖ ({(a, 1 - F * a), (1, -F)} : Set (A × A))
  apply top_unique
  rintro ⟨x, y⟩ _
  have h₁ : (a, 1 - F * a) ∈ P := by
    exact Submodule.subset_span (by simp)
  have h₂ : (1, -F) ∈ P := by
    exact Submodule.subset_span (by simp)
  let u : A := y + F * x
  let v : A := x - a * u
  have hz : (x, y) =
      (MulOpposite.op u : Aᵐᵒᵖ) • (a, 1 - F * a) +
        (MulOpposite.op v : Aᵐᵒᵖ) • (1, -F) := by
    simp only [Prod.smul_def, Prod.add_def, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, one_mul]
    change (x, y) = (a * u + v, (1 - F * a) * u + (-F) * v)
    dsimp [u, v]
    congr 1 <;> noncomm_ring
  rw [hz]
  exact P.add_mem (P.smul_mem _ h₁) (P.smul_mem _ h₂)

variable {M : Type v} [AddCommGroup M] [Module Aᵐᵒᵖ M]

/-- Two torsion elements have a common nonzero right annihilator. The product
order `d₂*e` is required for the right-module action. -/
theorem common_right_annihilator
    (htorsion : ∀ m : M, ∃ d : A, d ≠ 0 ∧
      (MulOpposite.op d : Aᵐᵒᵖ) • m = 0)
    (x y : M)
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0) :
    ∃ d : A, d ≠ 0 ∧
      (MulOpposite.op d : Aᵐᵒᵖ) • x = 0 ∧
      (MulOpposite.op d : Aᵐᵒᵖ) • y = 0 := by
  obtain ⟨d₂, hd₂, hdy⟩ := htorsion y
  obtain ⟨e, he, hdx⟩ := htorsion
    ((MulOpposite.op d₂ : Aᵐᵒᵖ) • x)
  refine ⟨d₂ * e, hmul d₂ e hd₂ he, ?_, ?_⟩
  · change (MulOpposite.op e * MulOpposite.op d₂) • x = 0
    rw [← smul_smul]
    exact hdx
  · change (MulOpposite.op e * MulOpposite.op d₂) • y = 0
    rw [← smul_smul, hdy, smul_zero]

/-- The matrix calculation proves pair replacement for any right module over a
ring satisfying the displayed coefficient identity. -/
theorem span_adjusted_pair_eq_span_pair
    (x y : M) (d F R S : A)
    (hxann : (MulOpposite.op d : Aᵐᵒᵖ) • x = 0)
    (hyann : (MulOpposite.op d : Aᵐᵒᵖ) • y = 0)
    (hcert : (1 : A) = d * R + F * d * S) :
    Submodule.span Aᵐᵒᵖ
        ({x - (MulOpposite.op F : Aᵐᵒᵖ) • y} : Set M) =
      Submodule.span Aᵐᵒᵖ ({x, y} : Set M) := by
  classical
  let g : M := x - (MulOpposite.op F : Aᵐᵒᵖ) • y
  let P : Submodule Aᵐᵒᵖ M := Submodule.span Aᵐᵒᵖ ({x, y} : Set M)
  let phi : (A × A) →ₗ[Aᵐᵒᵖ] M :=
    { toFun := fun z => (MulOpposite.op z.1 : Aᵐᵒᵖ) • x +
        (MulOpposite.op z.2 : Aᵐᵒᵖ) • y
      map_add' := by
        intro z w
        rcases z with ⟨z₁, z₂⟩
        rcases w with ⟨w₁, w₂⟩
        simp [Prod.add_def, MulOpposite.op_add, add_smul]
        abel
      map_smul' := by
        intro c z
        rcases z with ⟨z₁, z₂⟩
        simp only [Prod.smul_def, MulOpposite.smul_eq_mul_unop,
          MulOpposite.op_mul, smul_add, smul_smul]
        rfl }
  let U : Submodule Aᵐᵒᵖ (A × A) :=
    Submodule.span Aᵐᵒᵖ
      ({(d * S, 1 - F * (d * S)), (1, -F)} : Set (A × A))
  let H : Submodule Aᵐᵒᵖ M :=
    Submodule.span Aᵐᵒᵖ ({g} : Set M)
  have hzero₁ : phi (d * S, 1 - F * (d * S)) = 0 := by
    have hx : (MulOpposite.op (d * S) : Aᵐᵒᵖ) • x = 0 := by
      change (MulOpposite.op S * MulOpposite.op d) • x = 0
      rw [← smul_smul, hxann, smul_zero]
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
          _ = _ := by rw [MulOpposite.op_add, add_smul]
      simpa only [hy_dR, zero_add] using hsum.symm
    have hyfactor : (MulOpposite.op (1 - F * (d * S)) : Aᵐᵒᵖ) • y = 0 := by
      calc
        _ = (MulOpposite.op (1 : A) : Aᵐᵒᵖ) • y -
            (MulOpposite.op (F * d * S) : Aᵐᵒᵖ) • y := by
              rw [MulOpposite.op_sub, sub_smul]
              congr 1
              simp [mul_assoc]
        _ = 0 := by rw [MulOpposite.op_one, one_smul, hy_FdS, sub_self]
    change (MulOpposite.op (d * S) : Aᵐᵒᵖ) • x +
      (MulOpposite.op (1 - F * (d * S)) : Aᵐᵒᵖ) • y = 0
    rw [hx, hyfactor, add_zero]
  have hzero₂ : phi (1, -F) = g := by
    change (MulOpposite.op (1 : A) : Aᵐᵒᵖ) • x +
      (MulOpposite.op (-F) : Aᵐᵒᵖ) • y = _
    simp [g, sub_eq_add_neg]
  have hphi : phi.range = P := by
    apply le_antisymm
    · rintro z ⟨w, rfl⟩
      rcases w with ⟨a, b⟩
      change (MulOpposite.op a : Aᵐᵒᵖ) • x +
        (MulOpposite.op b : Aᵐᵒᵖ) • y ∈ P
      exact P.add_mem
        (P.smul_mem _ (Submodule.subset_span (by simp)))
        (P.smul_mem _ (Submodule.subset_span (by simp)))
    · apply Submodule.span_le.2
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨(1, 0), by simp [phi]⟩
      · exact ⟨(0, 1), by simp [phi]⟩
  have hmatrix := matrix_pair_spans (d * S) F
  have hgen : P = H := by
    calc
      P = phi.range := hphi.symm
      _ = Submodule.map phi ⊤ := (Submodule.map_top _).symm
      _ = Submodule.map phi U := by rw [← hmatrix]
      _ = H := by
        rw [Submodule.map_span]
        apply le_antisymm
        · apply Submodule.span_le.2
          rintro z ⟨w, hw, rfl⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with rfl | rfl
          · rw [hzero₁]
            exact H.zero_mem
          · rw [hzero₂]
            exact Submodule.subset_span (by simp)
        · apply Submodule.span_le.2
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst z
          rw [← hzero₂]
          exact Submodule.subset_span (by simp)
  simpa [P, H, g] using hgen.symm

/-- A torsion pair can be replaced by one generator. -/
theorem exists_adjusted_pair
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : ∀ m : M, ∃ d : A, d ≠ 0 ∧
      (MulOpposite.op d : Aᵐᵒᵖ) • m = 0) (x y : M) :
    ∃ F : A, Submodule.span Aᵐᵒᵖ
      ({x - (MulOpposite.op F : Aᵐᵒᵖ) • y} : Set M) =
        Submodule.span Aᵐᵒᵖ ({x, y} : Set M) := by
  obtain ⟨d, hd, hx, hy⟩ := common_right_annihilator htorsion x y hmul
  obtain ⟨F, R, S, hcert⟩ := hone d hd
  exact ⟨F, span_adjusted_pair_eq_span_pair x y d F R S hx hy hcert⟩

/-- Forget the explicit matrix coefficient and retain its generated singleton. -/
theorem exists_singleton_eq_span_pair
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : ∀ m : M, ∃ d : A, d ≠ 0 ∧
      (MulOpposite.op d : Aᵐᵒᵖ) • m = 0) (x y : M) :
    ∃ z : M, Submodule.span Aᵐᵒᵖ ({z} : Set M) =
      Submodule.span Aᵐᵒᵖ ({x, y} : Set M) := by
  obtain ⟨F, hF⟩ := exists_adjusted_pair hmul hone htorsion x y
  exact ⟨x - (MulOpposite.op F : Aᵐᵒᵖ) • y, hF⟩

/-- Pair replacement iterated along a finite spanning set makes any finitely
generated torsion right module cyclic. -/
theorem finite_torsion_module_is_cyclic
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : ∀ m : M, ∃ d : A, d ≠ 0 ∧
      (MulOpposite.op d : Aᵐᵒᵖ) • m = 0)
    [Module.Finite Aᵐᵒᵖ M] :
    ∃ z : M, Submodule.span Aᵐᵒᵖ ({z} : Set M) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule Aᵐᵒᵖ M).FG)
  have hcollapse (s : Finset M) :
      ∃ z : M, Submodule.span Aᵐᵒᵖ (s : Set M) =
        Submodule.span Aᵐᵒᵖ ({z} : Set M) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert x s hxs ih =>
        obtain ⟨y, hy⟩ := ih
        obtain ⟨z, hpair⟩ := exists_singleton_eq_span_pair hmul hone htorsion x y
        refine ⟨z, ?_⟩
        have hpairSet : ({x, y} : Set M) = ({x} : Set M) ∪ {y} := by
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

#print axioms matrix_pair_spans
#print axioms common_right_annihilator
#print axioms span_adjusted_pair_eq_span_pair
#print axioms exists_adjusted_pair
#print axioms exists_singleton_eq_span_pair
#print axioms finite_torsion_module_is_cyclic

end Stafford38.LinearAlgebra.PairReplacement
