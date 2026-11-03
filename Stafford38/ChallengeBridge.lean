module
public import Stafford38.ChallengeDefinitions

@[expose] public section

/-!
# Equivalences between the paper-form challenge statements and the Stafford statements

`PaperTheorem_1_1` and `PaperCorollary_6_3` (in `Stafford38.ChallengeDefinitions`)
state Theorem 1.1 and Corollary 6.3 as printed.  This file proves that they follow
from the identity form `UniversalStatement`, the fixed-source form
`UniversalFixedSourceStatement` and the span form of cyclicity, so that both
solution routes can supply them:

* `A_n = dA_n + FdA_n` iff `1 = dR + FdS` (`top_eq_sup_span_iff`);
* `IsLinearWeylCoordinate ℓ` iff `ℓ = Φ_g^{-1}(x₁)` for some `g ∈ Sp(2n, k)`
  (`isLinearWeylCoordinate_iff`);
* `span {m} = ⊤` iff `M = mA` (`isCyclicModule_iff_span`).
-/

namespace Stafford38Challenge

universe u v

/-- `Φ_g(u_i) = g(u_i)`. -/
theorem phiG_generator (k : Type*) [Field k] (n : ℕ) (g : Matrix.symplecticGroup (Fin n) k)
    (i : PhaseVar n) :
    phiG k n g (generator k n i) = linearImage k (g : Matrix (PhaseVar n) (PhaseVar n) k) i := by
  simp [phiG, generator, Stafford.freeWeylGenerator, RingQuot.liftAlgHom_mkAlgHom_apply]

/-- `A = dA + FdA` (right ideals) iff `1 = dR + FdS`. -/
theorem top_eq_sup_span_iff {A : Type*} [Ring A] (d F : A) :
    (⊤ : Submodule Aᵐᵒᵖ A) = Submodule.span Aᵐᵒᵖ {d} ⊔ Submodule.span Aᵐᵒᵖ {F * d} ↔
      ∃ R S : A, (1 : A) = d * R + F * d * S := by
  constructor
  · intro h
    have h1 : (1 : A) ∈ Submodule.span Aᵐᵒᵖ {d} ⊔ Submodule.span Aᵐᵒᵖ {F * d} := h ▸ trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨r.unop, s.unop, hyz.symm⟩
  · rintro ⟨R, S, h⟩
    refine (eq_top_iff.mpr fun x _ => ?_).symm
    have hx : x = d * (R * x) + F * d * (S * x) := by
      rw [← mul_assoc, ← mul_assoc, ← add_mul, ← h, one_mul]
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.mem_span_singleton.mpr ⟨MulOpposite.op (R * x), rfl⟩)
      (Submodule.mem_span_singleton.mpr ⟨MulOpposite.op (S * x), rfl⟩)

/-- A linear symplectic coordinate is `Φ_g^{-1}(x₁) = Φ_{g⁻¹}(x₁)` for some
`ω`-preserving `g`. -/
theorem isLinearWeylCoordinate_iff (k : Type*) [Field k] (m : ℕ) (ell : WeylAlg k (m + 1)) :
    Stafford38FixedSourceChallenge.IsLinearWeylCoordinate k m ell ↔
      ∃ g : Matrix.symplecticGroup (Fin (m + 1)) k,
        ell = phiG k (m + 1) g⁻¹ (x₁ k (Nat.succ_pos m)) := by
  constructor
  · rintro ⟨M, N, hM, -, hMN, -, rfl⟩
    refine ⟨⟨M, SymplecticGroup.mem_iff.mpr hM⟩, ?_⟩
    rw [phiG_generator, SymplecticGroup.coe_inv']
    change _ = Stafford.linearCombination (M⁻¹) _ _
    rw [Matrix.inv_eq_right_inv hMN]
    rfl
  · rintro ⟨g, rfl⟩
    refine ⟨g, (g⁻¹ : Matrix.symplecticGroup (Fin (m + 1)) k),
      SymplecticGroup.mem_iff.mp g.2, SymplecticGroup.mem_iff.mp (g⁻¹).2, ?_, ?_, ?_⟩
    · change ((g * g⁻¹ : Matrix.symplecticGroup (Fin (m + 1)) k) :
        Matrix (PhaseVar (m + 1)) (PhaseVar (m + 1)) k) = 1
      rw [mul_inv_cancel]
      rfl
    · change ((g⁻¹ * g : Matrix.symplecticGroup (Fin (m + 1)) k) :
        Matrix (PhaseVar (m + 1)) (PhaseVar (m + 1)) k) = 1
      rw [inv_mul_cancel]
      rfl
    · rw [phiG_generator]
      rfl

/-- `M = mA` iff `span {m} = ⊤`. -/
theorem isCyclicModule_iff_span (A : Type u) (M : Type v) [Ring A] [AddCommGroup M]
    [Module Aᵐᵒᵖ M] :
    IsCyclicModule A M ↔ ∃ m : M, Submodule.span Aᵐᵒᵖ {m} = ⊤ := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, eq_top_iff.mpr fun x _ => ?_⟩
    obtain ⟨a, rfl⟩ := hm x
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m)
  · rintro ⟨m, hm⟩
    refine ⟨m, fun x => ?_⟩
    have hx : x ∈ Submodule.span Aᵐᵒᵖ {m} := hm ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨a.unop, rfl⟩

/-- Theorem 1.1 as printed follows from the identity form and the fixed-source
form. -/
theorem paperTheorem_1_1_of (h1 : UniversalStatement.{u})
    (h2 : Stafford38FixedSourceChallenge.UniversalFixedSourceStatement.{u}) :
    PaperTheorem_1_1.{u} := by
  intro k _ _ n d hd
  obtain ⟨F, R, S, h⟩ := h1 k n d hd
  refine ⟨⟨F, (top_eq_sup_span_iff d F).2 ⟨R, S, h⟩⟩, ⟨F, S, R, h⟩, fun hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ell, R', S', hell, h'⟩ := h2 k m d hd
  obtain ⟨g, rfl⟩ := (isLinearWeylCoordinate_iff k m ell).1 hell
  exact ⟨g, R', S', h'⟩

/-- Corollary 6.3 as printed follows from the span form of cyclicity. -/
theorem paperCorollary_6_3_of
    (h : ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (M : Type v) [AddCommGroup M]
      [Module (WeylAlg k n)ᵐᵒᵖ M] [Module.Finite (WeylAlg k n)ᵐᵒᵖ M],
      Stafford38.TorsionCyclicity.IsRightTorsion (A := WeylAlg k n) (M := M) →
        ∃ z : M, Submodule.span (WeylAlg k n)ᵐᵒᵖ {z} = ⊤) :
    PaperCorollary_6_3.{u, v} := by
  intro k _ _ n M _ _ _ hM
  exact (isCyclicModule_iff_span _ _).2 (h k n M hM)

#print axioms top_eq_sup_span_iff
#print axioms isLinearWeylCoordinate_iff
#print axioms paperTheorem_1_1_of
#print axioms paperCorollary_6_3_of

end Stafford38Challenge
