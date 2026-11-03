module

public import Stafford38.Paper.Main
public import Stafford38.PaperClaimDefinitions
public import Stafford38.LeftHandedCorollary
public import Stafford38.LocalizedDifferentialCorollaries
public import Stafford38.EvolutionaryCorollary

@[expose] public section

/-!
# Section 7: consequences without a printed proof (tex 1629–1634)

The paper lists consequences of Theorem 1.1 that "have no printed proof".
Each is stated here in the Mathlib-only form of `Stafford38.PaperClaimDefinitions`
and proved directly; those that need Theorem 1.1 use
`Stafford38.Paper.theorem_1_1`.

* `leftHandedIdentity`: `1 = Rd + SdF`, the transpose (formal adjoint) of
  Theorem 1.1 applied to the transpose of `d`.
* `corollary_6_3_left`: the printed proof of Corollary 6.3 for right modules
  over `A_n(k)ᵐᵒᵖ`, i.e. left `A_n(k)`-modules, with the left-handed identity
  in place of `1 = dR + FdS` and the left Ore condition (via the transpose).
* `localizedDifferentialIdentity`: Theorem 1.1 for `A_n(k)` transported to
  `D_k(S⁻¹k[x])` by clearing a left denominator of each operator.
* `evolutionaryIdentity`: the Euler-root certificate for
  `d = p^r - ∑ a_j x^{m_j}`, which does not use Theorem 1.1.
-/

namespace Stafford38.Paper.Section7

open Stafford38Challenge

universe u v w

/-- **Left-handed identity.** Every nonzero `d ∈ A_n(k)` has `R, S, F` with
`1 = Rd + SdF`. -/
theorem leftHandedIdentity : LeftHandedIdentity.{u} :=
  Stafford38.LeftHandedCorollary.leftHanded_of_universalStatement Stafford38.Paper.theorem_1_1

open Stafford38.WeylTransposition Stafford38.WeylTranspositionFiltration in
/-- `A_n(k)` is a left Ore domain: the right Ore condition of `A_n(k)ᵐᵒᵖ`,
obtained from the right Ore condition of `A_n(k)` through the transpose. -/
theorem weyl_leftOreCondition (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    AlgebraicAnalysis.OreRightIntersection.RightOreCondition (WeylAlg k n)ᵐᵒᵖ := by
  intro a b ha hb
  have hne : ∀ c : (WeylAlg k n)ᵐᵒᵖ, c ≠ 0 → transpose k n c.unop ≠ 0 := by
    intro c hc h
    apply hc
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_zero]
    simpa only [transpose_transpose, transpose_zero] using congrArg (transpose k n) h
  obtain ⟨x, y, hxy, hx0⟩ :=
    Section6.weyl_rightOreCondition (k := k) n (hne a ha) (hne b hb)
  have hxy' := congrArg (transpose k n) hxy
  simp only [transpose_mul, transpose_transpose] at hxy'
  refine ⟨MulOpposite.op (transpose k n x), MulOpposite.op (transpose k n y), ?_, ?_⟩
  · apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using hxy'
  · intro h
    apply hx0
    have h' := congrArg (fun c => transpose k n c.unop) h
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_zero,
      transpose_mul, transpose_transpose, transpose_zero] using h'

/-- **Corollary 6.3 for left torsion modules.** Every finitely generated torsion
left `A_n(k)`-module is cyclic.  The left analogue of the printed proof
(`Section6.corollary_6_3_of` for the ring `A_n(k)ᵐᵒᵖ`, whose right modules are
the left `A_n(k)`-modules), fed with the left-handed identity `1 = Rd + SdF`
(`leftHandedIdentity`) and the left Ore condition; the two generators of the
left version of [Sta78, Thm. 3.7] come from the same identity. -/
theorem corollary_6_3_left : LeftCorollary_6_3.{u, v} := by
  intro k _ _ n M _ _ _ hM
  let ψ : (WeylAlg k n)ᵐᵒᵖᵐᵒᵖ →+* WeylAlg k n := (RingEquiv.opOp (WeylAlg k n)).symm.toRingHom
  let : Module (WeylAlg k n)ᵐᵒᵖᵐᵒᵖ M := Module.compHom M ψ
  have hsmul : ∀ (a : WeylAlg k n) (m : M),
      (MulOpposite.op (MulOpposite.op a) : (WeylAlg k n)ᵐᵒᵖᵐᵒᵖ) • m = a • m := fun _ _ => rfl
  have hone : ∀ d : (WeylAlg k n)ᵐᵒᵖ, d ≠ 0 →
      ∃ F R S : (WeylAlg k n)ᵐᵒᵖ, (1 : (WeylAlg k n)ᵐᵒᵖ) = d * R + F * d * S := by
    intro d hd
    obtain ⟨R, S, F, h⟩ := leftHandedIdentity k n d.unop
      (fun h0 => hd (MulOpposite.unop_injective (by rw [h0, MulOpposite.unop_zero])))
    refine ⟨MulOpposite.op F, MulOpposite.op R, MulOpposite.op S, ?_⟩
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_one, MulOpposite.unop_add, MulOpposite.unop_mul,
      MulOpposite.unop_op, h, mul_assoc]
  have : Module.Finite (WeylAlg k n)ᵐᵒᵖᵐᵒᵖ M := by
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule (WeylAlg k n) M).FG)
    refine ⟨⟨s, ?_⟩⟩
    let N : Submodule (WeylAlg k n) M :=
      { carrier := Submodule.span (WeylAlg k n)ᵐᵒᵖᵐᵒᵖ (s : Set M)
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := fun c x hx => by
          change c • x ∈ Submodule.span (WeylAlg k n)ᵐᵒᵖᵐᵒᵖ (s : Set M)
          rw [← hsmul]
          exact Submodule.smul_mem _ _ hx }
    have hN : (⊤ : Submodule (WeylAlg k n) M) ≤ N := by
      rw [← hs]
      exact Submodule.span_le.2 fun x hx => Submodule.subset_span hx
    exact eq_top_iff.2 fun x _ => hN Submodule.mem_top
  have hT : Stafford38.Paper.Section2.IsTorsion (WeylAlg k n)ᵐᵒᵖ M := by
    intro m
    obtain ⟨d, hd, hdm⟩ := hM m
    refine ⟨MulOpposite.op d, fun h => hd (MulOpposite.op_injective (by rw [h, MulOpposite.op_zero])),
      ?_⟩
    rw [hsmul, hdm]
  have hOre := weyl_leftOreCondition k n
  obtain ⟨m, hm⟩ := (Section6.corollary_6_3_of hOre hone hT
    ⟨Section6.two_generators_of_identity hOre hone hT,
      fun l hl => Section6.stably_generated_of_identity hOre hone hT l (by omega)⟩).1
  refine ⟨m, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hm x
  exact ⟨a.unop, ha⟩

section Localized

open Stafford38.DifferentialOperators

variable {k : Type u} {B : Type v} [CommRing k] [CommRing B] [Algebra k B]

/-- The iterated-commutator order of `Stafford38Challenge` is the recursive
order filtration `order N` of `AlgebraicAnalysis`. -/
theorem isDifferentialOperatorOfOrder_iff (N : ℕ) (P : Module.End k B) :
    IsDifferentialOperatorOfOrder k B N P ↔ P ∈ order (k := k) (R := B) N := by
  induction N generalizing P with
  | zero =>
      rw [mem_order_zero_iff]
      constructor
      · intro h a
        exact h [a] rfl
      · intro h b hb
        match b, hb with
        | [a], _ => exact h a
  | succ N ih =>
      rw [mem_order_succ_iff]
      constructor
      · intro h a
        rw [← ih]
        intro b hb
        exact h (a :: b) (by simp [hb])
      · intro h b hb
        match b, hb with
        | a :: b, hb => exact (ih _).2 (h a) b (by simpa using hb)

theorem isDifferentialOperator_iff (P : Module.End k B) :
    IsDifferentialOperator k B P ↔ P ∈ algebra (k := k) (R := B) := by
  simp only [IsDifferentialOperator, isDifferentialOperatorOfOrder_iff, mem_algebra_iff]

/-- The identity in the subalgebra `D_k(B)` gives the Mathlib-only form. -/
theorem hasDifferentialIdentity_of
    (h : AlgebraicAnalysis.TwoGeneratorIdentity (algebra (k := k) (R := B))) :
    HasDifferentialIdentity k B := by
  intro d hd hd0
  obtain ⟨F, R, S, hone⟩ := h ⟨d, (isDifferentialOperator_iff d).1 hd⟩
    (fun h0 => hd0 (congrArg Subtype.val h0))
  refine ⟨F, R, S, (isDifferentialOperator_iff _).2 F.2, (isDifferentialOperator_iff _).2 R.2,
    (isDifferentialOperator_iff _).2 S.2, ?_⟩
  exact congrArg Subtype.val hone

end Localized

section Transport

variable {k : Type u} {B' : Type v} {B : Type w} [CommRing k] [CommRing B'] [CommRing B]
  [Algebra k B'] [Algebra k B]

/-- Conjugation `P ↦ e ∘ P ∘ e⁻¹` of `k`-linear endomorphisms along `e`. -/
abbrev conjEnd (e : B' ≃ₐ[k] B) : Module.End k B' ≃+* Module.End k B :=
  LinearEquiv.conjRingEquiv e.toLinearEquiv

theorem conjEnd_apply (e : B' ≃ₐ[k] B) (P : Module.End k B') (x : B) :
    conjEnd e P x = e (P (e.symm x)) := rfl

theorem conjEnd_mulLeft (e : B' ≃ₐ[k] B) (b : B') :
    conjEnd e (LinearMap.mulLeft k b) = LinearMap.mulLeft k (e b) := by
  ext x
  simp

theorem foldl_conjEnd (e : B' ≃ₐ[k] B) :
    ∀ (l : List B') (P : Module.End k B'),
      (l.map e).foldl (fun Q c => Q * LinearMap.mulLeft k c - LinearMap.mulLeft k c * Q)
          (conjEnd e P) =
        conjEnd e (l.foldl (fun Q c => Q * LinearMap.mulLeft k c - LinearMap.mulLeft k c * Q) P)
  | [], _ => rfl
  | b :: l, P => by
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← foldl_conjEnd e l]
      congr 1
      rw [map_sub, map_mul, map_mul, conjEnd_mulLeft]

theorem isDifferentialOperator_conjEnd (e : B' ≃ₐ[k] B) {P : Module.End k B'}
    (h : IsDifferentialOperator k B' P) : IsDifferentialOperator k B (conjEnd e P) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun l hl => ?_⟩
  have hl' : (l.map e.symm).map e = l := by
    clear hl
    induction l with
    | nil => rfl
    | cons b l ih => simp only [List.map_cons, AlgEquiv.apply_symm_apply, ih]
  rw [← hl', foldl_conjEnd, hN _ (by simpa using hl), map_zero]

/-- The identity in `D_k(B')` transfers along a `k`-algebra isomorphism `B' ≅ B`. -/
theorem hasDifferentialIdentity_of_algEquiv (e : B' ≃ₐ[k] B)
    (h : HasDifferentialIdentity k B') : HasDifferentialIdentity k B := by
  intro d hd hd0
  let P := conjEnd e.symm d
  have hP : conjEnd e P = d := by
    ext x
    simp [P]
  have hP0 : P ≠ 0 := fun h0 => hd0 (by rw [← hP, h0, map_zero])
  obtain ⟨F, R, S, hF, hR, hS, hone⟩ := h P (isDifferentialOperator_conjEnd e.symm hd) hP0
  refine ⟨conjEnd e F, conjEnd e R, conjEnd e S, isDifferentialOperator_conjEnd e hF,
    isDifferentialOperator_conjEnd e hR, isDifferentialOperator_conjEnd e hS, ?_⟩
  have := congrArg (conjEnd e) hone
  simp only [map_one, map_add, map_mul, hP] at this
  exact this

end Transport

/-- **Localizations.** For every localization `B` of `k[x_1, …, x_n]`, every
nonzero finite-order differential operator `d` on `B` has finite-order `F, R, S`
with `1 = dR + FdS`.  Theorem 1.1 transfers to `D_k(S⁻¹k[x])` by clearing a left
denominator of each operator (`s38_localized_differential`, for `Localization S`)
and then along the isomorphism `Localization S ≅ B`. -/
theorem localizedDifferentialIdentity : LocalizedDifferentialIdentity.{u, v} := by
  intro k _ _ n S B _ _ _ _ _
  have h := hasDifferentialIdentity_of
    (Stafford38.LocalizedDifferentialCorollaries.s38_localized_differential S (Localization S)
      fun d hd => Stafford38.Paper.theorem_1_1 k n d hd)
  exact hasDifferentialIdentity_of_algEquiv
    ((IsLocalization.algEquiv S (Localization S) B).restrictScalars k) h

/-- `potentialSum` over the list of pairs `(a_j, m_j)` is `∑_j a_j x^{m_j}`. -/
theorem potentialSum_ofFn {D : Type v} [Ring D] (x : D) :
    ∀ (J : ℕ) (a : Fin J → D) (m : Fin J → ℕ),
      Stafford38.Evolution.potentialSum x (List.ofFn fun j => (a j, m j)) =
        ∑ j, a j * x ^ m j
  | 0, _, _ => by simp [Stafford38.Evolution.potentialSum]
  | J + 1, a, m => by
      rw [List.ofFn_succ, Fin.sum_univ_succ, Stafford38.Evolution.potentialSum,
        potentialSum_ofFn x J (fun j => a j.succ) (fun j => m j.succ)]

/-- **Evolutionary identity.** For `r ≥ 1` and `px = xp + 1` in a `k`-algebra,
`d = p^r - ∑_j a_j x^{m_j}` with each `a_j` commuting with `x` and `p` has
`1 = dR + x^r d S`. -/
theorem evolutionaryIdentity : EvolutionaryIdentity.{u, v} := by
  intro k _ _ D _ _ x p hw r hr J a m hx hp
  have hmem : ∀ t ∈ List.ofFn (fun j => (a j, m j)), ∃ j, t = (a j, m j) := by
    intro t ht
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ht
    exact ⟨j, rfl⟩
  obtain ⟨R, S, h⟩ := Stafford38.Evolution.evolutionaryCorollary k hw hr
    (List.ofFn fun j => (a j, m j))
    (fun t ht => by obtain ⟨j, rfl⟩ := hmem t ht; exact hx j)
    (fun t ht => by obtain ⟨j, rfl⟩ := hmem t ht; exact hp j) rfl
  exact ⟨R, S, by rw [← potentialSum_ofFn x J a m]; exact h⟩

#print axioms leftHandedIdentity
#print axioms weyl_leftOreCondition
#print axioms corollary_6_3_left
#print axioms localizedDifferentialIdentity
#print axioms evolutionaryIdentity

end Stafford38.Paper.Section7
