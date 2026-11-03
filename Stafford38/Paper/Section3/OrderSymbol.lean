module

public import Stafford38.Paper.Section3.Transport
public import Stafford38.Characteristic.AssociatedGradedModule
public import Stafford38.Geometry.ConormalAxisContradiction

@[expose] public section

/-!
# Definition 3.4, Lemma 3.5 and Proposition 3.6

For the normal form `d̃` of (3.1) with `N = deg_B d̃`, the order principal
symbol `σ_N^ord(d̃)` is `presentedPrincipalComponent k orderWeight N d̃` in
`k[x, ξ] = SymbolRing k (n + 1)`, where `Sum.inl i` indexes `x_{i+1}` and
`Sum.inr i` indexes `ξ_{i+1}`.  A polynomial `P ∈ k[ξ_1, …, ξ_{n+1}]` is an
element of `MvPolynomial (Fin (n + 1)) k`, regarded in `k[x, ξ]` through
`rename Sum.inr`.

`Q = A/𝓘` carries the order filtration `Q_m = q F_m` induced by `q = [1]`;
its associated graded module is `grQ`, the external direct sum of the
quotients `Q_m / Q_{m-1}` with its `k[x, ξ]`-module structure
(Definition 2.4, `Stafford38.Paper.Section2.grCyclic`).
-/

namespace Stafford38.Paper.Section3

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicHomogeneousChart
open Stafford38.Geometry.ConormalAxisContradiction
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylEulerResidue
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBW
open Stafford38.WeylPBWMonicBridge
open Stafford38.Paper.Section2

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- **Definition 3.4.** `P = ∑_{i=0}^N c_i ξ₁^i ∈ k[ξ_1, …, ξ_n]`, with
`c_i ∈ k[ξ_2, …, ξ_n]`, is monic of degree `N` in `ξ₁` if `c_N = 1`.  Here
`finSuccEquiv` writes `P` as a polynomial in `ξ₁ = X 0` with coefficients in
the remaining variables. -/
def IsMonicInXi1 {n : ℕ} (N : ℕ) (P : MvPolynomial (Fin (n + 1)) k) : Prop :=
  (MvPolynomial.finSuccEquiv k n P).natDegree ≤ N ∧
    (MvPolynomial.finSuccEquiv k n P).coeff N = 1

/-- The order principal symbol `σ_N^ord(d̃)`. -/
abbrev orderSymbol {n : ℕ} (N : ℕ) (dt : PresentedWeyl k n) : SymbolRing k n :=
  presentedPrincipalComponent k (@orderWeight n) N dt

/-- **Lemma 3.5, paragraph 1.** Since `deg_B d̃ = N`, every PBW monomial
`x^α ∂^β` of `d̃` has `|α| + |β| ≤ N`; a monomial contributing to the order-`N`
part has `|β| = N`, hence `|α| = 0`.  So `d̃ ∈ F_N` and its order-`N` part is a
`k`-linear combination of `∂^β` with `|β| = N`: `σ_N^ord(d̃)` involves no `x_i`
and is homogeneous of degree `N`. -/
theorem step_3_5_fibre {n N : ℕ} {dt : PresentedWeyl k n} (hdeg : bernsteinDegree k dt = N) :
    dt ∈ orderPiece k n N ∧ IsFibreOnly k (orderSymbol k N dt) ∧
      (orderSymbol k N dt).IsHomogeneous N := by
  have hB : dt ∈ bernsteinPiece k n N := (bernsteinDegree_le_iff k dt).mp hdeg.le
  have hfibre : IsFibreOnly k (orderSymbol k N dt) := by
    intro m hm i
    change AddMonoidAlgebra.coeff (orderSymbol k N dt) m ≠ 0 at hm
    rw [coeff_presentedPrincipalComponent] at hm
    by_cases horder : monomialWeight (@orderWeight n) m = N
    · rw [ite_eq_left horder] at hm
      exact coordinateExponent_eq_zero_of_order_eq_of_bernstein_le m horder
        ((mem_presentedWeightPiece k (@bernsteinWeight n) N dt).mp hB m hm) i
    · rw [ite_eq_right horder] at hm
      exact (hm rfl).elim
  refine ⟨bernsteinPiece_le_orderPiece k n N hB, hfibre, ?_⟩
  apply isHomogeneous_of_orderHomogeneous_of_isFibreOnly _ hfibre
  exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
    (w := @orderWeight n) (n := N) (presentedNormalFormLinearEquiv k n dt)

/-- **Lemma 3.5, paragraph 1 (conclusion).** A symbol without `x_i` is a
polynomial `P(ξ)` in the fibre variables alone, homogeneous of the same
degree. -/
theorem step_3_5_fibre_polynomial {n N : ℕ} {s : SymbolRing k n} (hfibre : IsFibreOnly k s)
    (hs : s.IsHomogeneous N) :
    ∃ P : MvPolynomial (Fin n) k, s = MvPolynomial.rename Sum.inr P ∧ P.IsHomogeneous N := by
  obtain ⟨P, hP⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range s Sum.inr
    Sum.inr_injective (by
      intro i hi
      rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hi
      obtain ⟨m, hm, hmi⟩ := hi
      rcases i with i | i
      · exact absurd (hfibre m (MvPolynomial.mem_support_iff.mp hm) i)
          (Finsupp.mem_support_iff.mp hmi)
      · exact ⟨i, rfl⟩)
  refine ⟨P, hP.symm, ?_⟩
  rw [← MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Sum.inr_injective, hP]
  exact hs

/-- **Lemma 3.5, paragraph 2 (the terms `p^j a_j`, `j < N`).** Since
`a_j ∈ C` involves no further factor of `p = ∂₁`, every order-`N` monomial of
`p^j a_j` has `∂₁`-exponent exactly `j < N` (and so carries a positive power of
some transverse `∂_i`); it contributes only to the coefficient `c_j` of
`ξ₁^j`, never to `c_N` (tex lines 494–500).  The monomials are read in the
order symbol, `σ_N^ord(p^j a_j) = ξ₁^j σ_{N-j}^ord(a_j)`, whose monomials are
the order-`N` PBW monomials of `p^j a_j`. -/
theorem step_3_5_lower_term {n j N : ℕ} (hj : j < N) {a : PresentedWeyl k (n + 1)}
    (haC : a ∈ C k n) (ha : bernsteinDegree k a ≤ N - j) (m : PhaseVar (n + 1) →₀ ℕ)
    (hm : MvPolynomial.coeff m (orderSymbol k N (p k n ^ j * a)) ≠ 0) :
    m (.inr 0) = j := by
  have haF : a ∈ orderPiece k (n + 1) (N - j) :=
    bernsteinPiece_le_orderPiece k (n + 1) _ ((bernsteinDegree_le_iff k a).mp ha)
  rw [orderSymbol, principal_order_p_pow_mul k hj.le haF] at hm
  simp only [MvPolynomial.coeff] at hm
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul'] at hm
  split_ifs at hm with hle
  · rw [one_mul, coeff_presentedPrincipalComponent] at hm
    split_ifs at hm
    swap
    · exact absurd rfl hm
    have h0 := normalForm_C_no_p k haC _ hm
    have h1 := Finsupp.le_def.mp hle (.inr 0)
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same] at h0 h1
    omega
  · exact absurd rfl hm

/-- **Lemma 3.5, paragraph 2 (the coefficient `c_N`).** The monomial
`p^N = ∂₁^N` occurs with coefficient `1`, and by `step_3_5_lower_term` no other
term contributes to `c_N`: the coefficient of `ξ₁^N` in `σ_N^ord(d̃)` is `1`
(tex lines 494–503). -/
theorem step_3_5_pure_coefficient {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (hform : IsMonicNormalForm k N dt) :
    MvPolynomial.coeff (Finsupp.single (.inr (0 : Fin (n + 1))) N) (orderSymbol k N dt) = 1 := by
  obtain ⟨a, ha, rfl⟩ := hform
  obtain ⟨-, hσN⟩ := p_pow_piece_principal k (@orderWeight (n + 1)) rfl N
  rw [orderSymbol, map_add, map_sum, hσN]
  simp only [MvPolynomial.coeff]
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_sum,
    Finset.sum_eq_zero, add_zero, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial,
    ite_eq_left rfl]
  intro j hj
  have hjN := Finset.mem_range.mp hj
  by_contra hne
  have := step_3_5_lower_term k hjN (ha j hjN).1 (ha j hjN).2 _ hne
  simp at this
  omega

/-- `d̃` has order exactly `N`: `d̃ ∈ F_N` and `d̃ ∉ F_j` for `j < N`, since its
order-`N` symbol is nonzero. -/
theorem step_3_5_order {n N : ℕ} {dt : PresentedWeyl k n} (hF : dt ∈ orderPiece k n N)
    (hne : orderSymbol k N dt ≠ 0) :
    dt ∈ orderPiece k n N ∧ ∀ j < N, dt ∉ orderPiece k n j :=
  ⟨hF, fun _ hj hmem => hne (presentedPrincipalComponent_eq_zero_of_mem_of_lt k _ dt hmem hj)⟩

private theorem degree_cons (n N : ℕ) (m : Fin n →₀ ℕ) :
    (Finsupp.cons N m).degree = N + m.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.cons_zero]
  simp [Finsupp.cons_succ]

/-- **Lemma 3.5, paragraph 2 (conclusion).** If `P` is homogeneous of degree
`N` and its coefficient of `ξ₁^N` is `1`, then `c_N = 1` identically, so `P`
is monic of degree `N` in `ξ₁` (Definition 3.4), `deg P = N`, and evaluating
at `(1, 0, …, 0)` gives `P(1, 0, …, 0) = 1`. -/
theorem step_3_5_monic {n N : ℕ} {P : MvPolynomial (Fin (n + 1)) k} (hP : P.IsHomogeneous N)
    (hcoeff : MvPolynomial.coeff (Finsupp.single 0 N) P = 1) :
    IsMonicInXi1 k N P ∧ P.totalDegree = N ∧
      MvPolynomial.eval (fun i => if i = 0 then 1 else 0) P = 1 := by
  have hne : P ≠ 0 := by
    rintro rfl
    simp at hcoeff
  refine ⟨⟨?_, ?_⟩, hP.totalDegree hne, ?_⟩
  · rw [MvPolynomial.natDegree_finSuccEquiv]
    exact (MvPolynomial.degreeOf_le_totalDegree P 0).trans hP.totalDegree_le
  · ext m
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    by_cases hm : m = 0
    · subst m
      have h0 : (Finsupp.cons N (0 : Fin n →₀ ℕ)) = Finsupp.single 0 N := by
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      rw [h0]
      simpa using hcoeff
    · rw [MvPolynomial.coeff_one, ite_eq_right (Ne.symm hm)]
      apply hP.coeff_eq_zero
      rw [degree_cons]
      have : m.degree ≠ 0 := fun h => hm ((Finsupp.degree_eq_zero_iff m).mp h)
      omega
  · have hsym := eval_axis_eq_one_of_pureCoefficient_one (k := k) (n := n + 1) (N := N)
      (.inr (0 : Fin (n + 1))) (P := MvPolynomial.rename Sum.inr P)
      ((MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Sum.inr_injective).mpr hP) (by
        have h := MvPolynomial.coeff_rename_mapDomain
          (Sum.inr : Fin (n + 1) → Fin (n + 1) ⊕ Fin (n + 1)) Sum.inr_injective P
          (Finsupp.single 0 N)
        rw [Finsupp.mapDomain_single] at h
        simpa [MvPolynomial.coeff] using h.trans hcoeff)
    have hpt : (axisPoint k (.inr (0 : Fin (n + 1))) ∘ Sum.inr : Fin (n + 1) → k) =
        fun i => if i = 0 then 1 else 0 := by
      funext i
      simp [axisPoint]
    rwa [MvPolynomial.eval_rename, hpt] at hsym

/-- **Lemma 3.5.** Let `d̃ = p^N + ∑_{j<N} p^j a_j` with `a_j ∈ C`,
`deg_B a_j ≤ N - j` as in (3.1), and `N = deg_B d̃`.  Then `d̃` has order `N`,
and its order principal symbol is a polynomial in `ξ` alone,
`σ_N^ord(d̃) = P(ξ)` with `P ∈ k[ξ_1, …, ξ_n]`, `deg P = N` (eq. (3.3)); `P` is
homogeneous, monic of degree `N` in `ξ₁`, and `P(1, 0, …, 0) = 1`
(eq. (3.4)). -/
theorem lemma_3_5 {n N : ℕ} {dt : PresentedWeyl k (n + 1)} (hform : IsMonicNormalForm k N dt)
    (hdeg : bernsteinDegree k dt = N) :
    (dt ∈ orderPiece k (n + 1) N ∧ ∀ j < N, dt ∉ orderPiece k (n + 1) j) ∧
      ∃ P : MvPolynomial (Fin (n + 1)) k,
        orderSymbol k N dt = MvPolynomial.rename Sum.inr P ∧
          P.IsHomogeneous N ∧ P.totalDegree = N ∧ IsMonicInXi1 k N P ∧
          MvPolynomial.eval (fun i => if i = 0 then 1 else 0) P = 1 := by
  obtain ⟨hF, hfibre, hhom⟩ := step_3_5_fibre k hdeg
  obtain ⟨P, hsP, hP⟩ := step_3_5_fibre_polynomial k hfibre hhom
  have hpure := step_3_5_pure_coefficient k hform
  have hne : orderSymbol k N dt ≠ 0 := by
    intro h
    rw [h] at hpure
    simp at hpure
  have hcoeff : MvPolynomial.coeff (Finsupp.single 0 N) P = 1 := by
    have h := MvPolynomial.coeff_rename_mapDomain
      (Sum.inr : Fin (n + 1) → Fin (n + 1) ⊕ Fin (n + 1)) Sum.inr_injective P
      (Finsupp.single 0 N)
    rw [Finsupp.mapDomain_single, ← hsP] at h
    simpa [MvPolynomial.coeff] using h.symm.trans hpure
  obtain ⟨hmonic, htot, heval⟩ := step_3_5_monic k hP hcoeff
  exact ⟨step_3_5_order k hF hne, P, hsP, hP, htot, hmonic, heval⟩

/-- Equation (3.4) read in `k[x, ξ]`: `σ_N^ord(d̃)` takes the value `1` at the
covector `ξ = (1, 0, …, 0)` over every base point `x = 0`, i.e. at
`axisPoint (.inr 0)`. -/
theorem lemma_3_5_eval_axis {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (hform : IsMonicNormalForm k N dt) (hdeg : bernsteinDegree k dt = N) :
    MvPolynomial.eval (axisPoint k (.inr (0 : Fin (n + 1)))) (orderSymbol k N dt) = 1 := by
  obtain ⟨-, P, hsP, -, -, -, heval⟩ := lemma_3_5 k hform hdeg
  have hpt : (axisPoint k (.inr (0 : Fin (n + 1))) ∘ Sum.inr : Fin (n + 1) → k) =
      fun i => if i = 0 then 1 else 0 := by
    funext i
    simp [axisPoint]
  rw [hsP, MvPolynomial.eval_rename, hpt]
  exact heval

/-- The associated graded module `gr Q` of `Q = A/𝓘` for the order filtration
`Q_m = q F_m` induced by `q = [1]` (Definition 2.4, `Section2.grCyclic`). -/
abbrev grQ {n : ℕ} (N : ℕ) (dt : PresentedWeyl k (n + 1)) :=
  grCyclic k (idealI k N dt)

/-- **Proposition 3.6, proof, first sentence.** `Q_•` is good because `Q` is
cyclic: `Q_m = qF_m` is a compatible filtration of `Q` (Definition 2.4), and
`gr Q` is finite over `k[x, ξ]`, generated by `q̄`. -/
theorem step_3_6_generated {n N : ℕ} (dt : PresentedWeyl k (n + 1)) :
    IsCompatibleFiltration (orderFiltration k (n + 1))
        (cyclicFiltration (orderFiltration k (n + 1)) (qClass k (idealI k N dt))) ∧
      Module.Finite (SymbolRing k (n + 1)) (grQ k N dt) ∧
      ∀ m : grQ k N dt, ∃ f : SymbolRing k (n + 1), f • qBar k (idealI k N dt) = m :=
  ⟨cyclicFiltration_order_isCompatible k _, grCyclic_good k _, grCyclic_generated k _⟩

/-- **Proposition 3.6, proof, second sentence.** `q d̃ = [d̃] = 0` in `Q`
because `d̃ ∈ 𝓘`, and `d̃ ∈ F_N`, so `q d̃ ∈ Q_N`; its image `q̄ · P` in
`Q_N/Q_{N-1}` is zero. -/
theorem step_3_6_kills {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (hF : dt ∈ orderPiece k (n + 1) N) :
    orderSymbol k N dt • qBar k (idealI k N dt) = 0 := by
  have h := smul_orderAssociatedGradedOf_mk_eq_of_mul k (idealI k N dt)
    (orderPieceOne (n := n + 1) k) (⟨dt, hF⟩ : orderPiece k (n + 1) N)
  change orderSymbol k N dt • qBar k (idealI k N dt) = _ at h
  rw [h]
  have hzero : orderPieceToQuotientGraded k (idealI k N dt) (0 + N)
      ⟨(orderPieceOne (n := n + 1) k : PresentedWeyl k (n + 1)) * dt,
        mul_mem_orderPiece k (orderPieceOne (n := n + 1) k).property hF⟩ = 0 := by
    have hpiece : orderPieceToQuotientPiece k (idealI k N dt) (0 + N)
        ⟨(orderPieceOne (n := n + 1) k : PresentedWeyl k (n + 1)) * dt,
          mul_mem_orderPiece k (orderPieceOne (n := n + 1) k).property hF⟩ = 0 := by
      apply Subtype.ext
      change Submodule.Quotient.mk ((1 : PresentedWeyl k (n + 1)) * dt) = 0
      rw [one_mul, Submodule.Quotient.mk_eq_zero]
      exact firstGenerator_mem (x₁ k n) dt N
    rw [orderPieceToQuotientGraded, LinearMap.comp_apply, hpiece, map_zero]
  rw [hzero]
  exact map_zero _

/-- **Proposition 3.6.** Equip `Q` with the order filtration `Q_m = qF_m`
induced by the cyclic generator `q = [1]`, and write `P = σ_N^ord(d̃)`.  Then
`P ∈ Ann_{k[x,ξ]} gr Q` (eq. (3.5)). -/
theorem proposition_3_6 {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (hform : IsMonicNormalForm k N dt) (hdeg : bernsteinDegree k dt = N) :
    orderSymbol k N dt ∈ Module.annihilator (SymbolRing k (n + 1)) (grQ k N dt) := by
  obtain ⟨⟨hF, -⟩, -⟩ := lemma_3_5 k hform hdeg
  rw [Module.mem_annihilator]
  intro m
  obtain ⟨f, rfl⟩ := (step_3_6_generated k dt).2.2 m
  rw [smul_comm, step_3_6_kills k hF, smul_zero]

#print axioms lemma_3_5
#print axioms lemma_3_5_eval_axis
#print axioms proposition_3_6

end

end Stafford38.Paper.Section3
