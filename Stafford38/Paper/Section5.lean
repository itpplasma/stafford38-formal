module

public import Stafford38.Paper.Section5.Place
public import Stafford38.Paper.Section5.ResidueBasis
public import Stafford38.Paper.Section5.TangentCone
public import Stafford38.Paper.Section5.GenericTangentRank
public import Stafford38.Paper.Section5.Steps
public import Stafford38.Paper.Section5.Proof
public import Stafford38.Paper.Section5.KaehlerRankBound
public import Stafford38.Paper.Section5.Completion
public import Stafford38.Geometry.ProjectiveConormalDirections

@[expose] public section

/-!
# Section 5.2 of the paper: Theorem 5.7 and its lemmas

The paper's lemmas are stated and proved in
`Stafford38.Paper.Section5.Place` (Lemmas 5.9, 5.10),
`Stafford38.Paper.Section5.ResidueBasis` (Lemma 5.11),
`Stafford38.Paper.Section5.TangentCone` and
`Stafford38.Paper.Section5.GenericTangentRank` (Lemmas 5.12, 5.13).

The paragraphs of the proof of Theorem 5.7(i) between those lemmas are stated
and proved in `Stafford38.Paper.Section5.Steps`; the theorems
`witness_lemma_*` there apply Lemmas 5.11–5.13 to the discrete valuation ring
and the Laurent column `q(t)` of the proof.
`GeneralDivisorialVisibleFrame.generalDivisorialVisibleFrameWithKaehlerFinite`
builds the place `V` of Lemmas 5.9–5.10 with `Ω_{V/K}` finitely generated, `Stafford38.Paper.Section5.Completion`
states the paragraph `V̂ ≅ κ[[t]]` and the bound of Lemma 5.12(a) at `V`, and
`Stafford38.Paper.Section5.KaehlerRankBound` proves that bound for any discrete
valuation ring.  `Stafford38.Paper.Section5.Proof` chains the paragraphs into
`theorem_5_7_i_paper`, which `theorem_5_7_i` below restates; `theorem_5_7_ii`
follows from it by `step_dir_of_fibre`.  The terminal
theorem in `GeneralAsymptoticConormal` proves the same statement by a second,
chart-based route and is kept unchanged.
-/

namespace Stafford38.Paper.Section5

open Stafford38.Geometry.ProjectiveConormalDirections

noncomputable section

universe u

/-- **Theorem 5.7(i).** If `Y = V(𝔭)` is nonempty, irreducible and avoids
`H = {x_1 = 0}`, every polynomial vanishing on the conormal cone `N(Y)` over the
smooth locus vanishes at `(1, 0, …, 0)`.  Proved paragraph by paragraph in
`theorem_5_7_i_paper`. -/
theorem theorem_5_7_i
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal)) :=
  theorem_5_7_i_paper hm I havoid

/-- `G(a ξ) = a^{deg G} G(ξ)` for a homogeneous `G`. -/
theorem eval_smul_of_isHomogeneous {k : Type*} [Field k] {n : ℕ}
    (G : MvPolynomial (Fin n) k) (d : ℕ) (hG : G.IsHomogeneous d)
    (a : k) (v : Fin n → k) :
    MvPolynomial.eval (a • v) G = a ^ d * MvPolynomial.eval v G := by
  simp only [MvPolynomial.eval_eq']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hd : ∑ i, s i = d := by
    rw [← s.sum_fintype (fun _ c => c) (fun _ => rfl)]
    simpa [MvPolynomial.IsHomogeneous, Finsupp.weight_apply] using
      hG (MvPolynomial.mem_support_iff.mp hs)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hd]
  ring

/-- **Proof of Theorem 5.7(ii) from (i).**  Let every polynomial vanishing on
`N(Y)` vanish at `ξ ≠ 0`, and let `G` be homogeneous of degree `d` and vanish on
all classes `[ξ']` with `0 ≠ ξ' ∈ N(Y)`.  By homogeneity `G` vanishes on every
nonzero `ξ' ∈ N(Y)`, and at `0` if `d > 0`, hence on `N(Y)`; so `G(ξ) = 0`, and
`G` vanishes at every representative `a ξ` of `[ξ]`.  If `d = 0`, `G` is a
constant vanishing at a class of `N(Y)`, so `G = 0`; that such a class exists
follows from the hypothesis itself, applied to a coordinate `ξ_i ≠ 0`. -/
theorem step_dir_of_fibre {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (ξ : Fin n → k) (hξ : ξ ≠ 0)
    (hvan : ξ ∈ MvPolynomial.zeroLocus k
      (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I))) :
    Projectivization.mk k ξ hξ ∈
      projectiveHomogeneousClosure
        (projectivizedDirectionSet (smoothConormalDirectionSet I)) := by
  intro G d hG hT
  -- `G` vanishes on every nonzero `ξ' ∈ N(Y)`.
  have hnonzero : ∀ v ∈ smoothConormalFibreProjection I, v ≠ 0 →
      MvPolynomial.eval v G = 0 := by
    intro v hv hv0
    rcases hv with ⟨y, hy, hc⟩
    exact hT ⟨v, ⟨y, hy, hv0, hc⟩, hv0, rfl⟩ v hv0 rfl
  have hξG : MvPolynomial.eval ξ G = 0 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · -- `d = 0`: `G` is constant, and some nonzero `ξ' ∈ N(Y)` exists.
      subst hd
      have hconst : ∀ x : Fin n → k, MvPolynomial.eval x G = MvPolynomial.eval 0 G := by
        intro x
        have h := eval_smul_of_isHomogeneous G 0 hG 0 x
        rw [zero_smul, pow_zero, one_mul] at h
        exact h.symm
      obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by simpa [funext_iff] using hξ
      obtain ⟨v, hv, hv0⟩ : ∃ v ∈ smoothConormalFibreProjection I, v ≠ 0 := by
        by_contra hnone
        push Not at hnone
        apply hi
        have hXi : MvPolynomial.X i ∈ MvPolynomial.vanishingIdeal k
            (smoothConormalFibreProjection I) := by
          rw [MvPolynomial.mem_vanishingIdeal_iff]
          intro v hv
          rw [hnone v hv]
          simp
        simpa using (MvPolynomial.mem_zeroLocus_iff.mp hvan) _ hXi
      rw [hconst, ← hconst v]
      exact hnonzero v hv hv0
    · -- `d > 0`: `G(0) = 0` too, so `G` vanishes on `N(Y)`.
      have hGvan : G ∈ MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I) := by
        rw [MvPolynomial.mem_vanishingIdeal_iff]
        intro v hv
        by_cases hv0 : v = 0
        · subst hv0
          have h := eval_smul_of_isHomogeneous G d hG 0 0
          rw [smul_zero, zero_pow hd.ne', zero_mul] at h
          exact h
        · exact hnonzero v hv hv0
      exact (MvPolynomial.mem_zeroLocus_iff.mp hvan) _ hGvan
  -- Every representative `a ξ` of `[ξ]`.
  intro v hv hz
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff k ξ v hξ hv).mp hz
  have hscaled := eval_smul_of_isHomogeneous G d hG (a : k) v
  have ha' : (a : k) • v = ξ := by
    rw [← Units.smul_def]
    exact ha
  rw [ha', hξG] at hscaled
  exact (mul_eq_zero.mp hscaled.symm).resolve_left (pow_ne_zero d (Units.ne_zero a))

/-- **Theorem 5.7(ii).** `[dx_1] ∈ Dir(Y)`: by `step_dir_of_fibre`, every
homogeneous `G` vanishing on the classes `[ξ]`, `0 ≠ ξ ∈ N(Y)`, vanishes on
`N(Y)`, hence at `(1, 0, …, 0)` by (i). -/
theorem theorem_5_7_ii
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    Projectivization.mk k
        (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0)
        (by intro h; have := congrFun h ⟨0, hm⟩; simp at this) ∈
      projectiveHomogeneousClosure
        (projectivizedDirectionSet (smoothConormalDirectionSet I.asIdeal)) :=
  step_dir_of_fibre I.asIdeal _ _ (theorem_5_7_i hm I havoid)

#print axioms eval_smul_of_isHomogeneous
#print axioms step_dir_of_fibre
#print axioms theorem_5_7_i
#print axioms theorem_5_7_ii

end

end Stafford38.Paper.Section5
