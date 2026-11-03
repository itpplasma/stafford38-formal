module

public import Stafford38.Paper.Section3.MonicForm

@[expose] public section

/-!
# Section 3: the scalar case and Proposition 3.2

The opening paragraph of Section 3 settles Bernstein degree `0`.  The proof of
Proposition 3.2 is split into its five paragraphs, `step_3_2_*`, and
`proposition_3_2` chains them; the second paragraph calls Lemma 3.1.

Notation: `e_p = phaseBasis k (.inr 0)` is the basis vector of `𝕍` for
`p = ∂₁`; evaluation of a symbol at `e_p` is evaluation at
`axisPoint k (.inr 0)`, the same function.
-/

namespace Stafford38.Paper.Section3

open Stafford38.Characteristic
open Stafford38.CharacteristicHomogeneousChart
open Stafford38.CharacteristicLinearAction
open Stafford38.CharacteristicSymplecticCompletion
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylMonicNormalization
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylPBW
open Stafford38.Paper.Section2

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- **Section 3, opening paragraph.** If `N = deg_B d = 0`, then
`d ∈ B_0 = k` is a nonzero scalar `c`, hence a unit, and `1 = dR + FdS` with
`F = 1`, `R = d⁻¹ = c⁻¹`, `S = 0`.  Otherwise `N ≥ 1`. -/
theorem step_scalar_case {n : ℕ} {d : PresentedWeyl k n} (hd : d ≠ 0) (hN : bernsteinDegree k d = 0) :
    ∃ c : k, c ≠ 0 ∧ d = algebraMap k (PresentedWeyl k n) c ∧
      (1 : PresentedWeyl k n) = d * algebraMap k _ c⁻¹ + 1 * d * 0 := by
  have hpiece : d ∈ bernsteinPiece k n 0 := (bernsteinDegree_le_iff k d).mp hN.le
  obtain ⟨c, rfl⟩ := eq_algebraMap_of_mem_bernsteinPiece_zero k hpiece
  have hc : c ≠ 0 := by
    rintro rfl
    exact hd (map_zero _)
  refine ⟨c, hc, rfl, ?_⟩
  rw [mul_zero, add_zero, ← map_mul, mul_inv_cancel₀ hc, map_one]

/-- A nonzero `d` lies in `B_N` for `N = deg_B d` (Definition 2.3), and its
Bernstein symbol `σ_N^B(d) ∈ B_N/B_{N-1}` (`Section2.symbol`), read in
`gr A_n(k) = k[x, ξ]` (`grEquivSymbolRing`), is the degree-`N` principal component,
nonzero and homogeneous of degree `N`. -/
theorem bernsteinSymbol_ne_zero {n : ℕ} {d : PresentedWeyl k n} (hd : d ≠ 0) :
    d ∈ bernsteinPiece k n (bernsteinDegree k d) ∧
      presentedPrincipalComponent k (@bernsteinWeight n) (bernsteinDegree k d) d ≠ 0 ∧
      (presentedPrincipalComponent k (@bernsteinWeight n) (bernsteinDegree k d) d).IsHomogeneous
        (bernsteinDegree k d) ∧
      symbol (isFiltration_bernstein k n) d ≠ 0 ∧
      grEquivSymbolRing k (@bernsteinWeight n)
          (DirectSum.of _ (bernsteinDegree k d) (symbol (isFiltration_bernstein k n) d)) =
        presentedPrincipalComponent k (@bernsteinWeight n) (bernsteinDegree k d) d := by
  have hmem : d ∈ bernsteinPiece k n (bernsteinDegree k d) :=
    mem_filtrationDegree (isFiltration_bernstein k n) d
  obtain ⟨N, hpiece, hne⟩ := exists_top_bernstein_piece k hd
  obtain rfl : bernsteinDegree k d = N := bernsteinDegree_eq_of_principal_ne_zero k hpiece hne
  refine ⟨hmem, hne, principal_isHomogeneous k d, ?_, ?_⟩
  swap
  · let _ := MvPolynomial.weightedDecomposition k (@bernsteinWeight n)
    simp only [grEquivSymbolRing, LinearEquiv.trans_apply]
    erw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_single]
    erw [DirectSum.decomposeLinearEquiv_symm_apply, DirectSum.decompose_symm_of]
    rfl
  intro h0
  exact hne ((grPiece_mk_eq_zero_iff k (@bernsteinWeight n) ⟨d, hmem⟩).mp h0)

/-- **Proposition 3.2, paragraph 1.** The Bernstein symbol `s` of `d` is a
nonzero homogeneous polynomial of degree `N ≥ 1` on `𝕍`.  A field of
characteristic zero is infinite, so `s(v) ≠ 0` for some `v`; as `s(0) = 0`,
`v ≠ 0`. -/
theorem step_3_2_nonvanishing [CharZero k] {n N : ℕ} {s : SymbolRing k n}
    (hs : s.IsHomogeneous N) (hne : s ≠ 0) (hN : 1 ≤ N) :
    ∃ v : PhaseVar n → k, MvPolynomial.eval v s ≠ 0 ∧ v ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_eval_ne_zero_of_homogeneous k hs hne
  refine ⟨v, hv, ?_⟩
  rintro rfl
  apply hv
  have hc : MvPolynomial.coeff 0 s = 0 := hs.coeff_eq_zero (by simp; omega)
  simpa [MvPolynomial.eval_zero', MvPolynomial.constantCoeff] using hc

/-- **Proposition 3.2, paragraph 2 (first part).** By Lemma 3.1 there is an
`ω`-preserving automorphism `h` of `𝕍` with `h(e_p) = v`. -/
theorem step_3_2_h [CharZero k] {n : ℕ} {v : PhaseVar n → k} (hv : v ≠ 0)
    (t : PhaseVar n) :
    ∃ h : (PhaseVar n → k) ≃ₗ[k] (PhaseVar n → k),
      (∀ x y, omega k n (h x) (h y) = omega k n x y) ∧ h (phaseBasis k t) = v := by
  have he : phaseBasis k t ≠ 0 := by
    intro h
    have := congrFun h t
    simp [phaseBasis] at this
  exact (lemma_3_1 n (omega k n) (omega_isSymplectic k n).1 (omega_isSymplectic k n).2
    (finrank_phaseSpace k n) hv).2 _ he

/-- **Proposition 3.2, paragraph 2 (second part).** If `h` preserves `ω`,
then `hᵀ J h = J`; inverting and using `J⁻¹ = -J` gives `h J hᵀ = J`, so the
matrix `M = h` (whose rows are the images `g(u_i)` of the generators for
`g = hᵀ`) is symplectic, and `M e_p = h(e_p)`. -/
theorem step_3_2_transpose {n : ℕ}
    (h : (PhaseVar n → k) ≃ₗ[k] (PhaseVar n → k))
    (hpres : ∀ x y, omega k n (h x) (h y) = omega k n x y) :
    ∃ g : Matrix.symplecticGroup (Fin n) k,
      g.1 = LinearMap.toMatrix' h.toLinearMap ∧
        ∀ e, Matrix.mulVec g.1 e = h e :=
  ⟨⟨_, toMatrix_mem_symplecticGroup k h.toLinearMap hpres⟩, rfl,
    fun e => LinearMap.toMatrix'_mulVec h.toLinearMap e⟩

/-- **Proposition 3.2, paragraph 3.** `Φ_g` maps `B_m` into `B_m`, and modulo
`B_{N-1}` it substitutes `u_i ↦ ∑_j M_ij u_j` in the commutative symbol, so
the Bernstein symbol of `Φ_g(d)` is `s_g : a ↦ s(Ma)`; at `e_p` its value is
`s(M e_p)`.  If this value is nonzero, `deg_B Φ_g(d) = N`. -/
theorem step_3_2_symbol {n N : ℕ} (g : Matrix.symplecticGroup (Fin n) k)
    {d : PresentedWeyl k n} (hd : d ∈ bernsteinPiece k n N) (t : PhaseVar n) :
    phiG k g d ∈ bernsteinPiece k n N ∧
      MvPolynomial.eval (axisPoint k t)
          (presentedPrincipalComponent k (@bernsteinWeight n) N (phiG k g d)) =
        MvPolynomial.eval (Matrix.mulVec g.1 (phaseBasis k t))
          (presentedPrincipalComponent k (@bernsteinWeight n) N d) ∧
      (MvPolynomial.eval (Matrix.mulVec g.1 (phaseBasis k t))
          (presentedPrincipalComponent k (@bernsteinWeight n) N d) ≠ 0 →
        bernsteinDegree k (phiG k g d) = N) := by
  have hpiece := phiG_mem_bernsteinPiece k g hd
  have heval : MvPolynomial.eval (axisPoint k t)
      (presentedPrincipalComponent k (@bernsteinWeight n) N (phiG k g d)) =
      MvPolynomial.eval (Matrix.mulVec g.1 (phaseBasis k t))
        (presentedPrincipalComponent k (@bernsteinWeight n) N d) := by
    rw [phiG_principal k g hd, eval_symbolLinearAlgHom_axis, mulVec_phaseBasis]
  refine ⟨hpiece, heval, fun hne => bernsteinDegree_eq_of_principal_ne_zero k hpiece ?_⟩
  intro hzero
  rw [hzero, map_zero] at heval
  exact hne heval.symm

/-- **Proposition 3.2, paragraph 4.** With `c := s(v) ≠ 0`, a central unit,
`d̃ := c⁻¹ Φ_g(d)` satisfies `deg_B d̃ = N` and `σ_N^B(d̃)(e_p) = 1`. -/
theorem step_3_2_normalize {n N : ℕ} {e : PresentedWeyl k n} (he : e ∈ bernsteinPiece k n N)
    (hdeg : bernsteinDegree k e = N) (t : PhaseVar n) {c : k} (hc : c ≠ 0)
    (hval : MvPolynomial.eval (axisPoint k t)
      (presentedPrincipalComponent k (@bernsteinWeight n) N e) = c) :
    c⁻¹ • e ∈ bernsteinPiece k n N ∧ bernsteinDegree k (c⁻¹ • e) = N ∧
      MvPolynomial.eval (axisPoint k t)
        (presentedPrincipalComponent k (@bernsteinWeight n) N (c⁻¹ • e)) = 1 := by
  have hpiece := (bernsteinPiece k n N).smul_mem c⁻¹ he
  have heval : MvPolynomial.eval (axisPoint k t)
      (presentedPrincipalComponent k (@bernsteinWeight n) N (c⁻¹ • e)) = 1 := by
    rw [map_smul, MvPolynomial.smul_eval, hval, inv_mul_cancel₀ hc]
  refine ⟨hpiece, ?_, heval⟩
  · subst hdeg
    refine bernsteinDegree_eq_of_principal_ne_zero k hpiece ?_
    intro hzero
    rw [hzero, map_zero] at heval
    exact zero_ne_one heval

/-- At `e_p`, a degree-`L` Bernstein symbol takes the value of the PBW
coefficient of `∂₁^L`: every other monomial of the homogeneous symbol contains
another coordinate and vanishes at `e_p`. -/
theorem eval_ep_principal {n L : ℕ} (a : PresentedWeyl k (n + 1)) :
    MvPolynomial.eval (axisPoint k (.inr (0 : Fin (n + 1))))
        (presentedPrincipalComponent k (@bernsteinWeight (n + 1)) L a) =
      MvPolynomial.coeff (Finsupp.single (.inr (0 : Fin (n + 1))) L)
        (presentedNormalFormLinearEquiv k (n + 1) a) := by
  rw [eval_axis_eq_pureCoefficient k _ (principal_isHomogeneous k a), coeff_axisPolynomial,
    coeff_principal_p_pow k _ rfl]

/-- **Proposition 3.2, paragraph 5 (decomposition).** Using the normal form
`A_n(k) = ⊕_j p^j C` (Convention 2.2), `d̃ = ∑_{j=0}^N p^j a_j` with
`a_j ∈ C`; the Bernstein filtration is compatible with this decomposition, so
`deg_B a_j ≤ N - j`, in particular `a_N ∈ C ∩ B_0 = k`. -/
theorem step_3_2_decomposition {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (hdt : dt ∈ bernsteinPiece k (n + 1) N) :
    ∃ a : ℕ → PresentedWeyl k (n + 1),
      (∀ j, a j ∈ C k n ∧ bernsteinDegree k (a j) ≤ N - j) ∧
      dt = ∑ j ∈ Finset.range (N + 1), p k n ^ j * a j ∧
      ∃ c : k, a N = algebraMap k _ c := by
  obtain ⟨a, ha, hdec⟩ := exists_bounded_decomposition k n N hdt
  refine ⟨a, ha, hdec, eq_algebraMap_of_mem_bernsteinPiece_zero k ?_⟩
  rw [← bernsteinDegree_le_iff]
  simpa using (ha N).2

/-- **Proposition 3.2, paragraph 5 (leading coefficient).** The symbol is
`σ_N^B(d̃) = ∑_{j + deg_B a_j = N} σ(p)^j σ(a_j)`.  For `j < N` the factor
`σ_{N-j}^B(a_j)` has positive degree and contains no `ξ₁` (`a_j ∈ C`), so it
vanishes at `e_p`; evaluating at `e_p` gives `a_N = σ_N^B(d̃)(e_p) = 1`. -/
theorem step_3_2_leading {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (a : ℕ → PresentedWeyl k (n + 1)) (ha : ∀ j, a j ∈ C k n ∧ bernsteinDegree k (a j) ≤ N - j)
    (hdec : dt = ∑ j ∈ Finset.range (N + 1), p k n ^ j * a j) (c : k)
    (hc : a N = algebraMap k _ c)
    (hval : MvPolynomial.eval (axisPoint k (.inr (0 : Fin (n + 1))))
      (presentedPrincipalComponent k (@bernsteinWeight (n + 1)) N dt) = 1) :
    a N = 1 := by
  have hsum : MvPolynomial.eval (axisPoint k (.inr (0 : Fin (n + 1))))
      (presentedPrincipalComponent k (@bernsteinWeight (n + 1)) N dt) =
      ∑ j ∈ Finset.range (N + 1), MvPolynomial.coeff
        (Finsupp.single (.inr (0 : Fin (n + 1))) (N - j))
        (presentedNormalFormLinearEquiv k (n + 1) (a j)) := by
    rw [hdec, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [(principal_bernstein_p_pow_mul k hjN ((bernsteinDegree_le_iff k (a j)).mp (ha j).2)).2,
      map_mul, map_pow, MvPolynomial.eval_X, eval_ep_principal]
    simp [axisPoint]
  rw [hsum, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self,
    Finsupp.single_zero, hc, Algebra.algebraMap_eq_smul_one, map_smul,
    presentedNormalFormLinearEquiv_one] at hval
  · have hc1 : c = 1 := by simpa using hval
    rw [hc, hc1, map_one]
  · intro j hj
    have hjN := Finset.mem_range.mp hj
    by_contra hne
    have := normalForm_C_no_p k (ha j).1 _ hne
    simp at this
    omega

/-- **Proposition 3.2, paragraph 5.** Hence
`d̃ = p^N + ∑_{j<N} p^j a_j` with `a_j ∈ C` and `deg_B a_j ≤ N - j`. -/
theorem step_3_2_monic {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (hdt : dt ∈ bernsteinPiece k (n + 1) N)
    (hval : MvPolynomial.eval (axisPoint k (.inr (0 : Fin (n + 1))))
      (presentedPrincipalComponent k (@bernsteinWeight (n + 1)) N dt) = 1) :
    IsMonicNormalForm k N dt := by
  obtain ⟨a, ha, hdec, c, hc⟩ := step_3_2_decomposition k hdt
  have hN := step_3_2_leading k a ha hdec c hc hval
  refine ⟨a, fun j _ => ha j, ?_⟩
  rw [hdec, Finset.sum_range_succ, hN, mul_one]
  exact add_comm _ _

/-- **Proposition 3.2.** Let `0 ≠ d ∈ A_n(k)` with `N := deg_B d ≥ 1`.  There
are an automorphism `Φ_g` of `A_n(k)` and `c ∈ k^×` with
`d̃ := c⁻¹ Φ_g(d) = p^N + ∑_{j<N} p^j a_j`, `a_j ∈ C`, `deg_B a_j ≤ N - j`
(eq. (3.1)), and `deg_B d̃ = N`. -/
theorem proposition_3_2 [CharZero k] {n : ℕ} {d : PresentedWeyl k (n + 1)} (hd : d ≠ 0)
    (hN : 1 ≤ bernsteinDegree k d) :
    ∃ (g : Matrix.symplecticGroup (Fin (n + 1)) k) (c : k), c ≠ 0 ∧
      IsMonicNormalForm k (bernsteinDegree k d) (c⁻¹ • phiG k g d) ∧
      bernsteinDegree k (c⁻¹ • phiG k g d) = bernsteinDegree k d := by
  obtain ⟨hpiece, hne, hhom, -, -⟩ := bernsteinSymbol_ne_zero k hd
  obtain ⟨v, hv, hv0⟩ := step_3_2_nonvanishing k hhom hne hN
  obtain ⟨h, hpres, hhe⟩ := step_3_2_h k hv0 (.inr (0 : Fin (n + 1)))
  obtain ⟨g, -, hmul⟩ := step_3_2_transpose k h hpres
  obtain ⟨hpiece', heval, hdeg'⟩ := step_3_2_symbol k g hpiece (.inr (0 : Fin (n + 1)))
  rw [hmul, hhe] at heval hdeg'
  obtain ⟨hpiece'', hdeg'', hval⟩ := step_3_2_normalize k hpiece' (hdeg' hv) _ hv heval
  exact ⟨g, _, hv, step_3_2_monic k hpiece'' hval, hdeg''⟩

#print axioms step_scalar_case
#print axioms proposition_3_2

end

end Stafford38.Paper.Section3
