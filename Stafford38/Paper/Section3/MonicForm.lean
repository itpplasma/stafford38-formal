module

public import Stafford38.Paper.Section3.PhiG
public import Stafford38.Paper.Section3.RightDecomposition
public import Stafford38.Weyl.MonicNormalization

@[expose] public section

/-!
# The monic normal form (3.1) and symbols of `p^j a` with `a ∈ C`

With the notation of Convention 2.2 (`x₁`, `p`, `C`; `Stafford38.Paper.Section2`)
and the Bernstein degree of Definition 2.3 (`Section2.bernsteinDegree`),
`IsMonicNormalForm N d̃` is the displayed form (3.1):
`d̃ = p^N + ∑_{j<N} p^j a_j` with `a_j ∈ C` and `deg_B a_j ≤ N - j`.

The lemmas below compute the symbols of the terms `p^j a_j` for both
filtrations; they are the PBW-monomial bookkeeping of the proofs of
Proposition 3.2 (paragraph 5) and Lemma 3.5 (second paragraph).
-/

namespace Stafford38.Paper.Section3

open Stafford38.Characteristic
open Stafford38.OreCoordinateStage
open Stafford38.OreIteratedPairStage
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylOuterOreMonic
open Stafford38.WeylPaperRightMonic
open Stafford38.WeylPBW
open Stafford38.WeylPBWMonicBridge
open Stafford38.Paper.Section2

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- **Equation (3.1).** `d̃ = p^N + ∑_{j<N} p^j a_j` with `a_j ∈ C` and
`deg_B a_j ≤ N - j`. -/
def IsMonicNormalForm {n : ℕ} (N : ℕ) (dt : PresentedWeyl k (n + 1)) : Prop :=
  ∃ a : ℕ → PresentedWeyl k (n + 1),
    (∀ j < N, a j ∈ C k n ∧ bernsteinDegree k (a j) ≤ N - j) ∧
      dt = p k n ^ N + ∑ j ∈ Finset.range N, p k n ^ j * a j

/-- A PBW monomial of an element of `C` contains no `∂₁`: `C = A_{n-1}(k)[x₁]`. -/
theorem normalForm_C_no_p {n : ℕ} {a : PresentedWeyl k (n + 1)} (ha : a ∈ C k n)
    (m : PhaseVar (n + 1) →₀ ℕ)
    (hm : MvPolynomial.coeff m (presentedNormalFormLinearEquiv k (n + 1) a) ≠ 0) :
    m (.inr 0) = 0 := by
  rw [C_eq_range] at ha
  obtain ⟨z, rfl⟩ := ha
  by_contra hL
  apply hm
  let aq : Fin (n + 1) → ℕ := fun i => m (.inl i)
  let pq : Fin (n + 1) → ℕ := fun i => m (.inr i)
  have hsplit : m = pairExponent n (aq 0) (pq 0)
      (phaseExponent (fun i => aq i.succ) (fun i => pq i.succ)) := by
    have hphase : phaseExponent aq pq = m := by
      ext i
      cases i <;> simp [phaseExponent, aq, pq]
    rw [← hphase, phaseExponent_succ]
    rfl
  change AddMonoidAlgebra.coeff (presentedNormalFormLinearEquiv k (n + 1)
    (coordinateStageToPresented k n z)) m = 0
  rw [coordinateStageToPresented_normalForm, hsplit, coeff_flattenPairSymbols,
    Polynomial.coeff_C, ite_eq_right (show pq 0 ≠ 0 from hL)]
  simp

/-- The normal form of `p^j` is `ξ₁^j`. -/
theorem normalForm_p_pow (n j : ℕ) :
    presentedNormalFormLinearEquiv k (n + 1) (p k n ^ j) =
      MvPolynomial.X (.inr (0 : Fin (n + 1))) ^ j := by
  have h := presentedNormalFormLinearEquiv_previous_ordered k n 0 j 1
  have hz : presentedCoefficientOrdered k n 0 j 1 = p k n ^ j := by
    simp [presentedCoefficientOrdered]
  rw [hz] at h
  rw [h, presentedNormalFormLinearEquiv_one]
  simp

private theorem weight_single_p (w : PhaseVar (n + 1) → ℕ) (hw : w (.inr 0) = 1) (j : ℕ) :
    monomialWeight w (Finsupp.single (.inr (0 : Fin (n + 1))) j) = j := by
  simp [monomialWeight, hw]

/-- `p^j` lies in the `j`-th piece and has symbol `ξ₁^j`, for any weight giving
`∂₁` degree `1` (Bernstein and order). -/
theorem p_pow_piece_principal {n : ℕ} (w : PhaseVar (n + 1) → ℕ) (hw : w (.inr 0) = 1)
    (j : ℕ) :
    p k n ^ j ∈ presentedWeightPiece k w j ∧
      presentedPrincipalComponent k w j (p k n ^ j) =
        MvPolynomial.X (.inr (0 : Fin (n + 1))) ^ j := by
  constructor
  · rw [mem_presentedWeightPiece, normalForm_p_pow]
    intro m hm
    simp only [MvPolynomial.coeff] at hm
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial] at hm
    split_ifs at hm with hmj
    · subst m
      rw [weight_single_p w hw]
    · exact absurd rfl hm
  · rw [presentedPrincipalComponent, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      normalForm_p_pow, MvPolynomial.X_pow_eq_monomial,
      weightedHomogeneousComponent_monomial, weight_single_p w hw]
    simp

/-- The coefficient of `ξ₁^L` in a degree-`L` symbol is the PBW coefficient of
`∂₁^L` (for any weight giving `∂₁` degree `1`). -/
theorem coeff_principal_p_pow {n L : ℕ} (w : PhaseVar (n + 1) → ℕ) (hw : w (.inr 0) = 1)
    (a : PresentedWeyl k (n + 1)) :
    MvPolynomial.coeff (Finsupp.single (.inr (0 : Fin (n + 1))) L)
        (presentedPrincipalComponent k w L a) =
      MvPolynomial.coeff (Finsupp.single (.inr (0 : Fin (n + 1))) L)
        (presentedNormalFormLinearEquiv k (n + 1) a) := by
  change AddMonoidAlgebra.coeff (presentedPrincipalComponent k w L a) _ = _
  rw [coeff_presentedPrincipalComponent, ite_eq_left (weight_single_p w hw L)]

/-- The coefficient of `ξ₁^N` in `ξ₁^j f` is the coefficient of `ξ₁^{N-j}` in
`f`, for `j ≤ N`. -/
theorem coeff_X_pow_mul_single {n j N : ℕ} (hj : j ≤ N) (f : SymbolRing k (n + 1)) :
    MvPolynomial.coeff (Finsupp.single (.inr (0 : Fin (n + 1))) N)
        (MvPolynomial.X (.inr 0) ^ j * f) =
      MvPolynomial.coeff (Finsupp.single (.inr (0 : Fin (n + 1))) (N - j)) f := by
  simp only [MvPolynomial.coeff]
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul',
    ite_eq_left (Finsupp.single_le_single.mpr hj), one_mul, ← Finsupp.single_tsub]

/-- **Bernstein symbol of `p^j a`.** For `a ∈ B_{N-j}`,
`σ_N^B(p^j a) = ξ₁^j σ_{N-j}^B(a)`. -/
theorem principal_bernstein_p_pow_mul {n j N : ℕ} (hj : j ≤ N) {a : PresentedWeyl k (n + 1)}
    (ha : a ∈ bernsteinPiece k (n + 1) (N - j)) :
    p k n ^ j * a ∈ bernsteinPiece k (n + 1) N ∧
      presentedPrincipalComponent k (@bernsteinWeight (n + 1)) N (p k n ^ j * a) =
        MvPolynomial.X (.inr 0) ^ j *
          presentedPrincipalComponent k (@bernsteinWeight (n + 1)) (N - j) a := by
  obtain ⟨hp, hσ⟩ := p_pow_piece_principal k (@bernsteinWeight (n + 1)) rfl j
  have hmem := mul_mem_bernsteinPiece k hp ha
  have hmul := presentedPrincipalComponent_mul_bernstein k hp ha
  rw [Nat.add_sub_cancel' hj] at hmem hmul
  rw [hmul, hσ]
  exact ⟨hmem, rfl⟩

/-- **Order symbol of `p^j a`.** For `a ∈ F_{N-j}`,
`σ_N^ord(p^j a) = ξ₁^j σ_{N-j}^ord(a)`. -/
theorem principal_order_p_pow_mul {n j N : ℕ} (hj : j ≤ N) {a : PresentedWeyl k (n + 1)}
    (ha : a ∈ orderPiece k (n + 1) (N - j)) :
    presentedPrincipalComponent k (@orderWeight (n + 1)) N (p k n ^ j * a) =
      MvPolynomial.X (.inr 0) ^ j *
        presentedPrincipalComponent k (@orderWeight (n + 1)) (N - j) a := by
  obtain ⟨hp, hσ⟩ := p_pow_piece_principal k (@orderWeight (n + 1)) rfl j
  have hmul := presentedPrincipalComponent_mul_order k hp ha
  rw [Nat.add_sub_cancel' hj] at hmul
  rw [hmul, hσ]

/-- An element of the form (3.1) is PBW-monic: it lies in `B_N` and the PBW
coefficient of `∂₁^N` is `1`.  This connects (3.1) to the repository's
`WeylPBWMonicBridge.IsPBWMonicAt`, the hypothesis of
`UniversalAssembly.CanonicalSupportVanishing`. -/
theorem isPBWMonicAt_of_isMonicNormalForm {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (h : IsMonicNormalForm k N dt) :
    IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N dt := by
  obtain ⟨a, ha, rfl⟩ := h
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :=
    principal_bernstein_p_pow_mul k (Finset.mem_range.mp hj).le
      ((bernsteinDegree_le_iff k (a j)).mp (ha j (Finset.mem_range.mp hj)).2)
  obtain ⟨hpN, hσN⟩ := p_pow_piece_principal k (@bernsteinWeight (n + 1)) rfl N
  refine ⟨add_mem hpN (Submodule.sum_mem _ fun j hj => (hterm j hj).1), ?_⟩
  rw [← coeff_principal_p_pow k (@bernsteinWeight (n + 1)) rfl, map_add, map_sum, hσN]
  simp only [MvPolynomial.coeff]
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_sum,
    Finset.sum_eq_zero, add_zero, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial,
    ite_eq_left rfl]
  intro j hj
  have hjN := Finset.mem_range.mp hj
  rw [(hterm j hj).2]
  have h := coeff_X_pow_mul_single k hjN.le
    (presentedPrincipalComponent k (@bernsteinWeight (n + 1)) (N - j) (a j))
  simp only [MvPolynomial.coeff] at h
  rw [h]
  have h2 := coeff_principal_p_pow k (L := N - j) (@bernsteinWeight (n + 1)) rfl (a j)
  simp only [MvPolynomial.coeff] at h2
  rw [h2]
  by_contra hne
  have := normalForm_C_no_p k (ha j hjN).1 _ hne
  simp at this
  omega

end

end Stafford38.Paper.Section3
