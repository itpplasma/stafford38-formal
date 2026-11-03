module

public import Stafford38.Paper.Section5.ResidueBasis
public import Stafford38.Paper.Section5.Place
public import Stafford38.Paper.Section5.TangentCone
public import Stafford38.Paper.Section5.GenericTangentRank
public import Stafford38.Paper.Section5.Completion
public import Stafford38.Geometry.ActualWitnessConormalAssembly
public import Stafford38.Geometry.ConormalScalarExtensionVanishing
public import Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
public import Stafford38.Geometry.FormalDivisorAxisLift
public import Stafford38.Geometry.PaperLaurentChartDerivation
public import Stafford38.Geometry.PaperResidueDerivationFrame
public import Stafford38.Geometry.PaperSameWitnessComponentFieldRank
public import Stafford38.Geometry.PaperRetainedChartAssembly
public import Stafford38.Geometry.ProjectiveConormalDirections
public import Stafford38.Geometry.SmoothConormalFibreVanishing

@[expose] public section

/-!
# The paragraphs of the proof of Theorem 5.7(i)

Section 5.2 proves Theorem 5.7(i) by a chain of paragraphs between
Lemmas 5.9–5.13.  Each declaration below states the claim of one paragraph and
proves it.  `Stafford38.Paper.Section5.Proof` chains them.

Notation.  `q : Fin (m+1) → κ[[t]]` is the column `q_i = x̄_i / x̄_j` in the
completed discrete valuation ring `V̂ ≅ κ[[t]]`, index `0` is the homogenizing
coordinate, the paper's index `1` is `Fin.succ ⟨0, hm⟩`, and `j` is the chart
with `q_j = 1`.  `laurentColumn` embeds `κ[[t]]` into `κ((t))`, and
`dehomogenizedPoint` is `y = (q_1/q_0, …, q_n/q_0)`.  The matrix
`M = (q, Z_{•1}, …, Z_{•d'}, τ)` is `formalTangentMatrix q Z τ`, whose column
index `Unit ⊕ (Fin d' ⊕ Unit)` lists `q`, then the `Z`-columns, then `τ`.
The row vector `u = (0, 1, 0, …, 0)` is `axisRow (Fin.succ ⟨0, hm⟩)`.
-/

namespace Stafford38.Paper.Section5

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.ActualWitnessConormalAssembly
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ConormalScalarExtensionVanishing
open Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
open Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.KaehlerVisibleDerivationFrame
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.PaperActualDivisorTangent
open Stafford38.Geometry.PaperLaurentChartDerivation
open Stafford38.Geometry.PaperResidueDerivationFrame
open Stafford38.Geometry.PaperRetainedChartAssembly
open Stafford38.Geometry.PaperSameWitnessComponentFieldRank
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.SmoothConormalFibreVanishing
open Stafford38.GeometryFormalDivisorAxisLift
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryPowerSeriesTangentLimit
open Stafford38.GeometryResidueMinorSelection
open Stafford38.GeometryRetractionSpecialization
open Stafford38.GeometrySplitTangentMatrix

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000

universe u

/-! ## The case `x̄_1` algebraic -/

section AlgebraicCoordinate

open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.ConormalPrincipalOpenDensity
open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.CoisotropicTranslation

/-- `Y = V(𝔭)` is nonempty for a prime `𝔭` (Nullstellensatz). -/
theorem exists_mem_zeroLocus_of_isPrime {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
    (I : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    ∃ y : Fin n → k, y ∈ MvPolynomial.zeroLocus k I.asIdeal := by
  obtain ⟨M, hMmax, hPM⟩ := Ideal.exists_le_maximal I.asIdeal I.isPrime.ne_top
  obtain ⟨y, hMy⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hMmax
  refine ⟨y, fun f hf ↦ ?_⟩
  have hfM : f ∈ M := hPM hf
  rw [hMy, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hfM
  exact hfM

/-- The smooth locus `Y_sm` of a nonempty `Y = V(𝔭)` is nonempty (it is dense in `Y`,
Definition 5.4(b)). -/
theorem exists_smoothAffinePoint {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
    (I : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    ∃ y : Fin n → k, SmoothAffinePoint I.asIdeal y := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨y, hy⟩ := exists_mem_zeroLocus_of_isPrime I
  have hmem : (Sum.elim y 0 : Fin n ⊕ Fin n → k) ∈ equationConormalClosure I.asIdeal := by
    intro f hf
    refine hf _ ⟨fun g hg ↦ by simpa using hy g hg, ?_⟩
    have h0 : coordinateCovector
        (fun i : Fin n ↦ (Sum.elim y 0 : Fin n ⊕ Fin n → k) (.inr i)) = 0 := by
      apply LinearMap.ext
      intro v
      simp [coordinateCovector_apply]
    rw [h0]
    exact Submodule.zero_mem _
  rw [← equationConormalClosure_smoothAffine_eq I.asIdeal I.isPrime] at hmem
  have hempty :
      restrictedEquationConormalLocus I.asIdeal {y | SmoothAffinePoint I.asIdeal y} = ∅ := by
    ext q
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hq ↦ hnone _ hq.2
  have h1 : (1 : MvPolynomial (Fin n ⊕ Fin n) k) ∈ MvPolynomial.vanishingIdeal k
      (restrictedEquationConormalLocus I.asIdeal {y | SmoothAffinePoint I.asIdeal y}) := by
    rw [hempty, MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    exact absurd hx (Set.notMem_empty x)
  simpa using hmem 1 h1

/-- **First paragraph of the proof of Theorem 5.7 (`x̄_1` algebraic).**  A nonzero
`g` with `g(x̄_1) = 0` gives `g(x_1) ∈ 𝔭`; over the algebraically closed `K`,
`g(x_1) = λ ∏ (x_1 − c_i)` with `λ ∈ K^×`, and since `𝔭` is prime some factor
`x_1 − c` lies in `𝔭`.  Thus `x_1 = c` on `Y`, and `Y ≠ ∅`, `Y ∩ H = ∅` give
`c ≠ 0`.  The equation `f = x_1 − c` has `df_y = dx_1` at every smooth point `y`,
and `Y_sm ≠ ∅`, so `(1, 0, …, 0) ∈ N(Y)`. -/
theorem step_coordinate_algebraic {k : Type u} [Field k] [IsAlgClosed k] {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0)
    (halg : IsAlgebraic k (componentCoordinate I ⟨0, hm⟩)) :
    ∃ c : k, MvPolynomial.X ⟨0, hm⟩ - MvPolynomial.C c ∈ I.asIdeal ∧ c ≠ 0 ∧
      (fun i : Fin m ↦ if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
        smoothConormalFibreProjection I.asIdeal := by
  classical
  let i₀ : Fin m := ⟨0, hm⟩
  let x₁ : MvPolynomial (Fin m) k := MvPolynomial.X i₀
  -- A nonzero `g` with `g(x̄_1) = 0`, hence `g(x_1) ∈ 𝔭`.
  obtain ⟨g, hg0, hgx⟩ := halg
  have hgmem : Polynomial.aeval x₁ g ∈ I.asIdeal := by
    have hcomp : componentCoordinate I i₀ =
        ((IsScalarTower.toAlgHom k (MvPolynomial (Fin m) k ⧸ I.asIdeal)
          (FractionRing (MvPolynomial (Fin m) k ⧸ I.asIdeal))).comp
          (Ideal.Quotient.mkₐ k I.asIdeal)) x₁ := rfl
    rw [hcomp, Polynomial.aeval_algHom_apply] at hgx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective (MvPolynomial (Fin m) k ⧸ I.asIdeal)
      (FractionRing (MvPolynomial (Fin m) k ⧸ I.asIdeal))
    rw [map_zero, ← hgx]
    rfl
  -- `K` algebraically closed: `g(x_1) = λ ∏ (x_1 − c_i)`, `λ ∈ K^×`.
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := g))
  have hlc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
  rw [← hfac, map_mul, Polynomial.aeval_C, map_multiset_prod, Multiset.map_map] at hgmem
  -- `𝔭` is prime, so some factor `x_1 − c` lies in `𝔭`.
  rcases I.isPrime.mem_or_mem hgmem with hC | hprod
  · exact absurd (I.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by
      have := Ideal.mul_mem_left _ (MvPolynomial.C g.leadingCoeff⁻¹) hC
      simpa [MvPolynomial.algebraMap_eq, ← MvPolynomial.C_mul, inv_mul_cancel₀ hlc] using this)))
      (by simp)
  obtain ⟨_, hmem, hc⟩ := (I.isPrime.multiset_prod_mem_iff_exists_mem _).mp hprod
  obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp hmem
  have hc' : x₁ - MvPolynomial.C c ∈ I.asIdeal := by
    simpa [x₁, Polynomial.aeval_X, MvPolynomial.algebraMap_eq] using hc
  -- `x_1 = c` on `Y`; `Y ≠ ∅` and `Y ∩ H = ∅` give `c ≠ 0`.
  obtain ⟨y, hy⟩ := exists_mem_zeroLocus_of_isPrime I
  have hyc : y i₀ = c := by
    have := hy _ hc'
    simpa [x₁, sub_eq_zero] using this
  have hc0 : c ≠ 0 := hyc ▸ havoid y hy
  -- `f = x_1 − c ∈ 𝔭` has `df_y = dx_1` at a smooth point `y`, so `dx_1 ∈ N*_y Y ⊆ N(Y)`.
  obtain ⟨y', hy'⟩ := exists_smoothAffinePoint I
  refine ⟨c, hc', hc0, (definition_5_4_d I.asIdeal _).2 ⟨y', hy', ?_⟩⟩
  have hdf : differentialAt y' (x₁ - MvPolynomial.C c) =
      fun i : Fin m ↦ if i = i₀ then (1 : k) else 0 := by
    funext i
    by_cases hi : i = i₀
    · subst hi; simp [differentialAt, x₁]
    · simp [differentialAt, x₁, hi, MvPolynomial.pderiv_X, Ne.symm hi]
  rw [← hdf]
  exact Submodule.subset_span ⟨⟨_, hc'⟩, rfl⟩

end AlgebraicCoordinate

/-! ## Paragraphs over `κ[[t]]` -/

section PowerSeriesSteps

variable {k κ : Type u} [Field k] [Field κ] [Algebra k κ] [CharZero k] [CharZero κ]

/-- **Paragraph after Lemma 5.11 (dual derivations and `Z`).**  If the
differentials `d(q_{i_l}(0))` form a basis of `Ω_{κ/K}`, there are dual
`K`-derivations `D_k` with `D_k(q_{i_l}(0)) = δ_{kl}` (Definition 5.2(c)).  The
matrix `Z_{ik} = Σ_r D_k(c_{ir}) t^r` then has `Z(0)` equal to the identity on
the rows `i_l`, so its selected minor has constant coefficient `1`; `Z_j = 0`;
and rows `0` and `1` are divisible by `t^a` and `t^b`. -/
theorem step_dual_derivations {m d : ℕ} (hm : 0 < m)
    (q : Fin (m + 1) → PowerSeries κ) (rows : Fin d ↪ Fin (m + 1))
    (hli : LinearIndependent κ
      (fun l ↦ KaehlerDifferential.D k κ (PowerSeries.constantCoeff (q (rows l)))))
    (hspan : Submodule.span κ (Set.range fun l ↦
      KaehlerDifferential.D k κ (PowerSeries.constantCoeff (q (rows l)))) = ⊤)
    (j : Fin (m + 1)) (hqj : q j = 1) (a b : ℕ) (u₀ u₁ : PowerSeries κ)
    (hq0 : q 0 = (PowerSeries.X : PowerSeries κ) ^ a * u₀)
    (hq1 : q (Fin.succ ⟨0, hm⟩) = (PowerSeries.X : PowerSeries κ) ^ b * u₁) :
    ∃ D : Fin d → Derivation k κ κ,
      (∀ k' l, D k' (PowerSeries.constantCoeff (q (rows l))) = if k' = l then 1 else 0) ∧
      (∀ l k', PowerSeries.constantCoeff (coefficientwiseTangentMatrix q D (rows l) k') =
        if l = k' then 1 else 0) ∧
      PowerSeries.constantCoeff
        (selectedMinor (coefficientwiseTangentMatrix q D) rows).det = 1 ∧
      (∀ k', coefficientwiseTangentMatrix q D j k' = 0) ∧
      (∀ k', ∃ w : PowerSeries κ,
        coefficientwiseTangentMatrix q D 0 k' = (PowerSeries.X : PowerSeries κ) ^ a * w) ∧
      (∀ k', ∃ w : PowerSeries κ,
        coefficientwiseTangentMatrix q D (Fin.succ ⟨0, hm⟩) k' =
          (PowerSeries.X : PowerSeries κ) ^ b * w) := by
  classical
  let B : Module.Basis (Fin d) κ (Ω[κ⁄k]) := Module.Basis.mk hli hspan.ge
  -- Definition 5.2(c): the dual derivations `D_k` of the basis `dβ_l`.
  obtain ⟨D, hdual⟩ := definition_5_2_c (K := k) (L := κ)
    (fun l ↦ PowerSeries.constantCoeff (q (rows l))) B (fun l ↦ Module.Basis.mk_apply _ _ _)
  have hentry : ∀ l k', PowerSeries.constantCoeff (coefficientwiseTangentMatrix q D (rows l) k') =
      if l = k' then 1 else 0 := by
    intro l k'
    rw [constantCoeff_coefficientwiseTangentMatrix, hdual]
    by_cases h : k' = l
    · subst h; simp
    · simp [h, Ne.symm h]
  refine ⟨D, hdual, hentry, ?_, ?_, ?_, ?_⟩
  · rw [constantCoeff_selectedMinor_det]
    have hone : selectedMinor (residueMatrix (coefficientwiseTangentMatrix q D)) rows = 1 := by
      ext l k'
      rw [Matrix.one_apply]
      exact hentry l k'
    rw [hone, Matrix.det_one]
  · intro k'
    rw [coefficientwiseTangentMatrix]
    simp only [hqj]
    exact (coefficientwiseDerivation (D k')).map_one_eq_zero
  · intro k'
    refine ⟨coefficientwiseDerivation (D k') u₀, ?_⟩
    rw [coefficientwiseTangentMatrix, hq0]
    exact coefficientwiseDerivation_X_pow_mul (D k') a u₀
  · intro k'
    refine ⟨coefficientwiseDerivation (D k') u₁, ?_⟩
    rw [coefficientwiseTangentMatrix, hq1]
    exact coefficientwiseDerivation_X_pow_mul (D k') b u₁

omit [CharZero κ] in
/-- A series `t^n r` with `r(0) ≠ 0` has order exactly `n`. -/
theorem order_X_pow_mul_of_constantCoeff_ne_zero (n : ℕ) (r : PowerSeries κ)
    (hr : PowerSeries.constantCoeff r ≠ 0) :
    ((PowerSeries.X : PowerSeries κ) ^ n * r).order = n := by
  rw [PowerSeries.order_mul, PowerSeries.order_X_pow,
    PowerSeries.order_zero_of_isUnit (PowerSeries.isUnit_iff_constantCoeff.mpr (IsUnit.mk0 _ hr)),
    add_zero]

omit [CharZero κ] in
/-- If `q_i = t^n u` and every entry of row `i` of `Z` is divisible by `t^n`
(`n ≥ 1`), then `q'_i − (Zλ)_i = t^{n-1} r` with `r(0) = n u(0)`. -/
theorem derivative_sub_mulVec_eq_X_pow_mul {ι' : Type*} {d : ℕ} (q : ι' → PowerSeries κ)
    (Z : Matrix ι' (Fin d) (PowerSeries κ)) (lambda : Fin d → PowerSeries κ) (i : ι') (n : ℕ)
    (hn : 0 < n) (u : PowerSeries κ) (hq : q i = (PowerSeries.X : PowerSeries κ) ^ n * u)
    (hZ : ∀ k', ∃ w : PowerSeries κ, Z i k' = (PowerSeries.X : PowerSeries κ) ^ n * w) :
    ∃ r : PowerSeries κ,
      PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i =
        (PowerSeries.X : PowerSeries κ) ^ (n - 1) * r ∧
      PowerSeries.constantCoeff r = n * PowerSeries.constantCoeff u := by
  choose w hw using hZ
  let S := ∑ k', w k' * lambda k'
  have hXn : (PowerSeries.X : PowerSeries κ) ^ n = PowerSeries.X ^ (n - 1) * PowerSeries.X := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  refine ⟨(n : PowerSeries κ) * u + PowerSeries.X * (PowerSeries.derivative (R := κ) u - S), ?_, ?_⟩
  · have hmv : Z.mulVec lambda i = PowerSeries.X ^ n * S := by
      simp only [Matrix.mulVec, dotProduct, hw, S, Finset.mul_sum, mul_assoc]
    rw [hq, hmv, Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_X, hXn]
    simp only [smul_eq_mul]
    ring
  · simp [S]

/-- **Paragraph defining `λ`, `w` and `τ`.**  `Z̃(0)` is the identity, so `Z̃`
is invertible over `κ[[t]]` and there is a unique `λ` with
`Z̃ λ = (q'_{i_1}, …, q'_{i_{d'}})`.  For `w = q' − Zλ`: `w_{i_l} = 0`;
`ord w_0 = a − 1` exactly; `c`, the minimal order of the entries of `w`,
satisfies `c ≤ a − 1`; `τ = t^{-c} w` lies in `κ[[t]]^{n+1}` (stated as
`w = t^c τ`) with `τ(0) ≠ 0`, `τ_{i_l} = 0`, `ord τ_1 ≥ b − a > 0` (so
`τ_1(0) = 0`) and `τ_j = 0`. -/
theorem step_lambda_w_tau {m d : ℕ} (hm : 0 < m)
    (q : Fin (m + 1) → PowerSeries κ) (Z : Matrix (Fin (m + 1)) (Fin d) (PowerSeries κ))
    (rows : Fin d ↪ Fin (m + 1)) (j : Fin (m + 1)) (a b : ℕ) (u₀ u₁ : PowerSeries κ)
    (hqj : q j = 1) (hZj : ∀ k', Z j k' = 0) (ha : 0 < a) (hab : a < b)
    (hq0 : q 0 = (PowerSeries.X : PowerSeries κ) ^ a * u₀)
    (hu₀ : PowerSeries.constantCoeff u₀ ≠ 0)
    (hZ0 : ∀ k', ∃ w : PowerSeries κ, Z 0 k' = (PowerSeries.X : PowerSeries κ) ^ a * w)
    (hq1 : q (Fin.succ ⟨0, hm⟩) = (PowerSeries.X : PowerSeries κ) ^ b * u₁)
    (hZ1 : ∀ k', ∃ w : PowerSeries κ,
      Z (Fin.succ ⟨0, hm⟩) k' = (PowerSeries.X : PowerSeries κ) ^ b * w)
    (hminor : PowerSeries.constantCoeff (selectedMinor Z rows).det = 1) :
    ∃ (lambda : Fin d → PowerSeries κ) (c : ℕ) (tau : Fin (m + 1) → PowerSeries κ),
      (∀ l, PowerSeries.derivative (R := κ) (q (rows l)) = Z.mulVec lambda (rows l)) ∧
      (∀ lambda' : Fin d → PowerSeries κ,
        (∀ l, PowerSeries.derivative (R := κ) (q (rows l)) = Z.mulVec lambda' (rows l)) →
          lambda' = lambda) ∧
      (∀ l, PowerSeries.derivative (R := κ) (q (rows l)) - Z.mulVec lambda (rows l) = 0) ∧
      (PowerSeries.derivative (R := κ) (q 0) - Z.mulVec lambda 0).order = (a - 1 : ℕ) ∧
      (∀ i, (c : ℕ∞) ≤ (PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i).order) ∧
      (∃ i, (PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i).order = c) ∧
      c ≤ a - 1 ∧
      (∀ i, PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i =
        (PowerSeries.X : PowerSeries κ) ^ c * tau i) ∧
      (∃ i, PowerSeries.constantCoeff (tau i) ≠ 0) ∧
      (∀ l, tau (rows l) = 0) ∧
      (∃ s : PowerSeries κ,
        tau (Fin.succ ⟨0, hm⟩) = (PowerSeries.X : PowerSeries κ) ^ (b - a) * s) ∧
      PowerSeries.constantCoeff (tau (Fin.succ ⟨0, hm⟩)) = 0 ∧
      tau j = 0 := by
  classical
  have hminor0 : PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0 := by
    rw [hminor]; exact one_ne_zero
  -- `Z̃(0)` is the identity, so `Z̃` is invertible over `κ[[t]]` and
  -- `λ = Z̃⁻¹ (q'_{i_1}, …, q'_{i_{d'}})` solves `Z̃ λ = (q'_{i_l})`.
  let v : Fin (m + 1) → PowerSeries κ := fun i ↦ PowerSeries.derivative (R := κ) (q i)
  let lambda : Fin d → PowerSeries κ := correctionCoefficients Z rows v
  have hsel : ∀ l, PowerSeries.derivative (R := κ) (q (rows l)) = Z.mulVec lambda (rows l) :=
    fun l ↦ sub_eq_zero.mp (correctedVector_selectedRow_eq_zero Z rows v hminor0 l)
  -- The solution is unique.
  have huniq : ∀ lambda' : Fin d → PowerSeries κ,
      (∀ l, PowerSeries.derivative (R := κ) (q (rows l)) = Z.mulVec lambda' (rows l)) →
        lambda' = lambda := by
    intro lambda' h'
    have hunit : IsUnit (selectedMinor Z rows) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr
        (PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hminor]; exact isUnit_one))
    apply Matrix.mulVec_injective_of_isUnit hunit
    funext l
    change Z.mulVec lambda' (rows l) = Z.mulVec lambda (rows l)
    rw [← h', hsel]
  -- `w = q' − Zλ` has `w_{i_l} = 0`.
  let w : Fin (m + 1) → PowerSeries κ := fun i ↦
    PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i
  have hwrows : ∀ l, w (rows l) = 0 := fun l ↦ sub_eq_zero.mpr (hsel l)
  -- `ord w_0 = a − 1`: `q'_0` has order exactly `a − 1` (its coefficient `a u_0(0)` of
  -- `t^{a-1}` is nonzero in characteristic zero), while `Z_{0•} λ` has order `≥ a`.
  obtain ⟨r₀, hr₀, hr₀c⟩ := derivative_sub_mulVec_eq_X_pow_mul q Z lambda 0 a ha u₀ hq0 hZ0
  have hr₀ne : PowerSeries.constantCoeff r₀ ≠ 0 := by
    rw [hr₀c]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr ha.ne') hu₀
  have hw0 : (PowerSeries.derivative (R := κ) (q 0) - Z.mulVec lambda 0).order = (a - 1 : ℕ) := by
    rw [hr₀]
    exact order_X_pow_mul_of_constantCoeff_ne_zero _ _ hr₀ne
  -- `c` is the minimal order among the entries of `w`; then `c ≤ a − 1`, and
  -- `τ = t^{-c} w` lies in `κ[[t]]^{n+1}` with `τ(0) ≠ 0`.
  have hcoeff : PowerSeries.coeff (a - 1) (w 0) ≠ 0 := by
    change PowerSeries.coeff (a - 1)
      (PowerSeries.derivative (R := κ) (q 0) - Z.mulVec lambda 0) ≠ 0
    rw [hr₀]
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (show PowerSeries.coeff (0 + (a - 1)) ((PowerSeries.X : PowerSeries κ) ^ (a - 1) * r₀) ≠ 0 by
        rw [PowerSeries.coeff_X_pow_mul]
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hr₀ne)
  obtain ⟨c, hc, tau, hfactor, hprim⟩ :=
    exists_primitive_commonPower_of_coeff_ne_zero w 0 (a - 1) hcoeff
  have hfactor' : ∀ i, PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i =
      (PowerSeries.X : PowerSeries κ) ^ c * tau i := hfactor
  have htau_of_w : ∀ i, w i = 0 → tau i = 0 := fun i hi ↦
    (mul_eq_zero.mp ((hfactor i).symm.trans hi)).resolve_left
      (pow_ne_zero c PowerSeries.X_ne_zero)
  have htaurows : ∀ l, tau (rows l) = 0 := fun l ↦ htau_of_w _ (hwrows l)
  -- In row `1`, `q'_1` and `Z_{1•} λ` have order `≥ b − 1`, so `ord τ_1 ≥ b − 1 − c ≥ b − a`.
  obtain ⟨r₁, hr₁, -⟩ :=
    derivative_sub_mulVec_eq_X_pow_mul q Z lambda _ b (ha.trans hab) u₁ hq1 hZ1
  have htau1' : tau (Fin.succ ⟨0, hm⟩) =
      (PowerSeries.X : PowerSeries κ) ^ (b - a) *
        ((PowerSeries.X : PowerSeries κ) ^ (a - 1 - c) * r₁) := by
    apply mul_left_cancel₀ (pow_ne_zero c (PowerSeries.X_ne_zero (R := κ)))
    rw [← hfactor', hr₁, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  have htau1 : PowerSeries.constantCoeff (tau (Fin.succ ⟨0, hm⟩)) = 0 := by
    rw [htau1', map_mul, map_pow, PowerSeries.constantCoeff_X,
      zero_pow (Nat.sub_ne_zero_of_lt hab), zero_mul]
  -- `q'_j = 0` and `Z_{j•} = 0` (as `q_j = 1`), so `τ_j = 0`.
  have htauj : tau j = 0 := by
    apply htau_of_w
    change PowerSeries.derivative (R := κ) (q j) - Z.mulVec lambda j = 0
    rw [hqj, Derivation.map_one_eq_zero, zero_sub, neg_eq_zero]
    simp [Matrix.mulVec, dotProduct, hZj]
  refine ⟨lambda, c, tau, hsel, huniq, hwrows, hw0, ?_, ?_, hc,
    hfactor', hprim, htaurows, ⟨_, htau1'⟩, htau1, htauj⟩
  · intro i
    rw [hfactor' i, PowerSeries.order_mul, PowerSeries.order_X_pow]
    exact le_self_add
  · obtain ⟨i, hi⟩ := hprim
    exact ⟨i, by rw [hfactor' i]; exact order_X_pow_mul_of_constantCoeff_ne_zero c _ hi⟩

omit [CharZero κ] in
/-- If some square minor `M_ι` of `M` has `det M_ι(0) ≠ 0`, then `det M_ι` is a
unit of `κ[[t]]` and the columns of `M` are linearly independent over
`κ((t))`. -/
theorem linearIndependent_laurent_of_selectedMinor {R ι : Type*} [Fintype R] [Fintype ι]
    [DecidableEq ι] (M : Matrix R ι (PowerSeries κ)) (rowsι : ι ↪ R)
    (h0 : PowerSeries.constantCoeff (selectedMinor M rowsι).det ≠ 0) :
    IsUnit (selectedMinor M rowsι).det ∧
      LinearIndependent (LaurentSeries κ)
        (fun col i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ) (M i col)) := by
  classical
  have hunit : IsUnit (selectedMinor M rowsι).det :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (IsUnit.mk0 _ h0)
  refine ⟨hunit, ?_⟩
  let f := algebraMap (PowerSeries κ) (LaurentSeries κ)
  let A := (selectedMinor M rowsι).map f
  have hA : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det]
    change IsUnit (f.mapMatrix (selectedMinor M rowsι)).det
    rw [← RingHom.map_det]
    exact hunit.map f
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmv : A.mulVec g = 0 := by
    funext c
    have hi := congrFun hg (rowsι c)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    rw [Pi.zero_apply, ← hi]
    simp only [Matrix.mulVec, dotProduct, A, Matrix.map_apply, selectedMinor]
    exact Finset.sum_congr rfl fun col _ ↦ mul_comm _ _
  have := Matrix.mulVec_injective_of_isUnit hA (hmv.trans (Matrix.mulVec_zero A).symm)
  exact fun col ↦ congrFun this col

/-- **Paragraph "`M(0)` has full column rank".**  For
`M = (q, Z_{•1}, …, Z_{•d'}, τ)`: `M(0)` has full column rank (row `j`, the
identity block on the rows `i_l`, and `τ(0) ≠ 0`); so some
`(d'+2) × (d'+2)` minor `M_ι(0)` is nonzero, the corresponding minor of `M(t)`
is a unit of `κ[[t]]`, and the columns of `M(t)` are linearly independent over
`κ((t))`.  Every column of `M(0)` has vanishing `1`-coordinate. -/
theorem step_M_minor {m d : ℕ} (hm : 0 < m)
    (q : Fin (m + 1) → PowerSeries κ) (Z : Matrix (Fin (m + 1)) (Fin d) (PowerSeries κ))
    (tau : Fin (m + 1) → PowerSeries κ) (rows : Fin d ↪ Fin (m + 1)) (j : Fin (m + 1))
    (b : ℕ) (u₁ : PowerSeries κ)
    (hqj : q j = 1) (hZj : ∀ k', Z j k' = 0) (htauj : tau j = 0)
    (htaurows : ∀ l, tau (rows l) = 0)
    (hminor : PowerSeries.constantCoeff (selectedMinor Z rows).det = 1)
    (hprim : ∃ i, PowerSeries.constantCoeff (tau i) ≠ 0) (hb : 0 < b)
    (hq1 : q (Fin.succ ⟨0, hm⟩) = (PowerSeries.X : PowerSeries κ) ^ b * u₁)
    (hZ1 : ∀ k', ∃ w : PowerSeries κ,
      Z (Fin.succ ⟨0, hm⟩) k' = (PowerSeries.X : PowerSeries κ) ^ b * w)
    (htau1 : PowerSeries.constantCoeff (tau (Fin.succ ⟨0, hm⟩)) = 0) :
    Function.Injective (residueMatrix (formalTangentMatrix q Z tau)).mulVec ∧
      (∃ rowsι : FormalTangentColumn (Fin d) ↪ Fin (m + 1),
        PowerSeries.constantCoeff (selectedMinor (formalTangentMatrix q Z tau) rowsι).det ≠ 0 ∧
        IsUnit (selectedMinor (formalTangentMatrix q Z tau) rowsι).det) ∧
      LinearIndependent (LaurentSeries κ)
        (fun col i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ)
          (formalTangentMatrix q Z tau i col)) ∧
      ∀ col, PowerSeries.constantCoeff
        (formalTangentMatrix q Z tau (Fin.succ ⟨0, hm⟩) col) = 0 := by
  classical
  have hinj := residue_formalTangentMatrix_mulVec_injective q Z tau rows j hqj hZj htauj
    htaurows (by rw [hminor]; exact one_ne_zero) hprim
  obtain ⟨rowsι, hρ⟩ :=
    powerSeries_exists_selectedMinor_constantCoeff_ne_zero_of_residue_mulVec_injective _ hinj
  obtain ⟨hunit, hli⟩ := linearIndependent_laurent_of_selectedMinor _ rowsι hρ
  exact ⟨hinj, ⟨rowsι, hρ, hunit⟩, hli,
    constantCoeff_formalTangentMatrix_axis_eq_zero q Z tau _ b u₁ hb hq1 hZ1 htau1⟩

omit [CharZero k] [CharZero κ] in
/-- **Paragraph "the columns of `M` span `𝒞`".**  The columns `q`, `Z_{•k}`
and `q'` have the form `δq` for `K`-derivations `δ` of `κ((t))` (the `D_k`
extended coefficientwise, and `d/dt`), so they lie in `𝒞` by Lemma 5.12(b);
`τ = t^{-c}(q' − Zλ)` is a `κ((t))`-combination of them.  With
`dim 𝒞 = dim Θ_y + 1` (Lemma 5.12(a)) and `dim Θ_y ≤ d' + 1`, the `d' + 2`
independent columns of `M` span `𝒞`. -/
theorem step_M_spans_cone {m d : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k)) (q : Fin (m + 1) → PowerSeries κ) (hq0 : q 0 ≠ 0)
    (hbase : ∀ f ∈ I, MvPolynomial.eval₂ (algebraMap k (LaurentSeries κ))
      (dehomogenizedPoint (laurentColumn q)) f = 0)
    (D : Fin d → Derivation k κ κ) (Z : Matrix (Fin (m + 1)) (Fin d) (PowerSeries κ))
    (hZ : Z = coefficientwiseTangentMatrix q D)
    (lambda : Fin d → PowerSeries κ) (c : ℕ) (tau : Fin (m + 1) → PowerSeries κ)
    (hfactor : ∀ i, PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i =
      (PowerSeries.X : PowerSeries κ) ^ c * tau i)
    (hli : LinearIndependent (LaurentSeries κ)
      (fun col i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ)
        (formalTangentMatrix q Z tau i col)))
    (hbound : Module.finrank (LaurentSeries κ) (tangentSpaceAt (laurentColumn q) I) ≤ d + 1) :
    (∀ col, (fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ)
        (formalTangentMatrix q Z tau i col)) ∈ tangentCone (laurentColumn q) I) ∧
      Submodule.span (LaurentSeries κ) (Set.range fun col i ↦
        algebraMap (PowerSeries κ) (LaurentSeries κ) (formalTangentMatrix q Z tau i col)) =
        tangentCone (laurentColumn q) I := by
  classical
  let L := LaurentSeries κ
  let f := algebraMap (PowerSeries κ) L
  let qL := laurentColumn q
  let 𝒞 := tangentCone qL I
  have hq0L : qL 0 ≠ 0 := laurentColumn_ne_zero_of_ne_zero q hq0
  -- Lemma 5.12(b) at `y = q/q₀`.
  obtain ⟨hδ, hq⟩ := lemma_5_12_b qL hq0L I hbase
  have hder : ∀ δ : Derivation k (PowerSeries κ) (PowerSeries κ),
      laurentColumn (fun i ↦ δ (q i)) ∈ 𝒞 := by
    intro δ
    have h := hδ (extendPowerSeriesDerivation δ)
    have hcol : (fun a ↦ extendPowerSeriesDerivation δ (qL a)) =
        laurentColumn (fun i ↦ δ (q i)) := by
      funext a
      exact extendPowerSeriesDerivation_on_powerSeries δ (q a)
    rw [hcol] at h
    exact h
  have hZcol : ∀ l, (fun i ↦ f (Z i l)) ∈ 𝒞 := by
    intro l
    have h := hder (coefficientwiseDerivation (D l))
    rw [hZ]
    exact h
  have hq' : (fun i ↦ f (PowerSeries.derivative (R := κ) (q i))) ∈ 𝒞 :=
    hder (uniformizerDerivation (k := k) (K := κ))
  -- `τ = t^{-c} (q' − Σ λ_l Z_{•l})`.
  let Xc : L := f ((PowerSeries.X : PowerSeries κ) ^ c)
  have hXc : Xc ≠ 0 := by
    simp [Xc, f]
  have htau : (fun i ↦ f (tau i)) ∈ 𝒞 := by
    have hcomb := 𝒞.smul_mem Xc⁻¹ (𝒞.sub_mem hq'
      (𝒞.sum_mem fun l (_ : l ∈ Finset.univ) ↦ 𝒞.smul_mem (f (lambda l)) (hZcol l)))
    convert hcomb using 1
    funext i
    have hi := congrArg f (hfactor i)
    simp only [map_sub, map_mul, Matrix.mulVec, dotProduct, map_sum] at hi
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
    rw [eq_inv_mul_iff_mul_eq₀ hXc]
    rw [← hi]
    congr 1
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    ring
  have hcols : ∀ col, (fun i ↦ f (formalTangentMatrix q Z tau i col)) ∈ 𝒞 := by
    intro col
    rcases col with _ | (l | _)
    · exact hq
    · exact hZcol l
    · exact htau
  refine ⟨hcols, ?_⟩
  have hle : Submodule.span L (Set.range fun col i ↦ f (formalTangentMatrix q Z tau i col)) ≤ 𝒞 :=
    Submodule.span_le.mpr (by rintro _ ⟨col, rfl⟩; exact hcols col)
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [finrank_span_eq_card hli]
  -- Lemma 5.12(a): `dim 𝒞 = dim Θ_y + 1 ≤ d' + 2`.
  have hcone : Module.finrank (LaurentSeries κ) (tangentCone (laurentColumn q) I) =
      Module.finrank (LaurentSeries κ) (tangentSpaceAt (laurentColumn q) I) + 1 :=
    lemma_5_12_a_cone (laurentColumn q) hq0L I
  change Module.finrank (LaurentSeries κ) (tangentCone (laurentColumn q) I) ≤ _
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

/-- The row `u_υ`: the entries of `u` in the rows outside `ι`, and `0` on `ι`. -/
def complementRow {R ι : Type*} [DecidableEq R] [Fintype ι] (rowsι : ι ↪ R) (u : R → κ) :
    R → PowerSeries κ :=
  fun i ↦ if ∃ c, rowsι c = i then 0 else PowerSeries.C (u i)

/-- The block `ℓ_ι = −u_υ M_υ M_ι⁻¹`. -/
def liftBlock {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq R] [DecidableEq ι]
    (M : Matrix R ι (PowerSeries κ)) (rowsι : ι ↪ R) (u : R → κ) : ι → PowerSeries κ :=
  -Matrix.vecMul (rowMul (complementRow rowsι u) M) (selectedMinor M rowsι)⁻¹

/-- The paper's lift `ℓ` of `u`: `ℓ_υ = u_υ` and `ℓ_ι = −u_υ M_υ M_ι⁻¹`. -/
def liftRow {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq R] [DecidableEq ι]
    (M : Matrix R ι (PowerSeries κ)) (rowsι : ι ↪ R) (u : R → κ) : R → PowerSeries κ :=
  fun i ↦ complementRow rowsι u i + ∑ c, if rowsι c = i then liftBlock M rowsι u c else 0

omit [CharZero κ] in
theorem liftRow_apply_of_not_mem {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq R]
    [DecidableEq ι] (M : Matrix R ι (PowerSeries κ)) (rowsι : ι ↪ R) (u : R → κ) (i : R)
    (hi : ¬ ∃ c, rowsι c = i) : liftRow M rowsι u i = PowerSeries.C (u i) := by
  have hc : ∀ c, rowsι c ≠ i := fun c h ↦ hi ⟨c, h⟩
  simp [liftRow, complementRow, hc]

omit [CharZero κ] in
theorem liftRow_apply_rows {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq R]
    [DecidableEq ι] (M : Matrix R ι (PowerSeries κ)) (rowsι : ι ↪ R) (u : R → κ) (c : ι) :
    liftRow M rowsι u (rowsι c) = liftBlock M rowsι u c := by
  simp [liftRow, complementRow, rowsι.injective.eq_iff]

omit [CharZero κ] in
/-- **Paragraph lifting `u`.**  Let `M(0)` have full column rank and
`u M(0) = 0`.  There is a set `ι` of row indices with `M_ι(0)` invertible;
then `det M_ι` has nonzero constant term, so `M_ι` is invertible over
`κ[[t]]`, and `ℓ_υ = u_υ`, `ℓ_ι = −u_υ M_υ M_ι⁻¹` satisfies `ℓ M = 0` and
`ℓ(0) = u`. -/
theorem step_lift_ell_minor {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq R]
    [DecidableEq ι] (M : Matrix R ι (PowerSeries κ))
    (hinj : Function.Injective (residueMatrix M).mulVec) (u : R → κ)
    (hu : rowMul u (residueMatrix M) = 0) :
    ∃ rowsι : ι ↪ R,
      (selectedMinor (residueMatrix M) rowsι).det ≠ 0 ∧
      IsUnit (selectedMinor M rowsι).det ∧
      (∀ i, (¬ ∃ c, rowsι c = i) → liftRow M rowsι u i = PowerSeries.C (u i)) ∧
      (∀ c, liftRow M rowsι u (rowsι c) = liftBlock M rowsι u c) ∧
      rowMul (liftRow M rowsι u) M = 0 ∧
      residueColumn (liftRow M rowsι u) = u := by
  classical
  obtain ⟨rowsι, h0⟩ := exists_selectedMinor_det_ne_zero_of_mulVec_injective _ hinj
  have h0' : PowerSeries.constantCoeff (selectedMinor M rowsι).det ≠ 0 := by
    rwa [constantCoeff_selectedMinor_det]
  have hunit : IsUnit (selectedMinor M rowsι).det :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (IsUnit.mk0 _ h0')
  set ℓ := liftRow M rowsι u
  -- `ℓ M = ℓ_ι M_ι + ℓ_υ M_υ = −u_υ M_υ + u_υ M_υ = 0`.
  have hblock : Matrix.vecMul (liftBlock M rowsι u) (selectedMinor M rowsι) =
      -rowMul (complementRow rowsι u) M := by
    rw [liftBlock, Matrix.neg_vecMul, Matrix.vecMul_vecMul,
      Matrix.nonsing_inv_mul _ hunit, Matrix.vecMul_one]
  have hell : rowMul ℓ M = 0 := by
    funext col
    have h := congrFun hblock col
    simp only [Matrix.vecMul, dotProduct, selectedMinor, Pi.neg_apply] at h
    have hsplit : rowMul ℓ M col = rowMul (complementRow rowsι u) M col +
        ∑ c, liftBlock M rowsι u c * M (rowsι c) col := by
      simp only [ℓ, liftRow, rowMul, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    rw [hsplit, h, Pi.zero_apply, add_neg_cancel]
  refine ⟨rowsι, h0, hunit, liftRow_apply_of_not_mem M rowsι u, liftRow_apply_rows M rowsι u,
    hell, ?_⟩
  -- `ℓ(0) − u` vanishes off `ι` and is killed by `M(0)`, hence vanishes on `ι`.
  let δ : R → κ := residueColumn ℓ - u
  have hoff : ∀ i, (¬ ∃ c, rowsι c = i) → δ i = 0 := by
    intro i hi
    simp [δ, residueColumn, ℓ, liftRow_apply_of_not_mem M rowsι u i hi]
  have hδ : Matrix.vecMul (fun c ↦ δ (rowsι c)) (selectedMinor (residueMatrix M) rowsι) = 0 := by
    funext col
    have hℓ := congrArg PowerSeries.constantCoeff (congrFun hell col)
    have hu' := congrFun hu col
    simp only [rowMul, map_sum, map_mul, Pi.zero_apply, map_zero] at hℓ hu'
    have hsum : ∑ i, δ i * residueMatrix M i col = 0 := by
      simp only [δ, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [hu', sub_zero]
      exact hℓ
    rw [Pi.zero_apply, ← hsum]
    simp only [Matrix.vecMul, dotProduct, selectedMinor]
    refine Fintype.sum_of_injective rowsι rowsι.injective _ _ ?_ fun c ↦ rfl
    intro i hi
    rw [hoff i (by simpa using hi), zero_mul]
  have hA : IsUnit (selectedMinor (residueMatrix M) rowsι) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (IsUnit.mk0 _ h0)
  have hzero := Matrix.vecMul_injective_of_isUnit hA (hδ.trans (Matrix.zero_vecMul _).symm)
  funext i
  by_cases hi : ∃ c, rowsι c = i
  · obtain ⟨c, rfl⟩ := hi
    exact sub_eq_zero.mp (congrFun hzero c)
  · exact sub_eq_zero.mp (hoff i hi)

omit [CharZero k] [CharZero κ] in
/-- **Paragraph "`ℓ` annihilates `𝒞`".**  If the columns of `M` span `𝒞` and
`ℓ M = 0`, then `ℓ` annihilates `𝒞`, so by Lemma 5.13 its affine part
`ℓ̃ = (ℓ_1, …, ℓ_n)` lies in `span {df_y : f ∈ 𝔭}`; and `ℓ(0) = u` gives
`ℓ̃(0) = (1, 0, …, 0)`. -/
theorem step_ell_conormal {m : ℕ} (hm : 0 < m) {ι : Type*} [Fintype ι]
    (I : Ideal (MvPolynomial (Fin m) k)) (q : Fin (m + 1) → PowerSeries κ) (hq0 : q 0 ≠ 0)
    (M : Matrix (Fin (m + 1)) ι (PowerSeries κ))
    (hspan : Submodule.span (LaurentSeries κ) (Set.range fun col i ↦
      algebraMap (PowerSeries κ) (LaurentSeries κ) (M i col)) = tangentCone (laurentColumn q) I)
    (ell : Fin (m + 1) → PowerSeries κ) (hell : rowMul ell M = 0)
    (hres : residueColumn ell = axisRow (k := κ) (Fin.succ ⟨0, hm⟩)) :
    coordinateCovector (fun i : Fin m ↦ laurentColumn ell i.succ) ∈
        equationCovectorSpan (dehomogenizedPoint (laurentColumn q))
          (I.map (MvPolynomial.map (algebraMap k (LaurentSeries κ)))) ∧
      residueColumn (fun i : Fin m ↦ ell i.succ) =
        fun i ↦ if i = ⟨0, hm⟩ then 1 else 0 := by
  classical
  let L := LaurentSeries κ
  let f := algebraMap (PowerSeries κ) L
  let φ : (Fin (m + 1) → L) →ₗ[L] L :=
    { toFun := fun v ↦ ∑ a, laurentColumn ell a * v a
      map_add' := fun v w ↦ by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by ring }
  have hle : tangentCone (laurentColumn q) I ≤ LinearMap.ker φ := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨col, rfl⟩
    have h := congrArg f (congrFun hell col)
    simp only [rowMul, map_sum, map_mul, Pi.zero_apply, map_zero] at h
    exact h
  have hann : ∀ v ∈ tangentCone (laurentColumn q) I, ∑ a, laurentColumn ell a * v a = 0 :=
    fun v hv ↦ hle hv
  refine ⟨lemma_5_13 (laurentColumn q) (laurentColumn_ne_zero_of_ne_zero q hq0) I
    (laurentColumn ell) hann, ?_⟩
  calc
    residueColumn (fun i : Fin m ↦ ell i.succ) =
        (fun i : Fin m ↦ residueColumn ell i.succ) := residueColumn_tail ell
    _ = (fun i : Fin m ↦ axisRow (k := κ) (Fin.succ ⟨0, hm⟩) i.succ) := by
      rw [hres]
    _ = (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
      funext i
      by_cases hi : i = ⟨0, hm⟩
      · subst i
        simp [axisRow]
      · have hne : i.succ ≠ Fin.succ ⟨0, hm⟩ := fun h ↦ hi (Fin.succ_injective m h)
        rw [axisRow_apply_of_ne hne]
        simp [hi]

end PowerSeriesSteps

/-! ## The final paragraph -/

section PolynomialLimit

/-- The closing computation of the final paragraph for a phase point of the
equation conormal: a polynomial vanishing on `N(Y)` vanishes at the residue of
a regular fibre coordinate `ξ(t)` attached to a Laurent point `y` of `Y`. -/
theorem eval_residue_eq_zero_of_mem_groundEquationConormalLocus
    {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] {m : ℕ}
    (I : PrimeSpectrum (MvPolynomial (Fin m) k)) (Pol : MvPolynomial (Fin m) k)
    (hPol : Pol ∈ MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal))
    (y : Fin m → LaurentSeries K) (xi : Fin m → PowerSeries K)
    (hgeneric : Sum.elim y
        (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
      groundEquationConormalLocus (k := k) (K := K) I.asIdeal) :
    MvPolynomial.eval₂ (algebraMap k K) (residueColumn xi) Pol = 0 := by
  have hfull := fibreLift_mem_vanishingIdeal_equationConormal I.asIdeal I.isPrime Pol hPol
  -- `Φ(x, μ) = P(Σ μ_k ∇g_k(x))` has coefficients in `𝔭`, so it vanishes at `y`.
  have hvan : ∀ q ∈ groundEquationConormalLocus (k := k) (K := K) I.asIdeal,
      MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) q (fibreLift Pol) = 0 := by
    letI : Algebra k (LaurentSeries K) :=
      (groundLaurentMap (k := k) (K := K)).toAlgebra
    intro q hq
    exact scalarExtension_vanishing I.asIdeal (fibreLift Pol) hfull q hq
  have hpoly := residueFibreLift_mem_extensionValuedVanishingIdeal_of_ground_vanishing
    I.asIdeal Pol hvan
  -- `P(ξ(t)) = 0` in `κ[[t]]`, so its constant term `P(ξ(0))` vanishes.
  have hclosure := residue_mem_residueExtensionFibreClosure_of_laurent_generic
    (K := K) (groundEquationConormalLocus (k := k) (K := K) I.asIdeal) y xi hgeneric
  have hzero := hclosure _ hpoly
  simpa [residuePolynomialMap, scalarPolynomialMap] using hzero

/-- **Final paragraph.**  Let `P ∈ K[ξ]` vanish on `N(Y)`, let the equations
of `Y` vanish at the generic point `y ∈ κ((t))^n`, and let
`ℓ̃(t) ∈ κ[[t]]^n` lie in the `κ((t))`-span of `{dg_y : g ∈ 𝔭}`.  Then
`P(ℓ̃(0)) = 0`. -/
theorem step_polynomial_limit
    {k κ : Type u} [Field k] [IsAlgClosed k] [Field κ] [Algebra k κ] {m : ℕ}
    (I : PrimeSpectrum (MvPolynomial (Fin m) k)) (Pol : MvPolynomial (Fin m) k)
    (hPol : Pol ∈ MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal))
    (y : Fin m → LaurentSeries κ)
    (hbase : ∀ f ∈ I.asIdeal, MvPolynomial.eval₂ (algebraMap k (LaurentSeries κ)) y f = 0)
    (ell : Fin m → PowerSeries κ)
    (hell : coordinateCovector (fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ) (ell i)) ∈
      equationCovectorSpan y
        (I.asIdeal.map (MvPolynomial.map (algebraMap k (LaurentSeries κ))))) :
    MvPolynomial.eval₂ (algebraMap k κ) (residueColumn ell) Pol = 0 := by
  apply eval_residue_eq_zero_of_mem_groundEquationConormalLocus I Pol hPol y ell
  refine ⟨?_, ?_⟩
  · have hker : I.asIdeal.map (groundPolynomialMap (k := k) (K := κ) (Fin m)) ≤
        RingHom.ker (MvPolynomial.eval y) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change MvPolynomial.eval y (MvPolynomial.map (algebraMap k (LaurentSeries κ)) f) = 0
      rw [MvPolynomial.eval_map]
      exact hbase f hf
    intro f hf
    exact RingHom.mem_ker.mp (hker hf)
  · change coordinateCovector (fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ) (ell i)) ∈
      affineConormalSpace y (I.asIdeal.map (MvPolynomial.map (algebraMap k (LaurentSeries κ))))
    rw [affineConormalSpace_eq_equationCovectorSpan]
    exact hell

end PolynomialLimit

/-! ## Paragraphs at the place of Lemmas 5.9–5.10 -/

section Place

/-- **Paragraph "`a = ord q_0`", `a > 0`.**  If `a = 0`, then `q_0` is a unit of
`V`, hence all `x̄_i = q_i/q_0` lie in `V`, so `R ⊆ V` since also `K ⊆ V`,
contradicting Lemma 5.10(a) (`lemma_5_10_a_not_R_le`).  So `q_0 ∉ V^×`. -/
theorem step_a_pos {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal) :
    letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
      (ComponentFractionField P) := w.column.W.ambientAlgebra
    ¬ IsUnit (w.column.q 0) := by
  let C := w.column
  let W := C.W
  let K := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K := W.ambientAlgebra
  let V := W.place.valuation
  letI : IsDiscreteValuationRing V.toSubring := W.place.isDiscrete
  let x : Fin m → K := fun j ↦ componentCoordinate P j
  -- `1 = ḡ x̄_1` with `ḡ ∈ R = K[x̄_1, …, x̄_n]`.
  obtain ⟨g, hg⟩ := hunit
  let phi : MvPolynomial (Fin m) k →+* K :=
    (algebraMap (MvPolynomial (Fin m) k ⧸ P.asIdeal) K).comp (Ideal.Quotient.mk P.asIdeal)
  have hphiC : phi.comp MvPolynomial.C = algebraMap k K := by
    ext c
    exact IsScalarTower.algebraMap_apply k (MvPolynomial (Fin m) k ⧸ P.asIdeal) K c
  have hpoly : phi g = MvPolynomial.eval₂ (algebraMap k K) x g := by
    rw [MvPolynomial.map_mvPolynomial_eq_eval₂ phi g]
    change MvPolynomial.eval₂Hom (phi.comp MvPolynomial.C) (fun j ↦ phi (MvPolynomial.X j)) g =
      MvPolynomial.eval₂Hom (algebraMap k K) x g
    exact MvPolynomial.eval₂Hom_congr hphiC rfl rfl
  have hinverse : x ⟨0, hm⟩ * MvPolynomial.eval₂ (algebraMap k K) x g = 1 := by
    have hzero : phi (MvPolynomial.X ⟨0, hm⟩ * g - 1) = 0 := by
      have hmk : Ideal.Quotient.mk P.asIdeal (MvPolynomial.X ⟨0, hm⟩ * g - 1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hg
      simpa [phi] using congrArg (algebraMap (MvPolynomial (Fin m) k ⧸ P.asIdeal) K) hmk
    rw [map_sub, map_mul, map_one, sub_eq_zero, hpoly] at hzero
    exact hzero
  have hgR : MvPolynomial.eval₂ (algebraMap k K) x g ∈ Algebra.adjoin k (Set.range x) := by
    rw [← MvPolynomial.aeval_def, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨g, rfl⟩
  -- `x̄_1 = ϖ ∈ 𝔪_V`.
  have hxV : x ⟨0, hm⟩ ∈ V.toSubring := by
    change componentCoordinate P ⟨0, hm⟩ ∈ V.toSubring
    rw [← W.parameter_eq_coordinate]
    exact W.place.parameter.2
  have hxm : (⟨x ⟨0, hm⟩, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring := by
    have : (⟨x ⟨0, hm⟩, hxV⟩ : V.toSubring) = W.place.parameter :=
      Subtype.ext W.parameter_eq_coordinate.symm
    rw [this, mem_maximalIdeal, mem_nonunits_iff]
    exact W.place.parameter_nonunit
  have hR := lemma_5_10_a_not_R_le x ⟨0, hm⟩ V hxV hxm ⟨_, hgR, hinverse⟩
  rintro ⟨u, hu⟩
  apply hR
  -- `q_0 ∈ V^×` puts every `x̄_i = q_i/q_0` in `V`.
  have hq0 : (C.q 0 : K) = C.scale := by
    simpa [componentProjectivePoint] using C.q_commonScale 0
  have hxjV : ∀ j, x j ∈ V.toSubring := by
    intro j
    have hqj : (C.q (Fin.succ j) : K) = C.scale * x j := by
      simpa [componentProjectivePoint] using C.q_commonScale (Fin.succ j)
    have hscale : ((u : V.toSubring) : K) = C.scale := by rw [hu]; exact hq0
    have hu1 : ((u : V.toSubring) : K) * ((↑(u⁻¹) : V.toSubring) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]
      rfl
    have : x j = (C.q (Fin.succ j) : K) * ((↑(u⁻¹) : V.toSubring) : K) := by
      rw [hqj, ← hscale, mul_comm ((u : V.toSubring) : K), mul_assoc, hu1, mul_one]
    rw [this]
    exact V.toSubring.mul_mem (C.q _).2 (↑(u⁻¹) : V.toSubring).2
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact hxjV j
  | algebraMap c =>
      rw [← C.groundCoeff_commutes]
      exact (C.groundCoeff c).2
  | add a b _ _ ha hb => exact V.toSubring.add_mem ha hb
  | mul a b _ _ ha hb => exact V.toSubring.mul_mem ha hb

/-- **Paragraph "`a = ord q_0`, `b = ord q_1`".**  For the column
`q_i = x̄_i / x̄_j` of the discrete valuation ring of Lemmas 5.9–5.10, read in
`κ[[t]]`: `q_0 = t^a u_0` and `q_1 = t^b u_1` with `u_0(0) ≠ 0 ≠ u_1(0)` and
`0 < a < b` (`a > 0` by `step_a_pos`, from Lemma 5.10(a)); hence `q_j = 1`
forces `j ∉ {0, 1}`.  The hypothesis `hunit` (`x̄_1` is a unit of `R`) is the
consequence of `Y ∩ H = ∅`. -/
theorem step_orders {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal) :
    let C := w.column
    let W := C.W
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    let q : Fin (m + 1) → PowerSeries κ := fun a ↦ retainedToCompletedPowerSeries W (C.q a)
    ∃ (a b : ℕ) (u₀ u₁ : PowerSeries κ),
      0 < a ∧ a < b ∧
      q 0 = (PowerSeries.X : PowerSeries κ) ^ a * u₀ ∧ PowerSeries.constantCoeff u₀ ≠ 0 ∧
      q (Fin.succ ⟨0, hm⟩) = (PowerSeries.X : PowerSeries κ) ^ b * u₁ ∧
      PowerSeries.constantCoeff u₁ ≠ 0 ∧
      q C.chart = 1 ∧ C.chart ≠ 0 ∧ C.chart ≠ Fin.succ ⟨0, hm⟩ := by
  classical
  intro C W V κ q
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
    (ComponentFractionField P) := W.ambientAlgebra
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  -- `a > 0` (`step_a_pos`, by Lemma 5.10(a)) and `b - a = ord x̄_1 > 0`.
  have hq₀max : C.q 0 ∈ maximalIdeal V := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact step_a_pos hm P w hunit
  have hparammax : W.place.parameter ∈ maximalIdeal V := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact W.place.parameter_nonunit
  obtain ⟨a, b', u₀, u₁', ha, hab', hq0, hu₀, hq1'⟩ := completed_order_gap
    (retainedToCompletedPowerSeries W)
    (Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer V)
    (retainedToCompletedPowerSeries_chosenUniformizer W)
    (Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer_irreducible V)
    (C.q 0) W.place.parameter (C.q (Fin.succ ⟨0, hm⟩)) C.q0_ne
    W.place.parameter_ne hq₀max hparammax C.q_parameter
  have hqj : q C.chart = 1 :=
    (congrArg (retainedToCompletedPowerSeries W) C.chart_one).trans (map_one _)
  -- `q_1 = q_0 x̄_1 ≠ 0`, so `b = ord q_1` is finite.
  have hq1ne : q (Fin.succ ⟨0, hm⟩) ≠ 0 := by
    intro h
    have hV : C.q (Fin.succ ⟨0, hm⟩) = 0 :=
      retainedToCompletedPowerSeries_injective W (h.trans (map_zero _).symm)
    rw [C.q_parameter] at hV
    exact mul_ne_zero C.q0_ne W.place.parameter_ne hV
  have hu₁ : PowerSeries.constantCoeff (q (Fin.succ ⟨0, hm⟩)).divXPowOrder ≠ 0 :=
    fun h ↦ hq1ne (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.mp h)
  have hq1'' : q (Fin.succ ⟨0, hm⟩) = (PowerSeries.X : PowerSeries κ) ^ b' * u₁' := hq1'
  have hb : b' ≤ (q (Fin.succ ⟨0, hm⟩)).order.toNat := by
    by_contra hlt
    apply hu₁
    rw [PowerSeries.constantCoeff_divXPowOrder]
    generalize (q (Fin.succ ⟨0, hm⟩)).order.toNat = n at hlt ⊢
    rw [hq1'', PowerSeries.coeff_X_pow_mul']
    exact ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)
  have hconst : ∀ i, q i = (PowerSeries.X : PowerSeries κ) ^ a * u₀ → i ≠ C.chart := by
    intro i hi hij
    have hi1 : q i = 1 := by rw [hij]; exact hqj
    have h1 := congrArg PowerSeries.constantCoeff (hi1.symm.trans hi)
    simp [ha.ne'] at h1
  have hconst1 : C.chart ≠ Fin.succ ⟨0, hm⟩ := by
    intro hij
    have hi1 : q (Fin.succ ⟨0, hm⟩) = 1 := by rw [← hij]; exact hqj
    have h1 := congrArg PowerSeries.constantCoeff (hi1.symm.trans hq1'')
    simp [(ha.trans hab').ne'] at h1
  exact ⟨a, (q (Fin.succ ⟨0, hm⟩)).order.toNat, u₀, (q (Fin.succ ⟨0, hm⟩)).divXPowOrder,
    ha, hab'.trans_le hb, hq0, hu₀, PowerSeries.X_pow_order_mul_divXPowOrder.symm, hu₁, hqj,
    fun h ↦ hconst 0 hq0 h.symm, hconst1⟩

/-- **Paragraph defining `y` (equation (generic)).**  The affine point
`y = (q_1/q_0, …, q_n/q_0) ∈ κ((t))^n` is the image of `(x̄_1, …, x̄_n)` under
`F ↪ κ((t))`, so `f(y) = 0 ↔ f ∈ 𝔭` for every `f ∈ K[x]`. -/
theorem step_generic_point {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    let q : Fin (m + 1) → PowerSeries κ := fun a ↦ retainedToCompletedPowerSeries W (C.q a)
    ∀ f : MvPolynomial (Fin m) k,
      MvPolynomial.eval₂ (algebraMap k (LaurentSeries κ))
        (dehomogenizedPoint (laurentColumn q)) f = 0 ↔ f ∈ P.asIdeal := by
  classical
  intro C W V κ q
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
    (ComponentFractionField P) := W.ambientAlgebra
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  have hground := retainedLaurentLift_comp_algebraMap P ⟨0, hm⟩ W
  have hpoint := retainedLaurentLift_componentCoordinate P ⟨0, hm⟩ W C.q C.scale
    C.q_commonScale C.q0_ne
  have hker := component_generic_kernel_after_point_transport P
    (retainedLaurentLift P ⟨0, hm⟩ W) (RingHom.injective _) hground _ hpoint
  intro f
  rw [← MvPolynomial.eval_map]
  exact hker f

/-- **Lemma 5.11 for the valuation ring of the formal proof.**  The residues
`res q_i` of its normalized column satisfy `res q_0 = res q_1 = 0`,
`res q_j = 1`, and some `res q_i` with `i ∉ {0, 1, j}` have differentials
forming a basis of `Ω_{κ/K}`. -/
theorem witness_lemma_5_11
    {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal) :
    let C := w.column
    let W := C.W
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    residue V (C.q 0) = 0 ∧ residue V (C.q (Fin.succ ⟨0, hm⟩)) = 0 ∧
      residue V (C.q C.chart) = 1 ∧
      ∃ (d' : ℕ) (rows : Fin d' → Fin (m + 1)),
        Function.Injective rows ∧
        (∀ l, rows l ≠ 0 ∧ rows l ≠ Fin.succ ⟨0, hm⟩ ∧ rows l ≠ C.chart) ∧
        LinearIndependent κ
          (fun l ↦ KaehlerDifferential.D k κ (residue V (C.q (rows l)))) ∧
        Submodule.span κ
          (Set.range fun l ↦ KaehlerDifferential.D k κ (residue V (C.q (rows l)))) = ⊤ ∧
        d' = Module.finrank κ (Ω[κ⁄k]) := by
  classical
  let C := w.column
  let W := C.W
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
    (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  obtain ⟨a, b, u₀, u₁, ha, hab, hq0, -, hq1⟩ := order_gap_of_actual_witness hm P w hunit
  have hres := constantCoeff_retainedToCompleted_eq_residue (k := k) W
  have hr0 : residue V (C.q 0) = 0 := by
    rw [← hres, hq0]
    simp [ha.ne']
  have hr1 : residue V (C.q (Fin.succ ⟨0, hm⟩)) = 0 := by
    rw [← hres, hq1]
    simp [(ha.trans hab).ne']
  have hrj : residue V (C.q C.chart) = 1 := by
    rw [C.chart_one, map_one]
  have halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range fun a ↦ residue V (C.q a)) :
        IntermediateField k κ) κ := by
    have h := w.halg
    have hle : IntermediateField.adjoin k
          (Set.range fun j : Fin m ↦ residue V (C.q (Fin.succ j))) ≤
        IntermediateField.adjoin k (Set.range fun a ↦ residue V (C.q a)) :=
      IntermediateField.adjoin.mono _ _ _ (by rintro _ ⟨j, rfl⟩; exact ⟨_, rfl⟩)
    exact ⟨fun z ↦ IsAlgebraic.tower_top_of_subalgebra_le
      (IntermediateField.toSubalgebra_le_toSubalgebra.mpr hle) (h.isAlgebraic z)⟩
  exact ⟨hr0, hr1, hrj,
    lemma_5_11 hm (fun a ↦ residue V (C.q a)) C.chart hr0 hr1 hrj halg⟩

/-- **Lemmas 5.12(a), 5.12(b) and 5.13 at the Laurent generic point of the
formal proof, given the bound `m ≤ d' + 1`.**  For the column `q(t)` of
`witness_lemma_5_11`, with `y = q/q_0 ∈ κ((t))^n`: `dim Θ_y = dim_F Ω_{F/K}`,
this equals `trdeg_K F = m`, and `m ≤ d' + 1` (the hypothesis `hfieldRank`);
`dim 𝒞 = dim Θ_y + 1`; `δq ∈ 𝒞` for every `K`-derivation `δ` of `κ((t))` and
`q ∈ 𝒞`; and every row annihilating `𝒞` has conormal affine part. -/
theorem witness_lemma_5_12_5_13_of_bound
    {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hfieldRank :
      let C := w.column
      let W := C.W
      let F := ComponentFractionField P
      letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
      let V := W.place.valuation.toSubring
      letI : IsDiscreteValuationRing V := W.place.isDiscrete
      letI : Algebra W.coefficientField V :=
        (relativeCoefficientMap W.coefficientField W.place).toAlgebra
      let κ := ResidueField V
      letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
      Module.finrank F (Ω[F⁄k]) ≤ Module.finrank κ (Ω[κ⁄k]) + 1) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    let E := LaurentSeries κ
    letI : Algebra k E := (groundLaurentMap (k := k) (K := κ)).toAlgebra
    letI : SMul k E := (inferInstance : Algebra k E).toSMul
    letI : Module k E := (inferInstance : Algebra k E).toModule
    let q : Fin (m + 1) → E :=
      laurentColumn fun a ↦ retainedToCompletedPowerSeries W (C.q a)
    (Module.finrank E (tangentSpaceAt q P.asIdeal) = Module.finrank F (Ω[F⁄k]) ∧
      (Module.finrank F (Ω[F⁄k]) : Cardinal) = Algebra.trdeg k F ∧
      Module.finrank F (Ω[F⁄k]) ≤ Module.finrank κ (Ω[κ⁄k]) + 1 ∧
      Module.finrank E (tangentCone q P.asIdeal) =
        Module.finrank E (tangentSpaceAt q P.asIdeal) + 1) ∧
    ((∀ δ : Derivation k E E, (fun a ↦ δ (q a)) ∈ tangentCone q P.asIdeal) ∧
      q ∈ tangentCone q P.asIdeal) ∧
    (∀ ell : Fin (m + 1) → E, (∀ v ∈ tangentCone q P.asIdeal, ∑ a, ell a * v a = 0) →
      coordinateCovector (fun i : Fin m ↦ ell i.succ) ∈
        equationCovectorSpan (dehomogenizedPoint q)
          (P.asIdeal.map (MvPolynomial.map (algebraMap k E)))) := by
  classical
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  let E := LaurentSeries κ
  letI : Algebra k E := (groundLaurentMap (k := k) (K := κ)).toAlgebra
  letI : SMul k E := (inferInstance : Algebra k E).toSMul
  letI : Module k E := (inferInstance : Algebra k E).toModule
  let q : Fin (m + 1) → E :=
    laurentColumn fun a ↦ retainedToCompletedPowerSeries W (C.q a)
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : CharZero κ :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k κ)
  let i₀ : Fin m := ⟨0, hm⟩
  let ell : F →+* E := retainedLaurentLift P i₀ W
  have hground : ell.comp (algebraMap k F) = groundLaurentMap (k := k) (K := κ) :=
    retainedLaurentLift_comp_algebraMap P i₀ W
  have hpoint : ell ∘ componentCoordinate P = dehomogenizedPoint q :=
    retainedLaurentLift_componentCoordinate P i₀ W C.q C.scale C.q_commonScale C.q0_ne
  have hq0 : q 0 ≠ 0 := by
    intro h
    apply C.q0_ne
    have h1 : HahnSeries.ofPowerSeries ℤ κ (retainedToCompletedPowerSeries W (C.q 0)) = 0 := by
      simpa [q, laurentColumn] using h
    have h' : retainedToCompletedPowerSeries W (C.q 0) = 0 :=
      HahnSeries.ofPowerSeries_injective (h1.trans (map_zero _).symm)
    exact (retainedToCompletedPowerSeries_injective W) (by rw [h', map_zero])
  have hbase : ∀ f ∈ P.asIdeal,
      MvPolynomial.eval₂ (algebraMap k E) (dehomogenizedPoint q) f = 0 :=
    fun f hf ↦ component_equations_vanish_after_point_transport P ell hground _ hpoint hf
  have hcone := lemma_5_12_a_cone q hq0 P.asIdeal
  have hb := lemma_5_12_b q hq0 P.asIdeal hbase
  have h13 := fun ell hell ↦ lemma_5_13 q hq0 P.asIdeal ell hell
  -- Lemma 5.12(a): `dim Θ_y = dim_F Ω_{F/K} = trdeg_K F ≤ d' + 1`.
  letI : Algebra F E := ell.toAlgebra
  letI : SMul k F := (inferInstance : Algebra k F).toSMul
  letI : Module k F := (inferInstance : Algebra k F).toModule
  letI : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun c ↦ by
    have h := congrArg (fun f : k →+* E ↦ f c) hground
    change (groundLaurentMap (k := k) (K := κ)) c = ell (algebraMap k F c)
    exact h.symm
  have hchartPoint : (fun j : Fin m ↦ algebraMap F E
      (Stafford38.Geometry.GenericPointKaehlerConormal.genericPoint P.asIdeal F j)) =
        dehomogenizedPoint q := by
    funext j
    exact congrFun hpoint j
  have hdim := generic_tangent_finrank_eq_component_kaehler_finrank (F := F) (E := E)
    (I := P.asIdeal)
  rw [hchartPoint] at hdim
  have htr := (component_kaehler_finrank_eq_trdeg (k := k) (componentCoordinate P)
    (componentCoordinate_adjoin_eq_top P)).1
  exact ⟨⟨hdim, htr, hfieldRank, hcone⟩, hb, h13⟩

/-- **Lemmas 5.12(a), 5.12(b) and 5.13 at the Laurent generic point of the
formal proof.**  For the column `q(t)` of `witness_lemma_5_11`, with
`y = q/q_0 ∈ κ((t))^n`: `dim Θ_y = dim_F Ω_{F/K}`, this equals
`trdeg_K F = m`, and `m ≤ d' + 1` by the printed argument
(`witness_lemma_5_12_a_bound`: second fundamental exact sequence for `V → κ`,
Nakayama with `Ω_{V/K}` finitely generated by Lemma 5.10(c), and
`F ⊗_V Ω_{V/K} = Ω_{F/K}`); `dim 𝒞 = dim Θ_y + 1`; `δq ∈ 𝒞` for every
`K`-derivation `δ` of `κ((t))` and `q ∈ 𝒞`; and every row annihilating `𝒞` has
conormal affine part. -/
theorem witness_lemma_5_12_5_13_paper
    {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hfin :
      letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
        (ComponentFractionField P) := w.column.W.ambientAlgebra
      let V := w.column.W.place.valuation.toSubring
      letI : Algebra k V := w.column.groundCoeff.toAlgebra
      Module.Finite V (Ω[V⁄k])) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    let E := LaurentSeries κ
    letI : Algebra k E := (groundLaurentMap (k := k) (K := κ)).toAlgebra
    letI : SMul k E := (inferInstance : Algebra k E).toSMul
    letI : Module k E := (inferInstance : Algebra k E).toModule
    let q : Fin (m + 1) → E :=
      laurentColumn fun a ↦ retainedToCompletedPowerSeries W (C.q a)
    (Module.finrank E (tangentSpaceAt q P.asIdeal) = Module.finrank F (Ω[F⁄k]) ∧
      (Module.finrank F (Ω[F⁄k]) : Cardinal) = Algebra.trdeg k F ∧
      Module.finrank F (Ω[F⁄k]) ≤ Module.finrank κ (Ω[κ⁄k]) + 1 ∧
      Module.finrank E (tangentCone q P.asIdeal) =
        Module.finrank E (tangentSpaceAt q P.asIdeal) + 1) ∧
    ((∀ δ : Derivation k E E, (fun a ↦ δ (q a)) ∈ tangentCone q P.asIdeal) ∧
      q ∈ tangentCone q P.asIdeal) ∧
    (∀ ell : Fin (m + 1) → E, (∀ v ∈ tangentCone q P.asIdeal, ∑ a, ell a * v a = 0) →
      coordinateCovector (fun i : Fin m ↦ ell i.succ) ∈
        equationCovectorSpan (dehomogenizedPoint q)
          (P.asIdeal.map (MvPolynomial.map (algebraMap k E)))) :=
  witness_lemma_5_12_5_13_of_bound hm P w (witness_lemma_5_12_a_bound hm P w hfin)

end Place

#print axioms exists_mem_zeroLocus_of_isPrime
#print axioms exists_smoothAffinePoint
#print axioms step_coordinate_algebraic
#print axioms step_dual_derivations
#print axioms step_lambda_w_tau
#print axioms step_M_minor
#print axioms step_M_spans_cone
#print axioms step_lift_ell_minor
#print axioms step_ell_conormal
#print axioms step_polynomial_limit
#print axioms step_a_pos
#print axioms step_orders
#print axioms step_generic_point
#print axioms witness_lemma_5_11
#print axioms witness_lemma_5_12_5_13_of_bound
#print axioms witness_lemma_5_12_5_13_paper

end

end Stafford38.Paper.Section5
