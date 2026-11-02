module

public import Stafford38.Paper.Section5.Steps
public import Stafford38.Geometry.FiniteGradientResidueExtension
public import Stafford38.Geometry.GeneralConstantCoordinateAxis
public import Stafford38.Geometry.GeneralCoordinateAvoidance

@[expose] public section

/-!
# Theorem 5.7(i), proved paragraph by paragraph

The proof below follows Section 5.2 of the paper.  Each block names the
paragraph it formalizes and calls the declaration of
`Stafford38.Paper.Section5.Steps` that states it, together with the paper's
Lemmas 5.11 (`witness_lemma_5_11`, via `lemma_5_11`), 5.12(a) and 5.12(b)
(`lemma_5_12_a_cone`, `lemma_5_12_b` in `step_M_spans_cone`, with the tangent
bound of `witness_lemma_5_12_5_13`) and 5.13 (`lemma_5_13` in
`step_ell_conormal`).
-/

namespace Stafford38.Paper.Section5

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.FiniteGradientResidueExtension
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.GeneralConstantCoordinateAxis
open Stafford38.Geometry.GeneralCoordinateAvoidance
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.KaehlerVisibleDerivationFrame
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.PaperResidueDerivationFrame
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.SmoothConormalFibreVanishing

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000

universe u

/-- **Theorem 5.7(i), along the paper's proof.**  If `Y = V(𝔭)` is nonempty,
irreducible and avoids `H = {x_1 = 0}`, every polynomial vanishing on the
conormal cone `N(Y)` over the smooth locus vanishes at `(1, 0, …, 0)`. -/
theorem theorem_5_7_i_paper
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal)) := by
  classical
  intro Pol hPol
  by_cases halg : IsAlgebraic k (componentCoordinate I ⟨0, hm⟩)
  · -- First paragraph: `x̄_1` algebraic, so `x_1 − c ∈ 𝔭` and
    -- `(1, 0, …, 0) = dx_1` is conormal at points of `Y`.
    obtain ⟨c, y, -, -, hmem⟩ := exists_constant_coordinate_equation_and_pure_axis hm I halg
    have h := fibreLift_mem_vanishingIdeal_equationConormal I.asIdeal I.isPrime Pol hPol _ hmem
    simpa [fibreLift, MvPolynomial.eval_rename, Function.comp_def] using h
  -- `x̄_1` transcendental.  `Y ∩ H = ∅` makes `x̄_1` a unit of `R`.
  have hunit := exists_coordinate_inverse_of_avoidance I.asIdeal ⟨0, hm⟩ havoid
  -- Lemmas 5.9–5.10: the discrete valuation ring `V` of `F` at infinity, the
  -- column `q_i = x̄_i / x̄_j` and `κ = V/𝔪_V`, read in `V̂ ≅ κ[[t]]`.
  obtain ⟨w⟩ := generalDivisorialVisibleFrameWithResidueAlgebraicity hm I hunit halg
  let C := w.column
  let W := C.W
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
    (ComponentFractionField I) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra I ⟨0, hm⟩ W
  letI : CharZero κ :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k κ)
  let q : Fin (m + 1) → PowerSeries κ := fun a ↦ retainedToCompletedPowerSeries W (C.q a)
  let axis : Fin (m + 1) := Fin.succ ⟨0, hm⟩
  -- Paragraph "`a = ord q_0`, `b = ord q_1`": `0 < a < b`, `j ∉ {0, 1}`.
  obtain ⟨a, b, u₀, u₁, ha, hab, hq0, hu₀, hq1, -, hqj, -, -⟩ := step_orders hm I w hunit
  have hq0ne : q 0 ≠ 0 := by
    intro h
    apply hu₀
    have h' : (PowerSeries.X : PowerSeries κ) ^ a * u₀ = 0 := hq0.symm.trans h
    rw [mul_eq_zero] at h'
    rcases h' with h' | h'
    · exact absurd h' (pow_ne_zero a PowerSeries.X_ne_zero)
    · rw [h', map_zero]
  -- Paragraph defining `y`, equation (generic): `f(y) = 0` for `f ∈ 𝔭`.
  have hbase : ∀ f ∈ I.asIdeal, MvPolynomial.eval₂ (algebraMap k (LaurentSeries κ))
      (dehomogenizedPoint (laurentColumn q)) f = 0 :=
    fun f hf ↦ (step_generic_point hm I w f).2 hf
  -- Lemma 5.11: `d(q_{i_l}(0))`, `i_l ∉ {0, 1, j}`, form a basis of `Ω_{κ/K}`.
  obtain ⟨-, -, -, d, rows, hinj, -, hli, hspan, hd⟩ := witness_lemma_5_11 hm I w hunit
  have hres := constantCoeff_retainedToCompleted_eq_residue (k := k) W
  have hresRows : (fun l ↦ KaehlerDifferential.D k κ (PowerSeries.constantCoeff (q (rows l)))) =
      fun l ↦ KaehlerDifferential.D k κ (residue V (C.q (rows l))) := by
    funext l
    rw [hres]
  rw [← hresRows] at hli hspan
  let rowsE : Fin d ↪ Fin (m + 1) := ⟨rows, hinj⟩
  -- Paragraph after Lemma 5.11: dual derivations `D_k` and the matrix `Z(t)`.
  obtain ⟨D, -, -, hminor, hZj, hZ0, hZ1⟩ :=
    step_dual_derivations (k := k) hm q rowsE hli hspan C.chart hqj a b u₀ u₁ hq0 hq1
  let Z := coefficientwiseTangentMatrix q D
  -- Paragraph defining `λ`, `w = q' − Zλ`, `c ≤ a − 1` and `τ = t^{-c} w`.
  obtain ⟨lambda, c, tau, -, -, hfactor, hprim, htaurows, htauj, htau1⟩ :=
    step_lambda_tau hm q Z rowsE C.chart a b u₀ u₁ hqj hZj ha hab hq0 hu₀ hZ0 hq1 hZ1 hminor
  -- Paragraph "`M(0)` has full column rank" for `M = (q, Z, τ)`.
  obtain ⟨Cinv, hCM, hliM, haxis⟩ :=
    step_M_full_rank hm q Z tau rowsE C.chart b u₁ hqj hZj htauj htaurows hminor hprim
      (ha.trans hab) hq1 hZ1 htau1
  -- Lemma 5.12(a): `dim Θ_y = dim_F Ω_{F/K} ≤ d' + 1`.
  obtain ⟨⟨hdim, -, hfieldRank, -⟩, -, -⟩ := witness_lemma_5_12_5_13 hm I w
  have hbound : Module.finrank (LaurentSeries κ)
      (tangentSpaceAt (laurentColumn q) I.asIdeal) ≤ d + 1 := by
    rw [hd]
    exact hdim.trans_le hfieldRank
  -- Paragraph "the columns of `M` span `𝒞`" (Lemmas 5.12(a), 5.12(b)).
  obtain ⟨-, hspanC⟩ :=
    step_M_spans_cone I.asIdeal q hq0ne hbase D Z rfl lambda c tau hfactor hliM hbound
  -- Paragraph lifting `u = (0, 1, 0, …, 0)` to `ℓ(t)` with `ℓM = 0`.
  obtain ⟨ell, hell, hellres⟩ := step_lift_ell _ Cinv hCM axis haxis
  -- Paragraph "`ℓ` annihilates `𝒞`" (Lemma 5.13): `ℓ̃ ∈ span {df_y}`.
  obtain ⟨hconormal, htail⟩ :=
    step_ell_conormal hm I.asIdeal q hq0ne _ hspanC ell hell hellres
  -- Final paragraph: `P(ℓ̃(0)) = 0` with `ℓ̃(0) = (1, 0, …, 0)`.
  have hzero := step_polynomial_limit I Pol hPol _ hbase (fun i ↦ ell i.succ) hconormal
  rw [htail, eval₂_extensionAxis_eq_algebraMap_eval_axis (K := κ) hm Pol] at hzero
  exact (FaithfulSMul.algebraMap_injective k κ) (hzero.trans (map_zero _).symm)

#print axioms theorem_5_7_i_paper

end

end Stafford38.Paper.Section5
