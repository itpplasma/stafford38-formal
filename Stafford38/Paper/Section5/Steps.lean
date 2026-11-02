module

public import Stafford38.Paper.Section5.ResidueBasis
public import Stafford38.Paper.Section5.TangentCone
public import Stafford38.Paper.Section5.GenericTangentRank
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
  -- Definition 5.2(c): `D_k = B^*_k ∘ d`.
  let D : Fin d → Derivation k κ κ := fun k' ↦ (B.coord k').compDer (KaehlerDifferential.D k κ)
  have hdual : ∀ k' l, D k' (PowerSeries.constantCoeff (q (rows l))) =
      if k' = l then 1 else 0 := by
    intro k' l
    have hB : B l = KaehlerDifferential.D k κ (PowerSeries.constantCoeff (q (rows l))) :=
      Module.Basis.mk_apply _ _ _
    change B.coord k' (KaehlerDifferential.D k κ _) = _
    rw [← hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : k' = l
    · subst h; simp
    · simp [h, Ne.symm h]
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

/-- **Paragraph defining `λ`, `w` and `τ`.**  The selected minor `Z̃` is
invertible over `κ[[t]]`, so some `λ` solves `Z̃ λ = (q'_{i_l})`.  With
`w = q' − Zλ`, the minimal order `c` of the entries of `w` is at most `a − 1`,
and `τ = t^{-c} w` lies over `κ[[t]]` with `τ(0) ≠ 0`, `τ_{i_l} = 0`, `τ_j = 0`
and `τ_1(0) = 0`.  Stated as `q' − Zλ = t^c τ`. -/
theorem step_lambda_tau {m d : ℕ} (hm : 0 < m)
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
      c ≤ a - 1 ∧
      (∀ i, PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i =
        (PowerSeries.X : PowerSeries κ) ^ c * tau i) ∧
      (∃ i, PowerSeries.constantCoeff (tau i) ≠ 0) ∧
      (∀ l, tau (rows l) = 0) ∧ tau j = 0 ∧
      PowerSeries.constantCoeff (tau (Fin.succ ⟨0, hm⟩)) = 0 := by
  classical
  obtain ⟨lambda, c, tau, -, -, -, hsel, htauj, htaurows, hc, hfactor, hprim, htau1,
      -, -, -, -⟩ :=
    exists_formalDivisorAxisLift q Z rows j 0 (Fin.succ ⟨0, hm⟩) a b u₀ u₁ hqj hZj ha hab
      hq0 hu₀ hZ0 hq1 hZ1 (by rw [hminor]; exact one_ne_zero)
  exact ⟨lambda, c, tau, hsel, hc, hfactor, hprim, htaurows, htauj, htau1⟩

/-- **Paragraph "`M(0)` has full column rank".**  For
`M = (q, Z_{•1}, …, Z_{•d'}, τ)`, the reduction `M(0)` is injective (row `j`,
the identity block on the rows `i_l`, and `τ(0) ≠ 0`), so `M` has a left
inverse over `κ[[t]]`; this is the paper's unit `(d'+2)`-minor, packaged as a
left inverse.  The columns of `M` are linearly independent over `κ((t))`, and
every column of `M(0)` has vanishing `1`-coordinate. -/
theorem step_M_full_rank {m d : ℕ} (hm : 0 < m)
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
    ∃ Cinv : Matrix (FormalTangentColumn (Fin d)) (Fin (m + 1)) (PowerSeries κ),
      Cinv * formalTangentMatrix q Z tau = 1 ∧
      LinearIndependent (LaurentSeries κ)
        (fun col i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ)
          (formalTangentMatrix q Z tau i col)) ∧
      ∀ col, PowerSeries.constantCoeff
        (formalTangentMatrix q Z tau (Fin.succ ⟨0, hm⟩) col) = 0 := by
  classical
  have hinj := residue_formalTangentMatrix_mulVec_injective q Z tau rows j hqj hZj htauj
    htaurows (by rw [hminor]; exact one_ne_zero) hprim
  obtain ⟨Cinv, hCM⟩ := powerSeries_exists_leftInverse_of_residue_mulVec_injective _ hinj
  refine ⟨Cinv, hCM, ?_,
    constantCoeff_formalTangentMatrix_axis_eq_zero q Z tau _ b u₁ hb hq1 hZ1 htau1⟩
  let f := algebraMap (PowerSeries κ) (LaurentSeries κ)
  let ML := (formalTangentMatrix q Z tau).map f
  let CL := Cinv.map f
  have hCL : CL * ML = 1 := by
    have h := congrArg (fun A ↦ A.map f) hCM
    simpa [CL, ML, Matrix.map_mul] using h
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmv : ML.mulVec g = 0 := by
    funext i
    have hi := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    rw [Pi.zero_apply, ← hi]
    simp only [Matrix.mulVec, dotProduct, ML, Matrix.map_apply]
    exact Finset.sum_congr rfl fun col _ ↦ mul_comm _ _
  have hg0 : g = CL.mulVec (ML.mulVec g) := by
    rw [Matrix.mulVec_mulVec, hCL, Matrix.one_mulVec]
  rw [hmv, Matrix.mulVec_zero] at hg0
  intro col
  rw [hg0]
  rfl

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

omit [CharZero κ] in
/-- **Paragraph lifting `u`.**  Since `M(0)` has vanishing `1`-coordinate in
every column, `u M(0) = 0` for `u = (0, 1, 0, …, 0)`; using the left inverse of
`M`, `u` lifts to `ℓ ∈ κ[[t]]^{n+1}` with `ℓ M = 0` and `ℓ(0) = u`.  The paper
writes the lift with an invertible square block `M_ι`; the left inverse plays
that role. -/
theorem step_lift_ell {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin (m + 1)) ι (PowerSeries κ))
    (Cinv : Matrix ι (Fin (m + 1)) (PowerSeries κ)) (hCM : Cinv * M = 1)
    (axis : Fin (m + 1)) (haxis : ∀ col, PowerSeries.constantCoeff (M axis col) = 0) :
    ∃ ell : Fin (m + 1) → PowerSeries κ,
      rowMul ell M = 0 ∧ residueColumn ell = axisRow (k := κ) axis := by
  classical
  have h₀ : rowMul (axisRow (k := κ) axis)
      (fun i col ↦ PowerSeries.constantCoeff (M i col)) = 0 := by
    funext col
    simp [rowMul, axisRow, haxis col]
  exact ⟨_, powerSeries_annihilatorLift_spec (constantColumn (axisRow (k := κ) axis)) _ M Cinv
    hCM (residueColumn_constantColumn _) h₀⟩

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

/-- **Paragraph "`a = ord q_0`, `b = ord q_1`".**  For the column
`q_i = x̄_i / x̄_j` of the discrete valuation ring of Lemmas 5.9–5.10, read in
`κ[[t]]`: `q_0 = t^a u_0` and `q_1 = t^b u_1` with `u_0(0) ≠ 0 ≠ u_1(0)` and
`0 < a < b`; hence `q_j = 1` forces `j ∉ {0, 1}`.  The hypothesis `hunit`
(`x̄_1` is a unit of `R`) is the consequence of `Y ∩ H = ∅` that gives `a > 0`. -/
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
  obtain ⟨a, b', u₀, u₁', ha, hab', hq0, hu₀, hq1'⟩ := order_gap_of_actual_witness hm P w hunit
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
formal proof.**  For the column `q(t)` of `witness_lemma_5_11`, with
`y = q/q_0 ∈ κ((t))^n`: `dim Θ_y = dim_F Ω_{F/K}`, this equals
`trdeg_K F = m`, and `m ≤ d' + 1`; `dim 𝒞 = dim Θ_y + 1`; `δq ∈ 𝒞` for every
`K`-derivation `δ` of `κ((t))` and `q ∈ 𝒞`; and every row annihilating `𝒞` has
conormal affine part. -/
theorem witness_lemma_5_12_5_13
    {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
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
  have hgenPoint : IntermediateField.adjoin k
      (Set.range (Stafford38.Geometry.GenericPointKaehlerConormal.genericPoint P.asIdeal F)) =
        ⊤ := by
    have hcoordinates :
        Stafford38.Geometry.GenericPointKaehlerConormal.genericPoint P.asIdeal F =
          componentCoordinate P := by
      funext j
      rfl
    rw [hcoordinates]
    exact componentCoordinate_adjoin_eq_top P
  have hchartPoint : (fun j : Fin m ↦ algebraMap F E
      (Stafford38.Geometry.GenericPointKaehlerConormal.genericPoint P.asIdeal F j)) =
        dehomogenizedPoint q := by
    funext j
    exact congrFun hpoint j
  have hdim := generic_tangent_finrank_eq_component_kaehler_finrank (E := E)
    (I := P.asIdeal) hgenPoint
  rw [hchartPoint] at hdim
  have htr := (component_kaehler_finrank_eq_trdeg (k := k) (componentCoordinate P)
    (componentCoordinate_adjoin_eq_top P)).1
  have hfieldRank : Module.finrank F (Ω[F⁄k]) ≤ Module.finrank κ (Ω[κ⁄k]) + 1 :=
    component_field_rank_of_witness hm P w
  exact ⟨⟨hdim, htr, hfieldRank, hcone⟩, hb, h13⟩

end Place

#print axioms step_dual_derivations
#print axioms step_lambda_tau
#print axioms step_M_full_rank
#print axioms step_M_spans_cone
#print axioms step_lift_ell
#print axioms step_ell_conormal
#print axioms step_polynomial_limit
#print axioms step_orders
#print axioms step_generic_point
#print axioms witness_lemma_5_11
#print axioms witness_lemma_5_12_5_13

end

end Stafford38.Paper.Section5
