module
public import Stafford38.Geometry.PaperLaurentChartDerivation
public import Stafford38.Geometry.KaehlerVisibleDerivationFrame
public import Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof
public import Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction
public import Stafford38.Geometry.RetainedPlaceConormalTransport
public import Stafford38.Geometry.RetainedGroundMapIdentification
public import Stafford38.Geometry.ProjectiveBoundaryFrameRank
public import Stafford38.Geometry.ProjectiveChartCoordinates
public import Stafford38.Geometry.ProjectiveTangentInclusion
public import Stafford38.Geometry.CompletedDVRPowerSeriesEquiv

@[expose] public section

/-!
# Tangent generators from an actual retained completed divisor chart

This module connects residue-field derivations and the uniformizer derivation
to the dehomogenized Laurent point of a retained projective column.  The
projective column `q` is kept separate from its affine ratios `q_(i+1)/q_0`.
-/

namespace Stafford38.Geometry.PaperActualDivisorTangent

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.KaehlerVisibleDerivationFrame
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.PaperLaurentChartDerivation
open Stafford38.Geometry.ProjectiveBoundaryFrameRank
open Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof
open Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.CompletedDVRCoefficientSection
open Stafford38.Geometry.ProjectiveTangentInclusion
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveDivisorOrderGap
open Stafford38.GeometryPowerSeriesTangentLimit
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.RetainedDVR
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.GeometryFormalDivisorAxisLift
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryResidueMinorSelection
open Stafford38.GeometryRetractionSpecialization
open Stafford38.GeometrySplitTangentMatrix

noncomputable section

universe u

variable {k κ : Type u} [Field k] [Field κ] [Algebra k κ]
  [CharZero k] [CharZero κ]

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

/-! ## Identify the completed chart parameter -/

/-- The actual chosen uniformizer of a retained divisor maps to the formal
series variable under its completed power-series chart. -/
theorem retainedToCompletedPowerSeries_chosenUniformizer
    {F : Type u} [Field F] [Algebra k F] {x : F}
    (W : Data k F x) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F :=
      W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    retainedToCompletedPowerSeries W (chosenUniformizer V) =
      (PowerSeries.X : PowerSeries (ResidueField V)) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F :=
    W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  apply W.completedPowerSeriesEquiv.injective
  calc
    W.completedPowerSeriesEquiv (retainedToCompletedPowerSeries W
        (chosenUniformizer V)) =
        algebraMap V (AdicCompletion (maximalIdeal V) V)
          (chosenUniformizer V) := by
      simp [retainedToCompletedPowerSeries]
      rfl
    _ = W.completedPowerSeriesEquiv PowerSeries.X := by
      symm
      change completedDVRPowerSeriesMap W.coefficientField V
          (relativeResidue_isSeparable W.coefficientField W.place)
          PowerSeries.X =
        algebraMap V (AdicCompletion (maximalIdeal V) V)
          (chosenUniformizer V)
      rw [completedDVRPowerSeriesMap_X]
      rfl

/-! ## Preserve the differentiated column while constructing its split -/

/-- Strengthened form of the normalized formal divisor-axis construction.
Besides the split matrix and annihilating row, it retains the exact identity
that expresses the normalized transverse column in terms of the actual
uniformizer derivative and the residue-derivation columns. -/
theorem exists_formalDivisorAxisLift_with_derivative_relation
    {ι : Type*} {δ : Type*} [Fintype ι] [Fintype δ]
    [DecidableEq ι] [DecidableEq δ]
    (q : ι → PowerSeries κ)
    (Z : Matrix ι δ (PowerSeries κ))
    (rows : δ ↪ ι) (chart zero axis : ι)
    (a b : ℕ) (u₀ u₁ : PowerSeries κ)
    (hqchart : q chart = 1) (hZchart : ∀ j, Z chart j = 0)
    (ha : 0 < a) (hab : a < b)
    (hqzero : q zero = (PowerSeries.X : PowerSeries κ) ^ a * u₀)
    (hu₀ : PowerSeries.constantCoeff u₀ ≠ 0)
    (hZzero : ∀ j, ∃ w : PowerSeries κ,
      Z zero j = (PowerSeries.X : PowerSeries κ) ^ a * w)
    (hqaxis : q axis = (PowerSeries.X : PowerSeries κ) ^ b * u₁)
    (hZaxis : ∀ j, ∃ w : PowerSeries κ,
      Z axis j = (PowerSeries.X : PowerSeries κ) ^ b * w)
    (hminor : PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0) :
    ∃ (lambda : δ → PowerSeries κ) (c : ℕ)
      (tau : ι → PowerSeries κ)
      (C : Matrix (FormalTangentColumn δ) ι (PowerSeries κ))
      (ell : ι → PowerSeries κ),
      c ≤ a - 1 ∧
      (∀ i, PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i =
        (PowerSeries.X : PowerSeries κ) ^ c * tau i) ∧
      (∃ i, PowerSeries.constantCoeff (tau i) ≠ 0) ∧
      C * formalTangentMatrix q Z tau = 1 ∧
      rowMul ell (formalTangentMatrix q Z tau) = 0 ∧
      residueColumn ell = axisRow (k := κ) axis := by
  obtain ⟨lambda, c, tau, C, ell, _hlambda, _hselected,
      _htauchart, _htauselected, hc, hfactor, hprimitive,
      _htauaxis, _haxiscolumns, hCB, hrow, hresidue⟩ :=
    exists_formalDivisorAxisLift q Z rows chart zero axis a b u₀ u₁
      hqchart hZchart ha hab hqzero hu₀ hZzero hqaxis hZaxis hminor
  exact ⟨lambda, c, tau, C, ell, hc, hfactor, hprimitive, hCB,
    hrow, hresidue⟩

/-! ## Linear-algebra comparison in the actual affine chart -/

abbrev zeroChartIndexEquiv {m : ℕ} :
    Fin m ≃ ChartAffineIndex (Fin (m + 1)) 0 :=
  Stafford38.Geometry.ProjectiveChartCoordinates.zerothChartEquiv (m := m)

/-- A left inverse of the augmented projective matrix makes the affine
dehomogenizations of its nonposition columns independent in the `q₀` chart. -/
theorem linearIndependent_dehomogenizedTangentColumns
    {m : ℕ} (hm : 0 < m) {δ : Type*} [Fintype δ]
    (q : Fin (m + 1) → LaurentSeries κ)
    (B : Matrix (Fin (m + 1)) δ (LaurentSeries κ))
    (hq0 : q 0 ≠ 0)
    (hinjective : Function.Injective
      (augmentedProjectiveMatrix q B).mulVec) :
    LinearIndependent (LaurentSeries κ)
      (fun j ↦ dehomogenizedTangentColumn q (fun i ↦ B i j)) := by
  let e := zeroChartIndexEquiv (m := m)
  have hchart := linearIndependent_chartDehomogenizedTangentColumns
    (chart := (0 : Fin (m + 1))) q B hq0 hinjective
  let reindex : (ChartAffineIndex (Fin (m + 1)) 0 → LaurentSeries κ) →ₗ[
      LaurentSeries κ] (Fin m → LaurentSeries κ) := {
    toFun := fun f i ↦ f (e i)
    map_add' := by intro f g; ext i; rfl
    map_smul' := by intro a f; ext i; rfl }
  have hReindex : Function.Injective reindex := by
    intro f g h
    funext i
    have hi := congrFun h (e.symm i)
    simpa [reindex] using hi
  have hkernel : LinearMap.ker reindex = ⊥ :=
    LinearMap.ker_eq_bot.mpr hReindex
  have h := hchart.map' reindex hkernel
  change LinearIndependent (LaurentSeries κ)
    (fun j ↦ reindex (chartDehomogenizedTangentColumn 0 q
      (fun i ↦ B i j))) at h
  have hcomp :
      (fun j ↦ reindex (chartDehomogenizedTangentColumn 0 q
        (fun i ↦ B i j))) =
        (fun j ↦ dehomogenizedTangentColumn q (fun i ↦ B i j)) := by
    funext j
    funext i
    simp [reindex, e, zeroChartIndexEquiv,
      chartDehomogenizedTangentColumn, dehomogenizedTangentColumn]
  rw [hcomp] at h
  exact h

/-- Coefficientwise residue derivations preserve divisibility by a power of
the uniformizer. -/
theorem coefficientwiseDerivation_X_pow_mul
    (D : Derivation k κ κ) (a : ℕ) (f : PowerSeries κ) :
    coefficientwiseDerivation D
        ((PowerSeries.X : PowerSeries κ) ^ a * f) =
      (PowerSeries.X : PowerSeries κ) ^ a *
        coefficientwiseDerivation D f := by
  rw [Derivation.leibniz]
  have hpow : coefficientwiseDerivation D
      ((PowerSeries.X : PowerSeries κ) ^ a) = 0 := by
    induction a with
    | zero => simp [Derivation.map_one_eq_zero]
    | succ a ih =>
      rw [pow_succ, Derivation.leibniz, coefficientwiseDerivation_X, ih]
      simp
  rw [hpow]
  simp [smul_eq_mul]

/-- The finite-dimensional comparison needed to produce the actual affine
tangent inclusion from its geometric derivation vectors. -/
theorem tangentSpace_eq_dehomogenizedTangentSpan_of_actual_columns
    {m d : ℕ} (hm : 0 < m)
    (q : Fin (m + 1) → PowerSeries κ)
    (Z : Matrix (Fin (m + 1)) (Fin d) (PowerSeries κ))
    (tau : Fin (m + 1) → PowerSeries κ)
    (C : Matrix (FormalTangentColumn (Fin d))
      (Fin (m + 1)) (PowerSeries κ))
    (hCB : C * formalTangentMatrix q Z tau = 1)
    (hq0 : q 0 ≠ 0)
    (I : Ideal (MvPolynomial (Fin m) k))
    (hbase : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (LaurentSeries κ))
        (dehomogenizedPoint (laurentColumn q)) f = 0)
    (D : Fin d → Derivation k κ κ)
    (hZ : Z = coefficientwiseTangentMatrix q D)
    (lambda : Fin d → PowerSeries κ) (c : ℕ)
    (hfactor : ∀ i,
      PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i =
        (PowerSeries.X : PowerSeries κ) ^ c * tau i)
    (hbound : Module.finrank (LaurentSeries κ)
      (zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (MvPolynomial.map (algebraMap k (LaurentSeries κ))))) ≤ d + 1) :
    dehomogenizedTangentSpan (laurentColumn q)
        (laurentNonpositionTangentMatrix Z tau) =
      zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (MvPolynomial.map (algebraMap k (LaurentSeries κ)))) := by
  let L := LaurentSeries κ
  let qL := laurentColumn q
  let B := laurentNonpositionTangentMatrix Z tau
  let T : Submodule L (AffineTangentVector L m) :=
    zariskiTangentSpace (dehomogenizedPoint qL)
      (I.map (MvPolynomial.map (algebraMap k L)))
  let S : Submodule L (AffineTangentVector L m) :=
    dehomogenizedTangentSpan qL B
  have hZtan (j : Fin d) :
      dehomogenizedTangentColumn qL (fun i ↦ B i (Sum.inl j)) ∈ T := by
    have hj := coefficientwise_chartVector_mem_zariskiTangentSpace
      I q hq0 (D j) hbase
    have hcol : (fun i ↦ B i (Sum.inl j)) =
        laurentColumn (fun i ↦ coefficientwiseDerivation (D j) (q i)) := by
      funext i
      simp [B, laurentNonpositionTangentMatrix, hZ,
        coefficientwiseTangentMatrix, laurentColumn,
        LaurentSeries.coe_algebraMap]
    rw [hcol]
    exact hj
  have hUtan :
      dehomogenizedTangentColumn qL
        (laurentColumn fun i ↦ PowerSeries.derivative (R := κ) (q i)) ∈ T := by
    have h := uniformizer_chartVector_mem_zariskiTangentSpace
      (k := k) I q hq0 hbase
    exact h
  let phi : (Fin (m + 1) → L) →ₗ[L] (Fin m → L) := {
    toFun := fun w ↦ dehomogenizedTangentColumn qL w
    map_add' := by
      intro v w
      funext i
      simp [dehomogenizedTangentColumn, Pi.add_apply]
      ring
    map_smul' := by
      intro a w
      funext i
      simp [dehomogenizedTangentColumn, Pi.smul_apply, smul_eq_mul]
      ring }
  let qDeriv : Fin (m + 1) → L :=
    fun i ↦ algebraMap (PowerSeries κ) L (PowerSeries.derivative (R := κ) (q i))
  let tauL : Fin (m + 1) → L :=
    fun i ↦ algebraMap (PowerSeries κ) L (tau i)
  let lambdaL : Fin d → L :=
    fun j ↦ algebraMap (PowerSeries κ) L (lambda j)
  let zcol (j : Fin d) : Fin (m + 1) → L :=
    fun i ↦ algebraMap (PowerSeries κ) L (Z i j)
  let Xc : L := algebraMap (PowerSeries κ) L
    ((PowerSeries.X : PowerSeries κ) ^ c)
  have hmul (i : Fin (m + 1)) :
      algebraMap (PowerSeries κ) L (Z.mulVec lambda i) =
        ∑ j, lambdaL j * zcol j i := by
    simp [Matrix.mulVec, dotProduct, lambdaL, zcol, map_sum,
      map_mul, mul_comm]
  have hfactorL : qDeriv - (∑ j, lambdaL j • zcol j) = Xc • tauL := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    have hi := congrArg (algebraMap (PowerSeries κ) L) (hfactor i)
    calc
      qDeriv i - (∑ j, lambdaL j • zcol j i) =
          algebraMap (PowerSeries κ) L (PowerSeries.derivative (R := κ) (q i)) -
            algebraMap (PowerSeries κ) L (Z.mulVec lambda i) := by
        simp only [qDeriv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [hmul]
      _ = algebraMap (PowerSeries κ) L
          (PowerSeries.derivative (R := κ) (q i) - Z.mulVec lambda i) := by
        rw [map_sub]
      _ = Xc * tauL i := by
        rw [hfactor i, map_mul]
  have hsumtan : phi (∑ j, lambdaL j • zcol j) ∈ T := by
    rw [map_sum]
    apply T.sum_mem
    intro j hj
    have hcolumn : phi (zcol j) =
        dehomogenizedTangentColumn qL (fun i ↦ B i (Sum.inl j)) := by
      rfl
    rw [phi.map_smul, hcolumn]
    exact T.smul_mem _ (hZtan j)
  have hXtau : Xc • phi tauL ∈ T := by
    have hUtan' : phi qDeriv ∈ T := by
      change dehomogenizedTangentColumn (laurentColumn q)
        (laurentColumn (fun i ↦ PowerSeries.derivative (R := κ) (q i))) ∈ T
      exact hUtan
    have hdiff := T.sub_mem hUtan' hsumtan
    have hdiff' : phi (qDeriv - ∑ j, lambdaL j • zcol j) ∈ T := by
      simpa [phi.map_sub] using hdiff
    rw [hfactorL] at hdiff'
    simpa [phi.map_smul] using hdiff'
  have hXc : Xc ≠ 0 := by
    have hpow : PowerSeries.X ^ c ≠ 0 :=
      pow_ne_zero c (PowerSeries.X_ne_zero (R := κ))
    simpa [Xc, LaurentSeries.coe_algebraMap] using
      (HahnSeries.ofPowerSeries_injective (Γ := ℤ)).ne hpow
  have htau : phi tauL ∈ T := by
    have h := T.smul_mem Xc⁻¹ hXtau
    have hx : Xc⁻¹ * Xc = 1 := inv_mul_cancel₀ hXc
    simpa [smul_smul, hx] using h
  have hSleT : S ≤ T := by
    change dehomogenizedTangentSpan qL B ≤ T
    rw [dehomogenizedTangentSpan]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rcases j with j | j
    · simpa [B, laurentNonpositionTangentMatrix,
        LaurentSeries.coe_algebraMap] using hZtan j
    · change dehomogenizedTangentColumn qL
        (fun i ↦ B i (Sum.inr j)) ∈ T
      have hcol : (fun i ↦ B i (Sum.inr j)) = tauL := by
        funext i
        change (HahnSeries.ofPowerSeries ℤ κ (tau i)) =
          algebraMap (PowerSeries κ) L (tau i)
        rfl
      rw [hcol]
      change dehomogenizedTangentColumn qL tauL ∈ T at htau
      exact htau
  let CL : Matrix (FormalTangentColumn (Fin d))
      (Fin (m + 1)) L :=
    fun i j ↦ algebraMap (PowerSeries κ) L (C i j)
  let aug := augmentedProjectiveMatrix qL B
  have haug : aug = fun i j ↦
      algebraMap (PowerSeries κ) L (formalTangentMatrix q Z tau i j) := by
    ext i j
    rcases j with _ | j
    · rfl
    · rcases j with j | _
      · rfl
      · rfl
  have hleft : CL * aug = 1 := by
    apply Matrix.ext
    intro i j
    have h := congrArg (algebraMap (PowerSeries κ) L)
      (congrFun (congrFun hCB i) j)
    simp only [Matrix.mul_apply, map_sum, map_mul] at h
    change (∑ a, CL i a * aug a j) = (1 : Matrix _ _ L) i j
    rw [Matrix.one_apply]
    simpa [CL, haug, LaurentSeries.coe_algebraMap,
      Matrix.one_apply, map_one] using h
  have hinjective : Function.Injective aug.mulVec := by
    intro v w hvw
    have hmulv : CL.mulVec (aug.mulVec v) = v := by
      have h := congrArg (fun M : Matrix _ _ L ↦ M.mulVec v) hleft
      calc
        CL.mulVec (aug.mulVec v) = (CL * aug).mulVec v :=
          Matrix.mulVec_mulVec v CL aug
        _ = v := by simpa [Matrix.one_mulVec] using h
    have hmulw : CL.mulVec (aug.mulVec w) = w := by
      have h := congrArg (fun M : Matrix _ _ L ↦ M.mulVec w) hleft
      calc
        CL.mulVec (aug.mulVec w) = (CL * aug).mulVec w :=
          Matrix.mulVec_mulVec w CL aug
        _ = w := by simpa [Matrix.one_mulVec] using h
    calc
      v = CL.mulVec (aug.mulVec v) := hmulv.symm
      _ = CL.mulVec (aug.mulVec w) := congrArg CL.mulVec hvw
      _ = w := hmulw
  have hli := linearIndependent_dehomogenizedTangentColumns
    (κ := κ) (m := m) (δ := Fin d ⊕ Unit) hm qL B
      (by simpa [qL] using laurentColumn_ne_zero_of_ne_zero q hq0) hinjective
  have hdimS : Module.finrank L S = d + 1 := by
    change Module.finrank L
      (Submodule.span L (Set.range fun j : Fin d ⊕ Unit ↦
        dehomogenizedTangentColumn qL (fun i ↦ B i j))) = d + 1
    rw [finrank_span_eq_card hli]
    simp
  have hSle : Module.finrank L S ≤ Module.finrank L T :=
    Submodule.finrank_mono hSleT
  have hTle : Module.finrank L T ≤ Module.finrank L S := by
    simpa [T, S, hdimS] using hbound
  have hfin : Module.finrank L S = Module.finrank L T := Nat.le_antisymm hSle hTle
  have heq : S = T := Submodule.eq_of_le_of_finrank_eq hSleT hfin
  exact heq

/-! ## Equations at the actual retained generic point -/

/-- A component equation remains zero after any ring homomorphism from its
function field.  The retained Laurent lift specializes this lemma using the
explicit identity between affine component coordinates and the ratios of the
completed projective column. -/
theorem component_equation_eval₂_vanish_after_map
    {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {R : Type*} [CommSemiring R]
    (lift : ComponentFractionField P →+* R)
    {f : MvPolynomial (Fin m) k} (hf : f ∈ P.asIdeal) :
    MvPolynomial.eval₂
        (lift.comp (algebraMap k (ComponentFractionField P)))
        (lift ∘ componentCoordinate P) f = 0 := by
  have hgeneric : MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
      (componentCoordinate P) f = 0 := by
    rw [← componentAffineGenericPointMap_eq_eval₂]
    exact componentAffineGenericPointMap_eq_zero_of_mem P hf
  have hmap := MvPolynomial.eval₂_comp_left lift
    (algebraMap k (ComponentFractionField P)) (componentCoordinate P) f
  rw [hgeneric, map_zero] at hmap
  exact hmap.symm



/-- The normalized matrix constructed from actual residue derivations yields
an official one-row conormal datum.  Its tangent inclusion is proved from the
derivation vectors and the independent dimension bound; it is not an input.
The component prime `P` transfers conormality to the reduced ideal `I` at the
same generic point. -/
theorem exists_regularizedOneRowConormalData_of_actual_columns
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsRadical)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hP : P.asIdeal ∈ I.minimalPrimes)
    (q : Fin (m + 1) → PowerSeries κ)
    (Z : Matrix (Fin (m + 1)) (Fin (Module.finrank κ (Ω[κ⁄k])))
      (PowerSeries κ))
    (rows : Fin (Module.finrank κ (Ω[κ⁄k])) ↪ Fin (m + 1))
    (chart : Fin (m + 1))
    (a b : ℕ) (u₀ u₁ : PowerSeries κ)
    (D : Fin (Module.finrank κ (Ω[κ⁄k])) → Derivation k κ κ)
    (hZ : Z = coefficientwiseTangentMatrix q D)
    (hqchart : q chart = 1)
    (ha : 0 < a) (hab : a < b)
    (hqzero : q 0 = (PowerSeries.X : PowerSeries κ) ^ a * u₀)
    (hu₀ : PowerSeries.constantCoeff u₀ ≠ 0)
    (hqaxis : q (Fin.succ ⟨0, hm⟩) =
      (PowerSeries.X : PowerSeries κ) ^ b * u₁)
    (hminor : PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0)
    (hbaseP : ∀ f ∈ P.asIdeal,
      MvPolynomial.eval₂ (algebraMap k (LaurentSeries κ))
        (dehomogenizedPoint (laurentColumn q)) f = 0)
    (hbound : Module.finrank (LaurentSeries κ)
      (zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (P.asIdeal.map
          (MvPolynomial.map (algebraMap k (LaurentSeries κ))))) ≤
        Module.finrank κ (Ω[κ⁄k]) + 1)
    (hy : ∀ f,
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q))
        (MvPolynomial.map (algebraMap k (LaurentSeries κ)) f) = 0 ↔
          f ∈ P.asIdeal) :
    Nonempty (RegularizedOneRowConormalData (k := k) (K := κ) hm I q) := by
  classical
  let axis : Fin (m + 1) := Fin.succ ⟨0, hm⟩
  let d := Module.finrank κ (Ω[κ⁄k])
  let L := LaurentSeries κ
  let qL := laurentColumn q
  let y := dehomogenizedPoint qL
  let Iext := I.map (MvPolynomial.map (algebraMap k L))
  let Pext := P.asIdeal.map (MvPolynomial.map (algebraMap k L))
  have hu₀ne : u₀ ≠ 0 := by
    intro h
    apply hu₀
    simp [h]
  have hq0 : q 0 ≠ 0 := by
    rw [hqzero]
    exact mul_ne_zero (pow_ne_zero a (PowerSeries.X_ne_zero (R := κ))) hu₀ne
  have hZchart : ∀ j, Z chart j = 0 := by
    intro j
    rw [hZ, coefficientwiseTangentMatrix]
    simp [hqchart]
  have hZzero : ∀ j, ∃ w : PowerSeries κ,
      Z 0 j = (PowerSeries.X : PowerSeries κ) ^ a * w := by
    intro j
    refine ⟨coefficientwiseDerivation (D j) u₀, ?_⟩
    rw [hZ, coefficientwiseTangentMatrix, hqzero]
    exact coefficientwiseDerivation_X_pow_mul (D j) a u₀
  have hZaxis : ∀ j, ∃ w : PowerSeries κ,
      Z axis j = (PowerSeries.X : PowerSeries κ) ^ b * w := by
    intro j
    refine ⟨coefficientwiseDerivation (D j) u₁, ?_⟩
    rw [hZ, coefficientwiseTangentMatrix, hqaxis]
    exact coefficientwiseDerivation_X_pow_mul (D j) b u₁
  obtain ⟨lambda, c, tau, C, ell, hc, hfactor, _hprimitive, hCB,
      hrow, hresidue⟩ :=
    exists_formalDivisorAxisLift_with_derivative_relation
      q Z rows chart 0 axis a b u₀ u₁ hqchart hZchart ha hab
      hqzero hu₀ hZzero hqaxis hZaxis hminor
  have hbase : ∀ f ∈ P.asIdeal,
      MvPolynomial.eval₂ (algebraMap k L) y f = 0 := by
    intro f hf
    simpa [L, y, qL] using hbaseP f hf
  have htangentEq := tangentSpace_eq_dehomogenizedTangentSpan_of_actual_columns
    (κ := κ) hm q Z tau C hCB hq0 P.asIdeal hbase D hZ
      lambda c hfactor hbound
  have htangent :
      zariskiTangentSpace y Pext ≤
        dehomogenizedTangentSpan qL
          (laurentNonpositionTangentMatrix Z tau) :=
    by
      change zariskiTangentSpace y Pext ≤ _
      rw [← htangentEq]
  have hrowL :=
    laurentNonposition_rowMul_eq_zero_of_formalTangent_rowMul q ell Z tau hrow
  have hdot := laurentColumn_dot_eq_zero_of_formalTangent_rowMul
    q ell Z tau hrow
  have hq0L : qL 0 ≠ 0 := by
    exact laurentColumn_ne_zero_of_ne_zero q hq0
  have hconormalP :=
    coordinateCovector_mem_affineConormalSpace_of_zariski_le_span
      Pext qL (laurentColumn ell)
      (laurentNonpositionTangentMatrix Z tau) hq0L hdot hrowL htangent
  have hconormalI :=
    affineConormalSpace_map_minimalPrime_le I P.asIdeal hI hP y hy hconormalP
  have hground : groundLaurentMap (k := k) (K := κ) =
      algebraMap k L := by
    ext c
    rfl
  have hPker : Pext ≤ RingHom.ker (MvPolynomial.eval y) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.eval_map]
    exact hbaseP f hf
  have hIleP : Iext ≤ Pext := by
    exact Ideal.map_mono hP.1.2
  have hbaseI : Iext ≤ RingHom.ker (MvPolynomial.eval y) := hIleP.trans hPker
  have hresidueTail :
      residueColumn (fun i : Fin m ↦ ell i.succ) =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
    calc
      residueColumn (fun i : Fin m ↦ ell i.succ) =
          (fun i : Fin m ↦ residueColumn ell i.succ) := residueColumn_tail ell
      _ = (fun i : Fin m ↦ axisRow (k := κ) axis i.succ) := by
        rw [hresidue]
      _ = (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
        funext i
        by_cases hi : i = ⟨0, hm⟩
        · subst i
          simp [axis, axisRow]
        · have hne : i.succ ≠ Fin.succ ⟨0, hm⟩ := by
            intro h
            exact hi (Fin.succ_injective m h)
          change axisRow (Fin.succ ⟨0, hm⟩) i.succ = _
          rw [axisRow_apply_of_ne hne, if_neg hi]
  refine ⟨{
    ell := ell
    q_origin_ne := hq0
    projective_annihilation := hdot
    base_vanish := ?_
    conormal := hconormalI
    residue_axis := hresidueTail }⟩
  intro f hf
  exact RingHom.mem_ker.mp (hbaseI hf)

end

end Stafford38.Geometry.PaperActualDivisorTangent
