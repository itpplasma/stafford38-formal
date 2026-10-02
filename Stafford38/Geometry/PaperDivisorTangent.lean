import Stafford38.Geometry.GeneralTangentLimitCriterion
import Stafford38.Geometry.FormalDivisorTangent
import Stafford38.Geometry.FormalDivisorAxisLift
import Mathlib.LinearAlgebra.Projection

/-!
# The manuscript's explicit divisor-tangent route

The selected minor produces the correction and primitive normalization.
The order gap forces the distinguished residue row to vanish. The resulting
matrix has a left inverse, and the tangent-limit theorem produces the axis.
The geometric generic-span dictionary is an explicit premise: this file does
not assume that an arbitrary local parametrization supplies it automatically.
-/

namespace Stafford38.Geometry.PaperDivisorTangent

set_option autoImplicit false

open Stafford38.GeometrySplitTangentMatrix
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryResidueMinorSelection
open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.GeneralTangentLatticePresentation
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.ConormalScalarExtensionVanishing
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.SmoothConormalFibreVanishing
open Stafford38.Characteristic
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.ProjectiveTangentInclusion
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.GeometryPowerSeriesTangentLimit
open Stafford38.GeometryRetractionSpecialization

noncomputable section
variable {k : Type*} [Field k] [CharZero k]

omit [CharZero k] in
/-- The paper's order gap makes the corrected normalized transverse tangent
vanish in the axis row. This is derived, not assumed as an output condition. -/
lemma normalized_axis_constantCoeff_eq_zero
    {ι κ : Type*} [Fintype κ]
    (q : ι → PowerSeries k) (Z : Matrix ι κ (PowerSeries k))
    (lambda : κ → PowerSeries k) (tau : ι → PowerSeries k)
    (axis : ι) (b c : ℕ) (u : PowerSeries k)
    (hbc : c + 1 < b)
    (hq : q axis = (PowerSeries.X : PowerSeries k) ^ b * u)
    (hZ : ∀ j, ∃ w : PowerSeries k,
      Z axis j = (PowerSeries.X : PowerSeries k) ^ b * w)
    (hfactor : ∀ i, PowerSeries.derivative k (q i) - Z.mulVec lambda i =
      (PowerSeries.X : PowerSeries k) ^ c * tau i) :
    PowerSeries.constantCoeff (tau axis) = 0 := by
  have hd : PowerSeries.coeff c (PowerSeries.derivative k (q axis)) = 0 := by
    rw [PowerSeries.coeff_derivative, hq, PowerSeries.coeff_X_pow_mul']
    simp [Nat.not_le_of_gt hbc]
  have hz : PowerSeries.coeff c (Z.mulVec lambda axis) = 0 := by
    change PowerSeries.coeff c (∑ j, Z axis j * lambda j) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    obtain ⟨w, hw⟩ := hZ j
    rw [hw, mul_assoc, PowerSeries.coeff_X_pow_mul']
    simp [Nat.not_le_of_gt (by omega : c < b)]
  have he := congrArg (PowerSeries.coeff c) (hfactor axis)
  rw [map_sub, hd, hz, sub_zero] at he
  simpa [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_zero_eq_constantCoeff_apply]
    using he.symm

/-- The local derivative/minor construction yields a normalized matrix with
an actual splitting and zero residue axis. Its rank properties are conclusions.
This follows the paper's correction and common-power normalization in order. -/
theorem exists_normalized_split_axis_matrix
    {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (rows : κ ↪ Fin (n + 1)) (chart : Fin (n + 1))
    (axis : Fin n) (a b : ℕ) (u₀ u₁ : PowerSeries k)
    (hqchart : q chart = 1) (hZchart : ∀ j, Z chart j = 0)
    (ha : 0 < a) (hab : a < b)
    (hqzero : q 0 = (PowerSeries.X : PowerSeries k) ^ a * u₀)
    (hu₀ : PowerSeries.constantCoeff u₀ ≠ 0)
    (hqaxis : q axis.succ = (PowerSeries.X : PowerSeries k) ^ b * u₁)
    (hZzero : ∀ j, ∃ w : PowerSeries k,
      Z 0 j = (PowerSeries.X : PowerSeries k) ^ a * w)
    (hZaxis : ∀ j, ∃ w : PowerSeries k,
      Z axis.succ j = (PowerSeries.X : PowerSeries k) ^ b * w)
    (hminor : PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0) :
    ∃ (lambda : κ → PowerSeries k) (c : ℕ)
      (tau : Fin (n + 1) → PowerSeries k)
      (C : Matrix (FormalTangentColumn κ) (Fin (n + 1)) (PowerSeries k)),
      c ≤ a - 1 ∧
      (∀ i, PowerSeries.derivative k (q i) - Z.mulVec lambda i =
        (PowerSeries.X : PowerSeries k) ^ c * tau i) ∧
      C * formalTangentMatrix q Z tau = 1 ∧
      (∀ j, PowerSeries.constantCoeff (formalTangentMatrix q Z tau axis.succ j) = 0) := by
  obtain ⟨lambda, c, tau, C, _, _, _, _, _, hc, hfactor, _, _,
      haxiscolumns, hCB, _, _⟩ :=
    Stafford38.GeometryFormalDivisorAxisLift.exists_formalDivisorAxisLift
      q Z rows chart 0 axis.succ a b u₀ u₁ hqchart hZchart ha hab
        hqzero hu₀ hZzero hqaxis hZaxis hminor
  exact ⟨lambda, c, tau, C, hc, hfactor, hCB, haxiscolumns⟩

/-! ## The actual power-series tangent lattice -/

/-- The lattice generated by the columns of the normalized position/divisor/
transverse matrix. -/
def normalizedTangentLattice
    {n : ℕ} {κ : Type*} [Fintype κ]
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k) :
    Submodule (PowerSeries k) (Fin (n + 1) → PowerSeries k) :=
  LinearMap.range (formalTangentMatrix q Z tau).mulVecLin

omit [CharZero k] in
/-- A left inverse makes the actual column lattice a direct summand.  The
projector is the composite B C, whose idempotence follows from C B = 1. -/
lemma normalizedTangentLattice_isComplemented
    {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (C : Matrix (FormalTangentColumn κ) (Fin (n + 1)) (PowerSeries k))
    (hCB : C * formalTangentMatrix q Z tau = 1) :
    IsComplemented (normalizedTangentLattice q Z tau) := by
  let B := formalTangentMatrix q Z tau
  let E : (Fin (n + 1) → PowerSeries k) →ₗ[PowerSeries k]
      (Fin (n + 1) → PowerSeries k) := B.mulVecLin.comp C.mulVecLin
  have hCBlin : C.mulVecLin.comp B.mulVecLin = LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, hCB, Matrix.mulVecLin_one]
  have hEidem : IsIdempotentElem E := by
    change E.comp E = E
    dsimp [E]
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc C.mulVecLin B.mulVecLin]
    rw [hCBlin]
    simp
  have hproj : LinearMap.IsProj (LinearMap.range E) E :=
    (LinearMap.isProj_range_iff_isIdempotentElem E).mpr hEidem
  have hrange : LinearMap.range E = normalizedTangentLattice q Z tau := by
    apply le_antisymm
    · rintro x ⟨v, rfl⟩
      exact ⟨C.mulVecLin v, rfl⟩
    · rintro x ⟨v, rfl⟩
      refine ⟨B.mulVecLin v, ?_⟩
      change B.mulVecLin (C.mulVecLin (B.mulVecLin v)) =
        B.mulVecLin v
      have hfix : C.mulVecLin (B.mulVecLin v) = v := by
        have h := congrArg (fun f : (FormalTangentColumn κ → PowerSeries k) →ₗ[
            PowerSeries k] (FormalTangentColumn κ → PowerSeries k) => f v) hCBlin
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
      rw [hfix]
  exact ⟨LinearMap.ker E, by simpa [hrange] using hproj.isCompl⟩

omit [CharZero k] in
/-- The split tangent matrix has one independent column for each formal
tangent direction. -/
lemma normalizedTangentLattice_finrank
    {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (C : Matrix (FormalTangentColumn κ) (Fin (n + 1)) (PowerSeries k))
    (hCB : C * formalTangentMatrix q Z tau = 1) :
    Module.finrank (PowerSeries k)
        (normalizedTangentLattice q Z tau) = Fintype.card (FormalTangentColumn κ) := by
  have hCBlin : C.mulVecLin.comp (formalTangentMatrix q Z tau).mulVecLin =
      LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, hCB, Matrix.mulVecLin_one]
  have hinj : Function.Injective (formalTangentMatrix q Z tau).mulVecLin := by
    intro x y hxy
    have h := congrArg C.mulVecLin hxy
    have h' : (C.mulVecLin.comp (formalTangentMatrix q Z tau).mulVecLin) x =
        (C.mulVecLin.comp (formalTangentMatrix q Z tau).mulVecLin) y := by
      simpa only [LinearMap.comp_apply] using h
    rw [hCBlin] at h'
    simpa using h'
  rw [normalizedTangentLattice, LinearMap.finrank_range_of_inj hinj]
  simp

omit [CharZero k] in
/-- The order-gap conclusion controls every residue vector in the actual
column lattice, not merely the displayed generators. -/
lemma normalizedTangentLattice_residue_axis
    {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (axis : Fin n)
    (haxis : ∀ j,
      PowerSeries.constantCoeff
        (formalTangentMatrix q Z tau axis.succ j) = 0) :
    ∀ v : normalizedTangentLattice q Z tau,
      PowerSeries.constantCoeff ((v : Fin (n + 1) → PowerSeries k) axis.succ) = 0 := by
  intro v
  obtain ⟨c, hc⟩ := v.property
  rw [← hc]
  change PowerSeries.constantCoeff
      (∑ j, formalTangentMatrix q Z tau axis.succ j * c j) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [map_mul, haxis]
  simp

/-! ## A one-sided tangent-limit criterion -/

/-- From containment of the projective tangent cone in a column span, the
point belongs to that span and the affine Zariski tangent space is contained
in the dehomogenized column span. The reverse span containment is unnecessary
for the conormal argument. -/
theorem matrix_tangent_dictionary_of_projectiveCone_le_span
    {K : Type*} [Field K] {n : ℕ} {κ : Type*} [Fintype κ]
    (q : Fin (n + 1) → K) (hq0 : q 0 ≠ 0)
    (T : Submodule K (Fin n → K))
    (B : Matrix (Fin (n + 1)) κ K)
    (hspan : projectiveTangentCone q T ≤
      Submodule.span K (Set.range fun j => fun i => B i j)) :
    (∃ c : κ → K, ∀ i, q i = ∑ j, B i j * c j) ∧
      T ≤ dehomogenizedTangentSpan q B := by
  let d := dehomogenizedTangentLinearMap q
  let H := Submodule.span K (Set.range fun j => fun i => B i j)
  have hqcone : q ∈ projectiveTangentCone q T := by
    change dehomogenizedTangentColumn q q ∈ T
    convert T.zero_mem using 1
    ext i
    simp [dehomogenizedTangentColumn]
  have hqspan : q ∈ H := hspan hqcone
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hqspan
  have hposition : ∃ c : κ → K, ∀ i, q i = ∑ j, B i j * c j := by
    refine ⟨c, fun i => ?_⟩
    have hi := congrFun hc.symm i
    simpa [Finset.sum_apply, smul_eq_mul, mul_comm] using hi
  have hmap : H.map d = dehomogenizedTangentSpan q B := by
    rw [dehomogenizedTangentSpan, Submodule.map_span]
    congr 1
    ext v
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨w, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨fun i => B i j, ⟨j, rfl⟩, rfl⟩
  have hdsurj : Function.Surjective d := by
    intro v
    refine ⟨Fin.cases 0 (fun i => v i * q 0), ?_⟩
    ext i
    change (v i * q 0 * q 0 - q i.succ * 0) / q 0 ^ 2 = v i
    field_simp
    ring
  have htangent : T ≤ dehomogenizedTangentSpan q B := by
    intro v hv
    obtain ⟨w, hw⟩ := hdsurj v
    have hwcone : w ∈ projectiveTangentCone q T := by
      change d w ∈ T
      rw [hw]
      exact hv
    have hwH : w ∈ H := hspan hwcone
    have hdH : d w ∈ H.map d := ⟨w, hwH, rfl⟩
    rw [hmap] at hdH
    simpa [hw] using hdH
  exact ⟨hposition, htangent⟩

/-- If the point is in a column span and its affine tangent space is in the
dehomogenized column span, then the full projective tangent cone is in the
original column span. The only extra direction in the kernel of chart
dehomogenization is the radial point direction. -/
theorem projectiveTangentCone_le_span_of_position_and_tangent
    {K : Type*} [Field K] {n : ℕ} {κ : Type*}
    (q : Fin (n + 1) → K) (hq0 : q 0 ≠ 0)
    (T : Submodule K (Fin n → K))
    (B : Matrix (Fin (n + 1)) κ K)
    (hqspan : q ∈ Submodule.span K (Set.range fun j => fun i => B i j))
    (htangent : T ≤ dehomogenizedTangentSpan q B) :
    projectiveTangentCone q T ≤
      Submodule.span K (Set.range fun j => fun i => B i j) := by
  let d := dehomogenizedTangentLinearMap q
  let H := Submodule.span K (Set.range fun j => fun i => B i j)
  have hmap : H.map d = dehomogenizedTangentSpan q B := by
    rw [dehomogenizedTangentSpan, Submodule.map_span]
    congr 1
    ext v
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨w, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨fun i => B i j, ⟨j, rfl⟩, rfl⟩
  intro x hx
  have hdx : d x ∈ T := hx
  have hdxspan : d x ∈ H.map d := by
    rw [hmap]
    exact htangent hdx
  rcases hdxspan with ⟨y, hy, hdy⟩
  let c : K := (x 0 - y 0) / q 0
  have hkernel : x - y = c • q := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · dsimp [c]
      field_simp [hq0]
    · have hj := congrFun hdy.symm j
      change dehomogenizedTangentColumn q x j =
        dehomogenizedTangentColumn q y j at hj
      simp [dehomogenizedTangentColumn] at hj
      field_simp [hq0] at hj
      dsimp [c]
      field_simp [hq0]
      linear_combination hj
  have hxdecomp : x = y + c • q := by
    have := congrArg (fun v : Fin (n + 1) → K => v + y) hkernel
    simpa [add_comm] using this
  have hxinH : x ∈ H := by
    rw [hxdecomp]
    exact H.add_mem hy (H.smul_mem c hqspan)
  exact hxinH

/-- The radial point direction and an exact affine tangent span determine the
full projective tangent cone. The inclusion uses the existing radial-kernel
comparison; the reverse inclusion follows from the column tangent equations. -/
theorem projectiveTangentCone_eq_span_of_position_and_tangent
    {K : Type*} [Field K] {n : ℕ} {κ : Type*}
    (q : Fin (n + 1) → K) (hq0 : q 0 ≠ 0)
    (T : Submodule K (Fin n → K))
    (B : Matrix (Fin (n + 1)) κ K)
    (hqspan : q ∈ Submodule.span K (Set.range fun j => fun i => B i j))
    (htangent : T = dehomogenizedTangentSpan q B) :
    projectiveTangentCone q T =
      Submodule.span K (Set.range fun j => fun i => B i j) := by
  apply le_antisymm
  · exact projectiveTangentCone_le_span_of_position_and_tangent
      q hq0 T B hqspan htangent.le
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change dehomogenizedTangentColumn q (fun i => B i j) ∈ T
    rw [htangent]
    exact Submodule.subset_span ⟨j, rfl⟩


omit [CharZero k] in
/-- The nonposition divisor and transverse columns are among the columns of
the full normalized tangent matrix. -/
lemma dehomogenizedTangentSpan_nonposition_le_full
    {n : ℕ} {κ : Type*}
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k) :
    dehomogenizedTangentSpan (laurentColumn q)
        (laurentNonpositionTangentMatrix Z tau) ≤
      dehomogenizedTangentSpan (laurentColumn q)
        (fun i j ↦ algebraMap (PowerSeries k) (LaurentSeries k)
          (formalTangentMatrix q Z tau i j)) := by
  change Submodule.span (LaurentSeries k)
      (Set.range fun j => dehomogenizedTangentColumn (laurentColumn q)
        (fun i => laurentNonpositionTangentMatrix Z tau i j)) ≤
    Submodule.span (LaurentSeries k)
      (Set.range fun j => dehomogenizedTangentColumn (laurentColumn q)
        (fun i => algebraMap (PowerSeries k) (LaurentSeries k)
          (formalTangentMatrix q Z tau i j)))
  apply Submodule.span_mono
  rintro x ⟨j, rfl⟩
  refine ⟨Sum.inr j, ?_⟩
  ext i
  rcases j with j | j <;>
    simp [laurentNonpositionTangentMatrix, formalTangentMatrix]

/-- Low-level split-matrix input for the original tangent-limit conclusion,
with only the tangent-space containment needed to construct the conormal. -/
structure TangentInclusionInput {n dimY : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (B : Matrix (Fin (n + 1)) κ (PowerSeries k)) where
  axis : Fin n
  C : Matrix κ (Fin (n + 1)) (PowerSeries k)
  hprime : I.IsPrime
  hsplit : C * B = 1
  hrank : Fintype.card κ = dimY + 1
  hq0 : q 0 ≠ 0
  hbase : ∀ f ∈ I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin n)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0
  hsmooth : SmoothAffinePoint
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (dehomogenizedPoint (laurentColumn q))
  hposition : ∃ c : κ → LaurentSeries k, ∀ i,
      laurentColumn q i = ∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
        (B i j) * c j
  htangent : zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n))) ≤
      dehomogenizedTangentSpan (laurentColumn q)
        (fun i j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (B i j))
  haxis : ∀ j, PowerSeries.constantCoeff (B axis.succ j) = 0

/-- Paper-facing data for the weaker criterion. Unlike the existing exact
`DirectSummandInput`, this requires only that the actual projective tangent
cone lie in the generic fibre of the supplied lattice. -/
structure DirectSummandInclusionInput {n dimY : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (L : Submodule (PowerSeries k)
      (Fin (n + 1) → PowerSeries k)) where
  axis : Fin n
  isComplemented : IsComplemented L
  rank_eq : Module.finrank (PowerSeries k) L = dimY + 1
  hprime : I.IsPrime
  chart_nonzero : q 0 ≠ 0
  arc_mem_closure : FormalProjectiveArcInClosure I q
  generic_smooth : SmoothAffinePoint
    (I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin n)))
    (dehomogenizedPoint (laurentColumn q))
  genericTangentCone_le :
    projectiveTangentCone (laurentColumn q)
        (zariskiTangentSpace
          (dehomogenizedPoint (laurentColumn q))
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin n)))) ≤
      genericFibre (K := LaurentSeries k) L
  residue_le_coordinateHyperplane : ∀ v : L,
    PowerSeries.constantCoeff ((v : Fin (n + 1) → PowerSeries k) axis.succ) = 0

/-- The divisor-normalized matrix supplies every lattice-side field of the
paper-facing one-sided input. The projective tangent-cone containment remains
an explicit output of the geometric chart producer. -/
def directSummandInclusionInput_of_normalizedTangentMatrix
    {n dimY : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (axis : Fin n)
    (C : Matrix (FormalTangentColumn κ) (Fin (n + 1)) (PowerSeries k))
    (hchart : q 0 = 1)
    (hCB : C * formalTangentMatrix q Z tau = 1)
    (haxis : ∀ j,
      PowerSeries.constantCoeff
        (formalTangentMatrix q Z tau axis.succ j) = 0)
    (hcard : Fintype.card (FormalTangentColumn κ) = dimY + 1)
    (hprime : I.IsPrime)
    (harc : FormalProjectiveArcInClosure I q)
    (hsmooth : SmoothAffinePoint
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (dehomogenizedPoint (laurentColumn q)))
    (hcone : projectiveTangentCone (laurentColumn q)
        (zariskiTangentSpace
          (dehomogenizedPoint (laurentColumn q))
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin n)))) ≤
      genericFibre (K := LaurentSeries k)
        (normalizedTangentLattice q Z tau)) :
    DirectSummandInclusionInput (dimY := dimY) I q
      (normalizedTangentLattice q Z tau) := by
  refine ⟨axis,
    normalizedTangentLattice_isComplemented q Z tau C hCB,
    ?_, hprime, ?_, harc, hsmooth, hcone,
    normalizedTangentLattice_residue_axis q Z tau axis haxis⟩
  · exact (normalizedTangentLattice_finrank q Z tau C hCB).trans hcard
  · rw [hchart]
    exact one_ne_zero


/-- An affine tangent-space inclusion for the divisor/transverse columns
produces the projective cone inclusion required by the one-sided criterion.
The position column supplies q itself, so the radial kernel of chart
dehomogenization is already in the lattice. -/
def directSummandInclusionInput_of_normalizedTangentMatrix_of_affineTangentInclusion
    {n dimY : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (axis : Fin n)
    (C : Matrix (FormalTangentColumn κ) (Fin (n + 1)) (PowerSeries k))
    (hchart : q 0 = 1)
    (hCB : C * formalTangentMatrix q Z tau = 1)
    (haxis : ∀ j,
      PowerSeries.constantCoeff
        (formalTangentMatrix q Z tau axis.succ j) = 0)
    (hcard : Fintype.card (FormalTangentColumn κ) = dimY + 1)
    (hprime : I.IsPrime)
    (harc : FormalProjectiveArcInClosure I q)
    (hsmooth : SmoothAffinePoint
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (dehomogenizedPoint (laurentColumn q)))
    (htangent : zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n))) ≤
      dehomogenizedTangentSpan (laurentColumn q)
        (laurentNonpositionTangentMatrix Z tau)) :
    DirectSummandInclusionInput (dimY := dimY) I q
      (normalizedTangentLattice q Z tau) := by
  let B := formalTangentMatrix q Z tau
  let BL : Matrix (Fin (n + 1)) (FormalTangentColumn κ) (LaurentSeries k) :=
    fun i j => algebraMap (PowerSeries k) (LaurentSeries k) (B i j)
  have hspan : Submodule.span (PowerSeries k)
      (Set.range fun j => fun i => B i j) =
        normalizedTangentLattice q Z tau := by
    change Submodule.span (PowerSeries k)
        (Set.range fun j => fun i => B i j) = LinearMap.range B.mulVecLin
    exact (Matrix.range_mulVecLin B).symm
  have hgenericSpan :
      genericFibre (K := LaurentSeries k)
          (normalizedTangentLattice q Z tau) =
        Submodule.span (LaurentSeries k)
          (Set.range fun j => fun i => BL i j) :=
    genericFibre_eq_span_matrixColumns _ B hspan
  have hqspan : laurentColumn q ∈ Submodule.span (LaurentSeries k)
      (Set.range fun j => fun i => BL i j) := by
    apply Submodule.subset_span
    refine ⟨Sum.inl (), ?_⟩
    funext i
    simp [BL, laurentColumn, B, formalTangentMatrix]
  have htangentFull := htangent.trans
    (dehomogenizedTangentSpan_nonposition_le_full q Z tau)
  have hconeSpan := projectiveTangentCone_le_span_of_position_and_tangent
    (laurentColumn q) (laurentColumn_ne_zero_of_ne_zero q (by
      rw [hchart]
      exact one_ne_zero))
    (zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n))))
    BL hqspan htangentFull
  have hcone :
      projectiveTangentCone (laurentColumn q)
          (zariskiTangentSpace
            (dehomogenizedPoint (laurentColumn q))
            (I.map (scalarPolynomialMap
              (k := k) (K := LaurentSeries k) (Fin n)))) ≤
        genericFibre (K := LaurentSeries k)
          (normalizedTangentLattice q Z tau) := by
    rw [hgenericSpan]
    exact hconeSpan
  exact directSummandInclusionInput_of_normalizedTangentMatrix
    I q Z tau axis C hchart hCB haxis hcard hprime harc hsmooth hcone

omit [CharZero k] in
private lemma rowMul_zero_of_leftInverse_axis
    {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (C : Matrix κ (Fin (n + 1)) (PowerSeries k))
    (axis : Fin (n + 1))
    (hCB : C * B = 1)
    (haxis : ∀ j, PowerSeries.constantCoeff (B axis j) = 0) :
    ∃ ell : Fin (n + 1) → PowerSeries k,
      rowMul ell B = 0 ∧
        residueColumn ell = axisRow (k := k) axis := by
  classical
  let a₀ : Fin (n + 1) → k := axisRow (k := k) axis
  let a : Fin (n + 1) → PowerSeries k := constantColumn a₀
  have hres : residueColumn a = a₀ := residueColumn_constantColumn a₀
  have hred : rowMul a₀
      (fun i j ↦ PowerSeries.constantCoeff (B i j)) = 0 := by
    funext j
    simp [a₀, axisRow, rowMul, haxis j]
  let ell : Fin (n + 1) → PowerSeries k := annihilatorLift a B C
  have hell := powerSeries_annihilatorLift_spec a a₀ B C hCB hres hred
  refine ⟨ell, ?_, ?_⟩
  · exact hell.1
  · simpa [ell, a₀] using hell.2

omit [CharZero k] in
private lemma rowMul_laurent_of_rowMul
    {n : ℕ} {κ : Type*} [Fintype κ]
    (ell : Fin (n + 1) → PowerSeries k)
    (B : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (h : rowMul ell B = 0) :
    rowMul (laurentColumn ell)
      (fun i j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (B i j)) = 0 := by
  funext j
  have hj := congrFun h j
  simpa [rowMul, laurentColumn, map_sum] using
    congrArg (algebraMap (PowerSeries k) (LaurentSeries k)) hj

/-- One-sided version of the split-matrix conormal consumer. It retains the
same residue, smoothness, and closure conclusions; only the tangent-space
dictionary is weakened to the containment used in the covector argument. -/
theorem exists_axis_laurent_smooth_conormal_direction_of_tangentInclusion
    {n dimY : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    [IsAlgClosed k]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (B : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (D : TangentInclusionInput (dimY := dimY) I q B) :
    ∃ ell : Fin (n + 1) → PowerSeries k,
      rowMul ell B = 0 ∧
      residueColumn ell = axisRow (k := k) D.axis.succ ∧
      (let phase : PhaseVar n → LaurentSeries k :=
        Sum.elim (dehomogenizedPoint (laurentColumn q))
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (ell i.succ));
       phase ∈ smoothEquationConormalLocus I ∧
       residueColumn (fun i : Fin n ↦ ell i.succ) ∈
         extensionFibreClosure (k := k) (K := LaurentSeries k)
           (smoothEquationConormalLocus I) ∧
       Projectivization.mk k
           (fun i : Fin n => if i = D.axis then (1 : k) else 0)
           (by
             intro h
             have hh := congrFun h D.axis
             simp at hh) ∈
         projectiveHomogeneousClosure
           (projectivizedDirectionSet (smoothConormalDirectionSet I))) := by
  obtain ⟨ell, hrow, hres⟩ := rowMul_zero_of_leftInverse_axis
    B D.C D.axis.succ D.hsplit D.haxis
  have hrowL := rowMul_laurent_of_rowMul ell B hrow
  have hqL : ∑ i, laurentColumn ell i * laurentColumn q i = 0 := by
    obtain ⟨c, hc⟩ := D.hposition
    have hprod : ∑ i, laurentColumn ell i * laurentColumn q i =
        ∑ j, (∑ i, laurentColumn ell i *
          algebraMap (PowerSeries k) (LaurentSeries k) (B i j)) * c j := by
      calc
        ∑ i, laurentColumn ell i * laurentColumn q i =
            ∑ i, laurentColumn ell i *
              (∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
                (B i j) * c j) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [hc i]
        _ = ∑ i, ∑ j, laurentColumn ell i *
              (algebraMap (PowerSeries k) (LaurentSeries k) (B i j) * c j) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
        _ = ∑ j, ∑ i, laurentColumn ell i *
              (algebraMap (PowerSeries k) (LaurentSeries k) (B i j) * c j) :=
                Finset.sum_comm
        _ = ∑ j, (∑ i, laurentColumn ell i *
              algebraMap (PowerSeries k) (LaurentSeries k) (B i j)) * c j := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i hi
                ring
    rw [hprod]
    have hzero : ∀ j, (∑ i, laurentColumn ell i *
          algebraMap (PowerSeries k) (LaurentSeries k) (B i j)) = 0 := by
      intro j
      exact congrFun hrowL j
    change (∑ j, rowMul (laurentColumn ell)
      (fun i l ↦ algebraMap (PowerSeries k) (LaurentSeries k) (B i l)) j * c j) = 0
    rw [hrowL]
    simp
  have hphase :
      Sum.elim (dehomogenizedPoint (laurentColumn q))
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (ell i.succ)) ∈
        equationConormalLocus
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin n))) := by
    exact phasePoint_mem_equationConormalLocus_of_zariski_le_span
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (laurentColumn q) (laurentColumn ell)
      (fun i j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (B i j))
      (laurentColumn_ne_zero_of_ne_zero q D.hq0)
      hqL hrowL D.hbase D.htangent
  let phase : PhaseVar n → LaurentSeries k :=
    Sum.elim (dehomogenizedPoint (laurentColumn q))
      (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (ell i.succ))
  have hphaseSmooth : phase ∈ smoothEquationConormalLocus I :=
    ⟨hphase, D.hsmooth⟩
  have hclosure := residue_mem_extensionFibreClosure_of_laurent_generic
    (S := smoothEquationConormalLocus I)
    (dehomogenizedPoint (laurentColumn q))
    (fun i : Fin n ↦ ell i.succ) hphaseSmooth
  let axisVec : Fin n → k := fun i => if i = D.axis then 1 else 0
  have hresTail : residueColumn (fun i : Fin n ↦ ell i.succ) = axisVec := by
    funext i
    have hi := congrFun hres i.succ
    simpa [residueColumn, axisRow, axisVec] using hi
  have hvanAxis : axisVec ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I)) := by
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro P hP
    have hf : fibreLift P ∈
        MvPolynomial.vanishingIdeal k (equationConormalLocus I) :=
      fibreLift_mem_vanishingIdeal_equationConormal I D.hprime P hP
    have hPext : P ∈ extensionValuedVanishingIdeal
        (k := k) (K := LaurentSeries k)
        (fibreImage (smoothEquationConormalLocus I)) := by
      rw [mem_extensionValuedVanishingIdeal_iff]
      intro v hv
      rcases hv with ⟨z, hz, rfl⟩
      have hs := scalarExtension_vanishing I (fibreLift P) (by
        simpa [fibreLift, MvPolynomial.eval_rename, Function.comp_def] using hf)
        z hz.1
      have hsplit :
          Sum.elim (fun i ↦ z (Sum.inl i)) (fun i ↦ z (Sum.inr i)) = z := by
        funext i
        rcases i with i | i <;> rfl
      rw [← hsplit] at hs
      simpa [eval₂_fibreLift] using hs
    have hz := hclosure P hPext
    rw [hresTail] at hz
    simpa [MvPolynomial.aeval_eq_eval] using hz
  have hproj := mk_mem_projectiveHomogeneousClosure_of_fibre_zeroLocus
    I axisVec (by
      intro h
      have hh := congrFun h D.axis
      simp [axisVec] at hh) hvanAxis
  exact ⟨ell, hrow, hres,
    ⟨hphaseSmooth, hclosure, by simpa [axisVec] using hproj⟩⟩

/-- Paper-level tangent-limit criterion under the one-sided tangent-cone
containment. The split matrix presentation is built from the actual
complemented lattice, and its point/tangent dictionary is derived from that
containment. -/
theorem tangent_limit_criterion_of_directSummand_inclusion
    {n dimY : ℕ} [IsAlgClosed k]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (L : Submodule (PowerSeries k)
      (Fin (n + 1) → PowerSeries k))
    (D : DirectSummandInclusionInput (dimY := dimY) I q L) :
    Projectivization.mk k
        (fun i : Fin n => if i = D.axis then (1 : k) else 0)
        (by
          intro h
          have hh := congrFun h D.axis
          simp at hh) ∈
      projectiveHomogeneousClosure
        (projectivizedDirectionSet (smoothConormalDirectionSet I)) := by
  obtain ⟨P⟩ := exists_splitMatrixPresentation_of_isComplemented
    L D.isComplemented (dimY + 1) D.rank_eq
  let B : Matrix (Fin (n + 1)) (Fin (dimY + 1))
      (PowerSeries k) := P.B
  let BL : Matrix (Fin (n + 1)) (Fin (dimY + 1))
      (LaurentSeries k) :=
    fun i j => algebraMap (PowerSeries k) (LaurentSeries k) (B i j)
  have hgenericSpan :
      genericFibre (K := LaurentSeries k) L =
        Submodule.span (LaurentSeries k)
          (Set.range fun j => fun i => BL i j) :=
    genericFibre_eq_span_matrixColumns L B P.columnsSpan
  have hcone :
      projectiveTangentCone (laurentColumn q)
          (zariskiTangentSpace
            (dehomogenizedPoint (laurentColumn q))
            (I.map (scalarPolynomialMap
              (k := k) (K := LaurentSeries k) (Fin n)))) ≤
        Submodule.span (LaurentSeries k)
          (Set.range fun j => fun i => BL i j) := by
    rw [← hgenericSpan]
    exact D.genericTangentCone_le
  have hq0L : laurentColumn q 0 ≠ 0 :=
    laurentColumn_ne_zero_of_ne_zero q D.chart_nonzero
  obtain ⟨hposition, htangent⟩ :=
    matrix_tangent_dictionary_of_projectiveCone_le_span
      (laurentColumn q) hq0L
      (zariskiTangentSpace
        (dehomogenizedPoint (laurentColumn q))
        (I.map (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n))))
      BL hcone
  have hbase : ∀ f ∈ I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin n)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0 := by
    have hz := (projectiveClosureAtZero_iff
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (laurentColumn q) hq0L).mp D.arc_mem_closure.2
    exact hz
  have haxis : ∀ j,
      PowerSeries.constantCoeff (B D.axis.succ j) = 0 := by
    intro j
    have hmem : (fun i => B i j) ∈ L := by
      rw [← P.columnsSpan]
      exact Submodule.subset_span ⟨j, rfl⟩
    let v : L := ⟨fun i => B i j, hmem⟩
    simpa [v] using D.residue_le_coordinateHyperplane v
  let low : TangentInclusionInput (dimY := dimY) I q B := {
    axis := D.axis
    C := P.C
    hprime := D.hprime
    hsplit := P.leftInverse
    hrank := Fintype.card_fin (dimY + 1)
    hq0 := D.chart_nonzero
    hbase := hbase
    hsmooth := D.generic_smooth
    hposition := hposition
    htangent := htangent
    haxis := haxis }
  obtain ⟨ell, hrow, hres, hfinal⟩ :=
    exists_axis_laurent_smooth_conormal_direction_of_tangentInclusion
      I q B low
  exact hfinal.2.2

#print axioms normalized_axis_constantCoeff_eq_zero
#print axioms exists_normalized_split_axis_matrix
#print axioms normalizedTangentLattice_isComplemented
#print axioms normalizedTangentLattice_finrank
#print axioms normalizedTangentLattice_residue_axis
#print axioms matrix_tangent_dictionary_of_projectiveCone_le_span
#print axioms projectiveTangentCone_le_span_of_position_and_tangent
#print axioms dehomogenizedTangentSpan_nonposition_le_full
#print axioms exists_axis_laurent_smooth_conormal_direction_of_tangentInclusion
#print axioms tangent_limit_criterion_of_directSummand_inclusion
#print axioms directSummandInclusionInput_of_normalizedTangentMatrix
#print axioms directSummandInclusionInput_of_normalizedTangentMatrix_of_affineTangentInclusion

end
end Stafford38.Geometry.PaperDivisorTangent
