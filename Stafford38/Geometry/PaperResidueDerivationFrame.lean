module
public import Stafford38.Geometry.KaehlerSpanSeparableAdjoin
public import Stafford38.Geometry.KaehlerVisibleDerivationFrame
public import Stafford38.Geometry.ResidueMinorSelection
public import Stafford38.Geometry.RetainedProjectiveCompletion
public import Stafford38.Geometry.RelativeRetainedBoundaryPlace
public import Stafford38.Geometry.CompletedDVRPowerSeriesEquiv
public import Stafford38.Geometry.CompletedDVRCoefficientSection

@[expose] public section

/-!
# Derivations visible in the retained residue coordinates

For a completed divisor chart, the residues of its projective coordinates
generate an intermediate field.  If the full residue field is algebraic over
that field, the existing Kähler-span theorem produces a dual derivation frame
on those same coordinates.  This module is the concrete interface between a
retained residue-coordinate family and the coefficientwise tangent columns.
-/

namespace Stafford38.Geometry.PaperResidueDerivationFrame

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.KaehlerSpanSeparableAdjoin
open Stafford38.Geometry.KaehlerVisibleDerivationFrame
open Stafford38.GeometryResidueMinorSelection
open Stafford38.GeometrySplitTangentMatrix
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.CompletedDVRCoefficientSection

noncomputable section

universe u v

variable {k κ : Type u} [Field k] [Field κ] [Algebra k κ] [CharZero k]

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

/-- The actual completed retained divisor chart has the expected residue
coordinates: its constant-coefficient map is the residue map of the retained
DVR. -/
theorem constantCoeff_retainedToCompleted_eq_residue
    {K : Type u} [Field K] [Algebra k K] {x : K}
    (W : Data k K x) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
      W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ v : V,
      PowerSeries.constantCoeff (retainedToCompletedPowerSeries W v) =
        residue V v := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
    W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let hsep := relativeResidue_isSeparable W.coefficientField W.place
  let ψ : PowerSeries (ResidueField V) →+* ResidueField V :=
    (completedResidue W.coefficientField V).toRingHom.comp
      W.completedPowerSeriesEquiv.toRingHom
  have hC (a : ResidueField V) : ψ (PowerSeries.C a) = a := by
    change (completedResidue W.coefficientField V)
      (W.completedPowerSeriesEquiv (PowerSeries.C a)) = a
    change (completedResidue W.coefficientField V)
      (completedDVRPowerSeriesMap W.coefficientField V hsep (PowerSeries.C a)) = a
    rw [completedDVRPowerSeriesMap_C]
    exact DFunLike.congr_fun
      (completedResidue_comp_completedCoefficientSection
        W.coefficientField V hsep) a
  have hres (v : V) :
      completedResidue W.coefficientField V
        (algebraMap V (AdicCompletion (maximalIdeal V) V) v) = residue V v := by
    simp [completedResidue, adicJetResidue]
  have hXcomp :
      completedDVRPowerSeriesMap W.coefficientField V hsep PowerSeries.X =
        algebraMap V (AdicCompletion (maximalIdeal V) V)
          (chosenUniformizer V) := by
    rw [completedDVRPowerSeriesMap_X, AdicCompletion.algebraMap_apply]
    rfl
  have hX : ψ PowerSeries.X = 0 := by
    change (completedResidue W.coefficientField V)
      (completedDVRPowerSeriesMap W.coefficientField V hsep PowerSeries.X) = 0
    rw [hXcomp, hres]
    apply (IsLocalRing.residue_eq_zero_iff (chosenUniformizer V)).mpr
    change chosenUniformizer V ∈ maximalIdeal V
    rw [maximalIdeal_eq_span_chosenUniformizer]
    exact Ideal.mem_span_singleton_self _
  have hψ : ψ = PowerSeries.constantCoeff := by
    apply RingHom.ext
    intro f
    have heq := congrArg ψ (PowerSeries.eq_shift_mul_X_add_const f)
    rw [map_add, map_mul, hX, mul_zero, zero_add, hC] at heq
    simpa [PowerSeries.constantCoeff] using heq
  rw [← hψ]
  dsimp only
  intro v
  change ψ (retainedToCompletedPowerSeries W v) = residue V v
  change (completedResidue W.coefficientField V)
    (W.completedPowerSeriesEquiv
      (W.completedPowerSeriesEquiv.symm
        (algebraMap V (AdicCompletion (maximalIdeal V) V) v))) = residue V v
  rw [W.completedPowerSeriesEquiv.apply_symm_apply]
  change adicJetResidue W.coefficientField V 0
    (Ideal.Quotient.mk ((maximalIdeal V) ^ 1) v) = residue V v
  simp [adicJetResidue]

/-- Residue coordinates of a finite completed projective column yield dual
derivations of the full residue field when that field is algebraic over the
subfield they generate. -/
theorem exists_visible_derivation_frame_of_residue_coordinates
    {ι : Type v} [Fintype ι] (qbar : ι → κ)
    (halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range qbar) : IntermediateField k κ)
      κ) :
    ∃ (rows : Fin (Module.finrank κ (Ω[κ⁄k])) ↪ ι)
      (D : Fin (Module.finrank κ (Ω[κ⁄k])) → Derivation k κ κ),
      ∀ i j, D j (qbar (rows i)) = if i = j then 1 else 0 := by
  let E : IntermediateField k κ := IntermediateField.adjoin k (Set.range qbar)
  letI : Algebra E κ := E.toSubalgebra.toAlgebra
  letI : IsScalarTower k E κ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.IsAlgebraic E κ := halg
  letI : Algebra.IsSeparable E κ := inferInstance
  let qE : ι → E := fun i =>
    ⟨qbar i, IntermediateField.subset_adjoin k (Set.range qbar) ⟨i, rfl⟩⟩
  have hgen : IntermediateField.adjoin k (Set.range qE) = ⊤ := by
    apply top_unique
    intro x _
    let T : IntermediateField k E := IntermediateField.adjoin k (Set.range qE)
    have hx : (x : κ) ∈ IntermediateField.adjoin k (Set.range qbar) := x.property
    have hT (y : κ) (hy : y ∈ IntermediateField.adjoin k (Set.range qbar)) :
        (⟨y, hy⟩ : E) ∈ T := by
      apply IntermediateField.adjoin_induction k
        (p := fun z hz => (⟨z, hz⟩ : E) ∈ T)
      · intro z hz
        change z ∈ Set.range qbar at hz
        obtain ⟨i, rfl⟩ := hz
        exact IntermediateField.subset_adjoin k (Set.range qE) ⟨i, rfl⟩
      · intro a
        exact T.algebraMap_mem a
      · intro a b _ _ ha hb
        exact T.add_mem ha hb
      · intro a _ ha
        exact T.inv_mem ha
      · intro a b _ _ ha hb
        exact T.mul_mem ha hb
    exact hT (x : κ) hx
  obtain ⟨rows, D, hD⟩ :=
    exists_visible_derivation_frame_of_finite_separable_adjoin
      (k := k) (E := E) (K := κ) qE hgen
  refine ⟨rows, D, ?_⟩
  intro i j
  simpa [qE] using hD i j

/-- The coefficientwise derivation columns of a completed projective arc
have a selected residue minor equal to one. -/
theorem exists_coefficientwise_residue_minor_eq_one
    {ι : Type v} [Fintype ι]
    (q : ι → PowerSeries κ)
    (halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun i => PowerSeries.constantCoeff (q i)) :
          IntermediateField k κ)
      κ) :
    ∃ (rows : Fin (Module.finrank κ (Ω[κ⁄k])) ↪ ι)
      (D : Fin (Module.finrank κ (Ω[κ⁄k])) → Derivation k κ κ),
      (∀ i j, D j (PowerSeries.constantCoeff (q (rows i))) =
        if i = j then 1 else 0) ∧
      PowerSeries.constantCoeff
        (selectedMinor (coefficientwiseTangentMatrix q D) rows).det = 1 := by
  obtain ⟨rows, D, hD⟩ :=
    exists_visible_derivation_frame_of_residue_coordinates
      (k := k) (κ := κ) (fun i => PowerSeries.constantCoeff (q i)) halg
  refine ⟨rows, D, hD, ?_⟩
  rw [constantCoeff_selectedMinor_det]
  have hmatrix :
      selectedMinor
          (residueMatrix (coefficientwiseTangentMatrix q D)) rows =
        (1 : Matrix (Fin (Module.finrank κ (Ω[κ⁄k])))
          (Fin (Module.finrank κ (Ω[κ⁄k]))) κ) := by
    ext i j
    simpa [selectedMinor, residueMatrix, Matrix.one_apply,
      constantCoeff_coefficientwiseTangentMatrix] using hD i j
  rw [hmatrix, Matrix.det_one]

/-- Applying the residue-coordinate frame to the actual retained completion
preserves the selected coefficientwise minor.  The hypotheses are the
residue-generation data supplied by the retained divisorial construction. -/
theorem exists_retained_coefficientwise_residue_minor_eq_one
    {K : Type u} [Field K] [Algebra k K] {x : K}
    (W : Data k K x) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
      W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ :=
      (((residue V).comp (relativeCoefficientMap W.coefficientField W.place)).comp
        (algebraMap k W.coefficientField)).toAlgebra
    ∀ {ι : Type v} [Fintype ι] (q : ι → V),
      Algebra.IsAlgebraic
        (IntermediateField.adjoin k
          (Set.range fun i => residue V (q i)) : IntermediateField k κ) κ →
      ∃ (rows : Fin (Module.finrank κ (Ω[κ⁄k])) ↪ ι)
        (D : Fin (Module.finrank κ (Ω[κ⁄k])) → Derivation k κ κ),
        (∀ i j, D j (residue V (q (rows i))) = if i = j then 1 else 0) ∧
        PowerSeries.constantCoeff
          (selectedMinor
            (coefficientwiseTangentMatrix
              (fun i => retainedToCompletedPowerSeries W (q i)) D) rows).det = 1 := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
    W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let κ := ResidueField V
  letI : Algebra k κ :=
    (((residue V).comp (relativeCoefficientMap W.coefficientField W.place)).comp
      (algebraMap k W.coefficientField)).toAlgebra
  dsimp only
  intro ι _ q halg
  let qhat : ι → PowerSeries κ :=
    fun i => retainedToCompletedPowerSeries W (q i)
  have hcoeff (i : ι) :
      PowerSeries.constantCoeff (qhat i) = residue V (q i) := by
    exact constantCoeff_retainedToCompleted_eq_residue W (q i)
  have hrange :
      Set.range (fun i => PowerSeries.constantCoeff (qhat i)) =
        Set.range (fun i => residue V (q i)) := by
    congr 1
    funext i
    exact hcoeff i
  have hgenerated :
      Algebra.IsAlgebraic
        (IntermediateField.adjoin k
          (Set.range fun i => PowerSeries.constantCoeff (qhat i)) :
            IntermediateField k κ) κ := by
    rw [hrange]
    exact halg
  obtain ⟨rows, D, hD, hminor⟩ :=
    exists_coefficientwise_residue_minor_eq_one
      (k := k) (κ := κ) qhat hgenerated
  refine ⟨rows, D, ?_, hminor⟩
  intro i j
  rw [← hcoeff (rows i)]
  exact hD i j

#print axioms exists_visible_derivation_frame_of_residue_coordinates
#print axioms exists_coefficientwise_residue_minor_eq_one
#print axioms constantCoeff_retainedToCompleted_eq_residue
#print axioms exists_retained_coefficientwise_residue_minor_eq_one

end

end Stafford38.Geometry.PaperResidueDerivationFrame
