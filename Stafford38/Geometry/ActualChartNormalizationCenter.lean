import Mathlib.RingTheory.SimpleRing.Principal
import Stafford38.Geometry.ActualChartRelativeDegree
import Stafford38.Geometry.ActualSelectedResidueBasis
import Stafford38.Geometry.ActualChartCenterNonzero
import Stafford38.Geometry.ActualChartCenterContraction
import Stafford38.Geometry.ActualChartCenterHeight
import Stafford38.Geometry.ActualResidueCenterHeight
import Stafford38.Geometry.ActualChartResidueMapCoherence
import Stafford38.Geometry.ActualNormalizationCenterResidueKernel
import Stafford38.Geometry.ProjectiveChartNormalizationCenter
import Stafford38.Geometry.ProjectiveChartNormalizationFinite
import Stafford38.Geometry.IntegralClosureCenterDVR
import Stafford38.Geometry.FiniteTypeCurveHeight
import Stafford38.Geometry.SelectedResidueNormalizationLocalization
import Stafford38.Geometry.FieldEquivFiniteType
import Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis
import Stafford38.Geometry.DVRUniformizerNumerator
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualChartNormalizationCenter

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ProjectiveChartNormalizationCenter
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.SameWitnessTranscendenceDegreeBound
open Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis

universe u

/-- The canonical ring equivalence from a subalgebra carrier to its underlying
subring of the ambient field. -/
def subalgebraToSubringRingEquiv
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (S : Subalgebra R K) : S ≃+* S.toSubring where
  toFun x := ⟨x.1, by simpa using x.2⟩
  invFun x := ⟨x.1, by simpa using x.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_mul' x y := by apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; rfl

/-- The same retained valuation has a height-one center after inverting any
specified finite residue-coordinate transcendence basis. The chosen basis and
coordinate representatives are inputs, so downstream constructions can use
the exact same data. No projective-scheme identification is asserted here. -/
theorem actual_chart_normalization_center_height_one_of_selected_basis
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let U := W.place.valuation
    let V := U.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    letI : Algebra k V := C.groundCoeff.toAlgebra
    let κ := ResidueField V
    let retained : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    letI : Algebra k κ := retained
    let e := chartAffineCoordinateEquiv C.chart
    let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
    let hQV : Q.toSubring ≤ V := by
      intro z hz
      have hz' : z ∈ Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e)) := by
        simpa [Q] using hz
      exact Stafford38.Geometry.ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring
        hm P w z hz'
    ∀ (t : Set κ), t.Finite →
      IsTranscendenceBasis k ((↑) : t → κ) →
      ∀ (index : t → Fin m), Function.Injective index →
        (∀ z : t, residue V (C.q (e (index z)).1) = (z : κ)) →
          (ProjectiveChartNormalizationCenter.integralClosureCenter Q.toSubring U hQV).height = 1 := by
  dsimp only
  classical
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let U := W.place.valuation
  let V := U.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V F := V.subtype.toAlgebra
  letI : IsScalarTower k V F := C.groundTower
  let κ := ResidueField V
  let retained : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  letI : Algebra k κ := retained
  have hretainedMap : @algebraMap k κ _ _ retained =
      (residue V).comp C.groundCoeff := by
    simpa [C, W, V, κ, C.groundCoeff_eq_retained] using w.retainedGroundMap
  letI : IsScalarTower k V κ := IsScalarTower.of_algebraMap_eq fun c => by
    have h := RingHom.congr_fun hretainedMap c
    change algebraMap k κ c = residue V (C.groundCoeff c)
    exact h
  intro t htFinite htBasis index hindex hres
  letI : Fintype t := htFinite.fintype
  let e := chartAffineCoordinateEquiv C.chart
  let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
  have hQV : Q.toSubring ≤ V := by
    intro z hz
    exact Stafford38.Geometry.ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring
      hm P w z hz
  have hground : ∀ c : k, (algebraMap k V c : F) = algebraMap k F c := by
    intro c
    exact DFunLike.congr_fun C.groundCoeff_commutes c
  let x : t → Q := fun z =>
    ⟨chartGenericPoint P C.chart e (index z),
      Algebra.subset_adjoin (R := k) (A := F) (Set.mem_range_self (index z))⟩
  have hx : ∀ z : t, residue V ⟨(x z : F), hQV (x z).property⟩ = (z : κ) := by
    intro z
    have hnorm := chartGenericPoint_eq_normalized_lift
      (P := P) (V := V) C.chart e C.q C.scale C.chart_one C.q_commonScale
    have hxV : (⟨(x z : F), hQV (x z).property⟩ : V) = C.q (e (index z)).1 := by
      apply Subtype.ext
      change chartGenericPoint P C.chart e (index z) = (C.q (e (index z)).1 : F)
      exact congrFun hnorm (index z)
    rw [hxV]
    exact hres z
  have hbound : Algebra.trdeg k F ≤ Algebra.trdeg k κ + 1 :=
    component_trdeg_le_residue_trdeg_add_one_of_witness hm P w
  obtain ⟨eA, fA, iA, g, fEV, fEF, hg, hgenA, hfA, hgvar,
      hresE, hfE, hiA, hgen, htrdeg⟩ :=
    Stafford38.Geometry.ActualChartRelativeDegree.same_witness_component_trdeg_one_from_basis
      hm P w t htFinite htBasis index hres
  let E := FractionRing (MvPolynomial t k)
  let P0 := MvPolynomial t k
  let R0 : Subalgebra k Q := Algebra.adjoin k (Set.range x)
  let B := integralClosure Q.toSubring F
  letI : Field E := FractionRing.field P0
  letI : Algebra E κ := g.toRingHom.toAlgebra
  letI : IsScalarTower k E κ := IsScalarTower.of_algebraMap_eq fun c =>
    (g.commutes c).symm
  have hvars : IsTranscendenceBasis k (fun z : t =>
      algebraMap E κ (algebraMap P0 E (MvPolynomial.X z))) := by
    change IsTranscendenceBasis k
      (fun z : t => g (algebraMap P0 E (MvPolynomial.X z)))
    have hfun : (fun z : t => g (algebraMap P0 E (MvPolynomial.X z))) =
        ((↑) : t → κ) := by
      funext z
      exact hgvar z
    rw [hfun]
    exact htBasis
  have hκalg : Algebra.IsAlgebraic E κ :=
    isAlgebraic_fractionRing_of_variable_images_isTranscendenceBasis hvars
  letI : Algebra E F := fEF.toRingHom.toAlgebra
  obtain ⟨j, fB, fLoc, hjF, hfBF, hLoc, hcomp⟩ :=
    Stafford38.Geometry.SelectedResidueCoefficientLocalization.exists_chart_normalization_localization_map
      Q U hground hQV htBasis x hx
  have hchartPoint : componentProjectivePoint P C.chart ≠ 0 := by
    intro hz
    have hq := C.q_commonScale C.chart
    change (C.q C.chart : F) = C.scale * componentProjectivePoint P C.chart at hq
    have hq1 : (C.q C.chart : F) = 1 := congrArg Subtype.val C.chart_one
    rw [hz, mul_zero, hq1] at hq
    exact one_ne_zero hq
  letI : Algebra Q.toSubring F := Q.toSubring.subtype.toAlgebra
  have hQfrac : IsFractionRing Q.toSubring F :=
    by
      let hQ : IsFractionRing Q F :=
        chartGenericPointSubalgebra_isFractionRing P C.chart e hchartPoint
      letI : IsFractionRing Q F := hQ
      letI : FaithfulSMul Q.toSubring F :=
        (faithfulSMul_iff_algebraMap_injective Q.toSubring F).mpr Subtype.val_injective
      apply IsFractionRing.of_field Q.toSubring F
      intro z
      obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective Q z
      let eqv := subalgebraToSubringRingEquiv Q
      refine ⟨eqv a, eqv b, ?_⟩
      change z = (eqv a : F) / (eqv b : F)
      calc
        z = (a : F) / (b : F) := hz.symm
        _ = (eqv a : F) / (eqv b : F) := by rfl
  letI : IsFractionRing Q.toSubring F := hQfrac
  letI : Algebra k Q.toSubring := Q.algebra
  letI : IsScalarTower k Q.toSubring F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hQfinite : Algebra.FiniteType k Q.toSubring := by
    change Algebra.FiniteType k Q
    exact chartGenericPointSubalgebra_finiteType P C.chart e
  letI : Algebra k B := Algebra.compHom B (algebraMap k Q.toSubring)
  letI : IsScalarTower k Q.toSubring B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hBfinite : Algebra.FiniteType k B :=
    Stafford38.Geometry.ProjectiveChartNormalizationFinite.integralClosure_finiteType_over_base
      k Q.toSubring F
  have hBfracSubring : IsFractionRing B.toSubring F :=
    Stafford38.Geometry.IntegralClosureCenterDVR.integralClosure_isFractionRing Q.toSubring
  letI : IsFractionRing B.toSubring F := hBfracSubring
  letI : FaithfulSMul B F :=
    (faithfulSMul_iff_algebraMap_injective B F).mpr Subtype.val_injective
  have hBfrac : IsFractionRing B F := by
    apply IsFractionRing.of_field B F
    intro z
    obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective B.toSubring z
    let e := subalgebraToSubringRingEquiv B
    refine ⟨e.symm a, e.symm b, ?_⟩
    change z = (e.symm a : F) / (e.symm b : F)
    calc
      z = (a : F) / (b : F) := hz.symm
      _ = (e.symm a : F) / (e.symm b : F) := by rfl
  letI : IsFractionRing B F := hBfrac
  letI : Algebra R0 B := j.toAlgebra
  let L := Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R0))
  letI : Algebra B L := inferInstance
  letI : SMul R0 F := (inferInstance : Algebra R0 F).toSMul
  letI : SMul B F := (inferInstance : Algebra B F).toSMul
  letI : SMul k R0 := (inferInstance : Algebra k R0).toSMul
  letI : SMul R0 B := (inferInstance : Algebra R0 B).toSMul
  letI : SMul k B := (inferInstance : Algebra k B).toSMul
  have hRF : algebraMap R0 F = (algebraMap B F).comp (algebraMap R0 B) := by
    ext a
    change (a : F) = (j a : F)
    exact (hjF a).symm
  letI : IsScalarTower R0 B F := IsScalarTower.of_algebraMap_eq' hRF
  have hJMap (a : R0) : algebraMap R0 B a = j a := by
    rfl
  have hKB : algebraMap k B = (algebraMap R0 B).comp (algebraMap k R0) := by
    ext c
    change (algebraMap k B c : F) =
      (algebraMap R0 B (algebraMap k R0 c) : F)
    change (algebraMap k B c : F) = (j (algebraMap k R0 c) : F)
    rw [hjF]
    rfl
  letI : IsScalarTower k R0 B := IsScalarTower.of_algebraMap_eq' hKB
  have hinj : Function.Injective (algebraMap R0 B) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.val_injective
    have hab' : j a = j b := by rw [← hJMap a, ← hJMap b]; exact hab
    calc
      ((a : Q) : F) = ((j a : B) : F) := (hjF a).symm
      _ = ((j b : B) : F) := congrArg (fun z : B => (z : F)) hab'
      _ = ((b : Q) : F) := hjF b
  obtain ⟨fEL, hELgen, hELfinite, hELdomain, hFdata⟩ :=
    Stafford38.Geometry.FieldEquivFiniteType.exists_finiteType_domain_fractionField_localization
      (k := k) (P := P0) (R := R0) (B := B) (F := F) eA hinj
  obtain ⟨fF, hFextend, hFfrac⟩ := hFdata
  letI : Algebra E L := fEL.toRingHom.toAlgebra
  letI : Algebra L F := fF.toAlgebra
  have hEFgen : ∀ p : P0,
      fF (fEL (algebraMap P0 E p)) = fEF (algebraMap P0 E p) := by
    intro p
    calc
      fF (fEL (algebraMap P0 E p)) =
          fF (algebraMap B L (algebraMap R0 B (eA p))) :=
        congrArg fF (hELgen p)
      _ = algebraMap B F (algebraMap R0 B (eA p)) := hFextend _
      _ = (j (eA p) : F) := by
        exact congrArg (fun b : B => (b : F)) (hJMap (eA p))
      _ = (((eA p : R0) : Q) : F) := hjF (eA p)
      _ = fEF (algebraMap P0 E p) := (hgen p).symm
  obtain ⟨hEFmap, hEFLtower⟩ :=
    Stafford38.Geometry.FieldEquivFiniteType.fractionField_map_coherence
      fEL fF fEF hEFgen
  letI : IsScalarTower E L F := hEFLtower
  let rhoL : L →+* κ := (residue V).comp fLoc
  let qV : Q →ₐ[k] V :=
    Stafford38.Geometry.SelectedResidueCoefficientLocalization.chartAlgebraToValuation
      Q U hground hQV
  have hAchart : fA.comp eA.toAlgHom =
      qV.comp ((Subalgebra.val R0).comp eA.toAlgHom) := by
    apply MvPolynomial.algHom_ext
    intro z
    change fA (eA (MvPolynomial.X z)) = qV ((eA (MvPolynomial.X z) : R0) : Q)
    calc
      fA (eA (MvPolynomial.X z)) =
          (⟨(x z : F), hQV (x z).property⟩ : V) := hfA z
      _ = qV (x z) := by
        apply Subtype.ext
        rfl
      _ = qV ((eA (MvPolynomial.X z) : R0) : Q) :=
        congrArg qV (hgenA z).symm
  have hELgen' : ∀ p : P0,
      fEL (algebraMap P0 E p) = algebraMap B L (j (eA p)) := by
    intro p
    calc
      fEL (algebraMap P0 E p) =
          algebraMap B L (algebraMap R0 B (eA p)) := hELgen p
      _ = algebraMap B L (j (eA p)) :=
        congrArg (algebraMap B L) (hJMap (eA p))
  have hRhoE : rhoL.comp fEL.toRingHom = g.toRingHom :=
    Stafford38.Geometry.ActualChartResidueMapCoherence.residue_map_coherence
      eA iA fEV fA g fEL (algebraMap B L) fLoc fB j (Subalgebra.val R0) qV
      (residue V) rhoL hELgen' hLoc rfl hcomp hAchart hfE
      (fun p => hiA p) hresE
  let rhoE : L →ₐ[E] κ := {
    toRingHom := rhoL
    commutes' := by
      intro z
      change rhoL (algebraMap E L z) = algebraMap E κ z
      change rhoL (fEL z) = g z
      exact RingHom.congr_fun hRhoE z
  }
  letI : Algebra.IsAlgebraic E κ := hκalg
  have hrestrict : rhoL.comp (algebraMap B L) =
      (residue V).comp fB := by
    ext b
    change residue V (fLoc (algebraMap B L b)) = residue V (fB b)
    exact congrArg (residue V) (RingHom.congr_fun hLoc b)
  let eB := subalgebraToSubringRingEquiv B
  let center := integralClosureCenter Q.toSubring U hQV
  have hcenterKernel : RingHom.ker ((residue V).comp fB) =
      center.comap eB.toRingHom := by
    exact Stafford38.Geometry.ActualNormalizationCenterResidueKernel.residue_kernel_eq_canonical_center_comap
      Q.toSubring U hQV eB fB (by intro b; rfl) hfBF
  have hcenter0 : center ≠ ⊥ :=
    Stafford38.Geometry.ActualChartCenterNonzero.actual_chart_normalization_center_ne_bot hm P w
  letI : IsDomain L := hELdomain
  letI : Algebra.FiniteType E L := hELfinite
  letI : IsFractionRing L F := hFfrac
  exact Stafford38.Geometry.ActualResidueCenterHeight.height_one_of_localized_algebraic_residue
    (E := E) (B := B) (A := L) (F := F) (κ := κ) (C := B.toSubring)
    (S := Algebra.algebraMapSubmonoid B (nonZeroDivisors R0))
    (rhoA := rhoL) (rhoE := rhoE) (hρ := rfl)
    (rhoB := (residue V).comp fB) hrestrict eB center hcenterKernel hcenter0 htrdeg

/-- The original entry point selects a residue basis once, then delegates to
the explicit-data theorem so other consumers can use the same selectors. -/
theorem actual_chart_normalization_center_height_one_of_basis
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let U := W.place.valuation
    let V := U.toSubring
    letI : Algebra k V := C.groundCoeff.toAlgebra
    let e := chartAffineCoordinateEquiv C.chart
    let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
    let hQV : Q.toSubring ≤ V := by
      intro z hz
      have hz' : z ∈ Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e)) := by
        simpa [Q] using hz
      exact Stafford38.Geometry.ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring
        hm P w z hz'
    (ProjectiveChartNormalizationCenter.integralClosureCenter Q.toSubring U hQV).height = 1 := by
  classical
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let U := W.place.valuation
  let V := U.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  let κ := ResidueField V
  let retained : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  letI : Algebra k κ := retained
  have hretainedMap : @algebraMap k κ _ _ retained =
      (residue V).comp C.groundCoeff := by
    simpa [C, W, V, κ, C.groundCoeff_eq_retained] using w.retainedGroundMap
  letI : IsScalarTower k V κ := IsScalarTower.of_algebraMap_eq fun c => by
    have h := RingHom.congr_fun hretainedMap c
    change algebraMap k κ c = residue V (C.groundCoeff c)
    exact h
  obtain ⟨t, htFinite, htBasis, index, hindex, hres⟩ :=
    Stafford38.Geometry.ActualSelectedResidueBasis.exists_actual_selected_residue_basis
      hm P w
  exact actual_chart_normalization_center_height_one_of_selected_basis
    hm P w t htFinite htBasis index hindex hres

end Stafford38.Geometry.ActualChartNormalizationCenter
