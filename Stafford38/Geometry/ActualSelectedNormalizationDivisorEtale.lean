import Stafford38.Geometry.ActualNormalizationDivisorEtale
import Stafford38.Geometry.ActualChartNormalizationCenter
import Stafford38.Geometry.ActualOptionColumnBinding
import Stafford38.Geometry.ActualChartResidueMapCoherence
import Stafford38.Geometry.ActualNormalizationCenterResidueKernel
import Stafford38.Geometry.FieldEquivFiniteType
import Stafford38.Geometry.SelectedResidueNormalizationLocalization
import Stafford38.Geometry.ResidueBasisLocalization
import Mathlib.Algebra.MvPolynomial.Rename

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.SelectedResidueCoefficientLocalization
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.ProjectiveChartNormalizationCenter
open Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis

universe u v w

structure ActualOptionEtaleCertificate
    (k : Type u) [Field k] (σ : Type v) (B : Type w)
    [CommRing B] [Algebra k B]
    (prime : Ideal B)
    (parameter : B) (rows : σ → B)
    (optionMap : MvPolynomial (Option σ) k →ₐ[k] B) : Prop where
  prime_isPrime : prime.IsPrime
  optionMap_none : optionMap (MvPolynomial.X none) = parameter
  optionMap_some : ∀ i : σ,
    optionMap (MvPolynomial.X (some i)) = rows i
  formallyEtale :
    letI : prime.IsPrime := prime_isPrime
    let actualMap : MvPolynomial (Option σ) k →ₐ[k] Localization.AtPrime prime :=
      (IsScalarTower.toAlgHom k B (Localization.AtPrime prime)).comp optionMap
    letI : Algebra (MvPolynomial (Option σ) k) (Localization.AtPrime prime) :=
      actualMap.toRingHom.toAlgebra
    Algebra.FormallyEtale (MvPolynomial (Option σ) k) (Localization.AtPrime prime)

private theorem span_atPrime_congr
    {k : Type u} [Field k] {B : Type w} [CommRing B] [Algebra k B]
    (P Q : Ideal B) [P.IsPrime] [Q.IsPrime] (h : P = Q) (s : B)
    (hs : Ideal.span {algebraMap B (Localization.AtPrime Q) s} =
      maximalIdeal (Localization.AtPrime Q)) :
    Ideal.span {algebraMap B (Localization.AtPrime P) s} =
      maximalIdeal (Localization.AtPrime P) := by
  cases h
  exact hs

private theorem formallyEtale_atPrime_congr
    {R : Type u} [CommRing R] {B : Type w} [CommRing B]
    (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P = Q) (f : R →+* B)
    (hf :
      letI : Algebra R (Localization.AtPrime P) :=
        ((algebraMap B (Localization.AtPrime P)).comp f).toAlgebra
      Algebra.FormallyEtale R (Localization.AtPrime P)) :
    letI : Algebra R (Localization.AtPrime Q) :=
      ((algebraMap B (Localization.AtPrime Q)).comp f).toAlgebra
    Algebra.FormallyEtale R (Localization.AtPrime Q) := by
  cases h
  exact hf

/-- The affine chart algebra selected by the retained witness. Its chart
coordinates use the same generic owner as arbitrary projective charts. -/
abbrev actualSelectedChartAlgebra
    {k : Type u} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
  Subalgebra k (ComponentFractionField P) :=
  chartGenericPointSubalgebra P w.column.chart
    (chartAffineCoordinateEquiv w.column.chart)

noncomputable def actualSelectedNormalization
    {k : Type u} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) := by
  let W := w.column.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let Q := actualSelectedChartAlgebra P w
  letI : Algebra Q.toSubring F := Q.toSubring.subtype.toAlgebra
  exact integralClosure Q.toSubring F

noncomputable def actualSelectedNormalizationCoefficients
    {k : Type u} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    k →+* actualSelectedNormalization P w := by
  let W := w.column.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let Q := actualSelectedChartAlgebra P w
  let B := actualSelectedNormalization P w
  letI : Algebra Q.toSubring (ComponentFractionField P) :=
    Q.toSubring.subtype.toAlgebra
  exact (chartSubalgebraToIntegralClosure Q).comp (algebraMap k Q)

noncomputable def actualSelectedNormalizationCenter
    {k : Type u} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hQV : let W := w.column.W
      let F := ComponentFractionField P
      letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
      (actualSelectedChartAlgebra P w).toSubring ≤ W.place.valuation.toSubring) :
    Ideal (actualSelectedNormalization P w).toSubring := by
  let W := w.column.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let Q := actualSelectedChartAlgebra P w
  exact integralClosureCenter Q.toSubring w.column.W.place.valuation hQV

noncomputable def actualSelectedNormalizationCenterPrime
    {k : Type u} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hQV : let W := w.column.W
      let F := ComponentFractionField P
      letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
      (actualSelectedChartAlgebra P w).toSubring ≤ W.place.valuation.toSubring) :
    Ideal (actualSelectedNormalization P w) := by
  let W := w.column.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let B := actualSelectedNormalization P w
  let eB := Stafford38.Geometry.ActualChartNormalizationCenter.subalgebraToSubringRingEquiv B
  exact (actualSelectedNormalizationCenter P w hQV).comap eB.toRingHom

noncomputable def actualSelectedNormalizationRows
    {k : Type u} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    {t : Type v} (index : t → Fin m) :
    t → actualSelectedNormalization P w :=
  fun z =>
    let W := w.column.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let qB := Stafford38.Geometry.ActualOptionColumnBinding.actualNormalizedProjectiveColumnInIntegralClosure
      hm P w
    qB (chartAffineCoordinateEquiv w.column.chart (index z)).1

/-- Formal etaleness of the actual option-coordinate map on the selected
normalization center. The selected residue basis and its chart-coordinate
representatives are fixed inputs, so the coefficient localization, center
height, and map are all built from the same retained witness data. The
divisor parameter is explicit; callers can feed the one numerator already
used in their order factorizations. -/
theorem formallyEtale_at_selected_actual_normalization_center_core
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
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    let B := actualSelectedNormalization P w
    let coeff := actualSelectedNormalizationCoefficients P w
    letI : Algebra k B := coeff.toAlgebra
    ∀ (hQV : (actualSelectedChartAlgebra P w).toSubring ≤ V),
    ∀ (t : Set κ), t.Finite →
    IsTranscendenceBasis k ((↑) : t → κ) →
    ∀ (index : t → Fin m), Function.Injective index →
    (∀ z : t, residue V
      (w.column.q ((chartAffineCoordinateEquiv w.column.chart) (index z)).1) = (z : κ)) →
    ∀ (s : B) (hP_B : (actualSelectedNormalizationCenterPrime P w hQV).IsPrime),
    s ≠ 0 → s ∈ actualSelectedNormalizationCenterPrime P w hQV →
    ∀ (hspan :
      letI : (actualSelectedNormalizationCenterPrime P w hQV).IsPrime := hP_B;
      Ideal.span {algebraMap B
        (Localization.AtPrime (actualSelectedNormalizationCenterPrime P w hQV)) s} =
          maximalIdeal (Localization.AtPrime (actualSelectedNormalizationCenterPrime P w hQV))),
    ∀ (fOption : MvPolynomial (Option t) k →ₐ[k] B),
    (fOption (MvPolynomial.X (none : Option t)) = s) →
    (∀ z : t, fOption (MvPolynomial.X (some z)) =
      actualSelectedNormalizationRows P w index z) →
    ActualOptionEtaleCertificate k t B
      (actualSelectedNormalizationCenterPrime P w hQV) s
      (actualSelectedNormalizationRows P w index) fOption := by
  intro C W F U V κ B coeff hQV t htFinite htBasis index hindex hres
    s hP_B hs0 hsP hspan fOption hnone hsomeRow
  classical
  letI : Fintype t := htFinite.fintype
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra k B := coeff.toAlgebra
  letI : IsScalarTower k V F := C.groundTower
  let retained : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  letI : Algebra k κ := retained
  have hretainedMap : @algebraMap k κ _ _ retained = (residue V).comp C.groundCoeff := by
    simpa [C, W, V, κ, C.groundCoeff_eq_retained] using w.retainedGroundMap
  letI : IsScalarTower k V κ := IsScalarTower.of_algebraMap_eq fun c => by
    have h := RingHom.congr_fun hretainedMap c
    change algebraMap k κ c = residue V (C.groundCoeff c)
    exact h
  let echart := chartAffineCoordinateEquiv C.chart
  let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart echart))
  have hground : ∀ c : k, (algebraMap k V c : F) = algebraMap k F c := by
    intro c
    exact DFunLike.congr_fun C.groundCoeff_commutes c
  let x : t → Q := fun z =>
    ⟨chartGenericPoint P C.chart echart (index z),
      Algebra.subset_adjoin (R := k) (A := F) (Set.mem_range_self (index z))⟩
  have hx : ∀ z : t,
      residue V ⟨(x z : F), hQV (x z).property⟩ = (z : κ) := by
    intro z
    have hnorm := chartGenericPoint_eq_normalized_lift
      (P := P) (V := V) C.chart echart C.q C.scale C.chart_one C.q_commonScale
    have hxV : (⟨(x z : F), hQV (x z).property⟩ : V) =
        C.q (echart (index z)).1 := by
      apply Subtype.ext
      change chartGenericPoint P C.chart echart (index z) =
        (C.q (echart (index z)).1 : F)
      exact congrFun hnorm (index z)
    rw [hxV]
    exact hres z
  have hchartPoint : componentProjectivePoint P C.chart ≠ 0 := by
    intro hz
    have hq := C.q_commonScale C.chart
    change (C.q C.chart : F) = C.scale * componentProjectivePoint P C.chart at hq
    have hq1 : (C.q C.chart : F) = 1 := congrArg Subtype.val C.chart_one
    rw [hz, mul_zero, hq1] at hq
    exact one_ne_zero hq
  have hBasisData :=
    Stafford38.Geometry.ActualChartRelativeDegree.same_witness_component_trdeg_one_from_basis
      hm P w t htFinite htBasis index hres
  let eA := Classical.choose hBasisData
  have hBasisData1 := Classical.choose_spec hBasisData
  let fA := Classical.choose hBasisData1
  have hBasisData2 := Classical.choose_spec hBasisData1
  let iA := Classical.choose hBasisData2
  have hBasisData3 := Classical.choose_spec hBasisData2
  let g := Classical.choose hBasisData3
  have hBasisData4 := Classical.choose_spec hBasisData3
  let fEV := Classical.choose hBasisData4
  have hBasisData5 := Classical.choose_spec hBasisData4
  let fEF := Classical.choose hBasisData5
  have hBasisProps := Classical.choose_spec hBasisData5
  have hg := hBasisProps.1
  have hgenA := hBasisProps.2.1
  have hfA := hBasisProps.2.2.1
  have hgvar := hBasisProps.2.2.2.1
  have hresE := hBasisProps.2.2.2.2.1
  have hfE := hBasisProps.2.2.2.2.2.1
  have hiA := hBasisProps.2.2.2.2.2.2.1
  have hgen := hBasisProps.2.2.2.2.2.2.2.1
  have htrdeg := hBasisProps.2.2.2.2.2.2.2.2
  letI : Algebra (FractionRing (MvPolynomial t k)) F := fEF.toRingHom.toAlgebra
  let P0 := MvPolynomial t k
  let E := FractionRing P0
  let R0 : Subalgebra k Q := Algebra.adjoin k (Set.range x)
  letI : Algebra Q.toSubring F := Q.toSubring.subtype.toAlgebra
  have hQfrac : IsFractionRing Q.toSubring F := by
    let hQ : IsFractionRing Q F :=
      chartGenericPointSubalgebra_isFractionRing P C.chart echart hchartPoint
    letI : IsFractionRing Q F := hQ
    letI : FaithfulSMul Q.toSubring F :=
      (faithfulSMul_iff_algebraMap_injective Q.toSubring F).mpr Subtype.val_injective
    apply IsFractionRing.of_field Q.toSubring F
    intro z
    obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective Q z
    let eqv := Stafford38.Geometry.ActualChartNormalizationCenter.subalgebraToSubringRingEquiv Q
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
    exact chartGenericPointSubalgebra_finiteType P C.chart echart
  letI : Algebra.FiniteType k Q.toSubring := hQfinite
  letI : Algebra Q.toSubring B := B.algebra
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
    let eqv := Stafford38.Geometry.ActualChartNormalizationCenter.subalgebraToSubringRingEquiv B
    refine ⟨eqv.symm a, eqv.symm b, ?_⟩
    change z = (eqv.symm a : F) / (eqv.symm b : F)
    calc
      z = (a : F) / (b : F) := hz.symm
      _ = (eqv.symm a : F) / (eqv.symm b : F) := by rfl
  letI : IsFractionRing B F := hBfrac
  letI : Algebra E κ := g.toRingHom.toAlgebra
  letI : IsScalarTower k E κ := IsScalarTower.of_algebraMap_eq fun c =>
    (g.commutes c).symm
  have hvars : IsTranscendenceBasis k
      (fun z : t => algebraMap E κ (algebraMap P0 E (MvPolynomial.X z))) := by
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
  let e := chartAffineCoordinateEquiv C.chart
  have hQV' : Q.toSubring ≤ V := hQV
  have hground' := hground
  have hLocData :=
    Stafford38.Geometry.SelectedResidueCoefficientLocalization.exists_chart_normalization_localization_map
      Q U hground' hQV' htBasis x hx
  choose j fB fLoc hjF hfBF hLoc0 hcomp using hLocData
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
  have hJMap (a : R0) : algebraMap R0 B a = j a := rfl
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
  letI : IsDomain L := hELdomain
  have hELgen' : ∀ p : P0,
      fEL (algebraMap P0 E p) = algebraMap B L (j (eA p)) := by
    intro p
    calc
      fEL (algebraMap P0 E p) = algebraMap B L (algebraMap R0 B (eA p)) := hELgen p
      _ = algebraMap B L (j (eA p)) := congrArg (algebraMap B L) (hJMap (eA p))
  have hEFgen : ∀ p : P0,
      fF (fEL (algebraMap P0 E p)) = fEF (algebraMap P0 E p) := by
    intro p
    calc
      fF (fEL (algebraMap P0 E p)) =
          fF (algebraMap B L (algebraMap R0 B (eA p))) := congrArg fF (hELgen p)
      _ = algebraMap B F (algebraMap R0 B (eA p)) := hFextend _
      _ = (j (eA p) : F) := congrArg (fun b : B => (b : F)) (hJMap (eA p))
      _ = (((eA p : R0) : Q) : F) := hjF (eA p)
      _ = fEF (algebraMap P0 E p) := (hgen p).symm
  have hCoherence :=
    Stafford38.Geometry.FieldEquivFiniteType.fractionField_map_coherence
      fEL fF fEF hEFgen
  have hEFmap := hCoherence.1
  have hEFLtower := hCoherence.2
  letI : IsScalarTower (FractionRing P0)
      (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R0))) F := hEFLtower
  let rhoL : L →+* κ := (residue V).comp fLoc
  let rhoB : B →+* κ := (residue V).comp fB
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
      _ = qV (x z) := by apply Subtype.ext; rfl
      _ = qV ((eA (MvPolynomial.X z) : R0) : Q) :=
        congrArg qV (hgenA z).symm
  have hRhoE : rhoL.comp fEL.toRingHom = g.toRingHom :=
    Stafford38.Geometry.ActualChartResidueMapCoherence.residue_map_coherence
      eA iA fEV fA g fEL (algebraMap B L) fLoc fB j (Subalgebra.val R0) qV
      (residue V) rhoL hELgen' hLoc0 rfl hcomp hAchart hfE
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
  let p : Ideal L := RingHom.ker rhoL
  have hpprime : p.IsPrime := RingHom.ker_isPrime _
  letI : p.IsPrime := hpprime
  have hpmax : p.IsMaximal := by
    change (RingHom.ker (rhoE : L →+* κ)).IsMaximal
    exact Stafford38.Geometry.ResidueBasisLocalization.ker_isMaximal_of_algebraic_residue
      (E := E) (A := L) (K := κ) rhoE
  letI : p.IsMaximal := hpmax
  have hLoc : rhoL.comp (algebraMap B L) = rhoB := by
    ext b
    change residue V (fLoc (algebraMap B L b)) = residue V (fB b)
    exact congrArg (residue V) (RingHom.congr_fun hLoc0 b)
  let eB := Stafford38.Geometry.ActualChartNormalizationCenter.subalgebraToSubringRingEquiv B
  let center := actualSelectedNormalizationCenter P w hQV
  let P_B := actualSelectedNormalizationCenterPrime P w hQV
  letI : P_B.IsPrime := hP_B
  have hcenterKernel : RingHom.ker rhoB = center.comap eB.toRingHom :=
    Stafford38.Geometry.ActualNormalizationCenterResidueKernel.residue_kernel_eq_canonical_center_comap
      Q.toSubring U hQV eB fB (by intro b; rfl) hfBF
  have hcontract : p.comap (algebraMap B L) = center.comap eB.toRingHom := by
    ext b
    change rhoL (algebraMap B L b) = 0 ↔ b ∈ center.comap eB.toRingHom
    have heq : rhoL (algebraMap B L b) = rhoB b := by
      simpa only [RingHom.comp_apply] using congrArg (fun q : B →+* κ => q b) hLoc
    rw [heq, ← hcenterKernel]
    exact (RingHom.mem_ker (f := rhoB)).symm
  have hcontractB : p.comap (algebraMap B L) = P_B := hcontract
  let f : P0 →ₐ[k] B := (IsScalarTower.toAlgHom k R0 B).comp eA.toAlgHom
  have hfMap (z : P0) : f z = algebraMap R0 B (eA z) := rfl
  have hELf (z : P0) :
      fEL (algebraMap P0 E z) = algebraMap B L (f z) := by
    calc
      fEL (algebraMap P0 E z) = algebraMap B L (j (eA z)) := hELgen' z
      _ = algebraMap B L (algebraMap R0 B (eA z)) :=
        congrArg (algebraMap B L) (hJMap (eA z)).symm
      _ = algebraMap B L (f z) :=
        congrArg (algebraMap B L) (hfMap z).symm
  have hcoeffL :
      (algebraMap E L).comp (algebraMap P0 E) =
        (algebraMap B L).comp f.toRingHom := by
    apply RingHom.ext
    intro z
    change fEL (algebraMap P0 E z) = algebraMap B L (f z)
    exact hELf z
  have hresVar (z : P0) : rhoB (f z) = g (algebraMap P0 E z) := by
    have h := congrArg (fun φ : E →+* κ => φ (algebraMap P0 E z)) hRhoE
    calc
      rhoB (f z) = rhoL (algebraMap B L (f z)) := by
        exact (RingHom.congr_fun hLoc (f z)).symm
      _ = rhoL (fEL (algebraMap P0 E z)) := by
        exact congrArg rhoL (hELf z).symm
      _ = g (algebraMap P0 E z) := h
  have hinjResid : Function.Injective (rhoB.comp f.toRingHom) := by
    intro a b hab
    apply IsFractionRing.injective P0 E
    apply hg
    calc
      g (algebraMap P0 E a) = rhoB (f a) := (hresVar a).symm
      _ = rhoB (f b) := hab
      _ = g (algebraMap P0 E b) := hresVar b
  have hheight : (p.comap (algebraMap B L)).height = 1 := by
    have hcenter :=
      Stafford38.Geometry.ActualChartNormalizationCenter.actual_chart_normalization_center_height_one_of_selected_basis
        hm P w t htFinite htBasis index hindex hres
    rw [hcontract]
    exact (RingEquiv.height_comap eB center).trans hcenter
  let qB := Stafford38.Geometry.ActualOptionColumnBinding.actualNormalizedProjectiveColumnInIntegralClosure
    hm P w
  obtain ⟨_hchartB, _hcoeB, hrowsB⟩ :=
    Stafford38.Geometry.ActualOptionColumnBinding.actualNormalizedProjectiveColumnInIntegralClosure_spec
      hm P w
  have hfF (z : t) : ((f (MvPolynomial.X z) : B) : F) =
      chartGenericPoint P C.chart echart (index z) := by
    change ((j (eA (MvPolynomial.X z)) : B) : F) = _
    rw [hjF]
    change ((eA (MvPolynomial.X z) : R0) : F) = _
    calc
      ((eA (MvPolynomial.X z) : R0) : F) = (x z : F) :=
        congrArg (fun a : Q => (a : F)) (hgenA z)
      _ = chartGenericPoint P C.chart echart (index z) := rfl
  have hrowTof (z : t) :
      actualSelectedNormalizationRows P w index z = f (MvPolynomial.X z) := by
    apply Subtype.ext
    change ((qB (echart (index z)).1 : B) : F) = _
    exact (hrowsB (index z)).trans (hfF z).symm
  have hsome : ∀ z : t,
      fOption (MvPolynomial.X (some z)) = f (MvPolynomial.X z) := by
    intro z
    rw [hsomeRow z, hrowTof z]
  letI : P_B.IsPrime := hP_B
  let actualMap : MvPolynomial (Option t) k →ₐ[k] Localization.AtPrime P_B :=
    (IsScalarTower.toAlgHom k B (Localization.AtPrime P_B)).comp fOption
  letI : Algebra (MvPolynomial (Option t) k)
      (Localization.AtPrime P_B) := actualMap.toRingHom.toAlgebra
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  letI : IsIntegrallyClosedIn B F := by
    change IsIntegrallyClosedIn (integralClosure Q.toSubring F) F
    infer_instance
  letI : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B F
  letI : (p.comap (algebraMap B L)).IsPrime := by
    rw [hcontract]
    exact hP_B
  have hsP' : s ∈ p.comap (algebraMap B L) := by
    rw [hcontract]
    exact hsP
  have hspan' :
      Ideal.span {algebraMap B
        (Localization.AtPrime (p.comap (algebraMap B L))) s} =
          maximalIdeal (Localization.AtPrime (p.comap (algebraMap B L))) := by
    exact span_atPrime_congr (k := k) (B := B)
      (p.comap (algebraMap B L)) P_B hcontractB s hspan
  have hEt := Stafford38.Geometry.ActualNormalizationDivisorEtale.formallyEtale_at_actual_normalization_center_of_specified_parameter
    p rhoL rhoB rfl hLoc f hinjResid hcoeffL hELfinite hheight s hs0 hsP' hspan'
    fOption hnone hsome
  exact {
    prime_isPrime := hP_B
    optionMap_none := hnone
    optionMap_some := hsomeRow
    formallyEtale := formallyEtale_atPrime_congr
      (P := p.comap (algebraMap B L)) (Q := P_B) hcontractB
      fOption.toRingHom hEt
  }

end Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
