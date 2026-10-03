module
public import Stafford38.Geometry.CenterNumeratorFromHeight
public import Stafford38.Geometry.ActualOptionColumnBinding
public import Stafford38.Geometry.ActualChartNormalizationCenter
public import Stafford38.Geometry.LocalNormalizationCenterEquivalence
public import Stafford38.Geometry.IntegralClosureCenterDVR
public import Stafford38.Geometry.ProjectiveChartNormalizationFinite
public import Stafford38.Geometry.ActualSelectedResidueBasis
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualSameWitnessDivisorNumerator

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

universe u

/-- The output data for the actual same-witness construction. The nested lets
are retained here so the proposition names exactly the canonical chart,
normalization, and center used by the existing owners. -/
noncomputable def actualParameterOutput
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) : Prop := by
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
  let retained := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  letI : Algebra k κ := retained
  have hretainedMap : @algebraMap k κ _ _ retained =
      (residue V).comp C.groundCoeff := by
    simpa [C, W, V, κ, C.groundCoeff_eq_retained] using w.retainedGroundMap
  letI : IsScalarTower k V κ := by
    exact IsScalarTower.of_algebraMap_eq fun c => by
      have h := RingHom.congr_fun hretainedMap c
      change algebraMap k κ c = residue V (C.groundCoeff c)
      exact h
  let eChart := chartAffineCoordinateEquiv C.chart
  let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart eChart))
  let hQV : Q.toSubring ≤ V := by
    intro z hz
    exact Stafford38.Geometry.ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring
      hm P w z hz
  let B := integralClosure Q.toSubring F
  let S := B.toSubring
  let center := integralClosureCenter Q.toSubring U hQV
  let eB := ActualChartNormalizationCenter.subalgebraToSubringRingEquiv B
  let centerB := center.comap (eB : B →+* S)
  letI : center.IsPrime := integralClosureCenter_isPrime Q.toSubring U hQV
  letI : centerB.IsPrime := Ideal.IsPrime.comap (eB : B →+* S)
  exact ∀ (t : Set κ), t.Finite →
      IsTranscendenceBasis k ((↑) : t → κ) →
      ∀ (index : t → Fin m), Function.Injective index →
        (∀ z : t, IsLocalRing.residue V (C.q (eChart (index z)).1) = (z : κ)) →
          ∃ (e : Localization.AtPrime centerB ≃+* V) (s : B)
            (den : centerB.primeCompl) (u₀ u₁ : Localization.AtPrime centerB),
            (∀ b : B, ((e (algebraMap B _ b) : V) : F) = (b : F)) ∧
            s ≠ 0 ∧ s ∈ centerB ∧
            IsLocalization.mk' _ s den = e.symm
              (Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer V) ∧
            Ideal.span {algebraMap B (Localization.AtPrime centerB) s} =
              maximalIdeal (Localization.AtPrime centerB) ∧
            IsUnit u₀ ∧ IsUnit u₁ ∧
            algebraMap B (Localization.AtPrime centerB)
                (ActualOptionColumnBinding.actualNormalizedProjectiveColumnInIntegralClosure hm P w 0) =
              (algebraMap B _ s) ^ w.differential.core.D.a * u₀ ∧
            algebraMap B (Localization.AtPrime centerB)
                (ActualOptionColumnBinding.actualNormalizedProjectiveColumnInIntegralClosure hm P w
                  (Fin.succ ⟨0, hm⟩)) =
              (algebraMap B _ s) ^ (w.differential.core.D.a + w.differential.core.D.e) * u₁

/-- The actual selected residue basis determines one normalization-center
localization, one numerator, and both retained coordinate order
factorizations. -/
theorem exists_actual_parameter_with_retained_orders
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
  actualParameterOutput hm P w := by
  classical
  unfold actualParameterOutput
  intro _Cpre _Wpre _Fpre _valuationPre _Vpre _κpre _retainedAlgebraPre
    _retainedMapPre _eChartPre _Qpre _hQVpre _Bpre _Spre _centerPre _eBPre
    _centerBPre t htFinite htBasis index hindex hres
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
  let retained := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  letI : Algebra k κ := retained
  let eChart := chartAffineCoordinateEquiv C.chart
  let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart eChart))
  have hQV : Q.toSubring ≤ V := by
    intro z hz
    exact Stafford38.Geometry.ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring
      hm P w z hz
  let B := integralClosure Q.toSubring F
  let S := B.toSubring
  let center := integralClosureCenter Q.toSubring U hQV
  let eB := ActualChartNormalizationCenter.subalgebraToSubringRingEquiv B
  let centerB := center.comap (eB : B →+* S)
  letI : center.IsPrime := integralClosureCenter_isPrime Q.toSubring U hQV
  letI : centerB.IsPrime := Ideal.IsPrime.comap (eB : B →+* S)
  have hchartPoint : componentProjectivePoint P C.chart ≠ 0 := by
    intro hz
    have hq := C.q_commonScale C.chart
    change (C.q C.chart : F) = C.scale * componentProjectivePoint P C.chart at hq
    have hq1 : (C.q C.chart : F) = 1 := congrArg Subtype.val C.chart_one
    rw [hz, mul_zero, hq1] at hq
    exact one_ne_zero hq
  letI : Algebra Q.toSubring F := Q.toSubring.subtype.toAlgebra
  have hQfrac : IsFractionRing Q.toSubring F := by
    let hQ : IsFractionRing Q F :=
      chartGenericPointSubalgebra_isFractionRing P C.chart eChart hchartPoint
    letI : IsFractionRing Q F := hQ
    letI : FaithfulSMul Q.toSubring F :=
      (faithfulSMul_iff_algebraMap_injective Q.toSubring F).mpr Subtype.val_injective
    apply IsFractionRing.of_field Q.toSubring F
    intro z
    obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective Q z
    let eqv := ActualChartNormalizationCenter.subalgebraToSubringRingEquiv Q
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
    exact chartGenericPointSubalgebra_finiteType P C.chart eChart
  letI : Algebra k B := Algebra.compHom B (algebraMap k Q.toSubring)
  letI : IsScalarTower k Q.toSubring B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hBfinite : Algebra.FiniteType k B :=
    Stafford38.Geometry.ProjectiveChartNormalizationFinite.integralClosure_finiteType_over_base
      k Q.toSubring F
  letI : Algebra k S := ((eB : B →+* S).comp (algebraMap k B)).toAlgebra
  let eBAlg : B ≃ₐ[k] S := AlgEquiv.ofRingEquiv (f := eB) (by intro c; rfl)
  letI : Algebra.FiniteType k B := hBfinite
  letI : Algebra.FiniteType k S :=
    Algebra.FiniteType.of_surjective eBAlg.toAlgHom eBAlg.surjective
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : Algebra S F := S.subtype.toAlgebra
  letI : FaithfulSMul S F :=
    (faithfulSMul_iff_algebraMap_injective S F).mpr Subtype.val_injective
  letI : IsIntegrallyClosedIn S F := by
    change IsIntegrallyClosedIn (integralClosure Q.toSubring F).toSubring F
    infer_instance
  letI : IsIntegrallyClosed S := IsIntegrallyClosed.of_isIntegrallyClosedIn S F
  letI : IsFractionRing S F :=
    Stafford38.Geometry.IntegralClosureCenterDVR.integralClosure_isFractionRing Q.toSubring
  letI : IsFractionRing (integralClosure Q.toSubring F).toSubring F :=
    Stafford38.Geometry.IntegralClosureCenterDVR.integralClosure_isFractionRing Q.toSubring
  have hcenterPrime : center.IsPrime := integralClosureCenter_isPrime Q.toSubring U hQV
  have hheight := ActualChartNormalizationCenter.actual_chart_normalization_center_height_one_of_selected_basis
    hm P w t htFinite htBasis index hindex hres
  have hNoethCanonical : IsNoetherianRing (integralClosure Q.toSubring F).toSubring := by
    change IsNoetherianRing S
    infer_instance
  have hIntegrallyClosedCanonical :
      IsIntegrallyClosed (integralClosure Q.toSubring F).toSubring := by
    change IsIntegrallyClosed S
    infer_instance
  have hFractionRingCanonical :
      IsFractionRing (integralClosure Q.toSubring F).toSubring F :=
    Stafford38.Geometry.IntegralClosureCenterDVR.integralClosure_isFractionRing Q.toSubring
  obtain ⟨eC, heC⟩ :=
    @Stafford38.Geometry.LocalNormalizationCenterEquivalence.exists_localization_equiv_of_height_one
      F inferInstance Q.toSubring U hQV hNoethCanonical hIntegrallyClosedCanonical
      hFractionRingCanonical hcenterPrime hheight
  let qB : Fin (m + 1) → B :=
    ActualOptionColumnBinding.actualNormalizedProjectiveColumnInIntegralClosure hm P w
  obtain ⟨_hchart, hqB, _hrows⟩ :=
    ActualOptionColumnBinding.actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
  have hq0 : eC (algebraMap S (Localization.AtPrime center) (eB (qB 0))) = C.q 0 := by
    apply Subtype.ext
    change ((eC (algebraMap S (Localization.AtPrime center) (eB (qB 0))) : V) : F) =
      ((C.q 0 : V) : F)
    calc
      _ = (eB (qB 0) : F) := heC (eB (qB 0))
      _ = (qB 0 : F) := by rfl
      _ = (C.q 0 : F) := hqB 0
  have hq1 : eC (algebraMap S (Localization.AtPrime center)
      (eB (qB (Fin.succ ⟨0, hm⟩)))) = C.q (Fin.succ ⟨0, hm⟩) := by
    apply Subtype.ext
    change ((eC (algebraMap S (Localization.AtPrime center)
      (eB (qB (Fin.succ ⟨0, hm⟩)))) : V) : F) =
      ((C.q (Fin.succ ⟨0, hm⟩) : V) : F)
    calc
      _ = (eB (qB (Fin.succ ⟨0, hm⟩)) : F) := heC (eB (qB (Fin.succ ⟨0, hm⟩)))
      _ = (qB (Fin.succ ⟨0, hm⟩) : F) := by rfl
      _ = (C.q (Fin.succ ⟨0, hm⟩) : F) := hqB (Fin.succ ⟨0, hm⟩)
  obtain ⟨hQ0, hQ1⟩ := ActualOptionColumnBinding.retained_frame_coordinate_orders hm P w
  let D := w.differential.core.D
  let π := Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer V
  have hπ : Irreducible π :=
    Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer_irreducible V
  have h0 : eC (algebraMap S (Localization.AtPrime center) (eB (qB 0))) =
      π ^ D.a * D.u := by rw [hq0]; exact hQ0
  have h1 : eC (algebraMap S (Localization.AtPrime center)
      (eB (qB (Fin.succ ⟨0, hm⟩)))) =
      π ^ (D.a + D.e) * D.w := by rw [hq1]; exact hQ1
  have hu₀ : IsUnit D.u := D.u_unit
  have hu₁ : IsUnit D.w := w.differential.core.D_w_unit
  have hcore := exists_numerator_across_carrier_equiv
    (coB := algebraMap B F) (coS := S.subtype) (coV := V.subtype)
    eB center centerB rfl eC heC (by intro b; rfl)
    π hπ (qB 0) (qB (Fin.succ ⟨0, hm⟩)) D.a (D.a + D.e) D.u D.w
    h0 h1 hu₀ hu₁
  exact hcore

/-- The canonical selected residue basis and the actual retained-order
producer coexist over one witness. The latter is universal in the selected
basis inputs, so it can be instantiated at precisely the `t/index/hres` from
the former without making a second selection. -/
theorem selected_basis_and_parameter_output
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    (∃ (t : Set κ), t.Finite ∧
      IsTranscendenceBasis k ((↑) : t → κ) ∧
      ∃ (index : t → Fin m), Function.Injective index ∧
        ∀ z : t, residue V
          (C.q ((chartAffineCoordinateEquiv C.chart) (index z)).1) = (z : κ)) ∧
    actualParameterOutput hm P w := by
  constructor
  · exact ActualSelectedResidueBasis.exists_actual_selected_residue_basis hm P w
  · exact exists_actual_parameter_with_retained_orders hm P w

end Stafford38.Geometry.ActualSameWitnessDivisorNumerator
