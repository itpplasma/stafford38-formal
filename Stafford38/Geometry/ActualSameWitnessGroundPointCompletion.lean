module
public import Stafford38.Geometry.ActualSameWitnessDivisorNumerator
public import Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
public import Stafford38.Geometry.GroundPointETCompatibility
public import Stafford38.Geometry.ActualOptionGroundPointCompletion
public import Stafford38.Geometry.ChartGenericPointFractionRing
public import Stafford38.Geometry.ProjectiveChartNormalizationFinite
public import Stafford38.Geometry.IntegralClosureCenterDVR
public import Stafford38.Geometry.ActualChartValuationImage
public import Stafford38.Geometry.RetainedGroundMapIdentification
public import Stafford38.Geometry.ComponentFunctionFieldBoundary
public import Stafford38.Geometry.UnitPowerCenterTransport

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option linter.style.haveILetI false
set_option pp.explicit false

noncomputable section

namespace Stafford38.Geometry.ActualSameWitnessGroundPointCompletion

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.ProjectiveChartNormalizationCenter
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.ActualOptionColumnBinding
open Stafford38.Geometry.ActualSameWitnessDivisorNumerator
open Stafford38.Geometry.RetainedGroundMapIdentification

universe u v w

def actualOptionMap {k : Type u} [CommSemiring k]
    {σ : Type v} {B : Type w} [CommSemiring B] [Algebra k B]
    (s : B) (rows : σ → B) : MvPolynomial (Option σ) k →ₐ[k] B :=
  MvPolynomial.aeval (fun j => Option.elim j s rows)

theorem actualOptionMap_none {k : Type u} [CommSemiring k]
    {σ : Type v} {B : Type w} [CommSemiring B] [Algebra k B]
    (s : B) (rows : σ → B) :
    actualOptionMap (k := k) s rows
      (MvPolynomial.X (none : Option σ) : MvPolynomial (Option σ) k) = s := by
  classical
  simp [actualOptionMap]

theorem actualOptionMap_some {k : Type u} [CommSemiring k]
    {σ : Type v} {B : Type w} [CommSemiring B] [Algebra k B]
    (s : B) (rows : σ → B) (z : σ) :
    actualOptionMap (k := k) s rows
      (MvPolynomial.X (some z : Option σ) : MvPolynomial (Option σ) k) = rows z := by
  classical
  simp [actualOptionMap]

/-- Exact output of the actual same-witness selected chart construction. This is a named
proposition so the dependent telescope is elaborated once and downstream callers can
refer to the canonical package without re-expanding its instance-heavy lets. -/
@[irreducible] def actualSameWitnessGroundPointOutput
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) : Prop :=
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
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  let hQV :=
    ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring hm P w
  let B := actualSelectedNormalization P w
  let coeff := actualSelectedNormalizationCoefficients P w
  letI : Algebra k B := coeff.toAlgebra
  let PB := actualSelectedNormalizationCenterPrime P w hQV
  ∃ (hBfinite : Algebra.FiniteType k B),
    letI : Algebra.FiniteType k B := hBfinite
    ∃ (t : Set κ) (htFinite : t.Finite),
    letI : Fintype t := htFinite.fintype
    ∃ (htBasis : IsTranscendenceBasis k ((↑) : t → κ))
      (index : t → Fin m), Function.Injective index ∧
      (∀ z : t, residue V
        (C.q ((chartAffineCoordinateEquiv C.chart) (index z)).1) = (z : κ)) ∧
      ∃ (hPB : PB.IsPrime),
        letI : PB.IsPrime := hPB
        ∃ (s : B) (hs0 : s ≠ 0) (hsPB : s ∈ PB)
          (u₀ u₁ : Localization.AtPrime PB)
          (hu₀ : IsUnit u₀) (hu₁ : IsUnit u₁)
          (hspan : Ideal.span {algebraMap B (Localization.AtPrime PB) s} =
            maximalIdeal (Localization.AtPrime PB))
          (hfactor₀ :
            algebraMap B (Localization.AtPrime PB)
                (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0) =
              (algebraMap B (Localization.AtPrime PB) s) ^
                w.differential.core.D.a * u₀)
          (hfactor₁ :
            algebraMap B (Localization.AtPrime PB)
                (actualNormalizedProjectiveColumnInIntegralClosure hm P w
                  (Fin.succ ⟨0, hm⟩)) =
              (algebraMap B (Localization.AtPrime PB) s) ^
                (w.differential.core.D.a + w.differential.core.D.e) * u₁),
          let rows := actualSelectedNormalizationRows P w index
          let fOption : MvPolynomial (Option t) k →ₐ[k] B :=
            actualOptionMap s rows
          ∃ (cert : ActualOptionEtaleCertificate k t B PB s rows fOption),
            ActualOptionGroundPointCompletion.GroundPointChartOutput
              PB fOption s
              (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0)
              (actualNormalizedProjectiveColumnInIntegralClosure hm P w
                (Fin.succ ⟨0, hm⟩))
              (actualSelectedNormalizationRows P w index)
              ((Fintype.equivFin t).symm)
              w.differential.core.D.a
              (w.differential.core.D.a + w.differential.core.D.e)

/-- One selected residue basis, one retained numerator, and the canonical
closed-ground-point completion chart built from that same option-coordinate
map. The output keeps the selected tuple and the numerator's order data, then
returns the existing ground-point theorem's full chart package. -/
theorem exists_actual_same_witness_groundpoint_chart
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
      actualSameWitnessGroundPointOutput hm P w := by
  classical
  unfold actualSameWitnessGroundPointOutput
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
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  let eChart := chartAffineCoordinateEquiv C.chart
  let Q : Subalgebra k F := actualSelectedChartAlgebra P w
  let hQV :=
    ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring hm P w
  let B := actualSelectedNormalization P w
  let coeff : k →+* B := actualSelectedNormalizationCoefficients P w
  letI : Algebra k B := coeff.toAlgebra
  letI : Algebra Q.toSubring F := Q.toSubring.subtype.toAlgebra
  have hchartPoint : componentProjectivePoint P C.chart ≠ 0 := by
    intro hz
    have hq := C.q_commonScale C.chart
    change (C.q C.chart : F) = C.scale * componentProjectivePoint P C.chart at hq
    have hq1 : (C.q C.chart : F) = 1 := congrArg Subtype.val C.chart_one
    rw [hz, mul_zero, hq1] at hq
    exact one_ne_zero hq
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
  letI : IsScalarTower k Q.toSubring F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hQfinite : Algebra.FiniteType k Q.toSubring := by
    change Algebra.FiniteType k Q
    exact chartGenericPointSubalgebra_finiteType P C.chart eChart
  letI : Algebra.FiniteType k Q.toSubring := hQfinite
  have hAlg :
      Algebra.compHom B (algebraMap k Q.toSubring) = coeff.toAlgebra := by
    apply Algebra.algebra_ext
    intro c
    rfl
  have hBfiniteComp :
      @Algebra.FiniteType k B _ _ (Algebra.compHom B (algebraMap k Q.toSubring)) := by
    letI : Algebra k B := Algebra.compHom B (algebraMap k Q.toSubring)
    letI : IsScalarTower k Q.toSubring B :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact ProjectiveChartNormalizationFinite.integralClosure_finiteType_over_base
      k Q.toSubring F
  have hfiniteEq := congrArg
    (fun A : Algebra k B => @Algebra.FiniteType k B _ _ A) hAlg
  have hBfinite : Algebra.FiniteType k B := hfiniteEq.mp hBfiniteComp
  refine ⟨hBfinite, ?_⟩
  letI : Algebra.FiniteType k B := hBfinite
  have hselected :=
    ActualSelectedResidueBasis.exists_actual_selected_residue_basis hm P w
  rcases hselected with ⟨t, htFinite, htBasis, index, hindex, hres⟩
  letI : Fintype t := htFinite.fintype
  have hparameterAt :=
    exists_actual_parameter_with_retained_orders hm P w t htFinite htBasis index hindex hres
  rcases hparameterAt with
    ⟨eCenter, s, den, u₀, u₁, hfield, hs0, hsPB, hmk, hspan,
      hu₀, hu₁, hfactor₀, hfactor₁⟩
  change actualSelectedNormalization P w at s
  let center := actualSelectedNormalizationCenter P w hQV
  let eB := ActualChartNormalizationCenter.subalgebraToSubringRingEquiv B
  let centerB := center.comap eB.toRingHom
  let PB := actualSelectedNormalizationCenterPrime P w hQV
  have hPB : PB.IsPrime := by
    have hc : center.IsPrime := integralClosureCenter_isPrime Q.toSubring U hQV
    letI : center.IsPrime := hc
    change (center.comap eB.toRingHom).IsPrime
    exact Ideal.IsPrime.comap eB.toRingHom
  letI : PB.IsPrime := hPB
  have hPB_eq : PB = centerB := rfl
  letI : centerB.IsPrime := hPB_eq ▸ hPB
  have hsPB' : s ∈ PB := by
    change s ∈ centerB
    exact hsPB
  have hspan' :
      Ideal.span {algebraMap B (Localization.AtPrime PB) s} =
        maximalIdeal (Localization.AtPrime PB) := by
    exact prime_span_eq_maximalIdeal_transport PB centerB hPB_eq s hspan
  let q₀ := actualNormalizedProjectiveColumnInIntegralClosure hm P w 0
  let q₁ := actualNormalizedProjectiveColumnInIntegralClosure hm P w
    (Fin.succ ⟨0, hm⟩)
  have hFactorTransport :
      ∃ u₀PB u₁PB : Localization.AtPrime PB,
        IsUnit u₀PB ∧ IsUnit u₁PB ∧
        algebraMap B (Localization.AtPrime PB) q₀ =
          (algebraMap B (Localization.AtPrime PB) s) ^ w.differential.core.D.a * u₀PB ∧
        algebraMap B (Localization.AtPrime PB) q₁ =
          (algebraMap B (Localization.AtPrime PB) s) ^
            (w.differential.core.D.a + w.differential.core.D.e) * u₁PB :=
    selected_center_retained_factors_at_canonical_prime PB centerB hPB_eq
      q₀ q₁ s w.differential.core.D.a w.differential.core.D.e
      u₀ u₁ hu₀ hu₁ hfactor₀ hfactor₁
  rcases hFactorTransport with
    ⟨u₀PB, u₁PB, hu₀PB, hu₁PB, hfactor₀', hfactor₁'⟩
  let rows : t → actualSelectedNormalization P w :=
    actualSelectedNormalizationRows P w index
  let fOption : MvPolynomial (Option t) k →ₐ[k] actualSelectedNormalization P w :=
    actualOptionMap s rows
  have hnone : fOption (MvPolynomial.X none) = s := by
    exact actualOptionMap_none s rows
  have hsome : ∀ z : t, fOption (MvPolynomial.X (some z)) = rows z := by
    intro z
    exact actualOptionMap_some s rows z
  have hPBDirect : (actualSelectedNormalizationCenterPrime P w hQV).IsPrime := by
    change PB.IsPrime
    exact hPB
  have certDirect :
      ActualOptionEtaleCertificate k t (actualSelectedNormalization P w)
        (actualSelectedNormalizationCenterPrime P w hQV) s rows fOption :=
    formallyEtale_at_selected_actual_normalization_center_core hm P w
      hQV t htFinite htBasis index hindex hres s hPBDirect hs0 hsPB' hspan'
      fOption hnone hsome
  have hEt := actualCertificate_formallyEtale_for_groundPointAdapter
    (actualSelectedNormalizationCenterPrime P w hQV) s rows fOption certDirect
  have hOrders : 0 < w.differential.core.D.a ∧
    w.differential.core.D.a <
      w.differential.core.D.a + w.differential.core.D.e := by
    have ha := w.differential.core.D.one_le_a
    have he := w.differential.core.D.one_le_e
    omega
  exact ⟨t, htFinite, htBasis, index, hindex, hres, hPB, s, hs0, hsPB',
    u₀PB, u₁PB, hu₀PB, hu₁PB, hspan', hfactor₀', hfactor₁',
    certDirect,
    ActualOptionGroundPointCompletion.exists_groundPoint_chart_from_option_map
      (actualSelectedNormalizationCenterPrime P w hQV) fOption s
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0)
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w (Fin.succ ⟨0, hm⟩))
      rows hnone hsPB' hsome ((Fintype.equivFin t).symm) hEt
      w.differential.core.D.a
      (w.differential.core.D.a + w.differential.core.D.e)
      hOrders u₀PB u₁PB hu₀PB hu₁PB hfactor₀' hfactor₁'⟩

end Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
