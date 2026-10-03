module
public import Stafford38.Geometry.SameWitness.CoordinatePresentation
public import Stafford38.Geometry.SameWitness.AxisLiftFromGroundPoint
public import Stafford38.Geometry.SameWitness.ChartGroundMap
public import Stafford38.Geometry.A0NormalizedProjectiveCoordinates
public import Stafford38.Geometry.ActualOptionColumnBinding
public import Stafford38.Geometry.ActualCommonOpenColumnGlue
public import Stafford38.Geometry.ActualCommonOpenArcCompatibility
public import Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
public import Stafford38.Geometry.ActualSelectedNormalizationChartTransport
public import Stafford38.Geometry.ActualWitnessSelectedChartBinding
public import Stafford38.Geometry.ProjectiveChartSameFieldOverlap

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.ActualOptionGroundPointCompletion
open Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
open Stafford38.Geometry.ActualPointAxisLift
open Stafford38.Geometry.ActualOptionColumnBinding
open Stafford38.Geometry.ActualCommonOpenColumnGlue
open Stafford38.Geometry.ActualCommonOpenArcCompatibility
open Stafford38.Geometry.A0NormalizedProjectiveCoordinates
open Stafford38.Geometry.A0ChartFormalEtale
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.ActualSelectedNormalizationChartTransport
open Stafford38.Geometry.ActualWitnessSelectedChartBinding
open Stafford38.Geometry.ActualChartValuationImage
open Stafford38.Geometry.ProjectiveChartSameFieldOverlap
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

universe u

-- Retain the witness's valuation action only while elaborating its columns.
set_option quotPrecheck false in
local notation:max "retainedColumns" hm:arg P:arg w:arg =>
  (letI : Algebra
      (Stafford38.Geometry.AsymptoticDivisorExistence.CoordinateZeroLocalRing
        (w).column.W.coefficientField)
      (ComponentFractionField P) := (w).column.W.ambientAlgebra
   letI : IsLocalRing (w).column.W.place.valuation.toSubring :=
     (w).column.W.place.isDiscrete.toIsLocalRing
   actualNormalizedProjectiveColumnInIntegralClosure hm P w)

set_option quotPrecheck false in
local notation:max "retainedColumnValue" P:arg w:arg a:arg =>
  (letI : Algebra
      (Stafford38.Geometry.AsymptoticDivisorExistence.CoordinateZeroLocalRing
        (w).column.W.coefficientField)
      (ComponentFractionField P) := (w).column.W.ambientAlgebra
   (((w).column.q a : (w).column.W.place.valuation.toSubring) : ComponentFractionField P))

set_option quotPrecheck false in
local notation:max "retainedOrder" P:arg w:arg =>
  (letI : Algebra
      (Stafford38.Geometry.AsymptoticDivisorExistence.CoordinateZeroLocalRing
        (w).column.W.coefficientField)
      (ComponentFractionField P) := (w).column.W.ambientAlgebra
   letI : IsLocalRing (w).column.W.place.valuation.toSubring :=
     (w).column.W.place.isDiscrete.toIsLocalRing
   (w).differential.core.D.a)

set_option quotPrecheck false in
local notation:max "retainedGap" P:arg w:arg =>
  (letI : Algebra
      (Stafford38.Geometry.AsymptoticDivisorExistence.CoordinateZeroLocalRing
        (w).column.W.coefficientField)
      (ComponentFractionField P) := (w).column.W.ambientAlgebra
   letI : IsLocalRing (w).column.W.place.valuation.toSubring :=
     (w).column.W.place.isDiscrete.toIsLocalRing
   (w).differential.core.D.e)

/-- The factors of a tilted point-local arc remain nonzero after passage to
its common open (paper proof, common-open step). -/
def CommonOpenArcFactors
    {k A Q : Type u} [Field k] [CommRing A] [CommRing Q]
    [Algebra k A] [Algebra Q A] {d : ℕ}
    [Algebra (MvPolynomial (Option (Fin d)) k) A]
    [IsScalarTower k (MvPolynomial (Option (Fin d)) k) A]
    [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) A]
    (M : Ideal A) [M.IsMaximal]
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) (Localization.AtPrime M)]
    (f : Q) (e : Localization.Away f ≃ₐ[Q] Localization.Away (algebraMap Q A f))
    (g : Q) (eM : (A ⧸ M) ≃ₐ[k] k) (alpha : Fin d → k)
    (bad r q0 q1 : A) : Prop :=
  let ρA := originalToPointLocalFinSuccArcLaurentSeries
    (k := k) (d := d) (A := A) M eM alpha
  ∃ (hf : IsUnit (ρA (algebraMap Q A f)))
    (hg : IsUnit (ρA (algebraMap Q A g))),
    let hunitM : ∀ b, b ∉ M → IsUnit (ρA b) := fun b hb => by
      exact IsUnit.map
        (pointLocalFinSuccArcLaurentSeries (k := k) (d := d) (A := A) M eM alpha).toRingHom
        (IsLocalization.map_units (Localization.AtPrime M) (M := M.primeCompl) ⟨b, hb⟩)
    let ρU := genericArcToGenericOpenExtraAwayB M f e ρA hf hunitM g hg
    (ρU.comp (genericOpenExtraAwayBMap M f e g) = ρA) ∧
    ((ρU.comp (genericOpenExtraAwayBMap M f e g)).comp
      (algebraMap k A) = algebraMap k (LaurentSeries k)) ∧
    (ρU (genericOpenExtraAwayBMap M f e g
      bad) ≠ 0) ∧
    (ρU (genericOpenExtraAwayBMap M f e g r) ≠ 0) ∧
    (ρU (genericOpenExtraAwayBMap M f e g
      q0) ≠ 0) ∧
    (ρU (genericOpenExtraAwayBMap M f e g
      q1) ≠ 0)

/-- The tilted-product avoidance certificate yields the nonvanishing
common-open factors (paper proof, common-open step). -/
theorem commonOpenArcFactors_of_tiltedProduct
    {k A Q : Type u} [Field k] [CommRing A] [CommRing Q]
    [Algebra k A] [Algebra Q A] {d : ℕ}
    [Algebra (MvPolynomial (Option (Fin d)) k) A]
    [IsScalarTower k (MvPolynomial (Option (Fin d)) k) A]
    [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) A]
    (M : Ideal A) [M.IsMaximal]
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) (Localization.AtPrime M)]
    (f : Q) (e : Localization.Away f ≃ₐ[Q] Localization.Away (algebraMap Q A f))
    (g : Q) (eM : (A ⧸ M) ≃ₐ[k] k) (alpha : Fin d → k)
    (bad r q0 q1 : A)
    (hbad : bad = algebraMap Q A f * r)
    (hq0 : q0 = algebraMap Q A g)
    (havoid : tiltedArc (k := k) alpha
      (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
          (algebraMap A (Localization.AtPrime M) bad) *
       localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
          (algebraMap A (Localization.AtPrime M) q0) *
       localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
          (algebraMap A (Localization.AtPrime M) q1)) ≠ 0) :
    CommonOpenArcFactors M f e g eM alpha bad r q0 q1 := by
  exact commonOpen_factors_ne_zero_of_tiltedProduct
    M f e g eM alpha r bad q0 q1 hbad hq0 havoid


/-- A finite-type coefficient algebra is essentially of finite type over
any retained polynomial coordinate presentation. -/
theorem essFiniteType_of_coordinateMap
    {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] {d : ℕ}
    (f : MvPolynomial (Option (Fin d)) k →ₐ[k] B) :
    @Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) B
      _ _ f.toRingHom.toAlgebra := by
  letI : Algebra (MvPolynomial (Option (Fin d)) k) B := f.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial (Option (Fin d)) k) B :=
    IsScalarTower.of_algHom f
  exact Algebra.EssFiniteType.of_comp k (MvPolynomial (Option (Fin d)) k) B

/-- The maximal point, selected chart, and common-open maps built from one
retained ground-point axis lift (paper proof, common-open step). -/
structure CommonOpenPointData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup) where
  M : Ideal (actualSelectedNormalization P w)
  [hM : M.IsMaximal]
  eM :
    letI : Algebra k (actualSelectedNormalization P w) := coords.coeff.toAlgebra
    (actualSelectedNormalization P w ⧸ M) ≃ₐ[k] k
  hEtM :
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    letI : Algebra k (actualSelectedNormalization P w) := coords.coeff.toAlgebra
    letI : Algebra.FiniteType k (actualSelectedNormalization P w) := coords.hBfinite
    letI : Algebra R (actualSelectedNormalization P w) :=
      coords.fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R (actualSelectedNormalization P w) :=
      IsScalarTower.of_algHom coords.fFin
    letI : Algebra.EssFiniteType R (actualSelectedNormalization P w) :=
      Algebra.EssFiniteType.of_comp k R (actualSelectedNormalization P w)
    letI : Algebra R (Localization.AtPrime M) := inferInstance
    Algebra.FormallyEtale R (Localization.AtPrime M)
  fUnit : actualSelectedNormalization P w
  hfUnitM : fUnit ∉ M
  u0 : Localization.AtPrime M
  u1 : Localization.AtPrime M
  hu0 : IsUnit u0
  hu1 : IsUnit u1
  hq0M : algebraMap (actualSelectedNormalization P w) (Localization.AtPrime M)
      ((retainedColumns hm P w) 0) =
    (algebraMap (actualSelectedNormalization P w) (Localization.AtPrime M) coords.s) ^ (retainedOrder P w) * u0
  hq1M : algebraMap (actualSelectedNormalization P w) (Localization.AtPrime M)
      ((retainedColumns hm P w)
        (Fin.succ (⟨0, hm⟩ : Fin m))) =
    (algebraMap (actualSelectedNormalization P w) (Localization.AtPrime M) coords.s) ^
      ((retainedOrder P w) + (retainedGap P w)) * u1
  alpha : Fin (@Fintype.card coords.t coords.htFinite) → k
  havoid :
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    letI : Algebra k (actualSelectedNormalization P w) := coords.coeff.toAlgebra
    letI : Algebra.FiniteType k (actualSelectedNormalization P w) := coords.hBfinite
    letI : Algebra R (actualSelectedNormalization P w) :=
      coords.fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R (actualSelectedNormalization P w) :=
      IsScalarTower.of_algHom coords.fFin
    letI : Algebra.EssFiniteType R (actualSelectedNormalization P w) :=
      Algebra.EssFiniteType.of_comp k R (actualSelectedNormalization P w)
    letI : Algebra R (Localization.AtPrime M) := inferInstance
    letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
    tiltedArc (k := k) alpha
      (localToFinSuccPowerSeries (k := k)
          (B := actualSelectedNormalization P w)
          (d := @Fintype.card coords.t coords.htFinite) M eM
          (algebraMap (actualSelectedNormalization P w) (Localization.AtPrime M)
            (algebraMap _ (actualSelectedNormalization P w) setup.f *
              algebraMap _ (actualSelectedNormalization P w) setup.r)) *
       localToFinSuccPowerSeries (k := k)
          (B := actualSelectedNormalization P w)
          (d := @Fintype.card coords.t coords.htFinite) M eM
          (algebraMap (actualSelectedNormalization P w) (Localization.AtPrime M)
            ((retainedColumns hm P w) 0)) *
       localToFinSuccPowerSeries (k := k)
          (B := actualSelectedNormalization P w)
          (d := @Fintype.card coords.t coords.htFinite) M eM
          (algebraMap (actualSelectedNormalization P w) (Localization.AtPrime M)
            ((retainedColumns hm P w)
              (Fin.succ (⟨0, hm⟩ : Fin m))))) ≠ 0
  hdata :
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    letI : Algebra k (actualSelectedNormalization P w) := coords.coeff.toAlgebra
    letI : Algebra.FiniteType k (actualSelectedNormalization P w) := coords.hBfinite
    letI : Algebra R (actualSelectedNormalization P w) :=
      coords.fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R (actualSelectedNormalization P w) :=
      IsScalarTower.of_algHom coords.fFin
    letI : Algebra.EssFiniteType R (actualSelectedNormalization P w) :=
      Algebra.EssFiniteType.of_comp k R (actualSelectedNormalization P w)
    letI : Algebra R (Localization.AtPrime M) := inferInstance
    letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
    SelectedCoordinateAxisLiftData
      (fun a => localToFinSuccPowerSeries (k := k)
        (B := actualSelectedNormalization P w)
        (d := @Fintype.card coords.t coords.htFinite) M eM
        (algebraMap (actualSelectedNormalization P w) (Localization.AtPrime M)
          ((retainedColumns hm P w) a)))
      coords.rows (Fin.succ setup.j) 0 (⟨0, hm⟩ : Fin m).succ
      (retainedOrder P w)
      ((retainedOrder P w) + (retainedGap P w))
      (fun j => PrescribedAffineResidueCompletion.residueCoordinates
        M eM (some j)) alpha
      (localToFinSuccPowerSeries (k := k)
        (B := actualSelectedNormalization P w)
        (d := @Fintype.card coords.t coords.htFinite) M eM u0)
      (localToFinSuccPowerSeries (k := k)
        (B := actualSelectedNormalization P w)
        (d := @Fintype.card coords.t coords.htFinite) M eM u1)

/-- The selected quotient coordinates for the retained columns. -/
structure CommonOpenChartData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup) where
  hxj : componentCoordinate P setup.j ≠ 0
  hsel : SelectedAffineChartQuotient (k := k) P setup.j ≃ₐ[k]
      actualSelectedChartAlgebra P w
  qQ : Fin (m + 1) → actualSelectedChartAlgebra P w
  hqchartQ : qQ (Fin.succ setup.j) = 1
  hqQF : ∀ a, (qQ a : ComponentFractionField P) =
      retainedColumnValue P w a
  hq0 : qQ 0 = hsel (selectedAffineChartDenominator P setup.j)
  hqvars : ∀ i : Fin m, ∀ hij : i ≠ setup.j,
      qQ (Fin.succ i) =
        hsel (selectedAffineChartVariableClass P setup.j i hij)
  hqA : ∀ a, (retainedColumns hm P w) a =
      algebraMap _ (actualSelectedNormalization P w) (qQ a)

/-- The common-open maps and arc factors for the retained point and columns. -/
structure CommonOpenMapData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (point : CommonOpenPointData hm P w setup coords) [point.M.IsMaximal]
    (chart : CommonOpenChartData hm P w setup coords) where
  hqUPoint :
    let g := chart.hsel (selectedAffineChartDenominator P setup.j)
    let Cq := genericOpenRing point.M setup.f setup.e
    let U := genericOpenExtraAwayB point.M setup.f setup.e g
    let qU : Fin (m + 1) → U := fun a =>
      algebraMap Cq U (algebraMap _ Cq (chart.qQ a))
    let qT : Fin (m + 1) → Localization.AtPrime point.M := fun a =>
      algebraMap (actualSelectedNormalization P w) (Localization.AtPrime point.M)
        ((retainedColumns hm P w) a)
    ∀ a, qU a = pointLocalToCommonOpen
      (A := actualSelectedNormalization P w) point.M setup.f setup.e g (qT a)
  hchartU :
    let g := chart.hsel (selectedAffineChartDenominator P setup.j)
    let Cq := genericOpenRing point.M setup.f setup.e
    let U := genericOpenExtraAwayB point.M setup.f setup.e g
    let qU : Fin (m + 1) → U := fun a =>
      algebraMap Cq U (algebraMap _ Cq (chart.qQ a))
    let φ := originalAffineChartToCommonOpen P setup.j chart.hxj chart.hsel point.M setup.f setup.e
    ∀ i : Fin m, qU i.succ = qU 0 *
      φ (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i))
  hq0B : (retainedColumns hm P w) 0 =
      algebraMap _ (actualSelectedNormalization P w)
        (chart.hsel (selectedAffineChartDenominator P setup.j))
  hbaseMap :
    let g := chart.hsel (selectedAffineChartDenominator P setup.j)
    let Cq := genericOpenRing point.M setup.f setup.e
    let U := genericOpenExtraAwayB point.M setup.f setup.e g
    (genericOpenExtraAwayBMap point.M setup.f setup.e g).comp
      (algebraMap (actualSelectedChartAlgebra P w)
        (actualSelectedNormalization P w)) =
    (algebraMap Cq U).comp (algebraMap _ Cq)

/-- The common-open construction retains bounded certificates for each step. -/
structure CommonOpenArcCompatibility
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (point : CommonOpenPointData hm P w setup coords) [point.M.IsMaximal]
    (chart : CommonOpenChartData hm P w setup coords) where
  hfactor :
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    letI : Algebra k (actualSelectedNormalization P w) := coords.coeff.toAlgebra
    letI : Algebra.FiniteType k (actualSelectedNormalization P w) := coords.hBfinite
    letI : Algebra R (actualSelectedNormalization P w) :=
      coords.fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R (actualSelectedNormalization P w) :=
      IsScalarTower.of_algHom coords.fFin
    letI : Algebra.EssFiniteType R (actualSelectedNormalization P w) :=
      Algebra.EssFiniteType.of_comp k R (actualSelectedNormalization P w)
    letI : Algebra R (Localization.AtPrime point.M) := inferInstance
    letI : Algebra.FormallyEtale R (Localization.AtPrime point.M) := point.hEtM
    CommonOpenArcFactors (k := k) (d := @Fintype.card coords.t coords.htFinite)
      (A := actualSelectedNormalization P w) point.M setup.f setup.e
      (chart.hsel (selectedAffineChartDenominator P setup.j)) point.eM point.alpha
      (algebraMap (actualSelectedChartAlgebra P w) (actualSelectedNormalization P w) setup.f *
        algebraMap (actualSelectedChartAlgebra P w) (actualSelectedNormalization P w) setup.r)
      (algebraMap (actualSelectedChartAlgebra P w) (actualSelectedNormalization P w) setup.r)
      ((retainedColumns hm P w) 0)
      ((retainedColumns hm P w) (Fin.succ (⟨0, hm⟩ : Fin m)))

/-- The common open stores each independently elaborated mathematical certificate. -/
structure CommonOpenData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup) where
  point : CommonOpenPointData hm P w setup coords
  chart : CommonOpenChartData hm P w setup coords
  maps :
    letI : point.M.IsMaximal := point.hM
    CommonOpenMapData hm P w setup coords point chart
  arc :
    letI : point.M.IsMaximal := point.hM
    CommonOpenArcCompatibility hm P w setup coords point chart

namespace CommonOpenData

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {m : ℕ} {hm : 0 < m} {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
  {w : GeneralDivisorialVisibleFrameWitness hm P} {setup : ChartSetup hm P w}
  {coords : CoordinatePresentation hm P w setup}

abbrev M (data : CommonOpenData hm P w setup coords) := data.point.M
abbrev hM (data : CommonOpenData hm P w setup coords) := data.point.hM
abbrev eM (data : CommonOpenData hm P w setup coords) := data.point.eM
abbrev hEtM (data : CommonOpenData hm P w setup coords) := data.point.hEtM
abbrev fUnit (data : CommonOpenData hm P w setup coords) := data.point.fUnit
abbrev hfUnitM (data : CommonOpenData hm P w setup coords) := data.point.hfUnitM
abbrev u0 (data : CommonOpenData hm P w setup coords) := data.point.u0
abbrev u1 (data : CommonOpenData hm P w setup coords) := data.point.u1
abbrev hu0 (data : CommonOpenData hm P w setup coords) := data.point.hu0
abbrev hu1 (data : CommonOpenData hm P w setup coords) := data.point.hu1
abbrev hq0M (data : CommonOpenData hm P w setup coords) := data.point.hq0M
abbrev hq1M (data : CommonOpenData hm P w setup coords) := data.point.hq1M
abbrev alpha (data : CommonOpenData hm P w setup coords) := data.point.alpha
abbrev havoid (data : CommonOpenData hm P w setup coords) := data.point.havoid
abbrev hdata (data : CommonOpenData hm P w setup coords) := data.point.hdata
abbrev hxj (data : CommonOpenData hm P w setup coords) := data.chart.hxj
abbrev hsel (data : CommonOpenData hm P w setup coords) := data.chart.hsel
abbrev qQ (data : CommonOpenData hm P w setup coords) := data.chart.qQ
abbrev hqchartQ (data : CommonOpenData hm P w setup coords) := data.chart.hqchartQ
abbrev hqQF (data : CommonOpenData hm P w setup coords) := data.chart.hqQF
abbrev hq0 (data : CommonOpenData hm P w setup coords) := data.chart.hq0
abbrev hqvars (data : CommonOpenData hm P w setup coords) := data.chart.hqvars
abbrev hqA (data : CommonOpenData hm P w setup coords) := data.chart.hqA
abbrev hqUPoint (data : CommonOpenData hm P w setup coords) :=
  letI : data.point.M.IsMaximal := data.point.hM
  data.maps.hqUPoint
abbrev hchartU (data : CommonOpenData hm P w setup coords) :=
  letI : data.point.M.IsMaximal := data.point.hM
  data.maps.hchartU
abbrev hq0B (data : CommonOpenData hm P w setup coords) :=
  letI : data.point.M.IsMaximal := data.point.hM
  data.maps.hq0B
abbrev hbaseMap (data : CommonOpenData hm P w setup coords) :=
  letI : data.point.M.IsMaximal := data.point.hM
  data.maps.hbaseMap

abbrev hfactor (data : CommonOpenData hm P w setup coords) :=
  letI : data.point.M.IsMaximal := data.point.hM
  data.arc.hfactor

end CommonOpenData

noncomputable def CommonOpenData.g
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} {hm : 0 < m}
    {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
    {w : GeneralDivisorialVisibleFrameWitness hm P}
    {setup : ChartSetup hm P w}
    {coords : CoordinatePresentation hm P w setup}
    (data : CommonOpenData hm P w setup coords) : actualSelectedChartAlgebra P w :=
  data.hsel (selectedAffineChartDenominator P setup.j)

noncomputable abbrev CommonOpenData.Cq
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} {hm : 0 < m}
    {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
    {w : GeneralDivisorialVisibleFrameWitness hm P}
    {setup : ChartSetup hm P w}
    {coords : CoordinatePresentation hm P w setup}
    (data : CommonOpenData hm P w setup coords) : Type u := by
  letI : data.M.IsMaximal := data.hM
  exact genericOpenRing data.M setup.f setup.e

noncomputable abbrev CommonOpenData.U
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} {hm : 0 < m}
    {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
    {w : GeneralDivisorialVisibleFrameWitness hm P}
    {setup : ChartSetup hm P w}
    {coords : CoordinatePresentation hm P w setup}
    (data : CommonOpenData hm P w setup coords) : Type u := by
  letI : data.M.IsMaximal := data.hM
  exact genericOpenExtraAwayB data.M setup.f setup.e data.g

noncomputable def CommonOpenData.qU
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} {hm : 0 < m}
    {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
    {w : GeneralDivisorialVisibleFrameWitness hm P}
    {setup : ChartSetup hm P w}
    {coords : CoordinatePresentation hm P w setup}
    (data : CommonOpenData hm P w setup coords) : Fin (m + 1) → data.U := by
  letI : data.M.IsMaximal := data.hM
  exact fun a => algebraMap data.Cq data.U (algebraMap _ data.Cq (data.qQ a))

noncomputable def CommonOpenData.qT
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} {hm : 0 < m}
    {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
    {w : GeneralDivisorialVisibleFrameWitness hm P}
    {setup : ChartSetup hm P w}
    {coords : CoordinatePresentation hm P w setup}
    (data : CommonOpenData hm P w setup coords) :
      letI : data.M.IsMaximal := data.hM
      Fin (m + 1) → Localization.AtPrime data.M := by
  letI : data.M.IsMaximal := data.hM
  exact fun a => algebraMap (actualSelectedNormalization P w) (Localization.AtPrime data.M)
    ((retainedColumns hm P w) a)

noncomputable def CommonOpenData.φ
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} {hm : 0 < m}
    {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
    {w : GeneralDivisorialVisibleFrameWitness hm P}
    {setup : ChartSetup hm P w}
    {coords : CoordinatePresentation hm P w setup}
    (data : CommonOpenData hm P w setup coords) :
      OriginalAffineChartQuotient (k := k) P →+* data.U := by
  letI : data.M.IsMaximal := data.hM
  exact originalAffineChartToCommonOpen P setup.j data.hxj data.hsel
    data.M setup.f setup.e

/-- Express the retained columns in the selected affine quotient. -/
theorem exists_selected_chart_coordinate_data
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {m : ℕ}
    (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (M : Ideal (actualSelectedNormalization P w)) [M.IsMaximal] :
    ∃ hsel : SelectedAffineChartQuotient (k := k) P setup.j ≃ₐ[k]
        actualSelectedChartAlgebra P w,
      ∃ qQ : Fin (m + 1) → actualSelectedChartAlgebra P w,
        qQ (Fin.succ setup.j) = 1 ∧
        (∀ a, (qQ a : ComponentFractionField P) =
          retainedColumnValue P w a) ∧
        qQ 0 = hsel (selectedAffineChartDenominator P setup.j) ∧
        (∀ i : Fin m, ∀ hij : i ≠ setup.j,
          qQ (Fin.succ i) = hsel (selectedAffineChartVariableClass P setup.j i hij)) := by
  let hsel : SelectedAffineChartQuotient (k := k) P setup.j ≃ₐ[k]
      (actualSelectedChartAlgebra P w) :=
    actual_witness_selected_chart_quotient_equiv P w setup.j setup.hchart
  have hqCoordinates :=
    actual_witness_selected_chart_q_coordinates_in_actual_algebra
      hm P w setup.j setup.hchart
  dsimp only at hqCoordinates
  rcases hqCoordinates with ⟨qQ, hqchartQ, hqQF, hq0, hqvars⟩
  exact ⟨hsel, qQ, hqchartQ, hqQF, hq0, hqvars⟩

/-- Identify the selected columns with their images in the common open and
the point-local route, and record the original chart map. -/
theorem exists_common_open_map_data
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (M : Ideal (actualSelectedNormalization P w)) [M.IsMaximal]
    (hsel : SelectedAffineChartQuotient (k := k) P setup.j ≃ₐ[k]
      actualSelectedChartAlgebra P w)
    (qQ : Fin (m + 1) → actualSelectedChartAlgebra P w)
    (hqchartQ : qQ (Fin.succ setup.j) = 1)
    (hqQF : ∀ a, (qQ a : ComponentFractionField P) =
      retainedColumnValue P w a)
    (hq0 : qQ 0 = hsel (selectedAffineChartDenominator P setup.j))
    (hqvars : ∀ i : Fin m, ∀ hij : i ≠ setup.j,
      qQ (Fin.succ i) = hsel (selectedAffineChartVariableClass P setup.j i hij)) :
    let Q := actualSelectedChartAlgebra P w
    let B := actualSelectedNormalization P w
    let g := hsel (selectedAffineChartDenominator P setup.j)
    let Cq := genericOpenRing M setup.f setup.e
    let U := genericOpenExtraAwayB M setup.f setup.e g
    let qU : Fin (m + 1) → U := fun a =>
      algebraMap Cq U (algebraMap Q Cq (qQ a))
    let qT : Fin (m + 1) → Localization.AtPrime M := fun a =>
      algebraMap B (Localization.AtPrime M)
        ((retainedColumns hm P w) a)
    ∃ hxj : componentCoordinate P setup.j ≠ 0,
      (∀ a, (retainedColumns hm P w) a = algebraMap Q B (qQ a)) ∧
      (∀ a, qU a = pointLocalToCommonOpen (A := B) M setup.f setup.e g (qT a)) ∧
      (∀ i : Fin m, qU i.succ = qU 0 *
        originalAffineChartToCommonOpen P setup.j hxj hsel M setup.f setup.e
          (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i))) ∧
      (retainedColumns hm P w) 0 =
        algebraMap Q B g ∧
      (genericOpenExtraAwayBMap M setup.f setup.e g).comp
          (algebraMap Q B) = (algebraMap Cq U).comp (algebraMap Q Cq) := by
  dsimp only
  let Q := actualSelectedChartAlgebra P w
  let B := actualSelectedNormalization P w
  let g := hsel (selectedAffineChartDenominator P setup.j)
  let Cq := genericOpenRing M setup.f setup.e
  let U := genericOpenExtraAwayB M setup.f setup.e g
  let qU : Fin (m + 1) → U := fun a =>
    algebraMap Cq U (algebraMap Q Cq (qQ a))
  let qB : Fin (m + 1) → B := (retainedColumns hm P w)
  let qT : Fin (m + 1) → Localization.AtPrime M := fun a =>
    algebraMap B (Localization.AtPrime M) (qB a)
  have hqBspec :=
    letI : Algebra
        (Stafford38.Geometry.AsymptoticDivisorExistence.CoordinateZeroLocalRing
          w.column.W.coefficientField)
        (ComponentFractionField P) := w.column.W.ambientAlgebra
    letI : IsLocalRing w.column.W.place.valuation.toSubring :=
      w.column.W.place.isDiscrete.toIsLocalRing
    actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
  have hqBf : ∀ a, ((qB a : B) : ComponentFractionField P) =
      retainedColumnValue P w a := by
    simpa [qB] using hqBspec.2.1
  have hqA : ∀ a, qB a = algebraMap Q B (qQ a) := by
    intro a
    exact actualColumn_eq_chartImage Q qQ qB
      (fun a => retainedColumnValue P w a)
      hqQF hqBf a
  have hqUPoint : ∀ a, qU a =
      pointLocalToCommonOpen (A := B) M setup.f setup.e g (qT a) := by
    have hroute := pointLocal_commonOpen_column (A := B) M setup.f setup.e g
      qQ qB hqA qT (fun a => rfl)
    intro a
    exact (hroute a).symm
  have hxj : componentCoordinate P setup.j ≠ 0 :=
    actualWitness_selected_coordinate_ne_zero hm P w setup.j setup.hchart
  let φ := originalAffineChartToCommonOpen P setup.j hxj hsel M setup.f setup.e
  have hchartU := q_column_commonOpen_coordinates P setup.j hxj hsel M setup.f
    setup.e qQ hqchartQ hq0 hqvars
  have hq0B : qB 0 = algebraMap Q B g := by
    exact (hqA 0).trans (congrArg (algebraMap Q B) hq0)
  have hbaseMap : (genericOpenExtraAwayBMap M setup.f setup.e g).comp
      (algebraMap Q B) =
      (algebraMap Cq U).comp (algebraMap Q Cq) := by
    apply RingHom.ext
    intro x
    change algebraMap Cq U
        (genericOpenBMap M setup.f setup.e (algebraMap Q B x)) =
      algebraMap Cq U (algebraMap Q Cq x)
    exact congrArg (algebraMap Cq U) (genericOpenBMap_base_eq M setup.f setup.e x)
  exact ⟨hxj, hqA, hqUPoint, hchartU, hq0B, hbaseMap⟩

/-- The retained ground-point output determines its maximal point and
chosen tilted coordinate axis (paper proof, common-open step). -/
theorem nonempty_commonOpenPointData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    : Nonempty (CommonOpenPointData hm P w setup coords) := by
  classical
  letI : Fintype coords.t := coords.htFinite
  let Q := actualSelectedChartAlgebra P w
  let B := actualSelectedNormalization P w
  let qB : Fin (m + 1) → B := (retainedColumns hm P w)
  let hQV := chartGenericPointSubalgebra_le_valuationSubring hm P w
  let PB := actualSelectedNormalizationCenterPrime P w hQV
  let bad : B := algebraMap Q B setup.f * algebraMap Q B setup.r
  have hbad : bad ≠ 0 := setup.fB_mul_rB_ne_zero
  obtain ⟨M, hM, eM, fUnit, hfUnitM, u0, u1, hu0, hu1, hq0M, hq1M,
      hEtM, alpha, havoid, hdata⟩ :=
    @exists_axis_lift_of_groundPointChartOutput k inferInstance inferInstance
      inferInstance B inferInstance coords.coeff.toAlgebra inferInstance
      coords.hBfinite coords.t coords.htFinite PB coords.hPB coords.fOption coords.s
      (qB 0) (qB (Fin.succ (⟨0, hm⟩ : Fin m))) coords.qRow coords.hnone
      coords.hsPB coords.hsome coords.τ (retainedOrder P w)
      ((retainedOrder P w) + (retainedGap P w)) coords.hOutput
      m qB w.column.chart (⟨0, hm⟩ : Fin m) coords.hqchartB
      rfl rfl coords.rows coords.hrows bad hbad
  exact ⟨{
      M := M, hM := hM, eM := eM
      hEtM := by simpa only [CoordinatePresentation.fFin] using hEtM
      fUnit := fUnit, hfUnitM := hfUnitM
      u0 := u0, u1 := u1
      hu0 := hu0, hu1 := hu1
      hq0M := hq0M, hq1M := hq1M
      alpha := alpha
      havoid := by simpa only [CoordinatePresentation.fFin] using havoid
      hdata := by simpa only [CoordinatePresentation.fFin, setup.hchart] using hdata
  }⟩

/-- The retained point-local tilt extends to the selected common open
with all factors nonzero (paper proof, common-open step). -/
theorem nonempty_commonOpenArcCompatibility
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (point : CommonOpenPointData hm P w setup coords)
    (chart : CommonOpenChartData hm P w setup coords) :
    letI : point.M.IsMaximal := point.hM
    Nonempty (CommonOpenArcCompatibility hm P w setup coords point chart) := by
  classical
  letI : point.M.IsMaximal := point.hM
  let Q := actualSelectedChartAlgebra P w
  let B := actualSelectedNormalization P w
  refine ⟨{ hfactor := ?_ }⟩
  apply @commonOpenArcFactors_of_tiltedProduct k B Q
    inferInstance inferInstance inferInstance coords.coeff.toAlgebra
    (inferInstance : Algebra Q B) (@Fintype.card coords.t coords.htFinite)
    (@RingHom.toAlgebra
      (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k) B
      inferInstance inferInstance
      (@AlgHom.toRingHom k
        (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k) B
        inferInstance inferInstance inferInstance inferInstance
        coords.coeff.toAlgebra coords.fFin))
    (@IsScalarTower.of_algHom k
      (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k) B
      inferInstance inferInstance inferInstance inferInstance
      coords.coeff.toAlgebra coords.fFin)
    (@essFiniteType_of_coordinateMap k B inferInstance inferInstance
      coords.coeff.toAlgebra coords.hBfinite
      (@Fintype.card coords.t coords.htFinite) coords.fFin)
    point.M point.hM point.hEtM
  · rfl
  · exact (chart.hqA 0).trans
      (congrArg (algebraMap Q B) chart.hq0)
  · exact point.havoid

/-- Construct the common open by transporting the chosen axis lift to the
selected affine chart and its extra-away localization. -/
theorem nonempty_commonOpenData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (hpoint : actualSameWitnessGroundPointOutput hm P w) :
    Nonempty (CommonOpenData hm P w setup coords) := by
  classical
  obtain ⟨point⟩ := nonempty_commonOpenPointData hm P w setup coords
  letI : point.M.IsMaximal := point.hM
  let Q := actualSelectedChartAlgebra P w
  let B := actualSelectedNormalization P w
  obtain ⟨hsel, qQ, hqchartQ, hqQF, hq0, hqvars⟩ :=
    exists_selected_chart_coordinate_data hm P w setup point.M
  obtain ⟨hxj, hqA, hqUPoint, hchartU, hq0B, hbaseMap⟩ :=
    exists_common_open_map_data hm P w setup point.M hsel qQ hqchartQ hqQF hq0 hqvars
  let chart : CommonOpenChartData hm P w setup coords := {
    hxj := hxj, hsel := hsel, qQ := qQ
    hqchartQ := hqchartQ, hqQF := hqQF
    hq0 := hq0, hqvars := hqvars, hqA := hqA
  }
  let maps : CommonOpenMapData hm P w setup coords point chart := {
    hqUPoint := hqUPoint, hchartU := hchartU
    hq0B := hq0B, hbaseMap := hbaseMap
  }
  obtain ⟨arc⟩ := nonempty_commonOpenArcCompatibility hm P w setup coords point chart
  exact ⟨{ point := point, chart := chart, maps := maps, arc := arc }⟩

end Stafford38.Geometry.SameWitness

end
