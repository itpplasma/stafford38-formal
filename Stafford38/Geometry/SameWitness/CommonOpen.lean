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

universe u

/-- The maximal point, selected chart, and common-open maps built from one
retained ground-point axis lift (paper proof, common-open step). -/
structure CommonOpenData
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
    letI : Algebra R (actualSelectedNormalization P w) :=
      coords.fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R (actualSelectedNormalization P w) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext c
        exact (coords.fFin.commutes c).symm)
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
  hq0M : algebraMap _ (Localization.AtPrime M)
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0) =
    (algebraMap _ (Localization.AtPrime M) coords.s) ^ w.differential.core.D.a * u0
  hq1M : algebraMap _ (Localization.AtPrime M)
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w
        (Fin.succ (⟨0, hm⟩ : Fin m))) =
    (algebraMap _ (Localization.AtPrime M) coords.s) ^
      (w.differential.core.D.a + w.differential.core.D.e) * u1
  alpha : Fin (@Fintype.card coords.t coords.htFinite) → k
  havoid :
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    letI : Algebra k (actualSelectedNormalization P w) := coords.coeff.toAlgebra
    letI : Algebra R (actualSelectedNormalization P w) :=
      coords.fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R (actualSelectedNormalization P w) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext c
        exact (coords.fFin.commutes c).symm)
    letI : Algebra.EssFiniteType R (actualSelectedNormalization P w) :=
      Algebra.EssFiniteType.of_comp k R (actualSelectedNormalization P w)
    letI : Algebra R (Localization.AtPrime M) := inferInstance
    letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
    tiltedArc (k := k) alpha
      (localToFinSuccPowerSeries (k := k)
          (B := actualSelectedNormalization P w)
          (d := @Fintype.card coords.t coords.htFinite) M eM
          (algebraMap _ (Localization.AtPrime M)
            (algebraMap _ (actualSelectedNormalization P w) setup.f *
              algebraMap _ (actualSelectedNormalization P w) setup.r)) *
       localToFinSuccPowerSeries (k := k)
          (B := actualSelectedNormalization P w)
          (d := @Fintype.card coords.t coords.htFinite) M eM
          (algebraMap _ (Localization.AtPrime M)
            (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0)) *
       localToFinSuccPowerSeries (k := k)
          (B := actualSelectedNormalization P w)
          (d := @Fintype.card coords.t coords.htFinite) M eM
          (algebraMap _ (Localization.AtPrime M)
            (actualNormalizedProjectiveColumnInIntegralClosure hm P w
              (Fin.succ (⟨0, hm⟩ : Fin m))))) ≠ 0
  hdata :
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    letI : Algebra k (actualSelectedNormalization P w) := coords.coeff.toAlgebra
    letI : Algebra R (actualSelectedNormalization P w) :=
      coords.fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R (actualSelectedNormalization P w) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext c
        exact (coords.fFin.commutes c).symm)
    letI : Algebra.EssFiniteType R (actualSelectedNormalization P w) :=
      Algebra.EssFiniteType.of_comp k R (actualSelectedNormalization P w)
    letI : Algebra R (Localization.AtPrime M) := inferInstance
    letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
    SelectedCoordinateAxisLiftData
      (fun a => localToFinSuccPowerSeries (k := k)
        (B := actualSelectedNormalization P w)
        (d := @Fintype.card coords.t coords.htFinite) M eM
        (algebraMap _ (Localization.AtPrime M)
          (actualNormalizedProjectiveColumnInIntegralClosure hm P w a)))
      coords.rows (Fin.succ setup.j) 0 (⟨0, hm⟩ : Fin m).succ
      w.differential.core.D.a
      (w.differential.core.D.a + w.differential.core.D.e)
      (fun j => PrescribedAffineResidueCompletion.residueCoordinates
        M eM (some j)) alpha
      (localToFinSuccPowerSeries (k := k)
        (B := actualSelectedNormalization P w)
        (d := @Fintype.card coords.t coords.htFinite) M eM u0)
      (localToFinSuccPowerSeries (k := k)
        (B := actualSelectedNormalization P w)
        (d := @Fintype.card coords.t coords.htFinite) M eM u1)
  hxj : componentCoordinate P setup.j ≠ 0
  hsel : SelectedAffineChartQuotient (k := k) P setup.j ≃ₐ[k]
      actualSelectedChartAlgebra P w
  qQ : Fin (m + 1) → actualSelectedChartAlgebra P w
  hqchartQ : qQ (Fin.succ setup.j) = 1
  hqQF : ∀ a, (qQ a : ComponentFractionField P) =
      ((w.column.q a : w.column.W.place.valuation.toSubring) : ComponentFractionField P)
  hq0 : qQ 0 = hsel (selectedAffineChartDenominator P setup.j)
  hqvars : ∀ i : Fin m, ∀ hij : i ≠ setup.j,
      qQ (Fin.succ i) =
        hsel (selectedAffineChartVariableClass P setup.j i hij)
  hqA : ∀ a, actualNormalizedProjectiveColumnInIntegralClosure hm P w a =
      algebraMap _ (actualSelectedNormalization P w) (qQ a)
  hqUPoint :
    let g := hsel (selectedAffineChartDenominator P setup.j)
    let Cq := genericOpenRing M setup.f setup.e
    let U := genericOpenExtraAwayB M setup.f setup.e g
    let qU : Fin (m + 1) → U := fun a =>
      algebraMap Cq U (algebraMap _ Cq (qQ a))
    let qT : Fin (m + 1) → Localization.AtPrime M := fun a =>
      algebraMap _ (Localization.AtPrime M)
        (actualNormalizedProjectiveColumnInIntegralClosure hm P w a)
    ∀ a, qU a = pointLocalToCommonOpen
      (A := actualSelectedNormalization P w) M setup.f setup.e g (qT a)
  hchartU :
    let g := hsel (selectedAffineChartDenominator P setup.j)
    let Cq := genericOpenRing M setup.f setup.e
    let U := genericOpenExtraAwayB M setup.f setup.e g
    let qU : Fin (m + 1) → U := fun a =>
      algebraMap Cq U (algebraMap _ Cq (qQ a))
    let φ := originalAffineChartToCommonOpen P setup.j hxj hsel M setup.f setup.e
    ∀ i : Fin m, qU i.succ = qU 0 *
      φ (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i))
  hq0B : actualNormalizedProjectiveColumnInIntegralClosure hm P w 0 =
      algebraMap _ (actualSelectedNormalization P w)
        (hsel (selectedAffineChartDenominator P setup.j))
  hbaseMap :
    let g := hsel (selectedAffineChartDenominator P setup.j)
    let Cq := genericOpenRing M setup.f setup.e
    let U := genericOpenExtraAwayB M setup.f setup.e g
    (genericOpenExtraAwayBMap M setup.f setup.e g).comp
      (algebraMap (actualSelectedChartAlgebra P w)
        (actualSelectedNormalization P w)) =
    (algebraMap Cq U).comp (algebraMap _ Cq)
  hfactor :
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    letI : Algebra k (actualSelectedNormalization P w) := coords.coeff.toAlgebra
    letI : Algebra R (actualSelectedNormalization P w) :=
      coords.fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R (actualSelectedNormalization P w) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext c
        exact (coords.fFin.commutes c).symm)
    letI : Algebra.EssFiniteType R (actualSelectedNormalization P w) :=
      Algebra.EssFiniteType.of_comp k R (actualSelectedNormalization P w)
    letI : Algebra R (Localization.AtPrime M) := inferInstance
    letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
    commonOpen_factors_ne_zero_of_tiltedProduct
      (k := k) (d := @Fintype.card coords.t coords.htFinite)
      (A := actualSelectedNormalization P w) M setup.f setup.e g eM alpha
      (algebraMap (actualSelectedChartAlgebra P w)
        (actualSelectedNormalization P w) setup.r)
      (algebraMap _ (actualSelectedNormalization P w) setup.f *
        algebraMap _ (actualSelectedNormalization P w) setup.r)
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0)
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w
        (Fin.succ (⟨0, hm⟩ : Fin m))) rfl hq0B havoid

noncomputable def CommonOpenData.g
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} {hm : 0 < m}
    {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
    {w : GeneralDivisorialVisibleFrameWitness hm P}
    {setup : ChartSetup hm P w}
    {coords : CoordinatePresentation hm P w setup}
    (data : CommonOpenData hm P w setup coords) : actualSelectedChartAlgebra P w :=
  data.hsel (selectedAffineChartDenominator P setup.j)

noncomputable def CommonOpenData.Cq
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} {hm : 0 < m}
    {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
    {w : GeneralDivisorialVisibleFrameWitness hm P}
    {setup : ChartSetup hm P w}
    {coords : CoordinatePresentation hm P w setup}
    (data : CommonOpenData hm P w setup coords) : Type u := by
  letI : data.M.IsMaximal := data.hM
  exact genericOpenRing data.M setup.f setup.e

noncomputable def CommonOpenData.U
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
  exact fun a => algebraMap _ (Localization.AtPrime data.M)
    (actualNormalizedProjectiveColumnInIntegralClosure hm P w a)

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
    {k : Type u} [Field k] [CharZero k] {m : ℕ}
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
          ((w.column.q a : w.column.W.place.valuation.toSubring) : ComponentFractionField P)) ∧
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
      ((w.column.q a : w.column.W.place.valuation.toSubring) : ComponentFractionField P))
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
        (actualNormalizedProjectiveColumnInIntegralClosure hm P w a)
    ∃ hxj : componentCoordinate P setup.j ≠ 0,
      (∀ a, qU a = pointLocalToCommonOpen (A := B) M setup.f setup.e g (qT a)) ∧
      (∀ i : Fin m, qU i.succ = qU 0 *
        originalAffineChartToCommonOpen P setup.j hxj hsel M setup.f setup.e
          (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i))) ∧
      actualNormalizedProjectiveColumnInIntegralClosure hm P w 0 =
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
  let qB : Fin (m + 1) → B := actualNormalizedProjectiveColumnInIntegralClosure hm P w
  let qT : Fin (m + 1) → Localization.AtPrime M := fun a =>
    algebraMap B (Localization.AtPrime M) (qB a)
  have hqBspec := actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
  have hqBf : ∀ a, ((qB a : B) : ComponentFractionField P) =
      ((w.column.q a : w.column.W.place.valuation.toSubring) : ComponentFractionField P) := by
    simpa [qB] using hqBspec.2.1
  have hqA : ∀ a, qB a = algebraMap Q B (qQ a) := by
    intro a
    exact actualColumn_eq_chartImage Q qQ qB
      (fun a => ((w.column.q a : w.column.W.place.valuation.toSubring) : ComponentFractionField P))
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
    rw [hqA 0, hq0]
  have hbaseMap : (genericOpenExtraAwayBMap M setup.f setup.e g).comp
      (algebraMap Q B) =
      (algebraMap Cq U).comp (algebraMap Q Cq) := by
    apply RingHom.ext
    intro x
    change algebraMap Cq U
        (genericOpenBMap M setup.f setup.e (algebraMap Q B x)) =
      algebraMap Cq U (algebraMap Q Cq x)
    rw [genericOpenBMap_base_eq]
  exact ⟨hxj, hqUPoint, hchartU, hq0B, hbaseMap⟩

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
  letI : Fintype coords.t := coords.htFinite
  let Q := actualSelectedChartAlgebra P w
  let B := actualSelectedNormalization P w
  let qB : Fin (m + 1) → B := actualNormalizedProjectiveColumnInIntegralClosure hm P w
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
      coords.hsPB coords.hsome coords.τ w.differential.core.D.a
      (w.differential.core.D.a + w.differential.core.D.e) coords.hOutput
      m qB w.column.chart (⟨0, hm⟩ : Fin m) coords.hqchartB
      rfl rfl coords.rows coords.hrows bad hbad
  letI : M.IsMaximal := hM
  obtain ⟨hsel, qQ, hqchartQ, hqQF, hq0, hqvars⟩ :=
    exists_selected_chart_coordinate_data hm P w setup M
  let g : Q := hsel (selectedAffineChartDenominator P setup.j)
  obtain ⟨hxj, hqUPoint, hchartU, hq0B, hbaseMap⟩ :=
    exists_common_open_map_data hm P w setup M hsel qQ hqchartQ hqQF hq0 hqvars
  exact ⟨{
    M := M
    hM := hM
    eM := eM
    hEtM := hEtM
    fUnit := fUnit
    hfUnitM := hfUnitM
    u0 := u0
    u1 := u1
    hu0 := hu0
    hu1 := hu1
    hq0M := hq0M
    hq1M := hq1M
    alpha := alpha
    havoid := havoid
    hdata := hdata
    hxj := hxj
    hsel := hsel
    qQ := qQ
    hqchartQ := hqchartQ
    hqQF := hqQF
    hq0 := hq0
    hqvars := hqvars
    hqA := hqA
    hqUPoint := hqUPoint
    hchartU := hchartU
    hq0B := hq0B
    hbaseMap := hbaseMap
    hfactor := by
      dsimp only
      change commonOpen_factors_ne_zero_of_tiltedProduct
        (k := k) (d := Fintype.card coords.t) (A := B) M setup.f setup.e g eM alpha
        (algebraMap Q B setup.r) bad (qB 0)
        (qB (Fin.succ (⟨0, hm⟩ : Fin m))) rfl hq0B havoid
      exact commonOpen_factors_ne_zero_of_tiltedProduct
        (k := k) (d := Fintype.card coords.t) (A := B) M setup.f setup.e g eM alpha
        (algebraMap Q B setup.r) bad (qB 0)
        (qB (Fin.succ (⟨0, hm⟩ : Fin m))) rfl hq0B havoid
  }⟩

end Stafford38.Geometry.SameWitness

end
