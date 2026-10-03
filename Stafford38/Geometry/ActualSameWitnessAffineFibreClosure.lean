import Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
import Stafford38.Geometry.ActualOptionColumnBinding
import Stafford38.Geometry.ActualSelectedNormalizationAway
import Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
import Stafford38.Geometry.GroundPointAxisLiftFromOutput
import Stafford38.Geometry.ActualWitnessCommonOpenColumnGlue
import Stafford38.Geometry.ActualWitnessSelectedChartBinding
import Stafford38.Geometry.ActualSelectedNormalizationChartTransport
import Stafford38.Geometry.ChartGenericPointFractionRing
import Stafford38.Geometry.ActualOptionCommonOpenColumns
import Stafford38.Geometry.ActualPointCommonOpenAssembly
import Stafford38.Geometry.ActualOptionGroundPointCompletion
import Stafford38.Geometry.GroundPointAxisLiftFromOutput
import Stafford38.Geometry.ActualSameWitnessAffineFibreEndpoint
import Stafford38.Geometry.ActualWitnessSelectedChartIndex
import Stafford38.Geometry.A0NormalizedProjectiveCoordinates
import Stafford38.Geometry.ActualSmoothOpenChartNumerator
import Stafford38.Geometry.CommonOpenEvaluation
import Stafford38.Geometry.ActualCommonOpenArcCompatibility
import Stafford38.Geometry.ProjectiveChartSameFieldOverlap
import Stafford38.Geometry.AsymptoticChartArcAdapter
import Stafford38.Geometry.A0ChartFormalEtale
import Stafford38.Geometry.A0ChartGeneratorCoordinates

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 8192
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualSameWitnessAffineFibreClosure

open Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ActualSelectedNormalizationAway
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.ActualOptionColumnBinding
open Stafford38.Geometry.ActualWitnessSelectedChartIndex
open Stafford38.Geometry.ActualWitnessCommonOpenColumnGlue
open Stafford38.Geometry.ActualWitnessSelectedChartBinding
open Stafford38.Geometry.ActualSelectedNormalizationChartTransport
open Stafford38.Geometry.ActualOptionCommonOpenColumns
open Stafford38.Geometry.ActualPointCommonOpenAssembly
open Stafford38.Geometry.ActualOptionGroundPointCompletion
open Stafford38.Geometry.GroundPointAxisLiftFromOutput
open Stafford38.Geometry.ActualSameWitnessAffineFibreEndpoint
open Stafford38.Geometry.A0NormalizedProjectiveCoordinates
open Stafford38.Geometry.A0ChartFormalEtale
open Stafford38.Geometry.A0ChartGeneratorCoordinates
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ActualSmoothOpenChartNumerator
open Stafford38.Geometry.CommonOpenEvaluation
open Stafford38.Geometry.ActualCommonOpenArcCompatibility
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.SelectedResidueCoefficientLocalization
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.ProjectiveChartSameFieldOverlap
open Stafford38.Geometry.ActualCommonOpenColumnGlue
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.RetainedGroundMapIdentification
open IsLocalRing
open Stafford38.Geometry.AsymptoticChartArcAdapter

universe u

/-- The common-open endpoint for the same selected witness follows from its
closed ground-point output.  The only extra input is the usual smooth affine
principal open on the original component; the away denominator and the
homogenized numerator are avoided by the one tilt returned by the existing
axis-lift producer. -/
theorem axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hpoint : actualSameWitnessGroundPointOutput hm P w)
    (hsmoothOpen : ∃ fbar : MvPolynomial (Fin m) k ⧸ P.asIdeal,
      fbar ≠ 0 ∧ Algebra.Smooth k (Localization.Away fbar)) :
    (fun i : Fin m => if i = (⟨0, hm⟩ : Fin m) then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection
            P.asIdeal)) := by
  classical
  obtain ⟨fbar, hfbar, hsmooth⟩ := hsmoothOpen
  obtain ⟨p, hpq⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) fbar
  have hp : Ideal.Quotient.mk P.asIdeal p ≠ 0 := by
    rw [hpq]
    exact hfbar
  obtain ⟨j, hchart⟩ := exists_succ_chart_index hm P w
  let C := w.column
  let F := ComponentFractionField P
  let W := C.W
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let U := W.place.valuation
  let V := U.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  let Q : Subalgebra k F := actualSelectedChartAlgebra P w
  let B := actualSelectedNormalization P w
  letI : IsDomain B := inferInstance
  let qB : Fin (m + 1) → B :=
    actualNormalizedProjectiveColumnInIntegralClosure hm P w
  let coeff : k →+* B := actualSelectedNormalizationCoefficients P w
  let hQV := ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring hm P w
  let PB := actualSelectedNormalizationCenterPrime P w hQV
  let qToB : Q →+* B := chartSubalgebraToIntegralClosure Q
  letI : Algebra k B := coeff.toAlgebra
  letI : Algebra Q B := qToB.toAlgebra
  letI : IsScalarTower k Q B := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rfl
  letI : Algebra Q F := Q.val.toAlgebra
  have haway := actual_selected_normalization_is_away_equiv P w
  obtain ⟨f0, hf0, he0⟩ := haway
  let e0 := Classical.choice he0
  let f : Q := f0
  have hf : f ≠ 0 := by
    intro h
    exact hf0 h
  let e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f) := e0
  obtain ⟨r0, hrF, hrformula, hr0⟩ :=
    exists_nonzero_homogenized_numerator hm P w p hp
  let r : Q := r0
  have hr : r ≠ 0 := by
    intro h
    exact hr0 h
  let rB : B := qToB r
  let fB : B := qToB f
  have hqToB_inj : Function.Injective qToB := by
    intro x y hxy
    apply Subtype.ext
    calc
      (x : F) = ((qToB x : B) : F) :=
        (coe_chartSubalgebraToIntegralClosure Q x).symm
      _ = ((qToB y : B) : F) := congrArg (fun z : B => (z : F)) hxy
      _ = (y : F) := coe_chartSubalgebraToIntegralClosure Q y
  have hqToBj_inj : Function.Injective qToB := hqToB_inj
  have hfB : fB ≠ 0 := by
    intro hz
    apply hf
    apply hqToBj_inj
    simpa [fB] using hz
  have hrB : rB ≠ 0 := by
    intro hz
    apply hr
    apply hqToBj_inj
    simpa [rB] using hz
  have hbad : fB * rB ≠ 0 := mul_ne_zero hfB hrB
  -- The named output keeps the large ground-point telescope opaque; open it
  -- once here and reuse its exact point, rows, and formal-etale certificate.
  unfold actualSameWitnessGroundPointOutput at hpoint
  dsimp only at hpoint
  rcases hpoint with ⟨hBfinite, t, htFinite, htBasis, index, hindex,
    hresidue, hPB, s, hs0, hsPB, u₀, u₁, hu₀, hu₁, hspan,
    hfactor₀, hfactor₁, hGroundPoint⟩
  letI : Algebra.FiniteType k B := hBfinite
  letI : Fintype t := htFinite.fintype
  letI : PB.IsPrime := hPB
  letI : Algebra Q B := qToB.toAlgebra
  let τ : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let rows : Fin (Fintype.card t) ↪ Fin (m + 1) :=
    ⟨fun i => (chartAffineCoordinateEquiv (Fin.succ j)
      (index (τ i))).1, by
      intro i i' hii
      change (chartAffineCoordinateEquiv (Fin.succ j)
          (index (τ i))).1 = (chartAffineCoordinateEquiv (Fin.succ j)
          (index (τ i'))).1 at hii
      have hcoord : chartAffineCoordinateEquiv (Fin.succ j) (index (τ i)) =
          chartAffineCoordinateEquiv (Fin.succ j) (index (τ i')) :=
        Subtype.ext hii
      apply τ.injective
      exact hindex ((chartAffineCoordinateEquiv (Fin.succ j)).injective hcoord)⟩
  let qRow : t → B := actualSelectedNormalizationRows P w index
  let fOption : MvPolynomial (Option t) k →ₐ[k] B :=
    actualOptionMap s qRow
  have hnone : fOption (MvPolynomial.X (R := k) none) = s := by
    exact actualOptionMap_none s qRow
  have hsome : ∀ z, fOption (MvPolynomial.X (R := k) (some z)) = qRow z := by
    intro z
    exact actualOptionMap_some s qRow z
  let d := Fintype.card t
  let R := MvPolynomial (Option (Fin d)) k
  let fFin : R →ₐ[k] B :=
    fOption.comp (MvPolynomial.renameEquiv k τ.optionCongr).toAlgHom
  letI : Algebra R B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    change algebraMap k B c = fFin (algebraMap k R c)
    exact (fFin.commutes c).symm
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  have hrows : ∀ i : Fin (Fintype.card t), qRow (τ i) = qB (rows i) := by
    intro i
    change actualNormalizedProjectiveColumnInIntegralClosure hm P w
      ((chartAffineCoordinateEquiv w.column.chart (index (τ i))).1) =
      actualNormalizedProjectiveColumnInIntegralClosure hm P w (rows i)
    congr 1
    exact congrArg (fun c =>
      (chartAffineCoordinateEquiv c (index (τ i))).1) hchart
  have hqchartB : qB C.chart = 1 := by
    obtain ⟨h, _, _⟩ := actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
    exact h
  have hzero : qB 0 = actualNormalizedProjectiveColumnInIntegralClosure hm P w 0 := rfl
  have haxis : qB (Fin.succ (⟨0, hm⟩ : Fin m)) =
      actualNormalizedProjectiveColumnInIntegralClosure hm P w
        (Fin.succ (⟨0, hm⟩ : Fin m)) := rfl
  rcases hGroundPoint with ⟨cert, hGroundPoint⟩
  have hOutput : GroundPointChartOutput
      (actualSelectedNormalizationCenterPrime P w
        (ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring hm P w))
      fOption s (qB 0)
      (qB (Fin.succ (⟨0, hm⟩ : Fin m))) qRow τ w.differential.core.D.a
      (w.differential.core.D.a + w.differential.core.D.e) := by
    change GroundPointChartOutput
      (actualSelectedNormalizationCenterPrime P w
        (ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring hm P w))
      (actualOptionMap s (actualSelectedNormalizationRows P w index)) s
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0)
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w
        (Fin.succ (⟨0, hm⟩ : Fin m)))
      (actualSelectedNormalizationRows P w index) ((Fintype.equivFin t).symm)
      w.differential.core.D.a (w.differential.core.D.a + w.differential.core.D.e)
    exact hGroundPoint
  let bad : B := fB * rB
  obtain ⟨M, hM, eM, fUnit, hfUnitM, u₀', u₁', hu₀', hu₁', hq₀M, hq₁M,
      hEtM, α, havoid, hdata⟩ :=
    exists_axis_lift_of_groundPointChartOutput PB fOption s (qB 0)
      (qB (Fin.succ (⟨0, hm⟩ : Fin m))) qRow
      hnone hsPB hsome τ w.differential.core.D.a
      (w.differential.core.D.a + w.differential.core.D.e) hOutput
      qB C.chart (⟨0, hm⟩ : Fin m) hqchartB rfl rfl rows hrows bad hbad
  letI : M.IsMaximal := hM
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
    actual_witness_selected_chart_quotient_equiv P w j hchart
  have hqCoordinates :=
    actual_witness_selected_chart_q_coordinates_in_actual_algebra hm P w j hchart
  dsimp only at hqCoordinates
  obtain ⟨qQ, hqchartQ', hqQF, hq0, hqvars⟩ := hqCoordinates
  let Cq := genericOpenRing M f e
  let g : Q := hsel (selectedAffineChartDenominator P j)
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq U := inferInstance
  letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
  let qU : Fin (m + 1) → U := fun a =>
    algebraMap Cq U (algebraMap Q Cq (qQ a))
  let qT : Fin (m + 1) → Localization.AtPrime M := fun a =>
    algebraMap B (Localization.AtPrime M) (qB a)
  have hqBspec := actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
  have hqBf : ∀ a, ((qB a : B) : F) = ((w.column.q a : V) : F) := by
    simpa [qB] using hqBspec.2.1
  have hqA : ∀ a, qB a = algebraMap Q B (qQ a) := by
    intro a
    exact actualColumn_eq_chartImage Q qQ qB
      (fun a => ((w.column.q a : V) : F)) hqQF hqBf a
  have hqUPoint : ∀ a, qU a =
      pointLocalToCommonOpen (A := B) M f e g (qT a) := by
    have hroute := pointLocal_commonOpen_column (A := B) M f e g qQ qB hqA
      qT (fun a => rfl)
    intro a
    exact (hroute a).symm
  have hxj : componentCoordinate P j ≠ 0 :=
    actualWitness_selected_coordinate_ne_zero hm P w j hchart
  let φ := originalAffineChartToCommonOpen P j hxj hsel M f e
  have hchartU := A0NormalizedProjectiveCoordinates.q_column_commonOpen_coordinates P j hxj hsel M f e qQ
    hqchartQ' hq0 (fun i hij => hqvars i hij)
  let axis : Fin m := ⟨0, hm⟩
  have hq0B : qB 0 = algebraMap Q B g := by
    rw [hqA 0, hq0]
  have hfactor := commonOpen_factors_ne_zero_of_tiltedProduct
    (k := k) (d := Fintype.card t) (A := B) M f e g eM α
    rB (fB * rB) (qB 0) (qB axis.succ) rfl hq0B havoid
  rcases hfactor with ⟨hf, hg, hcomp, hgroundB, hbadU, hrU, hq0U, hq1U⟩
  let rhoA := originalToPointLocalFinSuccArcLaurentSeries
    (k := k) (d := Fintype.card t) (A := B) M eM α
  let hunitM : ∀ b, b ∉ M → IsUnit (rhoA b) := fun b hb => by
    let T := Localization.AtPrime M
    have hu : IsUnit (algebraMap B T b) :=
      IsLocalization.map_units T (M := M.primeCompl) ⟨b, hb⟩
    change IsUnit
      ((pointLocalFinSuccArcLaurentSeries (k := k) (d := Fintype.card t)
        (A := B) M eM α).toRingHom (algebraMap B T b))
    exact IsUnit.map _ hu
  let rhoU := genericArcToGenericOpenExtraAwayB M f e rhoA hf hunitM g hg
  have hcomp' : rhoU.comp (genericOpenExtraAwayBMap M f e g) = rhoA := hcomp
  have hgroundB' : (rhoU.comp (genericOpenExtraAwayBMap M f e g)).comp
      (algebraMap k B) = algebraMap k (LaurentSeries k) := hgroundB
  letI : Algebra R Cq :=
    ((algebraMap B Cq).comp (algebraMap R B)).toAlgebra
  letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
  letI : Algebra k U := Algebra.compHom U (algebraMap k R)
  letI : SMul R U := (inferInstance : Algebra R U).toSMul
  letI : SMul k U := (inferInstance : Algebra k U).toSMul
  letI : IsScalarTower k R U := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    rfl
  letI : Algebra.FormallyEtale R U := by
    simpa [U, Cq] using formallyEtale_genericOpenExtraAway_of_pointLocal M f e g
  have hcols := actual_option_columns (k := k) (d := d) (A := B)
    M f e g eM α hf hunitM hg m qT qU hqUPoint
  rcases hcols with ⟨hposition, ⟨htransverseUU, hrawUU⟩⟩
  let qPre : Fin (m + 1) → MvPowerSeries (Fin (d + 1)) k := fun i =>
    PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
      (k := k) (B := B) (d := d) M eM (qT i)
  have hchartPre : qPre C.chart = 1 := by
    simp [qPre, qT, hqchartB]
  have hgroundCoeff : (algebraMap B F).comp (algebraMap k B) = algebraMap k F := by
    ext c
    change ((coeff c : B) : F) = algebraMap k F c
    change ((qToB (algebraMap k Q c) : B) : F) = algebraMap k F c
    exact coe_chartSubalgebraToIntegralClosure Q (algebraMap k Q c)
  have hEvalB : MvPolynomial.eval₂ (algebraMap k B) qB
      (LocalizedProjectiveChartTransition.homogenizeAtZero p) = rB := by
    apply Subtype.ext
    change algebraMap B F
        (MvPolynomial.eval₂ (algebraMap k B) qB (LocalizedProjectiveChartTransition.homogenizeAtZero p)) =
      (r : F)
    calc
      _ = MvPolynomial.eval₂
          ((algebraMap B F).comp (algebraMap k B))
          (algebraMap B F ∘ qB) (LocalizedProjectiveChartTransition.homogenizeAtZero p) :=
            MvPolynomial.eval₂_comp_left (algebraMap B F)
              (algebraMap k B) qB (LocalizedProjectiveChartTransition.homogenizeAtZero p)
      _ = MvPolynomial.eval₂ (algebraMap k F)
          (fun a => ((w.column.q a : V) : F)) (LocalizedProjectiveChartTransition.homogenizeAtZero p) := by
            rw [hgroundCoeff]
            congr 1
            funext a
            exact hqBf a
      _ = MvPolynomial.eval (fun a => ((w.column.q a : V) : F))
          (MvPolynomial.map (algebraMap k F) (LocalizedProjectiveChartTransition.homogenizeAtZero p)) :=
            (MvPolynomial.eval_map (algebraMap k F)
              (fun a => ((w.column.q a : V) : F)) (LocalizedProjectiveChartTransition.homogenizeAtZero p)).symm
      _ = (r : F) := hrF.symm
  have hcoords : ∀ i, qU i = genericOpenExtraAwayBMap M f e g (qB i) := by
    intro i
    calc
      qU i = pointLocalToCommonOpen (A := B) M f e g (qT i) := hqUPoint i
      _ = pointLocalToCommonOpen (A := B) M f e g
          (algebraMap B (Localization.AtPrime M) (qB i)) := rfl
      _ = genericOpenExtraAwayBMap M f e g (qB i) := by
        have h := congrArg (fun φ : B →+* U => φ (qB i))
          (pointLocalToCommonOpen_comp_algebraMap (A := B) M f e g)
        simpa only [RingHom.comp_apply] using h
  let qL : Fin (m + 1) → LaurentSeries k :=
    laurentColumn (fun i => tiltedArc α (qPre i))
  have hpositionL : ∀ i, rhoU (qU i) = qL i := by
    intro i
    simpa [qL, laurentColumn] using hposition i
  have hbaseMap : (genericOpenExtraAwayBMap M f e g).comp
      (algebraMap k B) = algebraMap k U := by
    apply RingHom.ext
    intro c
    change genericOpenExtraAwayBMap M f e g (algebraMap k B c) =
      algebraMap R U (algebraMap k R c)
    rw [← fFin.commutes c]
    rfl
  have hgroundU : rhoU.comp (algebraMap k U) = algebraMap k (LaurentSeries k) := by
    rw [← hbaseMap]
    exact hgroundB'
  have hcolumnsL := actual_option_columns_to_laurent
    (k := k) (d := d) (A := B) (U := U) (M := M) eM
    (algebraMap (PowerSeries k) (LaurentSeries k)) rhoU hgroundU
    α qT qU hposition htransverseUU hrawUU
  rcases hcolumnsL with ⟨_hpositionL, ⟨htransverse, hraw⟩⟩
  have hEval := eval_map_eq_arc_eval₂
    (genericOpenExtraAwayBMap M f e g) rhoU hgroundB' qB qU qL
    hcoords hpositionL (LocalizedProjectiveChartTransition.homogenizeAtZero p)
  have hnumerator : MvPolynomial.eval qL
      (MvPolynomial.map (algebraMap k (LaurentSeries k))
        (LocalizedProjectiveChartTransition.homogenizeAtZero p)) ≠ 0 := by
    rw [hEval, hEvalB]
    exact hrU
  let A₀ := MvPolynomial (Fin m) k ⧸ P.asIdeal
  have hphiGround : φ.comp (algebraMap k A₀) = algebraMap k U := by
    have hcanonical : φ.comp (algebraMap k A₀) =
        (algebraMap Q U).comp (algebraMap k Q) :=
      originalAffineChartToCommonOpen_groundMap P j hxj hsel M f e
    have hQ := genericOpenExtraAway_base_map_agrees M f e g
    apply RingHom.ext
    intro c
    calc
      φ (algebraMap k A₀ c) = algebraMap Q U (algebraMap k Q c) :=
        congrArg (fun h : k →+* U => h c) hcanonical
      _ = genericOpenExtraAwayBMap M f e g
          (algebraMap Q B (algebraMap k Q c)) :=
        (congrArg (fun h : Q →+* U => h (algebraMap k Q c)) hQ).symm
      _ = genericOpenExtraAwayBMap M f e g (algebraMap k B c) := rfl
      _ = algebraMap k U c := congrArg (fun h : k →+* U => h c) hbaseMap
  let quotientAlgebra : Algebra A₀ U := φ.toAlgebra
  letI : Algebra A₀ U := quotientAlgebra
  letI : SMul A₀ U := quotientAlgebra.toSMul
  let polynomialAlgebra : Algebra (MvPolynomial (Fin m) k) U :=
    Algebra.compHom U (algebraMap (MvPolynomial (Fin m) k) A₀)
  letI : Algebra (MvPolynomial (Fin m) k) U := polynomialAlgebra
  letI : SMul (MvPolynomial (Fin m) k) U := polynomialAlgebra.toSMul
  letI : IsScalarTower k A₀ U :=
    IsScalarTower.of_algebraMap_eq' hphiGround.symm
  letI : IsScalarTower (MvPolynomial (Fin m) k) A₀ U :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower k (MvPolynomial (Fin m) k) U :=
    IsScalarTower.to₁₂₄ k (MvPolynomial (Fin m) k) A₀ U
  letI : Algebra.FormallyEtale A₀ U := by
    exact formallyEtale_originalAffineChartToCommonOpen P j hxj hsel M f e
  let beta : Fin d → k := fun z =>
    Stafford38.Geometry.PrescribedAffineResidueCompletion.residueCoordinates
      M eM (some z)
  let u₀ : MvPowerSeries (Fin (d + 1)) k :=
    PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
      (k := k) (B := B) (d := d) M eM u₀'
  let u₁ : MvPowerSeries (Fin (d + 1)) k :=
    PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
      (k := k) (B := B) (d := d) M eM u₁'
  exact axis_mem_smoothConormalFibreProjection_closure_of_actual_columns
    (k := k) (E := U) (n := m) (d := d) (I := P.asIdeal) rhoU
    hgroundU
    qU qPre rows C.chart axis w.differential.core.D.a
    (w.differential.core.D.a + w.differential.core.D.e) beta α u₀ u₁
    hchartPre hdata hpositionL htransverse hraw
    hchartU p fbar hpq hsmooth hnumerator

end Stafford38.Geometry.ActualSameWitnessAffineFibreClosure

end
