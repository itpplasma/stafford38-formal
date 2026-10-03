module
public import Stafford38.Geometry.SameWitness.CommonOpenArcDerivatives
public import Stafford38.Geometry.CommonOpenEvaluation

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.SelectedResidueCoefficientLocalization
open Stafford38.Geometry.ActualOptionColumnBinding
open Stafford38.Geometry.ActualSelectedNormalizationChartTransport
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ActualOptionCommonOpenColumns
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.CommonOpenEvaluation
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.HomogenizedAffineEvaluation
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.LocalizedProjectiveChartTransition

universe u

/-- The retained witness columns satisfy the common-open derivative and
selected-numerator identities required by the endpoint. -/
structure CommonOpenColumnsData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords)
    (etale : CommonOpenEtaleData hm P w setup coords arc)
    (positions : CommonOpenPositionData hm P w setup coords arc) : Prop where
  derivatives : CommonOpenDerivativeData etale.ψU etale.hψEtale arc.rhoU
    arc.hgroundU arc.common.alpha positions.qPre arc.common.qU
  hnumerator : MvPolynomial.eval positions.qL
      (MvPolynomial.map (algebraMap k (LaurentSeries k))
        (homogenizeAtZero setup.p)) ≠ 0

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {m : ℕ} {hm : 0 < m} {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
  {w : GeneralDivisorialVisibleFrameWitness hm P} {setup : ChartSetup hm P w}
  {coords : CoordinatePresentation hm P w setup}
  {arc : CommonOpenArcData hm P w setup coords}
  {etale : CommonOpenEtaleData hm P w setup coords arc}
  {positions : CommonOpenPositionData hm P w setup coords arc}

/-- The transverse derivative identity retained by the abstract certificate. -/
abbrev CommonOpenColumnsData.htransverse
    (data : CommonOpenColumnsData hm P w setup coords arc etale positions) :=
  data.derivatives.htransverse

/-- The raw derivative identity retained by the abstract certificate. -/
abbrev CommonOpenColumnsData.hraw
    (data : CommonOpenColumnsData hm P w setup coords arc etale positions) :=
  data.derivatives.hraw

/-- Homogenized evaluation of the retained projective column is the selected
chart numerator, which stays nonzero on the common-open Laurent arc. -/
theorem commonOpen_selectedNumerator_ne_zero
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords)
    (etale : CommonOpenEtaleData hm P w setup coords arc)
    (positions : CommonOpenPositionData hm P w setup coords arc) :
    MvPolynomial.eval positions.qL
      (MvPolynomial.map (algebraMap k (LaurentSeries k))
        (homogenizeAtZero setup.p)) ≠ 0 := by
  classical
  letI : arc.common.M.IsMaximal := arc.common.hM
  let B := actualSelectedNormalization P w
  let F := ComponentFractionField P
  let qB : Fin (m + 1) → B := actualNormalizedProjectiveColumnInIntegralClosure hm P w
  have hqBspec := actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
  have hqBf : ∀ a, (qB a : F) = (w.column.q a : F) := hqBspec.2.1
  have hgroundCoeff : (algebraMap B F).comp coords.coeff = algebraMap k F := by
    ext c
    change ((coords.coeff c : B) : F) = algebraMap k F c
    rw [coords.hcoeff]
    rfl
  have hEvalB : MvPolynomial.eval₂ coords.coeff qB
      (homogenizeAtZero setup.p) = algebraMap
        (actualSelectedChartAlgebra P w) B setup.r := by
    apply Subtype.ext
    change algebraMap B F (MvPolynomial.eval₂ coords.coeff qB
      (homogenizeAtZero setup.p)) = (setup.r : F)
    calc
      _ = MvPolynomial.eval₂ ((algebraMap B F).comp coords.coeff)
          (fun a => algebraMap B F (qB a)) (homogenizeAtZero setup.p) := by
            exact (MvPolynomial.eval₂_comp_left (algebraMap B F)
              coords.coeff qB (homogenizeAtZero setup.p))
      _ = MvPolynomial.eval₂ (algebraMap k F)
          (fun a => (w.column.q a : F)) (homogenizeAtZero setup.p) := by
            rw [hgroundCoeff]
            congr 1
            funext a
            exact hqBf a
      _ = MvPolynomial.eval (fun a => (w.column.q a : F))
          (MvPolynomial.map (algebraMap k F) (homogenizeAtZero setup.p)) := by
            exact (MvPolynomial.eval_map (algebraMap k F)
              (fun a => (w.column.q a : F)) (homogenizeAtZero setup.p)).symm
      _ = (setup.r : F) := setup.hrF.symm
  have hEval := @eval_map_eq_arc_eval₂ k B arc.common.U (LaurentSeries k)
    (Fin (m + 1)) _ _ _ _ coords.coeff.toAlgebra inferInstance
    (genericOpenExtraAwayBMap arc.common.M setup.f setup.e arc.common.g) arc.rhoU
    arc.hgroundB' qB arc.common.qU positions.qL
    positions.hcoords positions.hpositionL (homogenizeAtZero setup.p)
  have hEval' : MvPolynomial.eval positions.qL
      (MvPolynomial.map (algebraMap k (LaurentSeries k))
        (homogenizeAtZero setup.p)) =
      arc.rhoU (genericOpenExtraAwayBMap arc.common.M setup.f setup.e
        arc.common.g (MvPolynomial.eval₂ coords.coeff qB (homogenizeAtZero setup.p))) := hEval
  rw [hEval', hEvalB]
  exact arc.hrU

/-- Derive the endpoint derivative and numerator facts from the retained
point-local columns without installing scalar actions on selected rings. -/
theorem commonOpenColumnsData_of_arc
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords)
    (etale : CommonOpenEtaleData hm P w setup coords arc)
    (positions : CommonOpenPositionData hm P w setup coords arc) :
    CommonOpenColumnsData hm P w setup coords arc etale positions := by
  exact ⟨commonOpen_arcDerivativeData hm P w setup coords arc etale positions,
    commonOpen_selectedNumerator_ne_zero hm P w setup coords arc etale positions⟩

end Stafford38.Geometry.SameWitness

end
