module
public import Stafford38.Geometry.SameWitness.CommonOpenColumnDerivatives

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
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.HomogenizedAffineEvaluation
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.LocalizedProjectiveChartTransition

universe u

/-- Infer the retained certificate at the kernel-checked application boundary. -/
private noncomputable def retainedArcDerivativeCertificate
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords)
    (etale : CommonOpenEtaleData hm P w setup coords arc)
    (positions : CommonOpenPositionData hm P w setup coords arc) := letI : arc.common.M.IsMaximal := arc.common.hM;
  commonOpen_derivatives_of_retainedArc (k := k) (B := actualSelectedNormalization P w) (Q := actualSelectedChartAlgebra P w) (d := @Fintype.card coords.t coords.htFinite) (n := m)
  coords.coeff (chartSubalgebraToIntegralClosure (actualSelectedChartAlgebra P w)) coords.fFin coords.hBfinite arc.common.M
  setup.f setup.e arc.common.g arc.common.eM arc.common.hEtM
  arc.common.alpha arc.rhoA arc.hf arc.hunitM arc.hg arc.hcanonicalRhoA
  arc.common.qT arc.common.qU arc.common.hqUPoint
  etale.ψU etale.hψAction etale.hψEtale
  arc.rhoU arc.hgroundU arc.hcanonicalRhoU
  positions.qPre positions.hqPre

/-- The retained arc yields exactly the prescribed concrete derivative certificate. -/
theorem commonOpen_arcDerivativeData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords)
    (etale : CommonOpenEtaleData hm P w setup coords arc)
    (positions : CommonOpenPositionData hm P w setup coords arc) :
    CommonOpenDerivativeData etale.ψU etale.hψEtale arc.rhoU
      arc.hgroundU arc.common.alpha positions.qPre arc.common.qU := by
  exact retainedArcDerivativeCertificate hm P w setup coords arc etale positions

end Stafford38.Geometry.SameWitness

end
