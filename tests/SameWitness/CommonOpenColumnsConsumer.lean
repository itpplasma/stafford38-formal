import Stafford38.Geometry.SameWitness.CommonOpenColumns

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.GeneralDivisorialVisibleFrame

universe u

/-- Literal consumer for same-witness common-open derivatives and numerator. -/
theorem commonOpenColumnsData_consumer
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords)
    (etale : CommonOpenEtaleData hm P w setup coords arc)
    (positions : CommonOpenPositionData hm P w setup coords arc) :
    CommonOpenColumnsData hm P w setup coords arc etale positions :=
  commonOpenColumnsData_of_arc hm P w setup coords arc etale positions

#print axioms commonOpenColumnsData_of_arc
#print axioms commonOpenColumnsData_consumer

end Stafford38.Geometry.SameWitness

end
