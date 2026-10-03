module
public import Stafford38.Geometry.SameWitness.CommonOpenEtale

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.SameWitness.CommonOpenEtaleConsumer

open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.SameWitness

universe u

/-- Literal consumer for the two formally-etale common-open maps retained
from the same selected chart and ground-point arc. -/
theorem nonempty_commonOpenEtaleData_consumer
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords) :
    Nonempty (CommonOpenEtaleData hm P w setup coords arc) := by
  exact nonempty_commonOpenEtaleData hm P w setup coords arc

#print axioms nonempty_commonOpenEtaleData
#print axioms nonempty_commonOpenEtaleData_consumer

end Stafford38.Geometry.SameWitness.CommonOpenEtaleConsumer

end
