module
public import Stafford38.Geometry.SameWitness.CommonOpen

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ActualSameWitnessGroundPointCompletion

universe u

/-- Literal consumer for the same-witness common-open construction. -/
theorem nonempty_commonOpenData_consumer
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (hpoint : actualSameWitnessGroundPointOutput hm P w) :
    Nonempty (CommonOpenData hm P w setup coords) :=
  nonempty_commonOpenData hm P w setup coords hpoint

#print axioms nonempty_commonOpenData_consumer

end Stafford38.Geometry.SameWitness

end
