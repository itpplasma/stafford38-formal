import Stafford38.Geometry.SameWitness.CommonOpenArc

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.GeneralDivisorialVisibleFrame

universe u

theorem exists_commonOpenArcData_consumer
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (common : CommonOpenData hm P w setup coords) :
    Nonempty (CommonOpenArcData hm P w setup coords) :=
  exists_commonOpenArcData hm P w setup coords common

#print axioms exists_commonOpenArcData_consumer

end Stafford38.Geometry.SameWitness

end
