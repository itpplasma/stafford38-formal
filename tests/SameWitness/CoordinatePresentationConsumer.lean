module

public import Stafford38.Geometry.SameWitness.CoordinatePresentation

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
open Stafford38.Geometry.GeneralDivisorialVisibleFrame

universe u

theorem nonempty_coordinatePresentation_consumer
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (hpoint : actualSameWitnessGroundPointOutput hm P w) :
    Nonempty (CoordinatePresentation hm P w setup) :=
  nonempty_coordinatePresentation hm P w setup hpoint

#print axioms nonempty_coordinatePresentation_consumer

end Stafford38.Geometry.SameWitness

end
