import Stafford38.Geometry.SameWitness.CommonOpenPositions

open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.SameWitness

universe u

theorem commonOpenPositionData_of_arc_consumer
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords) :
    CommonOpenPositionData hm P w setup coords arc := by
  exact commonOpenPositionData_of_arc hm P w setup coords arc

#print axioms commonOpenPositionData_of_arc_consumer
