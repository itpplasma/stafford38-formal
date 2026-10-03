module
public import Stafford38.Geometry.SameWitness.ChartSetup

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.SameWitness.ChartSetupConsumer

open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.SameWitness

universe u

/-- Literal consumer for the chart and away data extracted from the smooth
open and the same retained visible-frame witness. -/
theorem nonempty_chartSetup_consumer
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hsmoothOpen : ∃ fbar : MvPolynomial (Fin m) k ⧸ P.asIdeal,
      fbar ≠ 0 ∧ Algebra.Smooth k (Localization.Away fbar)) :
    Nonempty (ChartSetup hm P w) := by
  exact nonempty_chartSetup hm P w hsmoothOpen

#print axioms nonempty_chartSetup
#print axioms nonempty_chartSetup_consumer

end Stafford38.Geometry.SameWitness.ChartSetupConsumer
