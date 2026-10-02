import Stafford38.Geometry.ActualCommonOpenColumnGlue

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.ActualCommonOpenColumnGlueConsumer

universe u v

open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.ActualCommonOpenColumnGlue
open Stafford38.Geometry.EtaleGenericOpenTransport

/-- Literal-unit consumer of the point-local/common-open map comparison. -/
theorem literal_unit_column
    {Q : Type u} [CommRing Q]
    {A : Type v} [CommRing A] [Algebra Q A]
    (M : Ideal A) [M.IsPrime]
    (f : Q) (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q) :
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq U := inferInstance
    letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
    pointLocalToCommonOpen (A := A) M f e g
      (algebraMap A (Localization.AtPrime M) (algebraMap Q A (1 : Q))) =
      algebraMap Q U (1 : Q) := by
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq U := inferInstance
  letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
  have h := pointLocal_commonOpen_column
    (A := A) (M := M) (f := f) (e := e) (g := g)
    (qQ := fun _ : Unit => (1 : Q))
    (qA := fun _ : Unit => algebraMap Q A (1 : Q))
    (by intro x; rfl)
    (qT := fun _ : Unit =>
      algebraMap A (Localization.AtPrime M) (algebraMap Q A (1 : Q)))
    (by intro x; rfl)
  simpa using h ()

#print axioms literal_unit_column
#print axioms Stafford38.Geometry.ActualCommonOpenColumnGlue.pointLocal_commonOpen_column
#print axioms Stafford38.Geometry.ActualCommonOpenColumnGlue.actual_integral_column_commonOpen_eq_pointLocal

end Stafford38.Geometry.ActualCommonOpenColumnGlueConsumer
