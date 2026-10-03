module
public import Stafford38.Geometry.ActualCommonOpenCompletionDerivation
public import Stafford38.Geometry.A0ChartGeneratorCoordinates
public import Stafford38.Geometry.SelectedResidueNormalizationLocalization

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.ActualCommonOpenColumnGlue

open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.A0ChartGeneratorCoordinates
open Stafford38.Geometry.SelectedResidueCoefficientLocalization

noncomputable section

universe u v w z

/-- The actual localization maps identify a column transported from the
chart algebra with the same column transported through the point-local ring.
The only coordinate equality used here is equality in the original ring `A`;
there is no separately assumed common-open/point-local compatibility. -/
theorem pointLocal_commonOpen_column
    {Q : Type u} [CommRing Q]
    {A : Type v} [CommRing A] [Algebra Q A]
    {ι : Type z}
    (M : Ideal A) [M.IsPrime]
    (f : Q) (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    (qQ : ι → Q) (qA : ι → A)
    (hA : ∀ i, qA i = algebraMap Q A (qQ i))
    (qT : ι → Localization.AtPrime M)
    (hT : ∀ i, qT i = algebraMap A (Localization.AtPrime M) (qA i)) :
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq U := inferInstance
    letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
    ∀ i, pointLocalToCommonOpen (A := A) M f e g (qT i) =
      algebraMap Q U (qQ i) := by
  dsimp
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq U := inferInstance
  letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
  have hroute := pointLocalToCommonOpen_comp_algebraMap (A := A) M f e g
  intro i
  rw [hT i]
  calc
    pointLocalToCommonOpen (A := A) M f e g
        (algebraMap A (Localization.AtPrime M) (qA i)) =
      genericOpenExtraAwayBMap M f e g (qA i) := by
        have hi := congrArg (fun φ : A →+* U => φ (qA i)) hroute
        simpa only [RingHom.comp_apply] using hi
    _ = genericOpenExtraAwayBMap M f e g (algebraMap Q A (qQ i)) :=
      congrArg (genericOpenExtraAwayBMap M f e g) (hA i)
    _ = algebraMap Q U (qQ i) := by
      change genericOpenExtraAwayBMap M f e g (algebraMap Q A (qQ i)) =
        algebraMap Cq U (algebraMap Q Cq (qQ i))
      exact genericOpenExtraAwayBMap_algebraMap M f e g (qQ i)

/-- The unique inclusion of an affine chart element into its integral closure
is recovered from its value in the common component fraction field. -/
theorem actualColumn_eq_chartImage
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    (Q : Subalgebra k F) {ι : Type z}
    (qQ : ι → Q)
    (qB : ι → integralClosure Q.toSubring F)
    (v : ι → F)
    (hqQ : ∀ i, (qQ i : F) = v i)
    (hqB : ∀ i, ((qB i : integralClosure Q.toSubring F) : F) = v i) :
    ∀ i, qB i = chartSubalgebraToIntegralClosure Q (qQ i) := by
  intro i
  apply Subtype.ext
  exact (hqB i).trans (hqQ i).symm

/-- For one actual integral-closure column, the chart-algebra and point-local
routes to the same common open agree. The two F-valued specifications are
the existing same-witness producers' outputs; this theorem derives the
intervening equality in the integral closure by subtype extensionality. -/
theorem actual_integral_column_commonOpen_eq_pointLocal
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    (Q : Subalgebra k F) {ι : Type z}
    (M : Ideal (integralClosure Q.toSubring F)) [M.IsPrime]
    (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away
        (algebraMap Q (integralClosure Q.toSubring F) f))
    (g : Q)
    (qQ : ι → Q)
    (qB : ι → integralClosure Q.toSubring F)
    (v : ι → F)
    (hqQ : ∀ i, (qQ i : F) = v i)
    (hqB : ∀ i, ((qB i : integralClosure Q.toSubring F) : F) = v i)
    (qC : ι → genericOpenExtraAwayB M f e g)
    (hqC : ∀ i,
      algebraMap Q (genericOpenExtraAwayB M f e g) (qQ i) = qC i)
    (qT : ι → Localization.AtPrime M)
    (hqT : ∀ i,
      qT i = algebraMap (integralClosure Q.toSubring F)
        (Localization.AtPrime M) (qB i)) :
    ∀ i, qC i = pointLocalToCommonOpen
      (A := integralClosure Q.toSubring F) M f e g (qT i) := by
  classical
  let B := integralClosure Q.toSubring F
  let qToB : Q →+* B := chartSubalgebraToIntegralClosure Q
  letI : Algebra Q B := qToB.toAlgebra
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq U := inferInstance
  letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
  have hqB' : ∀ i, qB i = algebraMap Q B (qQ i) := by
    intro i
    calc
      qB i = qToB (qQ i) := actualColumn_eq_chartImage Q qQ qB v hqQ hqB i
      _ = algebraMap Q B (qQ i) := rfl
  have hroute := pointLocal_commonOpen_column
    (A := B) M f e g qQ qB hqB' qT hqT
  intro i
  calc
    qC i = algebraMap Q U (qQ i) := (hqC i).symm
    _ = pointLocalToCommonOpen (A := B) M f e g (qT i) := (hroute i).symm

end
end Stafford38.Geometry.ActualCommonOpenColumnGlue
