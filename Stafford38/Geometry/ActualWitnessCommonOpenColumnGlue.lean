module
public import Stafford38.Geometry.ActualCommonOpenColumnGlue
public import Stafford38.Geometry.ActualOptionColumnBinding
public import Stafford38.Geometry.ActualWitnessSelectedChartBinding
public import Stafford38.Geometry.AsymptoticChartArcAdapter

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.ActualWitnessCommonOpenColumnGlue

open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.ActualCommonOpenColumnGlue
open Stafford38.Geometry.ActualWitnessSelectedChartBinding
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ActualOptionColumnBinding
open Stafford38.Geometry.SelectedResidueCoefficientLocalization
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ProjectiveChartSameFieldOverlap

noncomputable section

universe u v w

/-- The selected-chart common-open column from the retained witness equals
its point-local image in the same integral closure. The chart-coordinate tuple
is obtained from the actual witness producer, and the map to the closure is
the canonical inclusion of the chart algebra. -/
theorem actual_witness_commonOpen_eq_pointLocal
    {k : Type u} [Field k] [CharZero k] {m : ℕ}
    (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (j : Fin m) (hchart : w.column.chart = Fin.succ j)
    (M : Ideal (integralClosure
      (Algebra.adjoin k (Set.range (chartGenericPoint P (Fin.succ j)
        (SelectedAffineCoordinateEquiv j)))).toSubring
      (ComponentFractionField P)))
    [M.IsPrime]
    (f : Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j))))
    (e : Localization.Away f ≃ₐ[
      Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))]
      Localization.Away (algebraMap _
        (integralClosure
          (Algebra.adjoin k (Set.range (chartGenericPoint P (Fin.succ j)
            (SelectedAffineCoordinateEquiv j)))).toSubring
          (ComponentFractionField P)) f)) :
    let F := ComponentFractionField P
    let W := w.column.W
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : Algebra V F := V.subtype.toAlgebra
    let Q : Subalgebra k F := Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
    let B := integralClosure Q.toSubring F
    letI : Algebra Q B := (chartSubalgebraToIntegralClosure Q).toAlgebra
    let hxj := actualWitness_selected_coordinate_ne_zero hm P w j hchart
    let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
      componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
        (SelectedAffineCoordinateEquiv j) (by
          simpa [componentProjectivePoint] using hxj)
    let g := hsel (selectedAffineChartDenominator P j)
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Semiring U := (inferInstance : CommSemiring U).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq U := inferInstance
    letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
    let qU : Fin (m + 1) → U := Fin.cases
      (algebraMap Cq U (algebraMap Q Cq g))
      (fun i => if hij : i = j then 1 else
        algebraMap Cq U (algebraMap Q Cq
          (hsel (selectedAffineChartVariableClass P j i hij))))
    ∃ qQ : Fin (m + 1) → Q,
      qQ (Fin.succ j) = 1 ∧
      (∀ a, ((qQ a : Q) : F) =
        ((w.column.q a : w.column.W.place.valuation.toSubring) : F)) ∧
      ∀ a, qU a = pointLocalToCommonOpen (A := B) M f e g
        (algebraMap B (Localization.AtPrime M)
          (chartSubalgebraToIntegralClosure Q (qQ a))) := by
  classical
  dsimp only
  let F := ComponentFractionField P
  let W := w.column.W
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : Algebra V F := V.subtype.toAlgebra
  let Q : Subalgebra k F := Algebra.adjoin k (Set.range
    (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
  let B := integralClosure Q.toSubring F
  let qToB := chartSubalgebraToIntegralClosure Q
  letI : Algebra Q B := qToB.toAlgebra
  let hxj := actualWitness_selected_coordinate_ne_zero hm P w j hchart
  let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
    componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
      (SelectedAffineCoordinateEquiv j) (by
        simpa [componentProjectivePoint] using hxj)
  let g := hsel (selectedAffineChartDenominator P j)
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Semiring U := (inferInstance : CommSemiring U).toSemiring
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq U := inferInstance
  letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
  let qU : Fin (m + 1) → U := Fin.cases
    (algebraMap Cq U (algebraMap Q Cq g))
    (fun i => if hij : i = j then 1 else
      algebraMap Cq U (algebraMap Q Cq
          (hsel (selectedAffineChartVariableClass P j i hij))))
  obtain ⟨qQ, hqchart, hqF, _, _, hqU⟩ :=
    actualWitness_commonOpen_q_coordinates hm P w j hchart M f e
  let Qcolumn : Subalgebra k F := Algebra.adjoin k (Set.range
    (chartGenericPoint P w.column.chart
      (chartAffineCoordinateEquiv w.column.chart)))
  let Bcolumn := integralClosure Qcolumn.toSubring F
  let hQ : Qcolumn = Q := by
    change Algebra.adjoin k (Set.range
      (chartGenericPoint P w.column.chart
        (chartAffineCoordinateEquiv w.column.chart))) = Q
    rw [hchart]
  let hQSubring : Qcolumn.toSubring = Q.toSubring := congrArg
    Subalgebra.toSubring hQ
  let qBraw : Fin (m + 1) → Bcolumn :=
    actualNormalizedProjectiveColumnInIntegralClosure hm P w
  let qB : Fin (m + 1) → B := fun a =>
    ⟨(qBraw a : F), by
      change IsIntegral Q.toSubring (qBraw a : F)
      rw [← hQSubring]
      exact (qBraw a).property⟩
  let v : Fin (m + 1) → F := fun a =>
    ((w.column.q a : w.column.W.place.valuation.toSubring) : F)
  have hqBraw : ∀ a, ((qBraw a : Bcolumn) : F) = v a := by
    intro a
    have hs := actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
    have h := hs.2.1 a
    simpa [qBraw, Qcolumn, Bcolumn, F, v] using h
  have hqB : ∀ a, ((qB a : B) : F) = v a := by
    intro a
    change ((qBraw a : Bcolumn) : F) = v a
    exact hqBraw a
  have hqBimage : ∀ a, qB a = qToB (qQ a) :=
    actualColumn_eq_chartImage Q qQ qB v hqF hqB
  have hbridge := actual_integral_column_commonOpen_eq_pointLocal
    Q M f e g qQ qB v hqF hqB qU hqU
    (fun a => algebraMap B (Localization.AtPrime M) (qB a))
    (by intro a; rfl)
  refine ⟨qQ, hqchart, hqF, ?_⟩
  intro a
  calc
    qU a = pointLocalToCommonOpen (A := B) M f e g
        (algebraMap B (Localization.AtPrime M) (qB a)) := hbridge a
    _ = pointLocalToCommonOpen (A := B) M f e g
        (algebraMap B (Localization.AtPrime M) (qToB (qQ a))) := by
      rw [hqBimage a]

end
end Stafford38.Geometry.ActualWitnessCommonOpenColumnGlue
