module
public import Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
public import Stafford38.Geometry.ProjectiveChartSameFieldOverlap
public import Stafford38.Geometry.AsymptoticChartArcAdapter
public import Stafford38.Geometry.ChartGenericPointFractionRing
public import Stafford38.Geometry.ComponentFunctionFieldBoundary
public import Stafford38.Geometry.ComponentProjectiveClosure
public import Stafford38.Geometry.ComponentProjectiveChartKernel
public import Stafford38.Geometry.ActualWitnessSelectedChartBinding


@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualSelectedNormalizationChartTransport

open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ProjectiveChartSameFieldOverlap
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ActualWitnessSelectedChartBinding
open Stafford38.Geometry.AsymptoticDivisorExistence

universe u

noncomputable def actual_witness_selected_chart_quotient_equiv
    {k : Type u} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (j : Fin m) (hchart : w.column.chart = Fin.succ j) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : Algebra V F := V.subtype.toAlgebra
    let Q : Subalgebra k (ComponentFractionField P) := actualSelectedChartAlgebra P w
    SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q := by
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : Algebra V F := V.subtype.toAlgebra
  let Qj : Subalgebra k F := Algebra.adjoin k (Set.range
    (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
  let Q : Subalgebra k F := actualSelectedChartAlgebra P w
  have hpoint : componentProjectivePoint P (Fin.succ j) ≠ 0 := by
    have hxj := actualWitness_selected_coordinate_ne_zero hm P w j hchart
    simpa [componentProjectivePoint] using hxj
  have hselJ := componentChartEquationQuotient_equiv_genericSubalgebra
    P (Fin.succ j) (SelectedAffineCoordinateEquiv j) hpoint
  have hQ : Q = Qj := by
    change Algebra.adjoin k (Set.range
      (chartGenericPoint P w.column.chart
        (chartAffineCoordinateEquiv w.column.chart))) =
      Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
    rw [hchart]
  exact hselJ.trans (Subalgebra.equivOfEq Qj Q hQ.symm)

theorem actual_witness_selected_chart_q_coordinates_in_actual_algebra
    {k : Type u} [Field k] [CharZero k] {m : ℕ}
    (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (j : Fin m) (hchart : w.column.chart = Fin.succ j) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : Algebra V F := V.subtype.toAlgebra
    let Q : Subalgebra k F := actualSelectedChartAlgebra P w
    let hsel := actual_witness_selected_chart_quotient_equiv P w j hchart
    ∃ qQ : Fin (m + 1) → Q,
      qQ (Fin.succ j) = 1 ∧
      (∀ a, (qQ a : F) = ((C.q a : C.W.place.valuation.toSubring) : F)) ∧
      qQ 0 = hsel (selectedAffineChartDenominator P j) ∧
      ∀ i : Fin m, ∀ hij : i ≠ j,
        qQ (Fin.succ i) = hsel (selectedAffineChartVariableClass P j i hij) := by
  classical
  dsimp only
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : Algebra V F := V.subtype.toAlgebra
  let Qj : Subalgebra k (ComponentFractionField P) := Algebra.adjoin k (Set.range
    (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
  let Q : Subalgebra k (ComponentFractionField P) := actualSelectedChartAlgebra P w
  let hselJ := componentChartEquationQuotient_equiv_genericSubalgebra P
    (Fin.succ j) (SelectedAffineCoordinateEquiv j)
    (by
      have hxj := actualWitness_selected_coordinate_ne_zero hm P w j hchart
      simpa [componentProjectivePoint] using hxj)
  let hQ : Q = Qj := by
    change Algebra.adjoin k (Set.range
      (chartGenericPoint P w.column.chart
        (chartAffineCoordinateEquiv w.column.chart))) =
      Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
    rw [hchart]
  let eSub : Qj ≃ₐ[k] Q := Subalgebra.equivOfEq Qj Q hQ.symm
  let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q := hselJ.trans eSub
  obtain ⟨qJ, hchartJ, hcoerceJ, hzeroJ, hrowsJ⟩ :=
    ActualWitnessSelectedChartBinding.actual_selected_chart_q_coordinates
      hm P w j hchart
  refine ⟨fun a => eSub (qJ a), ?_, ?_, ?_, ?_⟩
  · simpa using congrArg eSub hchartJ
  · intro a
    calc
      ((eSub (qJ a) : Q) : F) = (qJ a : Qj) := by
        change ((Qj.equivOfEq Q hQ.symm) (qJ a) : F) = _
        simp only [Subalgebra.equivOfEq_apply]
      _ = ((C.q a : V) : F) := hcoerceJ a
  · calc
      eSub (qJ 0) = eSub (hselJ (selectedAffineChartDenominator P j)) :=
        congrArg eSub hzeroJ
      _ = hsel (selectedAffineChartDenominator P j) := rfl
  · intro i hij
    calc
      eSub (qJ (Fin.succ i)) =
          eSub (hselJ (selectedAffineChartVariableClass P j i hij)) :=
        congrArg eSub (hrowsJ i hij)
      _ = hsel (selectedAffineChartVariableClass P j i hij) := rfl

end Stafford38.Geometry.ActualSelectedNormalizationChartTransport
