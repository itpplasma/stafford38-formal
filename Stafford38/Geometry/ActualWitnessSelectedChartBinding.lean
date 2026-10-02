import Stafford38.Geometry.A0NormalizedProjectiveCoordinates
import Stafford38.Geometry.AffineComponentCoordinateSplit
import Stafford38.Geometry.AsymptoticDivisorExistence
import Stafford38.Geometry.ActualChartValuationImage
import Stafford38.Geometry.ComponentProjectiveChartFactorization
import Stafford38.Geometry.ComponentProjectiveChartKernel
import Stafford38.Geometry.ComponentProjectiveClosure
import Stafford38.Geometry.EtaleGenericOpenExtraAwayB
import Stafford38.Geometry.EtaleGenericOpenTransport
import Stafford38.Geometry.GeneralDivisorialVisibleFrameResidueSupport

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Stafford38.Geometry.ActualWitnessSelectedChartBinding

open IsLocalRing
open Stafford38.Geometry.A0ChartFormalEtale
open Stafford38.Geometry.A0NormalizedProjectiveCoordinates
open Stafford38.Geometry.ActualChartValuationImage
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.ProjectiveChartSameFieldOverlap

universe u v w

/-- The canonical chart quotient equivalence sends each polynomial generator
to its named generic-chart coordinate. -/
theorem componentChartEquiv_mk_X
    {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) (i : Fin m) :
    componentChartEquationGenericPointMap P chart e hchart
      (Ideal.Quotient.mk (componentChartEquationIdeal P chart e)
        (MvPolynomial.X i)) = chartGenericPoint P chart e i := by
  simpa using componentChartEquationGenericPointMap_mk P chart e hchart
    (MvPolynomial.X i)

/-- The selected chart's distinguished denominator is the generic coordinate
at the original zeroth projective index. -/
theorem selected_denominator_eq_generic_coordinate
    {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hchart : componentProjectivePoint P (Fin.succ j) ≠ 0) :
    let e := SelectedAffineCoordinateEquiv j
    let Q := Algebra.adjoin k (Set.range (chartGenericPoint P (Fin.succ j) e))
    let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
      componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j) e hchart
    hsel (selectedAffineChartDenominator P j) =
      ⟨chartGenericPoint P (Fin.succ j) e (selectedAffineChartOrigin j),
        Algebra.subset_adjoin (R := k) (A := ComponentFractionField P)
          (Set.mem_range_self (selectedAffineChartOrigin j))⟩ := by
  dsimp only
  let e := SelectedAffineCoordinateEquiv j
  let Q := Algebra.adjoin k (Set.range (chartGenericPoint P (Fin.succ j) e))
  let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
    componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j) e hchart
  apply Subtype.ext
  change componentChartEquationGenericPointMap P (Fin.succ j) e hchart
      (Ideal.Quotient.mk (componentChartEquationIdeal P (Fin.succ j) e)
        (MvPolynomial.X (selectedAffineChartOrigin j))) = _
  exact componentChartEquiv_mk_X P (Fin.succ j) e hchart
    (selectedAffineChartOrigin j)

/-- A selected non-chart affine variable is the matching generic chart
coordinate under the canonical quotient equivalence. -/
theorem selected_variable_eq_generic_coordinate
    {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j i : Fin m)
    (hij : i ≠ j)
    (hchart : componentProjectivePoint P (Fin.succ j) ≠ 0) :
    let e := SelectedAffineCoordinateEquiv j
    let Q := Algebra.adjoin k (Set.range (chartGenericPoint P (Fin.succ j) e))
    let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
      componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j) e hchart
    hsel (selectedAffineChartVariableClass P j i hij) =
      ⟨chartGenericPoint P (Fin.succ j) e
          ((SelectedAffineCoordinateEquiv j).symm ⟨i.succ, by simpa using hij⟩),
        Algebra.subset_adjoin (R := k) (A := ComponentFractionField P)
          (Set.mem_range_self
            ((SelectedAffineCoordinateEquiv j).symm ⟨i.succ, by simpa using hij⟩))⟩ := by
  dsimp only
  let e := SelectedAffineCoordinateEquiv j
  let Q := Algebra.adjoin k (Set.range (chartGenericPoint P (Fin.succ j) e))
  let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
    componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j) e hchart
  apply Subtype.ext
  change componentChartEquationGenericPointMap P (Fin.succ j) e hchart
      (Ideal.Quotient.mk (componentChartEquationIdeal P (Fin.succ j) e)
        (MvPolynomial.X ((SelectedAffineCoordinateEquiv j).symm
          ⟨i.succ, by simpa using hij⟩))) = _
  exact componentChartEquiv_mk_X P (Fin.succ j) e hchart
    ((SelectedAffineCoordinateEquiv j).symm ⟨i.succ, by simpa using hij⟩)

/-- The retained witness's actual normalized column, when read in the
canonical selected-chart quotient algebra Q, is the same tuple as the
canonical quotient equivalence: q₀ is its distinguished denominator, qᵢ is
the selected chart class for i≠j, and qⱼ=1. -/
theorem actual_selected_chart_q_coordinates
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
    let e := SelectedAffineCoordinateEquiv j
    let Q := Algebra.adjoin k (Set.range (chartGenericPoint P (Fin.succ j) e))
    let hxj : componentCoordinate P j ≠ 0 := by
      have hp : componentProjectivePoint P (Fin.succ j) ≠ 0 := by
        have hc : componentProjectivePoint P C.chart ≠ 0 := by
          intro hz
          have hqchartF : ((C.q C.chart : V) : F) = 1 :=
            congrArg (fun z : V => (z : F)) C.chart_one
          have hqzeroF : ((C.q C.chart : V) : F) = 0 := by
            rw [C.q_commonScale C.chart, hz]
            simp
          exact one_ne_zero (hqchartF.symm.trans hqzeroF)
        simpa [C, hchart] using hc
      simpa [componentProjectivePoint] using hp
    let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
      componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j) e (by
        simpa [componentProjectivePoint] using hxj)
    ∃ qQ : Fin (m + 1) → Q,
      qQ (Fin.succ j) = 1 ∧
      (∀ a, ((qQ a : Q) : F) = ((C.q a : V) : F)) ∧
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
  have hpChart : componentProjectivePoint P (Fin.succ j) ≠ 0 := by
    have hp : componentProjectivePoint P C.chart ≠ 0 := by
      intro hz
      have hqchartF : ((C.q C.chart : V) : F) = 1 :=
        congrArg (fun z : V => (z : F)) C.chart_one
      have hqzeroF : ((C.q C.chart : V) : F) = 0 := by
        rw [C.q_commonScale C.chart, hz]
        simp
      exact one_ne_zero (hqchartF.symm.trans hqzeroF)
    simpa [C, hchart] using hp
  have hxj : componentCoordinate P j ≠ 0 := by
    simpa [componentProjectivePoint] using hpChart
  let e := SelectedAffineCoordinateEquiv j
  let Q := Algebra.adjoin k (Set.range (chartGenericPoint P (Fin.succ j) e))
  let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
    componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j) e hpChart
  have hactual := exists_actual_normalizedProjectiveColumn hm P w
  dsimp only at hactual
  rw [hchart] at hactual
  obtain ⟨qQ, hqChart, hqcoe, hqrows⟩ := hactual
  have hqChart' : qQ (Fin.succ j) = 1 := hqChart
  have horigin :
      (SelectedAffineCoordinateEquiv j (selectedAffineChartOrigin j)).1 = 0 := by
    have h := Equiv.apply_symm_apply (SelectedAffineCoordinateEquiv j)
      ⟨0, by simpa [eq_comm] using Fin.succ_ne_zero j⟩
    exact congrArg Subtype.val h
  have hq0generic : ((qQ 0 : Q) : F) =
      chartGenericPoint P (Fin.succ j) e (selectedAffineChartOrigin j) := by
    have hi := hqrows (selectedAffineChartOrigin j)
    simpa [SelectedAffineCoordinateEquiv, horigin] using hi
  have hq0 : qQ 0 = hsel (selectedAffineChartDenominator P j) := by
    calc
      qQ 0 = ⟨chartGenericPoint P (Fin.succ j) e (selectedAffineChartOrigin j),
        Algebra.subset_adjoin (R := k) (A := F)
          (Set.mem_range_self (selectedAffineChartOrigin j))⟩ := by
        apply Subtype.ext
        exact hq0generic
      _ = hsel (selectedAffineChartDenominator P j) := by
        exact (selected_denominator_eq_generic_coordinate P j hpChart).symm
  have hqvars : ∀ i : Fin m, ∀ hij : i ≠ j,
      qQ (Fin.succ i) = hsel (selectedAffineChartVariableClass P j i hij) := by
    intro i hij
    let ai := (SelectedAffineCoordinateEquiv j).symm
      ⟨i.succ, by simpa using hij⟩
    have ha : (SelectedAffineCoordinateEquiv j ai).1 = Fin.succ i := by
      have h := Equiv.apply_symm_apply (SelectedAffineCoordinateEquiv j)
        ⟨i.succ, by simpa using hij⟩
      exact congrArg Subtype.val h
    have hi := hqrows ai
    have hrow : ((qQ (Fin.succ i) : Q) : F) =
        chartGenericPoint P (Fin.succ j) e ai := by
      simpa [SelectedAffineCoordinateEquiv, ha] using hi
    calc
      qQ (Fin.succ i) =
          ⟨chartGenericPoint P (Fin.succ j) e ai,
            Algebra.subset_adjoin (R := k) (A := F) (Set.mem_range_self ai)⟩ := by
              apply Subtype.ext
              exact hrow
      _ = hsel (selectedAffineChartVariableClass P j i hij) := by
        exact (selected_variable_eq_generic_coordinate P j i hij hpChart).symm
  exact ⟨qQ, hqChart', hqcoe, hq0, hqvars⟩

/-- The chart chosen by a retained witness is a nonzero projective coordinate,
so its matching affine component coordinate is nonzero. -/
theorem actualWitness_selected_coordinate_ne_zero
    {k : Type u} [Field k] [CharZero k] {m : ℕ}
    (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (j : Fin m) (hchart : w.column.chart = Fin.succ j) :
    componentCoordinate P j ≠ 0 := by
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : Algebra V F := V.subtype.toAlgebra
  have hpoint : componentProjectivePoint P C.chart ≠ 0 := by
    intro hz
    have hqchartF : ((C.q C.chart : V) : F) = 1 :=
      congrArg (fun z : V => (z : F)) C.chart_one
    have hqzeroF : ((C.q C.chart : V) : F) = 0 := by
      rw [C.q_commonScale C.chart, hz]
      simp
    exact one_ne_zero (hqchartF.symm.trans hqzeroF)
  have hselected : componentProjectivePoint P (Fin.succ j) ≠ 0 := by
    simpa [C, hchart] using hpoint
  simpa [componentProjectivePoint] using hselected

/-- The retained witness's normalized column, transported from its canonical
selected-chart quotient into the common open, is the same tuple as the
canonical common-open coordinates. This is the same Q, denominator, map and
generic-open data used by `canonicalChart_all_normalized_projective_coordinates`.
-/
theorem actualWitness_commonOpen_q_coordinates
    {k : Type u} [Field k] [CharZero k] {m : ℕ}
    (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (j : Fin m) (hchart : w.column.chart = Fin.succ j)
    {B : Type w} [CommRing B]
    [Algebra (Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))) B]
    (M : Ideal B) [M.IsPrime]
    (f : Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j))))
    (e : Localization.Away f ≃ₐ[
      Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))]
      Localization.Away (algebraMap _ B f)) :
    let Q := Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
    let hxj := actualWitness_selected_coordinate_ne_zero hm P w j hchart
    let F := ComponentFractionField P
    let W := w.column.W
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : Algebra V F := V.subtype.toAlgebra
    let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
      componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
        (SelectedAffineCoordinateEquiv j) (by
          simpa [componentProjectivePoint] using hxj)
    let g := hsel (selectedAffineChartDenominator P j)
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq C := inferInstance
    letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
    let qC : Fin (m + 1) → C := Fin.cases
      (algebraMap Cq C (algebraMap Q Cq g))
      (fun i => if hij : i = j then 1 else
        algebraMap Cq C (algebraMap Q Cq
          (hsel (selectedAffineChartVariableClass P j i hij))))
    ∃ qQ : Fin (m + 1) → Q,
      qQ (Fin.succ j) = 1 ∧
      (∀ a, ((qQ a : Q) : F) =
        ((w.column.q a : w.column.W.place.valuation.toSubring) : F)) ∧
      qQ 0 = hsel (selectedAffineChartDenominator P j) ∧
      (∀ i : Fin m, ∀ hij : i ≠ j,
        qQ (Fin.succ i) = hsel (selectedAffineChartVariableClass P j i hij)) ∧
      ∀ a, algebraMap Q C (qQ a) = qC a := by
  classical
  dsimp only
  have hxj : componentCoordinate P j ≠ 0 :=
    actualWitness_selected_coordinate_ne_zero hm P w j hchart
  let Q := Algebra.adjoin k (Set.range
    (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
  let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
    componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
      (SelectedAffineCoordinateEquiv j) (by
        simpa [componentProjectivePoint] using hxj)
  let g := hsel (selectedAffineChartDenominator P j)
  let Cq := genericOpenRing M f e
  let C := genericOpenExtraAwayB M f e g
  letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq C := inferInstance
  letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
  have hcomp (x : Q) : algebraMap Q C x =
      algebraMap Cq C (algebraMap Q Cq x) := rfl
  let qC : Fin (m + 1) → C := Fin.cases
    (algebraMap Cq C (algebraMap Q Cq g))
    (fun i => if hij : i = j then 1 else
      algebraMap Cq C (algebraMap Q Cq
        (hsel (selectedAffineChartVariableClass P j i hij))))
  obtain ⟨qQ, hqchart, hqcoe, hq0, hqvars⟩ :=
    actual_selected_chart_q_coordinates hm P w j hchart
  refine ⟨qQ, hqchart, hqcoe, hq0, hqvars, ?_⟩
  intro a
  cases a using Fin.cases with
  | zero =>
      calc
        algebraMap Q C (qQ 0) =
            algebraMap Q C (hsel (selectedAffineChartDenominator P j)) :=
          congrArg (algebraMap Q C) hq0
        _ = algebraMap Cq C (algebraMap Q Cq
              (hsel (selectedAffineChartDenominator P j))) := hcomp _
        _ = qC 0 := by simp [qC, g]
  | succ i =>
      by_cases hij : i = j
      · subst i
        calc
          algebraMap Q C (qQ (Fin.succ j)) = algebraMap Q C 1 :=
            congrArg (algebraMap Q C) hqchart
          _ = algebraMap Cq C (algebraMap Q Cq 1) := hcomp _
          _ = qC (Fin.succ j) := by simp [qC]
      · calc
          algebraMap Q C (qQ (Fin.succ i)) =
              algebraMap Q C
                (hsel (selectedAffineChartVariableClass P j i hij)) :=
            congrArg (algebraMap Q C) (hqvars i hij)
          _ = algebraMap Cq C (algebraMap Q Cq
                (hsel (selectedAffineChartVariableClass P j i hij))) := hcomp _
          _ = qC (Fin.succ i) := by simp [qC, hij]

#print axioms componentChartEquiv_mk_X
#print axioms selected_denominator_eq_generic_coordinate
#print axioms selected_variable_eq_generic_coordinate
#print axioms actualWitness_selected_coordinate_ne_zero
#print axioms actual_selected_chart_q_coordinates
#print axioms actualWitness_commonOpen_q_coordinates

end Stafford38.Geometry.ActualWitnessSelectedChartBinding
end
