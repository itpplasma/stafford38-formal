import Stafford38.Geometry.GeneralDivisorialVisibleFrameResidueSupport
import Stafford38.Geometry.ChartGenericPointFractionRing
import Stafford38.Geometry.AsymptoticChartArcAdapter

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Stafford38.Geometry.ActualChartValuationImage

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RetainedGroundMapIdentification

universe u

/-- The affine generic-chart coordinate algebra lies in the actual valuation
ring of the same retained visible-frame witness. -/
theorem chartGenericPointSubalgebra_le_valuationSubring
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
      (ComponentFractionField P) := w.column.W.ambientAlgebra
    ∀ z : ComponentFractionField P, z ∈ Algebra.adjoin k (Set.range
      (chartGenericPoint P w.column.chart
        (chartAffineCoordinateEquiv w.column.chart))) →
        z ∈ w.column.W.place.valuation.toSubring := by
  classical
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  letI : IsDiscreteValuationRing W.place.valuation.toSubring := W.place.isDiscrete
  letI : IsLocalRing W.place.valuation.toSubring := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField W.place.valuation.toSubring :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra W.place.valuation.toSubring F :=
    W.place.valuation.toSubring.subtype.toAlgebra
  letI := C.groundCoeff.toAlgebra
  letI := C.groundTower
  let e := chartAffineCoordinateEquiv C.chart
  let A := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
  have hcoeffmem : ∀ a : k, algebraMap k F a ∈ W.place.valuation.toSubring := by
    intro a
    rw [← DFunLike.congr_fun C.groundCoeff_commutes a]
    exact (C.groundCoeff a).property
  let Vsub : Subalgebra k F :=
    {W.place.valuation.toSubring with algebraMap_mem' := hcoeffmem}
  have hgen : A ≤ Vsub := by
    apply Algebra.adjoin_le
    rintro z ⟨i, rfl⟩
    change chartGenericPoint P C.chart e i ∈ Vsub
    rw [chartGenericPoint_eq_normalized_lift (P := P)
      (V := W.place.valuation.toSubring) C.chart e C.q C.scale
      C.chart_one C.q_commonScale]
    exact (C.q (e i).1).property
  intro z hz
  exact hgen hz

/-- Every coordinate of the retained normalized projective lift lies in the
actual affine generic-chart subalgebra of the same component function field.
This is the reusable membership fact behind the projective-column binding. -/
theorem normalizedCoordinate_mem_chartGenericPointSubalgebra
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : Algebra V F := V.subtype.toAlgebra
    ∀ a : Fin (m + 1),
      ((C.q a : V) : F) ∈ Algebra.adjoin k (Set.range
        (chartGenericPoint P C.chart (chartAffineCoordinateEquiv C.chart))) := by
  classical
  dsimp only
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra V F := V.subtype.toAlgebra
  letI := C.groundCoeff.toAlgebra
  letI := C.groundTower
  let e := chartAffineCoordinateEquiv C.chart
  let Q := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
  let qF : Fin (m + 1) → F := fun a ↦ ((C.q a : V) : F)
  have hval (v : V) : algebraMap V F v = (v : F) := rfl
  have hqF_chart : qF C.chart = 1 := by
    change ((C.q C.chart : V) : F) = 1
    exact congrArg (fun v : V => (v : F)) C.chart_one
  have hgeneric := chartGenericPoint_eq_normalized_lift
    (P := P) (V := V) C.chart e C.q C.scale C.chart_one C.q_commonScale
  intro a
  change qF a ∈ Q
  by_cases ha : a = C.chart
  · subst a
    rw [hqF_chart]
    exact one_mem Q
  · let i : Fin m := e.symm ⟨a, ha⟩
    have hi := congrFun hgeneric i
    have hvalue : chartGenericPoint P C.chart e i = qF a := by
      calc
        chartGenericPoint P C.chart e i = algebraMap V F (C.q (e i).1) := hi
        _ = qF a := by
          rw [hval]
          simp [qF, i]
    rw [← hvalue]
    exact Algebra.subset_adjoin (R := k) (A := F) (Set.mem_range_self i)

/-- The retained q-column, reinterpreted coordinatewise in its actual generic
chart algebra, has the same values in the component field and preserves the
chosen chart normalization.  The affine rows agree with the canonical
`chartGenericPoint` rows, so later selected-row statements use the very same
residue-basis indices. -/
theorem exists_actual_normalizedProjectiveColumn
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : Algebra V F := V.subtype.toAlgebra
    let e := chartAffineCoordinateEquiv C.chart
    let Q := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
    ∃ qQ : Fin (m + 1) → Q,
      qQ C.chart = 1 ∧
      (∀ a, ((qQ a : Q) : F) = ((C.q a : V) : F)) ∧
      (∀ i : Fin m, ((qQ (e i).1 : Q) : F) =
        chartGenericPoint P C.chart e i) := by
  classical
  dsimp only
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra V F := V.subtype.toAlgebra
  letI := C.groundCoeff.toAlgebra
  letI := C.groundTower
  let e := chartAffineCoordinateEquiv C.chart
  let Q := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
  let qF : Fin (m + 1) → F := fun a ↦ ((C.q a : V) : F)
  have hval (v : V) : algebraMap V F v = (v : F) := rfl
  have hqmem := normalizedCoordinate_mem_chartGenericPointSubalgebra hm P w
  let qQ : Fin (m + 1) → Q := fun a ↦ ⟨qF a, hqmem a⟩
  have hgeneric := chartGenericPoint_eq_normalized_lift
    (P := P) (V := V) C.chart e C.q C.scale C.chart_one C.q_commonScale
  have hchart : qQ C.chart = 1 := by
    apply Subtype.ext
    change qF C.chart = 1
    exact congrArg (fun v : V => (v : F)) C.chart_one
  have hcoe : ∀ a, ((qQ a : Q) : F) = ((C.q a : V) : F) := by
    intro a
    rfl
  have hrows : ∀ i : Fin m, ((qQ (e i).1 : Q) : F) =
      chartGenericPoint P C.chart e i := by
    intro i
    have hi := congrFun hgeneric i
    calc
      ((qQ (e i).1 : Q) : F) = qF (e i).1 := rfl
      _ = algebraMap V F (C.q (e i).1) := (hval _).symm
      _ = chartGenericPoint P C.chart e i := hi.symm
  exact ⟨qQ, hchart, hcoe, hrows⟩

end Stafford38.Geometry.ActualChartValuationImage
