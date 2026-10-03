module
public import Stafford38.Geometry.ActualSmoothOpenChartNumerator
public import Stafford38.Geometry.SelectedResidueNormalizationLocalization
public import Mathlib.RingTheory.MvPolynomial

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Stafford38.Geometry.ActualOptionColumnBinding

open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.SelectedResidueCoefficientLocalization

universe u

/-- The Option-indexed coordinate values attached to one selected residue
indexing and one normalized projective column. `none` is the divisor
parameter; `some i` is the same retained chart row chosen by `index`. -/
def actualOptionCoordinateValues
    {B : Type u} (m d : ℕ) (chart : Fin (m + 1))
    (qB : Fin (m + 1) → B) (index : Fin d → Fin m) (s : B) :
    Option (Fin d) → B := fun j =>
      match j with
      | none => s
      | some i => qB ((chartAffineCoordinateEquiv chart) (index i)).1

/-- The canonical algebra map for the actual divisor parameter and the
selected rows of the same normalized projective column. Its coefficient map is
the one induced by the canonical chart-subalgebra inclusion into the actual
integral closure. -/
def actualOptionCoordinateAlgebraMap
    {k B : Type u} [CommSemiring k] [CommSemiring B] [Algebra k B]
    (d : ℕ) (values : Option (Fin d) → B) :
    MvPolynomial (Option (Fin d)) k →ₐ[k] B :=
  MvPolynomial.aeval values

@[simp] theorem actualOptionCoordinateAlgebraMap_X_none
    {k B : Type u} [CommSemiring k] [CommSemiring B] [Algebra k B]
    (d : ℕ) (values : Option (Fin d) → B) :
    actualOptionCoordinateAlgebraMap d values
      (MvPolynomial.X (R := k) (none : Option (Fin d))) =
      values none := by
  exact MvPolynomial.aeval_X values none

@[simp] theorem actualOptionCoordinateAlgebraMap_X_some
    {k B : Type u} [CommSemiring k] [CommSemiring B] [Algebra k B]
    (d : ℕ) (values : Option (Fin d) → B) (i : Fin d) :
    actualOptionCoordinateAlgebraMap d values
      (MvPolynomial.X (R := k) (some i : Option (Fin d))) =
      values (some i) := by
  exact MvPolynomial.aeval_X values (some i)

@[simp] theorem actualOptionCoordinateAlgebraMap_C
    {k B : Type u} [CommSemiring k] [CommSemiring B] [Algebra k B]
    (d : ℕ) (values : Option (Fin d) → B) (c : k) :
    actualOptionCoordinateAlgebraMap d values (MvPolynomial.C (R := k) c) = algebraMap k B c := by
  exact MvPolynomial.aeval_C values c

/-- The `R`-algebra structure induced by this single map is compatible with
the retained ground `k`-algebra structure. -/
theorem actualOptionCoordinateMap_scalarTower
    {k B : Type u} [CommSemiring k] [CommSemiring B] [Algebra k B]
    (d : ℕ) (values : Option (Fin d) → B) :
    let f := actualOptionCoordinateAlgebraMap d values
    letI : Algebra (MvPolynomial (Option (Fin d)) k) B := f.toRingHom.toAlgebra
    IsScalarTower k (MvPolynomial (Option (Fin d)) k) B := by
  let f : MvPolynomial (Option (Fin d)) k →ₐ[k] B :=
    actualOptionCoordinateAlgebraMap d values
  letI : Algebra (MvPolynomial (Option (Fin d)) k) B := f.toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  change algebraMap k B c = f (algebraMap k (MvPolynomial (Option (Fin d)) k) c)
  exact (f.commutes c).symm

/-- The unique integral-closure column selected by the retained witness. Its
coordinates are fixed by the component-field inclusion, so later consumers do
not independently choose a second column. -/
noncomputable def actualNormalizedProjectiveColumnInIntegralClosure
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let e := chartAffineCoordinateEquiv C.chart
    let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
    let B := integralClosure Q.toSubring F
    Fin (m + 1) → B := by
  classical
  dsimp only
  exact Classical.choose
    (Stafford38.Geometry.ActualSmoothOpenChartNumerator.exists_actual_normalizedProjectiveColumn_in_integralClosure
      hm P w)

theorem actualNormalizedProjectiveColumnInIntegralClosure_spec
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let e := chartAffineCoordinateEquiv C.chart
    let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
    let B := integralClosure Q.toSubring F
    let qB := actualNormalizedProjectiveColumnInIntegralClosure hm P w
    qB C.chart = 1 ∧
      (∀ a, ((qB a : B) : F) = ((C.q a : C.W.place.valuation.toSubring) : F)) ∧
      (∀ i : Fin m, ((qB (e i).1 : B) : F) = chartGenericPoint P C.chart e i) := by
  classical
  dsimp only
  exact Classical.choose_spec
    (Stafford38.Geometry.ActualSmoothOpenChartNumerator.exists_actual_normalizedProjectiveColumn_in_integralClosure
      hm P w)

/-- Bind the actual retained normalized projective column and the actual
selected residue rows into one Option-indexed polynomial map to the same
integral closure. No row values are accepted as premises: they are obtained
from the retained witness's chart algebra and the selected index map. -/
theorem exists_actual_option_coordinate_map
    {k : Type u} [Field k] [CharZero k]
    {m d : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (index : Fin d → Fin m)
    (s : integralClosure
      ((Algebra.adjoin k (Set.range
        (chartGenericPoint P w.column.chart
          (chartAffineCoordinateEquiv w.column.chart)))).toSubring)
      (ComponentFractionField P)) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let e := chartAffineCoordinateEquiv C.chart
    let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
    let B := integralClosure Q.toSubring F
    let coeff : k →+* B :=
      (chartSubalgebraToIntegralClosure Q).comp (algebraMap k Q)
    letI : Algebra k B := coeff.toAlgebra
    ∃ qB : Fin (m + 1) → B, ∃ f : MvPolynomial (Option (Fin d)) k →ₐ[k] B,
      qB C.chart = 1 ∧
      (∀ a, ((qB a : B) : F) = ((C.q a : C.W.place.valuation.toSubring) : F)) ∧
      (∀ i : Fin m, ((qB (e i).1 : B) : F) = chartGenericPoint P C.chart e i) ∧
      f (MvPolynomial.X (R := k) (none : Option (Fin d))) = s ∧
      (∀ i : Fin d, f (MvPolynomial.X (R := k) (some i : Option (Fin d))) =
        qB (e (index i)).1) ∧
      (∀ c : k, f (MvPolynomial.C (R := k) c) = coeff c) := by
  classical
  dsimp only
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let e := chartAffineCoordinateEquiv C.chart
  let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
  let B := integralClosure Q.toSubring F
  let coeff : k →+* B :=
    (chartSubalgebraToIntegralClosure Q).comp (algebraMap k Q)
  letI : Algebra k B := coeff.toAlgebra
  let qB : Fin (m + 1) → B := actualNormalizedProjectiveColumnInIntegralClosure hm P w
  obtain ⟨hchart, hcoe, hrows⟩ :=
    actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
  let values : Option (Fin d) → B := actualOptionCoordinateValues m d C.chart qB index s
  let f : MvPolynomial (Option (Fin d)) k →ₐ[k] B :=
    actualOptionCoordinateAlgebraMap d values
  refine ⟨qB, f, hchart, hcoe, hrows, ?_, ?_, ?_⟩
  · simp [f, values, actualOptionCoordinateAlgebraMap, actualOptionCoordinateValues]
  · intro i
    simp [f, values, actualOptionCoordinateAlgebraMap,
      actualOptionCoordinateValues, C]
  · intro c
    calc
      f (MvPolynomial.C (R := k) c) = algebraMap k B c := by
        simp [f, actualOptionCoordinateAlgebraMap]
      _ = coeff c := rfl

/-- The selected actual integral-closure column maps to the same retained
column after the checked localization equivalence. This isolates the map
coherence needed before applying the generic numerator/order transport. -/
theorem actual_normalized_column_map_eq_retained
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField) F := C.W.ambientAlgebra
    let echart := chartAffineCoordinateEquiv C.chart
    let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart echart))
    let B := integralClosure Q.toSubring F
    let V : Subring F := C.W.place.valuation.toSubring
    ∀ (center : PrimeSpectrum B),
      (e : Localization.AtPrime center.asIdeal ≃+* V) →
      (hlocalF : ∀ b : B,
        ((e (algebraMap B (Localization.AtPrime center.asIdeal) b) : V) : F) = (b : F)) →
      let qB := actualNormalizedProjectiveColumnInIntegralClosure hm P w
      e (algebraMap B (Localization.AtPrime center.asIdeal) (qB 0)) = C.q 0 ∧
      e (algebraMap B (Localization.AtPrime center.asIdeal)
          (qB (Fin.succ ⟨0, hm⟩))) = C.q (Fin.succ ⟨0, hm⟩) := by
  classical
  dsimp only
  intro center e hlocalF
  let C := w.column
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField) F := C.W.ambientAlgebra
  let echart := chartAffineCoordinateEquiv C.chart
  let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart echart))
  let B := integralClosure Q.toSubring F
  let V : Subring F := C.W.place.valuation.toSubring
  let qB : Fin (m + 1) → B := actualNormalizedProjectiveColumnInIntegralClosure hm P w
  obtain ⟨_hchart, hqB, _hrows⟩ :=
    actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
  have hq0 : e (algebraMap B (Localization.AtPrime center.asIdeal) (qB 0)) = C.q 0 := by
    apply Subtype.ext
    change ((e (algebraMap B (Localization.AtPrime center.asIdeal) (qB 0)) : V) : F) =
      ((C.q 0 : V) : F)
    rw [hlocalF]
    exact hqB 0
  have hq1 : e (algebraMap B (Localization.AtPrime center.asIdeal)
      (qB (Fin.succ ⟨0, hm⟩))) = C.q (Fin.succ ⟨0, hm⟩) := by
    apply Subtype.ext
    change ((e (algebraMap B (Localization.AtPrime center.asIdeal)
      (qB (Fin.succ ⟨0, hm⟩))) : V) : F) =
      ((C.q (Fin.succ ⟨0, hm⟩) : V) : F)
    rw [hlocalF]
    exact hqB (Fin.succ ⟨0, hm⟩)
  exact ⟨hq0, hq1⟩

/-- The retained visible frame itself supplies the uniformizer powers of its
position and distinguished chart coordinates. No selected order is assumed. -/
theorem retained_frame_coordinate_orders
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V : Subring F := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    letI : Algebra k V := C.groundCoeff.toAlgebra
    letI : Algebra V F := V.subtype.toAlgebra
    letI : IsScalarTower k V F := C.groundTower
    let D := w.differential.core.D
    C.q 0 = Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer V ^ D.a * D.u ∧
    C.q (Fin.succ ⟨0, hm⟩) =
      Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer V ^ (D.a + D.e) * D.w := by
  classical
  dsimp only
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V : Subring F := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V F := V.subtype.toAlgebra
  letI : IsScalarTower k V F := C.groundTower
  let D := w.differential.core.D
  have ht : D.t = Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer V :=
    w.differential.core.D_uniformizer
  have h0 : C.q 0 = D.t ^ D.a * D.u := by
    calc
      C.q 0 = D.Q₀ := w.differential.core.D_Q0.symm
      _ = D.t ^ D.a * D.u := D.Q₀_eq
  have h1 : C.q (Fin.succ ⟨0, hm⟩) = D.t ^ (D.a + D.e) * D.w := by
    calc
      C.q (Fin.succ ⟨0, hm⟩) = D.Q₁ := w.differential.core.D_Q1.symm
      _ = D.t ^ (D.a + D.e) * D.w := D.Q₁_eq
  constructor
  · rw [h0, ht]
  · rw [h1, ht]

end Stafford38.Geometry.ActualOptionColumnBinding
