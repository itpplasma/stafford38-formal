module
public import Stafford38.Geometry.GeneralDivisorialVisibleFrame
public import Stafford38.Geometry.ChartGenericPointFractionRing
public import Stafford38.Geometry.RetainedPlaceConormalTransport
public import Stafford38.Geometry.HomogenizedAffineEvaluation
public import Stafford38.Geometry.ActualChartValuationImage
public import Stafford38.Geometry.SelectedResidueNormalizationLocalization

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace Stafford38.Geometry.ActualSmoothOpenChartNumerator

noncomputable section

open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ActualChartValuationImage
open Stafford38.Geometry.SelectedResidueCoefficientLocalization
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.HomogenizedAffineEvaluation
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.LocalizedProjectiveChartTransition
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedProjectiveCompletion

universe u

/-- A nonzero function on the original affine component gives a nonzero
homogenized numerator in the actual selected chart algebra of the retained
projective witness.  Its value in the component function field is exactly the
zeroth-coordinate power times the original generic-point value. -/
theorem exists_nonzero_homogenized_numerator
    {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (p : MvPolynomial (Fin m) k)
    (hp : Ideal.Quotient.mk P.asIdeal p ≠ 0) :
    let C : GeneralDivisorialVisibleFrameColumn hm P := w.column
    letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
        (ComponentFractionField P) := C.W.ambientAlgebra
    letI : Algebra (C.W.place.valuation.toSubring)
        (ComponentFractionField P) := C.W.place.valuation.toSubring.subtype.toAlgebra
    let e := chartAffineCoordinateEquiv C.chart
    let F := ComponentFractionField P
    let Q := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
    ∃ r : Q,
      (r : F) = MvPolynomial.eval
        (fun a : Fin (m + 1) ↦ (C.q a : F))
        (MvPolynomial.map (algebraMap k F) (homogenizeAtZero p)) ∧
      (r : F) = (C.q 0 : F) ^
        (MvPolynomial.map (algebraMap k F) p).totalDegree *
          componentAffineGenericPointMap P p ∧
      r ≠ 0 := by
  classical
  let C := w.column
  let e := chartAffineCoordinateEquiv C.chart
  let F := ComponentFractionField P
  let Q := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
  letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField) F := C.W.ambientAlgebra
  let V := C.W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := C.W.place.isDiscrete
  letI : Algebra C.W.coefficientField V :=
    (relativeCoefficientMap C.W.coefficientField C.W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V F := V.subtype.toAlgebra
  letI : IsScalarTower k V F := C.groundTower
  letI : Algebra Q F := Q.val.toAlgebra
  let qF : Fin (m + 1) → F := fun a ↦ (C.q a : F)
  have hqF_common : ∀ a, qF a = C.scale * componentProjectivePoint P a :=
    C.q_commonScale
  have hqF_zero : qF 0 ≠ 0 := by
    intro h
    exact C.q0_ne (Subtype.ext h)
  have hdehom :
      ProjectiveConormalDehomogenization.dehomogenizedPoint qF =
        componentCoordinate P := by
    funext i
    change qF i.succ / qF 0 = componentCoordinate P i
    exact componentCoordinate_eq_div P qF C.scale hqF_common hqF_zero i
  have hpnot : p ∉ P.asIdeal := by
    intro hmem
    exact hp (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hgeneric_nonzero : componentAffineGenericPointMap P p ≠ 0 := by
    intro hzero
    apply hpnot
    rw [← componentAffineGenericPointMap_ker P, RingHom.mem_ker]
    exact hzero
  let pF : MvPolynomial (Fin m) F := MvPolynomial.map (algebraMap k F) p
  have hdehom_eval :
      MvPolynomial.eval
          (ProjectiveConormalDehomogenization.dehomogenizedPoint qF) pF =
        componentAffineGenericPointMap P p := by
    rw [MvPolynomial.eval_map, hdehom]
    exact (componentAffineGenericPointMap_eq_eval₂ P p).symm
  have hnumerator_eval :
      MvPolynomial.eval qF
          (MvPolynomial.map (algebraMap k F) (homogenizeAtZero p)) =
        qF 0 ^ pF.totalDegree * componentAffineGenericPointMap P p := by
    rw [map_homogenizeAtZero,
      eval_homogenizeAtZero_eq_pow_mul_dehomogenizedPoint pF qF hqF_zero]
    rw [hdehom_eval]
  have hnumerator_ne :
      MvPolynomial.eval qF
          (MvPolynomial.map (algebraMap k F) (homogenizeAtZero p)) ≠ 0 := by
    rw [hnumerator_eval]
    exact mul_ne_zero (pow_ne_zero _ hqF_zero) hgeneric_nonzero
  have hqmem : ∀ a, qF a ∈ Q := by
    intro a
    simpa [qF, C, F, V, Q] using
      (normalizedCoordinate_mem_chartGenericPointSubalgebra hm P w a)
  let qQ : Fin (m + 1) → Q := fun a ↦ ⟨qF a, hqmem a⟩
  let r : Q := MvPolynomial.eval₂ (algebraMap k Q) qQ (homogenizeAtZero p)
  have hmap_eval :
      (algebraMap Q F) r =
        MvPolynomial.eval qF
          (MvPolynomial.map (algebraMap k F) (homogenizeAtZero p)) := by
    dsimp [r]
    have hcomp := (MvPolynomial.eval₂_comp_left
      (algebraMap Q F) (algebraMap k Q) qQ (homogenizeAtZero p)).symm
    have hground :
        (algebraMap Q F).comp (algebraMap k Q) = algebraMap k F :=
      IsScalarTower.algebraMap_eq k Q F
    calc
      (algebraMap Q F)
          (MvPolynomial.eval₂ (algebraMap k Q) qQ (homogenizeAtZero p)) =
        MvPolynomial.eval₂
          ((algebraMap Q F).comp (algebraMap k Q))
          (fun a ↦ algebraMap Q F (qQ a)) (homogenizeAtZero p) := hcomp.symm
      _ = MvPolynomial.eval₂ (algebraMap k F) qF (homogenizeAtZero p) := by
        rw [hground]
        congr 1
      _ = MvPolynomial.eval qF
          (MvPolynomial.map (algebraMap k F) (homogenizeAtZero p)) := by
        exact (MvPolynomial.eval_map (algebraMap k F) qF (homogenizeAtZero p)).symm
  have hr_eq :
      (r : F) = MvPolynomial.eval qF
        (MvPolynomial.map (algebraMap k F) (homogenizeAtZero p)) := by
    exact hmap_eval
  have hr_formula :
      (r : F) = qF 0 ^ pF.totalDegree * componentAffineGenericPointMap P p := by
    rw [hr_eq, hnumerator_eval]
  have hr_ne : r ≠ 0 := by
    intro h
    have hF : (r : F) = 0 := congrArg (algebraMap Q F) h
    apply hnumerator_ne
    rw [← hr_eq]
    exact hF
  exact ⟨r, hr_eq, hr_formula, hr_ne⟩

/-- Map the same retained normalized projective column into the canonical
integral closure of its actual generic-chart algebra. Every coordinate remains
the original witness coordinate in the same component fraction field, and its
affine rows remain the selected chart generators. -/
theorem exists_actual_normalizedProjectiveColumn_in_integralClosure
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
    let B := integralClosure Q.toSubring F
    ∃ qB : Fin (m + 1) → B,
      qB C.chart = 1 ∧
      (∀ a, ((qB a : B) : F) = ((C.q a : V) : F)) ∧
      (∀ i : Fin m, ((qB (e i).1 : B) : F) =
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
  let B := integralClosure Q.toSubring F
  obtain ⟨qQ, hchart, hcoe, hrows⟩ :=
    exists_actual_normalizedProjectiveColumn hm P w
  let qToB : Q →+* B := chartSubalgebraToIntegralClosure Q
  let qB : Fin (m + 1) → B := fun a ↦ qToB (qQ a)
  have hchartB : qB C.chart = 1 := by
    change qToB (qQ C.chart) = 1
    rw [hchart, map_one]
  have hcoeB : ∀ a, ((qB a : B) : F) = ((C.q a : V) : F) := by
    intro a
    calc
      ((qB a : B) : F) = ((qQ a : Q) : F) := by
        change ((chartSubalgebraToIntegralClosure Q (qQ a) : B) : F) = _
        exact coe_chartSubalgebraToIntegralClosure Q (qQ a)
      _ = ((C.q a : V) : F) := hcoe a
  have hrowsB : ∀ i : Fin m, ((qB (e i).1 : B) : F) =
      chartGenericPoint P C.chart e i := by
    intro i
    calc
      ((qB (e i).1 : B) : F) = ((qQ (e i).1 : Q) : F) := by
        change ((chartSubalgebraToIntegralClosure Q (qQ (e i).1) : B) : F) = _
        exact coe_chartSubalgebraToIntegralClosure Q (qQ (e i).1)
      _ = chartGenericPoint P C.chart e i := hrows i
  exact ⟨qB, hchartB, hcoeB, hrowsB⟩


end
end Stafford38.Geometry.ActualSmoothOpenChartNumerator
