module
public import Stafford38.Geometry.ActualChartValuationImage
public import Stafford38.Geometry.ProjectiveChartNormalizationCenter
public import Stafford38.Geometry.GeneralDivisorialVisibleFrameResidueSupport
public import Stafford38.Geometry.RelativeCoefficientDVRPlace

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualChartCenterNonzero

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.ActualChartValuationImage

universe u

/-- The zeroth projective coordinate is nonzero and belongs to the center in
the integral closure of the chart coordinate algebra. -/
theorem actual_chart_normalization_center_ne_bot
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
      (ComponentFractionField P) := w.column.W.ambientAlgebra
    let U := w.column.W.place.valuation
    let V : Subring (ComponentFractionField P) := w.column.W.place.valuation.toSubring
    let Q : Subalgebra k (ComponentFractionField P) :=
      Algebra.adjoin k (Set.range (chartGenericPoint P w.column.chart
        (chartAffineCoordinateEquiv w.column.chart)))
    let hQV : Q.toSubring ≤ V := by
      intro z hz
      exact chartGenericPointSubalgebra_le_valuationSubring hm P w z hz
    ProjectiveChartNormalizationCenter.integralClosureCenter Q.toSubring U hQV ≠ ⊥ := by
  classical
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let U := W.place.valuation
  let V : Subring F := W.place.valuation.toSubring
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V F := V.subtype.toAlgebra
  letI : IsScalarTower k V F := C.groundTower
  let e := chartAffineCoordinateEquiv C.chart
  let Q : Subalgebra k F := Algebra.adjoin k (Set.range (chartGenericPoint P C.chart e))
  have hQV : Q.toSubring ≤ V := by
    intro z hz
    exact chartGenericPointSubalgebra_le_valuationSubring hm P w z hz
  have hq0max : C.q 0 ∈ maximalIdeal V :=
    witness_q0_mem_maximal hm P w
  have hchart : 0 ≠ C.chart := by
    intro hc
    have hq1 : C.q 0 = 1 := by simpa [hc] using C.chart_one
    have hnot : (1 : V) ∉ maximalIdeal V :=
      (IsLocalRing.notMem_maximalIdeal).mpr isUnit_one
    exact hnot (hq1 ▸ hq0max)
  let i0 : Fin m := e.symm ⟨0, hchart⟩
  have hi0 : (e i0).1 = 0 := by
    have heq := Equiv.apply_symm_apply e ⟨0, hchart⟩
    exact congrArg Subtype.val heq
  have hnorm := chartGenericPoint_eq_normalized_lift
    (P := P) (V := V) C.chart e C.q C.scale C.chart_one C.q_commonScale
  have hrmem : chartGenericPoint P C.chart e i0 ∈ Q :=
    Algebra.subset_adjoin (R := k) (A := F) (Set.mem_range_self i0)
  let r : Q.toSubring := ⟨chartGenericPoint P C.chart e i0, hrmem⟩
  have hmap : Subring.inclusion hQV r = C.q 0 := by
    apply Subtype.ext
    change chartGenericPoint P C.chart e i0 = (C.q 0 : V)
    calc
      chartGenericPoint P C.chart e i0 =
          algebraMap V F (C.q (e i0).1) := congrFun hnorm i0
      _ = algebraMap V F (C.q 0) := by rw [hi0]
      _ = (C.q 0 : F) := rfl
  have hr0 : (r : F) ≠ 0 := by
    intro hz
    have hz' : Subring.inclusion hQV r = 0 := Subtype.ext hz
    rw [hmap] at hz'
    exact C.q0_ne hz'
  have hrmax : Subring.inclusion hQV r ∈ maximalIdeal U.toLocalSubring.toSubring := by
    rw [hmap]
    exact hq0max
  exact ProjectiveChartNormalizationCenter.integralClosureCenter_ne_bot_of_nonzero_maximal
    Q.toSubring U hQV r hr0 hrmax


end Stafford38.Geometry.ActualChartCenterNonzero
