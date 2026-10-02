import Stafford38.Geometry.GeneralDivisorialVisibleFrameResidueSupport

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.ActualWitnessSelectedChartIndex

open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.AsymptoticDivisorExistence
open IsLocalRing

noncomputable section

universe u

/-- The retained order factorization makes the zeroth projective coordinate
nonzero in the chart index: its residue is zero, whereas the selected chart
coordinate has been normalized to one. Hence every actual witness chart is a
successor coordinate. -/
theorem exists_succ_chart_index
    {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    ∃ j : Fin m, w.column.chart = Fin.succ j := by
  classical
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField) F :=
    w.column.W.ambientAlgebra
  let V := w.column.W.place.valuation.toSubring
  letI : IsLocalRing V := w.column.W.place.isDiscrete.toIsLocalRing
  have hq0res : residue V (w.column.q 0) = 0 :=
    witness_q0_residue_eq_zero hm P w
  have hchart : w.column.chart ≠ 0 := by
    intro hz
    have hq01 : w.column.q 0 = 1 := by
      simpa [hz] using w.column.chart_one
    have hres := congrArg (residue V) hq01
    rw [hq0res, map_one] at hres
    exact zero_ne_one hres
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero hchart
  exact ⟨j, hj.symm⟩

end
end Stafford38.Geometry.ActualWitnessSelectedChartIndex
