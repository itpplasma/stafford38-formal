module
public import Stafford38.Geometry.FiniteBirationalAway
public import Stafford38.Geometry.ChartGenericPointFractionRing
public import Stafford38.Geometry.ProjectiveChartNormalizationFinite
public import Stafford38.Geometry.GeneralDivisorialVisibleFrameWitness
public import Stafford38.Geometry.AsymptoticChartArcAdapter

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.ProjectiveChartNormalizationFinite
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.FiniteBirationalAway

universe u

/-- The literal generic chart domain selected by a divisorial-frame column. -/
abbrev witnessChartDomain
    {k : Type u} [Field k] [CharZero k] {m : ℕ}
    (hm : 0 < m) (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (C : GeneralDivisorialVisibleFrameColumn hm P) :=
  Algebra.adjoin k
    (Set.range (chartGenericPoint P C.chart (chartAffineCoordinateEquiv C.chart)))

/-- Applying the finite-birational localization theorem to the actual chart
subalgebra and its integral closure.  The chart is nonzero because the
normalized projective column has coordinate one and a common nonzero scale. -/
theorem actual_chart_normalization_is_away_equiv
    {k : Type u} [Field k] [CharZero k] {m : ℕ}
    (hm : 0 < m) (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (C : GeneralDivisorialVisibleFrameColumn hm P) :
    ∃ f : witnessChartDomain hm P C, f ≠ 0 ∧
      Nonempty
        (Localization.Away f ≃ₐ[witnessChartDomain hm P C]
          Localization.Away
            (algebraMap (witnessChartDomain hm P C)
              (integralClosure (witnessChartDomain hm P C)
                (ComponentFractionField P)) f)) := by
  let Q := witnessChartDomain hm P C
  let F := ComponentFractionField P
  let B := integralClosure Q F
  have hchart : componentProjectivePoint P C.chart ≠ 0 := by
    have hscale : C.scale * componentProjectivePoint P C.chart = 1 := by
      simpa [C.chart_one] using (C.q_commonScale C.chart).symm
    intro hz
    rw [hz, mul_zero] at hscale
    exact one_ne_zero hscale.symm
  letI : IsFractionRing Q F :=
    chartGenericPointSubalgebra_isFractionRing P C.chart
      (chartAffineCoordinateEquiv C.chart) hchart
  letI : Algebra.FiniteType k Q :=
    chartGenericPointSubalgebra_finiteType P C.chart
      (chartAffineCoordinateEquiv C.chart)
  haveI : Module.Finite Q B :=
    finite_integralClosure_in_fractionField k Q F
  exact exists_nonzero_away_equiv_of_finite
    (Q := Q) (F := F) (B := B) Subtype.val_injective

#print axioms actual_chart_normalization_is_away_equiv

end
