module
public import Stafford38.Geometry.AsymptoticChartArcAdapter
public import Stafford38.Geometry.PowerSeriesArcTangency

@[expose] public section

open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
open Stafford38.Geometry.PowerSeriesArcTangency

/-- An explicit series whose linear coefficient is seven. -/
def sampleSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n : ℕ => if n = 1 then 7 else 0

def sampleArc : Fin 2 → PowerSeries ℚ := fun _ => sampleSeries

def singletonArc : Unit → PowerSeries ℚ := fun _ => sampleSeries

theorem generic_first_coefficient_reads_linear_term :
    powerSeriesFirstCoefficient singletonArc () = 7 := by
  simp [powerSeriesFirstCoefficient, singletonArc, sampleSeries,
    PowerSeries.coeff_mk]

theorem arcVelocity_reads_linear_term : arcVelocity sampleArc 0 = 7 := by
  simp [arcVelocity, powerSeriesFirstCoefficient, sampleArc, sampleSeries,
    PowerSeries.coeff_mk]

theorem projectiveFirstJet_reads_linear_term :
    projectiveFirstJet singletonArc () = 7 := by
  simp [projectiveFirstJet, powerSeriesFirstCoefficient, singletonArc,
    sampleSeries, PowerSeries.coeff_mk]

theorem arcVelocity_uses_canonical_first_coefficient :
    arcVelocity sampleArc = powerSeriesFirstCoefficient sampleArc := rfl

theorem projectiveFirstJet_uses_canonical_first_coefficient :
    projectiveFirstJet singletonArc = powerSeriesFirstCoefficient singletonArc := rfl

theorem first_coefficient_is_derivative_at_constant_term :
    powerSeriesFirstCoefficient singletonArc =
      fun i => PowerSeries.constantCoeff (PowerSeries.derivative ℚ (singletonArc i)) :=
  powerSeriesFirstCoefficient_eq_constantCoeff_derivative singletonArc

#print axioms generic_first_coefficient_reads_linear_term
#print axioms arcVelocity_reads_linear_term
#print axioms projectiveFirstJet_reads_linear_term
#print axioms first_coefficient_is_derivative_at_constant_term
#print axioms Stafford38.Geometry.PowerSeriesArcTangency.arcVelocity_eq_constantCoeff_derivative
#print axioms arcVelocity_uses_canonical_first_coefficient
#print axioms projectiveFirstJet_uses_canonical_first_coefficient
