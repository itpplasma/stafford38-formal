import Stafford38.Geometry.PaperDivisorTangent
import Stafford38.Geometry.ProjectiveBoundaryFrameRank
import Stafford38.Geometry.ProjectiveConormalDehomogenization
import Mathlib.Tactic

private def sampleQ : Fin 3 → ℚ := fun i =>
  if i.val = 0 then 2 else if i.val = 1 then 3 else 5

private def sampleW : Fin 3 → ℚ := fun i =>
  if i.val = 0 then 7 else if i.val = 1 then 11 else 13

private abbrev fin3Zero : Fin 3 := 0
private abbrev fin3One : Fin 3 := Fin.succ (0 : Fin 2)
private abbrev fin3Two : Fin 3 := Fin.succ (Fin.succ (0 : Fin 1))

private theorem sampleQ_zero : sampleQ fin3Zero = 2 := by
  norm_num [sampleQ, fin3Zero]
private theorem sampleQ_one : sampleQ fin3One = 3 := by
  norm_num [sampleQ, fin3One]
private theorem sampleQ_two : sampleQ fin3Two = 5 := by
  norm_num [sampleQ, fin3Two]
private theorem sampleW_zero : sampleW fin3Zero = 7 := by
  norm_num [sampleW, fin3Zero]
private theorem sampleW_one : sampleW fin3One = 11 := by
  norm_num [sampleW, fin3One]
private theorem sampleW_two : sampleW fin3Two = 13 := by
  norm_num [sampleW, fin3Two]

private abbrev chartOneIndexZero :
    Stafford38.Geometry.ProjectiveChartCoordinates.ChartAffineIndex
      (Fin 3) (1 : Fin 3) := ⟨0, by decide⟩

private abbrev chartOneIndexTwo :
    Stafford38.Geometry.ProjectiveChartCoordinates.ChartAffineIndex
      (Fin 3) fin3One := ⟨fin3Two, by decide⟩

/-- The generic owner gives the signed quotient-rule value in chart one. -/
theorem generic_chart_tangent_literal_oracle :
    Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedTangentColumn
      fin3One sampleQ sampleW chartOneIndexZero = -(1 : ℚ) / 9 := by
  norm_num [Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedTangentColumn,
    sampleQ, sampleW, fin3Zero, fin3One, fin3Two, chartOneIndexZero,
    Fin.cases_zero, Fin.cases_succ]

/-- The historical arbitrary-chart API delegates to the same generic value. -/
theorem arbitrary_chart_tangent_literal_oracle :
    Stafford38.Geometry.ProjectiveBoundaryFrameRank.chartDehomogenizedTangentColumn
      fin3One sampleQ sampleW chartOneIndexTwo = -(16 : ℚ) / 9 := by
  norm_num [Stafford38.Geometry.ProjectiveBoundaryFrameRank.chartDehomogenizedTangentColumn,
    Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedTangentColumn,
    sampleQ, sampleW, fin3Zero, fin3One, fin3Two, chartOneIndexTwo,
    Fin.cases_zero, Fin.cases_succ]

/-- The historical zero-chart API keeps its `Fin.succ` coordinate order. -/
theorem zero_chart_tangent_literal_oracle :
    Stafford38.Geometry.ProjectiveConormalDehomogenization.dehomogenizedTangentColumn
      sampleQ sampleW (0 : Fin 2) = (1 : ℚ) / 4 := by
  norm_num [Stafford38.Geometry.ProjectiveConormalDehomogenization.dehomogenizedTangentColumn,
    Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedTangentColumn,
    Stafford38.Geometry.ProjectiveChartCoordinates.zerothChartEquiv_apply,
    sampleQ, sampleW, fin3Zero, fin3One, fin3Two,
    Fin.cases_zero, Fin.cases_succ]

theorem zero_chart_second_coordinate_literal_oracle :
    Stafford38.Geometry.ProjectiveConormalDehomogenization.dehomogenizedTangentColumn
      sampleQ sampleW (Fin.succ (0 : Fin 1)) = -(9 : ℚ) / 4 := by
  norm_num [Stafford38.Geometry.ProjectiveConormalDehomogenization.dehomogenizedTangentColumn,
    Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedTangentColumn,
    Stafford38.Geometry.ProjectiveChartCoordinates.zerothChartEquiv_apply,
    sampleQ, sampleW, fin3Zero, fin3One, fin3Two,
    Fin.cases_zero, Fin.cases_succ]

/-- A finite difference of the actual chart-one ratio equals the tangent value
times the expected chart-denominator correction; this checks the quotient
rule sign independently at the concrete point. -/
theorem chart_one_quotient_difference_literal_oracle :
    (sampleQ fin3Zero + sampleW fin3Zero) /
        (sampleQ fin3One + sampleW fin3One) -
        sampleQ fin3Zero / sampleQ fin3One =
      Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedTangentColumn
        fin3One sampleQ sampleW chartOneIndexZero *
          sampleQ fin3One / (sampleQ fin3One + sampleW fin3One) := by
  norm_num [Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedTangentColumn,
    sampleQ, sampleW, fin3Zero, fin3One, fin3Two, chartOneIndexZero,
    Fin.cases_zero, Fin.cases_succ]

/-- The fixed zeroth-chart API satisfies the same finite-difference oracle. -/
theorem chart_zero_quotient_difference_literal_oracle :
    (sampleQ fin3One + sampleW fin3One) /
        (sampleQ fin3Zero + sampleW fin3Zero) -
        sampleQ fin3One / sampleQ fin3Zero =
      Stafford38.Geometry.ProjectiveConormalDehomogenization.dehomogenizedTangentColumn
        sampleQ sampleW (0 : Fin 2) *
          sampleQ fin3Zero / (sampleQ fin3Zero + sampleW fin3Zero) := by
  norm_num [Stafford38.Geometry.ProjectiveConormalDehomogenization.dehomogenizedTangentColumn,
    Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedTangentColumn,
    Stafford38.Geometry.ProjectiveChartCoordinates.zerothChartEquiv_apply,
    sampleQ, sampleW, fin3Zero, fin3One, fin3Two,
    Fin.cases_zero, Fin.cases_succ]

#print axioms generic_chart_tangent_literal_oracle
#print axioms arbitrary_chart_tangent_literal_oracle
#print axioms zero_chart_tangent_literal_oracle
#print axioms zero_chart_second_coordinate_literal_oracle
#print axioms chart_one_quotient_difference_literal_oracle
#print axioms chart_zero_quotient_difference_literal_oracle

namespace Stafford38.Geometry.PaperDivisorTangent
open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.ProjectiveConormalDehomogenization
/-- A non-unit normalized position with zero affine tangent space has exactly
its radial line as its projective tangent cone. -/
example :
    let q : Fin 2 → ℚ := ![2, 3]
    projectiveTangentCone q (⊥ : Submodule ℚ (Fin 1 → ℚ)) =
      Submodule.span ℚ ({q} : Set (Fin 2 → ℚ)) := by
  dsimp only
  let q : Fin 2 → ℚ := ![2, 3]
  let B : Matrix (Fin 2) Unit ℚ := fun i _ => q i
  have hpos : q ∈ Submodule.span ℚ (Set.range fun j => fun i => B i j) :=
    Submodule.subset_span ⟨(), rfl⟩
  have htan : (⊥ : Submodule ℚ (Fin 1 → ℚ)) =
      dehomogenizedTangentSpan q B := by
    symm
    apply Submodule.span_eq_bot.mpr
    rintro _ ⟨j, rfl⟩
    ext i
    fin_cases i
    norm_num [dehomogenizedTangentColumn, q, B]
  have h := projectiveTangentCone_eq_span_of_position_and_tangent
    q (by norm_num [q]) ⊥ B hpos htan
  have hrange : (Set.range fun j => fun i => B i j) = {q} := by
    ext v
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      rfl
    · rintro rfl
      exact ⟨(), rfl⟩
  simpa only [hrange] using h

end Stafford38.Geometry.PaperDivisorTangent

#print axioms Stafford38.Geometry.PaperDivisorTangent.projectiveTangentCone_eq_span_of_position_and_tangent
