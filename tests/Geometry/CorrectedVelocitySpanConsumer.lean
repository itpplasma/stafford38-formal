module
public import Mathlib
public import Stafford38.Geometry.CorrectedVelocitySpan

@[expose] public section

open Stafford38.Geometry.CorrectedVelocitySpan

def zColumn (_ : Fin 1) : Fin 2 → ℚ :=
  fun i => if i = 0 then 0 else 1

def correctedVelocity : Fin 2 → ℚ :=
  fun i => if i = 0 then 1 else 0

def rawVelocity : Fin 2 → ℚ :=
  fun i => if i = 0 then 3 else 2

def firstCoordinate : (Fin 2 → ℚ) →ₗ[ℚ] ℚ where
  toFun := fun v => v 0
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

/-- A literal two-coordinate use: `raw - 2 z = 3 corrected`, with both
transverse and corrected directions nonzero. -/
theorem corrected_velocity_span_example :
    Submodule.span ℚ
        (Set.range (fun i => firstCoordinate (zColumn i)) ∪
          {firstCoordinate correctedVelocity}) =
      Submodule.span ℚ
        (Set.range (fun i => firstCoordinate (zColumn i)) ∪
          {firstCoordinate rawVelocity}) := by
  apply span_map_range_union_singleton_eq_of_corrected_velocity
    firstCoordinate zColumn (fun _ : Fin 1 => (2 : ℚ))
    correctedVelocity rawVelocity 3
  · norm_num
  · ext i
    fin_cases i <;> norm_num [zColumn, correctedVelocity, rawVelocity]

#print axioms corrected_velocity_span_example

#print axioms Stafford38.Geometry.CorrectedVelocitySpan.span_range_union_singleton_eq_of_corrected_velocity

#print axioms Stafford38.Geometry.CorrectedVelocitySpan.span_map_range_union_singleton_eq_of_corrected_velocity
