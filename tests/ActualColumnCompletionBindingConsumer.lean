import Stafford38.Geometry.ActualOptionColumnBinding
import Stafford38.Geometry.ActualDivisorUniformizerNumerator

open Stafford38.Geometry.ActualOptionColumnBinding

example : actualOptionCoordinateAlgebraMap (k := ℚ) (B := ℚ) 1
    (fun i : Option (Fin 1) => if i.isNone then 3 else 5)
    (MvPolynomial.X (R := ℚ) (none : Option (Fin 1))) = 3 := by
  simp [actualOptionCoordinateAlgebraMap]

#check Stafford38.Geometry.ActualOptionColumnBinding.exists_actual_option_coordinate_map
#check Stafford38.Geometry.ActualOptionColumnBinding.actualOptionCoordinateMap_scalarTower
#check Stafford38.Geometry.ActualOptionColumnBinding.actual_normalized_column_map_eq_retained
#check Stafford38.Geometry.ActualOptionColumnBinding.retained_frame_coordinate_orders
#print axioms Stafford38.Geometry.ActualOptionColumnBinding.exists_actual_option_coordinate_map
#print axioms Stafford38.Geometry.ActualOptionColumnBinding.actual_normalized_column_map_eq_retained
#print axioms Stafford38.Geometry.ActualOptionColumnBinding.retained_frame_coordinate_orders
#print axioms Stafford38.Geometry.ActualDivisorUniformizerNumerator.exists_numerator_with_two_unit_power_factorizations

#print axioms Stafford38.Geometry.ActualDivisorUniformizerNumerator.exists_numerator_with_two_unit_power_factorizations_and_span
