import Stafford38.Geometry.ActualChartNormalizationCenter

#print axioms Stafford38.Geometry.ActualChartNormalizationCenter.actual_chart_normalization_center_height_one_of_basis
#print axioms Stafford38.Geometry.ActualChartNormalizationCenter.actual_chart_normalization_center_height_one_of_selected_basis
#print axioms Stafford38.Geometry.ActualChartNormalizationCenter.subalgebraToSubringRingEquiv

open Stafford38.Geometry.ActualChartNormalizationCenter

/-- The public carrier/subring equivalence preserves the ambient value. -/
example (q : ℚ) :
    (((subalgebraToSubringRingEquiv (⊤ : Subalgebra ℚ ℚ))
      ⟨q, Set.mem_univ q⟩ : (⊤ : Subalgebra ℚ ℚ).toSubring) : ℚ) = q := rfl
