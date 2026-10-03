module
public import Stafford38.Geometry.ProjectiveChartSameFieldOverlap

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.ProjectiveChartSameFieldOverlapConsumer

open Stafford38.Geometry.ProjectiveChartSameFieldOverlap
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.AffineComponentCoordinateSplit

universe u
variable {k : Type u} [Field k] {m : ℕ}
variable (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j i : Fin m)
variable (hxj : componentCoordinate P j ≠ 0)

-- A downstream affine-chart consumer can read the original variable image.
theorem original_coordinate_action (hij : i ≠ j) :
    originalAffineChartOverlapEquiv P j hxj
      (algebraMap (OriginalAffineChartQuotient (k := k) P)
        (OriginalAffineChartLocalization (k := k) P j)
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i))) =
      algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j)
        (selectedAffineChartVariableClass P j i hij) *
        IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) :=
  originalAffineChartOverlapEquiv_Xi P j i hij hxj

-- The same object is genuinely an equivalence, not a one-way ring map.
theorem reverse_coordinate_action (hij : i ≠ j) :
    (originalAffineChartOverlapEquiv P j hxj).symm
      (algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j)
        (selectedAffineChartVariableClass P j i hij)) =
      algebraMap (OriginalAffineChartQuotient (k := k) P)
        (OriginalAffineChartLocalization (k := k) P j)
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) *
        IsLocalization.Away.invSelf (originalAffineChartDenominator P j) :=
  originalAffineChartOverlapEquiv_symm_Xi P j i hij hxj

-- The actual field embeddings commute with the direct chart equivalence.
theorem common_function_field_action :
    (selectedAffineChartToFunctionField P j hxj).comp
        (originalAffineChartOverlapEquiv P j hxj).toAlgHom.toRingHom =
      originalAffineChartToFunctionField P j hxj :=
  originalAffineChartOverlap_sameField_forward P j hxj

#print axioms original_coordinate_action
#print axioms reverse_coordinate_action
#print axioms common_function_field_action

end Stafford38.Geometry.ProjectiveChartSameFieldOverlapConsumer
