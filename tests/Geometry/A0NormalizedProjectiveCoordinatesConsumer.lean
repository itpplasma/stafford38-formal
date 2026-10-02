import Stafford38.Geometry.A0NormalizedProjectiveCoordinates

set_option autoImplicit false

noncomputable section
namespace Stafford38.Geometry.A0NormalizedProjectiveCoordinatesConsumer

open Stafford38.Geometry.ProjectiveChartSameFieldOverlap
open Stafford38.Geometry.A0ChartFormalEtale
open Stafford38.Geometry.A0NormalizedProjectiveCoordinates
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ChartGenericPointFractionRing

universe u w

/-- A separate import consumer projects the selected-chart normalization and
all original-generator identities from the canonical common-open theorem. -/
theorem canonical_chart_coordinate_consumer
    {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0)
    {B : Type w} [CommRing B]
    [Algebra
      (Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))) B]
    (M : Ideal B) [M.IsPrime]
    (f : Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j))))
    (e : Localization.Away f ≃ₐ[
      Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))]
      Localization.Away (algebraMap _ B f)) :
    let Q := Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
    let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
      componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
        (SelectedAffineCoordinateEquiv j) (by
          simpa [componentProjectivePoint] using hxj)
    let g := hsel (selectedAffineChartDenominator P j)
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq C := inferInstance
    letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
    let φ := originalAffineChartToCommonOpen P j hxj hsel M f e
    let q : Fin (m + 1) → C := Fin.cases
      (algebraMap Cq C (algebraMap Q Cq g))
      (fun i => if hij : i = j then 1 else
        algebraMap Cq C (algebraMap Q Cq
          (hsel (selectedAffineChartVariableClass P j i hij))))
    q (Fin.succ j) = 1 ∧
      ∀ i : Fin m, q (Fin.succ i) =
        q 0 * φ (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) := by
  exact canonicalChart_all_normalized_projective_coordinates P j hxj M f e

#print axioms canonical_chart_coordinate_consumer

end Stafford38.Geometry.A0NormalizedProjectiveCoordinatesConsumer
end
