module
public import Stafford38.Geometry.ComponentProjectiveChartKernel
public import Stafford38.Geometry.IntegralPolynomialExtensionDimension

@[expose] public section

/-! Independent API consumer for the affine chart-kernel and local height bridges. -/

set_option autoImplicit false

namespace Stafford38.Tests.ProjectiveDivisorChartBridgeConsumer

open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.IntegralPolynomialExtensionDimension

universe u
variable {k : Type u} [Field k] {m : ℕ}

theorem chart_membership_iff_generic_ratio_evaluation
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0)
    (f : MvPolynomial (Fin m) k) :
    f ∈ componentChartEquationIdeal P chart e ↔
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (chartGenericPoint P chart e) f = 0 := by
  rw [componentChartEquationIdeal_eq_genericEvalKer P chart e hchart]
  rfl

theorem maximal_height_bound_from_polynomial_normalization
    {E A : Type*} [Field E] [CommRing A] [IsDomain A] [Algebra E A]
    (f : Polynomial E →ₐ[E] A) (hint : f.toRingHom.IsIntegral)
    (p : PrimeSpectrum A) [p.asIdeal.IsMaximal] : p.asIdeal.height ≤ 1 :=
  height_le_one_of_integral_polynomial_map f hint p

#print axioms chart_membership_iff_generic_ratio_evaluation
#print axioms maximal_height_bound_from_polynomial_normalization

end Stafford38.Tests.ProjectiveDivisorChartBridgeConsumer
