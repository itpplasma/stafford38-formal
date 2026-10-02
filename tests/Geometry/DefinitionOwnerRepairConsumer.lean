import proofs.stafford38_reduction
import Stafford38.Geometry.ComponentProjectiveChartKernel
import Stafford38.Geometry.ChartGenericPointFractionRing
import Stafford38.Geometry.ProjectiveChartSameFieldOverlap

set_option autoImplicit false

namespace Stafford38.Geometry.DefinitionOwnerRepairConsumer

open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ProjectiveChartCoordinates

universe u
variable {k : Type u} [Field k] {m : ℕ}

/-- The canonical map acts on every polynomial quotient generator by evaluation. -/
theorem chartMap_generator
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0)
    (p : MvPolynomial (Fin m) k) :
    ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap
        P chart e hchart
        (Ideal.Quotient.mk _ p) =
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (ComponentProjectiveChartKernel.chartGenericPoint P chart e) p :=
  ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap_mk
    P chart e hchart p

/-- The map is uniquely determined by its evaluation after quotienting. -/
theorem chartMap_unique
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0)
    (f : (MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e) →ₐ[k]
      ComponentFractionField P)
    (hf : f.comp (Ideal.Quotient.mkₐ k (componentChartEquationIdeal P chart e)) =
        MvPolynomial.aeval (ComponentProjectiveChartKernel.chartGenericPoint P chart e)) :
    f = ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap
      P chart e hchart :=
  ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap_unique
    P chart e hchart f hf

/-- The transcendence-basis API keeps the same field-valued quotient map. -/
theorem chartGenericPoint_map_is_canonical
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) :
    ChartGenericPointFractionRing.componentChartEquationGenericPointMap
      P chart e hchart =
    ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap
      P chart e hchart := rfl

/-- The reduction's `ad` notation has the shared ordered commutator meaning. -/
theorem reduction_ad_shared {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (Y u : A) :
    Stafford.Reduction.ad Y u = AlgebraicAnalysis.ringCommutator Y u := rfl

theorem reduction_ad_formula {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (Y u : A) : Stafford.Reduction.ad Y u = Y * u - u * Y := by
  simp [Stafford.Reduction.ad, AlgebraicAnalysis.ringCommutator]

end Stafford38.Geometry.DefinitionOwnerRepairConsumer

#print axioms Stafford38.Geometry.ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap
#print axioms Stafford38.Geometry.ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap_mk
#print axioms Stafford38.Geometry.ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap_comp_mk
#print axioms Stafford38.Geometry.ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap_unique
#print axioms Stafford.Reduction.ad_eq_shared

#print axioms Stafford38.Geometry.DefinitionOwnerRepairConsumer.chartMap_generator
#print axioms Stafford38.Geometry.DefinitionOwnerRepairConsumer.chartMap_unique
#print axioms Stafford38.Geometry.DefinitionOwnerRepairConsumer.reduction_ad_formula
