module
public import Stafford38.Geometry.ChartGenericPointFractionRing

@[expose] public section

noncomputable section
set_option autoImplicit false

open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.ChartGenericPointFractionRing

universe u

/-- Consumer check: every element of the component function field is a quotient
of classes in the exact dehomogenized chart equation ring. -/
theorem chart_function_field_element_is_quotient_of_chart_classes
    {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (eidx : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0)
    (z : ComponentFractionField P) :
    let R := MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart eidx
    letI : Algebra R (ComponentFractionField P) :=
      (componentChartEquationGenericPointMap P chart eidx hchart).toRingHom.toAlgebra
    ∃ a b : R, b ∈ nonZeroDivisors R ∧
      z = algebraMap R (ComponentFractionField P) a /
        algebraMap R (ComponentFractionField P) b := by
  let R := MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart eidx
  letI : Algebra R (ComponentFractionField P) :=
    (componentChartEquationGenericPointMap P chart eidx hchart).toRingHom.toAlgebra
  letI : IsFractionRing R (ComponentFractionField P) :=
    componentChartEquationQuotient_isFractionRing P chart eidx hchart
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R z
  exact ⟨a, b, hb, hab.symm⟩

#print axioms chart_function_field_element_is_quotient_of_chart_classes
