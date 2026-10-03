module
public import Stafford38.Geometry.ProjectiveChartNormalizationFinite
public import Stafford38.Geometry.AffineComponentCoordinateSplit
public import Stafford38.Geometry.ComponentFunctionFieldBoundary
public import Stafford38.Geometry.ComponentProjectiveClosure
public import Stafford38.Geometry.ComponentProjectiveChartFactorization
public import Stafford38.Geometry.ComponentProjectiveChartKernel
public import Stafford38.Geometry.ProjectiveChartCoordinates
public import Stafford38.Geometry.ChartGenericPointFractionRing
public import Mathlib.RingTheory.FiniteType

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ChartGenericPointFractionRing

universe u

/-- The exact chart equation quotient has a finite-type normalization over k
before introducing any residue-basis localization. -/
theorem chart_normalization_finite_type_over_ground
    (k : Type u) [Field k] [CharZero k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) :
    let R := MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e
    let F := ComponentFractionField P
    letI : Algebra R F :=
      (componentChartEquationGenericPointMap P chart e hchart).toRingHom.toAlgebra
    let C : Subalgebra R F := integralClosure R F
    letI : Algebra k C := Algebra.compHom C (algebraMap k R)
    letI : IsScalarTower k R C := IsScalarTower.of_algebraMap_eq' (R := k) (S := R) (A := C) rfl
    Algebra.FiniteType k C := by
  let R := MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e
  let F := ComponentFractionField P
  letI : Algebra R F :=
    (componentChartEquationGenericPointMap P chart e hchart).toRingHom.toAlgebra
  have hprime : (componentChartEquationIdeal P chart e).IsPrime := by
    rw [componentChartEquationIdeal_eq_genericEvalKer P chart e hchart]
    exact RingHom.ker_isPrime _
  letI : IsDomain R := (Ideal.Quotient.isDomain_iff_prime (componentChartEquationIdeal P chart e)).2 hprime
  letI : IsFractionRing R F :=
    componentChartEquationQuotient_isFractionRing P chart e hchart
  let C : Subalgebra R F := integralClosure R F
  letI : Algebra k C := Algebra.compHom C (algebraMap k R)
  haveI : IsScalarTower k R C := IsScalarTower.of_algebraMap_eq' (R := k) (S := R) (A := C) rfl
  haveI : Algebra.FiniteType k R := inferInstance
  haveI : Module.Finite R C :=
    Stafford38.Geometry.ProjectiveChartNormalizationFinite.finite_integralClosure_in_fractionField
      k R F
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k R)
    (inferInstance : Algebra.FiniteType R C)

#print axioms chart_normalization_finite_type_over_ground
