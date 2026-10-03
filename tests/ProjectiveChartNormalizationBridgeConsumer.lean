module
public import Stafford38.Geometry.ProjectiveChartNormalizationBridge

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
universe u
open Stafford38.Geometry.ProjectiveChartNormalizationBridge
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open AlgebraicGeometry
open Stafford38.Geometry.AsymptoticChartArcAdapter

local instance {k : Type u} [Field k] {m : ℕ} :
    GradedRing (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k) :=
  MvPolynomial.gradedAlgebra

example {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (chart : Fin (m + 1)) :
    (MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart
      (Stafford38.Geometry.AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart)) ≃+*
      (HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart)) ⧸
        componentHomogeneousChartIdealAny P chart :=
  componentChartClosedRingEquivAny P chart

example {k : Type 1} [Field k] {m : ℕ}
    (chart : Fin (m + 1)) :
    (Proj.basicOpen (G k m) (MvPolynomial.X chart)).toScheme ≅
      Spec (.of (HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart))) :=
  componentBasicOpenProjIsoSpecAny chart

#print axioms Stafford38.Geometry.ProjectiveChartNormalizationBridge.componentChartClosedRingEquivAny
#print axioms Stafford38.Geometry.ProjectiveChartNormalizationBridge.componentChartEquationIdeal_map_eq_any
