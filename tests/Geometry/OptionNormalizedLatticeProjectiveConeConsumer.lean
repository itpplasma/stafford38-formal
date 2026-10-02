import Stafford38.Geometry.NormalizedLatticeProjectiveConeAdapter
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.MvPolynomial.Rename

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Stafford38.Geometry.NormalizedLatticeProjectiveConeAdapter
open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.PaperDivisorTangent
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.GeneralTangentLimitCriterion

noncomputable section

abbrev P := MvPolynomial (Fin 1) ℚ
abbrev S := MvPolynomial (Option (Fin 0)) ℚ
abbrev A := P ⧸ (⊥ : Ideal P)
abbrev C := S

def parameterIndexEquiv : Fin 1 ≃ Option (Fin 0) where
  toFun _ := none
  invFun _ := 0
  left_inv i := by fin_cases i; rfl
  right_inv j := by cases j with | none => rfl | some j => exact Fin.elim0 j

def sourcePolynomialEquiv : P ≃ₐ[ℚ] S :=
  MvPolynomial.renameEquiv ℚ parameterIndexEquiv

def quotientToChartEquiv : A ≃ₐ[ℚ] C :=
  (AlgEquiv.quotientBot ℚ P).trans sourcePolynomialEquiv

local instance : Algebra ℚ A := Ideal.Quotient.algebra ℚ
local instance : Algebra P A := Ideal.Quotient.algebra P
local instance : SMul ℚ A := (inferInstance : Algebra ℚ A).toSMul
local instance : SMul P A := (inferInstance : Algebra P A).toSMul
local instance : Algebra P C := sourcePolynomialEquiv.toAlgHom.toAlgebra
local instance : Algebra A C := quotientToChartEquiv.toAlgHom.toAlgebra
local instance : SMul A C := (inferInstance : Algebra A C).toSMul
local instance : Algebra S C := inferInstance
local instance : SMul S C := (inferInstance : Algebra S C).toSMul

local instance : IsScalarTower ℚ P A := inferInstance
local instance : IsScalarTower ℚ P C := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact (sourcePolynomialEquiv.commutes x).symm
local instance : IsScalarTower ℚ A C := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact (quotientToChartEquiv.commutes x).symm
local instance : IsScalarTower ℚ S C := inferInstance
local instance : IsScalarTower P A C := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro p
  change quotientToChartEquiv (Ideal.Quotient.mk ⊥ p) = sourcePolynomialEquiv p
  simp [quotientToChartEquiv]

local instance : Algebra.FormallyEtale A C := by
  let e : A ≃ₐ[A] C := {
    toFun := algebraMap A C
    invFun := quotientToChartEquiv.symm
    left_inv := by intro x; change quotientToChartEquiv.symm (quotientToChartEquiv x) = x; simp
    right_inv := by intro x; change quotientToChartEquiv (quotientToChartEquiv.symm x) = x; simp
    map_mul' := by intro x y; exact map_mul (algebraMap A C) x y
    map_add' := by intro x y; exact map_add (algebraMap A C) x y
    commutes' := by intro x; rfl
  }
  exact Algebra.FormallyEtale.of_equiv e
local instance : Algebra.FormallyEtale S C := inferInstance

def rho : C →+* LaurentSeries ℚ :=
  (MvPolynomial.aeval (fun _ : Option (Fin 0) =>
    (3 : LaurentSeries ℚ) + algebraMap (PowerSeries ℚ) (LaurentSeries ℚ) PowerSeries.X) :
      S →ₐ[ℚ] LaurentSeries ℚ).toRingHom

local instance : Algebra C (LaurentSeries ℚ) := rho.toAlgebra
local instance : Algebra ℚ (LaurentSeries ℚ) :=
  RingHom.toAlgebra' (algebraMap ℚ (LaurentSeries ℚ)) (by intro x y; exact mul_comm _ _)
local instance : Module ℚ (LaurentSeries ℚ) := Algebra.toModule
local instance : SMul ℚ (LaurentSeries ℚ) :=
  (Algebra.toModule : Module ℚ (LaurentSeries ℚ)).toSMul
local instance : Algebra A (LaurentSeries ℚ) :=
  RingHom.toAlgebra' (rho.comp (algebraMap A C)) (by intro x y; exact mul_comm _ _)
local instance : Algebra P (LaurentSeries ℚ) :=
  RingHom.toAlgebra' (rho.comp (algebraMap P C)) (by intro x y; exact mul_comm _ _)
local instance : Algebra S (LaurentSeries ℚ) :=
  RingHom.toAlgebra' (rho.comp (algebraMap S C)) (by intro x y; exact mul_comm _ _)

theorem hground : rho.comp (algebraMap ℚ C) = algebraMap ℚ (LaurentSeries ℚ) := by
  apply RingHom.ext
  intro x
  simp [rho]

local instance : IsScalarTower ℚ C (LaurentSeries ℚ) :=
  IsScalarTower.of_algebraMap_eq' hground.symm
local instance : IsScalarTower A C (LaurentSeries ℚ) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower P C (LaurentSeries ℚ) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower S C (LaurentSeries ℚ) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℚ A (LaurentSeries ℚ) := by
  apply IsScalarTower.of_algebraMap_eq'
  calc
    algebraMap ℚ (LaurentSeries ℚ) = rho.comp (algebraMap ℚ C) := hground.symm
    _ = rho.comp ((algebraMap A C).comp (algebraMap ℚ A)) := by
      congr 1
      exact IsScalarTower.algebraMap_eq ℚ A C
    _ = (rho.comp (algebraMap A C)).comp (algebraMap ℚ A) := rfl
local instance : IsScalarTower ℚ P (LaurentSeries ℚ) := by
  apply IsScalarTower.of_algebraMap_eq'
  calc
    algebraMap ℚ (LaurentSeries ℚ) = rho.comp (algebraMap ℚ C) := hground.symm
    _ = rho.comp ((algebraMap P C).comp (algebraMap ℚ P)) := by
      congr 1
      exact IsScalarTower.algebraMap_eq ℚ P C
    _ = (rho.comp (algebraMap P C)).comp (algebraMap ℚ P) := rfl
local instance : IsScalarTower ℚ S (LaurentSeries ℚ) := by
  apply IsScalarTower.of_algebraMap_eq'
  calc
    algebraMap ℚ (LaurentSeries ℚ) = rho.comp (algebraMap ℚ C) := hground.symm
    _ = rho.comp ((algebraMap S C).comp (algebraMap ℚ S)) := by
      congr 1
    _ = (rho.comp (algebraMap S C)).comp (algebraMap ℚ S) := rfl
local instance : IsScalarTower P A (LaurentSeries ℚ) := by
  apply IsScalarTower.of_algebraMap_eq'
  calc
    algebraMap P (LaurentSeries ℚ) = rho.comp (algebraMap P C) := rfl
    _ = rho.comp ((algebraMap A C).comp (algebraMap P A)) := by
      exact congrArg (fun f : P →+* C => rho.comp f) (IsScalarTower.algebraMap_eq P A C)
    _ = (rho.comp (algebraMap A C)).comp (algebraMap P A) := rfl

def qC : Fin 2 → C := fun i => if i = 0 then 1 else MvPolynomial.X none

def q : Fin 2 → PowerSeries ℚ := fun i =>
  if i = 0 then PowerSeries.C 1 else PowerSeries.C 3 + PowerSeries.X

def Z : Matrix (Fin 2) (Fin 0) (PowerSeries ℚ) := fun _ j => Fin.elim0 j

def tau : Fin 2 → PowerSeries ℚ := fun i => PowerSeries.derivative ℚ (q i)

def alpha : Fin 0 → PowerSeries ℚ := Fin.elim0

theorem chartCoordinate : algebraMap A C (Ideal.Quotient.mk ⊥ (MvPolynomial.X (0 : Fin 1))) =
    MvPolynomial.X none := by
  change quotientToChartEquiv (Ideal.Quotient.mk ⊥ (MvPolynomial.X (0 : Fin 1))) = _
  simp [quotientToChartEquiv, sourcePolynomialEquiv, parameterIndexEquiv]

theorem hposition : ∀ i, rho (qC i) =
    algebraMap (PowerSeries ℚ) (LaurentSeries ℚ) (q i) := by
  intro i
  fin_cases i <;> simp [qC, q, rho, HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_X]

theorem htransverse : ∀ (j : Fin 0) (i : Fin 2),
    coordinateDerivation (k := ℚ) (σ := Option (Fin 0)) (B := C)
      (L := LaurentSeries ℚ) (some j) (qC i) =
      algebraMap (PowerSeries ℚ) (LaurentSeries ℚ) (Z i j) := by
  intro j
  exact Fin.elim0 j

theorem hraw : ∀ i, algebraMap (PowerSeries ℚ) (LaurentSeries ℚ)
      (PowerSeries.derivative ℚ (q i)) =
    coordinateDerivation (k := ℚ) (σ := Option (Fin 0)) (B := C)
      (L := LaurentSeries ℚ) (none : Option (Fin 0)) (qC i) +
      ∑ j : Fin 0, algebraMap (PowerSeries ℚ) (LaurentSeries ℚ) (alpha j) *
        coordinateDerivation (k := ℚ) (σ := Option (Fin 0)) (B := C)
          (L := LaurentSeries ℚ) (some j) (qC i) := by
  intro i
  fin_cases i
  · simp [q, qC]
  · have hD : coordinateDerivation (k := ℚ) (σ := Option (Fin 0))
        (B := C) (L := LaurentSeries ℚ) none (MvPolynomial.X none) = 1 := by
      simpa using coordinateDerivation_apply_parameter (k := ℚ) (σ := Option (Fin 0))
        (B := C) (L := LaurentSeries ℚ) (i := none) (j := none)
    simp [q, qC, hD]

theorem hq0 : algebraMap C (LaurentSeries ℚ) (qC 0) ≠ 0 := by
  simp [qC]

theorem hchart : ∀ i : Fin 1, qC i.succ = qC 0 *
    algebraMap A C (Ideal.Quotient.mk ⊥ (MvPolynomial.X i)) := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [qC, chartCoordinate]

theorem literal_option_normalized_projective_cone_oracle :
    genericFibre (normalizedTangentLattice q Z tau) =
      projectiveTangentCone (fun i => rho (qC i))
        (zariskiTangentSpace (dehomogenizedPoint (fun i => rho (qC i)))
          ((⊥ : Ideal P).map (MvPolynomial.map (algebraMap ℚ (LaurentSeries ℚ))))) := by
  have hcorrection : ∀ i, PowerSeries.derivative ℚ (q i) - Z.mulVec alpha i =
      (PowerSeries.X : PowerSeries ℚ) ^ 0 * tau i := by
    intro i
    simp [tau]
  exact genericFibre_normalizedTangentLattice_eq_actualProjectiveTangentCone
    (rho := rho) hground q Z tau alpha 0 hcorrection qC
    hposition htransverse hraw hq0 hchart

#print axioms literal_option_normalized_projective_cone_oracle
