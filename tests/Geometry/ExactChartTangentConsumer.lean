import Stafford38.Geometry.EtaleTangentChartSpan
import Mathlib.RingTheory.Ideal.Quotient.Operations

open Stafford38.Geometry.EtaleTangentChartSpan
open Stafford38.Geometry.EtaleCotangentBasis

noncomputable section

abbrev R := MvPolynomial (Fin 1) ℚ
abbrev A := R ⧸ (⊥ : Ideal R)

local instance : Algebra R ℚ := (MvPolynomial.aeval (fun _ : Fin 1 => (3 : ℚ))).toAlgebra
local instance : Algebra A ℚ :=
  ((MvPolynomial.aeval (fun _ : Fin 1 => (3 : ℚ))).comp
    (AlgEquiv.quotientBot ℚ R).toAlgHom).toAlgebra
local instance : SMul ℚ A := (inferInstance : Algebra ℚ A).toSMul
local instance : SMul A A := (inferInstance : Algebra A A).toSMul
local instance : IsScalarTower A A ℚ where
  smul_assoc x y z := by
    change algebraMap A ℚ (x * y) * z =
      algebraMap A ℚ x * (algebraMap A ℚ y * z)
    rw [map_mul, mul_assoc]
local instance : SMul R A := (inferInstance : Algebra R A).toSMul
local instance : IsScalarTower ℚ A ℚ := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change x = ((MvPolynomial.aeval (fun _ : Fin 1 => (3 : ℚ))).comp
    (AlgEquiv.quotientBot ℚ R).toAlgHom) (algebraMap ℚ A x)
  simp
local instance : IsScalarTower R A ℚ := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro p
  change (MvPolynomial.aeval (fun _ : Fin 1 => (3 : ℚ))) p =
    ((MvPolynomial.aeval (fun _ : Fin 1 => (3 : ℚ))).comp
      (AlgEquiv.quotientBot ℚ R).toAlgHom) (Ideal.Quotient.mk ⊥ p)
  simp
local instance : IsScalarTower ℚ R ℚ := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change x = (MvPolynomial.aeval (fun _ : Fin 1 => (3 : ℚ))) (MvPolynomial.C x)
  simp
local instance : Algebra.FormallyEtale R A :=
  Algebra.FormallyEtale.of_equiv (AlgEquiv.quotientBot R R).symm

/-- At the rational point 3 of the affine line, the canonical parameter
 derivative column is 1; the tangent space therefore contains every scalar. -/
theorem rational_affine_line_tangent_oracle (v : Fin 1 → ℚ) :
    v ∈ Stafford38.Geometry.AffineConormalSpan.zariskiTangentSpace
      (fun _ : Fin 1 => (3 : ℚ))
      ((⊥ : Ideal R).map (MvPolynomial.map (algebraMap ℚ ℚ))) := by
  rw [zariskiTangentSpace_eq_span_parameterDerivations
    (r := 1) (C := A) (L := ℚ) (fun _ : Fin 1 => (3 : ℚ))]
  · have hcol : (fun i : Fin 1 => coordinateDerivation
        (k := ℚ) (σ := Fin 1) (B := A) (L := ℚ) (0 : Fin 1)
        (algebraMap A A (Ideal.Quotient.mk (⊥ : Ideal R) (MvPolynomial.X i)))) =
        (fun _ : Fin 1 => (1 : ℚ)) := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa [Algebra.algebraMap_self, RingHom.id_apply,
        Ideal.Quotient.algebraMap_eq] using
        coordinateDerivation_apply_parameter
          (k := ℚ) (σ := Fin 1) (B := A) (L := ℚ) (0 : Fin 1) 0
    have hmem : (fun _ : Fin 1 => (1 : ℚ)) ∈
        Submodule.span ℚ (Set.range fun j : Fin 1 => fun i : Fin 1 =>
          coordinateDerivation (k := ℚ) (σ := Fin 1) (B := A) (L := ℚ) j
            (algebraMap A A (Ideal.Quotient.mk (⊥ : Ideal R) (MvPolynomial.X i)))) :=
      Submodule.subset_span ⟨0, hcol⟩
    have hv : v = v 0 • (fun _ : Fin 1 => (1 : ℚ)) := by
      ext i
      simp [Subsingleton.elim i (0 : Fin 1)]
    rw [hv]
    exact Submodule.smul_mem _ _ hmem
  · intro i
    simp [algebraMap]

#print axioms rational_affine_line_tangent_oracle
#print axioms Stafford38.Geometry.EtaleTangentChartSpan.zariskiTangentSpace_eq_span_parameterDerivations
