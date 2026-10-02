import Stafford38.Geometry.ProjectiveConormalDehomogenization
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Tactic.NormNum

open Stafford38.Geometry.ProjectiveConormalDehomogenization

noncomputable section
abbrev R := MvPolynomial (Fin 1) ℚ
local instance : Algebra R ℚ := (MvPolynomial.aeval (fun _ : Fin 1 => (2 : ℚ))).toAlgebra
local instance : IsScalarTower ℚ R ℚ := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  change x = (MvPolynomial.aeval (fun _ : Fin 1 => (2 : ℚ))) (MvPolynomial.C x)
  simp

/-- For q=(t²,t³) at t=2, the affine coordinate is t and its
 derivative is exactly 1, despite the projective radial scaling. -/
theorem nonlinear_projective_derivation_oracle :
    dehomogenizedTangentColumn
      (fun i : Fin 2 => algebraMap R ℚ
        (if i = 0 then (MvPolynomial.X (0 : Fin 1)) ^ 2 else
          (MvPolynomial.X (0 : Fin 1)) ^ 3))
      (fun i : Fin 2 => (MvPolynomial.mkDerivation ℚ
        (fun _ : Fin 1 => (1 : ℚ)))
        (if i = 0 then (MvPolynomial.X (0 : Fin 1)) ^ 2 else
          (MvPolynomial.X (0 : Fin 1)) ^ 3)) =
      (fun _ : Fin 1 => (1 : ℚ)) := by
  have h := dehomogenizedTangentColumn_derivation
    (MvPolynomial.mkDerivation ℚ (fun _ : Fin 1 => (1 : ℚ)))
    (fun i : Fin 2 => if i = 0 then (MvPolynomial.X (0 : Fin 1)) ^ 2 else
      (MvPolynomial.X (0 : Fin 1)) ^ 3)
    (fun _ : Fin 1 => MvPolynomial.X (0 : Fin 1))
    (by norm_num [algebraMap])
    (by intro i; simp; ring)
  simpa only [MvPolynomial.mkDerivation_X] using h

#print axioms nonlinear_projective_derivation_oracle
#print axioms Stafford38.Geometry.ProjectiveConormalDehomogenization.dehomogenizedTangentColumn_derivation
