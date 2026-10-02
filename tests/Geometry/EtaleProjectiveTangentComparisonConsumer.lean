import Stafford38.Geometry.EtaleProjectiveTangentComparison
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


open Stafford38.Geometry.EtaleProjectiveTangentComparison
open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.AffineConormalSpan

/-- The radial column (4,12) and the derivative column (0,4) span every
projective tangent vector of the affine line at 3; their determinant is 16. -/
theorem rational_projective_tangent_cone_oracle (v : Fin 2 → ℚ) :
    let q : Fin 2 → A := fun i =>
      if i = 0 then 4 else 4 * Ideal.Quotient.mk (⊥ : Ideal R) (MvPolynomial.X 0)
    v ∈ projectiveTangentCone (fun i => algebraMap A ℚ (q i))
      (zariskiTangentSpace (dehomogenizedPoint (fun i => algebraMap A ℚ (q i)))
        ((⊥ : Ideal R).map (MvPolynomial.map (algebraMap ℚ ℚ)))) := by
  dsimp only
  let q : Fin 2 → A := fun i =>
    if i = 0 then 4 else 4 * Ideal.Quotient.mk (⊥ : Ideal R) (MvPolynomial.X 0)
  have h0 : algebraMap A ℚ (q 0) ≠ 0 := by norm_num [q, map_ofNat]
  have hfactor : ∀ i : Fin 1, q i.succ = q 0 *
      algebraMap A A (Ideal.Quotient.mk (⊥ : Ideal R) (MvPolynomial.X i)) := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [q]
  rw [projectiveTangentCone_eq_span_chartDerivation_columns (r := 1) q h0 hfactor]
  let cols : Option (Fin 1) → Fin 2 → ℚ := fun j => fun i =>
    match j with
    | none => algebraMap A ℚ (q i)
    | some j => coordinateDerivation (k := ℚ) (σ := Fin 1) (B := A) (L := ℚ) j (q i)
  suffices hvspan : v ∈ Submodule.span ℚ (Set.range cols) by
    convert hvspan using 1
    congr 1
    congr 1
    funext j i
    cases j <;> rfl
  have hxval : algebraMap A ℚ
      (Ideal.Quotient.mk (⊥ : Ideal R) (MvPolynomial.X (0 : Fin 1))) = 3 := by
    change (MvPolynomial.aeval (fun _ : Fin 1 => (3 : ℚ)))
      ((AlgEquiv.quotientBot ℚ R)
        (Ideal.Quotient.mk (⊥ : Ideal R) (MvPolynomial.X (0 : Fin 1)))) = 3
    simp
  have hd4 : coordinateDerivation (k := ℚ) (σ := Fin 1) (B := A) (L := ℚ)
      (0 : Fin 1) (4 : A) = 0 := by
    simpa using (coordinateDerivation (k := ℚ) (σ := Fin 1) (B := A) (L := ℚ)
      (0 : Fin 1)).map_natCast 4
  have hrad : cols none = (fun i : Fin 2 => if i = 0 then 4 else 12) := by
    ext i
    fin_cases i <;> norm_num [cols, q, map_ofNat, hxval]
  have hder : cols (some 0) = (fun i : Fin 2 => if i = 0 then 0 else 4) := by
    ext i
    fin_cases i
    · simp [cols, q, hd4]
    · simp only [cols, q, Fin.mk_one, show ¬ (1 : Fin 2) = 0 by decide,
        if_false, Derivation.leibniz, Algebra.smul_def, map_ofNat, hd4]
      have hX := coordinateDerivation_apply_parameter
        (k := ℚ) (σ := Fin 1) (B := A) (L := ℚ) (0 : Fin 1) 0
      simpa [Ideal.Quotient.algebraMap_eq] using congrArg (fun x : ℚ => 4*x) hX
  have hv : v = (v 0 / 4) • cols none + ((v 1 - 3 * v 0) / 4) • cols (some 0) := by
    rw [hrad, hder]
    ext i
    fin_cases i <;> simp <;> ring
  rw [hv]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨some 0, rfl⟩)

#print axioms rational_projective_tangent_cone_oracle
#print axioms Stafford38.Geometry.EtaleProjectiveTangentComparison.projectiveTangentCone_eq_span_chartDerivation_columns
