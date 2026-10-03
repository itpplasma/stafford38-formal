module
public import Stafford38.Geometry.SmoothAffinePointScalarExtension
public import Mathlib.RingTheory.Smooth.Basic

@[expose] public section

set_option autoImplicit false

open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.SmoothAffinePointScalarExtension

namespace Stafford38.Geometry.SmoothAffinePointScalarExtensionConsumer

private abbrev P := MvPolynomial (Fin 1) ℚ
private noncomputable def I : Ideal P := ⊥
private abbrev A := P ⧸ I

private noncomputable def quotientEquiv : A ≃ₐ[ℚ] P :=
  AlgEquiv.quotientBot ℚ P

private noncomputable def point : A →ₐ[ℚ] ℚ :=
  (MvPolynomial.aeval (fun _ : Fin 1 => (4 : ℚ))).comp quotientEquiv.toAlgHom

private theorem smoothAwayOne : Algebra.Smooth ℚ
    (Localization.Away (Ideal.Quotient.mk I (1 : P))) := by
  let : Algebra.Smooth ℚ P := {
    formallySmooth := inferInstance
    finitePresentation := inferInstance
  }
  let : Algebra.Smooth ℚ A := Algebra.Smooth.of_equiv quotientEquiv.symm
  let : Algebra.Smooth A
      (Localization.Away (Ideal.Quotient.mk I (1 : P))) :=
    Algebra.Smooth.of_isLocalization_Away (Ideal.Quotient.mk I (1 : P))
  let : Algebra A (Localization.Away (Ideal.Quotient.mk I (1 : P))) := inferInstance
  let : IsScalarTower ℚ A (Localization.Away (Ideal.Quotient.mk I (1 : P))) := inferInstance
  exact Algebra.Smooth.comp ℚ A _

private theorem point_avoids_one :
    point (Ideal.Quotient.mk I (1 : P)) ≠ 0 := by
  simp [point]

theorem rationalArcField_point_is_smooth :
    SmoothAffinePoint (k := ℚ)
      (I.map (Stafford38.Geometry.ScalarExtensionPoints.scalarPolynomialMap
        (k := ℚ) (K := ℚ) (Fin 1)))
      (fun i ↦ point (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
  exact smoothAffinePoint_of_quotient_point_avoiding_smooth_away
    (k := ℚ) (L := ℚ) (n := 1) I
    (Ideal.Quotient.mk I (1 : P)) smoothAwayOne point point_avoids_one

#print axioms rationalArcField_point_is_smooth

end Stafford38.Geometry.SmoothAffinePointScalarExtensionConsumer
