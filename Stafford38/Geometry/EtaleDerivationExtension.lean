module
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

set_option autoImplicit false
open scoped TensorProduct

namespace Stafford38.Geometry.EtaleDerivationExtension

noncomputable section

variable {k A U L : Type*}
variable [CommRing k] [CommRing A] [CommRing U] [Field L]
variable [Algebra k A] [Algebra k U] [Algebra A U]
variable [IsScalarTower k A U]
variable [Algebra U L] [Algebra A L] [Algebra k L]
variable [IsScalarTower A U L] [IsScalarTower k A L] [IsScalarTower k U L]
variable [Algebra.FormallyEtale A U]

/-- Extend a derivation across a formally étale algebra by transporting its
Kähler functional through the canonical cotangent base-change equivalence. -/
noncomputable def extendDerivation (D : Derivation k A L) : Derivation k U L := by
  let d : Ω[A⁄k] →ₗ[A] L := D.liftKaehlerDifferential
  let T : U ⊗[A] Ω[A⁄k] →ₗ[U] L := d.liftBaseChange U
  let E : U ⊗[A] Ω[A⁄k] ≃ₗ[U] Ω[U⁄k] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A U
  exact KaehlerDifferential.linearMapEquivDerivation k U (T.comp E.symm.toLinearMap)

/-- The extended derivation restricts to the original derivation on `A`. -/
theorem extendDerivation_algebraMap (D : Derivation k A L) (a : A) :
    extendDerivation (k := k) (A := A) (U := U) (L := L) D
      (algebraMap A U a) = D a := by
  simp [extendDerivation,
    KaehlerDifferential.linearMapEquivDerivation_apply_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul,
    Derivation.liftKaehlerDifferential_comp_D]


end

end Stafford38.Geometry.EtaleDerivationExtension
