module
public import Stafford38.Geometry.SmoothAffinePointScalarExtension

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.SmoothAffinePointScalarExtensionConsumer

open Stafford38.Geometry.SmoothAffineConormal

universe u

variable {k L : Type u} [Field k] [Field L] [Algebra k L] {n : ℕ}

theorem original_arc_point_avoiding_open_is_smooth
    (I : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin n) k ⧸ I)
    (hg : Algebra.Smooth k (Localization.Away g))
    (φ : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] L)
    (havoid : φ g ≠ 0) :
    SmoothAffinePoint (k := L)
      (I.map (Stafford38.Geometry.ScalarExtensionPoints.scalarPolynomialMap
        (k := k) (K := L) (Fin n)))
      (fun i ↦ φ (Ideal.Quotient.mk I (MvPolynomial.X i))) :=
  Stafford38.Geometry.SmoothAffinePointScalarExtension.smoothAffinePoint_of_quotient_point_avoiding_smooth_away
    (k := k) I g hg φ havoid

#print axioms original_arc_point_avoiding_open_is_smooth

end Stafford38.Geometry.SmoothAffinePointScalarExtensionConsumer

#print axioms Stafford38.Geometry.SmoothAffinePointScalarExtension.exists_generic_smooth_open_point_criterion
