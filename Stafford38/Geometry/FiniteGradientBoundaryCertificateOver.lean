import Stafford38.Geometry.LaurentConormalResidueExtension
import Stafford38.Geometry.CoisotropicTranslation
import Stafford38.Geometry.RetractionSpecialization

/-!
# Shared finite-gradient boundary certificate

This is the single record owner for finite-gradient boundary data over a
ground field `k` and a boundary residue field `K`.  The base-field producer
uses its checked `K = k` specialization; residue-extension consumers retain
the full coefficient-extension scope.
-/

namespace Stafford38.Geometry.FiniteGradientResidueExtension

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A completed projective arc and one finite gradient identity over the
natural boundary residue field `K`, for an affine ideal defined over `k`. -/
structure FiniteGradientBoundaryCertificateOver
    (m : ℕ) (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) where
  equationCount : ℕ
  q : Fin (m + 1) → PowerSeries K
  ell : Fin (m + 1) → PowerSeries K
  q_origin_ne : q 0 ≠ 0
  projective_annihilation :
    ∑ i, laurentColumn ell i * laurentColumn q i = 0
  base_vanish :
    ∀ f ∈ I.map (groundPolynomialMap (k := k) (K := K) (Fin m)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0
  equations : Fin equationCount →
    I.map (groundPolynomialMap (k := k) (K := K) (Fin m))
  coefficients : Fin equationCount → LaurentSeries K
  gradient_identity : ∀ i : Fin m,
    laurentColumn ell i.succ =
      ∑ j, coefficients j *
        differentialAt (dehomogenizedPoint (laurentColumn q))
          (equations j).1 i
  residue_axis :
    residueColumn (fun i : Fin m ↦ ell i.succ) =
      (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0)

end

end Stafford38.Geometry.FiniteGradientResidueExtension
