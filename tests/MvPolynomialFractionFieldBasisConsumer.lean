module
public import Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.MvPolynomialFractionFieldBasisConsumer

universe u

variable {k : Type u} [Field k] (d : ℕ)

theorem canonicalFractionFieldBasis :
    IsTranscendenceBasis k
      (fun i : ULift.{u} (Fin d) =>
        algebraMap (MvPolynomial (Fin d) k)
          (FractionRing (MvPolynomial (Fin d) k)) (MvPolynomial.X i.down)) :=
  Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis.standardVariables_isTranscendenceBasis d

theorem canonicalFractionFieldFiniteTrdeg :
    Algebra.trdeg k (FractionRing (MvPolynomial (Fin d) k)) < Cardinal.aleph0 :=
  Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis.trdeg_lt_aleph0 d

#print axioms canonicalFractionFieldBasis
#print axioms canonicalFractionFieldFiniteTrdeg

end Stafford38.Geometry.MvPolynomialFractionFieldBasisConsumer
