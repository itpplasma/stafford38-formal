import Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis

set_option autoImplicit false

namespace Stafford38.Geometry.MvPolynomialFractionFieldGenericConsumer

universe u v w

variable {k : Type u} [Field k]

abbrev TailIndex := {i : Fin 5 // i.val ≠ 0}

theorem tail_variables_are_a_basis :
    IsTranscendenceBasis k
      (fun i : ULift.{u} TailIndex =>
        algebraMap (MvPolynomial TailIndex k)
          (FractionRing (MvPolynomial TailIndex k))
          (MvPolynomial.X i.down)) :=
  _root_.Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis.standardVariables_isTranscendenceBasis_of_fintype
    (k := k) (σ := TailIndex)

theorem tail_fraction_field_has_finite_trdeg :
    Algebra.trdeg k (FractionRing (MvPolynomial TailIndex k)) = Fintype.card TailIndex :=
  _root_.Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis.trdeg_eq_of_fintype
    (k := k) (σ := TailIndex)

theorem tail_fraction_field_variables_algebraic_extension
    {κ : Type w} [Field κ] [Algebra k κ]
    [Algebra (FractionRing (MvPolynomial TailIndex k)) κ]
    [IsScalarTower k (FractionRing (MvPolynomial TailIndex k)) κ]
    (hvars : IsTranscendenceBasis k
      (fun i : TailIndex =>
        algebraMap (FractionRing (MvPolynomial TailIndex k)) κ
          (algebraMap (MvPolynomial TailIndex k)
            (FractionRing (MvPolynomial TailIndex k)) (MvPolynomial.X i)))) :
    Algebra.IsAlgebraic (FractionRing (MvPolynomial TailIndex k)) κ :=
  _root_.Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis.isAlgebraic_fractionRing_of_variable_images_isTranscendenceBasis
    hvars

#print axioms tail_variables_are_a_basis
#print axioms tail_fraction_field_has_finite_trdeg
#print axioms tail_fraction_field_variables_algebraic_extension

end Stafford38.Geometry.MvPolynomialFractionFieldGenericConsumer
