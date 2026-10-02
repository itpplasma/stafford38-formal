import Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
import Stafford38.Geometry.ActualOptionGroundPointCompletion
import Mathlib.Algebra.Algebra.Tower

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u v w

theorem actualCertificate_formallyEtale_for_groundPointAdapter
    {k : Type u} [Field k] {σ : Type v} {B : Type w}
    [CommRing B] [Algebra k B]
    (P : Ideal B) (s : B) (rows : σ → B)
    (fOption : MvPolynomial (Option σ) k →ₐ[k] B)
    (cert : Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale.ActualOptionEtaleCertificate
      k σ B P s rows fOption) :
    letI : P.IsPrime := cert.prime_isPrime
    let Rσ := MvPolynomial (Option σ) k
    letI : Algebra Rσ B := fOption.toRingHom.toAlgebra
    letI : IsScalarTower k Rσ B := IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (fOption.commutes c).symm)
    letI : Algebra Rσ (Localization.AtPrime P) := inferInstance
    Algebra.FormallyEtale Rσ (Localization.AtPrime P) := by
  letI : P.IsPrime := cert.prime_isPrime
  let Rσ := MvPolynomial (Option σ) k
  letI : Algebra Rσ B := fOption.toRingHom.toAlgebra
  letI : IsScalarTower k Rσ B := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact (fOption.commutes c).symm)
  letI : Algebra Rσ (Localization.AtPrime P) := inferInstance
  let actualMap : MvPolynomial (Option σ) k →ₐ[k] Localization.AtPrime P :=
    (IsScalarTower.toAlgHom k B (Localization.AtPrime P)).comp fOption
  have hAlgebra : (inferInstance : Algebra Rσ (Localization.AtPrime P)) =
      actualMap.toRingHom.toAlgebra := by
    apply Algebra.algebra_ext
    intro c
    change algebraMap B (Localization.AtPrime P) (fOption c) = actualMap.toRingHom c
    rfl
  have hprop := congrArg
    (fun A : Algebra Rσ (Localization.AtPrime P) =>
      @Algebra.FormallyEtale Rσ (Localization.AtPrime P) _ _ A) hAlgebra
  exact hprop.mpr cert.formallyEtale
