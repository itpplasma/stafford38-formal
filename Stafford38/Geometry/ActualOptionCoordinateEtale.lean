import Stafford38.Geometry.DVRParameterSmoothness
import Stafford38.Geometry.OptionCoordinateEtaleComposition

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualOptionCoordinateEtale

open Polynomial
open Stafford38.Geometry.OptionCoordinateEtaleComposition

universe u v w x y z

/-- Formal etaleness of an actual option-indexed coordinate map follows from a
polynomial-parameter DVR model when the model's local ring is identified over
`Polynomial E` with the target local ring. The coordinate equations are imposed
on the transported local parameters themselves, so the conclusion concerns the
actual chart map, not just an abstract model map. -/
theorem formallyEtale_of_uniformizer_model
    {k : Type u} [CommRing k] {σ : Type w}
    {E : Type v} [Field E]
    {S : Type x} [CommRing S] [IsDomain S]
    [Algebra E S] [Algebra (Polynomial E) S]
    [IsScalarTower E (Polynomial E) S]
    [Algebra.FiniteType E S]
    (p : Ideal S) [p.IsPrime]
    (hX0 : algebraMap (Polynomial E) S (Polynomial.X : Polynomial E) ≠ 0)
    (hparam : (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).map
        (algebraMap (Polynomial E) (Localization.AtPrime p)) =
          IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hsep : Algebra.IsSeparable E p.ResidueField)
    [Algebra (MvPolynomial σ k) E] [Algebra k E]
    [IsScalarTower k (MvPolynomial σ k) E]
    [IsLocalization (nonZeroDivisors (MvPolynomial σ k)) E]
    {B : Type y} [CommRing B] [Algebra k B]
    {T : Type z} [CommRing T]
    [Algebra k T] [Algebra (Polynomial E) T]
    [IsScalarTower k (Polynomial E) T]
    (ρ : B →ₐ[k] T)
    (q : Option σ → B)
    (e : Localization.AtPrime p ≃ₐ[Polynomial E] T)
    (hnone : e (algebraMap (Polynomial E) (Localization.AtPrime p)
        (Polynomial.X : Polynomial E)) = ρ (q none))
    (hsome : ∀ i : σ,
      e (algebraMap (Polynomial E) (Localization.AtPrime p)
        (Polynomial.C (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i)))) =
          ρ (q (some i))) :
    let f : MvPolynomial (Option σ) k →ₐ[k] T :=
      MvPolynomial.aeval (fun i => ρ (q i))
    letI : Algebra (MvPolynomial (Option σ) k) T := f.toRingHom.toAlgebra
    Algebra.FormallyEtale (MvPolynomial (Option σ) k) T := by
  have hmodel : Algebra.FormallyEtale (Polynomial E) (Localization.AtPrime p) :=
    Stafford38.Geometry.DVRParameterSmoothness.formallyEtale_localization_of_polynomial_uniformizer
      p hX0 hparam hsep
  letI : Algebra.FormallyEtale (Polynomial E) (Localization.AtPrime p) := hmodel
  have htarget : Algebra.FormallyEtale (Polynomial E) T :=
    Algebra.FormallyEtale.of_equiv e
  letI : Algebra.FormallyEtale (Polynomial E) T := htarget
  let f : MvPolynomial (Option σ) k →ₐ[k] T :=
    MvPolynomial.aeval (fun i => ρ (q i))
  have hnone' : f (MvPolynomial.X none) =
      algebraMap (Polynomial E) T (Polynomial.X : Polynomial E) := by
    rw [show f (MvPolynomial.X none) = ρ (q none) by simp [f]]
    rw [← hnone]
    exact e.commutes (Polynomial.X : Polynomial E)
  have hsome' : ∀ i : σ,
      f (MvPolynomial.X (some i)) = algebraMap (Polynomial E) T
        (Polynomial.C (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i))) := by
    intro i
    rw [show f (MvPolynomial.X (some i)) = ρ (q (some i)) by simp [f]]
    rw [← hsome i]
    exact e.commutes (Polynomial.C
      (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i)))
  exact formallyEtale_of_optionCoordinate_generator_images f hnone' hsome' htarget

end Stafford38.Geometry.ActualOptionCoordinateEtale
