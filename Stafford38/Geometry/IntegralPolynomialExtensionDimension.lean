import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# A height bound for an integral extension of a one-variable polynomial ring

An integral map from `E[X]` into a domain forces every maximal ideal of the
target to have height at most one.  Injectivity is not needed: if the kernel
is nonzero, the image has dimension zero, while the integral-spectrum argument
still gives the same bound.  This packages the local dimension step used after
a one-variable Noether normalization.
-/

namespace Stafford38.Geometry.IntegralPolynomialExtensionDimension

set_option autoImplicit false

noncomputable section

/-- If a domain `A` is integral over the image of a one-variable polynomial ring
over a field, then every maximal ideal of `A` has height at most one. -/
theorem height_le_one_of_integral_polynomial_map
    {E A : Type*} [Field E] [CommRing A] [IsDomain A] [Algebra E A]
    (f : Polynomial E →ₐ[E] A) (hint : f.toRingHom.IsIntegral)
    (p : PrimeSpectrum A) [p.asIdeal.IsMaximal] : p.asIdeal.height ≤ 1 := by
  letI : Algebra (Polynomial E) A := f.toRingHom.toAlgebra
  letI : Algebra.IsIntegral (Polynomial E) A := ⟨hint⟩
  let g : PrimeSpectrum A → PrimeSpectrum (Polynomial E) :=
    PrimeSpectrum.comap f.toRingHom
  have hg : StrictMono g := by
    intro x y hxy
    change x.asIdeal < y.asIdeal at hxy
    change (x.asIdeal.comap f.toRingHom) < (y.asIdeal.comap f.toRingHom)
    exact Ideal.IsIntegral.comap_lt_comap hxy
  have hgmax : (g p).asIdeal.IsMaximal := by
    change Ideal.IsMaximal ((p.asIdeal).comap f.toRingHom)
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f.toRingHom hint _
  letI : (g p).asIdeal.IsMaximal := hgmax
  have hpoly : (g p).asIdeal.height = 1 :=
    IsPrincipalIdealRing.height_eq_one_of_isMaximal _ (Polynomial.not_isField E)
  rw [p.height_eq_orderHeight]
  exact (Order.height_le_height_apply_of_strictMono g hg p).trans_eq
    (by rw [← (g p).height_eq_orderHeight, hpoly])

end

end Stafford38.Geometry.IntegralPolynomialExtensionDimension
