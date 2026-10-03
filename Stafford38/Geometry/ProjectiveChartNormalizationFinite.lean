module
public import Stafford38.Geometry.NormalizationHeightOne
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.FiniteType

@[expose] public section

/-!
# Finiteness of the normalization in a chosen fraction-field model

The chart-to-valuation construction uses a concrete function field, while
Noether normalization is most convenient in `FractionRing R`. This adapter
transports the finite normalization to that concrete field without changing
the base domain.
-/

set_option autoImplicit false

noncomputable section

open scoped nonZeroDivisors

namespace Stafford38.Geometry.ProjectiveChartNormalizationFinite

universe u

/-- The integral closure of a finite-type domain in any chosen realization of
its fraction field is finite over the original domain. -/
theorem finite_integralClosure_in_fractionField
    (k R K : Type u) [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) := by
  let C₀ : Subalgebra R (FractionRing R) := integralClosure R (FractionRing R)
  have hC₀ : Module.Finite R C₀ :=
    Stafford38.Geometry.NormalizationHeightOne.finite_normalization_of_fg_domain
      k R C₀
  let e : FractionRing R ≃ₐ[R] K :=
    IsLocalization.algEquiv R⁰ (FractionRing R) K
  exact Module.Finite.equiv e.mapIntegralClosure.toLinearEquiv

/-- The integral closure is finite type over the ground field, before any
localization of the ground field or of the domain. -/
theorem integralClosure_finiteType_over_base
    (k R K : Type u) [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    let C : Subalgebra R K := integralClosure R K
    letI : Algebra k C := Algebra.compHom C (algebraMap k R)
    letI : IsScalarTower k R C := IsScalarTower.of_algebraMap_eq fun _ => rfl
    Algebra.FiniteType k C := by
  let C : Subalgebra R K := integralClosure R K
  letI : Algebra k C := Algebra.compHom C (algebraMap k R)
  haveI : IsScalarTower k R C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite R C :=
    finite_integralClosure_in_fractionField k R K
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k R)
    (inferInstance : Algebra.FiniteType R C)


end Stafford38.Geometry.ProjectiveChartNormalizationFinite
