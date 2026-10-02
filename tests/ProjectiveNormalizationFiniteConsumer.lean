import Stafford38.Geometry.ProjectiveChartNormalizationFinite

set_option autoImplicit false

universe u

theorem projective_normalization_finite_consumer
    (k R K : Type u) [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) :=
  Stafford38.Geometry.ProjectiveChartNormalizationFinite.finite_integralClosure_in_fractionField
    k R K

#print axioms projective_normalization_finite_consumer
