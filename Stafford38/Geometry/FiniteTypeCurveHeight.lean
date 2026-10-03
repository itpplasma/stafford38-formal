module
public import Stafford38.Geometry.FiniteTypeCurveNormalization
public import Stafford38.Geometry.IntegralPolynomialExtensionDimension
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.FiniteTypeCurveHeight

/-- In a finite-type domain over a field, transcendence degree one of an actual
fraction field bounds the height of every maximal ideal by one. -/
theorem maximal_ideal_height_le_one_of_fraction_field_trdeg_one
    {E A L : Type*} [Field E] [CommRing A] [IsDomain A] [Algebra E A]
    [Algebra.FiniteType E A] [Field L] [Algebra A L] [IsFractionRing A L]
    [Algebra E L] [IsScalarTower E A L]
    (htrdeg : Algebra.trdeg E L = 1)
    (p : PrimeSpectrum A) [p.asIdeal.IsMaximal] : p.asIdeal.height ≤ 1 := by
  obtain ⟨f, _hinj, hint⟩ :=
    Stafford38.Geometry.FiniteTypeCurveNormalization.exists_injective_integral_polynomial_of_isFractionRing_trdeg_one
      (E := E) (A := A) (L := L) htrdeg
  exact Stafford38.Geometry.IntegralPolynomialExtensionDimension.height_le_one_of_integral_polynomial_map
    f hint p

/-- A maximal center in a localization of a finite-type curve has height at
most one after contraction to the original domain. -/
theorem localized_maximal_center_height_le_one_of_fraction_field_trdeg_one
    {E R A L : Type*}
    [Field E] [CommRing R] [IsDomain R] {S : Submonoid R}
    [CommRing A] [IsDomain A]
    [Algebra R A] [IsLocalization S A]
    [Algebra E A] [Algebra.FiniteType E A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    [Algebra E L] [IsScalarTower E A L]
    (htrdeg : Algebra.trdeg E L = 1)
    (q : PrimeSpectrum A) [q.asIdeal.IsMaximal] :
    (Ideal.under R q.asIdeal).height ≤ 1 := by
  rw [IsLocalization.height_under (R := R) (S := S) (A := A) q.asIdeal]
  exact maximal_ideal_height_le_one_of_fraction_field_trdeg_one
    (E := E) (A := A) (L := L) htrdeg q

/-- If the contracted center is nonzero, the preceding bound is sharp. -/
theorem localized_maximal_center_height_eq_one_of_fraction_field_trdeg_one
    {E R A L : Type*}
    [Field E] [CommRing R] [IsDomain R] {S : Submonoid R}
    [CommRing A] [IsDomain A]
    [Algebra R A] [IsLocalization S A]
    [Algebra E A] [Algebra.FiniteType E A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    [Algebra E L] [IsScalarTower E A L]
    (htrdeg : Algebra.trdeg E L = 1)
    (q : PrimeSpectrum A) [q.asIdeal.IsMaximal]
    (h0 : Ideal.under R q.asIdeal ≠ ⊥) :
    (Ideal.under R q.asIdeal).height = 1 := by
  let I := Ideal.under R q.asIdeal
  have hle : I.height ≤ 1 :=
    localized_maximal_center_height_le_one_of_fraction_field_trdeg_one
      (E := E) (R := R) (A := A) (L := L) (S := S) htrdeg q
  have hne : I.height ≠ 0 := by
    intro h
    apply h0
    exact Ideal.height_eq_zero_iff_eq_bot.mp h
  have hge : 1 ≤ I.height := (Order.one_le_iff_ne_zero).2 hne
  exact le_antisymm hle hge

end Stafford38.Geometry.FiniteTypeCurveHeight
