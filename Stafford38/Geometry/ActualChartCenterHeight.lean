import Stafford38.Geometry.FiniteTypeCurveHeight
import Mathlib.RingTheory.Ideal.Height

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.ActualChartCenterHeight

universe u v w x y

/-- After a localization center has been identified with the contraction of a
canonical normalization center, the dimension-theoretic conclusion follows
from the finite-type curve height theorem. -/
theorem normalized_center_height_one_of_localized_curve
    {E : Type u} {R : Type v} {A : Type w} {F : Type x} {C : Type y}
    [Field E] [CommRing R] [IsDomain R] {S : Submonoid R}
    [CommRing A] [IsDomain A] [Algebra R A] [IsLocalization S A]
    [Algebra E A] [Algebra.FiniteType E A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra E F] [IsScalarTower E A F]
    [CommRing C]
    (e : R ≃+* C)
    (p : PrimeSpectrum A) [hp : p.asIdeal.IsMaximal]
    (J : Ideal C)
    (hcenter : J.comap e.toRingHom = Ideal.under R p.asIdeal)
    (h0 : J.comap e.toRingHom ≠ ⊥)
    (htrdeg : Algebra.trdeg E F = 1) : J.height = 1 := by
  letI : p.asIdeal.IsMaximal := hp
  have h0' : Ideal.under R p.asIdeal ≠ ⊥ := by
    rw [← hcenter]
    exact h0
  have hheight :=
    Stafford38.Geometry.FiniteTypeCurveHeight.localized_maximal_center_height_eq_one_of_fraction_field_trdeg_one
      (E := E) (R := R) (A := A) (L := F) (S := S) htrdeg p h0'
  calc
    J.height = (J.comap e.toRingHom).height :=
      (RingEquiv.height_comap e J).symm
    _ = (Ideal.under R p.asIdeal).height := by rw [hcenter]
    _ = 1 := hheight

end Stafford38.Geometry.ActualChartCenterHeight
