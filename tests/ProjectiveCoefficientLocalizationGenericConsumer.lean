import Stafford38.Geometry.ProjectiveCoefficientLocalization

set_option autoImplicit false

namespace Stafford38.Geometry.ProjectiveCoefficientLocalizationGenericConsumer

universe u v

variable {k : Type u} [Field k]

abbrev Selected := {i : Fin 5 // i.val ≠ 0}
abbrev A := MvPolynomial Selected k
abbrev E := FractionRing (A (k := k))
abbrev Rsrc := MvPolynomial (Option Selected) k

theorem selected_index_localization :
    letI : Algebra (Rsrc (k := k)) (Polynomial (E (k := k))) :=
      (_root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap
        (k := k) (E := E (k := k)) (σ := Selected)).toRingHom.toAlgebra
    IsLocalization
      (_root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateDenominators
        (k := k) (σ := Selected)) (Polynomial (E (k := k))) :=
  _root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap_isLocalization
    (k := k) (E := E (k := k)) (σ := Selected)

theorem selected_index_formally_etale :
    letI : Algebra (Rsrc (k := k)) (Polynomial (E (k := k))) :=
      (_root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap
        (k := k) (E := E (k := k)) (σ := Selected)).toRingHom.toAlgebra
    Algebra.FormallyEtale (Rsrc (k := k)) (Polynomial (E (k := k))) :=
  _root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap_formallyEtale
    (k := k) (E := E (k := k)) (σ := Selected)

theorem distinguished_parameter_image :
    _root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap
      (k := k) (E := E (k := k)) (σ := Selected)
      (MvPolynomial.X none) = (Polynomial.X : Polynomial (E (k := k))) := by
  simp

theorem selected_coefficient_image (i : Selected) :
    _root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap
      (k := k) (E := E (k := k)) (σ := Selected)
      (MvPolynomial.X (some i)) =
        Polynomial.C (algebraMap (A (k := k)) (E (k := k)) (MvPolynomial.X i)) := by
  simp

theorem none_is_not_a_denominator :
    MvPolynomial.X (none : Option Selected) ∉
      _root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateDenominators
        (k := k) (σ := Selected) := by
  change MvPolynomial.optionEquivLeft k Selected (MvPolynomial.X none) ∉
    Submonoid.map Polynomial.C (nonZeroDivisors (A (k := k)))
  rw [MvPolynomial.optionEquivLeft_X_none]
  intro hx
  rcases hx with ⟨p, hp, hpx⟩
  have hcoeff := congrArg (fun q : Polynomial (A (k := k)) => q.coeff 1) hpx
  simp at hcoeff

/-- The old `Fin` statement remains a wrapper at the original source ring. -/
theorem legacy_fin_formally_etale (d : ℕ) :
    letI : Algebra
      (_root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.Source k d)
      (Polynomial (FractionRing
        (_root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.Coeff k d))) :=
      (_root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.coordinateMap
        (k := k) d).toRingHom.toAlgebra
    Algebra.FormallyEtale
      (_root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.Source k d)
      (Polynomial (FractionRing
        (_root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.Coeff k d))) :=
  _root_.Stafford38.Geometry.ProjectiveCoefficientLocalization.fractionCoordinateMap_formallyEtale
    (k := k) d

#print axioms selected_index_localization
#print axioms selected_index_formally_etale
#print axioms distinguished_parameter_image
#print axioms selected_coefficient_image
#print axioms none_is_not_a_denominator
#print axioms legacy_fin_formally_etale

end Stafford38.Geometry.ProjectiveCoefficientLocalizationGenericConsumer
