module
public import Stafford38.Geometry.FiniteTypeCurveHeight
public import Mathlib.RingTheory.Polynomial.Quotient

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.FiniteTypeCurveHeightConsumer

/-- Independent literal check on the maximal ideal `(X)` in `E[X]`. -/
theorem polynomial_maximal_height_le_one (E : Type*) [Field E] :
    (Ideal.span ({Polynomial.X - Polynomial.C (0 : E)} : Set (Polynomial E))).height ≤ 1 := by
  let I : Ideal (Polynomial E) :=
    Ideal.span ({Polynomial.X - Polynomial.C (0 : E)} : Set (Polynomial E))
  have hmax : I.IsMaximal := by
    change Ideal.IsMaximal
      (Ideal.span ({Polynomial.X - Polynomial.C (0 : E)} : Set (Polynomial E)))
    exact PrincipalIdealRing.isMaximal_of_irreducible (Polynomial.irreducible_X_sub_C 0)
  letI : I.IsMaximal := hmax
  let p : PrimeSpectrum (Polynomial E) := ⟨I, inferInstance⟩
  have htrdeg : Algebra.trdeg E (FractionRing (Polynomial E)) = 1 := by
    rw [Stafford38.Geometry.FiniteTypeCurveNormalization.trdeg_fractionRing_eq_trdeg]
    exact Polynomial.trdeg_of_isDomain
  change p.asIdeal.height ≤ 1
  exact Stafford38.Geometry.FiniteTypeCurveHeight.maximal_ideal_height_le_one_of_fraction_field_trdeg_one htrdeg p

/-- The localization transport and nonzero-contraction sharpening are also
checked on the identity localization at units of `E[X]`. -/
theorem polynomial_localized_maximal_center_height_eq_one (E : Type*) [Field E] :
    (Ideal.under (Polynomial E)
      (Ideal.span ({Polynomial.X - Polynomial.C (0 : E)} : Set (Polynomial E)))).height = 1 := by
  let I : Ideal (Polynomial E) :=
    Ideal.span ({Polynomial.X - Polynomial.C (0 : E)} : Set (Polynomial E))
  have hmax : I.IsMaximal := by
    change Ideal.IsMaximal
      (Ideal.span ({Polynomial.X - Polynomial.C (0 : E)} : Set (Polynomial E)))
    exact PrincipalIdealRing.isMaximal_of_irreducible (Polynomial.irreducible_X_sub_C 0)
  letI : I.IsMaximal := hmax
  let q : PrimeSpectrum (Polynomial E) := ⟨I, inferInstance⟩
  have htrdeg : Algebra.trdeg E (FractionRing (Polynomial E)) = 1 := by
    rw [Stafford38.Geometry.FiniteTypeCurveNormalization.trdeg_fractionRing_eq_trdeg]
    exact Polynomial.trdeg_of_isDomain
  have h0 : Ideal.under (Polynomial E) q.asIdeal ≠ ⊥ := by
    intro h
    have hx : (Polynomial.X : Polynomial E) ∈ Ideal.under (Polynomial E) q.asIdeal := by
      rw [Ideal.mem_under]
      apply Ideal.subset_span
      simp
    rw [h] at hx
    exact Polynomial.X_ne_zero hx
  exact Stafford38.Geometry.FiniteTypeCurveHeight.localized_maximal_center_height_eq_one_of_fraction_field_trdeg_one
    (E := E) (R := Polynomial E) (A := Polynomial E)
    (L := FractionRing (Polynomial E)) (S := IsUnit.submonoid (Polynomial E))
    htrdeg q h0

#print axioms polynomial_maximal_height_le_one
#print axioms polynomial_localized_maximal_center_height_eq_one

end Stafford38.Geometry.FiniteTypeCurveHeightConsumer
