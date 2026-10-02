import Stafford38.Geometry.LocalizationStageFractionCoefficients
import Mathlib.RingTheory.Ideal.Prime

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.LocalizationStageFractionCoefficients

/-- Concrete denominator-lift oracle: in the polynomial fraction field, the
constructed map into the zero-prime localization sends `X + 2` to the expected
localized polynomial. -/
theorem fractionRingToAtPrime_polynomial_X_add_two :
    fractionRingToAtPrime (RingHom.id (Polynomial ℚ))
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
      (⊥ : Ideal (Polynomial ℚ))
      (by
        ext f
        simp only [Ideal.mem_bot, RingHom.mem_ker]
        constructor
        · intro hf
          simpa using congrArg (algebraMap (Polynomial ℚ)
            (FractionRing (Polynomial ℚ))) hf
        · intro hf
          exact (IsFractionRing.injective (Polynomial ℚ)
            (FractionRing (Polynomial ℚ))) (by simpa using hf))
      (by
        intro a b hab
        change algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) a =
          algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) b at hab
        exact (IsFractionRing.injective (Polynomial ℚ)
          (FractionRing (Polynomial ℚ))) hab)
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))
        (Polynomial.X + Polynomial.C 2)) =
    algebraMap (Polynomial ℚ)
      (Localization.AtPrime (⊥ : Ideal (Polynomial ℚ)))
      (Polynomial.X + Polynomial.C 2) := by
  refine fractionRingToAtPrime_algebraMap (RingHom.id (Polynomial ℚ))
    (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
    (⊥ : Ideal (Polynomial ℚ)) ?_ ?_ (Polynomial.X + Polynomial.C 2)

/-- In the same polynomial fraction-field model, the stage equivalence carries
the actual fraction-field coefficient map to the localization lift from the
original polynomial ring. -/
theorem polynomial_fraction_field_stage_coefficients :
    ∃ e : Localization.AtPrime (⊥ : Ideal (FractionRing (Polynomial ℚ))) ≃ₐ[Polynomial ℚ]
        Localization.AtPrime
          ((⊥ : Ideal (FractionRing (Polynomial ℚ))).comap
            (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))),
      ∃ hcenter :
          (⊥ : Ideal (FractionRing (Polynomial ℚ))).comap
              (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) =
            RingHom.ker (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))),
        e.toRingEquiv.toRingHom.comp
            (RingHom.comp
              (algebraMap (FractionRing (Polynomial ℚ))
                (Localization.AtPrime (⊥ : Ideal (FractionRing (Polynomial ℚ)))))
              (RingHom.id (FractionRing (Polynomial ℚ)))) =
          fractionRingToAtPrime (RingHom.id (Polynomial ℚ))
            (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
            ((⊥ : Ideal (FractionRing (Polynomial ℚ))).comap
              (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))))
            hcenter
            (by
              intro a b hab
              exact (IsFractionRing.injective (Polynomial ℚ)
                (FractionRing (Polynomial ℚ))) hab) := by
  let B := Polynomial ℚ
  let M : Submonoid B := nonZeroDivisors B
  let L := Localization M
  letI : Field L := FractionRing.field B
  let rhoL : L →+* L := RingHom.id L
  let rhoB : B →+* L := algebraMap B L
  let p : Ideal L := ⊥
  have hp : p = RingHom.ker rhoL := by
    ext x
    simp [p, rhoL, RingHom.mem_ker]
  have hLoc : rhoL.comp (algebraMap B L) = rhoB := by
    apply RingHom.ext
    intro b
    rfl
  let f : B →+* B := RingHom.id B
  have hinj : Function.Injective (rhoB.comp f) := by
    change Function.Injective (algebraMap B (FractionRing B))
    exact IsFractionRing.injective B (FractionRing B)
  let coeffL : FractionRing B →+* L := RingHom.id L
  have hcoeffL : coeffL.comp (algebraMap B (FractionRing B)) =
      (algebraMap B L).comp f := by
    apply RingHom.ext
    intro b
    rfl
  exact stageFractionCoefficientMap_commutes M p rhoL rhoB hp hLoc f hinj
    coeffL hcoeffL

/-- The polynomial-algebra promotion also preserves a concrete evaluated
polynomial when both coefficient and parameter data agree. -/
noncomputable def polynomial_identity_parameter_equiv :
    Polynomial ℚ ≃ₐ[Polynomial ℚ] Polynomial ℚ :=
  polynomialAlgEquivOfCompatibleEvaluation
    (RingEquiv.refl (Polynomial ℚ))
    (by intro c; rfl)
    Polynomial.X Polynomial.X rfl
    (by intro p; simp)
    (by intro p; simp)

theorem polynomial_identity_parameter_oracle :
    polynomial_identity_parameter_equiv (Polynomial.X + Polynomial.C 2) =
      Polynomial.X + Polynomial.C 2 := by
  rfl

#print axioms fractionRingToAtPrime_polynomial_X_add_two
#print axioms polynomial_fraction_field_stage_coefficients
#print axioms polynomial_identity_parameter_oracle

end Stafford38.Geometry.LocalizationStageFractionCoefficients
