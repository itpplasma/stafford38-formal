module
public import Stafford38.Geometry.LocalizationInStagesAtPrime
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.LocalizationInStagesAtPrime

/-- A concrete fraction-field test: localizing the polynomial fraction field
at zero agrees over the polynomial ring with localizing the original ring at
the center of zero. The displayed test value is the nonconstant polynomial
`X + 2`, so the consumer checks the map on an actual generator expression. -/
theorem polynomial_fraction_field_stage_point :
    ∃ e : Localization.AtPrime (⊥ : Ideal (FractionRing (Polynomial ℚ))) ≃ₐ[Polynomial ℚ]
        Localization.AtPrime
          ((⊥ : Ideal (FractionRing (Polynomial ℚ))).comap
            (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))),
      e (algebraMap (FractionRing (Polynomial ℚ))
          (Localization.AtPrime (⊥ : Ideal (FractionRing (Polynomial ℚ))))
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))
          (Polynomial.X + Polynomial.C 2))) =
        algebraMap (Polynomial ℚ)
          (Localization.AtPrime
            ((⊥ : Ideal (FractionRing (Polynomial ℚ))).comap
              (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))))
          (Polynomial.X + Polynomial.C 2) := by
  let B := Polynomial ℚ
  let M : Submonoid B := nonZeroDivisors B
  let L := Localization M
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
  obtain ⟨e, hcenter, hmap⟩ :=
    kernel_center_localization_equiv M p rhoL rhoB hp hLoc
  exact ⟨e, hmap _⟩

#print axioms polynomial_fraction_field_stage_point

end Stafford38.Geometry.LocalizationInStagesAtPrime
