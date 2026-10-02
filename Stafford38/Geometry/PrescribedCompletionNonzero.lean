import Stafford38.Geometry.PrescribedAffineResidueCompletion
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Localization.Submodule

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Stafford38.Geometry.PrescribedCompletionNonzero

noncomputable section

open Stafford38.Geometry.PrescribedAffineResidueCompletion

variable {k σ B : Type*} [Field k] [Fintype σ] [CommRing B] [Algebra k B]
  [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B]

local notation "R" => MvPolynomial σ k

/-- Essential finite type over the polynomial coordinate ring makes the selected
prime localization Noetherian. -/
theorem localizationAtPrime_isNoetherianRing
    [Algebra.EssFiniteType R B] (M : Ideal B) [M.IsPrime] :
    IsNoetherianRing (Localization.AtPrime M) := by
  letI : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing R B
  exact IsLocalization.isNoetherianRing M.primeCompl _ (inferInstance : IsNoetherianRing B)

/-- Completion at the maximal ideal of this local Noetherian ring is separated,
so its canonical map is injective. -/
theorem localizationCompletion_of_injective
    [Algebra.EssFiniteType R B] (M : Ideal B) [M.IsPrime] :
    Function.Injective
      (AdicCompletion.of (IsLocalRing.maximalIdeal (Localization.AtPrime M))
        (Localization.AtPrime M)) := by
  letI : IsNoetherianRing (Localization.AtPrime M) :=
    localizationAtPrime_isNoetherianRing (k := k) (σ := σ) (B := B) M
  exact AdicCompletion.of_injective _ _

/-- A nonzero element of the finite-type domain remains nonzero after localization,
completion, and transport to the prescribed formal-series model. The point may
lie on its zero set; localization injectivity and separatedness give the claim. -/
theorem prescribedSeries_image_ne_zero
    (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.EssFiniteType R B]
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    [IsDomain B] (b : B) (hb : b ≠ 0) :
    (powerSeriesCompletionAtGroundPoint (σ := σ) M eM).symm
      (AdicCompletion.of
        (IsLocalRing.maximalIdeal (Localization.AtPrime M))
        (Localization.AtPrime M)
        (algebraMap B (Localization.AtPrime M) b)) ≠ 0 := by
  let E := powerSeriesCompletionAtGroundPoint (σ := σ) M eM
  letI : IsNoetherianRing (Localization.AtPrime M) :=
    localizationAtPrime_isNoetherianRing (k := k) (σ := σ) (B := B) M
  have hinj : Function.Injective (algebraMap B (Localization.AtPrime M)) :=
    IsLocalization.injective (Localization.AtPrime M)
      (Ideal.primeCompl_le_nonZeroDivisors M)
  intro hseries
  have hcompleted :
      AdicCompletion.of (IsLocalRing.maximalIdeal (Localization.AtPrime M))
          (Localization.AtPrime M) (algebraMap B (Localization.AtPrime M) b) = 0 := by
    have h := congrArg E hseries
    simpa [E] using h
  have hlocal : algebraMap B (Localization.AtPrime M) b = 0 :=
    (localizationCompletion_of_injective (k := k) (σ := σ) (B := B) M).eq_iff.mp
      hcompleted
  exact hb (hinj (by simpa using hlocal))

#print axioms localizationAtPrime_isNoetherianRing
#print axioms localizationCompletion_of_injective
#print axioms prescribedSeries_image_ne_zero

end
end Stafford38.Geometry.PrescribedCompletionNonzero
