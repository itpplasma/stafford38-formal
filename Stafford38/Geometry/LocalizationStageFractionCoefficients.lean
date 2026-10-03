module
public import Stafford38.Geometry.LocalizationInStagesAtPrime
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.LocalizationStageFractionCoefficients

universe u v w x y

open Stafford38.Geometry.LocalizationInStagesAtPrime

/-- If a map from a domain has injective image in the residue field, it extends
from the domain's fraction ring to the localization at that residue kernel. -/
noncomputable def fractionRingToAtPrime
    {A : Type u} [CommRing A] [IsDomain A]
    {B : Type v} [CommRing B] {κ : Type w} [Field κ]
    (f : A →+* B) (rho : B →+* κ)
    (P : Ideal B) [P.IsPrime] (hP : P = RingHom.ker rho)
    (hinj : Function.Injective (rho.comp f)) :
    FractionRing A →+* Localization.AtPrime P := by
  let g : A →+* Localization.AtPrime P :=
    (algebraMap B (Localization.AtPrime P)).comp f
  have hg : ∀ y : nonZeroDivisors A, IsUnit (g y) := by
    intro y
    have hnot : f y ∉ P := by
      intro hmem
      have hz : rho (f y) = 0 := by
        rw [hP, RingHom.mem_ker] at hmem
        exact hmem
      have hz' : (rho.comp f) y = 0 := by
        simpa only [RingHom.comp_apply] using hz
      apply (nonZeroDivisors.ne_zero y.2)
      exact hinj (by simpa using hz')
    exact IsLocalization.map_units (Localization.AtPrime P)
      (⟨f y, hnot⟩ : P.primeCompl)
  exact IsLocalization.lift hg

@[simp]
theorem fractionRingToAtPrime_algebraMap
    {A : Type u} [CommRing A] [IsDomain A]
    {B : Type v} [CommRing B] {κ : Type w} [Field κ]
    (f : A →+* B) (rho : B →+* κ)
    (P : Ideal B) [P.IsPrime] (hP : P = RingHom.ker rho)
    (hinj : Function.Injective (rho.comp f)) (a : A) :
    fractionRingToAtPrime f rho P hP hinj
      (algebraMap A (FractionRing A) a) =
      algebraMap B (Localization.AtPrime P) (f a) := by
  simp [fractionRingToAtPrime]

/-- The coefficient field maps into the two local rings are compatible with
the canonical localization-in-stages equivalence. The only selected-data
condition is injectivity of the chosen domain in the residue field; the right
coefficient map is constructed by the localization universal property. -/
theorem stageFractionCoefficientMap_commutes
    {A : Type u} [CommRing A] [IsDomain A]
    {B : Type v} [CommRing B] {κ : Type w} [Field κ]
    (M : Submonoid B) (p : Ideal (Localization M)) [p.IsPrime]
    (rhoL : Localization M →+* κ) (rhoB : B →+* κ)
    (hp : p = RingHom.ker rhoL)
    (hLoc : rhoL.comp (algebraMap B (Localization M)) = rhoB)
    (f : A →+* B)
    (hinj : Function.Injective (rhoB.comp f))
    (coeffL : FractionRing A →+* Localization M)
    (hcoeffL : coeffL.comp (algebraMap A (FractionRing A)) =
      (algebraMap B (Localization M)).comp f) :
    ∃ e : Localization.AtPrime p ≃ₐ[B]
        Localization.AtPrime (p.comap (algebraMap B (Localization M))),
      ∃ hcenter : p.comap (algebraMap B (Localization M)) = RingHom.ker rhoB,
      e.toRingEquiv.toRingHom.comp
          ((algebraMap (Localization M) (Localization.AtPrime p)).comp coeffL) =
        fractionRingToAtPrime f rhoB
          (p.comap (algebraMap B (Localization M)))
          hcenter hinj := by
  obtain ⟨e, hcenter, _hmap⟩ :=
    kernel_center_localization_equiv M p rhoL rhoB hp hLoc
  refine ⟨e, hcenter, ?_⟩
  apply IsLocalization.ringHom_ext (M := nonZeroDivisors A)
  apply RingHom.ext
  intro a
  change e (algebraMap (Localization M) (Localization.AtPrime p)
      (coeffL (algebraMap A (FractionRing A) a))) =
    fractionRingToAtPrime f rhoB
      (p.comap (algebraMap B (Localization M))) hcenter hinj
      (algebraMap A (FractionRing A) a)
  have hcoeffA : coeffL (algebraMap A (FractionRing A) a) =
      algebraMap B (Localization M) (f a) := by
    exact RingHom.congr_fun hcoeffL a
  rw [hcoeffA]
  calc
    e (algebraMap (Localization M) (Localization.AtPrime p)
        (algebraMap B (Localization M) (f a))) =
      algebraMap B (Localization.AtPrime (p.comap (algebraMap B (Localization M))))
        (f a) := _hmap (f a)
    _ = fractionRingToAtPrime f rhoB
          (p.comap (algebraMap B (Localization M))) hcenter hinj
          (algebraMap A (FractionRing A) a) := by
            symm
            exact fractionRingToAtPrime_algebraMap f rhoB
              (p.comap (algebraMap B (Localization M))) hcenter hinj a

/-- If a ring equivalence preserves the coefficient map and the distinguished
parameter, it is automatically an equivalence over the induced polynomial
parameter algebra. The two `hEval` premises record that the chosen polynomial
algebra structures are exactly evaluation at those data. -/
noncomputable def polynomialAlgEquivOfCompatibleEvaluation
    {E : Type u} [CommSemiring E]
    {T₁ : Type v} [CommSemiring T₁] {T₂ : Type w} [CommSemiring T₂]
    [Algebra E T₁] [Algebra E T₂]
    [Algebra (Polynomial E) T₁] [Algebra (Polynomial E) T₂]
    (f : T₁ ≃+* T₂)
    (hcoeff : ∀ c : E, f (algebraMap E T₁ c) = algebraMap E T₂ c)
    (a₁ : T₁) (a₂ : T₂) (ha : f a₁ = a₂)
    (hEval₁ : ∀ p : Polynomial E,
      algebraMap (Polynomial E) T₁ p = Polynomial.aeval a₁ p)
    (hEval₂ : ∀ p : Polynomial E,
      algebraMap (Polynomial E) T₂ p = Polynomial.aeval a₂ p) :
    T₁ ≃ₐ[Polynomial E] T₂ := by
  let fE : T₁ ≃ₐ[E] T₂ := AlgEquiv.ofRingEquiv (f := f) hcoeff
  have hpoly : fE.toAlgHom.comp (Polynomial.aeval a₁) = Polynomial.aeval a₂ := by
    apply Polynomial.algHom_ext
    simpa [fE] using ha
  apply AlgEquiv.ofRingEquiv (f := f)
  intro p
  rw [hEval₁ p, hEval₂ p]
  have hp := congrArg (fun g : Polynomial E →ₐ[E] T₂ => g p) hpoly
  simpa [fE] using hp

end Stafford38.Geometry.LocalizationStageFractionCoefficients
