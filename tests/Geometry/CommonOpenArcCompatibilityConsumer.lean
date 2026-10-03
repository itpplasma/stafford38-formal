module
public import Stafford38.Geometry.ActualCommonOpenArcCompatibility


@[expose] public section

set_option autoImplicit false

open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift

universe u v w

variable {k : Type u} [Field k] {d : ℕ}
variable {A : Type v} [CommRing A] [Algebra k A]
  [Algebra (MvPolynomial (Option (Fin d)) k) A]
  [IsScalarTower k (MvPolynomial (Option (Fin d)) k) A]
  [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) A]
variable {Q : Type w} [CommRing Q] [Algebra Q A]

/-- Literal importer: the numerator `r` is distinct from the chart
denominator `g`; the same avoidance input returns its nonzero common-open
image. -/
theorem actual_numerator_survives_common_open
    (M : Ideal A) [M.IsMaximal]
    (f : Q) (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    (eM : (A ⧸ M) ≃ₐ[k] k) (α : Fin d → k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (Localization.AtPrime M)]
    (r bad q₀ q₁ : A)
    (hbad : bad = algebraMap Q A f * r)
    (hq₀ : q₀ = algebraMap Q A g)
    (havoid : tiltedArc (k := k) α
      (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
          (algebraMap A (Localization.AtPrime M) bad) *
       localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
          (algebraMap A (Localization.AtPrime M) q₀) *
       localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
          (algebraMap A (Localization.AtPrime M) q₁)) ≠ 0) :
    let ρA := originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := A) M eM α
    ∃ (hf : IsUnit (ρA (algebraMap Q A f)))
      (hg : IsUnit (ρA (algebraMap Q A g))),
      let hunitM : ∀ b, b ∉ M → IsUnit (ρA b) := fun b hb => by
        let T := Localization.AtPrime M
        have hu : IsUnit (algebraMap A T b) :=
          IsLocalization.map_units T (M := M.primeCompl) ⟨b, hb⟩
        change IsUnit
          ((pointLocalFinSuccArcLaurentSeries
            (k := k) (d := d) (A := A) M eM α).toRingHom
              (algebraMap A T b))
        exact IsUnit.map _ hu
      let ρU := genericArcToGenericOpenExtraAwayB M f e ρA hf hunitM g hg
      ρU (genericOpenExtraAwayBMap M f e g r) ≠ 0 := by
  rcases Stafford38.Geometry.ActualCommonOpenArcCompatibility.commonOpen_factors_ne_zero_of_tiltedProduct
      M f e g eM α r bad q₀ q₁ hbad hq₀ havoid with
    ⟨hf, hg, _hcomp, _hground, _hbad, hr, _hq₀, _hq₁⟩
  exact ⟨hf, hg, hr⟩

#print axioms Stafford38.Geometry.ActualCommonOpenArcCompatibility.genericArcToExtraAway_comp_commonOpenMap
#print axioms Stafford38.Geometry.ActualCommonOpenArcCompatibility.pointArc_factors_ne_zero_of_tiltedProduct
#print axioms Stafford38.Geometry.ActualCommonOpenArcCompatibility.commonOpen_factors_ne_zero_of_tiltedProduct
#print axioms actual_numerator_survives_common_open
