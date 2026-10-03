module
public import Stafford38.Geometry.ActualCommonOpenCompletionDerivation


@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Stafford38.Geometry.ActualCommonOpenArcCompatibility

open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift

universe u v w

variable {k : Type u} [Field k] {d : ℕ}
local notation "R" => MvPolynomial (Option (Fin d)) k
variable {A : Type v} [CommRing A] [Algebra k A]
  [Algebra (MvPolynomial (Option (Fin d)) k) A]
  [IsScalarTower k (MvPolynomial (Option (Fin d)) k) A]
  [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) A]
variable {Q : Type w} [CommRing Q] [Algebra Q A]

/-- The arc extended to the actual common open restricts to the original
point-local arc on the canonical map from the finite-type chart algebra.
This is a derived composition identity: it uses the existing localization
comparison and does not posit a second common-open map. -/
theorem genericArcToExtraAway_comp_commonOpenMap
    {L : Type*} [Field L]
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    (ρ : A →+* L)
    (hf : IsUnit (ρ (algebraMap Q A f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b))
    (hg : IsUnit (ρ (algebraMap Q A g))) :
    (genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg).comp
      (genericOpenExtraAwayBMap M f e g) = ρ := by
  let T := Localization.AtPrime M
  let U := genericOpenExtraAwayB M f e g
  let θ := pointLocalToCommonOpen (A := A) M f e g
  let ρU := genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg
  have hlocal := pointLocalToCommonOpen_comp_algebraMap (A := A) M f e g
  have harc := genericArcToExtraAway_comp_pointLocalToCommonOpen
    (A := A) M f e g ρ hf hunitM hg
  ext a
  have hmap : genericOpenExtraAwayBMap M f e g a =
      θ (algebraMap A T a) := by
    have h := congrArg (fun φ : A →+* U => φ a) hlocal
    simpa only [RingHom.comp_apply, θ, T, U] using h.symm
  calc
    ρU (genericOpenExtraAwayBMap M f e g a) =
        ρU (θ (algebraMap A T a)) := congrArg ρU hmap
    _ = localPointToField M ρ hunitM (algebraMap A T a) := by
      have h := congrArg (fun φ : T →+* L => φ (algebraMap A T a)) harc
      simpa only [RingHom.comp_apply, ρU, θ] using h
    _ = ρ a := by
      exact localPointToField_apply M ρ hunitM a

/-- Nonvanishing at the original point-local arc is preserved by the same
common-open map, including for a homogenized numerator. -/
theorem genericArcToExtraAway_ne_zero_of_pointArc_ne_zero
    {L : Type*} [Field L]
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    (ρ : A →+* L)
    (hf : IsUnit (ρ (algebraMap Q A f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b))
    (hg : IsUnit (ρ (algebraMap Q A g)))
    (a : A) (ha : ρ a ≠ 0) :
    genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg
      (genericOpenExtraAwayBMap M f e g a) ≠ 0 := by
  have hcomp := genericArcToExtraAway_comp_commonOpenMap
    (A := A) M f e g ρ hf hunitM hg
  have h := congrArg (fun φ : A →+* L => φ a) hcomp
  have h' : genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg
      (genericOpenExtraAwayBMap M f e g a) = ρ a := by
    simpa only [RingHom.comp_apply] using h
  rw [h']
  exact ha

section PointArcAvoidance

variable {B : Type v} [CommRing B] [Algebra k B]
  [Algebra (MvPolynomial (Option (Fin d)) k) B]
  [IsScalarTower k (MvPolynomial (Option (Fin d)) k) B]
  [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) B]

private theorem originalPointArc_eq_laurent_tilt
    (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (Localization.AtPrime M)]
    (α : Fin d → k) (a : B) :
    originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := B) M eM α a =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (tiltedArc (k := k) α
          (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
            (algebraMap B (Localization.AtPrime M) a))) := by
  rfl

/-- A single selected tilt that avoids a product certifies nonvanishing of
each of its three actual point-local factors after mapping to the Laurent
series field. -/
theorem pointArc_factors_ne_zero_of_tiltedProduct
    (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (Localization.AtPrime M)]
    (α : Fin d → k) (a b c : B)
    (havoid : tiltedArc (k := k) α
      (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
          (algebraMap B (Localization.AtPrime M) a) *
       localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
          (algebraMap B (Localization.AtPrime M) b) *
       localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
          (algebraMap B (Localization.AtPrime M) c)) ≠ 0) :
    (originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := B) M eM α a ≠ 0) ∧
    (originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := B) M eM α b ≠ 0) ∧
    (originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := B) M eM α c ≠ 0) := by
  have hmul :
      tiltedArc (k := k) α
          (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
            (algebraMap B (Localization.AtPrime M) a)) *
      tiltedArc (k := k) α
          (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
            (algebraMap B (Localization.AtPrime M) b)) *
      tiltedArc (k := k) α
          (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
            (algebraMap B (Localization.AtPrime M) c)) ≠ 0 := by
    simpa only [tiltedArc, map_mul] using havoid
  have ha : tiltedArc (k := k) α
      (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
        (algebraMap B (Localization.AtPrime M) a)) ≠ 0 := by
    intro hz
    apply hmul
    simp [hz]
  have hb : tiltedArc (k := k) α
      (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
        (algebraMap B (Localization.AtPrime M) b)) ≠ 0 := by
    intro hz
    apply hmul
    simp [hz]
  have hc : tiltedArc (k := k) α
      (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
        (algebraMap B (Localization.AtPrime M) c)) ≠ 0 := by
    intro hz
    apply hmul
    simp [hz]
  have hla : algebraMap (PowerSeries k) (LaurentSeries k)
      (tiltedArc (k := k) α
        (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
          (algebraMap B (Localization.AtPrime M) a))) ≠ 0 :=
    (by simpa only [map_zero] using
      (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).ne ha)
  have hlb : algebraMap (PowerSeries k) (LaurentSeries k)
      (tiltedArc (k := k) α
        (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
          (algebraMap B (Localization.AtPrime M) b))) ≠ 0 :=
    (by simpa only [map_zero] using
      (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).ne hb)
  have hlc : algebraMap (PowerSeries k) (LaurentSeries k)
      (tiltedArc (k := k) α
        (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
          (algebraMap B (Localization.AtPrime M) c))) ≠ 0 :=
    (by simpa only [map_zero] using
      (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).ne hc)
  constructor
  · rw [originalPointArc_eq_laurent_tilt]
    exact hla
  constructor
  · rw [originalPointArc_eq_laurent_tilt]
    exact hlb
  · rw [originalPointArc_eq_laurent_tilt]
    exact hlc

end PointArcAvoidance

section CommonOpenAvoidance

/-- The point-local tilt-avoidance witness supplies the actual away-unit
inputs while keeping the homogenized numerator `r` separate from the
common-open chart denominator `g`. The bad product is `map(f) * r`; the
zeroth column is `map(g)`. The denominator need not avoid the closed center:
its image is a unit because the same arc extends from the chosen point-local
ring. -/
theorem commonOpen_factors_ne_zero_of_tiltedProduct
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
      (ρU.comp (genericOpenExtraAwayBMap M f e g) = ρA) ∧
      ((ρU.comp (genericOpenExtraAwayBMap M f e g)).comp
          (algebraMap k A) = algebraMap k (LaurentSeries k)) ∧
      (ρU (genericOpenExtraAwayBMap M f e g bad) ≠ 0) ∧
      (ρU (genericOpenExtraAwayBMap M f e g r) ≠ 0) ∧
      (ρU (genericOpenExtraAwayBMap M f e g q₀) ≠ 0) ∧
      (ρU (genericOpenExtraAwayBMap M f e g q₁) ≠ 0) := by
  let ρA := originalToPointLocalFinSuccArcLaurentSeries
    (k := k) (d := d) (A := A) M eM α
  have hpoints := pointArc_factors_ne_zero_of_tiltedProduct
    (k := k) (d := d) (B := A) M eM α bad q₀ q₁ havoid
  rcases hpoints with ⟨hbadPoint, hq₀Point, hq₁Point⟩
  have hbadFactor : ρA bad =
      ρA (algebraMap Q A f) * ρA r := by
    calc
      ρA bad = ρA (algebraMap Q A f * r) := congrArg ρA hbad
      _ = ρA (algebraMap Q A f) * ρA r := map_mul ρA _ _
  have hq₀Chart : ρA q₀ = ρA (algebraMap Q A g) := congrArg ρA hq₀
  have hf0 : ρA (algebraMap Q A f) ≠ 0 := by
    intro hz
    apply hbadPoint
    rw [hbadFactor, hz]
    simp
  have hr0 : ρA r ≠ 0 := by
    intro hz
    apply hbadPoint
    rw [hbadFactor, hz]
    simp
  have hg0 : ρA (algebraMap Q A g) ≠ 0 := by
    intro hz
    apply hq₀Point
    rw [hq₀Chart, hz]
  have hf : IsUnit (ρA (algebraMap Q A f)) := isUnit_iff_ne_zero.mpr hf0
  have hg : IsUnit (ρA (algebraMap Q A g)) := isUnit_iff_ne_zero.mpr hg0
  have hunitM : ∀ b, b ∉ M → IsUnit (ρA b) := by
    intro b hb
    let T := Localization.AtPrime M
    have hu : IsUnit (algebraMap A T b) :=
      IsLocalization.map_units T (M := M.primeCompl) ⟨b, hb⟩
    change IsUnit
      ((pointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := A) M eM α).toRingHom (algebraMap A T b))
    exact IsUnit.map _ hu
  let ρU := genericArcToGenericOpenExtraAwayB M f e ρA hf hunitM g hg
  have hcomp := genericArcToExtraAway_comp_commonOpenMap
    (A := A) M f e g ρA hf hunitM hg
  have hbaseA : ρA.comp (algebraMap k A) =
      algebraMap k (LaurentSeries k) := by
    apply RingHom.ext
    intro c
    exact originalToPointLocalFinSuccArcLaurentSeries_base
      (k := k) (d := d) (A := A) M eM α c
  have hground : (ρU.comp (genericOpenExtraAwayBMap M f e g)).comp
      (algebraMap k A) = algebraMap k (LaurentSeries k) := by
    calc
      (ρU.comp (genericOpenExtraAwayBMap M f e g)).comp (algebraMap k A) =
          ρA.comp (algebraMap k A) := by
            exact congrArg (fun φ : A →+* LaurentSeries k =>
              φ.comp (algebraMap k A)) hcomp
      _ = algebraMap k (LaurentSeries k) := hbaseA
  have hmap (a : A) : ρU (genericOpenExtraAwayBMap M f e g a) = ρA a := by
    have h := congrArg (fun φ : A →+* LaurentSeries k => φ a) hcomp
    simpa only [RingHom.comp_apply, ρU] using h
  refine ⟨hf, hg, hcomp, hground, ?_, ?_, ?_, ?_⟩
  · rw [hmap]
    exact hbadPoint
  · rw [hmap]
    exact hr0
  · rw [hmap]
    exact hq₀Point
  · rw [hmap]
    exact hq₁Point

end CommonOpenAvoidance

end Stafford38.Geometry.ActualCommonOpenArcCompatibility

end
