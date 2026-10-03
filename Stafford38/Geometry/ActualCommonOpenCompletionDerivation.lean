module
public import Stafford38.Geometry.EtaleGenericOpenExtraAwayB
public import Stafford38.Geometry.EtaleCotangentBasis
public import Stafford38.Geometry.PrescribedCompletionDerivationCommutation
public import Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
public import Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
public import Mathlib.RingTheory.LaurentSeries

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Actual common-open and completed-chart derivations

The map from the selected point-local ring into the common open is the one
induced by `localPointToGenericOpen`, followed by its actual chart-denominator
localization.  Its compatibility with the parameter algebra is proved from
the localization maps.  Consequently the coordinate derivations on the
common open restrict to the prescribed local derivations, and those commute
with the canonical multivariate completion and tilted arc on every element.
-/

namespace Stafford38.Geometry.ActualCommonOpenCompletionDerivation

open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.Geometry.PrescribedCompletionDerivationCommutation
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift

noncomputable section

universe u v w

variable {k : Type u} [Field k] {d : ℕ}
local notation "R" => MvPolynomial (Option (Fin d)) k
variable {A : Type v} [CommRing A] [Algebra k A]
  [Algebra (MvPolynomial (Option (Fin d)) k) A]
  [IsScalarTower k (MvPolynomial (Option (Fin d)) k) A]
  [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) A]
variable {Q : Type w} [CommRing Q] [Algebra Q A]

theorem scalarTower_k_R_pointLocal
    (M : Ideal A) [M.IsPrime]
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    IsScalarTower k R (Localization.AtPrime M) := by
  infer_instance

/-- The actual map from the point-local ring into the generic common open,
including the selected chart denominator localization. -/
noncomputable def pointLocalToCommonOpen
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q) :
    Localization.AtPrime M →+* genericOpenExtraAwayB M f e g :=
  (algebraMap (genericOpenRing M f e)
    (genericOpenExtraAwayB M f e g)).comp
      (localPointToGenericOpen M f e)

/-- Restriction to the original finite-type ring recovers the sole common-open
map from that ring.  This is the comparison that induces parameter
compatibility; it is not supplied as an additional hypothesis. -/
theorem pointLocalToCommonOpen_comp_algebraMap
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q) :
    (pointLocalToCommonOpen (A := A) M f e g).comp
      (algebraMap A (Localization.AtPrime M)) =
    genericOpenExtraAwayBMap M f e g := by
  ext a
  simp [pointLocalToCommonOpen, genericOpenExtraAwayBMap, genericOpenBMap,
    localPointToGenericOpen_apply]

/-- A chosen field-valued arc on the original chart extends to the actual
common open, and its restriction along the point-local map is the canonical
localization of that same arc. -/
theorem genericArcToExtraAway_comp_pointLocalToCommonOpen
    {L : Type*} [Field L]
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    (ρ : A →+* L)
    (hf : IsUnit (ρ (algebraMap Q A f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b))
    (hg : IsUnit (ρ (algebraMap Q A g))) :
    (genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg).comp
      (pointLocalToCommonOpen (A := A) M f e g) =
        localPointToField (B := A) M ρ hunitM := by
  apply IsLocalization.ringHom_ext M.primeCompl
  ext b
  simp [pointLocalToCommonOpen, genericArcToGenericOpenExtraAwayB,
    genericOpenExtraAwayBMap, genericArcToGenericOpen_apply,
    localPointToGenericOpen_apply, localPointToField_apply]

/-- If the local point map and the generic-open algebra map come from the
same polynomial parameters on `A`, then their induced maps agree on every
parameter.  The equality follows from the preceding actual localization-map
identity and the scalar tower `k → R → A`. -/
theorem pointLocalToCommonOpen_parameter_map
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q) :
    let T := Localization.AtPrime M
    let U := genericOpenExtraAwayB M f e g
    let Cq := genericOpenRing M f e
    letI : Algebra R T := Algebra.compHom T (algebraMap R A)
    letI : Algebra R Cq :=
      ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
    letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
    ∀ j : Option (Fin d),
      pointLocalToCommonOpen (A := A) M f e g
        (algebraMap R T (MvPolynomial.X j)) =
      algebraMap R U (MvPolynomial.X j) := by
  dsimp
  let T := Localization.AtPrime M
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra R T := Algebra.compHom T (algebraMap R A)
  letI : SMul R T := (inferInstance : Algebra R T).toSMul
  letI : SMul A T := (inferInstance : Algebra A T).toSMul
  letI : IsScalarTower R A T :=
    IsScalarTower.of_algebraMap_eq'
      (show algebraMap R T = (algebraMap A T).comp (algebraMap R A) from rfl)
  letI : Algebra R Cq :=
    ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A Cq :=
    IsScalarTower.of_algebraMap_eq'
      (show algebraMap R Cq = (algebraMap A Cq).comp (algebraMap R A) from rfl)
  letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
  intro j
  have hloc := pointLocalToCommonOpen_comp_algebraMap (A := A) M f e g
  have hRU : (genericOpenExtraAwayBMap M f e g).comp
      (algebraMap R A) = algebraMap R U := by
    apply RingHom.ext
    intro r
    change algebraMap Cq U
      (genericOpenBMap M f e (algebraMap R A r)) =
        algebraMap Cq U (algebraMap A Cq (algebraMap R A r))
    rfl
  have hloc' (x : A) :
      pointLocalToCommonOpen (A := A) M f e g
        (algebraMap A T x) = genericOpenExtraAwayBMap M f e g x := by
    have hx := congrArg (fun φ : A →+* U => φ x) hloc
    simpa only [RingHom.comp_apply] using hx
  calc
    pointLocalToCommonOpen (A := A) M f e g
        (algebraMap R T (MvPolynomial.X j)) =
      pointLocalToCommonOpen (A := A) M f e g
        (algebraMap A T (algebraMap R A (MvPolynomial.X j))) := by
          rw [IsScalarTower.algebraMap_apply R A T]
    _ = genericOpenExtraAwayBMap M f e g
        (algebraMap R A (MvPolynomial.X j)) := by
          exact hloc' _
    _ = algebraMap R U (MvPolynomial.X j) := by
      have hX := congrArg (fun φ : R →+* U => φ (MvPolynomial.X j)) hRU
      change genericOpenExtraAwayBMap M f e g
        (algebraMap R A (MvPolynomial.X j)) = algebraMap R U (MvPolynomial.X j)
      simpa only [RingHom.comp_apply] using hX

theorem pointLocalToCommonOpen_comp_polynomialMap
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q) :
    let T := Localization.AtPrime M
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Algebra A T := inferInstance
    letI : Algebra R T := inferInstance
    letI : Algebra R Cq :=
      ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
    letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
    (pointLocalToCommonOpen (A := A) M f e g).comp (algebraMap R T) =
      algebraMap R U := by
  dsimp
  let T := Localization.AtPrime M
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra A T := inferInstance
  letI : Algebra R T := inferInstance
  letI : Algebra R Cq :=
    ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A Cq :=
    IsScalarTower.of_algebraMap_eq'
      (show algebraMap R Cq = (algebraMap A Cq).comp (algebraMap R A) from rfl)
  letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
  have hRT : algebraMap R T = (algebraMap A T).comp (algebraMap R A) := by
    exact IsScalarTower.algebraMap_eq R A T
  apply MvPolynomial.ringHom_ext
  · intro c
    have hc : algebraMap R T (MvPolynomial.C c) =
        algebraMap A T (algebraMap k A c) := by
      have hcomp := congrArg (fun φ : R →+* T => φ (MvPolynomial.C c)) hRT
      calc
        algebraMap R T (MvPolynomial.C c) =
            algebraMap A T (algebraMap R A (MvPolynomial.C c)) := by
              simpa only [RingHom.comp_apply] using hcomp
        _ = algebraMap A T (algebraMap k A c) := by
              congr 1
              exact (IsScalarTower.algebraMap_apply k R A c).symm
    calc
      pointLocalToCommonOpen (A := A) M f e g
          (algebraMap R T (MvPolynomial.C c)) =
        pointLocalToCommonOpen (A := A) M f e g
          (algebraMap A T (algebraMap k A c)) := congrArg _ hc
      _ = genericOpenExtraAwayBMap M f e g (algebraMap k A c) := by
        have hl := congrArg
          (fun φ : A →+* U => φ (algebraMap k A c))
          (pointLocalToCommonOpen_comp_algebraMap (A := A) M f e g)
        simpa only [RingHom.comp_apply] using hl
      _ = algebraMap R U (MvPolynomial.C c) := by
        have hRU : (genericOpenExtraAwayBMap M f e g).comp
            (algebraMap R A) = algebraMap R U := by
          apply RingHom.ext
          intro r
          change algebraMap Cq U
              (genericOpenBMap M f e (algebraMap R A r)) =
            algebraMap Cq U (algebraMap A Cq (algebraMap R A r))
          rfl
        have hr := congrArg
          (fun φ : R →+* U => φ (MvPolynomial.C c)) hRU
        have hkc : algebraMap R A (MvPolynomial.C c) = algebraMap k A c :=
          (IsScalarTower.algebraMap_apply k R A c).symm
        rw [← hkc]
        exact hr
  · intro i
    exact pointLocalToCommonOpen_parameter_map (A := A) M f e g i

noncomputable def pointLocalToCommonOpenAlg
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    let T := Localization.AtPrime M
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Algebra A T := inferInstance
    letI : Algebra R T := inferInstance
    letI : Algebra R Cq :=
      ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
    letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
    letI : IsScalarTower k R T := scalarTower_k_R_pointLocal (A := A) M
    letI : Algebra k U := Algebra.compHom U (algebraMap k R)
    letI : SMul R U := (inferInstance : Algebra R U).toSMul
    letI : SMul k U := (inferInstance : Algebra k U).toSMul
    letI : IsScalarTower k R U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      rfl
    T →ₐ[k] U := by
  dsimp
  let T := Localization.AtPrime M
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra A T := inferInstance
  letI : Algebra R T := inferInstance
  letI : Algebra R Cq :=
    ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
  letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
  letI : IsScalarTower k R T := scalarTower_k_R_pointLocal (A := A) M
  letI : Algebra k U := Algebra.compHom U (algebraMap k R)
  letI : SMul R U := (inferInstance : Algebra R U).toSMul
  letI : SMul k U := (inferInstance : Algebra k U).toSMul
  letI : IsScalarTower k R U := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    rfl
  let hR := pointLocalToCommonOpen_comp_polynomialMap (k := k) (d := d) (A := A) M f e g
  refine ⟨pointLocalToCommonOpen (A := A) M f e g, ?_⟩
  intro c
  change pointLocalToCommonOpen (A := A) M f e g (algebraMap k T c) =
    algebraMap k U c
  rw [IsScalarTower.algebraMap_apply k R T c]
  have hc := congrArg (fun φ : R →+* U => φ (algebraMap k R c)) hR
  calc
    pointLocalToCommonOpen (A := A) M f e g
        (algebraMap R T (algebraMap k R c)) =
      algebraMap R U (algebraMap k R c) := by
        simpa only [RingHom.comp_apply] using hc
    _ = algebraMap k U c := (IsScalarTower.algebraMap_apply k R U c).symm

/-- The actual coordinate derivations on the common open restrict to the
coordinate derivations of the selected point-local chart.  The parameter
compatibility is the localization identity above, while formal étaleness of
the common open is transported from the point-local chart. -/
theorem coordinateDerivation_restrict_to_pointLocal
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] (j : Option (Fin d)) :
    let T := Localization.AtPrime M
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Algebra A T := inferInstance
    letI : Algebra R T := inferInstance
    letI : Algebra R Cq :=
      ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
    letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
    letI : IsScalarTower k R T := scalarTower_k_R_pointLocal (A := A) M
    letI : Algebra k U := Algebra.compHom U (algebraMap k R)
    letI : SMul R U := (inferInstance : Algebra R U).toSMul
    letI : SMul k U := (inferInstance : Algebra k U).toSMul
    letI : IsScalarTower k R U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      rfl
    let θ := pointLocalToCommonOpenAlg (k := k) (d := d) (A := A) M f e g
    letI : Algebra T U := θ.toRingHom.toAlgebra' (fun x y => mul_comm (θ x) y)
    letI : SMul T U := (inferInstance : Algebra T U).toSMul
    letI : SMul U U := (inferInstance : Algebra U U).toSMul
    letI : IsScalarTower k T U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      change algebraMap k U c = algebraMap T U (algebraMap k T c)
      rw [RingHom.algebraMap_toAlgebra' _ (fun x y => mul_comm (θ x) y)]
      exact (θ.commutes c).symm
    letI : IsScalarTower T U U := ⟨fun t u₁ u₂ => by
      change (algebraMap T U t * u₁) * u₂ =
        algebraMap T U t * (u₁ * u₂)
      exact mul_assoc _ _ _⟩
    letI : Algebra.FormallyEtale R U := by
      simpa [U, Cq] using formallyEtale_genericOpenExtraAway_of_pointLocal M f e g
    (Algebra.linearMap T U).compDer
        (coordinateDerivation (k := k) (σ := Option (Fin d)) (B := T) j) =
      ((coordinateDerivation (k := k) (σ := Option (Fin d))
        (B := U) (L := U) j).compAlgebraMap T) := by
  dsimp
  let T := Localization.AtPrime M
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra A T := inferInstance
  letI : Algebra R T := inferInstance
  letI : Algebra R Cq :=
    ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A T := by infer_instance
  letI : IsScalarTower R A Cq :=
    IsScalarTower.of_algebraMap_eq'
      (show algebraMap R Cq = (algebraMap A Cq).comp (algebraMap R A) from rfl)
  letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
  letI : IsScalarTower k R T := scalarTower_k_R_pointLocal (A := A) M
  letI : Algebra k U := Algebra.compHom U (algebraMap k R)
  letI : SMul R U := (inferInstance : Algebra R U).toSMul
  letI : SMul k U := (inferInstance : Algebra k U).toSMul
  letI : IsScalarTower k R U := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    rfl
  let θ := pointLocalToCommonOpenAlg (k := k) (d := d) (A := A) M f e g
  letI : Algebra T U := θ.toRingHom.toAlgebra' (fun x y => mul_comm (θ x) y)
  letI : Algebra.FormallyEtale R U := by
    simpa [U, Cq] using formallyEtale_genericOpenExtraAway_of_pointLocal M f e g
  letI : SMul T U := (inferInstance : Algebra T U).toSMul
  letI : SMul U U := (inferInstance : Algebra U U).toSMul
  letI : IsScalarTower k T U := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    change algebraMap k U c = algebraMap T U (algebraMap k T c)
    rw [RingHom.algebraMap_toAlgebra' _ (fun x y => mul_comm (θ x) y)]
    exact (θ.commutes c).symm
  letI : IsScalarTower T U U := ⟨fun t u₁ u₂ => by
    change (algebraMap T U t * u₁) * u₂ =
      algebraMap T U t * (u₁ * u₂)
    exact mul_assoc _ _ _⟩
  have hparam : ∀ i : Option (Fin d),
      algebraMap T U (algebraMap R T (MvPolynomial.X i)) =
        algebraMap R U (MvPolynomial.X i) := by
    intro i
    calc
      algebraMap T U (algebraMap R T (MvPolynomial.X i)) =
          pointLocalToCommonOpen (A := A) M f e g
            (algebraMap R T (MvPolynomial.X i)) := by
              rw [RingHom.algebraMap_toAlgebra' _ (fun x y => mul_comm (θ x) y)]
              change pointLocalToCommonOpen (A := A) M f e g
                (algebraMap R T (MvPolynomial.X i)) = _
              rfl
      _ = algebraMap R U (MvPolynomial.X i) :=
        pointLocalToCommonOpen_parameter_map (A := A) M f e g i
  exact coordinateDerivation_compAlgebraMap (k := k)
    (σ := Option (Fin d)) (B := T) (C := U) hparam j

/-- The canonical tilted arc on the `Option (Fin d)` chart, reindexed through
the existing `Fin (d+1)` completion and then included into its fraction field. -/
noncomputable def pointLocalFinSuccArcFractionField
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    (α : Fin d → k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    Localization.AtPrime M →ₐ[k] FractionRing (PowerSeries k) :=
  (IsScalarTower.toAlgHom k (PowerSeries k) (FractionRing (PowerSeries k))).comp
    ((SmoothLocalTiltedArcAxisLift.punitToPowerSeries (k := k)).toAlgHom.comp
      ((MvPowerSeries.substAlgHom
        (SmoothLocalTiltedArcAxisLift.tiltedArcHasSubstPUnit (k := k) α)).comp
        (PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
          (k := k) (B := A) (d := d) M eM)))

/-- The canonical point-local tilted arc viewed as a field-valued map on the
original chart algebra. -/
noncomputable def originalToPointLocalFinSuccArcFractionField
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    (α : Fin d → k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    A →+* FractionRing (PowerSeries k) :=
  (pointLocalFinSuccArcFractionField (k := k) (d := d) (A := A) M eM α).toRingHom.comp
    (algebraMap A (Localization.AtPrime M))

/-- The canonical point-local tilted arc with values in the Laurent-series
field used by the projective-conormal comparison. -/
private theorem groundMap_powerSeries_to_laurent (c : k) :
    algebraMap k (LaurentSeries k) c =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (algebraMap k (PowerSeries k) c) := by rfl

theorem groundTower_powerSeries_to_laurent :
    letI : Module k (LaurentSeries k) := Algebra.toModule
    letI : SMul k (LaurentSeries k) :=
      (Algebra.toModule : Module k (LaurentSeries k)).toSMul
    IsScalarTower k (PowerSeries k) (LaurentSeries k) := by
  letI : Module k (LaurentSeries k) := Algebra.toModule
  letI : SMul k (LaurentSeries k) :=
    (Algebra.toModule : Module k (LaurentSeries k)).toSMul
  exact IsScalarTower.of_algebraMap_eq groundMap_powerSeries_to_laurent

noncomputable def pointLocalFinSuccArcLaurentSeries
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    (α : Fin d → k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    Localization.AtPrime M →ₐ[k] LaurentSeries k := by
  letI : Module k (LaurentSeries k) := Algebra.toModule
  letI : SMul k (LaurentSeries k) :=
    (Algebra.toModule : Module k (LaurentSeries k)).toSMul
  letI : IsScalarTower k (PowerSeries k) (LaurentSeries k) :=
    groundTower_powerSeries_to_laurent
  exact (IsScalarTower.toAlgHom k (PowerSeries k) (LaurentSeries k)).comp
    ((SmoothLocalTiltedArcAxisLift.punitToPowerSeries (k := k)).toAlgHom.comp
      ((MvPowerSeries.substAlgHom
        (SmoothLocalTiltedArcAxisLift.tiltedArcHasSubstPUnit (k := k) α)).comp
        (PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
          (k := k) (B := A) (d := d) M eM)))

/-- The original chart algebra map into Laurent series for this same
point-local tilted arc. -/
noncomputable def originalToPointLocalFinSuccArcLaurentSeries
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    (α : Fin d → k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    A →+* LaurentSeries k :=
  (pointLocalFinSuccArcLaurentSeries (k := k) (d := d) (A := A) M eM α).toRingHom.comp
    (algebraMap A (Localization.AtPrime M))

/-- The canonical point-local arc preserves the ground field map. -/
theorem originalToPointLocalFinSuccArcLaurentSeries_base
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    (α : Fin d → k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] (c : k) :
    originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := A) M eM α (algebraMap k A c) =
      algebraMap k (LaurentSeries k) c := by
  letI : Module k (LaurentSeries k) := Algebra.toModule
  letI : SMul k (LaurentSeries k) :=
    (Algebra.toModule : Module k (LaurentSeries k)).toSMul
  letI : IsScalarTower k (PowerSeries k) (LaurentSeries k) :=
    groundTower_powerSeries_to_laurent
  change pointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := A) M eM α
      (algebraMap A (Localization.AtPrime M) (algebraMap k A c)) = _
  rw [← IsScalarTower.algebraMap_apply k A (Localization.AtPrime M) c]
  exact (pointLocalFinSuccArcLaurentSeries
    (k := k) (d := d) (A := A) M eM α).commutes c

/-- Applying an actual field-valued arc to the common-open coordinate
derivation agrees, on every element of the selected local ring, with the
same coordinate derivation followed by the localized arc. -/
theorem genericArc_coordinateDerivation_on_pointLocal
    {L : Type*} [Field L]
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    (ρ : A →+* L)
    (hf : IsUnit (ρ (algebraMap Q A f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b))
    (hg : IsUnit (ρ (algebraMap Q A g)))
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (j : Option (Fin d)) (b : Localization.AtPrime M) :
    let T := Localization.AtPrime M
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Algebra A T := inferInstance
    letI : Algebra R T := inferInstance
    letI : Algebra R Cq :=
      ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
    letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
    letI : IsScalarTower k R T := scalarTower_k_R_pointLocal (A := A) M
    letI : Algebra k U := Algebra.compHom U (algebraMap k R)
    letI : SMul R U := (inferInstance : Algebra R U).toSMul
    letI : SMul k U := (inferInstance : Algebra k U).toSMul
    letI : IsScalarTower k R U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      rfl
    let θ := pointLocalToCommonOpenAlg (k := k) (d := d) (A := A) M f e g
    letI : Algebra T U := θ.toRingHom.toAlgebra' (fun x y => mul_comm (θ x) y)
    letI : SMul T U := (inferInstance : Algebra T U).toSMul
    letI : SMul U U := (inferInstance : Algebra U U).toSMul
    letI : IsScalarTower k T U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      change algebraMap k U c = algebraMap T U (algebraMap k T c)
      rw [RingHom.algebraMap_toAlgebra' _ (fun x y => mul_comm (θ x) y)]
      exact (θ.commutes c).symm
    letI : IsScalarTower T U U := ⟨fun t u₁ u₂ => by
      change (algebraMap T U t * u₁) * u₂ =
        algebraMap T U t * (u₁ * u₂)
      exact mul_assoc _ _ _⟩
    letI : Algebra.FormallyEtale R U :=
      formallyEtale_genericOpenExtraAway_of_pointLocal M f e g
    genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg
      (EtaleCotangentBasis.coordinateDerivation
        (k := k) (σ := Option (Fin d)) (B := genericOpenExtraAwayB M f e g)
        (L := genericOpenExtraAwayB M f e g) j
        (pointLocalToCommonOpen (A := A) M f e g b)) =
      localPointToField (B := A) M ρ hunitM
        (EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := Localization.AtPrime M)
          (L := Localization.AtPrime M) j b) := by
  let T := Localization.AtPrime M
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra A T := inferInstance
  letI : Algebra R T := inferInstance
  letI : Algebra R Cq :=
    ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A T := inferInstance
  letI : IsScalarTower R A Cq :=
    IsScalarTower.of_algebraMap_eq'
      (show algebraMap R Cq = (algebraMap A Cq).comp (algebraMap R A) from rfl)
  letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
  letI : IsScalarTower k R T := scalarTower_k_R_pointLocal (A := A) M
  letI : Algebra k U := Algebra.compHom U (algebraMap k R)
  letI : SMul R U := (inferInstance : Algebra R U).toSMul
  letI : SMul k U := (inferInstance : Algebra k U).toSMul
  letI : IsScalarTower k R U := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    rfl
  let θ := pointLocalToCommonOpenAlg (k := k) (d := d) (A := A) M f e g
  letI : Algebra T U := θ.toRingHom.toAlgebra' (fun x y => mul_comm (θ x) y)
  letI : SMul T U := (inferInstance : Algebra T U).toSMul
  letI : SMul U U := (inferInstance : Algebra U U).toSMul
  letI : IsScalarTower k T U := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    change algebraMap k U c = algebraMap T U (algebraMap k T c)
    rw [RingHom.algebraMap_toAlgebra' _ (fun x y => mul_comm (θ x) y)]
    exact (θ.commutes c).symm
  letI : IsScalarTower T U U := ⟨fun t u₁ u₂ => by
    change (algebraMap T U t * u₁) * u₂ =
      algebraMap T U t * (u₁ * u₂)
    exact mul_assoc _ _ _⟩
  letI : Algebra.FormallyEtale R U :=
    formallyEtale_genericOpenExtraAway_of_pointLocal M f e g
  have htheta : θ.toRingHom = pointLocalToCommonOpen (A := A) M f e g := by
    ext x
    rfl
  have hmap : algebraMap T U = pointLocalToCommonOpen (A := A) M f e g := by
    rw [RingHom.algebraMap_toAlgebra' _ (fun x y => mul_comm (θ x) y)]
    exact htheta
  have hcomp := genericArcToExtraAway_comp_pointLocalToCommonOpen
    (A := A) M f e g ρ hf hunitM hg
  have hder := congrArg
    (fun D : Derivation k T U => D b)
    (coordinateDerivation_restrict_to_pointLocal
      (k := k) (d := d) (A := A) M f e g j)
  change algebraMap T U
      (EtaleCotangentBasis.coordinateDerivation
        (k := k) (σ := Option (Fin d)) (B := T) (L := T) j b) =
    EtaleCotangentBasis.coordinateDerivation
      (k := k) (σ := Option (Fin d)) (B := U) (L := U) j
        (algebraMap T U b) at hder
  rw [hmap] at hder
  calc
    genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg
        (EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := U) (L := U) j
          (pointLocalToCommonOpen (A := A) M f e g b)) =
      genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg
        (pointLocalToCommonOpen (A := A) M f e g
          (EtaleCotangentBasis.coordinateDerivation
            (k := k) (σ := Option (Fin d)) (B := T) (L := T) j b)) :=
          congrArg _ hder.symm
    _ = localPointToField (B := A) M ρ hunitM
        (EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := T) (L := T) j b) := by
      have h := congrArg
        (fun φ : T →+* L => φ
          (EtaleCotangentBasis.coordinateDerivation
            (k := k) (σ := Option (Fin d)) (B := T) (L := T) j b)) hcomp
      simpa only [RingHom.comp_apply] using h

/-- The actual common-open arc has the canonical ground-field restriction
when it is built from the same point-local tilted arc. -/
theorem genericArcToPointLocalLaurentSeries_base
    (M : Ideal A) [M.IsMaximal] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (eM : (A ⧸ M) ≃ₐ[k] k) (α : Fin d → k)
    (hf : IsUnit (originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := A) M eM α (algebraMap Q A f)))
    (hunitM : ∀ b, b ∉ M → IsUnit
      (originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := A) M eM α b))
    (hg : IsUnit (originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := A) M eM α (algebraMap Q A g)))
    (c : k) :
    let T := Localization.AtPrime M
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Algebra A T := inferInstance
    letI : Algebra R T := inferInstance
    letI : Algebra R Cq :=
      ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
    letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
    letI : IsScalarTower k R T := scalarTower_k_R_pointLocal (A := A) M
    letI : Algebra k U := Algebra.compHom U (algebraMap k R)
    letI : SMul R U := (inferInstance : Algebra R U).toSMul
    letI : SMul k U := (inferInstance : Algebra k U).toSMul
    letI : IsScalarTower k R U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      rfl
    (genericArcToGenericOpenExtraAwayB M f e
      (originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := A) M eM α) hf hunitM g hg)
        (algebraMap k U c) = algebraMap k (LaurentSeries k) c := by
  dsimp
  let T := Localization.AtPrime M
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  let ρ := originalToPointLocalFinSuccArcLaurentSeries
    (k := k) (d := d) (A := A) M eM α
  letI : Algebra A T := inferInstance
  letI : Algebra R T := inferInstance
  letI : Algebra R Cq :=
    ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A T := inferInstance
  letI : IsScalarTower R A Cq :=
    IsScalarTower.of_algebraMap_eq'
      (show algebraMap R Cq = (algebraMap A Cq).comp (algebraMap R A) from rfl)
  letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
  letI : IsScalarTower k R T := scalarTower_k_R_pointLocal (A := A) M
  letI : Algebra k U := Algebra.compHom U (algebraMap k R)
  letI : SMul R U := (inferInstance : Algebra R U).toSMul
  letI : SMul k U := (inferInstance : Algebra k U).toSMul
  letI : IsScalarTower k R U := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    rfl
  let θ := pointLocalToCommonOpenAlg (k := k) (d := d) (A := A) M f e g
  letI : Algebra T U := θ.toRingHom.toAlgebra' (fun x y => mul_comm (θ x) y)
  have hθ : θ.toRingHom = pointLocalToCommonOpen (A := A) M f e g := by
    ext x
    rfl
  have hcomm (c : k) :
      pointLocalToCommonOpen (A := A) M f e g (algebraMap k T c) =
        algebraMap k U c := by
    have h := θ.commutes c
    change pointLocalToCommonOpen (A := A) M f e g
      (algebraMap k T c) = algebraMap k U c at h
    exact h
  have hcomp := genericArcToExtraAway_comp_pointLocalToCommonOpen
    (A := A) M f e g ρ hf hunitM hg
  have heval := congrArg
    (fun φ : T →+* LaurentSeries k => φ (algebraMap k T c)) hcomp
  change genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg
      (pointLocalToCommonOpen (A := A) M f e g (algebraMap k T c)) =
    localPointToField (B := A) M ρ hunitM (algebraMap k T c) at heval
  calc
    genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg
        (algebraMap k U c) =
      genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg
        (pointLocalToCommonOpen (A := A) M f e g (algebraMap k T c)) :=
          congrArg _ (hcomm c).symm
    _ = localPointToField (B := A) M ρ hunitM (algebraMap k T c) := heval
    _ = ρ (algebraMap k A c) := by
          rw [IsScalarTower.algebraMap_apply k A T c]
          exact localPointToField_apply M ρ hunitM (algebraMap k A c)
    _ = algebraMap k (LaurentSeries k) c := by
          exact originalToPointLocalFinSuccArcLaurentSeries_base
            (k := k) (d := d) (A := A) M eM α c


end
end Stafford38.Geometry.ActualCommonOpenCompletionDerivation
