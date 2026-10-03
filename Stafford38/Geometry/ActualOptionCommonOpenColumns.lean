import Stafford38.Geometry.ActualCommonOpenCompletionDerivation
import Stafford38.Geometry.ActualOptionArcDerivative
import Stafford38.Geometry.EtaleCotangentBasis

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.ActualOptionCommonOpenColumns

open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.ActualOptionArcDerivative
open Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.PrescribedCompletionDerivationCommutation
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift

noncomputable section

universe u v w

variable {k : Type u} [Field k] {d : ℕ}
variable {A : Type v} [CommRing A] [Algebra k A]
  [Algebra (MvPolynomial (Option (Fin d)) k) A]
  [IsScalarTower k (MvPolynomial (Option (Fin d)) k) A]
  [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) A]
variable {Q : Type w} [CommRing Q] [Algebra Q A]

local notation "R" => MvPolynomial (Option (Fin d)) k

/-- For one actual common-open column coming from the selected point-local
column, position, transverse derivatives, and the raw derivative all agree
with the same canonical tilted arc. -/
theorem actual_option_columns
    (M : Ideal A) [M.IsPrime] [M.IsMaximal]
    (f : Q) (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (α : Fin d → k)
    (hf : IsUnit ((originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := A) M eM α) (algebraMap Q A f)))
    (hunitM : ∀ b, b ∉ M → IsUnit
      ((originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := A) M eM α) b))
    (hg : IsUnit ((originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := A) M eM α) (algebraMap Q A g)))
    (n : ℕ) (qT : Fin (n + 1) → Localization.AtPrime M)
    (qU : Fin (n + 1) → genericOpenExtraAwayB M f e g)
    (hq : ∀ i, qU i = pointLocalToCommonOpen (A := A) M f e g (qT i)) :
    let T := Localization.AtPrime M
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    let rhoA := originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := A) M eM α
    letI : Algebra A T := inferInstance
    letI : Algebra R T := inferInstance
    letI : Algebra R Cq := ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
    letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
    letI : IsScalarTower k R T := by infer_instance
    letI : Algebra k U := Algebra.compHom U (algebraMap k R)
    letI : SMul R U := (inferInstance : Algebra R U).toSMul
    letI : SMul k U := (inferInstance : Algebra k U).toSMul
    letI : IsScalarTower k R U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      rfl
    let theta := pointLocalToCommonOpenAlg (k := k) (d := d) (A := A) M f e g
    letI : Algebra T U := theta.toRingHom.toAlgebra' (fun x y => mul_comm (theta x) y)
    letI : SMul T U := (inferInstance : Algebra T U).toSMul
    letI : SMul U U := (inferInstance : Algebra U U).toSMul
    letI : IsScalarTower k T U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      change algebraMap k U c = algebraMap T U (algebraMap k T c)
      rw [RingHom.algebraMap_toAlgebra' _ (fun x y => mul_comm (theta x) y)]
      exact (theta.commutes c).symm
    letI : IsScalarTower T U U := ⟨fun t u₁ u₂ => by
      change (algebraMap T U t * u₁) * u₂ =
        algebraMap T U t * (u₁ * u₂)
      exact mul_assoc _ _ _⟩
    letI : Algebra.FormallyEtale R U := by
      simpa [U, Cq] using formallyEtale_genericOpenExtraAway_of_pointLocal M f e g
    (∀ i,
      genericArcToGenericOpenExtraAwayB M f e rhoA hf hunitM g hg (qU i) =
        algebraMap (PowerSeries k) (LaurentSeries k)
          (tiltedArc (k := k) α
            (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i)))) ∧
    (∀ j i,
      genericArcToGenericOpenExtraAwayB M f e rhoA hf hunitM g hg
          (coordinateDerivation (k := k) (σ := Option (Fin d))
            (B := genericOpenExtraAwayB M f e g)
            (L := genericOpenExtraAwayB M f e g) (some j) (qU i)) =
        algebraMap (PowerSeries k) (LaurentSeries k)
          (tiltedArc (k := k) α
            (MvPowerSeries.pderiv j.succ
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (qT i))))) ∧
    (∀ i,
      algebraMap (PowerSeries k) (LaurentSeries k)
          (PowerSeries.derivative (R := k)
            (tiltedArc (k := k) α
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (qT i)))) =
        genericArcToGenericOpenExtraAwayB M f e rhoA hf hunitM g hg
            (coordinateDerivation (k := k) (σ := Option (Fin d))
              (B := genericOpenExtraAwayB M f e g)
              (L := genericOpenExtraAwayB M f e g) none (qU i)) +
          ∑ j : Fin d,
            algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C (α j)) *
              genericArcToGenericOpenExtraAwayB M f e rhoA hf hunitM g hg
                (coordinateDerivation (k := k) (σ := Option (Fin d))
                  (B := genericOpenExtraAwayB M f e g)
                  (L := genericOpenExtraAwayB M f e g) (some j) (qU i))) := by
  classical
  dsimp
  let T := Localization.AtPrime M
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  let theta := pointLocalToCommonOpen (A := A) M f e g
  let psi := pointLocalFinSuccArcLaurentSeries
    (k := k) (d := d) (A := A) M eM α
  let rhoA := originalToPointLocalFinSuccArcLaurentSeries
    (k := k) (d := d) (A := A) M eM α
  let rhoU := genericArcToGenericOpenExtraAwayB M f e rhoA hf hunitM g hg
  have hlocal : localPointToField (B := A) M rhoA hunitM = psi.toRingHom := by
    apply IsLocalization.ringHom_ext M.primeCompl
    ext1 a
    change localPointToField (B := A) M rhoA hunitM
      (algebraMap A T a) = psi (algebraMap A T a)
    rw [localPointToField_apply]
    rfl
  letI : Algebra A T := inferInstance
  letI : Algebra R T := inferInstance
  letI : Algebra R Cq :=
    ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A T := inferInstance
  letI : IsScalarTower R A Cq :=
    IsScalarTower.of_algebraMap_eq'
      (show algebraMap R Cq = (algebraMap A Cq).comp (algebraMap R A) from rfl)
  letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
  letI : IsScalarTower k R T := by infer_instance
  letI : Algebra k U := Algebra.compHom U (algebraMap k R)
  letI : SMul R U := (inferInstance : Algebra R U).toSMul
  letI : SMul k U := (inferInstance : Algebra k U).toSMul
  letI : IsScalarTower k R U := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    rfl
  let thetaAlg := pointLocalToCommonOpenAlg (k := k) (d := d) (A := A) M f e g
  letI : Algebra T U :=
    thetaAlg.toRingHom.toAlgebra' (fun x y => mul_comm (thetaAlg x) y)
  letI : SMul T U := (inferInstance : Algebra T U).toSMul
  letI : SMul U U := (inferInstance : Algebra U U).toSMul
  letI : IsScalarTower k T U := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    change algebraMap k U c = algebraMap T U (algebraMap k T c)
    rw [RingHom.algebraMap_toAlgebra' _ (fun x y => mul_comm (thetaAlg x) y)]
    exact (thetaAlg.commutes c).symm
  letI : IsScalarTower T U U := ⟨fun t u₁ u₂ => by
    change (algebraMap T U t * u₁) * u₂ =
      algebraMap T U t * (u₁ * u₂)
    exact mul_assoc _ _ _⟩
  letI : Algebra.FormallyEtale R U :=
    formallyEtale_genericOpenExtraAway_of_pointLocal M f e g
  have hcomp := genericArcToExtraAway_comp_pointLocalToCommonOpen
    (A := A) M f e g rhoA hf hunitM hg
  have hposition (i : Fin (n + 1)) :
      rhoU (qU i) = algebraMap (PowerSeries k) (LaurentSeries k)
        (tiltedArc (k := k) α
          (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i))) := by
    calc
      rhoU (qU i) = rhoU (theta (qT i)) := congrArg rhoU (hq i)
      _ = localPointToField (B := A) M rhoA hunitM (qT i) := by
        have hcomp_i := congrArg (fun φ : T →+* LaurentSeries k => φ (qT i)) hcomp
        simpa [rhoU] using hcomp_i
      _ = psi (qT i) := congrArg (fun φ : T →+* LaurentSeries k => φ (qT i)) hlocal
      _ = _ := rfl
  have hderiv (j : Option (Fin d)) (i : Fin (n + 1)) :
      rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := U) (L := U) j (qU i)) =
        algebraMap (PowerSeries k) (LaurentSeries k)
          (tiltedArc (k := k) α
            (MvPowerSeries.pderiv (j.elim 0 Fin.succ)
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (qT i)))) := by
    have hqderiv :
        coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := U) (L := U) j (qU i) =
        coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := U) (L := U) j (theta (qT i)) :=
      congrArg (coordinateDerivation (k := k) (σ := Option (Fin d))
        (B := U) (L := U) j) (hq i)
    calc
      rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := U) (L := U) j (qU i)) =
        rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := U) (L := U) j (theta (qT i))) := congrArg rhoU hqderiv
      _ = localPointToField (B := A) M rhoA hunitM
          (coordinateDerivation (k := k) (σ := Option (Fin d))
            (B := T) (L := T) j (qT i)) :=
        by
          simpa only [rhoU, theta] using
            (genericArc_coordinateDerivation_on_pointLocal
              (A := A) M f e g rhoA hf hunitM hg j (qT i))
      _ = psi (coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := T) (L := T) j (qT i)) := congrArg (fun φ : T →+* LaurentSeries k =>
            φ (coordinateDerivation (k := k) (σ := Option (Fin d))
              (B := T) (L := T) j (qT i))) hlocal
      _ = _ := by
        cases j with
        | none =>
            have hc := localToFinSuccPowerSeries_commutes_coordinateDerivation
              (k := k) (d := d) (Aₒ := A) M eM 0 (qT i)
            have hc' : MvPowerSeries.pderiv 0
                (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i)) =
                localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                  (coordinateDerivation (k := k) (σ := Option (Fin d))
                    (B := T) (L := T) none (qT i)) := by
              simpa using hc
            change algebraMap (PowerSeries k) (LaurentSeries k)
              (tiltedArc (k := k) α
                (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                  (coordinateDerivation (k := k) (σ := Option (Fin d))
                    (B := T) (L := T) none (qT i)))) =
              algebraMap (PowerSeries k) (LaurentSeries k)
                (tiltedArc (k := k) α
                  (MvPowerSeries.pderiv 0
                    (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i))))
            exact congrArg
              (fun z : MvPowerSeries (Fin (d + 1)) k =>
                algebraMap (PowerSeries k) (LaurentSeries k) (tiltedArc (k := k) α z))
              hc'.symm
        | some j =>
            have hc := localToFinSuccPowerSeries_commutes_coordinateDerivation
              (k := k) (d := d) (Aₒ := A) M eM j.succ (qT i)
            have hc' : MvPowerSeries.pderiv j.succ
                (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i)) =
                localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                  (coordinateDerivation (k := k) (σ := Option (Fin d))
                    (B := T) (L := T) (some j) (qT i)) := by
              simpa using hc
            change algebraMap (PowerSeries k) (LaurentSeries k)
              (tiltedArc (k := k) α
                (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                  (coordinateDerivation (k := k) (σ := Option (Fin d))
                    (B := T) (L := T) (some j) (qT i)))) =
              algebraMap (PowerSeries k) (LaurentSeries k)
                (tiltedArc (k := k) α
                  (MvPowerSeries.pderiv j.succ
                    (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i))))
            exact congrArg
              (fun z : MvPowerSeries (Fin (d + 1)) k =>
                algebraMap (PowerSeries k) (LaurentSeries k) (tiltedArc (k := k) α z))
              hc'.symm
  have hraw (i : Fin (n + 1)) :
      algebraMap (PowerSeries k) (LaurentSeries k)
          (PowerSeries.derivative (R := k)
            (tiltedArc (k := k) α
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (qT i)))) =
        rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := U) (L := U) none (qU i)) +
          ∑ j : Fin d,
            algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C (α j)) *
              rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
                (B := U) (L := U) (some j) (qU i)) := by
    have h := localToFinSuccArc_derivative_eq_option_coordinate_sum
      (k := k) (d := d) (A := A) M eM α (qT i)
    have hmap := congrArg (algebraMap (PowerSeries k) (LaurentSeries k)) h
    have hcomm (j : Option (Fin d)) :
        algebraMap (PowerSeries k) (LaurentSeries k)
            (tiltedArc (k := k) α
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (coordinateDerivation (k := k) (σ := Option (Fin d))
                  (B := T) (L := T) j (qT i)))) =
          algebraMap (PowerSeries k) (LaurentSeries k)
            (tiltedArc (k := k) α
              (MvPowerSeries.pderiv (j.elim 0 Fin.succ)
                (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                  (qT i)))) := by
      cases j with
      | none =>
          have hc := localToFinSuccPowerSeries_commutes_coordinateDerivation
            (k := k) (d := d) (Aₒ := A) M eM 0 (qT i)
          have hc' : MvPowerSeries.pderiv 0
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i)) =
              localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (coordinateDerivation (k := k) (σ := Option (Fin d))
                  (B := T) (L := T) none (qT i)) := by
            simpa using hc
          exact congrArg
            (fun z : MvPowerSeries (Fin (d + 1)) k =>
              algebraMap (PowerSeries k) (LaurentSeries k) (tiltedArc (k := k) α z))
            hc'.symm
      | some j =>
          have hc := localToFinSuccPowerSeries_commutes_coordinateDerivation
            (k := k) (d := d) (Aₒ := A) M eM j.succ (qT i)
          have hc' : MvPowerSeries.pderiv j.succ
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i)) =
              localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (coordinateDerivation (k := k) (σ := Option (Fin d))
                  (B := T) (L := T) (some j) (qT i)) := by
            simpa using hc
          exact congrArg
            (fun z : MvPowerSeries (Fin (d + 1)) k =>
              algebraMap (PowerSeries k) (LaurentSeries k) (tiltedArc (k := k) α z))
            hc'.symm
    calc
      algebraMap (PowerSeries k) (LaurentSeries k)
          (PowerSeries.derivative (R := k)
            (tiltedArc (k := k) α
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (qT i)))) =
        algebraMap (PowerSeries k) (LaurentSeries k)
          ((tiltedArc (k := k) α
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (coordinateDerivation (k := k) (σ := Option (Fin d))
                  (B := T) (L := T) none (qT i))) +
            ∑ j : Fin d, PowerSeries.C (α j) *
              tiltedArc (k := k) α
                (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                  (coordinateDerivation (k := k) (σ := Option (Fin d))
                    (B := T) (L := T) (some j) (qT i))))) := hmap
      _ = _ := by
        rw [map_add, map_sum]
        simp only [map_mul]
        calc
          algebraMap (PowerSeries k) (LaurentSeries k)
              (tiltedArc (k := k) α
                (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                  (coordinateDerivation (k := k) (σ := Option (Fin d))
                    (B := T) (L := T) none (qT i)))) +
            ∑ j : Fin d,
              algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C (α j)) *
                algebraMap (PowerSeries k) (LaurentSeries k)
                  (tiltedArc (k := k) α
                    (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                      (coordinateDerivation (k := k) (σ := Option (Fin d))
                        (B := T) (L := T) (some j) (qT i)))) =
            algebraMap (PowerSeries k) (LaurentSeries k)
                (tiltedArc (k := k) α
                  (MvPowerSeries.pderiv 0
                    (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i)))) +
            ∑ j : Fin d,
              algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C (α j)) *
                algebraMap (PowerSeries k) (LaurentSeries k)
                  (tiltedArc (k := k) α
                    (MvPowerSeries.pderiv j.succ
                      (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i)))) := by
              rw [hcomm none]
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              rw [hcomm (some j)]
              rfl
          _ = rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
                (B := U) (L := U) none (qU i)) +
              ∑ j : Fin d,
                algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C (α j)) *
                  rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
                    (B := U) (L := U) (some j) (qU i)) := by
              have hderiv_none : rhoU (coordinateDerivation (k := k)
                  (σ := Option (Fin d)) (B := U) (L := U) none (qU i)) =
                  algebraMap (PowerSeries k) (LaurentSeries k)
                    (tiltedArc (k := k) α
                      (MvPowerSeries.pderiv 0
                        (localToFinSuccPowerSeries (k := k) (B := A) (d := d)
                          M eM (qT i)))) := by
                simpa using hderiv none i
              rw [← hderiv_none]
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              have hderiv_some : rhoU (coordinateDerivation (k := k)
                  (σ := Option (Fin d)) (B := U) (L := U) (some j) (qU i)) =
                  algebraMap (PowerSeries k) (LaurentSeries k)
                    (tiltedArc (k := k) α
                      (MvPowerSeries.pderiv j.succ
                        (localToFinSuccPowerSeries (k := k) (B := A) (d := d)
                          M eM (qT i)))) := by
                simpa using hderiv (some j) i
              rw [← hderiv_some]
  exact ⟨hposition, (fun j i => hderiv (some j) i), hraw⟩

universe z

variable {n : ℕ}

/-- Promote the transverse and raw common-open coordinate-derivative columns
to the target coefficient field.  This is the scalar-extension identity for
the canonical Kähler-coordinate derivation; the position column is unchanged.
-/
theorem actual_option_columns_to_laurent
    {U : Type w} [CommRing U] [Algebra k U]
    [Algebra (MvPolynomial (Option (Fin d)) k) U]
    [IsScalarTower k (MvPolynomial (Option (Fin d)) k) U]
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) U]
    (M : Ideal A) [M.IsMaximal]
    (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (Localization.AtPrime M)]
    {L : Type z} [CommRing L] [Algebra k L]
    (powerSeriesMap : PowerSeries k →+* L)
    (rhoU : U →+* L)
    (hground : rhoU.comp (algebraMap k U) = algebraMap k L)
    (α : Fin d → k) (qT : Fin (n + 1) → Localization.AtPrime M)
    (qU : Fin (n + 1) → U)
    (hpositionU : ∀ i,
      rhoU (qU i) = powerSeriesMap
        (tiltedArc (k := k) α
          (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
            (qT i))))
    (htransverseU : ∀ j i,
      rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
        (B := U) (L := U) (some j) (qU i)) =
        powerSeriesMap
          (tiltedArc (k := k) α
            (MvPowerSeries.pderiv j.succ
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (qT i)))))
    (hrawU : ∀ i,
      powerSeriesMap
          (PowerSeries.derivative (R := k)
            (tiltedArc (k := k) α
              (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
                (qT i)))) =
        rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := U) (L := U) none (qU i)) +
        ∑ j : Fin d,
          powerSeriesMap (PowerSeries.C (α j)) *
            rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
              (B := U) (L := U) (some j) (qU i))) :
    letI : Algebra U L :=
      RingHom.toAlgebra' rhoU (by intro x y; exact mul_comm _ _)
    letI : IsScalarTower k U L :=
      IsScalarTower.of_algebraMap_eq' (by
        simpa only [RingHom.algebraMap_toAlgebra'] using hground.symm)
    letI : IsScalarTower U L L :=
      ⟨fun x y z => by
        change (algebraMap U L x * y) * z = _
        exact mul_assoc _ _ _⟩
    (∀ i, rhoU (qU i) = powerSeriesMap
      (tiltedArc (k := k) α
        (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM (qT i)))) ∧
    (∀ j i,
      coordinateDerivation (k := k) (σ := Option (Fin d))
        (B := U) (L := L) (some j) (qU i) =
      powerSeriesMap
        (tiltedArc (k := k) α
          (MvPowerSeries.pderiv j.succ
            (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
              (qT i))))) ∧
    (∀ i,
      powerSeriesMap
        (PowerSeries.derivative (R := k)
          (tiltedArc (k := k) α
            (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
              (qT i)))) =
      coordinateDerivation (k := k) (σ := Option (Fin d))
        (B := U) (L := L) none (qU i) +
      ∑ j : Fin d,
        powerSeriesMap (PowerSeries.C (α j)) *
          coordinateDerivation (k := k) (σ := Option (Fin d))
            (B := U) (L := L) (some j) (qU i)) := by
  letI : Algebra U L :=
    RingHom.toAlgebra' rhoU (by intro x y; exact mul_comm _ _)
  letI : IsScalarTower k U L :=
    IsScalarTower.of_algebraMap_eq' (by
      simpa only [RingHom.algebraMap_toAlgebra'] using hground.symm)
  letI : IsScalarTower U L L :=
    ⟨fun x y z => by
      change (algebraMap U L x * y) * z = _
      exact mul_assoc _ _ _⟩
  have hcoord (j : Option (Fin d)) (b : U) :
      rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
        (B := U) (L := U) j b) =
      coordinateDerivation (k := k) (σ := Option (Fin d))
        (B := U) (L := L) j b := by
    simpa only [RingHom.algebraMap_toAlgebra'] using
      (coordinateDerivation_algebraMap (k := k) (σ := Option (Fin d))
        (B := U) (L := L) j b)
  refine ⟨hpositionU, ?_, ?_⟩
  · intro j i
    calc
      coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := U) (L := L) (some j) (qU i) =
        rhoU (coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := U) (L := U) (some j) (qU i)) := (hcoord (some j) (qU i)).symm
      _ = _ := htransverseU j i
  · intro i
    rw [hrawU i]
    simp_rw [hcoord]

end
end Stafford38.Geometry.ActualOptionCommonOpenColumns
