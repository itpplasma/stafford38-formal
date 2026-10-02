module
public import Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
public import Stafford38.Geometry.SmoothLocalTiltedArcAxisLift

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualPointAxisLift

open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.PrescribedAffineResidueCompletion
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift

universe u

/-- From one prescribed formally-etale ground point, its canonical completion,
centered selected rows, divisor/axis order factorizations, and nonzero equations
for the required generic open, choose one tilt and construct the complete
selected-row axis-lift certificate. The avoidance series is the product of
the smooth/bad open and both ordered coordinates, so no second tilt is chosen
later. -/
theorem exists_actual_point_axis_lift
    {k B : Type u} [Field k] [Infinite k] [CharZero k]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    {d n : ℕ} (M : Ideal B) [M.IsMaximal]
    (eM : (B ⧸ M) ≃ₐ[k] k)
    (f : MvPolynomial (Option (Fin d)) k →ₐ[k] B)
    [Algebra (MvPolynomial (Option (Fin d)) k) B]
    [IsScalarTower k (MvPolynomial (Option (Fin d)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) B]
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (Localization.AtPrime M)]
    (hmap : algebraMap (MvPolynomial (Option (Fin d)) k) B = f.toRingHom)
    (s bad : B) (hs : f (MvPolynomial.X none) = s) (hsM : s ∈ M)
    (hbad : bad ≠ 0)
    (qB : Fin (n + 1) → B) (chart : Fin (n + 1)) (axis : Fin n)
    (hqchart : qB chart = 1)
    (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (u₀ u₁ : Localization.AtPrime M)
    (hu₀ : IsUnit u₀) (hu₁ : IsUnit u₁)
    (hq₀ : algebraMap B (Localization.AtPrime M) (qB 0) =
      (algebraMap B (Localization.AtPrime M) s) ^ a * u₀)
    (hq₁ : algebraMap B (Localization.AtPrime M) (qB axis.succ) =
      (algebraMap B (Localization.AtPrime M) s) ^ b * u₁)
    (rows : Fin d ↪ Fin (n + 1))
    (hrows : ∀ j, f (MvPolynomial.X (some j)) = qB (rows j)) :
    ∃ α : Fin d → k,
      tiltedArc (k := k) α
        ((localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
          (algebraMap B (Localization.AtPrime M) bad)) *
         localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
          (algebraMap B (Localization.AtPrime M) (qB 0)) *
         localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
          (algebraMap B (Localization.AtPrime M) (qB axis.succ))) ≠ 0 ∧
      SelectedCoordinateAxisLiftData (k := k)
        (fun i => localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
          (algebraMap B (Localization.AtPrime M) (qB i)))
        rows chart 0 axis.succ a b
        (fun j => residueCoordinates M eM (some j)) α
        (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM u₀)
        (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM u₁) := by
  classical
  let R := MvPolynomial (Option (Fin d)) k
  let T := Localization.AtPrime M
  let Φ := localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
  let q : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k :=
    fun i => Φ (algebraMap B T (qB i))
  let U₀ : MvPowerSeries (Fin (d + 1)) k := Φ u₀
  let U₁ : MvPowerSeries (Fin (d + 1)) k := Φ u₁
  let badSeries : MvPowerSeries (Fin (d + 1)) k := Φ (algebraMap B T bad)
  let badProduct : MvPowerSeries (Fin (d + 1)) k :=
    badSeries * q 0 * q axis.succ
  have hF (p : R) : f p = algebraMap R B p := by
    change f.toRingHom p = algebraMap R B p
    rw [← hmap]
  have hsMap : f (MvPolynomial.X (R := k) none) =
      algebraMap R B (MvPolynomial.X none) := hF _
  have hnoneEq : algebraMap R B (MvPolynomial.X none) = s := by
    rw [← hsMap]
    exact hs
  have hBeta : residueCoordinates (σ := Option (Fin d)) M eM none = 0 := by
    unfold residueCoordinates
    rw [Ideal.Quotient.mkₐ_eq_mk]
    have hmk : Ideal.Quotient.mk M (algebraMap R B (MvPolynomial.X none)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hnoneEq ▸ hsM)
    rw [hmk]
    simp
  have hsPhi : Φ (algebraMap B T s) = MvPowerSeries.X (0 : Fin (d + 1)) := by
    calc
      Φ (algebraMap B T s) =
          Φ (algebraMap B T (algebraMap R B (MvPolynomial.X none))) := by
            rw [hnoneEq]
      _ = MvPowerSeries.C (residueCoordinates M eM none) +
          MvPowerSeries.X (0 : Fin (d + 1)) := by
            exact localToFinSuccPowerSeries_none (k := k) (B := B) (d := d) M eM
      _ = MvPowerSeries.X (0 : Fin (d + 1)) := by rw [hBeta]; simp
  have hrow : ∀ j, q (rows j) =
      MvPowerSeries.C (residueCoordinates M eM (some j)) +
        MvPowerSeries.X j.succ := by
    intro j
    calc
      q (rows j) = Φ (algebraMap B T (f (MvPolynomial.X (some j)))) := by
        simp [q, hrows j]
      _ = Φ (algebraMap B T (algebraMap R B (MvPolynomial.X (some j)))) := by
        rw [hF]
      _ = MvPowerSeries.C (residueCoordinates M eM (some j)) +
          MvPowerSeries.X j.succ := by
        exact localToFinSuccPowerSeries_some (k := k) (B := B) (d := d)
          M eM j
  have hqchart' : q chart = 1 := by
    simp [q, hqchart]
  have hq₀' : q 0 = MvPowerSeries.X (0 : Fin (d + 1)) ^ a * U₀ := by
    calc
      q 0 = Φ (algebraMap B T (qB 0)) := rfl
      _ = Φ ((algebraMap B T s) ^ a * u₀) := congrArg Φ hq₀
      _ = Φ (algebraMap B T s) ^ a * Φ u₀ := by simp
      _ = MvPowerSeries.X (0 : Fin (d + 1)) ^ a * U₀ := by rw [hsPhi]
  have hq₁' : q axis.succ =
      MvPowerSeries.X (0 : Fin (d + 1)) ^ b * U₁ := by
    calc
      q axis.succ = Φ (algebraMap B T (qB axis.succ)) := rfl
      _ = Φ ((algebraMap B T s) ^ b * u₁) := congrArg Φ hq₁
      _ = Φ (algebraMap B T s) ^ b * Φ u₁ := by simp
      _ = MvPowerSeries.X (0 : Fin (d + 1)) ^ b * U₁ := by rw [hsPhi]
  have hU₀ : IsUnit U₀ := IsUnit.map Φ hu₀
  have hU₁ : IsUnit U₁ := IsUnit.map Φ hu₁
  have hU₀cc : MvPowerSeries.constantCoeff U₀ ≠ 0 := by
    have h := MvPowerSeries.isUnit_constantCoeff U₀ hU₀
    exact isUnit_iff_ne_zero.mp h
  have hU₁cc : MvPowerSeries.constantCoeff U₁ ≠ 0 := by
    have h := MvPowerSeries.isUnit_constantCoeff U₁ hU₁
    exact isUnit_iff_ne_zero.mp h
  have hbadSne : badSeries ≠ 0 := by
    exact localToFinSuccPowerSeries_algebraMap_ne_zero
      (k := k) (B := B) (d := d) M eM bad hbad
  have hX : MvPowerSeries.X (0 : Fin (d + 1)) ≠
      (0 : MvPowerSeries (Fin (d + 1)) k) := by
    intro hx
    have hc := congrArg
      (MvPowerSeries.coeff (Finsupp.single (0 : Fin (d + 1)) 1)) hx
    simpa using hc
  have hq₀ne : q 0 ≠ 0 := by
    rw [hq₀']
    exact mul_ne_zero (pow_ne_zero a hX) hU₀.ne_zero
  have hq₁ne : q axis.succ ≠ 0 := by
    rw [hq₁']
    exact mul_ne_zero (pow_ne_zero b hX) hU₁.ne_zero
  have hbadProduct : badProduct ≠ 0 := by
    dsimp [badProduct]
    exact mul_ne_zero (mul_ne_zero hbadSne hq₀ne) hq₁ne
  obtain ⟨α, havoid, hdata⟩ :=
    exists_tilted_local_axis_lift_of_selected_coordinate_rows
      (k := k) q badProduct hbadProduct rows chart 0 axis.succ a b
      (fun j => residueCoordinates M eM (some j)) U₀ U₁
      hqchart' ha hab hq₀' hU₀cc hq₁' hU₁cc hrow
  refine ⟨α, ?_, hdata⟩
  simpa [badProduct, badSeries, q, Φ] using havoid

end Stafford38.Geometry.ActualPointAxisLift
end
