module
public import Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
public import Stafford38.Geometry.ActualPointAxisLift
public import Stafford38.Geometry.SameWitness.AwayFactorToAtPrime

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.ActualOptionGroundPointCompletion
open Stafford38.Geometry.ActualPointAxisLift
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

universe u v

/-- Extract the chosen maximal point and the same tilted arc from the
closed-ground-point output. The two divisor factorizations are transported
from its single away open to the local ring at that same point. -/
theorem exists_axis_lift_of_groundPointChartOutput
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {B : Type u} [CommRing B] [Algebra k B] [IsDomain B]
    [Algebra.FiniteType k B] {σ : Type v} [Fintype σ]
    (P : Ideal B) [P.IsPrime]
    (fOption : MvPolynomial (Option σ) k →ₐ[k] B)
    (s q₀ q₁ : B) (qRow : σ → B)
    (hnone : fOption (MvPolynomial.X none) = s)
    (hsP : s ∈ P)
    (hsome : ∀ z, fOption (MvPolynomial.X (some z)) = qRow z)
    (τ : Fin (Fintype.card σ) ≃ σ) (e₀ e₁ : ℕ)
    (hOutput : GroundPointChartOutput P fOption s q₀ q₁ qRow τ e₀ e₁)
    {n : ℕ} (qB : Fin (n + 1) → B) (chart : Fin (n + 1)) (axis : Fin n)
    (hqchart : qB chart = 1)
    (hzero : qB 0 = q₀) (haxis : qB axis.succ = q₁)
    (rows : Fin (Fintype.card σ) ↪ Fin (n + 1))
    (hrows : ∀ i, qRow (τ i) = qB (rows i))
    (bad : B) (hbad : bad ≠ 0) :
    ∃ (M : Ideal B) (hM : M.IsMaximal) (eM : (B ⧸ M) ≃ₐ[k] k)
      (fUnit : B) (hfUnitM : fUnit ∉ M),
      let R := MvPolynomial (Option (Fin (Fintype.card σ))) k
      let fFin : R →ₐ[k] B := fOption.comp (MvPolynomial.renameEquiv k τ.optionCongr).toAlgHom
      letI : Algebra R B := fFin.toRingHom.toAlgebra
      letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
        ext c
        exact (fFin.commutes c).symm)
      letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
      letI : Algebra R (Localization.AtPrime M) := inferInstance
      ∃ (u₀ u₁ : Localization.AtPrime M) (hu₀ : IsUnit u₀) (hu₁ : IsUnit u₁)
        (hq₀ : algebraMap B (Localization.AtPrime M) (qB 0) =
          (algebraMap B (Localization.AtPrime M) s) ^ e₀ * u₀)
        (hq₁ : algebraMap B (Localization.AtPrime M) (qB axis.succ) =
          (algebraMap B (Localization.AtPrime M) s) ^ e₁ * u₁)
        (hEtM : Algebra.FormallyEtale R (Localization.AtPrime M))
        (α : Fin (Fintype.card σ) → k),
        tiltedArc (k := k) α
          ((localToFinSuccPowerSeries (k := k) (B := B)
              (d := Fintype.card σ) M eM (algebraMap B (Localization.AtPrime M) bad)) *
            localToFinSuccPowerSeries (k := k) (B := B)
              (d := Fintype.card σ) M eM
              (algebraMap B (Localization.AtPrime M) (qB 0)) *
            localToFinSuccPowerSeries (k := k) (B := B)
              (d := Fintype.card σ) M eM
              (algebraMap B (Localization.AtPrime M) (qB axis.succ))) ≠ 0 ∧
        SelectedCoordinateAxisLiftData
          (fun i => localToFinSuccPowerSeries (k := k) (B := B)
            (d := Fintype.card σ) M eM (algebraMap B (Localization.AtPrime M) (qB i)))
          rows chart 0 axis.succ e₀ e₁
          (fun j => Stafford38.Geometry.PrescribedAffineResidueCompletion.residueCoordinates
            M eM (some j)) α
          (localToFinSuccPowerSeries (k := k) (B := B)
            (d := Fintype.card σ) M eM
            u₀)
          (localToFinSuccPowerSeries (k := k) (B := B)
            (d := Fintype.card σ) M eM
            u₁) := by
  classical
  unfold GroundPointChartOutput at hOutput
  rcases hOutput with ⟨fUnit, fEtale, M, hM, eM, v₀, v₁, chartMap, U₀, U₁,
    hfUnitP, hfUnitM, hPM, hfEtaleP, hfEtaleM, hStandard,
    hv₀, hv₁, hAway₀, hAway₁, hOrders, hU₀, hU₁, hcc₀, hcc₁,
    hsChart, hrowChart, hq₀Chart, hq₁Chart, hEtM, hchartEq⟩
  let R := MvPolynomial (Option (Fin (Fintype.card σ))) k
  let fFin : R →ₐ[k] B := fOption.comp (MvPolynomial.renameEquiv k τ.optionCongr).toAlgHom
  letI : Algebra R B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact (fFin.commutes c).symm)
  letI : M.IsMaximal := hM
  letI : Algebra R (Localization.AtPrime M) := inferInstance
  have hEt' : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEt'
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  have hmap : algebraMap R B = fFin.toRingHom :=
    RingHom.algebraMap_toAlgebra fFin.toRingHom
  have hnoneFin : fFin (MvPolynomial.X (R := k) none) = s := by
    simp [fFin, MvPolynomial.renameEquiv, MvPolynomial.rename_X, hnone]
  have hrowsFin (i : Fin (Fintype.card σ)) :
      fFin (MvPolynomial.X (R := k) (some i)) = qB (rows i) := by
    calc
      fFin (MvPolynomial.X (R := k) (some i)) = qRow (τ i) := by
        simp [fFin, MvPolynomial.renameEquiv, MvPolynomial.rename_X, hsome]
      _ = qB (rows i) := hrows i
  have hq₀ : algebraMap B (Localization.Away fUnit) (qB 0) =
      (algebraMap B (Localization.Away fUnit) s) ^ e₀ * v₀ := by
    simpa [hzero] using hAway₀
  have hq₁ : algebraMap B (Localization.Away fUnit) (qB axis.succ) =
      (algebraMap B (Localization.Away fUnit) s) ^ e₁ * v₁ := by
    simpa [haxis] using hAway₁
  obtain ⟨u₀, u₁, hu₀, hu₁, hq₀M, hq₁M⟩ :=
    SameWitness.pair_factorizations_to_atPrime M fUnit hfUnitM s (qB 0)
      (qB axis.succ) e₀ e₁ v₀ v₁ hv₀ hv₁ hq₀ hq₁
  have hsM : s ∈ M := hPM hsP
  obtain ⟨α, havoid, hdata⟩ :=
    exists_actual_point_axis_lift M eM fFin hmap s bad hnoneFin hsM hbad qB chart axis
      hqchart e₀ e₁ hOrders.1 hOrders.2 u₀ u₁ hu₀ hu₁ hq₀M hq₁M rows hrowsFin
  exact ⟨M, hM, eM, fUnit, hfUnitM, u₀, u₁, hu₀, hu₁, hq₀M, hq₁M,
    hEt', α, havoid, hdata⟩

end Stafford38.Geometry.SameWitness
