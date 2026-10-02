module
public import Stafford38.Geometry.SameWitness.AxisLiftFromGroundPoint

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.SameWitness.AxisLiftFromGroundPointConsumer

open Stafford38.Geometry.ActualOptionGroundPointCompletion
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

universe u v

/-- Consumer for the same-witness axis lift: the conclusion of
`Stafford38.Geometry.SameWitness.exists_axis_lift_of_groundPointChartOutput`
is restated literally and proved by applying that theorem. -/
theorem exists_axis_lift_of_groundPointChartOutput_consumer
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
  exact Stafford38.Geometry.SameWitness.exists_axis_lift_of_groundPointChartOutput
    P fOption s q₀ q₁ qRow hnone hsP hsome τ e₀ e₁ hOutput qB chart axis
    hqchart hzero haxis rows hrows bad hbad

#print axioms exists_axis_lift_of_groundPointChartOutput_consumer

end Stafford38.Geometry.SameWitness.AxisLiftFromGroundPointConsumer
