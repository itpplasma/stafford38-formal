module
public import Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.PrescribedGroundPointUnitPowerConsumer

open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

variable {k : Type*} [Field k] [IsAlgClosed k]

local notation "R" => MvPolynomial (Option (Fin 1)) k

/-- Concrete one-coordinate check: for the divisor `X = 0`, the produced chart
sends `X` to the distinguished formal variable and factors `X²`, `X³` with
units whose constant terms are nonzero. -/
theorem x2_x3_have_prescribed_ground_chart :
    ∃ (P : Ideal R) (_hP : P.IsPrime),
      MvPolynomial.X none ∈ P ∧
      (∃ (M : Ideal R) (_hM : M.IsMaximal)
        (chart : Localization.AtPrime M →ₐ[k] MvPowerSeries (Fin 2) k)
        (U₀ U₁ : MvPowerSeries (Fin 2) k),
        chart (algebraMap R (Localization.AtPrime M) (MvPolynomial.X none)) =
          MvPowerSeries.X (0 : Fin 2) ∧
        chart (algebraMap R (Localization.AtPrime M)
          (MvPolynomial.X (some (0 : Fin 1)))) = MvPowerSeries.X (1 : Fin 2) ∧
        chart (algebraMap R (Localization.AtPrime M) ((MvPolynomial.X none)^2)) =
          MvPowerSeries.X (0 : Fin 2)^2 * U₀ ∧
        chart (algebraMap R (Localization.AtPrime M) ((MvPolynomial.X none)^3)) =
          MvPowerSeries.X (0 : Fin 2)^3 * U₁ ∧
        U₀ = 1 ∧ U₁ = 1 ∧
        MvPowerSeries.constantCoeff U₀ ≠ 0 ∧ MvPowerSeries.constantCoeff U₁ ≠ 0) := by
  classical
  let eval0 : R →+* k := MvPolynomial.eval (fun _ : Option (Fin 1) => (0 : k))
  let P : Ideal R := RingHom.ker eval0
  have hP : P.IsPrime := RingHom.ker_isPrime eval0
  have hsP : MvPolynomial.X (none : Option (Fin 1)) ∈ P := by
    change eval0 (MvPolynomial.X none) = 0
    simp [eval0]
  letI : P.IsPrime := hP
  letI : IsLocalization P.primeCompl (Localization.AtPrime P) := inferInstance
  have hEt : Algebra.FormallyEtale R (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization P.primeCompl
  have h0 : algebraMap R (Localization.AtPrime P) ((MvPolynomial.X none)^2) =
      algebraMap R (Localization.AtPrime P) (MvPolynomial.X none)^2 * 1 := by
    simp
  have h1 : algebraMap R (Localization.AtPrime P) ((MvPolynomial.X none)^3) =
      algebraMap R (Localization.AtPrime P) (MvPolynomial.X none)^3 * 1 := by
    simp
  obtain ⟨fUnit, fEtale, M, hM, hrest⟩ :=
    Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.exists_prescribed_ground_point_chart_with_unit_powers
      (k := k) (B := R) (d := 1) P (MvPolynomial.X none)
      ((MvPolynomial.X none)^2) ((MvPolynomial.X none)^3)
      rfl hsP hEt 2 3 ⟨by omega, by omega⟩ 1 1 isUnit_one isUnit_one h0 h1
  letI : M.IsMaximal := hM
  rcases hrest with ⟨eM, hEtM, v₀, v₁, _huP, _huM, hPM, _hfP, _hfM,
    _hStandard, _hU₀, _hU₁, _hAway₀, _hAway₁, _hOrders, hChart⟩
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  rcases hChart with ⟨U₀, U₁, _hu₀, _hu₁, hc₀, hc₁, hAxis, _hcoordinates, hq₀, hq₁⟩
  let chart := Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
    (k := k) (B := R) (d := 1) M eM
  have hX : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) k) ≠ 0 := by
    intro hx
    have hcoeff := congrArg
      (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) hx
    have hzero : (1 : k) = 0 := by
      simpa only [MvPowerSeries.coeff_index_single_self_X, MvPowerSeries.coeff_zero] using hcoeff
    exact one_ne_zero hzero
  have hU₀ : U₀ = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hX)
    calc
      MvPowerSeries.X (0 : Fin 2)^2 * U₀ =
          chart (algebraMap R (Localization.AtPrime M) ((MvPolynomial.X none)^2)) := hq₀.symm
      _ = (chart (algebraMap R (Localization.AtPrime M) (MvPolynomial.X none)))^2 := by
        simp only [map_pow]
      _ = MvPowerSeries.X (0 : Fin 2)^2 * 1 := by rw [hAxis]; simp
  have hU₁ : U₁ = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hX)
    calc
      MvPowerSeries.X (0 : Fin 2)^3 * U₁ =
          chart (algebraMap R (Localization.AtPrime M) ((MvPolynomial.X none)^3)) := hq₁.symm
      _ = (chart (algebraMap R (Localization.AtPrime M) (MvPolynomial.X none)))^3 := by
        simp only [map_pow]
      _ = MvPowerSeries.X (0 : Fin 2)^3 * 1 := by rw [hAxis]; simp
  have hXiP : (algebraMap R R) (MvPolynomial.X (some (0 : Fin 1))) ∈ P := by
    change eval0 (MvPolynomial.X (some (0 : Fin 1))) = 0
    simp [eval0]
  have hXiM : (algebraMap R R) (MvPolynomial.X (some (0 : Fin 1))) ∈ M := hPM hXiP
  have hBeta : Stafford38.Geometry.PrescribedAffineResidueCompletion.residueCoordinates
      (σ := Option (Fin 1)) M eM (some (0 : Fin 1)) = 0 := by
    unfold Stafford38.Geometry.PrescribedAffineResidueCompletion.residueCoordinates
    rw [Ideal.Quotient.mkₐ_eq_mk]
    have hmk : Ideal.Quotient.mk M ((algebraMap R R)
        (MvPolynomial.X (some (0 : Fin 1)))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hXiM
    rw [hmk]
    simp
  refine ⟨P, hP, hsP, ⟨M, hM,
    chart,
    U₀, U₁, ?_, ?_, ?_, ?_, hU₀, hU₁, hc₀, hc₁⟩⟩
  · simpa using hAxis
  · simpa [hBeta] using _hcoordinates (0 : Fin 1)
  · simpa using hq₀
  · simpa using hq₁

end Stafford38.Geometry.PrescribedGroundPointUnitPowerConsumer

#print axioms Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.exists_prescribed_ground_point_chart_with_unit_powers
#print axioms Stafford38.Geometry.PrescribedGroundPointUnitPowerConsumer.x2_x3_have_prescribed_ground_chart
