import Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap
import Stafford38.Geometry.PaperUnitPowerFactorization
import Stafford38.Geometry.PrescribedEtaleGroundPoint
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

noncomputable section

open Stafford38.Geometry.PrescribedAffineResidueCompletion

variable {k B : Type*} {d : ℕ} [Field k] [CommRing B] [Algebra k B]
  [Algebra (MvPolynomial (Option (Fin d)) k) B]
  [IsScalarTower k (MvPolynomial (Option (Fin d)) k) B]
  [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) B]

local notation "R" => MvPolynomial (Option (Fin d)) k

/-- The prescribed Option-indexed completion chart reindexed by the standard
`Fin (d+1) ≃ Option (Fin d)` equivalence. -/
def localToFinSuccPowerSeries (M : Ideal B) [M.IsMaximal]
    (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    Localization.AtPrime M →ₐ[k] MvPowerSeries (Fin (d + 1)) k :=
  (MvPowerSeries.renameEquiv k (_root_.finSuccEquiv d).symm).toAlgHom.comp
    (Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap.localToPowerSeries
      (σ := Option (Fin d)) M eM)

theorem localToFinSuccPowerSeries_none (M : Ideal B) [M.IsMaximal]
    (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
      (algebraMap B (Localization.AtPrime M)
        (algebraMap R B (MvPolynomial.X none))) =
      MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM none) +
        MvPowerSeries.X (0 : Fin (d + 1)) := by
  simpa [localToFinSuccPowerSeries] using
    congrArg (MvPowerSeries.renameEquiv k (_root_.finSuccEquiv d).symm)
      (Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap.originalAlgebraToPowerSeries_coordinate
        (σ := Option (Fin d)) M eM none)

theorem localToFinSuccPowerSeries_some (M : Ideal B) [M.IsMaximal]
    (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] (i : Fin d) :
    localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
      (algebraMap B (Localization.AtPrime M)
        (algebraMap R B (MvPolynomial.X (some i)))) =
      MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM (some i)) +
        MvPowerSeries.X i.succ := by
  simpa [localToFinSuccPowerSeries] using
    congrArg (MvPowerSeries.renameEquiv k (_root_.finSuccEquiv d).symm)
      (Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap.originalAlgebraToPowerSeries_coordinate
        (σ := Option (Fin d)) M eM (some i))

omit [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) B] in
/-- Combine the actual divisor-prime unit-power factorizations with the chosen
ground point and its prescribed completion chart. The only open avoided at the
ground point for the two factors is the common denominator open supplied by
`PaperUnitPowerFactorization`; later bad-locus avoidance remains a separate
tilt choice. -/
theorem exists_prescribed_ground_point_chart_with_unit_powers
    [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B]
    (P : Ideal B) [P.IsPrime] (s q₀ q₁ : B)
    (hs : s = algebraMap R B (MvPolynomial.X none)) (hsP : s ∈ P)
    (hEt : Algebra.FormallyEtale R (Localization.AtPrime P))
    (e₀ e₁ : ℕ) (hOrders : 0 < e₀ ∧ e₀ < e₁)
    (u₀ u₁ : Localization.AtPrime P)
    (hu₀ : IsUnit u₀) (hu₁ : IsUnit u₁)
    (h₀ : algebraMap B (Localization.AtPrime P) q₀ =
      (algebraMap B (Localization.AtPrime P) s) ^ e₀ * u₀)
    (h₁ : algebraMap B (Localization.AtPrime P) q₁ =
      (algebraMap B (Localization.AtPrime P) s) ^ e₁ * u₁) :
    letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
    ∃ (fUnit fEtale : B) (M : Ideal B) (hM : M.IsMaximal),
      letI : M.IsMaximal := hM
      ∃ (eM : (B ⧸ M) ≃ₐ[k] k)
        (hEtM : Algebra.FormallyEtale R (Localization.AtPrime M))
        (v₀ v₁ : Localization.Away fUnit),
        fUnit ∉ P ∧ fUnit ∉ M ∧ P ≤ M ∧
        fEtale ∉ P ∧ fEtale ∉ M ∧
        Algebra.IsStandardEtale R (Localization.Away fEtale) ∧
        IsUnit v₀ ∧ IsUnit v₁ ∧
        algebraMap B (Localization.Away fUnit) q₀ =
          (algebraMap B (Localization.Away fUnit) s) ^ e₀ * v₀ ∧
        algebraMap B (Localization.Away fUnit) q₁ =
          (algebraMap B (Localization.Away fUnit) s) ^ e₁ * v₁ ∧
        (0 < e₀ ∧ e₀ < e₁) ∧
        (letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
         let chart := localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
         ∃ (U₀ U₁ : MvPowerSeries (Fin (d + 1)) k),
           IsUnit U₀ ∧ IsUnit U₁ ∧
           MvPowerSeries.constantCoeff U₀ ≠ 0 ∧
           MvPowerSeries.constantCoeff U₁ ≠ 0 ∧
           chart (algebraMap B (Localization.AtPrime M) s) =
             MvPowerSeries.X (0 : Fin (d + 1)) ∧
           (∀ i : Fin d,
             chart (algebraMap B (Localization.AtPrime M)
               (algebraMap R B (MvPolynomial.X (some i)))) =
               MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM (some i)) +
                 MvPowerSeries.X i.succ) ∧
           chart (algebraMap B (Localization.AtPrime M) q₀) =
             MvPowerSeries.X (0 : Fin (d + 1)) ^ e₀ * U₀ ∧
           chart (algebraMap B (Localization.AtPrime M) q₁) =
             MvPowerSeries.X (0 : Fin (d + 1)) ^ e₁ * U₁) := by
  classical
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  letI : Algebra.FiniteType R B :=
    Algebra.FiniteType.of_restrictScalars_finiteType k R B
  letI : Algebra.FinitePresentation R B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨_d₀, _n₀, _d₁, _n₁, fUnit, _hd₀, _hn₀, _hd₁, _hn₁, hfUnitP,
      _h₀cleared, _h₁cleared, v₀, v₁, hv₀, hv₁, hAway₀, hAway₁⟩ :=
    Stafford38.Geometry.PaperUnitPowerFactorization.exists_common_away_unit_power_factorizations
      P s q₀ q₁ e₀ e₁ u₀ u₁ hu₀ hu₁ h₀ h₁
  obtain ⟨fEtale, M, hM, hfEtaleP, hPM, hfEtaleM, hfUnitM, hStandard,
      hResidue, hEtM⟩ :=
    Stafford38.Geometry.PrescribedEtaleGroundPoint.exists_standardEtale_neighborhood_and_formallyEtale_ground_point_avoiding
      (k := k) (B := B) P fUnit hfUnitP hEt
  letI : M.IsMaximal := hM
  let eM : (B ⧸ M) ≃ₐ[k] k := Classical.choice hResidue
  let φ : Localization.Away fUnit →+* Localization.AtPrime M :=
    IsLocalization.Away.lift fUnit
      (IsLocalization.map_units (Localization.AtPrime M) (M := M.primeCompl)
        ⟨fUnit, hfUnitM⟩)
  let chart : Localization.AtPrime M →ₐ[k] MvPowerSeries (Fin (d + 1)) k :=
    localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM
  let ψ : Localization.Away fUnit →+* MvPowerSeries (Fin (d + 1)) k :=
    chart.toRingHom.comp φ
  have hφ : φ.comp (algebraMap B (Localization.Away fUnit)) =
      algebraMap B (Localization.AtPrime M) := by
    ext b
    simp [φ]
  have hψ : ψ.comp (algebraMap B (Localization.Away fUnit)) =
      chart.toRingHom.comp (algebraMap B (Localization.AtPrime M)) := by
    calc
      ψ.comp (algebraMap B (Localization.Away fUnit)) =
          chart.toRingHom.comp (φ.comp (algebraMap B (Localization.Away fUnit))) := rfl
      _ = chart.toRingHom.comp (algebraMap B (Localization.AtPrime M)) :=
        congrArg (fun f => chart.toRingHom.comp f) hφ
  have hsM : s ∈ M := hPM hsP
  have hBeta : residueCoordinates (σ := Option (Fin d)) M eM none = 0 := by
    unfold residueCoordinates
    rw [Ideal.Quotient.mkₐ_eq_mk]
    have hmk : Ideal.Quotient.mk M (algebraMap R B (MvPolynomial.X none)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [hs] using hsM)
    rw [hmk]
    simp
  have hAxis : chart (algebraMap B (Localization.AtPrime M) s) =
      MvPowerSeries.X (0 : Fin (d + 1)) := by
    simpa [hs, hBeta] using
      localToFinSuccPowerSeries_none (k := k) (B := B) (d := d) M eM
  have hCoordinates : ∀ i : Fin d,
      chart (algebraMap B (Localization.AtPrime M)
        (algebraMap R B (MvPolynomial.X (some i)))) =
      MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM (some i)) +
        MvPowerSeries.X i.succ := by
    intro i
    exact localToFinSuccPowerSeries_some (k := k) (B := B) (d := d) M eM i
  have hψs : ψ (algebraMap B (Localization.Away fUnit) s) =
      chart (algebraMap B (Localization.AtPrime M) s) := DFunLike.congr_fun hψ s
  let U₀ : MvPowerSeries (Fin (d + 1)) k := ψ v₀
  let U₁ : MvPowerSeries (Fin (d + 1)) k := ψ v₁
  have hU₀ : IsUnit U₀ := IsUnit.map ψ hv₀
  have hU₁ : IsUnit U₁ := IsUnit.map ψ hv₁
  have hConst₀ : MvPowerSeries.constantCoeff U₀ ≠ 0 := by
    have h := MvPowerSeries.isUnit_constantCoeff U₀ hU₀
    exact (isUnit_iff_ne_zero.mp h)
  have hConst₁ : MvPowerSeries.constantCoeff U₁ ≠ 0 := by
    have h := MvPowerSeries.isUnit_constantCoeff U₁ hU₁
    exact (isUnit_iff_ne_zero.mp h)
  have hPower₀ : chart (algebraMap B (Localization.AtPrime M) q₀) =
      MvPowerSeries.X (0 : Fin (d + 1)) ^ e₀ * U₀ := by
    calc
      chart (algebraMap B (Localization.AtPrime M) q₀) =
          ψ (algebraMap B (Localization.Away fUnit) q₀) := (DFunLike.congr_fun hψ q₀).symm
      _ = ψ ((algebraMap B (Localization.Away fUnit) s) ^ e₀ * v₀) :=
        congrArg ψ hAway₀
      _ = ψ (algebraMap B (Localization.Away fUnit) s) ^ e₀ * ψ v₀ := by
        simp only [map_mul, map_pow]
      _ = MvPowerSeries.X (0 : Fin (d + 1)) ^ e₀ * U₀ := by
        rw [hψs, hAxis]
  have hPower₁ : chart (algebraMap B (Localization.AtPrime M) q₁) =
      MvPowerSeries.X (0 : Fin (d + 1)) ^ e₁ * U₁ := by
    calc
      chart (algebraMap B (Localization.AtPrime M) q₁) =
          ψ (algebraMap B (Localization.Away fUnit) q₁) := (DFunLike.congr_fun hψ q₁).symm
      _ = ψ ((algebraMap B (Localization.Away fUnit) s) ^ e₁ * v₁) :=
        congrArg ψ hAway₁
      _ = ψ (algebraMap B (Localization.Away fUnit) s) ^ e₁ * ψ v₁ := by
        simp only [map_mul, map_pow]
      _ = MvPowerSeries.X (0 : Fin (d + 1)) ^ e₁ * U₁ := by
        rw [hψs, hAxis]
  refine ⟨fUnit, fEtale, M, hM, ?_⟩
  letI : M.IsMaximal := hM
  refine ⟨eM, hEtM, v₀, v₁, hfUnitP, hfUnitM, hPM, hfEtaleP, hfEtaleM,
    hStandard, hv₀, hv₁, hAway₀, hAway₁, hOrders, ?_⟩
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  exact ⟨U₀, U₁, hU₀, hU₁, hConst₀, hConst₁, hAxis, hCoordinates, hPower₀, hPower₁⟩

/-- Canonical reindexing of the genuine local completion preserves injectivity. -/
theorem localToFinSuccPowerSeries_injective
    (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) (Localization.AtPrime M)] :
    Function.Injective (localToFinSuccPowerSeries (k := k) (d := d) M eM) := by
  exact (MvPowerSeries.renameEquiv k (_root_.finSuccEquiv d).symm).injective.comp
    (PrescribedGroundPointPowerSeriesMap.localToPowerSeries_injective
      (σ := Option (Fin d)) M eM)

/-- A nonzero element of the actual domain remains nonzero in the canonical
renamed completion, even if its closed-point residue is zero. -/
theorem localToFinSuccPowerSeries_algebraMap_ne_zero
    [IsDomain B] (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) (Localization.AtPrime M)]
    (b : B) (hb : b ≠ 0) :
    localToFinSuccPowerSeries (k := k) (d := d) M eM
      (algebraMap B (Localization.AtPrime M) b) ≠ 0 := by
  have hinj := (localToFinSuccPowerSeries_injective (d := d) M eM).comp
    (IsLocalization.injective (Localization.AtPrime M)
      (Ideal.primeCompl_le_nonZeroDivisors M))
  intro hz
  exact hb (hinj (by simpa using hz))


end
end Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

#print axioms Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries_injective
#print axioms Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries_algebraMap_ne_zero
