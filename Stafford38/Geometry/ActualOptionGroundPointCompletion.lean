module
public import Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualOptionGroundPointCompletion

/-- Formal étaleness is invariant under an algebra equivalence of source
rings, followed by composition through the equivalent source. -/
theorem formallyEtale_after_source_equiv
    {k R S T : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing T]
    [Algebra k R] [Algebra k S] [Algebra S T] [Algebra R S] [Algebra R T]
    [IsScalarTower R S T]
    (e : R ≃ₐ[k] S) (he : e.toRingEquiv.toFun = algebraMap R S)
    (hEt : Algebra.FormallyEtale S T) :
    Algebra.FormallyEtale R T := by
  letI : Algebra R R := Algebra.id R
  have eR : R ≃ₐ[R] S :=
    { toRingEquiv := e.toRingEquiv
      commutes' := by intro x; exact congrFun he x }
  have hBase : Algebra.FormallyEtale R S :=
    Algebra.FormallyEtale.of_equiv (R := R) (A := R) eR
  letI : Algebra.FormallyEtale R S := hBase
  exact Algebra.FormallyEtale.comp R S T

/-- Transfer formal etaleness across two algebra structures on the same
underlying target ring when their algebra maps agree. The identity ring
isomorphism is the induced algebra equivalence. -/
theorem formallyEtale_of_same_target_algebraMap
    {R T : Type*} [CommRing R] [CommRing T]
    (a₁ a₂ : Algebra R T)
    (hmap : @algebraMap R T _ _ a₁ = @algebraMap R T _ _ a₂)
    (hEt : @Algebra.FormallyEtale R T _ _ a₁) :
    @Algebra.FormallyEtale R T _ _ a₂ := by
  let e : @AlgEquiv R T T _ _ _ a₁ a₂ :=
    @AlgEquiv.ofRingEquiv R T T _ _ _ a₁ a₂ (RingEquiv.refl T) (by
      intro x
      exact congrArg (fun g : R →+* T => g x) hmap)
  exact @Algebra.FormallyEtale.of_equiv R T T _ _ a₁ _ a₂ hEt e

/-- The complete output of the prescribed closed-ground-point chart
construction for the given option-coordinate map and divisor parameter. -/
abbrev GroundPointChartOutput
    {k B σ : Type*} [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [IsDomain B] [Algebra.FiniteType k B] [Fintype σ]
    (P : Ideal B) [P.IsPrime]
    (fOption : MvPolynomial (Option σ) k →ₐ[k] B)
    (s q₀ q₁ : B) (qRow : σ → B)
    (τ : Fin (Fintype.card σ) ≃ σ)
    (e₀ e₁ : ℕ) : Prop :=
  let Rfin := MvPolynomial (Option (Fin (Fintype.card σ))) k
  let e : Rfin ≃ₐ[k] MvPolynomial (Option σ) k :=
    MvPolynomial.renameEquiv k τ.optionCongr
  let fFin : Rfin →ₐ[k] B := fOption.comp e.toAlgHom
  letI : Algebra Rfin B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k Rfin B := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact (fFin.commutes c).symm)
  ∃ (fUnit fEtale : B) (M : Ideal B) (hM : M.IsMaximal),
    letI : M.IsMaximal := hM
    letI : Algebra Rfin (Localization.AtPrime M) := inferInstance
    ∃ (eM : (B ⧸ M) ≃ₐ[k] k)
      (v₀ v₁ : Localization.Away fUnit)
      (chart : Localization.AtPrime M →ₐ[k]
        MvPowerSeries (Fin (Fintype.card σ + 1)) k)
      (U₀ U₁ : MvPowerSeries (Fin (Fintype.card σ + 1)) k),
      fUnit ∉ P ∧ fUnit ∉ M ∧ P ≤ M ∧
      fEtale ∉ P ∧ fEtale ∉ M ∧
      Algebra.IsStandardEtale Rfin (Localization.Away fEtale) ∧
      IsUnit v₀ ∧ IsUnit v₁ ∧
      algebraMap B (Localization.Away fUnit) q₀ =
        (algebraMap B (Localization.Away fUnit) s) ^ e₀ * v₀ ∧
      algebraMap B (Localization.Away fUnit) q₁ =
        (algebraMap B (Localization.Away fUnit) s) ^ e₁ * v₁ ∧
      (0 < e₀ ∧ e₀ < e₁) ∧
      IsUnit U₀ ∧ IsUnit U₁ ∧
      MvPowerSeries.constantCoeff U₀ ≠ 0 ∧
      MvPowerSeries.constantCoeff U₁ ≠ 0 ∧
      chart (algebraMap B (Localization.AtPrime M) s) =
        MvPowerSeries.X (0 : Fin (Fintype.card σ + 1)) ∧
      (∀ z : σ, chart (algebraMap B (Localization.AtPrime M) (qRow z)) =
        MvPowerSeries.C
          (@Stafford38.Geometry.PrescribedAffineResidueCompletion.residueCoordinates
            k (Option (Fin (Fintype.card σ))) B inferInstance inferInstance inferInstance
            fFin.toRingHom.toAlgebra M eM (some (τ.symm z))) +
        MvPowerSeries.X (τ.symm z).succ) ∧
      chart (algebraMap B (Localization.AtPrime M) q₀) =
        MvPowerSeries.X (0 : Fin (Fintype.card σ + 1)) ^ e₀ * U₀ ∧
      chart (algebraMap B (Localization.AtPrime M) q₁) =
        MvPowerSeries.X (0 : Fin (Fintype.card σ + 1)) ^ e₁ * U₁ ∧
      ∃ (hEtM : Algebra.FormallyEtale Rfin (Localization.AtPrime M)),
        chart = @Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
          k B (Fintype.card σ) inferInstance inferInstance inferInstance
          (inferInstance : Algebra Rfin B) (inferInstance : IsScalarTower k Rfin B)
          (Algebra.EssFiniteType.of_comp k Rfin B) M hM eM hEtM

/-- Starting from the actual Option-coordinate map and its specified divisor
parameter, obtain the existing closed-ground-point completion chart. Every
selected row identity is transported through the same polynomial rename. -/
theorem exists_groundPoint_chart_from_option_map
    {k B σ : Type*} [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [IsDomain B] [Algebra.FiniteType k B] [Fintype σ]
    (P : Ideal B) [P.IsPrime]
    (fOption : MvPolynomial (Option σ) k →ₐ[k] B)
    (s q₀ q₁ : B) (qRow : σ → B)
    (hnone : fOption (MvPolynomial.X none) = s)
    (hsP : s ∈ P)
    (hsome : ∀ z, fOption (MvPolynomial.X (some z)) = qRow z)
    (τ : Fin (Fintype.card σ) ≃ σ)
    (hEt :
      let Rσ := MvPolynomial (Option σ) k
      letI : Algebra Rσ B := fOption.toRingHom.toAlgebra
      letI : IsScalarTower k Rσ B := IsScalarTower.of_algebraMap_eq' (by
        ext c
        exact (fOption.commutes c).symm)
      letI : Algebra Rσ (Localization.AtPrime P) := inferInstance
      Algebra.FormallyEtale Rσ (Localization.AtPrime P))
    (e₀ e₁ : ℕ) (hOrders : 0 < e₀ ∧ e₀ < e₁)
    (u₀ u₁ : Localization.AtPrime P) (hu₀ : IsUnit u₀) (hu₁ : IsUnit u₁)
    (h₀ : algebraMap B (Localization.AtPrime P) q₀ =
      (algebraMap B (Localization.AtPrime P) s) ^ e₀ * u₀)
    (h₁ : algebraMap B (Localization.AtPrime P) q₁ =
      (algebraMap B (Localization.AtPrime P) s) ^ e₁ * u₁) :
    GroundPointChartOutput P fOption s q₀ q₁ qRow τ e₀ e₁ := by
  classical
  let Rσ := MvPolynomial (Option σ) k
  let Rfin := MvPolynomial (Option (Fin (Fintype.card σ))) k
  let e : Rfin ≃ₐ[k] Rσ := MvPolynomial.renameEquiv k τ.optionCongr
  letI : Algebra Rfin Rσ := e.toRingEquiv.toRingHom.toAlgebra
  letI : Algebra Rσ B := fOption.toRingHom.toAlgebra
  letI : IsScalarTower k Rσ B := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact (fOption.commutes c).symm)
  let fFin : Rfin →ₐ[k] B := fOption.comp e.toAlgHom
  letI : Algebra Rfin B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k Rfin B := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact (fFin.commutes c).symm)
  let algDefault : Algebra Rσ (Localization.AtPrime P) := inferInstance
  have hmapFin : algebraMap Rfin B =
      (algebraMap Rσ B).comp (algebraMap Rfin Rσ) := by
    change fFin.toRingHom = fOption.toRingHom.comp e.toRingHom
    rfl
  letI : IsScalarTower Rfin Rσ B := IsScalarTower.of_algebraMap_eq' hmapFin
  letI : Algebra Rσ (Localization.AtPrime P) := algDefault
  letI : Algebra.FormallyEtale Rσ (Localization.AtPrime P) := hEt
  have hmapFinT : algebraMap Rfin (Localization.AtPrime P) =
      (algebraMap Rσ (Localization.AtPrime P)).comp (algebraMap Rfin Rσ) := by
    calc
      algebraMap Rfin (Localization.AtPrime P) =
          (algebraMap B (Localization.AtPrime P)).comp (algebraMap Rfin B) :=
        IsScalarTower.algebraMap_eq Rfin B (Localization.AtPrime P)
      _ = (algebraMap B (Localization.AtPrime P)).comp
          ((algebraMap Rσ B).comp (algebraMap Rfin Rσ)) := by rw [hmapFin]
      _ = ((algebraMap B (Localization.AtPrime P)).comp (algebraMap Rσ B)).comp
          (algebraMap Rfin Rσ) := by rw [RingHom.comp_assoc]
      _ = (algebraMap Rσ (Localization.AtPrime P)).comp (algebraMap Rfin Rσ) :=
        congrArg (fun g => g.comp (algebraMap Rfin Rσ))
          (IsScalarTower.algebraMap_eq Rσ B (Localization.AtPrime P))
  letI : IsScalarTower Rfin Rσ (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq' hmapFinT
  have hEtFin : Algebra.FormallyEtale Rfin (Localization.AtPrime P) :=
    formallyEtale_after_source_equiv e (by ext p; rfl) hEt
  letI : Algebra.EssFiniteType Rfin B := Algebra.EssFiniteType.of_comp k Rfin B
  have hnoneFin : s = algebraMap Rfin B (MvPolynomial.X none) := by
    change s = fFin (MvPolynomial.X none)
    simp [fFin, e, MvPolynomial.renameEquiv, MvPolynomial.rename_X, hnone]
  have hrowsFin (i : Fin (Fintype.card σ)) :
      algebraMap Rfin B (MvPolynomial.X (some i)) = qRow (τ i) := by
    change fFin (MvPolynomial.X (some i)) = qRow (τ i)
    simp [fFin, e, MvPolynomial.renameEquiv, MvPolynomial.rename_X, hsome]
  obtain ⟨fUnit, fEtale, M, hM, eM, hEtM, v₀, v₁,
      hfUnitP, hfUnitM, hPM, hfEtaleP, hfEtaleM, hStandard,
      hv₀, hv₁, hAway₀, hAway₁, hOrders', hChart⟩ :=
    Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.exists_prescribed_ground_point_chart_with_unit_powers
      (k := k) (B := B) (d := Fintype.card σ) P s q₀ q₁ hnoneFin hsP hEtFin
      e₀ e₁ hOrders u₀ u₁ hu₀ hu₁ h₀ h₁
  letI : M.IsMaximal := hM
  letI : Algebra.FormallyEtale Rfin (Localization.AtPrime M) := hEtM
  let chart := Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
    (k := k) (B := B) (d := Fintype.card σ) M eM
  obtain ⟨U₀, U₁, hU₀, hU₁, hcc₀, hcc₁, hsChart, hrows, hq₀Chart, hq₁Chart⟩ := hChart
  have hrowEq (z : σ) : qRow z =
      algebraMap Rfin B (MvPolynomial.X (some (τ.symm z))) := by
    simpa using (hrowsFin (τ.symm z)).symm
  have hqRow (z : σ) : chart (algebraMap B (Localization.AtPrime M) (qRow z)) =
      MvPowerSeries.C
        (Stafford38.Geometry.PrescribedAffineResidueCompletion.residueCoordinates
          (σ := Option (Fin (Fintype.card σ))) M eM (some (τ.symm z))) +
        MvPowerSeries.X (τ.symm z).succ := by
    rw [hrowEq z]
    exact hrows (τ.symm z)
  exact ⟨fUnit, fEtale, M, hM, eM, v₀, v₁, chart, U₀, U₁,
    hfUnitP, hfUnitM, hPM, hfEtaleP, hfEtaleM, hStandard,
    hv₀, hv₁, hAway₀, hAway₁, hOrders', hU₀, hU₁, hcc₀, hcc₁,
    hsChart, hqRow, hq₀Chart, hq₁Chart, hEtM, rfl⟩

end Stafford38.Geometry.ActualOptionGroundPointCompletion
