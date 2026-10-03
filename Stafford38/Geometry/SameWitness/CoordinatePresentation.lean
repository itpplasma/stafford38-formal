module
public import Stafford38.Geometry.SameWitness.ChartSetup
public import Stafford38.Geometry.ActualChartValuationImage
public import Stafford38.Geometry.ActualOptionGroundPointCompletion
public import Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
public import Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
public import Stafford38.Geometry.ActualOptionColumnBinding
public import Stafford38.Geometry.AsymptoticChartArcAdapter

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.ActualChartValuationImage
open Stafford38.Geometry.ActualOptionGroundPointCompletion
open Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.ActualOptionColumnBinding
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.GeneralDivisorialVisibleFrame

universe u

/-- The finite coordinate presentation and the ground-point chart output
retained from one same-witness chart setup. -/
structure CoordinatePresentation
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w) where
  t : Type
  htFinite : Fintype t
  coeff : k →+* actualSelectedNormalization P w
  hcoeff : coeff = actualSelectedNormalizationCoefficients P w
  hBfinite : @Algebra.FiniteType k (actualSelectedNormalization P w)
    _ _ coeff.toAlgebra
  hPB : (actualSelectedNormalizationCenterPrime P w
    (chartGenericPointSubalgebra_le_valuationSubring hm P w)).IsPrime
  τ : Fin (@Fintype.card t htFinite) ≃ t
  rows : Fin (@Fintype.card t htFinite) ↪ Fin (m + 1)
  qRow : t → actualSelectedNormalization P w
  fOption : @AlgHom k (MvPolynomial (Option t) k)
    (actualSelectedNormalization P w) _ _ _ _ coeff.toAlgebra
  s : actualSelectedNormalization P w
  hsPB : s ∈ actualSelectedNormalizationCenterPrime P w
    (chartGenericPointSubalgebra_le_valuationSubring hm P w)
  hnone : fOption (MvPolynomial.X (R := k) none) = s
  hsome : ∀ z, fOption (MvPolynomial.X (R := k) (some z)) = qRow z
  fFin : @AlgHom k (MvPolynomial (Option (Fin (@Fintype.card t htFinite))) k)
    (actualSelectedNormalization P w) _ _ _ _ coeff.toAlgebra
  hrows : ∀ i, qRow (τ i) =
    actualNormalizedProjectiveColumnInIntegralClosure hm P w (rows i)
  hqchartB : actualNormalizedProjectiveColumnInIntegralClosure hm P w
    w.column.chart = 1
  hzero : actualNormalizedProjectiveColumnInIntegralClosure hm P w 0 =
    actualNormalizedProjectiveColumnInIntegralClosure hm P w 0
  haxis : actualNormalizedProjectiveColumnInIntegralClosure hm P w
      (Fin.succ (⟨0, hm⟩ : Fin m)) =
    actualNormalizedProjectiveColumnInIntegralClosure hm P w
      (Fin.succ (⟨0, hm⟩ : Fin m))
  hOutput : letI : IsLocalRing w.column.W.place.valuation.toSubring :=
      w.column.W.place.isDiscrete.toIsLocalRing
    @GroundPointChartOutput k (actualSelectedNormalization P w) t
      inferInstance inferInstance inferInstance coeff.toAlgebra inferInstance
      hBfinite htFinite
      (actualSelectedNormalizationCenterPrime P w
        (chartGenericPointSubalgebra_le_valuationSubring hm P w)) hPB
      fOption s
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0)
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w
        (Fin.succ (⟨0, hm⟩ : Fin m)))
      qRow τ w.differential.core.D.a
      (w.differential.core.D.a + w.differential.core.D.e)

/-- A same-witness chart setup and its retained ground-point output determine
the corresponding finite coordinate presentation. -/
theorem nonempty_coordinatePresentation
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (hpoint : actualSameWitnessGroundPointOutput hm P w) :
    Nonempty (CoordinatePresentation hm P w setup) := by
  classical
  let B := actualSelectedNormalization P w
  letI : IsLocalRing w.column.W.place.valuation.toSubring :=
    w.column.W.place.isDiscrete.toIsLocalRing
  unfold actualSameWitnessGroundPointOutput at hpoint
  dsimp only at hpoint
  rcases hpoint with ⟨hBfinite, t, htFinite, htBasis, index, hindex,
    hresidue, hPB', s, hs0, hsPB, u₀, u₁, hu₀, hu₁, hspan,
    hfactor₀, hfactor₁, hGroundPoint⟩
  letI : Fintype t := htFinite.fintype
  let τ : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let rows : Fin (Fintype.card t) ↪ Fin (m + 1) :=
    ⟨fun i => (chartAffineCoordinateEquiv (Fin.succ setup.j)
      (index (τ i))).1, by
      intro i i' hii
      change (chartAffineCoordinateEquiv (Fin.succ setup.j)
          (index (τ i))).1 = (chartAffineCoordinateEquiv (Fin.succ setup.j)
            (index (τ i'))).1 at hii
      have hcoord : chartAffineCoordinateEquiv (Fin.succ setup.j)
          (index (τ i)) = chartAffineCoordinateEquiv (Fin.succ setup.j)
            (index (τ i')) := Subtype.ext hii
      apply τ.injective
      exact hindex ((chartAffineCoordinateEquiv (Fin.succ setup.j)).injective hcoord)⟩
  let qRow : t → B := actualSelectedNormalizationRows P w index
  let coeff := actualSelectedNormalizationCoefficients P w
  let fOption : @AlgHom k (MvPolynomial (Option t) k) B _ _ _ _ coeff.toAlgebra :=
    @actualOptionMap k _ t B _ coeff.toAlgebra s qRow
  have hnone : fOption (MvPolynomial.X (R := k) none) = s :=
    @actualOptionMap_none k _ t B _ coeff.toAlgebra s qRow
  have hsome : ∀ z, fOption (MvPolynomial.X (R := k) (some z)) = qRow z := by
    intro z
    exact @actualOptionMap_some k _ t B _ coeff.toAlgebra s qRow z
  let fFin : @AlgHom k (MvPolynomial (Option (Fin (Fintype.card t))) k)
      B _ _ _ _ coeff.toAlgebra :=
    fOption.comp (MvPolynomial.renameEquiv k τ.optionCongr).toAlgHom
  have hrows : ∀ i : Fin (Fintype.card t), qRow (τ i) =
      actualNormalizedProjectiveColumnInIntegralClosure hm P w (rows i) := by
    intro i
    change actualNormalizedProjectiveColumnInIntegralClosure hm P w
        ((chartAffineCoordinateEquiv w.column.chart (index (τ i))).1) =
      actualNormalizedProjectiveColumnInIntegralClosure hm P w (rows i)
    congr 1
    exact congrArg (fun c =>
      (chartAffineCoordinateEquiv c (index (τ i))).1) setup.hchart
  have hqchartB : actualNormalizedProjectiveColumnInIntegralClosure hm P w
      w.column.chart = 1 := by
    obtain ⟨h, _, _⟩ := actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
    exact h
  have hzero : actualNormalizedProjectiveColumnInIntegralClosure hm P w 0 =
      actualNormalizedProjectiveColumnInIntegralClosure hm P w 0 := rfl
  have haxis : actualNormalizedProjectiveColumnInIntegralClosure hm P w
      (Fin.succ (⟨0, hm⟩ : Fin m)) =
    actualNormalizedProjectiveColumnInIntegralClosure hm P w
      (Fin.succ (⟨0, hm⟩ : Fin m)) := rfl
  rcases hGroundPoint with ⟨cert, hGroundPoint⟩
  have hOutput : @GroundPointChartOutput k B t inferInstance inferInstance
      inferInstance coeff.toAlgebra inferInstance hBfinite htFinite.fintype
      (actualSelectedNormalizationCenterPrime P w
        (chartGenericPointSubalgebra_le_valuationSubring hm P w)) hPB'
      fOption s
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0)
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w
        (Fin.succ (⟨0, hm⟩ : Fin m)))
      qRow τ w.differential.core.D.a
      (w.differential.core.D.a + w.differential.core.D.e) := by
    change @GroundPointChartOutput k B t inferInstance inferInstance
      inferInstance coeff.toAlgebra inferInstance hBfinite htFinite.fintype
      (actualSelectedNormalizationCenterPrime P w
        (chartGenericPointSubalgebra_le_valuationSubring hm P w)) hPB'
      (@actualOptionMap k _ t B _ coeff.toAlgebra s
        (actualSelectedNormalizationRows P w index)) s
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0)
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w
        (Fin.succ (⟨0, hm⟩ : Fin m)))
      (actualSelectedNormalizationRows P w index) ((Fintype.equivFin t).symm)
      w.differential.core.D.a
      (w.differential.core.D.a + w.differential.core.D.e)
    exact hGroundPoint
  exact ⟨{
    t := t
    htFinite := htFinite.fintype
    coeff := coeff
    hcoeff := rfl
    hBfinite := hBfinite
    hPB := hPB'
    τ := τ
    rows := rows
    qRow := qRow
    fOption := fOption
    s := s
    hsPB := hsPB
    hnone := hnone
    hsome := hsome
    fFin := fFin
    hrows := hrows
    hqchartB := hqchartB
    hzero := hzero
    haxis := haxis
    hOutput := hOutput
  }⟩

end Stafford38.Geometry.SameWitness

end
