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
  t : Type u
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
  hOutput :
    letI : Algebra (Stafford38.Geometry.AsymptoticDivisorExistence.CoordinateZeroLocalRing
      w.column.W.coefficientField)
      (Stafford38.Geometry.ComponentProjectiveClosure.ComponentFractionField P) :=
        w.column.W.ambientAlgebra
    letI : IsLocalRing w.column.W.place.valuation.toSubring :=
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

/-- Distinct retained rows remain distinct in the selected affine chart. -/
theorem chart_rows_injective
    {m d : ℕ} (j : Fin (m + 1)) {t : Type u}
    (index : t → Fin m) (hindex : Function.Injective index)
    (τ : Fin d ≃ t) :
    Function.Injective (fun i => (chartAffineCoordinateEquiv j (index (τ i))).1) := by
  intro i i' hii
  have hcoord : chartAffineCoordinateEquiv j (index (τ i)) =
      chartAffineCoordinateEquiv j (index (τ i')) := Subtype.ext hii
  exact τ.injective (hindex ((chartAffineCoordinateEquiv j).injective hcoord))

/-- Retained normalization rows agree with the selected chart's coordinates. -/
theorem selected_rows_chart_eq
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w) {t : Type u} (index : t → Fin m) (z : t) :
    actualSelectedNormalizationRows P w index z =
      actualNormalizedProjectiveColumnInIntegralClosure hm P w
        (chartAffineCoordinateEquiv (Fin.succ setup.j) (index z)).1 := by
  change actualNormalizedProjectiveColumnInIntegralClosure hm P w
      (chartAffineCoordinateEquiv w.column.chart (index z)).1 = _
  congr 1
  exact congrArg (fun c => (chartAffineCoordinateEquiv c (index z)).1) setup.hchart

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
  letI : IsLocalRing (
    letI : Algebra
      (Stafford38.Geometry.AsymptoticDivisorExistence.CoordinateZeroLocalRing
        w.column.W.coefficientField)
      (Stafford38.Geometry.ComponentProjectiveClosure.ComponentFractionField P) :=
        w.column.W.ambientAlgebra;
    w.column.W.place.valuation.toSubring) :=
    letI : Algebra
      (Stafford38.Geometry.AsymptoticDivisorExistence.CoordinateZeroLocalRing
        w.column.W.coefficientField)
      (Stafford38.Geometry.ComponentProjectiveClosure.ComponentFractionField P) :=
        w.column.W.ambientAlgebra
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
      (index (τ i))).1, chart_rows_injective (Fin.succ setup.j) index hindex τ⟩
  let qRow : t → B := actualSelectedNormalizationRows P w index
  let coeff := actualSelectedNormalizationCoefficients P w
  let fOption : @AlgHom k (MvPolynomial (Option t) k) B _ _ _ _ coeff.toAlgebra :=
    @actualOptionMap k _ t B _ coeff.toAlgebra s qRow
  let fFin : @AlgHom k (MvPolynomial (Option (Fin (Fintype.card t))) k)
      B _ _ _ _ coeff.toAlgebra :=
    @AlgHom.comp k (MvPolynomial (Option (Fin (Fintype.card t))) k)
      (MvPolynomial (Option t) k) B _ _ _ _ _ _ coeff.toAlgebra
      fOption (MvPolynomial.renameEquiv k τ.optionCongr).toAlgHom
  have hrows : ∀ i : Fin (Fintype.card t), qRow (τ i) =
      actualNormalizedProjectiveColumnInIntegralClosure hm P w (rows i) :=
    fun i => selected_rows_chart_eq hm P w setup index (τ i)
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
      (w.differential.core.D.a + w.differential.core.D.e) := hGroundPoint
  exact ⟨{
    t := t, htFinite := htFinite.fintype
    coeff := coeff, hcoeff := rfl, hBfinite := hBfinite
    hPB := hPB', τ := τ, rows := rows, qRow := qRow
    fOption := fOption, s := s, hsPB := hsPB
    hnone := @actualOptionMap_none k _ t B _ coeff.toAlgebra s qRow
    hsome := @actualOptionMap_some k _ t B _ coeff.toAlgebra s qRow
    fFin := fFin
    hrows := hrows
    hqchartB := (actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w).1
    hzero := rfl, haxis := rfl, hOutput := hOutput }⟩

end Stafford38.Geometry.SameWitness

end
