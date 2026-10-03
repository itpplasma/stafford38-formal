module
public import Stafford38.Geometry.AsymptoticChartArcAdapter
public import Stafford38.Geometry.ComponentProjectiveChartKernel
public import Stafford38.Geometry.ComponentProjectiveClosure
public import Stafford38.Geometry.ComponentFunctionFieldBoundary
public import Stafford38.Geometry.AffineComponentCoordinateSplit
public import Stafford38.Geometry.ComponentProjectiveChartFactorization

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace Stafford38.Geometry.ProjectiveChartSameFieldOverlap

noncomputable section
universe u

open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary

variable {k : Type u} [Field k] {m : ℕ}

abbrev OriginalAffineChartQuotient (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :=
  MvPolynomial (Fin m) k ⧸ P.asIdeal

abbrev SelectedAffineChart (j : Fin m) := Fin.succ j

abbrev SelectedAffineCoordinateEquiv (j : Fin m) :=
  AsymptoticChartArcAdapter.chartAffineCoordinateEquiv (Fin.succ j)

/-- The local affine index for the projective coordinate `X₀`, derived from
the canonical selected-chart coordinate equivalence. -/
abbrev selectedAffineChartOrigin (j : Fin m) : Fin m :=
  (SelectedAffineCoordinateEquiv j).symm
    ⟨0, by simpa [eq_comm] using Fin.succ_ne_zero j⟩

private theorem selectedAffineChartOrigin_coordinate (j : Fin m) :
    ((SelectedAffineCoordinateEquiv j) (selectedAffineChartOrigin j)).1 = 0 := by
  exact congrArg Subtype.val
    ((SelectedAffineCoordinateEquiv j).apply_symm_apply
      ⟨0, by simpa [eq_comm] using Fin.succ_ne_zero j⟩)

abbrev SelectedAffineChartIdeal (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :=
  componentChartEquationIdeal P (Fin.succ j) (SelectedAffineCoordinateEquiv j)

abbrev SelectedAffineChartQuotient (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :=
  MvPolynomial (Fin m) k ⧸ SelectedAffineChartIdeal (k := k) P j

private def selectedPoint
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) : Fin m → ComponentFractionField P :=
  chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)

private theorem selectedChart_nonzero
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    componentProjectivePoint P (Fin.succ j) ≠ 0 := by
    simpa [componentProjectivePoint] using hxj

private theorem selectedPoint_zero_coordinate
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :
    selectedPoint P j (selectedAffineChartOrigin j) =
      (componentCoordinate P j)⁻¹ := by
  have hidx : ((SelectedAffineCoordinateEquiv j)
      (selectedAffineChartOrigin j)).1 = 0 :=
    selectedAffineChartOrigin_coordinate j
  change componentProjectivePoint P
      ((SelectedAffineCoordinateEquiv j)
        (selectedAffineChartOrigin j)).1 /
      componentProjectivePoint P (Fin.succ j) = _
  rw [hidx]
  simp [componentProjectivePoint]

private theorem selectedPoint_original_coordinate
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j i : Fin m)
    (hij : i ≠ j) :
    selectedPoint P j
      ((SelectedAffineCoordinateEquiv j).symm
        ⟨i.succ, by simpa using hij⟩) =
      componentCoordinate P i / componentCoordinate P j := by
  have hidx : ((SelectedAffineCoordinateEquiv j)
      ((SelectedAffineCoordinateEquiv j).symm
        ⟨i.succ, by simpa using hij⟩)).1 = i.succ := by
    exact congrArg Subtype.val
      ((SelectedAffineCoordinateEquiv j).apply_symm_apply
        ⟨i.succ, by simpa using hij⟩)
  change componentProjectivePoint P
      ((SelectedAffineCoordinateEquiv j)
        ((SelectedAffineCoordinateEquiv j).symm
          ⟨i.succ, by simpa using hij⟩)).1 /
      componentProjectivePoint P (Fin.succ j) = _
  rw [hidx]
  simp [componentProjectivePoint]

private abbrev selectedQuotientToField
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    SelectedAffineChartQuotient (k := k) P j →ₐ[k] ComponentFractionField P :=
  ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap
    P (Fin.succ j) (SelectedAffineCoordinateEquiv j)
    (selectedChart_nonzero P j hxj)

private theorem selectedQuotientToField_mk
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) (f : MvPolynomial (Fin m) k) :
    selectedQuotientToField P j hxj (Ideal.Quotient.mk _ f) =
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (selectedPoint P j) f := by
  simpa [selectedQuotientToField, selectedPoint, SelectedAffineChartIdeal,
    SelectedAffineChartQuotient] using
      ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap_mk
        P (Fin.succ j) (SelectedAffineCoordinateEquiv j)
        (selectedChart_nonzero P j hxj) f

private theorem away_lift_injective
    {R : Type u} [CommRing R] [IsDomain R] {r : R} (hr : r ≠ 0)
    {F : Type u} [Field F] (g : R →+* F) (hg : Function.Injective g)
    (hunit : IsUnit (g r)) :
    Function.Injective (IsLocalization.Away.lift (g := g) r hunit :
      Localization.Away r →+* F) := by
  have hbase : Function.Injective (algebraMap R (Localization.Away r)) := by
    letI : Algebra R (Localization.Away r) := inferInstance
    letI : IsLocalization (Submonoid.powers r) (Localization.Away r) :=
      Localization.isLocalization
    apply IsLocalization.injective (M := Submonoid.powers r)
      (Localization.Away r)
    rw [Submonoid.powers_le]
    exact (mem_nonZeroDivisors_iff_ne_zero).2 hr
  letI : Algebra R (Localization.Away r) := inferInstance
  letI : IsLocalization (Submonoid.powers r) (Localization.Away r) :=
    Localization.isLocalization
  let f : Localization.Away r →+* F := IsLocalization.Away.lift (g := g) r hunit
  have hf := IsLocalization.injective_iff_map_algebraMap_eq
    (M := Submonoid.powers r) (S := Localization.Away r) f
  change Function.Injective f
  rw [hf]
  intro x y
  rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
  constructor
  · intro h
    have hxy := hbase h
    subst y
    rfl
  · intro h
    have hxy := hg h
    subst y
    rfl

private theorem selectedIdeal_isPrime
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (SelectedAffineChartIdeal (k := k) P j).IsPrime := by
  change (componentChartEquationIdeal P (Fin.succ j) (SelectedAffineCoordinateEquiv j)).IsPrime
  rw [componentChartEquationIdeal_eq_genericEvalKer P (Fin.succ j)
    (SelectedAffineCoordinateEquiv j) (selectedChart_nonzero P j hxj)]
  exact RingHom.ker_isPrime _

def originalAffineChartDenominator
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :
    OriginalAffineChartQuotient (k := k) P :=
  Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j)

def selectedAffineChartDenominator
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :
    SelectedAffineChartQuotient (k := k) P j :=
  Ideal.Quotient.mk (SelectedAffineChartIdeal (k := k) P j)
    (MvPolynomial.X (selectedAffineChartOrigin j))

private theorem originalDenominator_map
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :
    algebraMap (OriginalAffineChartQuotient (k := k) P) (ComponentFractionField P)
      (originalAffineChartDenominator P j) = componentCoordinate P j := by
  rfl

private theorem originalVariable_map
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m) :
    algebraMap (OriginalAffineChartQuotient (k := k) P) (ComponentFractionField P)
      (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) = componentCoordinate P i := by
  rfl

private theorem selectedDenominator_map
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    selectedQuotientToField P j hxj (selectedAffineChartDenominator P j) =
      (componentCoordinate P j)⁻¹ := by
  change selectedQuotientToField P j hxj
    (Ideal.Quotient.mk (SelectedAffineChartIdeal (k := k) P j)
      (MvPolynomial.X (selectedAffineChartOrigin j))) = _
  rw [selectedQuotientToField_mk]
  rw [MvPolynomial.eval₂_X, selectedPoint_zero_coordinate]

def originalAffineChartToFunctionField
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    Localization.Away (originalAffineChartDenominator P j) →+* ComponentFractionField P :=
  IsLocalization.Away.lift
    (g := algebraMap (OriginalAffineChartQuotient (k := k) P) (ComponentFractionField P))
    (originalAffineChartDenominator P j)
    (isUnit_iff_ne_zero.mpr (by simpa [originalDenominator_map] using hxj))

def selectedAffineChartToFunctionField
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    Localization.Away (selectedAffineChartDenominator P j) →+* ComponentFractionField P := by
  letI : (SelectedAffineChartIdeal (k := k) P j).IsPrime := selectedIdeal_isPrime P j hxj
  letI : IsDomain (SelectedAffineChartQuotient (k := k) P j) :=
    Ideal.Quotient.isDomain (SelectedAffineChartIdeal (k := k) P j)
  exact IsLocalization.Away.lift (g := (selectedQuotientToField P j hxj).toRingHom)
    (selectedAffineChartDenominator P j)
    (isUnit_iff_ne_zero.mpr (by
      change selectedQuotientToField P j hxj (selectedAffineChartDenominator P j) ≠ 0
      rw [selectedDenominator_map P j hxj]
      exact inv_ne_zero hxj))

private theorem originalLocalizationToField_injective
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    Function.Injective (originalAffineChartToFunctionField P j hxj) := by
  letI : IsDomain (OriginalAffineChartQuotient (k := k) P) := Ideal.Quotient.isDomain P.asIdeal
  have hg : Function.Injective
      (algebraMap (OriginalAffineChartQuotient (k := k) P) (ComponentFractionField P)) :=
    IsFractionRing.injective _ _
  exact away_lift_injective
    (r := originalAffineChartDenominator P j) (by
      intro hzero
      have := congrArg (algebraMap (OriginalAffineChartQuotient (k := k) P)
        (ComponentFractionField P)) hzero
      rw [originalDenominator_map] at this
      exact hxj (by simpa using this))
    _ hg (isUnit_iff_ne_zero.mpr (by
      simpa [originalDenominator_map] using hxj))

private theorem selectedLocalizationToField_injective
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    Function.Injective (selectedAffineChartToFunctionField P j hxj) := by
  letI : (SelectedAffineChartIdeal (k := k) P j).IsPrime := selectedIdeal_isPrime P j hxj
  letI : IsDomain (SelectedAffineChartQuotient (k := k) P j) :=
    Ideal.Quotient.isDomain (SelectedAffineChartIdeal (k := k) P j)
  have hg : Function.Injective (selectedQuotientToField P j hxj) := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hmem : x - y ∈ SelectedAffineChartIdeal (k := k) P j := by
      change x - y ∈ componentChartEquationIdeal P (Fin.succ j) (SelectedAffineCoordinateEquiv j)
      rw [componentChartEquationIdeal_eq_genericEvalKer P (Fin.succ j)
        (SelectedAffineCoordinateEquiv j) (selectedChart_nonzero P j hxj)]
      apply RingHom.mem_ker.mpr
      change (MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
        (selectedPoint P j)) (x - y) = 0
      have hxy' : MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
          (selectedPoint P j) x =
        MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
          (selectedPoint P j) y := by
        simpa [selectedQuotientToField_mk] using hxy
      change (MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
        (selectedPoint P j)) x =
        (MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
          (selectedPoint P j)) y at hxy'
      rw [map_sub, hxy', sub_self]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).2 hmem
  exact away_lift_injective (r := selectedAffineChartDenominator P j) (by
    intro hzero
    have := congrArg (selectedQuotientToField P j hxj) hzero
    change selectedQuotientToField P j hxj (selectedAffineChartDenominator P j) = 0 at this
    rw [selectedDenominator_map P j hxj] at this
    exact hxj (inv_eq_zero.mp this))
    _ hg (isUnit_iff_ne_zero.mpr (by
      change selectedQuotientToField P j hxj (selectedAffineChartDenominator P j) ≠ 0
      rw [selectedDenominator_map P j hxj]
      exact inv_ne_zero hxj))

abbrev OriginalAffineChartLocalization
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :=
  Localization.Away (originalAffineChartDenominator P j)

abbrev SelectedAffineChartLocalization
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :=
  Localization.Away (selectedAffineChartDenominator P j)

def selectedAffineChartVariableClass
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j i : Fin m) (hij : i ≠ j) :
    SelectedAffineChartQuotient (k := k) P j :=
  Ideal.Quotient.mk (SelectedAffineChartIdeal (k := k) P j)
    (MvPolynomial.X ((SelectedAffineCoordinateEquiv j).symm ⟨i.succ, by simpa using hij⟩))

private theorem selectedVariable_map
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j i : Fin m)
    (hij : i ≠ j) (hxj : componentCoordinate P j ≠ 0) :
    selectedQuotientToField P j hxj (selectedAffineChartVariableClass P j i hij) =
      componentCoordinate P i / componentCoordinate P j := by
  change selectedQuotientToField P j hxj
    (Ideal.Quotient.mk (SelectedAffineChartIdeal (k := k) P j)
      (MvPolynomial.X ((SelectedAffineCoordinateEquiv j).symm ⟨i.succ, by simpa using hij⟩))) = _
  rw [selectedQuotientToField_mk]
  rw [MvPolynomial.eval₂_X]
  rw [selectedPoint_original_coordinate P j i hij]

private def forwardPolynomialMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :
    MvPolynomial (Fin m) k →ₐ[k] SelectedAffineChartLocalization (k := k) P j :=
  MvPolynomial.aeval (fun i =>
    if hij : i = j then
      IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)
    else
      algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j) (selectedAffineChartVariableClass P j i hij) *
        IsLocalization.Away.invSelf (selectedAffineChartDenominator P j))

private def backwardPolynomialMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :
    MvPolynomial (Fin m) k →ₐ[k] OriginalAffineChartLocalization (k := k) P j :=
  MvPolynomial.aeval (fun a =>
    if ha : a = selectedAffineChartOrigin j then
      IsLocalization.Away.invSelf (originalAffineChartDenominator P j)
    else
      algebraMap (OriginalAffineChartQuotient (k := k) P)
        (OriginalAffineChartLocalization (k := k) P j)
        (Ideal.Quotient.mk P.asIdeal
          (MvPolynomial.X (Fin.cases j (fun i => i) ((SelectedAffineCoordinateEquiv j) a).1))) *
        IsLocalization.Away.invSelf (originalAffineChartDenominator P j))

def originalAffineChartToFunctionField'
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    OriginalAffineChartLocalization (k := k) P j →+* ComponentFractionField P :=
  originalAffineChartToFunctionField P j hxj

def selectedAffineChartToFunctionField'
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    SelectedAffineChartLocalization (k := k) P j →+* ComponentFractionField P :=
  selectedAffineChartToFunctionField P j hxj

private theorem originalLocalizationToField_base
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) (a : OriginalAffineChartQuotient (k := k) P) :
    originalAffineChartToFunctionField P j hxj
      (algebraMap (OriginalAffineChartQuotient (k := k) P) (OriginalAffineChartLocalization (k := k) P j) a) =
        algebraMap (OriginalAffineChartQuotient (k := k) P) (ComponentFractionField P) a := by
  simp [originalAffineChartToFunctionField]

private theorem selectedLocalizationToField_base
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) (a : SelectedAffineChartQuotient (k := k) P j) :
    selectedAffineChartToFunctionField P j hxj
      (algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j) a) = selectedQuotientToField P j hxj a := by
  simp [selectedAffineChartToFunctionField]

private theorem originalLocalizationToField_invSelf
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    originalAffineChartToFunctionField P j hxj
      (IsLocalization.Away.invSelf (originalAffineChartDenominator P j)) =
        (componentCoordinate P j)⁻¹ := by
  have hmul := congrArg (originalAffineChartToFunctionField P j hxj)
    (IsLocalization.Away.mul_invSelf (originalAffineChartDenominator P j))
  rw [map_mul, originalLocalizationToField_base P j hxj,
    originalDenominator_map P j, map_one] at hmul
  apply mul_left_cancel₀ hxj
  calc
    componentCoordinate P j *
        originalAffineChartToFunctionField P j hxj
          (IsLocalization.Away.invSelf (originalAffineChartDenominator P j)) = 1 := hmul
    _ = componentCoordinate P j * (componentCoordinate P j)⁻¹ :=
      (mul_inv_cancel₀ hxj).symm

private theorem selectedLocalizationToField_invSelf
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    selectedAffineChartToFunctionField P j hxj
      (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) = componentCoordinate P j := by
  have hmul := congrArg (selectedAffineChartToFunctionField P j hxj)
    (IsLocalization.Away.mul_invSelf (selectedAffineChartDenominator P j))
  rw [map_mul, selectedLocalizationToField_base P j hxj,
    selectedDenominator_map P j hxj, map_one] at hmul
  apply mul_left_cancel₀ (inv_ne_zero hxj)
  calc
    (componentCoordinate P j)⁻¹ *
        selectedAffineChartToFunctionField P j hxj
          (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) = 1 := hmul
    _ = (componentCoordinate P j)⁻¹ * componentCoordinate P j :=
      (inv_mul_cancel₀ hxj).symm

private theorem forwardPolynomialMap_X_toField
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j i : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    selectedAffineChartToFunctionField P j hxj
      (forwardPolynomialMap P j (MvPolynomial.X i)) = componentCoordinate P i := by
  change selectedAffineChartToFunctionField P j hxj
    (MvPolynomial.aeval (fun i => if hij : i = j then
      IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) else
      algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j) (selectedAffineChartVariableClass P j i hij) *
        IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]
  by_cases hij : i = j
  · subst i
    simpa [selectedLocalizationToField_invSelf P j hxj]
  · simp only [dif_neg hij]
    rw [map_mul, selectedLocalizationToField_base P j hxj,
      selectedVariable_map P j i hij hxj,
      selectedLocalizationToField_invSelf P j hxj]
    field_simp [hxj]

private theorem backwardPolynomialMap_X_toField
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j a : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    originalAffineChartToFunctionField P j hxj
      (backwardPolynomialMap P j (MvPolynomial.X a)) = selectedPoint P j a := by
  change originalAffineChartToFunctionField P j hxj
    (MvPolynomial.aeval (fun a => if ha : a = selectedAffineChartOrigin j then
      IsLocalization.Away.invSelf (originalAffineChartDenominator P j) else
      algebraMap (OriginalAffineChartQuotient (k := k) P)
        (OriginalAffineChartLocalization (k := k) P j)
        (Ideal.Quotient.mk P.asIdeal
          (MvPolynomial.X (Fin.cases j (fun i => i) ((SelectedAffineCoordinateEquiv j) a).1))) *
        IsLocalization.Away.invSelf (originalAffineChartDenominator P j)) (MvPolynomial.X a)) = _
  rw [MvPolynomial.aeval_X]
  by_cases ha : a = selectedAffineChartOrigin j
  · subst a
    rw [selectedPoint_zero_coordinate]
    simp [backwardPolynomialMap, originalLocalizationToField_invSelf P j hxj]
  · have hcoord : ((SelectedAffineCoordinateEquiv j) a).1 ≠ 0 := by
      intro hzero
      apply ha
      apply (SelectedAffineCoordinateEquiv j).injective
      apply Subtype.ext
      exact hzero.trans (selectedAffineChartOrigin_coordinate j).symm
    rcases Fin.eq_zero_or_eq_succ ((SelectedAffineCoordinateEquiv j) a).1 with hzero | ⟨i, hi⟩
    · exact False.elim (hcoord hzero)
    · have hidx : ((SelectedAffineCoordinateEquiv j) a).1 = i.succ := hi
      have hij : i ≠ j := by
        intro h
        apply ((SelectedAffineCoordinateEquiv j) a).property
        simpa [hidx, h]
      have hback :
          originalAffineChartToFunctionField P j hxj
            (algebraMap (OriginalAffineChartQuotient (k := k) P)
              (OriginalAffineChartLocalization (k := k) P j)
              (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) *
                IsLocalization.Away.invSelf (originalAffineChartDenominator P j)) =
            componentCoordinate P i / componentCoordinate P j := by
        rw [map_mul, originalLocalizationToField_base P j hxj,
          originalLocalizationToField_invSelf P j hxj]
        rw [originalVariable_map]
        rfl
      simp only [dif_neg ha]
      rw [hidx]
      have hfin : Fin.cases j (fun i => i) i.succ = i := rfl
      rw [hfin, map_mul, originalLocalizationToField_base P j hxj,
        originalVariable_map, originalLocalizationToField_invSelf P j hxj]
      simpa [selectedPoint, chartGenericPoint, componentProjectivePoint,
        hidx, hij, div_eq_mul_inv] using hback

private theorem forwardPolynomialMap_toField
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (selectedAffineChartToFunctionField P j hxj).comp
        (forwardPolynomialMap P j).toRingHom = componentAffineGenericPointMap P := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change selectedAffineChartToFunctionField P j hxj
      (MvPolynomial.aeval (fun i => if hij : i = j then
        IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) else
        algebraMap (SelectedAffineChartQuotient (k := k) P j)
          (SelectedAffineChartLocalization (k := k) P j) (selectedAffineChartVariableClass P j i hij) *
          IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) (MvPolynomial.C c)) =
      componentAffineGenericPointMap P (MvPolynomial.C c)
    rw [MvPolynomial.aeval_C]
    rw [componentAffineGenericPointMap_eq_eval₂]
    simp only [MvPolynomial.eval₂_C]
    rw [IsScalarTower.algebraMap_apply k (SelectedAffineChartQuotient (k := k) P j)
      (SelectedAffineChartLocalization (k := k) P j) c]
    rw [selectedLocalizationToField_base P j hxj]
    exact (selectedQuotientToField P j hxj).commutes c
  · intro i
    exact forwardPolynomialMap_X_toField P j i hxj

private theorem backwardPolynomialMap_toField
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (originalAffineChartToFunctionField P j hxj).comp
        (backwardPolynomialMap P j).toRingHom =
      MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P)) (selectedPoint P j) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change originalAffineChartToFunctionField P j hxj
      (MvPolynomial.aeval (fun a => if ha : a = selectedAffineChartOrigin j then
        IsLocalization.Away.invSelf (originalAffineChartDenominator P j) else
        algebraMap (OriginalAffineChartQuotient (k := k) P)
          (OriginalAffineChartLocalization (k := k) P j)
          (Ideal.Quotient.mk P.asIdeal
            (MvPolynomial.X (Fin.cases j (fun i => i) ((SelectedAffineCoordinateEquiv j) a).1))) *
          IsLocalization.Away.invSelf (originalAffineChartDenominator P j)) (MvPolynomial.C c)) =
      (MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
        (selectedPoint P j)) (MvPolynomial.C c)
    rw [MvPolynomial.aeval_C]
    change originalAffineChartToFunctionField P j hxj
      (algebraMap k (OriginalAffineChartLocalization (k := k) P j) c) =
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (selectedPoint P j) (MvPolynomial.C c)
    rw [MvPolynomial.eval₂_C]
    change originalAffineChartToFunctionField P j hxj
      (algebraMap k (OriginalAffineChartLocalization (k := k) P j) c) =
        algebraMap k (ComponentFractionField P) c
    rw [IsScalarTower.algebraMap_apply k (OriginalAffineChartQuotient (k := k) P)
      (OriginalAffineChartLocalization (k := k) P j) c]
    rw [originalLocalizationToField_base P j hxj]
    rfl
  · intro a
    simpa [MvPolynomial.eval₂_X] using backwardPolynomialMap_X_toField P j a hxj

private def forwardQuotientMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    OriginalAffineChartQuotient (k := k) P →ₐ[k] SelectedAffineChartLocalization (k := k) P j := by
  let f := forwardPolynomialMap P j
  refine Ideal.Quotient.liftₐ P.asIdeal f ?_
  intro a ha
  have hcomp := forwardPolynomialMap_toField P j hxj
  have heval : selectedAffineChartToFunctionField P j hxj (f a) = 0 := by
    calc
      selectedAffineChartToFunctionField P j hxj (f a) = componentAffineGenericPointMap P a :=
        congrArg (fun g : MvPolynomial (Fin m) k →+* ComponentFractionField P => g a) hcomp
      _ = 0 := componentAffineGenericPointMap_eq_zero_of_mem P ha
  exact selectedLocalizationToField_injective P j hxj (by simpa using heval)

private def backwardQuotientMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    SelectedAffineChartQuotient (k := k) P j →ₐ[k] OriginalAffineChartLocalization (k := k) P j := by
  let f := backwardPolynomialMap P j
  refine Ideal.Quotient.liftₐ (SelectedAffineChartIdeal (k := k) P j) f ?_
  intro a ha
  have heval : MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
      (selectedPoint P j) a = 0 := by
    have hker := componentChartEquationIdeal_eq_genericEvalKer P (Fin.succ j)
      (SelectedAffineCoordinateEquiv j) (selectedChart_nonzero P j hxj)
    change a ∈ componentChartEquationIdeal P (Fin.succ j) (SelectedAffineCoordinateEquiv j) at ha
    rw [hker] at ha
    simpa [selectedPoint] using (RingHom.mem_ker.mp ha)
  have hcomp := backwardPolynomialMap_toField P j hxj
  have hzero : originalAffineChartToFunctionField P j hxj (f a) = 0 := by
    calc
      originalAffineChartToFunctionField P j hxj (f a) =
          MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
            (selectedPoint P j) a :=
        congrArg (fun g : MvPolynomial (Fin m) k →+* ComponentFractionField P => g a) hcomp
      _ = 0 := heval
  exact originalLocalizationToField_injective P j hxj (by simpa using hzero)

private theorem invSelf_isUnit
    {R S : Type u} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] :
    IsUnit (IsLocalization.Away.invSelf (R := R) (S := S) r) := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨algebraMap R S r, by
    simpa [mul_comm] using IsLocalization.Away.mul_invSelf (R := R) (S := S) r⟩

private theorem forwardQuotientMap_denominator
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    forwardQuotientMap P j hxj (originalAffineChartDenominator P j) =
      IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) := by
  change (Ideal.Quotient.lift P.asIdeal (forwardPolynomialMap P j).toRingHom _)
    (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j)) = _
  rw [Ideal.Quotient.lift_mk]
  change MvPolynomial.aeval (fun i => if hij : i = j then
      IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) else
      algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j) (selectedAffineChartVariableClass P j i hij) *
        IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) (MvPolynomial.X j) = _
  rw [MvPolynomial.aeval_X]
  simp [forwardPolynomialMap]

private theorem backwardQuotientMap_denominator
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    backwardQuotientMap P j hxj (selectedAffineChartDenominator P j) =
      IsLocalization.Away.invSelf (originalAffineChartDenominator P j) := by
  change (Ideal.Quotient.lift (SelectedAffineChartIdeal (k := k) P j)
      (backwardPolynomialMap P j).toRingHom _)
    (Ideal.Quotient.mk (SelectedAffineChartIdeal (k := k) P j)
      (MvPolynomial.X (selectedAffineChartOrigin j))) = _
  rw [Ideal.Quotient.lift_mk]
  change MvPolynomial.aeval (fun a => if ha : a = selectedAffineChartOrigin j then
      IsLocalization.Away.invSelf (originalAffineChartDenominator P j) else
      algebraMap (OriginalAffineChartQuotient (k := k) P)
        (OriginalAffineChartLocalization (k := k) P j)
        (Ideal.Quotient.mk P.asIdeal
          (MvPolynomial.X (Fin.cases j (fun i => i) ((SelectedAffineCoordinateEquiv j) a).1))) *
      IsLocalization.Away.invSelf (originalAffineChartDenominator P j))
      (MvPolynomial.X (selectedAffineChartOrigin j)) = _
  rw [MvPolynomial.aeval_X]
  simp [backwardPolynomialMap, selectedAffineChartOrigin_coordinate]

def originalAffineChartOverlapForward
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    OriginalAffineChartLocalization (k := k) P j →ₐ[k] SelectedAffineChartLocalization (k := k) P j :=
  IsLocalization.Away.liftAlgHom (originalAffineChartDenominator P j)
    (f := forwardQuotientMap P j hxj)
    (by rw [forwardQuotientMap_denominator P j hxj]
        exact invSelf_isUnit (selectedAffineChartDenominator P j))

def originalAffineChartOverlapBackward
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    SelectedAffineChartLocalization (k := k) P j →ₐ[k] OriginalAffineChartLocalization (k := k) P j :=
  IsLocalization.Away.liftAlgHom (selectedAffineChartDenominator P j)
    (f := backwardQuotientMap P j hxj)
    (by rw [backwardQuotientMap_denominator P j hxj]
        exact invSelf_isUnit (originalAffineChartDenominator P j))

private theorem forwardQuotientMap_toField
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (selectedAffineChartToFunctionField P j hxj).comp
        (forwardQuotientMap P j hxj).toRingHom =
      algebraMap (OriginalAffineChartQuotient (k := k) P) (ComponentFractionField P) := by
  apply Ideal.Quotient.ringHom_ext
  change ((selectedAffineChartToFunctionField P j hxj).comp
      (Ideal.Quotient.lift P.asIdeal (forwardPolynomialMap P j).toRingHom _)).comp
        (Ideal.Quotient.mk P.asIdeal) = componentAffineGenericPointMap P
  rw [RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk]
  exact forwardPolynomialMap_toField P j hxj

private theorem backwardQuotientMap_toField
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (originalAffineChartToFunctionField P j hxj).comp
        (backwardQuotientMap P j hxj).toRingHom =
      (selectedQuotientToField P j hxj).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  change ((originalAffineChartToFunctionField P j hxj).comp
      (Ideal.Quotient.lift (SelectedAffineChartIdeal (k := k) P j)
        (backwardPolynomialMap P j).toRingHom _)).comp
        (Ideal.Quotient.mk (SelectedAffineChartIdeal (k := k) P j)) =
    (selectedQuotientToField P j hxj).toRingHom.comp
      (Ideal.Quotient.mk (SelectedAffineChartIdeal (k := k) P j))
  rw [RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk]
  exact backwardPolynomialMap_toField P j hxj

private theorem forwardLocalizationMap_comp_base
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (originalAffineChartOverlapForward P j hxj).toRingHom.comp
        (algebraMap (OriginalAffineChartQuotient (k := k) P)
          (OriginalAffineChartLocalization (k := k) P j)) =
      (forwardQuotientMap P j hxj).toRingHom := by
  change (IsLocalization.Away.liftAlgHom (originalAffineChartDenominator P j)
      (f := forwardQuotientMap P j hxj) ?_).toRingHom.comp
        (algebraMap (OriginalAffineChartQuotient (k := k) P)
          (OriginalAffineChartLocalization (k := k) P j)) =
      (forwardQuotientMap P j hxj).toRingHom
  rw [IsLocalization.Away.liftAlgHom_toRingHom,
    IsLocalization.Away.lift_comp]

private theorem backwardLocalizationMap_comp_base
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (originalAffineChartOverlapBackward P j hxj).toRingHom.comp
        (algebraMap (SelectedAffineChartQuotient (k := k) P j)
          (SelectedAffineChartLocalization (k := k) P j)) =
      (backwardQuotientMap P j hxj).toRingHom := by
  change (IsLocalization.Away.liftAlgHom (selectedAffineChartDenominator P j)
      (f := backwardQuotientMap P j hxj) ?_).toRingHom.comp
        (algebraMap (SelectedAffineChartQuotient (k := k) P j)
          (SelectedAffineChartLocalization (k := k) P j)) =
      (backwardQuotientMap P j hxj).toRingHom
  rw [IsLocalization.Away.liftAlgHom_toRingHom,
    IsLocalization.Away.lift_comp]

private theorem selectedField_comp_forwardLocalization
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (selectedAffineChartToFunctionField P j hxj).comp
        (originalAffineChartOverlapForward P j hxj).toRingHom =
      originalAffineChartToFunctionField P j hxj := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (originalAffineChartDenominator P j))
  calc
    ((selectedAffineChartToFunctionField P j hxj).comp
        (originalAffineChartOverlapForward P j hxj).toRingHom).comp
        (algebraMap (OriginalAffineChartQuotient (k := k) P)
          (OriginalAffineChartLocalization (k := k) P j)) =
      (selectedAffineChartToFunctionField P j hxj).comp
        (forwardQuotientMap P j hxj).toRingHom := by
          rw [RingHom.comp_assoc]
          rw [forwardLocalizationMap_comp_base P j hxj]
    _ = algebraMap (OriginalAffineChartQuotient (k := k) P) (ComponentFractionField P) :=
      forwardQuotientMap_toField P j hxj
    _ = (originalAffineChartToFunctionField P j hxj).comp
      (algebraMap (OriginalAffineChartQuotient (k := k) P)
            (OriginalAffineChartLocalization (k := k) P j)) := by
          symm
          simp [originalAffineChartToFunctionField, IsLocalization.Away.lift_comp]

private theorem originalField_comp_backwardLocalization
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (originalAffineChartToFunctionField P j hxj).comp
        (originalAffineChartOverlapBackward P j hxj).toRingHom =
      selectedAffineChartToFunctionField P j hxj := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (selectedAffineChartDenominator P j))
  calc
    ((originalAffineChartToFunctionField P j hxj).comp
        (originalAffineChartOverlapBackward P j hxj).toRingHom).comp
        (algebraMap (SelectedAffineChartQuotient (k := k) P j)
          (SelectedAffineChartLocalization (k := k) P j)) =
      (originalAffineChartToFunctionField P j hxj).comp
        (backwardQuotientMap P j hxj).toRingHom := by
          rw [RingHom.comp_assoc]
          rw [backwardLocalizationMap_comp_base P j hxj]
    _ = (selectedQuotientToField P j hxj).toRingHom :=
      backwardQuotientMap_toField P j hxj
    _ = (selectedAffineChartToFunctionField P j hxj).comp
      (algebraMap (SelectedAffineChartQuotient (k := k) P j)
            (SelectedAffineChartLocalization (k := k) P j)) := by
          symm
          simp [selectedAffineChartToFunctionField, IsLocalization.Away.lift_comp]

private theorem forward_backward_selected
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (originalAffineChartOverlapForward P j hxj).toRingHom.comp
        (originalAffineChartOverlapBackward P j hxj).toRingHom =
      RingHom.id (SelectedAffineChartLocalization (k := k) P j) := by
  ext z
  apply selectedLocalizationToField_injective P j hxj
  calc
    selectedAffineChartToFunctionField P j hxj
        ((originalAffineChartOverlapForward P j hxj).toRingHom
          ((originalAffineChartOverlapBackward P j hxj).toRingHom z)) =
        originalAffineChartToFunctionField P j hxj
          ((originalAffineChartOverlapBackward P j hxj).toRingHom z) := by
            have h := congrArg
              (fun f : OriginalAffineChartLocalization (k := k) P j →+*
                  ComponentFractionField P =>
                f ((originalAffineChartOverlapBackward P j hxj).toRingHom z))
              (selectedField_comp_forwardLocalization P j hxj)
            simpa only [RingHom.comp_apply] using h
    _ = selectedAffineChartToFunctionField P j hxj z := by
          have h := congrArg
            (fun f : SelectedAffineChartLocalization (k := k) P j →+*
                ComponentFractionField P => f z)
            (originalField_comp_backwardLocalization P j hxj)
          simpa only [RingHom.comp_apply] using h
    _ = selectedAffineChartToFunctionField P j hxj
          ((RingHom.id (SelectedAffineChartLocalization (k := k) P j)) z) := rfl

private theorem backward_forward_original
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (originalAffineChartOverlapBackward P j hxj).toRingHom.comp
        (originalAffineChartOverlapForward P j hxj).toRingHom =
      RingHom.id (OriginalAffineChartLocalization (k := k) P j) := by
  ext z
  apply originalLocalizationToField_injective P j hxj
  calc
    originalAffineChartToFunctionField P j hxj
        ((originalAffineChartOverlapBackward P j hxj).toRingHom
          ((originalAffineChartOverlapForward P j hxj).toRingHom z)) =
        selectedAffineChartToFunctionField P j hxj
          ((originalAffineChartOverlapForward P j hxj).toRingHom z) := by
            have h := congrArg
              (fun f : SelectedAffineChartLocalization (k := k) P j →+*
                  ComponentFractionField P =>
                f ((originalAffineChartOverlapForward P j hxj).toRingHom z))
              (originalField_comp_backwardLocalization P j hxj)
            simpa only [RingHom.comp_apply] using h
    _ = originalAffineChartToFunctionField P j hxj z := by
          have h := congrArg
            (fun f : OriginalAffineChartLocalization (k := k) P j →+*
                ComponentFractionField P => f z)
            (selectedField_comp_forwardLocalization P j hxj)
          simpa only [RingHom.comp_apply] using h
    _ = originalAffineChartToFunctionField P j hxj
          ((RingHom.id (OriginalAffineChartLocalization (k := k) P j)) z) := rfl

/-- The direct same-function-field comparison between the original affine
chart, localized at `X j`, and the chart with original `X j` distinguished. -/
noncomputable def originalAffineChartOverlapEquiv
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    OriginalAffineChartLocalization (k := k) P j ≃ₐ[k]
      SelectedAffineChartLocalization (k := k) P j :=
  AlgEquiv.ofAlgHom (originalAffineChartOverlapForward P j hxj)
    (originalAffineChartOverlapBackward P j hxj)
    (by
      apply AlgHom.ext
      intro z
      exact DFunLike.congr_fun (forward_backward_selected P j hxj) z)
    (by
      apply AlgHom.ext
      intro z
      exact DFunLike.congr_fun (backward_forward_original P j hxj) z)

/-- The selected coordinate corresponding to original `X j` is the inverse
chart coordinate on the overlap. -/
theorem originalAffineChartOverlapEquiv_Xj
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    originalAffineChartOverlapEquiv P j hxj
      (algebraMap (OriginalAffineChartQuotient (k := k) P)
        (OriginalAffineChartLocalization (k := k) P j)
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j))) =
      IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) := by
  change originalAffineChartOverlapForward P j hxj
      (algebraMap (OriginalAffineChartQuotient (k := k) P)
        (OriginalAffineChartLocalization (k := k) P j)
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j))) = _
  calc
    _ = forwardQuotientMap P j hxj
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j)) := by
          have h := congrArg
            (fun f : OriginalAffineChartQuotient (k := k) P →+*
                SelectedAffineChartLocalization (k := k) P j =>
              f (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j)))
            (forwardLocalizationMap_comp_base P j hxj)
          change (originalAffineChartOverlapForward P j hxj).toRingHom _ =
            (forwardQuotientMap P j hxj).toRingHom _
          simpa only [RingHom.comp_apply] using h
    _ = IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) := by
          change (Ideal.Quotient.lift P.asIdeal
            (forwardPolynomialMap P j).toRingHom _)
            (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j)) = _
          rw [Ideal.Quotient.lift_mk]
          change MvPolynomial.aeval (fun i => if hij : i = j then
            IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) else
            algebraMap (SelectedAffineChartQuotient (k := k) P j)
              (SelectedAffineChartLocalization (k := k) P j)
              (selectedAffineChartVariableClass P j i hij) *
                IsLocalization.Away.invSelf (selectedAffineChartDenominator P j))
            (MvPolynomial.X j) = _
          rw [MvPolynomial.aeval_X]
          simp

/-- Other original affine coordinates map to their selected-chart ratios. -/
theorem originalAffineChartOverlapEquiv_Xi
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j i : Fin m)
    (hij : i ≠ j) (hxj : componentCoordinate P j ≠ 0) :
    originalAffineChartOverlapEquiv P j hxj
      (algebraMap (OriginalAffineChartQuotient (k := k) P)
        (OriginalAffineChartLocalization (k := k) P j)
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i))) =
      algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j)
        (selectedAffineChartVariableClass P j i hij) *
        IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) := by
  change originalAffineChartOverlapForward P j hxj
      (algebraMap (OriginalAffineChartQuotient (k := k) P)
        (OriginalAffineChartLocalization (k := k) P j)
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i))) = _
  calc
    _ = forwardQuotientMap P j hxj
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) := by
          have h := congrArg
            (fun f : OriginalAffineChartQuotient (k := k) P →+*
                SelectedAffineChartLocalization (k := k) P j =>
              f (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)))
            (forwardLocalizationMap_comp_base P j hxj)
          change (originalAffineChartOverlapForward P j hxj).toRingHom _ =
            (forwardQuotientMap P j hxj).toRingHom _
          simpa only [RingHom.comp_apply] using h
    _ = algebraMap (SelectedAffineChartQuotient (k := k) P j)
          (SelectedAffineChartLocalization (k := k) P j)
          (selectedAffineChartVariableClass P j i hij) *
          IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) := by
          change (Ideal.Quotient.lift P.asIdeal
            (forwardPolynomialMap P j).toRingHom _)
            (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) = _
          rw [Ideal.Quotient.lift_mk]
          change MvPolynomial.aeval (fun a => if h : a = j then
            IsLocalization.Away.invSelf (selectedAffineChartDenominator P j) else
            algebraMap (SelectedAffineChartQuotient (k := k) P j)
              (SelectedAffineChartLocalization (k := k) P j)
              (selectedAffineChartVariableClass P j a h) *
                IsLocalization.Away.invSelf (selectedAffineChartDenominator P j))
            (MvPolynomial.X i) = _
          rw [MvPolynomial.aeval_X]
          simp [hij]

/-- The selected distinguished coordinate is sent back to `1/X j`. -/
theorem originalAffineChartOverlapEquiv_symm_X0
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (originalAffineChartOverlapEquiv P j hxj).symm
      (algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j)
        (selectedAffineChartDenominator P j)) =
      IsLocalization.Away.invSelf (originalAffineChartDenominator P j) := by
  change originalAffineChartOverlapBackward P j hxj
      (algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j)
        (selectedAffineChartDenominator P j)) = _
  calc
    _ = backwardQuotientMap P j hxj (selectedAffineChartDenominator P j) := by
          have h := congrArg
            (fun f : SelectedAffineChartQuotient (k := k) P j →+*
                OriginalAffineChartLocalization (k := k) P j =>
              f (selectedAffineChartDenominator P j))
            (backwardLocalizationMap_comp_base P j hxj)
          change (originalAffineChartOverlapBackward P j hxj).toRingHom _ =
            (backwardQuotientMap P j hxj).toRingHom _
          simpa only [RingHom.comp_apply] using h
    _ = IsLocalization.Away.invSelf (originalAffineChartDenominator P j) :=
          backwardQuotientMap_denominator P j hxj

/-- The reverse overlap action sends each non-distinguished selected affine
coordinate to the matching original coordinate divided by `X j`. -/
theorem originalAffineChartOverlapEquiv_symm_Xi
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j i : Fin m)
    (hij : i ≠ j) (hxj : componentCoordinate P j ≠ 0) :
    (originalAffineChartOverlapEquiv P j hxj).symm
      (algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j)
        (selectedAffineChartVariableClass P j i hij)) =
      algebraMap (OriginalAffineChartQuotient (k := k) P)
        (OriginalAffineChartLocalization (k := k) P j)
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) *
        IsLocalization.Away.invSelf (originalAffineChartDenominator P j) := by
  change originalAffineChartOverlapBackward P j hxj
      (algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j)
        (selectedAffineChartVariableClass P j i hij)) = _
  calc
    _ = backwardQuotientMap P j hxj
        (selectedAffineChartVariableClass P j i hij) := by
          have h := congrArg
            (fun f : SelectedAffineChartQuotient (k := k) P j →+*
                OriginalAffineChartLocalization (k := k) P j =>
              f (selectedAffineChartVariableClass P j i hij))
            (backwardLocalizationMap_comp_base P j hxj)
          change (originalAffineChartOverlapBackward P j hxj).toRingHom _ =
            (backwardQuotientMap P j hxj).toRingHom _
          simpa only [RingHom.comp_apply] using h
    _ = algebraMap (OriginalAffineChartQuotient (k := k) P)
          (OriginalAffineChartLocalization (k := k) P j)
          (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) *
          IsLocalization.Away.invSelf (originalAffineChartDenominator P j) := by
          let a := (SelectedAffineCoordinateEquiv j).symm
            ⟨i.succ, by simpa using hij⟩
          have hidx : ((SelectedAffineCoordinateEquiv j) a).1 = i.succ := by
            dsimp [a]
            simp
          have ha : a ≠ selectedAffineChartOrigin j := by
            intro h
            have h' := congrArg (fun z => ((SelectedAffineCoordinateEquiv j) z).1) h
            rw [selectedAffineChartOrigin_coordinate] at h'
            rw [hidx] at h'
            exact Fin.succ_ne_zero i h'
          change backwardQuotientMap P j hxj
            (Ideal.Quotient.mk (SelectedAffineChartIdeal (k := k) P j)
              (MvPolynomial.X a)) = _
          change (Ideal.Quotient.lift (SelectedAffineChartIdeal (k := k) P j)
            (backwardPolynomialMap P j).toRingHom _)
            (Ideal.Quotient.mk (SelectedAffineChartIdeal (k := k) P j)
              (MvPolynomial.X a)) = _
          rw [Ideal.Quotient.lift_mk]
          change MvPolynomial.aeval (fun b => if hb : b =
              selectedAffineChartOrigin j then
            IsLocalization.Away.invSelf (originalAffineChartDenominator P j) else
            algebraMap (OriginalAffineChartQuotient (k := k) P)
              (OriginalAffineChartLocalization (k := k) P j)
              (Ideal.Quotient.mk P.asIdeal
                (MvPolynomial.X (Fin.cases j (fun z => z)
                  ((SelectedAffineCoordinateEquiv j) b).1))) *
                IsLocalization.Away.invSelf (originalAffineChartDenominator P j))
            (MvPolynomial.X a) = _
          rw [MvPolynomial.aeval_X, dif_neg ha, hidx]
          rfl

/-- The two chart-localization injections into the function field commute with
the overlap equivalence. -/
theorem originalAffineChartOverlap_sameField_forward
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (selectedAffineChartToFunctionField P j hxj).comp
        (originalAffineChartOverlapEquiv P j hxj).toAlgHom.toRingHom =
      originalAffineChartToFunctionField P j hxj := by
  change (selectedAffineChartToFunctionField P j hxj).comp
      (originalAffineChartOverlapForward P j hxj).toRingHom = _
  exact selectedField_comp_forwardLocalization P j hxj

theorem originalAffineChartOverlap_sameField_backward
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0) :
    (originalAffineChartToFunctionField P j hxj).comp
        (originalAffineChartOverlapEquiv P j hxj).symm.toAlgHom.toRingHom =
      selectedAffineChartToFunctionField P j hxj := by
  change (originalAffineChartToFunctionField P j hxj).comp
      (originalAffineChartOverlapBackward P j hxj).toRingHom = _
  exact originalField_comp_backwardLocalization P j hxj

end
end Stafford38.Geometry.ProjectiveChartSameFieldOverlap
