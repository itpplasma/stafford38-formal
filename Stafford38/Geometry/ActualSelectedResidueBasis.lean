module
public import Stafford38.Geometry.ActualChartValuationImage
public import Stafford38.Geometry.RetainedGroundMapIdentification

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualSelectedResidueBasis

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RetainedGroundMapIdentification

universe u

/-- A finite residue basis has distinct representatives among the chart coordinates. -/
theorem exists_selected_residue_basis_indices
    {k V : Type u} [Field k] [CommRing V] [IsLocalRing V]
    [Algebra k V] [Algebra k (ResidueField V)]
    [IsScalarTower k V (ResidueField V)]
    {m : ℕ} (q : Fin (m + 1) → V) (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hqchart : q chart = 1) (hq0res : residue V (q 0) = 0)
    (halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun j : Fin m => residue V (q (Fin.succ j))))
      (ResidueField V)) :
    ∃ t : Set (ResidueField V), t.Finite ∧
      IsTranscendenceBasis k ((↑) : t → ResidueField V) ∧
      ∃ index : t → Fin m, Function.Injective index ∧
        ∀ z : t, residue V (q (e (index z)).1) = (z : ResidueField V) := by
  classical
  obtain ⟨t, htFinite, htSubset, htBasis⟩ :=
    exists_finite_chartCoordinate_residue_transcendenceBasis
      (k := k) (m := m) (V := V) q chart e hqchart hq0res halg
  have hchoose : ∀ z : t, ∃ i : Fin m,
      residue V (q (e i).1) = (z : ResidueField V) := fun z => htSubset z.property
  choose index hindex using hchoose
  have hinj : Function.Injective index := by
    intro z₁ z₂ h
    apply Subtype.ext
    calc
      (z₁ : ResidueField V) = residue V (q (e (index z₁)).1) := (hindex z₁).symm
      _ = residue V (q (e (index z₂)).1) := by rw [h]
      _ = (z₂ : ResidueField V) := hindex z₂
  exact ⟨t, htFinite, htBasis, index, hinj, hindex⟩

/-- Select a finite residue transcendence basis from the actual retained
chart coordinates and retain distinct indices for its representatives. -/
theorem exists_actual_selected_residue_basis
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    ∃ t : Set κ, t.Finite ∧
      IsTranscendenceBasis k ((↑) : t → κ) ∧
      ∃ index : t → Fin m, Function.Injective index ∧
        ∀ z : t, residue V
          (C.q ((chartAffineCoordinateEquiv C.chart) (index z)).1) = (z : κ) := by
  classical
  dsimp only
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  let κ := ResidueField V
  let retained : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  letI : Algebra k κ := retained
  have hretainedMap : @algebraMap k κ _ _ retained =
      (residue V).comp C.groundCoeff := by
    simpa [C, W, V, κ, C.groundCoeff_eq_retained] using w.retainedGroundMap
  letI : IsScalarTower k V κ := IsScalarTower.of_algebraMap_eq fun c => by
    have h := RingHom.congr_fun hretainedMap c
    change algebraMap k κ c = residue V (C.groundCoeff c)
    exact h
  let e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) C.chart :=
    chartAffineCoordinateEquiv C.chart
  exact exists_selected_residue_basis_indices (k := k) (V := V) (m := m)
    C.q C.chart e C.chart_one (witness_q0_residue_eq_zero hm P w) w.halg

end Stafford38.Geometry.ActualSelectedResidueBasis

