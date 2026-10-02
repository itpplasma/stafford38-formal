import Stafford38.Geometry.GeneralDivisorialVisibleFrameResidueSupport
import Stafford38.Geometry.PaperSameWitnessComponentFieldRank
import Stafford38.Geometry.ChartGenericPointFractionRing
import Stafford38.Geometry.AsymptoticChartArcAdapter
import Stafford38.Geometry.KaehlerTranscendenceBasis
import Stafford38.Geometry.RelativeDivisorialTower
import Stafford38.Geometry.RetainedGroundMapIdentification

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.SameWitnessTranscendenceDegreeBound

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.PaperSameWitnessComponentFieldRank
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification

universe u

noncomputable section

/-- The actual retained witness bounds the transcendence degree of its component field by one
more than that of its own residue field.  The chart-residue basis is selected from this same
witness's normalized projective coordinates. -/
theorem component_trdeg_le_residue_trdeg_add_one_of_witness
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
    Algebra.trdeg k F ≤ Algebra.trdeg k κ + 1 := by
  classical
  dsimp only
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let i₀ : Fin m := ⟨0, hm⟩
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  let κ := ResidueField V
  let retained : Algebra k κ := retainedResidueGroundAlgebra P i₀ W
  letI : Algebra k κ := retained
  have hretainedMap :
      @algebraMap k κ _ _ retained = (residue V).comp C.groundCoeff := by
    simpa [C, W, V, κ, C.groundCoeff_eq_retained] using w.retainedGroundMap
  letI : IsScalarTower k V κ := IsScalarTower.of_algebraMap_eq fun c => by
    have h := RingHom.congr_fun hretainedMap c
    change algebraMap k κ c = residue V (C.groundCoeff c)
    exact h
  obtain ⟨t, htFinite, _htSubset, htBasis⟩ :=
    exists_finite_chartCoordinate_residue_transcendenceBasis
      (k := k) (V := V) C.q C.chart (chartAffineCoordinateEquiv C.chart)
      C.chart_one (witness_q0_residue_eq_zero hm P w) w.halg
  let coordSet : Set F := Set.range (componentCoordinate P)
  let A := Algebra.adjoin k coordSet
  let E := IntermediateField.adjoin k coordSet
  letI : Algebra A E := (Subalgebra.inclusion
    (IntermediateField.algebra_adjoin_le_adjoin k coordSet)).toAlgebra
  letI : Algebra E F := E.toSubalgebra.toAlgebra
  letI : Algebra A F := A.val.toAlgebra
  have hgen : E = ⊤ := componentCoordinate_adjoin_eq_top P
  have hsurj : Function.Surjective (algebraMap E F) := by
    intro x
    have hx : x ∈ E := by rw [hgen]; simp
    exact ⟨⟨x, hx⟩, rfl⟩
  have hEF : Algebra.IsAlgebraic E F := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := hsurj x
    rw [← hy]
    exact isAlgebraic_algebraMap y
  have hAE : Algebra.IsAlgebraic A E :=
    Stafford38.Geometry.RelativeDivisorialTower.intermediateAdjoin_isAlgebraic_over_algebraAdjoin
      k coordSet
  have hTower : IsScalarTower A E F :=
    Subalgebra.inclusion.isScalarTower_right
      (IntermediateField.algebra_adjoin_le_adjoin k coordSet) F
  have hAF : Algebra.IsAlgebraic A F :=
    @Algebra.IsAlgebraic.trans A E F _ _ _ _ _ _ hTower _ hAE hEF
  have hAF' : Algebra.IsAlgebraic (Algebra.adjoin k coordSet) F := by
    simpa [A] using hAF
  obtain ⟨s, hsSubset, hsBasis⟩ :=
    @exists_isTranscendenceBasis_subset k F inferInstance inferInstance
      inferInstance inferInstance inferInstance coordSet hAF'
  have hsFinite : s.Finite := (Set.finite_range _).subset hsSubset
  letI : Fintype s := hsFinite.fintype
  letI : Fintype t := htFinite.fintype
  have hrank : Module.finrank F (KaehlerDifferential k F) ≤
      Module.finrank κ (KaehlerDifferential k κ) + 1 :=
    component_field_rank_of_witness hm P w
  rw [kaehlerFinrankOfTranscendenceBasis k F s (fun z => z) hsBasis,
      kaehlerFinrankOfTranscendenceBasis k κ t (fun z => z) htBasis] at hrank
  have hcard : (Fintype.card s : Cardinal) ≤ Fintype.card t + 1 := by
    exact_mod_cast hrank
  have hsCard : Algebra.trdeg k F = Fintype.card s := by
    rw [← hsBasis.cardinalMk_eq_trdeg]
    exact Cardinal.mk_fintype (↥s)
  have htCard : Algebra.trdeg k κ = Fintype.card t := by
    rw [← htBasis.cardinalMk_eq_trdeg]
    exact Cardinal.mk_fintype (↥t)
  calc
    Algebra.trdeg k F = Fintype.card s := hsCard
    _ ≤ Fintype.card t + 1 := hcard
    _ = Algebra.trdeg k κ + 1 := by rw [← htCard]

end
end Stafford38.Geometry.SameWitnessTranscendenceDegreeBound
