module

public import Stafford38.Paper.Section5.KaehlerRankBound
public import Stafford38.Geometry.GeneralDivisorialVisibleFrame
public import Stafford38.Geometry.PaperActualDivisorTangent
public import Stafford38.Geometry.PaperResidueDerivationFrame
public import Stafford38.Geometry.PaperResidueGroundAlgebraTransport
public import Stafford38.Geometry.RetainedPlaceConormalTransport

@[expose] public section

/-!
# The completion `V̂ ≅ κ[[t]]` and the bound of Lemma 5.12(a) at the place `V`

Two paragraphs of the proof of Theorem 5.7(i) at the discrete valuation ring
`V` of Lemmas 5.9–5.10 (the witness `w`):

* `step_completion`: a coefficient field of `V̂` containing `K` identifies
  `V̂ ≅ κ[[t]]` with `ϖ ↦ t`; `V → κ[[t]]` is injective and extends to
  `F ↪ κ((t))`, and the residue is the constant term.
* `witness_lemma_5_12_a_bound`: Lemma 5.12(a)'s bound `dim_F Ω_{F/K} ≤ d' + 1`
  for this `V`, by the printed argument of `lemma_5_12_a_bound`.
-/

namespace Stafford38.Paper.Section5

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.PaperActualDivisorTangent
open Stafford38.Geometry.PaperResidueDerivationFrame
open Stafford38.Geometry.PaperResidueGroundAlgebraTransport
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RetainedProjectiveCompletion

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

universe u

/-- **Paragraph "`V̂ ≅ κ[[t]]`".**  For the discrete valuation ring `V` of the
proof, with uniformizer `ϖ` (`𝔪_V = (ϖ)`), the map `V → V̂ ≅ κ[[t]]` given by
a coefficient field containing `K`: is injective; sends `c ∈ K` to the
constant series `c`; sends `ϖ` to `t`; has constant term equal to the residue
`res : V → κ`; and extends to an embedding `F ↪ κ((t))` which is the identity
on `K`. -/
theorem step_completion {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    maximalIdeal V = Ideal.span {chosenUniformizer V} ∧
      Function.Injective (retainedToCompletedPowerSeries W) ∧
      (∀ c : k, retainedToCompletedPowerSeries W (C.groundCoeff c) =
        PowerSeries.C (algebraMap k κ c)) ∧
      retainedToCompletedPowerSeries W (chosenUniformizer V) = PowerSeries.X ∧
      (∀ v : V, PowerSeries.constantCoeff (retainedToCompletedPowerSeries W v) =
        residue V v) ∧
      Function.Injective (retainedLaurentLift P ⟨0, hm⟩ W) ∧
      (∀ v : V, retainedLaurentLift P ⟨0, hm⟩ W (algebraMap V (ComponentFractionField P) v) =
        algebraMap (PowerSeries κ) (LaurentSeries κ) (retainedToCompletedPowerSeries W v)) ∧
      (retainedLaurentLift P ⟨0, hm⟩ W).comp (algebraMap k (ComponentFractionField P)) =
        groundLaurentMap (k := k) (K := κ) := by
  intro C W
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
    (ComponentFractionField P) := W.ambientAlgebra
  intro V
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  intro κ
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  have hground : ∀ c : k, retainedToCompletedPowerSeries W (C.groundCoeff c) =
      PowerSeries.C (algebraMap k κ c) := by
    intro c
    rw [C.groundCoeff_eq_retained]
    exact retainedToCompletedPowerSeries_ground P ⟨0, hm⟩ W c
  exact ⟨maximalIdeal_eq_span_chosenUniformizer V, retainedToCompletedPowerSeries_injective W,
    hground, retainedToCompletedPowerSeries_chosenUniformizer (k := k) W,
    constantCoeff_retainedToCompleted_eq_residue (k := k) W, RingHom.injective _,
    retainedLaurentLift_algebraMap P ⟨0, hm⟩ W, retainedLaurentLift_comp_algebraMap P ⟨0, hm⟩ W⟩

/-- **Lemma 5.12(a), `m ≤ d' + 1`, at the place of the proof.**  For the
discrete valuation ring `V` of the witness, with `Ω_{V/K}` finitely generated
(Lemma 5.10(c)), `dim_F Ω_{F/K} ≤ dim_κ Ω_{κ/K} + 1`; this is
`lemma_5_12_a_bound` (second fundamental exact sequence for `V → κ`,
Nakayama, `F ⊗_V Ω_{V/K} = Ω_{F/K}`), read with the witness's `K`-algebra
structure on `κ`. -/
theorem witness_lemma_5_12_a_bound {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hfin :
      letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
        (ComponentFractionField P) := w.column.W.ambientAlgebra
      let V := w.column.W.place.valuation.toSubring
      letI : Algebra k V := w.column.groundCoeff.toAlgebra
      Module.Finite V (Ω[V⁄k])) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    Module.finrank F (Ω[F⁄k]) ≤ Module.finrank κ (Ω[κ⁄k]) + 1 := by
  intro C W F
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  intro V
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  intro κ
  have hfrac : IsFractionRing (↥W.place.valuation) (ComponentFractionField P) := inferInstance
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V F := V.subtype.toAlgebra
  letI : IsScalarTower k V F := C.groundTower
  letI : IsFractionRing V F := hfrac
  letI : Module.Finite V (Ω[V⁄k]) := hfin
  -- The bound with `κ` a `K`-algebra through `V`, i.e. `c ↦ res (c)`.
  have hbound := lemma_5_12_a_bound (k := k) (V := V) (F := F)
  -- That structure is the witness's retained one.
  have hres : (retainedResidueGroundAlgebra P ⟨0, hm⟩ W : Algebra k κ) =
      (inferInstance : Algebra k κ) := by
    apply Algebra.algebra_ext
    intro c
    have h := RingHom.congr_fun w.retainedGroundMap c
    change (@algebraMap k κ _ _ (retainedResidueGroundAlgebra P ⟨0, hm⟩ W)) c =
      residue V (retainedComponentCoefficientMap P ⟨0, hm⟩ W c) at h
    rw [h, ← C.groundCoeff_eq_retained]
    rfl
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  change Module.finrank F (Ω[F⁄k]) ≤
    (letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W;
      Module.finrank κ (Ω[κ⁄k])) + 1
  rw [kaehler_finrank_eq_of_algebra_eq _ _ hres]
  exact hbound

end

#print axioms step_completion
#print axioms witness_lemma_5_12_a_bound

end Stafford38.Paper.Section5
