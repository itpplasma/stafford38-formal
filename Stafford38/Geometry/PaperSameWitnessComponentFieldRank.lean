module
public import Stafford38.Geometry.GeneralDivisorialVisibleFrame
public import Stafford38.Geometry.PaperVisibleFrameFieldRank
public import Stafford38.Geometry.PaperResidueGroundAlgebraTransport
public import Stafford38.Geometry.PaperGenericTangentRank
public import Stafford38.Geometry.RetainedPlaceConormalTransport
public import Stafford38.Geometry.ScalarExtensionPoints
public import Stafford38.Geometry.FormalDivisorLaurentConormal

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000

namespace Stafford38.Geometry.PaperSameWitnessComponentFieldRank

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ExactVisibleDivisorFrameInterface
open Stafford38.Geometry.KaehlerDVRVisibility
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedDVR
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.DivisorTangentLattice
open Stafford38.Geometry.PaperGenericTangentRank
open Stafford38.Geometry.GeneralDivisorialVisibleFrame

noncomputable section
universe u

/-- The same-witness component-field Kähler rank bound, isolated from the
larger completed-chart tangent transport. -/
theorem component_field_rank_of_witness
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
    let E := LaurentSeries κ
    letI : Algebra k E := (groundLaurentMap (k := k) (K := κ)).toAlgebra
    letI : SMul k E := (inferInstance : Algebra k E).toSMul
    letI : Module k E := (inferInstance : Algebra k E).toModule
    let lift := retainedLaurentLift P ⟨0, hm⟩ W
    letI : Algebra F E := lift.toAlgebra
    letI : Algebra k F := inferInstance
    letI : SMul k F := (inferInstance : Algebra k F).toSMul
    letI : Module k F := (inferInstance : Algebra k F).toModule
    Module.finrank F (Ω[F⁄k]) ≤ Module.finrank κ (Ω[κ⁄k]) + 1 := by
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
  letI : Algebra V F := V.subtype.toAlgebra
  letI : IsScalarTower k V F := C.groundTower
  let κ := ResidueField V
  let retainedResidueAlgebra : Algebra k κ :=
    retainedResidueGroundAlgebra P i₀ W
  let canonicalResidueAlgebra : Algebra k κ :=
    ((residue V).comp C.groundCoeff).toAlgebra
  letI : Algebra k κ := retainedResidueAlgebra
  have hretainedMap :
      @algebraMap k κ _ _ retainedResidueAlgebra =
        (residue V).comp C.groundCoeff := by
    simpa [C, W, V, κ, C.groundCoeff_eq_retained] using w.retainedGroundMap
  have hMap :
      @algebraMap k κ _ _ retainedResidueAlgebra =
        @algebraMap k κ _ _ canonicalResidueAlgebra := by
    calc
      _ = (residue V).comp C.groundCoeff := hretainedMap
      _ = _ := rfl
  have hresidueAlgebra :
      retainedResidueAlgebra = canonicalResidueAlgebra := by
    exact Algebra.algebra_ext _ _ (RingHom.congr_fun hMap)
  let E := LaurentSeries κ
  letI : Algebra k E := (groundLaurentMap (k := k) (K := κ)).toAlgebra
  letI : SMul k E := (inferInstance : Algebra k E).toSMul
  letI : Module k E := (inferInstance : Algebra k E).toModule
  let lift := retainedLaurentLift P i₀ W
  letI : Algebra F E := lift.toAlgebra
  letI : Algebra k F := inferInstance
  letI : SMul k F := (inferInstance : Algebra k F).toSMul
  letI : Module k F := (inferInstance : Algebra k F).toModule
  have hground := retainedLaurentLift_comp_algebraMap P i₀ W
  letI : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun c ↦ by
    have h := congrArg (fun f : k →+* E ↦ f c) hground
    change (groundLaurentMap (k := k) (K := κ)) c =
      lift (algebraMap k F c)
    exact h.symm
  let D := w.differential.core.D
  have himage : ∀ ω : Ω[V⁄k],
      KaehlerDifferential.map k k V F ω ∈ D.W := by
    intro ω
    rw [w.differential.sourceImage.D_sourceImage]
    exact ⟨ω, rfl⟩
  have hcoordinate : ∀ j : Fin m,
      componentCoordinate P j =
        algebraMap V F (D.Q j) / algebraMap V F D.Q₀ := by
    have hq0F : (C.q 0 : F) ≠ 0 := by
      intro h
      apply C.q0_ne
      exact Subtype.ext h
    have hdiv : ∀ j : Fin m,
        componentCoordinate P j =
          algebraMap V F (C.q j.succ) / algebraMap V F (C.q 0) := by
      intro j
      exact (componentCoordinate_eq_div P (fun a ↦ (C.q a : F))
        C.scale C.q_commonScale hq0F j).symm
    intro j
    rw [w.differential.core.D_Q j, w.differential.core.D_Q0]
    exact hdiv j
  have hD_Q_values :
      (fun j : Fin m ↦ residue V (D.Q j)) =
        (fun j : Fin m ↦ residue V (C.q (Fin.succ j))) := by
    funext j
    exact congrArg (residue V) (w.differential.core.D_Q j)
  have hD_Q_range :
      Set.range (fun j : Fin m ↦ residue V (D.Q j)) =
        Set.range (fun j : Fin m ↦ residue V (C.q (Fin.succ j))) :=
    congrArg Set.range hD_Q_values
  have halgRetained : letI : Algebra k κ := retainedResidueAlgebra;
      Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun j : Fin m ↦ residue V (D.Q j)) :
        IntermediateField k κ) κ := by
    rw [hD_Q_range]
    exact w.halg
  have halgCanonical : letI : Algebra k κ := canonicalResidueAlgebra;
      Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun j : Fin m ↦ residue V (D.Q j)) :
        IntermediateField k κ) κ :=
    PaperResidueGroundAlgebraTransport.algebraic_adjoin_transfer_of_algebra_eq
      retainedResidueAlgebra canonicalResidueAlgebra hresidueAlgebra
      (Set.range fun j : Fin m ↦ residue V (D.Q j)) halgRetained
  have hRankCanonical : letI : Algebra k κ := canonicalResidueAlgebra;
      Module.finrank F (Ω[F⁄k]) ≤ Module.finrank κ (Ω[κ⁄k]) + 1 := by
    letI : Algebra k κ := canonicalResidueAlgebra
    exact @Stafford38.Geometry.PaperVisibleFrameFieldRank.component_fraction_field_rank_bound
      k V F inferInstance inferInstance inferInstance inferInstance inferInstance
      (C.groundCoeff.toAlgebra) inferInstance (V.subtype.toAlgebra)
      C.groundTower (Fin m) inferInstance D w.differential.core.D_maximalIdeal
      himage halgCanonical (componentCoordinate P) hcoordinate
      (componentCoordinate_adjoin_eq_top P)
  have hResidueRankEq :=
    PaperResidueGroundAlgebraTransport.kaehler_finrank_eq_of_algebra_eq
      retainedResidueAlgebra canonicalResidueAlgebra hresidueAlgebra
  change Module.finrank F (Ω[F⁄k]) ≤
    (letI : Algebra k κ := retainedResidueAlgebra;
      Module.finrank κ (Ω[κ⁄k])) + 1
  rw [hResidueRankEq]
  exact hRankCanonical

#print axioms component_field_rank_of_witness

end
end Stafford38.Geometry.PaperSameWitnessComponentFieldRank
