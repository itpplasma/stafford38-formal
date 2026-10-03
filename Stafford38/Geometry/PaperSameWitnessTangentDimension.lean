module
public import Stafford38.Geometry.GeneralDivisorialVisibleFrame
public import Stafford38.Geometry.PaperGenericTangentRank
public import Stafford38.Geometry.PaperSameWitnessComponentFieldRank
public import Stafford38.Geometry.ScalarExtensionPoints
public import Stafford38.Geometry.FormalDivisorLaurentConormal
public import Stafford38.Geometry.RetainedPlaceConormalTransport
public import Stafford38.Geometry.ExactDivisorialVisibleFrameExistence

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000

namespace Stafford38.Geometry.PaperSameWitnessTangentDimension

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.GenericPointKaehlerConormal
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.PaperGenericTangentRank
open Stafford38.Geometry.PaperSameWitnessComponentFieldRank
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.ScalarExtensionPoints

noncomputable section
universe u

/-- Tangent rank at the actual Laurent point of the same retained chart is at
most one plus the Kähler rank of its residue field. -/
def tangent_finrank_goal
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) : Prop :=
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
    let E := LaurentSeries κ
    letI : Algebra k E := (groundLaurentMap (k := k) (K := κ)).toAlgebra
    letI : SMul k E := (inferInstance : Algebra k E).toSMul
    letI : Module k E := (inferInstance : Algebra k E).toModule
    Module.finrank E
        (zariskiTangentSpace
          (dehomogenizedPoint
            (laurentColumn fun a ↦ retainedToCompletedPowerSeries W (C.q a)))
          (P.asIdeal.map
            (scalarPolynomialMap (k := k) (K := E) (Fin m)))) ≤
      Module.finrank κ (Ω[κ⁄k]) + 1

theorem tangent_finrank_le_residue_add_one_of_witness
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    tangent_finrank_goal hm P w := by
  dsimp [tangent_finrank_goal]
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
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P i₀ W
  let E := LaurentSeries κ
  letI : Algebra k E := (groundLaurentMap (k := k) (K := κ)).toAlgebra
  letI : SMul k E := (inferInstance : Algebra k E).toSMul
  letI : Module k E := (inferInstance : Algebra k E).toModule
  let ell : F →+* E := retainedLaurentLift P i₀ W
  let y : Fin m → E := dehomogenizedPoint
    (laurentColumn fun a ↦ retainedToCompletedPowerSeries W (C.q a))
  have hground : ell.comp (algebraMap k F) =
      groundLaurentMap (k := k) (K := κ) := by
    dsimp [ell]
    exact retainedLaurentLift_comp_algebraMap P i₀ W
  have hpoint : ell ∘ componentCoordinate P = y := by
    dsimp [ell, y]
    exact retainedLaurentLift_componentCoordinate P i₀ W C.q C.scale
      C.q_commonScale C.q0_ne
  have hy : y = dehomogenizedPoint
      (laurentColumn fun a ↦ retainedToCompletedPowerSeries W (C.q a)) := rfl
  letI : Algebra F E := ell.toAlgebra
  letI : Algebra k F := inferInstance
  letI : SMul k F := (inferInstance : Algebra k F).toSMul
  letI : Module k F := (inferInstance : Algebra k F).toModule
  letI : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun c ↦ by
    have h := congrArg (fun f : k →+* E ↦ f c) hground
    change (groundLaurentMap (k := k) (K := κ)) c =
      ell (algebraMap k F c)
    exact h.symm
  have hfieldRank : Module.finrank F (Ω[F⁄k]) ≤
      Module.finrank κ (Ω[κ⁄k]) + 1 :=
    component_field_rank_of_witness hm P w
  have hgenPoint : IntermediateField.adjoin k
      (Set.range (GenericPointKaehlerConormal.genericPoint P.asIdeal F)) = ⊤ := by
    change IntermediateField.adjoin k
      (Set.range (GenericPointKaehlerConormal.genericPoint P.asIdeal
        (ComponentFractionField P))) = ⊤
    have hcoordinates :
        GenericPointKaehlerConormal.genericPoint P.asIdeal
          (ComponentFractionField P) = componentCoordinate P := by
      funext j
      rfl
    rw [hcoordinates]
    exact componentCoordinate_adjoin_eq_top P
  have hgenericRank : Module.finrank E
      (AffineConormalSpan.zariskiTangentSpace
        (fun i : Fin m ↦ algebraMap F E
          (GenericPointKaehlerConormal.genericPoint P.asIdeal F i))
        (P.asIdeal.map (MvPolynomial.map (algebraMap k E)))) ≤
      Module.finrank F (Ω[F⁄k]) :=
    generic_tangent_finrank_le_component_kaehler_finrank
      (I := P.asIdeal) (hgen := hgenPoint)
  have hchartPoint :
      (fun j : Fin m ↦
        algebraMap F E (GenericPointKaehlerConormal.genericPoint P.asIdeal F j)) =
      dehomogenizedPoint
        (laurentColumn fun a ↦ retainedToCompletedPowerSeries W (C.q a)) := by
    calc
      (fun j : Fin m ↦
          algebraMap F E (GenericPointKaehlerConormal.genericPoint P.asIdeal F j)) = y := by
        funext j
        change ell (componentCoordinate P j) = y j
        exact congrFun hpoint j
      _ = dehomogenizedPoint
          (laurentColumn fun a ↦ retainedToCompletedPowerSeries W (C.q a)) := hy
  rw [hchartPoint] at hgenericRank
  have hbound := hgenericRank.trans hfieldRank
  change Nat.le _ _ at hbound
  change Nat.le _ _
  exact hbound

#print axioms tangent_finrank_le_residue_add_one_of_witness

end
end Stafford38.Geometry.PaperSameWitnessTangentDimension
