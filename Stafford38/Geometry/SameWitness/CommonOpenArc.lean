module
public import Stafford38.Geometry.SameWitness.CommonOpen

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.ActualCommonOpenArcCompatibility
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

universe u

/-- The point-local Laurent arc extends to the selected same-witness common
open and retains its restriction and ground-field identities (paper proof,
common-open arc step). -/
structure CommonOpenArcData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup) where
  common : CommonOpenData hm P w setup coords
  rhoA : actualSelectedNormalization P w →+* LaurentSeries k
  hcanonicalRhoA :
    letI : common.M.IsMaximal := common.hM
    rhoA = originalToPointLocalFinSuccArcLaurentSeries
    (k := k) (d := @Fintype.card coords.t coords.htFinite)
    (A := actualSelectedNormalization P w) common.M common.eM common.alpha
  hf : IsUnit (rhoA (algebraMap (actualSelectedChartAlgebra P w)
    (actualSelectedNormalization P w) setup.f))
  hg : IsUnit (rhoA (algebraMap (actualSelectedChartAlgebra P w)
    (actualSelectedNormalization P w) common.g))
  hunitM : ∀ b, b ∉ common.M → IsUnit (rhoA b)
  rhoU : common.U →+* LaurentSeries k
  hcanonicalRhoU :
    letI : common.M.IsMaximal := common.hM
    rhoU = genericArcToGenericOpenExtraAwayB
    common.M setup.f setup.e rhoA hf hunitM common.g hg
  hcomp' :
    letI : common.M.IsMaximal := common.hM
    rhoU.comp
      (genericOpenExtraAwayBMap common.M setup.f setup.e common.g) = rhoA
  hgroundB' :
    letI : common.M.IsMaximal := common.hM
    (rhoU.comp
      (genericOpenExtraAwayBMap common.M setup.f setup.e common.g)).comp
      (@algebraMap k (actualSelectedNormalization P w) _ _
        coords.coeff.toAlgebra) =
    algebraMap k (LaurentSeries k)
  hbaseMap :
    letI : common.M.IsMaximal := common.hM
    (genericOpenExtraAwayBMap common.M setup.f setup.e common.g).comp
      (@algebraMap k (actualSelectedNormalization P w) _ _
        coords.coeff.toAlgebra) =
    algebraMap k common.U
  hgroundU : rhoU.comp (algebraMap k common.U) = algebraMap k (LaurentSeries k)
  hbadU :
    letI : common.M.IsMaximal := common.hM
    rhoU (genericOpenExtraAwayBMap common.M setup.f setup.e common.g
    (algebraMap (actualSelectedChartAlgebra P w)
      (actualSelectedNormalization P w) setup.f *
     algebraMap (actualSelectedChartAlgebra P w)
      (actualSelectedNormalization P w) setup.r)) ≠ 0
  hrU :
    letI : common.M.IsMaximal := common.hM
    rhoU (genericOpenExtraAwayBMap common.M setup.f setup.e common.g
    (algebraMap (actualSelectedChartAlgebra P w)
      (actualSelectedNormalization P w) setup.r)) ≠ 0
  hq0U :
    letI : common.M.IsMaximal := common.hM
    rhoU (genericOpenExtraAwayBMap common.M setup.f setup.e common.g
    (actualNormalizedProjectiveColumnInIntegralClosure hm P w 0)) ≠ 0
  hq1U :
    letI : common.M.IsMaximal := common.hM
    rhoU (genericOpenExtraAwayBMap common.M setup.f setup.e common.g
      (actualNormalizedProjectiveColumnInIntegralClosure hm P w
        (Fin.succ (⟨0, hm⟩ : Fin m)))) ≠ 0

/-- The retained point-local arc sends every element outside its maximal
center to a unit in the Laurent-series field. -/
private theorem pointLocalArc_unit_of_not_mem
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (common : CommonOpenData hm P w setup)
    (b : actualSelectedNormalization P w) (hb : b ∉ common.M) :
    letI : common.M.IsMaximal := common.hM
    IsUnit ((originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := @Fintype.card coords.t coords.htFinite)
      (A := actualSelectedNormalization P w) common.M common.eM common.alpha) b) := by
  letI : common.M.IsMaximal := common.hM
  let T := Localization.AtPrime common.M
  have hu : IsUnit (algebraMap (actualSelectedNormalization P w) T b) :=
    IsLocalization.map_units T (M := common.M.primeCompl) ⟨b, hb⟩
  change IsUnit
    ((pointLocalFinSuccArcLaurentSeries (k := k)
      (d := @Fintype.card coords.t coords.htFinite)
      (A := actualSelectedNormalization P w) common.M common.eM common.alpha).toRingHom
      (algebraMap (actualSelectedNormalization P w) T b))
  exact IsUnit.map _ hu

/-- The selected common-open map carries the canonical coefficient map to
the existing ground map on its localization. -/
private theorem commonOpenMap_comp_groundMap
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (common : CommonOpenData hm P w setup coords) :
    letI : common.M.IsMaximal := common.hM
    (genericOpenExtraAwayBMap common.M setup.f setup.e common.g).comp
      (@algebraMap k (actualSelectedNormalization P w) _ _ coords.coeff.toAlgebra) =
    algebraMap k common.U := by
  letI : common.M.IsMaximal := common.hM
  let B := actualSelectedNormalization P w
  let Q := actualSelectedChartAlgebra P w
  have hcoeff : @algebraMap k B _ _ coords.coeff.toAlgebra =
      (algebraMap Q B).comp (algebraMap k Q) := by
    rw [coords.hcoeff]
    apply RingHom.ext
    intro c
    rfl
  apply RingHom.ext
  intro c
  have h := congrArg
    (fun f : Q →+* common.U => f (algebraMap k Q c)) common.hbaseMap
  change genericOpenExtraAwayBMap common.M setup.f setup.e common.g
      (algebraMap k B c) = algebraMap k common.U c
  rw [hcoeff]
  change genericOpenExtraAwayBMap common.M setup.f setup.e common.g
      (algebraMap Q B (algebraMap k Q c)) = _
  rw [h]
  rfl

/-- Construct the Laurent-series arc on the common open from the retained
ground-point tilt and its factor-avoidance certificate. -/
theorem exists_commonOpenArcData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (common : CommonOpenData hm P w setup coords) :
    Nonempty (CommonOpenArcData hm P w setup coords) := by
  classical
  letI : common.M.IsMaximal := common.hM
  let B := actualSelectedNormalization P w
  let Q := actualSelectedChartAlgebra P w
  let d := @Fintype.card coords.t coords.htFinite
  let coeff := coords.coeff
  let rhoA := originalToPointLocalFinSuccArcLaurentSeries
    (k := k) (d := d) (A := B) common.M common.eM common.alpha
  have hfactor := common.hfactor
  rcases hfactor with ⟨hf, hg, hcomp, hgroundB, hbadU, hrU, hq0U, hq1U⟩
  let hunitM : ∀ b, b ∉ common.M → IsUnit (rhoA b) := fun b hb => by
    exact pointLocalArc_unit_of_not_mem hm P w setup coords common b hb
  let rhoU := genericArcToGenericOpenExtraAwayB common.M setup.f setup.e
    rhoA hf hunitM common.g hg
  have hcomp' : rhoU.comp
      (genericOpenExtraAwayBMap common.M setup.f setup.e common.g) = rhoA := hcomp
  have hgroundB' :
      (rhoU.comp (genericOpenExtraAwayBMap common.M setup.f setup.e common.g)).comp
        (@algebraMap k B _ _ coeff.toAlgebra) =
      algebraMap k (LaurentSeries k) := hgroundB
  have hbaseMap := commonOpenMap_comp_groundMap hm P w setup coords common
  have hgroundU : rhoU.comp (algebraMap k common.U) =
      algebraMap k (LaurentSeries k) := by
    rw [← hbaseMap]
    exact hgroundB'
  exact ⟨{
    common := common
    rhoA := rhoA
    hcanonicalRhoA := rfl
    hf := hf
    hg := hg
    hunitM := hunitM
    rhoU := rhoU
    hcanonicalRhoU := rfl
    hcomp' := hcomp'
    hgroundB' := hgroundB'
    hbaseMap := hbaseMap
    hgroundU := hgroundU
    hbadU := hbadU
    hrU := hrU
    hq0U := hq0U
    hq1U := hq1U
  }⟩

end Stafford38.Geometry.SameWitness

end
