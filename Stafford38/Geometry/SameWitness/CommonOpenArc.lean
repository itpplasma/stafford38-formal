module
public import Stafford38.Geometry.SameWitness.CommonOpen

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.ActualCommonOpenArcCompatibility
open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

universe u

/-- A Laurent arc on a point-local normalization extends to its common open,
retaining its ground map and nonzero factors. -/
structure CommonOpenArcTransport
    {k A Q : Type u} [Field k] [CommRing A] [CommRing Q]
    [Algebra k Q] [Algebra Q A]
    (M : Ideal A) [M.IsMaximal] (f : Q)
    (e : Localization.Away f ≃ₐ[Q] Localization.Away (algebraMap Q A f))
    (g : Q) (coeff : k →+* A) (canonical : A →+* LaurentSeries k)
    (bad rB q0 q1 : A) where
  rhoA : A →+* LaurentSeries k
  hcanonicalRhoA : rhoA = canonical
  hf : IsUnit (rhoA (algebraMap (Q)
    (A) f))
  hg : IsUnit (rhoA (algebraMap (Q)
    (A) g))
  hunitM : ∀ b, b ∉ M → IsUnit (rhoA b)
  rhoU : genericOpenExtraAwayB M f e g →+* LaurentSeries k
  hcanonicalRhoU :
    rhoU = genericArcToGenericOpenExtraAwayB
    M f e rhoA hf hunitM g hg
  hcomp' :
    rhoU.comp
      (genericOpenExtraAwayBMap M f e g) = rhoA
  hgroundB' :
    (rhoU.comp
      (genericOpenExtraAwayBMap M f e g)).comp
      coeff =
    algebraMap k (LaurentSeries k)
  hbaseMap :
    (genericOpenExtraAwayBMap M f e g).comp
      coeff =
    algebraMap k (genericOpenExtraAwayB M f e g)
  hgroundU : rhoU.comp (algebraMap k (genericOpenExtraAwayB M f e g)) = algebraMap k (LaurentSeries k)
  hbadU :
    rhoU (genericOpenExtraAwayBMap M f e g
    bad) ≠ 0
  hrU :
    rhoU (genericOpenExtraAwayBMap M f e g
    rB) ≠ 0
  hq0U :
    rhoU (genericOpenExtraAwayBMap M f e g
    q0) ≠ 0
  hq1U :
    rhoU (genericOpenExtraAwayBMap M f e g
      q1) ≠ 0


/-- Elements outside the maximal center become units under the retained
point-local Laurent arc. -/
private theorem pointLocalArc_unit_of_not_mem
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] {d : ℕ}
    [Algebra (MvPolynomial (Option (Fin d)) k) A]
    [IsScalarTower k (MvPolynomial (Option (Fin d)) k) A]
    [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) A]
    (M : Ideal A) [M.IsMaximal]
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) (Localization.AtPrime M)]
    (eM : (A ⧸ M) ≃ₐ[k] k) (alpha : Fin d → k)
    (b : A) (hb : b ∉ M) :
    IsUnit (originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := A) M eM alpha b) := by
  exact IsUnit.map
    (pointLocalFinSuccArcLaurentSeries (k := k) (d := d) (A := A) M eM alpha).toRingHom
    (IsLocalization.map_units (Localization.AtPrime M) (M := M.primeCompl) ⟨b, hb⟩)

/-- The tilted-product factors determine the Laurent arc transport and its
restriction to the ground field (paper proof, common-open arc step). -/
private theorem exists_commonOpenArcTransport
    {k A Q : Type u} [Field k] [CommRing A] [CommRing Q]
    [Algebra k A] [Algebra k Q] [Algebra Q A] {d : ℕ}
    [Algebra (MvPolynomial (Option (Fin d)) k) A]
    [IsScalarTower k (MvPolynomial (Option (Fin d)) k) A]
    [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) A]
    (M : Ideal A) [M.IsMaximal]
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) (Localization.AtPrime M)]
    (f : Q) (e : Localization.Away f ≃ₐ[Q] Localization.Away (algebraMap Q A f))
    (g : Q) (eM : (A ⧸ M) ≃ₐ[k] k) (alpha : Fin d → k)
    (bad rB q0 q1 : A)
    (hfactor : CommonOpenArcFactors M f e g eM alpha bad rB q0 q1)
    (hbaseMap : (genericOpenExtraAwayBMap M f e g).comp (algebraMap k A) =
      algebraMap k (genericOpenExtraAwayB M f e g)) :
    Nonempty (CommonOpenArcTransport M f e g (algebraMap k A)
      (originalToPointLocalFinSuccArcLaurentSeries (k := k) (d := d) (A := A) M eM alpha)
      bad rB q0 q1) := by
  classical
  let rhoA := originalToPointLocalFinSuccArcLaurentSeries
    (k := k) (d := d) (A := A) M eM alpha
  unfold CommonOpenArcFactors at hfactor
  rcases hfactor with ⟨hf, hg, hcomp, hgroundB, hbadU, hrU, hq0U, hq1U⟩
  let hunitM : ∀ b, b ∉ M → IsUnit (rhoA b) := fun b hb =>
    pointLocalArc_unit_of_not_mem M eM alpha b hb
  let rhoU := genericArcToGenericOpenExtraAwayB M f e rhoA hf hunitM g hg
  have hgroundU : rhoU.comp (algebraMap k (genericOpenExtraAwayB M f e g)) =
      algebraMap k (LaurentSeries k) := by
    exact (congrArg (fun h => rhoU.comp h) hbaseMap).symm.trans hgroundB
  exact ⟨{
    rhoA := rhoA, hcanonicalRhoA := rfl
    hf := hf, hg := hg, hunitM := hunitM
    rhoU := rhoU, hcanonicalRhoU := rfl
    hcomp' := hcomp, hgroundB' := hgroundB, hbaseMap := hbaseMap
    hgroundU := hgroundU, hbadU := hbadU, hrU := hrU
    hq0U := hq0U, hq1U := hq1U
  }⟩

/-- The retained ground-point arc and its common-open transport keep the
same normalization witness (paper proof, common-open arc step). -/
structure CommonOpenArcData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup) where
  common : CommonOpenData hm P w setup coords
  transport :
    letI : Algebra
        (Stafford38.Geometry.AsymptoticDivisorExistence.CoordinateZeroLocalRing
          w.column.W.coefficientField)
        (Stafford38.Geometry.ComponentProjectiveClosure.ComponentFractionField P) :=
      w.column.W.ambientAlgebra
    letI : IsLocalRing w.column.W.place.valuation.toSubring :=
      w.column.W.place.isDiscrete.toIsLocalRing
    letI : common.M.IsMaximal := common.hM
    let B := actualSelectedNormalization P w
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    letI : Algebra k B := coords.coeff.toAlgebra
    letI : Algebra R B := coords.fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R B := IsScalarTower.of_algHom coords.fFin
    letI : Algebra.FiniteType k B := coords.hBfinite
    letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
    letI : Algebra R (Localization.AtPrime common.M) := inferInstance
    letI : Algebra.FormallyEtale R (Localization.AtPrime common.M) := common.hEtM
    CommonOpenArcTransport common.M setup.f setup.e common.g
      (@algebraMap k B _ _ coords.coeff.toAlgebra)
      (originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := @Fintype.card coords.t coords.htFinite)
        (A := B) common.M common.eM common.alpha)
      (algebraMap (actualSelectedChartAlgebra P w) B setup.f *
        algebraMap (actualSelectedChartAlgebra P w) B setup.r)
      (algebraMap (actualSelectedChartAlgebra P w) B setup.r)
      (Stafford38.Geometry.ActualOptionColumnBinding.actualNormalizedProjectiveColumnInIntegralClosure hm P w 0)
      (Stafford38.Geometry.ActualOptionColumnBinding.actualNormalizedProjectiveColumnInIntegralClosure hm P w
        (Fin.succ (⟨0, hm⟩ : Fin m)))

namespace CommonOpenArcData
variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {m : ℕ} {hm : 0 < m} {P : PrimeSpectrum (MvPolynomial (Fin m) k)}
  {w : GeneralDivisorialVisibleFrameWitness hm P} {setup : ChartSetup hm P w}
  {coords : CoordinatePresentation hm P w setup}
abbrev rhoA (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.rhoA
abbrev hcanonicalRhoA (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hcanonicalRhoA
abbrev hf (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hf
abbrev hg (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hg
abbrev hunitM (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hunitM
abbrev rhoU (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.rhoU
abbrev hcanonicalRhoU (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hcanonicalRhoU
abbrev hcomp' (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hcomp'
abbrev hgroundB' (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hgroundB'
abbrev hbaseMap (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hbaseMap
abbrev hgroundU (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hgroundU
abbrev hbadU (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hbadU
abbrev hrU (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hrU
abbrev hq0U (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hq0U
abbrev hq1U (arc : CommonOpenArcData hm P w setup coords) :=
  letI : arc.common.M.IsMaximal := arc.common.hM
  arc.transport.hq1U
end CommonOpenArcData

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
  calc
    genericOpenExtraAwayBMap common.M setup.f setup.e common.g
        (coords.coeff c) =
      genericOpenExtraAwayBMap common.M setup.f setup.e common.g
        (algebraMap Q B (algebraMap k Q c)) :=
          congrArg (genericOpenExtraAwayBMap common.M setup.f setup.e common.g)
            (RingHom.congr_fun hcoeff c)
    _ = (algebraMap common.Cq common.U)
        (algebraMap Q common.Cq (algebraMap k Q c)) := h
    _ = algebraMap k common.U c := by
      exact (congrArg (algebraMap common.Cq common.U)
        (IsScalarTower.algebraMap_apply k Q common.Cq c).symm).trans
          (IsScalarTower.algebraMap_apply k common.Cq common.U c).symm

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
  refine ⟨{ common := common, transport := ?_ }⟩
  apply Classical.choice
  apply @exists_commonOpenArcTransport k B Q
    inferInstance inferInstance inferInstance coords.coeff.toAlgebra
    (inferInstance : Algebra k Q) (inferInstance : Algebra Q B)
    (@Fintype.card coords.t coords.htFinite)
    (@RingHom.toAlgebra
      (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k) B
      inferInstance inferInstance
      (@AlgHom.toRingHom k
        (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k) B
        inferInstance inferInstance inferInstance inferInstance
        coords.coeff.toAlgebra coords.fFin))
    (@IsScalarTower.of_algHom k
      (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k) B
      inferInstance inferInstance inferInstance inferInstance
      coords.coeff.toAlgebra coords.fFin)
    (@essFiniteType_of_coordinateMap k B inferInstance inferInstance
      coords.coeff.toAlgebra coords.hBfinite
      (@Fintype.card coords.t coords.htFinite) coords.fFin)
    common.M common.hM common.hEtM
  · exact common.hfactor
  · exact commonOpenMap_comp_groundMap hm P w setup coords common

end Stafford38.Geometry.SameWitness

end
