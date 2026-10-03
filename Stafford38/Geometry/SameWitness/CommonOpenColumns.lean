module
public import Stafford38.Geometry.SameWitness.CommonOpenPositions
public import Stafford38.Geometry.SameWitness.CommonOpenEtale
public import Stafford38.Geometry.CommonOpenEvaluation

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.ActualOptionCommonOpenColumns
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.CommonOpenEvaluation
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.HomogenizedAffineEvaluation
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.LocalizedProjectiveChartTransition

universe u

/-- The retained witness columns satisfy the common-open derivative and
selected-numerator identities required by the endpoint. -/
structure CommonOpenColumnsData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords)
    (etale : CommonOpenEtaleData hm P w setup coords arc)
    (positions : CommonOpenPositionData hm P w setup coords arc) where
  htransverse :
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    letI : Algebra R arc.common.U := etale.ψU.toRingHom.toAlgebra
    letI : Algebra k arc.common.U := Algebra.compHom arc.common.U (algebraMap k R)
    letI : IsScalarTower k R arc.common.U :=
      IsScalarTower.of_algebraMap_eq' etale.ψU.comp_algebraMap.symm
    letI : Algebra.FormallyEtale R arc.common.U := etale.hψEtale
    letI : Algebra arc.common.U (LaurentSeries k) :=
      RingHom.toAlgebra' arc.rhoU (by intro x y; exact mul_comm _ _)
    letI : Algebra k (LaurentSeries k) :=
      RingHom.toAlgebra' (algebraMap k (LaurentSeries k))
        (by intro x y; exact mul_comm _ _)
    letI : IsScalarTower k arc.common.U (LaurentSeries k) :=
      IsScalarTower.of_algebraMap_eq' arc.hgroundU.symm
    letI : IsScalarTower arc.common.U (LaurentSeries k) (LaurentSeries k) :=
      ⟨fun x y z => by
        change (algebraMap arc.common.U (LaurentSeries k) x * y) * z = _
        exact mul_assoc _ _ _⟩
    ∀ j i, coordinateDerivation (k := k)
    (σ := Option (Fin (@Fintype.card coords.t coords.htFinite)))
    (B := arc.common.U) (L := LaurentSeries k) (some j)
    (arc.common.qU i) = algebraMap (PowerSeries k) (LaurentSeries k)
      (tiltedTransverseDerivativeMatrix arc.common.alpha positions.qPre i j)
  hraw :
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    letI : Algebra R arc.common.U := etale.ψU.toRingHom.toAlgebra
    letI : Algebra k arc.common.U := Algebra.compHom arc.common.U (algebraMap k R)
    letI : IsScalarTower k R arc.common.U :=
      IsScalarTower.of_algebraMap_eq' etale.ψU.comp_algebraMap.symm
    letI : Algebra.FormallyEtale R arc.common.U := etale.hψEtale
    letI : Algebra arc.common.U (LaurentSeries k) :=
      RingHom.toAlgebra' arc.rhoU (by intro x y; exact mul_comm _ _)
    letI : Algebra k (LaurentSeries k) :=
      RingHom.toAlgebra' (algebraMap k (LaurentSeries k))
        (by intro x y; exact mul_comm _ _)
    letI : IsScalarTower k arc.common.U (LaurentSeries k) :=
      IsScalarTower.of_algebraMap_eq' arc.hgroundU.symm
    letI : IsScalarTower arc.common.U (LaurentSeries k) (LaurentSeries k) :=
      ⟨fun x y z => by
        change (algebraMap arc.common.U (LaurentSeries k) x * y) * z = _
        exact mul_assoc _ _ _⟩
    ∀ i, algebraMap (PowerSeries k) (LaurentSeries k)
      (PowerSeries.derivative (R := k)
        (tiltedArc arc.common.alpha (positions.qPre i))) =
    coordinateDerivation (k := k)
      (σ := Option (Fin (@Fintype.card coords.t coords.htFinite)))
      (B := arc.common.U) (L := LaurentSeries k) none (arc.common.qU i) +
      ∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.C (arc.common.alpha j)) *
        coordinateDerivation (k := k)
          (σ := Option (Fin (@Fintype.card coords.t coords.htFinite)))
          (B := arc.common.U) (L := LaurentSeries k) (some j)
          (arc.common.qU i)
  hnumerator : MvPolynomial.eval positions.qL
      (MvPolynomial.map (algebraMap k (LaurentSeries k))
        (homogenizeAtZero setup.p)) ≠ 0

/-- Derive derivatives and numerator nonvanishing from the same point-local
columns, arc, and smooth chart retained by the upstream packages. -/
theorem commonOpenColumnsData_of_arc
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords)
    (etale : CommonOpenEtaleData hm P w setup coords arc)
    (positions : CommonOpenPositionData hm P w setup coords arc) :
    CommonOpenColumnsData hm P w setup coords arc etale positions := by
  classical
  let d := @Fintype.card coords.t coords.htFinite
  let B := actualSelectedNormalization P w
  let F := ComponentFractionField P
  let R := MvPolynomial (Option (Fin d)) k
  let g := arc.common.g
  let U := arc.common.U
  let qB : Fin (m + 1) → B := actualNormalizedProjectiveColumnInIntegralClosure hm P w
  have hqBspec := actualNormalizedProjectiveColumnInIntegralClosure_spec hm P w
  have hqBf : ∀ a, ((qB a : B) : ComponentFractionField P) =
      ((w.column.q a : w.column.W.place.valuation.toSubring) : ComponentFractionField P) := by
    simpa [qB] using hqBspec.2.1
  have hf := arc.hf
  rw [arc.hcanonicalRhoA] at hf
  have hunitM := arc.hunitM
  rw [arc.hcanonicalRhoA] at hunitM
  have hg := arc.hg
  rw [arc.hcanonicalRhoA] at hg
  letI : Algebra k B := coords.coeff.toAlgebra
  letI : Algebra R B := coords.fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
    ext c; exact (coords.fFin.commutes c).symm)
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  letI : Algebra R (Localization.AtPrime arc.common.M) := inferInstance
  letI : Algebra.FormallyEtale R (Localization.AtPrime arc.common.M) := arc.common.hEtM
  letI : Algebra R (genericOpenRing arc.common.M setup.f setup.e) :=
    ((algebraMap B (genericOpenRing arc.common.M setup.f setup.e)).comp
      (algebraMap R B)).toAlgebra
  letI : Algebra R U := Algebra.compHom U
    (algebraMap R (genericOpenRing arc.common.M setup.f setup.e))
  letI : Algebra k U := Algebra.compHom U (algebraMap k R)
  letI : IsScalarTower k R U := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    rfl
  letI : Algebra.FormallyEtale R U := by
    simpa [U, genericOpenRing] using
      formallyEtale_genericOpenExtraAway_of_pointLocal arc.common.M setup.f setup.e g
  have hcols := actual_option_columns (k := k) (d := d) (A := B)
    arc.common.M setup.f setup.e g arc.common.eM arc.common.alpha hf hunitM hg
    m arc.common.qT arc.common.qU arc.common.hqUPoint
  rcases hcols with ⟨_, ⟨htransverseUU, hrawUU⟩⟩
  have hcolumnsL := actual_option_columns_to_laurent
    (k := k) (d := d) (A := B) (U := U) (M := arc.common.M)
    arc.common.eM (algebraMap (PowerSeries k) (LaurentSeries k)) arc.rhoU
    arc.hgroundU arc.common.alpha arc.common.qT arc.common.qU
    (by
      intro i
      rw [arc.hcanonicalRhoU]
      exact positions.hpositionL i)
    htransverseUU hrawUU
  rcases hcolumnsL with ⟨_, ⟨htransverse, hraw⟩⟩
  have hgroundCoeff : (algebraMap B F).comp (algebraMap k B) =
      algebraMap k F := by
    ext c
    change ((coords.coeff c : B) : F) = algebraMap k F c
    rw [coords.hcoeff]
    rfl
  have hEvalB : MvPolynomial.eval₂ (algebraMap k B) qB
      (homogenizeAtZero setup.p) = algebraMap
        (actualSelectedChartAlgebra P w) B setup.r := by
    apply Subtype.ext
    change MvPolynomial.eval₂ (algebraMap k F) (fun a => (qB a : F))
        (homogenizeAtZero setup.p) = (setup.r : F)
    calc
      _ = MvPolynomial.eval₂
          ((algebraMap B F).comp (algebraMap k B))
          (fun a => algebraMap B F (qB a)) (homogenizeAtZero setup.p) := by
            exact (MvPolynomial.eval₂_comp_left (algebraMap B F)
              (algebraMap k B) qB (homogenizeAtZero setup.p)).symm
      _ = MvPolynomial.eval₂ (algebraMap k F)
          (fun a => (w.column.q a : F)) (homogenizeAtZero setup.p) := by
            rw [hgroundCoeff]
            congr 1
            funext a
            exact hqBf a
      _ = MvPolynomial.eval (fun a => (w.column.q a : F))
          (MvPolynomial.map (algebraMap k F) (homogenizeAtZero setup.p)) := by
            exact (MvPolynomial.eval_map (algebraMap k F)
              (fun a => (w.column.q a : F)) (homogenizeAtZero setup.p)).symm
      _ = (setup.r : F) := setup.hrF.symm
  have hEval := eval_map_eq_arc_eval₂
    (genericOpenExtraAwayBMap arc.common.M setup.f setup.e g) arc.rhoU
    arc.hgroundB' qB arc.common.qU positions.qL
    positions.hcoords positions.hpositionL (homogenizeAtZero setup.p)
  have hnumerator : MvPolynomial.eval positions.qL
      (MvPolynomial.map (algebraMap k (LaurentSeries k))
        (homogenizeAtZero setup.p)) ≠ 0 := by
    rw [hEval, hEvalB]
    exact arc.hrU
  have htransverse' : ∀ j i, coordinateDerivation (k := k)
      (σ := Option (Fin d)) (B := U) (L := LaurentSeries k) (some j)
      (arc.common.qU i) = algebraMap (PowerSeries k) (LaurentSeries k)
        (tiltedTransverseDerivativeMatrix arc.common.alpha positions.qPre i j) := by
    rw [← etale.hψAction]
    exact htransverse
  have hraw' : ∀ i, algebraMap (PowerSeries k) (LaurentSeries k)
      (PowerSeries.derivative (R := k)
        (tiltedArc arc.common.alpha (positions.qPre i))) =
    coordinateDerivation (k := k) (σ := Option (Fin d))
      (B := U) (L := LaurentSeries k) none (arc.common.qU i) +
      ∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.C (arc.common.alpha j)) *
        coordinateDerivation (k := k) (σ := Option (Fin d))
          (B := U) (L := LaurentSeries k) (some j) (arc.common.qU i) := by
    rw [← etale.hψAction]
    exact hraw
  exact ⟨htransverse', hraw', hnumerator⟩

end Stafford38.Geometry.SameWitness

end
