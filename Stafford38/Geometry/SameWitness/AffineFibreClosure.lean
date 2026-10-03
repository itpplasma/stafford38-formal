module
public import Stafford38.Geometry.SameWitness.EndpointOfAlgHoms
public import Stafford38.Geometry.SameWitness.ChartSetup
public import Stafford38.Geometry.SameWitness.CoordinatePresentation
public import Stafford38.Geometry.SameWitness.CommonOpen
public import Stafford38.Geometry.SameWitness.CommonOpenArc
public import Stafford38.Geometry.SameWitness.CommonOpenPositions
public import Stafford38.Geometry.SameWitness.CommonOpenColumns
public import Stafford38.Geometry.SameWitness.CommonOpenEtale

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ActualSameWitnessGroundPointCompletion
open Stafford38.Geometry.PrescribedAffineResidueCompletion
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

universe u

/-- Package the residue point and two completed unit series over abstract
normalization rings, using the retained coordinate and étale dictionaries. -/
private noncomputable def retainedClosureChartData
    {k B : Type u} [Field k] [CommRing B] {d : ℕ}
    (coeff : k →+* B)
    (fFin : @AlgHom k (MvPolynomial (Option (Fin d)) k) B _ _ _ _ coeff.toAlgebra)
    (hfinite : @Algebra.FiniteType k B _ _ coeff.toAlgebra)
    (M : Ideal B) (hM : M.IsMaximal)
    (eM : letI : Algebra k B := coeff.toAlgebra
      (B ⧸ M) ≃ₐ[k] k)
    (hEtM :
      letI : M.IsMaximal := hM
      let R := MvPolynomial (Option (Fin d)) k
      letI : Algebra k B := coeff.toAlgebra
      letI : Algebra.FiniteType k B := hfinite
      letI : Algebra R B := fFin.toRingHom.toAlgebra
      letI : IsScalarTower k R B := IsScalarTower.of_algHom fFin
      letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
      letI : Algebra R (Localization.AtPrime M) := inferInstance
      Algebra.FormallyEtale R (Localization.AtPrime M))
    (u₀ u₁ : Localization.AtPrime M) :
    ((Fin d → k) × MvPowerSeries (Fin (d + 1)) k) ×
      MvPowerSeries (Fin (d + 1)) k := by
  letI : M.IsMaximal := hM
  let R := MvPolynomial (Option (Fin d)) k
  letI : Algebra k B := coeff.toAlgebra
  letI : Algebra R B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := IsScalarTower.of_algHom fFin
  letI : Algebra.FiniteType k B := hfinite
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  letI : Algebra R (Localization.AtPrime M) := inferInstance
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  let chart := pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM
  exact ((fun z => residueCoordinates M eM (some z), chart u₀), chart u₁)

/-- Transport the retained lift by the chart coercion and computed tuple equalities. -/
private theorem retainedClosureChartData_lift
    {k B : Type u} [Field k] [CommRing B] {d : ℕ}
    (coeff : k →+* B)
    (fFin : @AlgHom k (MvPolynomial (Option (Fin d)) k) B _ _ _ _ coeff.toAlgebra)
    (hfinite : @Algebra.FiniteType k B _ _ coeff.toAlgebra)
    (M : Ideal B) (hM : M.IsMaximal)
    (eM : letI : Algebra k B := coeff.toAlgebra
      (B ⧸ M) ≃ₐ[k] k)
    (hEtM :
      letI : M.IsMaximal := hM
      let R := MvPolynomial (Option (Fin d)) k
      letI : Algebra k B := coeff.toAlgebra
      letI : Algebra.FiniteType k B := hfinite
      letI : Algebra R B := fFin.toRingHom.toAlgebra
      letI : IsScalarTower k R B := IsScalarTower.of_algHom fFin
      letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
      letI : Algebra R (Localization.AtPrime M) := inferInstance
      Algebra.FormallyEtale R (Localization.AtPrime M))
    (u₀ u₁ : Localization.AtPrime M) :
    letI : M.IsMaximal := hM
    let R := MvPolynomial (Option (Fin d)) k
    letI : Algebra k B := coeff.toAlgebra
    letI : Algebra R B := fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R B := IsScalarTower.of_algHom fFin
    letI : Algebra.FiniteType k B := hfinite
    letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
    letI : Algebra R (Localization.AtPrime M) := inferInstance
    letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
    ∀ {n : ℕ} (qT : Fin (n + 1) → Localization.AtPrime M)
    (rows : Fin d ↪ Fin (n + 1)) (chart zero axis : Fin (n + 1))
    (a b : ℕ) (alpha : Fin d → k)
    (qPre : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (hqPre : qPre = fun i => pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM (qT i)),
    Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.SelectedCoordinateAxisLiftData
      (fun i => localToFinSuccPowerSeries M eM (qT i)) rows chart zero axis a b
      (fun j => residueCoordinates M eM (some j)) alpha
      (localToFinSuccPowerSeries M eM u₀) (localToFinSuccPowerSeries M eM u₁) →
    let chartData := retainedClosureChartData coeff fFin hfinite M hM eM hEtM u₀ u₁
    Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.SelectedCoordinateAxisLiftData
      qPre rows chart zero axis a b chartData.1.1 alpha chartData.1.2 chartData.2 := by

  letI : M.IsMaximal := hM
  let R := MvPolynomial (Option (Fin d)) k
  letI : Algebra k B := coeff.toAlgebra
  letI : Algebra R B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := IsScalarTower.of_algHom fFin
  letI : Algebra.FiniteType k B := hfinite
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  letI : Algebra R (Localization.AtPrime M) := inferInstance
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  dsimp only
  intro n qT rows chart zero axis a b alpha qPre hqPre hdata
  have hchart (x : Localization.AtPrime M) :
      pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM x =
        localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM x := by
    unfold pointLocalPowerSeriesChart
    dsimp only [id_eq]
    exact congrFun (AlgHom.coe_toRingHom
      (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM)) x
  have hcolumns : (fun i => pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM (qT i)) =
      (fun i => localToFinSuccPowerSeries M eM (qT i)) := by
    funext i
    exact hchart (qT i)
  have htuple : retainedClosureChartData coeff fFin hfinite M hM eM hEtM u₀ u₁ =
      ((fun j => residueCoordinates M eM (some j), localToFinSuccPowerSeries M eM u₀),
        localToFinSuccPowerSeries M eM u₁) := by
    unfold retainedClosureChartData
    dsimp only
    rw [hchart, hchart]
  rw [hqPre, hcolumns, htuple]
  exact hdata

/-- The smooth affine-conormal axis lies in the fibre closure through the
retained ground-point output and its same-witness common-open arc. -/
theorem axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hpoint : actualSameWitnessGroundPointOutput hm P w)
    (hsmoothOpen : ∃ fbar : MvPolynomial (Fin m) k ⧸ P.asIdeal,
      fbar ≠ 0 ∧ Algebra.Smooth k (Localization.Away fbar)) :
    (fun i : Fin m => if i = (⟨0, hm⟩ : Fin m) then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection
            P.asIdeal)) := by
  classical
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
  obtain ⟨setup⟩ := nonempty_chartSetup hm P w hsmoothOpen
  obtain ⟨coords⟩ := nonempty_coordinatePresentation hm P w setup hpoint
  obtain ⟨common⟩ := nonempty_commonOpenData hm P w setup coords hpoint
  obtain ⟨arc⟩ := exists_commonOpenArcData hm P w setup coords common
  let arcData := arc.common
  obtain ⟨etale⟩ := nonempty_commonOpenEtaleData hm P w setup coords arc
  let positions := commonOpenPositionData_of_arc hm P w setup coords arc
  let cols := commonOpenColumnsData_of_arc hm P w setup coords arc etale positions
  let d := @Fintype.card coords.t coords.htFinite
  let chartData := retainedClosureChartData
    coords.coeff coords.fFin coords.hBfinite arcData.M arcData.hM
    arcData.eM arcData.hEtM arcData.u0 arcData.u1
  let beta := chartData.1.1
  let u₀ := chartData.1.2
  let u₁ := chartData.2
  have hchartPre : positions.qPre w.column.chart = 1 := by
    rw [setup.hchart]
    exact positions.hchartPre
  have hdata := retainedClosureChartData_lift
    coords.coeff coords.fFin coords.hBfinite arcData.M arcData.hM
    arcData.eM arcData.hEtM arcData.u0 arcData.u1
    arcData.qT coords.rows (Fin.succ setup.j) 0 (⟨0, hm⟩ : Fin m).succ
    w.differential.core.D.a (w.differential.core.D.a + w.differential.core.D.e)
    arcData.alpha positions.qPre positions.hqPre arcData.hdata
  rw [← setup.hchart] at hdata
  have hchartU : ∀ i : Fin m, arc.common.qU i.succ =
      arc.common.qU 0 * etale.φk (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) := by
    intro i
    calc
      _ = arc.common.qU 0 * arc.common.φ
          (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) := arcData.hchartU i
      _ = _ := congrArg (fun z => arc.common.qU 0 * z)
        (RingHom.congr_fun etale.hφAction
          (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i))).symm
  exact axis_mem_smoothConormalFibreProjection_closure_of_algHoms
    (k := k) (E := arc.common.U) (n := m) (d := d) (I := P.asIdeal)
    etale.φk etale.ψU etale.hφEtale etale.hψEtale arc.rhoU arc.hgroundU
    arc.common.qU positions.qPre coords.rows w.column.chart (⟨0, hm⟩ : Fin m)
    w.differential.core.D.a
    (w.differential.core.D.a + w.differential.core.D.e)
    beta arcData.alpha u₀ u₁ hchartPre hdata
    positions.hpositionL cols.htransverse cols.hraw hchartU
    setup.p setup.fbar setup.hrep setup.hsmooth cols.hnumerator

end Stafford38.Geometry.SameWitness

end
