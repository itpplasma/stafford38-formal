import Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
import Stafford38.Geometry.ProjectiveChartNormalizationFinite
import Stafford38.Geometry.FiniteBirationalAway
import Stafford38.Geometry.SelectedResidueNormalizationLocalization

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

namespace Stafford38.Geometry.ActualSelectedNormalizationAway

open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.ActualChartNormalizationCenter
open Stafford38.Geometry.SelectedResidueCoefficientLocalization
open Stafford38.Geometry.ProjectiveChartNormalizationFinite
open Stafford38.Geometry.FiniteBirationalAway

universe u

/-- The normalization of the selected affine chart becomes the selected chart
itself after inverting one nonzero element of the chart domain. -/
theorem actual_selected_normalization_is_away_equiv
    {k : Type u} [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    ∃ f : actualSelectedChartAlgebra P w, f ≠ 0 ∧
      Nonempty
        (Localization.Away f ≃ₐ[actualSelectedChartAlgebra P w]
          Localization.Away
            (algebraMap (actualSelectedChartAlgebra P w)
              (actualSelectedNormalization P w) f)) := by
  let Q := actualSelectedChartAlgebra P w
  let F := ComponentFractionField P
  let B := actualSelectedNormalization P w
  letI : Algebra Q F := Q.val.toAlgebra
  let echart := chartAffineCoordinateEquiv w.column.chart
  have hchart : componentProjectivePoint P w.column.chart ≠ 0 := by
    have hscale : w.column.scale * componentProjectivePoint P w.column.chart = 1 := by
      simpa [w.column.chart_one] using (w.column.q_commonScale w.column.chart).symm
    intro hz
    rw [hz, mul_zero] at hscale
    exact one_ne_zero hscale.symm
  letI : Algebra Q.toSubring F := Q.toSubring.subtype.toAlgebra
  have hQfrac : IsFractionRing Q.toSubring F := by
    letI : IsFractionRing Q F :=
      chartGenericPointSubalgebra_isFractionRing P w.column.chart echart hchart
    letI : FaithfulSMul Q.toSubring F :=
      (faithfulSMul_iff_algebraMap_injective Q.toSubring F).mpr Subtype.val_injective
    apply IsFractionRing.of_field Q.toSubring F
    intro z
    obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective Q z
    let eqv := subalgebraToSubringRingEquiv Q
    refine ⟨eqv a, eqv b, ?_⟩
    change z = (eqv a : F) / (eqv b : F)
    calc
      z = (a : F) / (b : F) := hz.symm
      _ = (eqv a : F) / (eqv b : F) := by rfl
  letI : IsFractionRing Q.toSubring F := hQfrac
  letI : Algebra k Q.toSubring := Q.algebra
  have hQfinite : Algebra.FiniteType k Q.toSubring := by
    change Algebra.FiniteType k Q
    exact chartGenericPointSubalgebra_finiteType P w.column.chart echart
  letI : Algebra.FiniteType k Q.toSubring := hQfinite
  letI : Algebra Q.toSubring B := B.algebra
  have hfiniteSubring : Module.Finite Q.toSubring B := by
    change Module.Finite Q.toSubring (integralClosure Q.toSubring F)
    exact finite_integralClosure_in_fractionField k Q.toSubring F
  let eqv := subalgebraToSubringRingEquiv Q
  letI : Algebra Q.toSubring Q := eqv.symm.toRingHom.toAlgebra
  letI : Algebra Q B := (chartSubalgebraToIntegralClosure Q).toAlgebra
  have hTowerSubring : IsScalarTower Q.toSubring Q B := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    apply Subtype.ext
    rfl
  letI : IsScalarTower Q.toSubring Q B := hTowerSubring
  have hfinite : Module.Finite Q B :=
    Module.Finite.of_restrictScalars_finite Q.toSubring Q B
  letI : IsFractionRing Q F :=
    chartGenericPointSubalgebra_isFractionRing P w.column.chart
      (chartAffineCoordinateEquiv w.column.chart) hchart
  letI : Algebra B F := B.val.toAlgebra
  have hTowerQ : IsScalarTower Q B F := by
    refine IsScalarTower.of_algebraMap_eq fun q => ?_
    change (q : F) = ((chartSubalgebraToIntegralClosure Q q : B) : F)
    rw [coe_chartSubalgebraToIntegralClosure]
  exact @exists_nonzero_away_equiv_of_finite Q _ _ F _ _ _ B _ _ _
    hTowerQ hfinite Subtype.val_injective


end Stafford38.Geometry.ActualSelectedNormalizationAway
