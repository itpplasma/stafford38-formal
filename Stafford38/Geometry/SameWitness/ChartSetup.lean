module
public import Stafford38.Geometry.GeneralDivisorialVisibleFrame
public import Stafford38.Geometry.ActualSelectedNormalizationAway
public import Stafford38.Geometry.ActualSmoothOpenChartNumerator
public import Stafford38.Geometry.ActualWitnessSelectedChartIndex

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.ActualSelectedNormalizationAway
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.ActualSmoothOpenChartNumerator
open Stafford38.Geometry.ActualWitnessSelectedChartIndex
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.LocalizedProjectiveChartTransition
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.SelectedResidueCoefficientLocalization

universe u

/-- The chart, smooth affine open, and homogenized numerator data retained
from one same-witness construction. The smooth open is the original affine
component open used in the paper's conormal closure argument. -/
structure ChartSetup
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) where
  fbar : MvPolynomial (Fin m) k ⧸ P.asIdeal
  hfbar : fbar ≠ 0
  p : MvPolynomial (Fin m) k
  hrep : Ideal.Quotient.mk P.asIdeal p = fbar
  hp : Ideal.Quotient.mk P.asIdeal p ≠ 0
  hsmooth : Algebra.Smooth k (Localization.Away fbar)
  j : Fin m
  hchart : w.column.chart = Fin.succ j
  f : actualSelectedChartAlgebra P w
  hf : f ≠ 0
  e : Localization.Away f ≃ₐ[actualSelectedChartAlgebra P w]
    Localization.Away
      (algebraMap (actualSelectedChartAlgebra P w)
        (actualSelectedNormalization P w) f)
  r : actualSelectedChartAlgebra P w
  hr : r ≠ 0
  hrF : (r : ComponentFractionField P) = MvPolynomial.eval
    (fun a : Fin (m + 1) => (w.column.q a : ComponentFractionField P))
    (MvPolynomial.map (algebraMap k (ComponentFractionField P))
      (homogenizeAtZero p))
  hrformula : (r : ComponentFractionField P) =
    (w.column.q 0 : ComponentFractionField P) ^
      (MvPolynomial.map (algebraMap k (ComponentFractionField P)) p).totalDegree *
        componentAffineGenericPointMap P p
  qToB_injective : Function.Injective
    (chartSubalgebraToIntegralClosure (actualSelectedChartAlgebra P w))
  fB_mul_rB_ne_zero :
    chartSubalgebraToIntegralClosure (actualSelectedChartAlgebra P w) f *
      chartSubalgebraToIntegralClosure (actualSelectedChartAlgebra P w) r ≠ 0

/-- The same-witness chart setup exists from a smooth principal open of the
original affine component. -/
theorem nonempty_chartSetup
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hsmoothOpen : ∃ fbar : MvPolynomial (Fin m) k ⧸ P.asIdeal,
      fbar ≠ 0 ∧ Algebra.Smooth k (Localization.Away fbar)) :
    Nonempty (ChartSetup hm P w) := by
  classical
  obtain ⟨fbar, hfbar, hsmooth⟩ := hsmoothOpen
  obtain ⟨p, hrep⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) fbar
  have hp : Ideal.Quotient.mk P.asIdeal p ≠ 0 := by
    rw [hrep]
    exact hfbar
  obtain ⟨j, hchart⟩ := exists_succ_chart_index hm P w
  obtain ⟨f, hf, he⟩ := actual_selected_normalization_is_away_equiv P w
  let e := Classical.choice he
  obtain ⟨r, hrF, hrformula, hr⟩ :=
    exists_nonzero_homogenized_numerator hm P w p hp
  let Q := actualSelectedChartAlgebra P w
  let qToB : Q →+* actualSelectedNormalization P w :=
    chartSubalgebraToIntegralClosure Q
  have hqToB_injective : Function.Injective qToB := by
    intro x y hxy
    apply Subtype.ext
    calc
      (x : ComponentFractionField P) = ((qToB x : actualSelectedNormalization P w) :
          ComponentFractionField P) :=
        (coe_chartSubalgebraToIntegralClosure Q x).symm
      _ = ((qToB y : actualSelectedNormalization P w) :
          ComponentFractionField P) := congrArg
            (fun z : actualSelectedNormalization P w => (z : ComponentFractionField P)) hxy
      _ = (y : ComponentFractionField P) := coe_chartSubalgebraToIntegralClosure Q y
  have hfB : qToB f ≠ 0 := by
    intro hz
    apply hf
    apply hqToB_injective
    simpa using hz
  have hrB : qToB r ≠ 0 := by
    intro hz
    apply hr
    apply hqToB_injective
    simpa using hz
  have hbad : qToB f * qToB r ≠ 0 := mul_ne_zero hfB hrB
  exact ⟨{
    fbar := fbar
    hfbar := hfbar
    p := p
    hrep := hrep
    hp := hp
    hsmooth := hsmooth
    j := j
    hchart := hchart
    f := f
    hf := hf
    e := e
    r := r
    hr := hr
    hrF := hrF
    hrformula := hrformula
    qToB_injective := hqToB_injective
    fB_mul_rB_ne_zero := hbad
  }⟩

end Stafford38.Geometry.SameWitness

end
