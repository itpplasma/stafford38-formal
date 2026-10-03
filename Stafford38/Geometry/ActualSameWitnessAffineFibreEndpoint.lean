import Stafford38.Geometry.ActualAffineSmoothPointFromNumeratorCore
import Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
import Stafford38.Geometry.DirectSummandInputOfActualChart
import Stafford38.Geometry.GeneralTangentLimitCriterion
import Stafford38.Geometry.FormalDivisorLaurentConormal
import Stafford38.Geometry.HomogenizedAffineEvaluation

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Stafford38.Geometry.ActualSameWitnessAffineFibreEndpoint

open Stafford38.Geometry.ActualAffineSmoothPointFromNumerator
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.Geometry.HomogenizedAffineEvaluation
open Stafford38.Geometry.LocalizedProjectiveChartTransition

noncomputable section

universe u

/-- The original affine smooth-fibre axis endpoint follows from the same
common-open column identities used by the tangent calculation.  The selected
unit-power data supplies the nonzero zeroth coordinate; the actual
homogenized numerator supplies smoothness, and quotient evaluation supplies
the closure hypothesis needed by the existing direct-summand owner. -/
theorem axis_mem_smoothConormalFibreProjection_closure_of_actual_columns
    {k E : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing E] {n d : ℕ} {I : Ideal (MvPolynomial (Fin n) k)}
    [I.IsPrime] [Algebra k E]
    [Algebra (MvPolynomial (Fin n) k ⧸ I) E]
    [Algebra (MvPolynomial (Fin n) k) E]
    [Algebra (MvPolynomial (Option (Fin d)) k) E]
    [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) E]
    [IsScalarTower k (MvPolynomial (Fin n) k) E]
    [IsScalarTower k (MvPolynomial (Option (Fin d)) k) E]
    [IsScalarTower (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ I) E]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) E]
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) E]
    (rho : E →+* LaurentSeries k)
    (hground : rho.comp (algebraMap k E) = algebraMap k (LaurentSeries k)) :
    letI : Algebra E (LaurentSeries k) :=
      RingHom.toAlgebra' rho (by intro x y; exact mul_comm _ _)
    letI : Algebra k (LaurentSeries k) :=
      RingHom.toAlgebra' (algebraMap k (LaurentSeries k))
        (by intro x y; exact mul_comm _ _)
    letI : Module k (LaurentSeries k) := Algebra.toModule
    letI : SMul k (LaurentSeries k) :=
      (Algebra.toModule : Module k (LaurentSeries k)).toSMul
    letI : IsScalarTower k E (LaurentSeries k) :=
      IsScalarTower.of_algebraMap_eq' hground.symm
    ∀ (qC : Fin (n + 1) → E)
    (qPre : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (rows : Fin d ↪ Fin (n + 1)) (chart : Fin (n + 1)) (axis : Fin n)
    (a b : ℕ) (beta alpha : Fin d → k)
    (u₀ u₁ : MvPowerSeries (Fin (d + 1)) k)
    (hqchartPre : qPre chart = 1)
    (hdata : SelectedCoordinateAxisLiftData qPre rows chart 0 axis.succ
      a b beta alpha u₀ u₁)
    (hposition : ∀ i, rho (qC i) =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (tiltedArc alpha (qPre i)))
    (htransverse : ∀ j i,
      coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
        (L := LaurentSeries k) (some j) (qC i) =
        algebraMap (PowerSeries k) (LaurentSeries k)
          (tiltedTransverseDerivativeMatrix alpha qPre i j))
    (hraw : ∀ i,
      algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.derivative (R := k) (tiltedArc alpha (qPre i))) =
      coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
        (L := LaurentSeries k) none (qC i) +
        ∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
          (PowerSeries.C (alpha j)) *
            coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
              (L := LaurentSeries k) (some j) (qC i))
    (hchart : ∀ i : Fin n,
      qC i.succ = qC 0 *
        algebraMap (MvPolynomial (Fin n) k ⧸ I) E
          (Ideal.Quotient.mk I (MvPolynomial.X i)))
    (p : MvPolynomial (Fin n) k)
    (fbar : MvPolynomial (Fin n) k ⧸ I)
    (hrep : Ideal.Quotient.mk I p = fbar)
    (hsmooth : Algebra.Smooth k (Localization.Away fbar))
    (hnumerator : MvPolynomial.eval
      (laurentColumn (fun i => tiltedArc alpha (qPre i)))
      (MvPolynomial.map (algebraMap k (LaurentSeries k))
        (homogenizeAtZero p)) ≠ 0),
    (fun i : Fin n => if i = axis then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection I)) := by
  intro qC qPre rows chart axis a b beta alpha u₀ u₁ hqchartPre hdata
    hposition htransverse hraw hchart p fbar hrep hsmooth hnumerator
  letI : Algebra E (LaurentSeries k) :=
    RingHom.toAlgebra' rho (by intro x y; exact mul_comm _ _)
  letI : Algebra k (LaurentSeries k) :=
    RingHom.toAlgebra' (algebraMap k (LaurentSeries k))
      (by intro x y; exact mul_comm _ _)
  letI : Module k (LaurentSeries k) := Algebra.toModule
  letI : SMul k (LaurentSeries k) :=
    (Algebra.toModule : Module k (LaurentSeries k)).toSMul
  letI : IsScalarTower k E (LaurentSeries k) :=
    IsScalarTower.of_algebraMap_eq' hground.symm
  let q : Fin (n + 1) → PowerSeries k :=
    fun i => tiltedArc alpha (qPre i)
  let qL : Fin (n + 1) → LaurentSeries k := laurentColumn q
  rcases hdata with
    ⟨hzero, hunit₀, _, _, _, _, _, hexists⟩
  rcases hexists with
    ⟨c, tau, C, ell, hc, hrowDerivative, hTauChart, hTauRows,
      hfactor, hTauNonzero, hTauAxis, haxisColumns, hCB, hrowEll, hresidue⟩
  have hunitSeries : q 0 ≠ 0 := by
    change tiltedArc alpha (qPre 0) ≠ 0
    rw [hzero]
    have hu : tiltedArc alpha u₀ ≠ 0 := by
      intro hz
      apply hunit₀
      simpa [hz]
    exact mul_ne_zero (pow_ne_zero a (PowerSeries.X_ne_zero (R := k))) hu
  have hq0 : qL 0 ≠ 0 :=
    laurentColumn_ne_zero_of_ne_zero q hunitSeries
  have hqchart : q chart = 1 := by
    change tiltedArc alpha (qPre chart) = 1
    rw [hqchartPre]
    simp [tiltedArc]
  let φ : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] LaurentSeries k :=
    { toRingHom := rho.comp (algebraMap (MvPolynomial (Fin n) k ⧸ I) E)
      commutes' := by
        intro z
        change rho (algebraMap (MvPolynomial (Fin n) k ⧸ I) E
          (algebraMap k (MvPolynomial (Fin n) k ⧸ I) z)) =
            algebraMap k (LaurentSeries k) z
        rw [← IsScalarTower.algebraMap_apply k
          (MvPolynomial (Fin n) k ⧸ I) E z]
        exact congrArg (fun f : k →+* LaurentSeries k => f z) hground }
  have hpos : ∀ i, rho (qC i) = qL i := by
    intro i
    simpa [qL, laurentColumn, q] using hposition i
  have hq0rho : rho (qC 0) ≠ 0 := by
    rw [hpos 0]
    exact hq0
  have hdehom :
      dehomogenizedPoint qL =
        fun i => φ (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
    funext i
    rw [ProjectiveConormalDehomogenization.dehomogenizedPoint]
    calc
      qL i.succ / qL 0 = rho (qC i.succ) / rho (qC 0) := by
        rw [← hpos i.succ, ← hpos 0]
      _ = rho (algebraMap (MvPolynomial (Fin n) k ⧸ I) E
            (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
        rw [hchart i, map_mul]
        exact mul_div_cancel_left₀ _ hq0rho
      _ = φ (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
        simp [φ]
  have hsmoothPoint : SmoothAffinePoint
      (I.map (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin n)))
      (dehomogenizedPoint qL) :=
    smoothAffinePoint_of_homogenized_eval I p fbar hrep φ qL
      hdehom hq0 hsmooth hnumerator
  have hclosure : dehomogenizedPoint qL ∈
      MvPolynomial.zeroLocus (LaurentSeries k)
        (I.map (scalarPolynomialMap (k := k)
          (K := LaurentSeries k) (Fin n))) := by
    intro r hr
    obtain ⟨e, heval, _⟩ := hsmoothPoint
    have hmk : Ideal.Quotient.mk
        (I.map (scalarPolynomialMap (k := k)
          (K := LaurentSeries k) (Fin n))) r = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hr
    rw [← heval r, hmk, map_zero]
  have hq0chart : algebraMap E (LaurentSeries k) (qC 0) ≠ 0 := by
    change rho (qC 0) ≠ 0
    rw [hposition 0]
    exact hq0
  have hprime : I.IsPrime := inferInstance
  obtain ⟨D, hDaxis⟩ :=
    Stafford38.Geometry.DirectSummandInputOfActualChart.directSummandInput_of_actual_chart_columns
        (rho := rho) hground qC q
        (tiltedTransverseDerivativeMatrix alpha qPre) tau
        (fun j => PowerSeries.C (alpha j)) c hfactor
        hposition htransverse hraw hq0chart hchart chart hqchart hunitSeries axis C
        hCB haxisColumns hprime hclosure hsmoothPoint
  have hendpoint :=
    Stafford38.Geometry.GeneralTangentLimitCriterion.tangent_limit_affine_fibre_closure_of_directSummand
        I q (Stafford38.Geometry.PaperDivisorTangent.normalizedTangentLattice
          q (tiltedTransverseDerivativeMatrix alpha qPre) tau) D
  rw [hDaxis] at hendpoint
  exact hendpoint

end

end Stafford38.Geometry.ActualSameWitnessAffineFibreEndpoint
