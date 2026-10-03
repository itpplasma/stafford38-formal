module
public import Stafford38.Geometry.ActualPointAxisLift
public import Stafford38.Geometry.ActualOptionCommonOpenColumns
public import Stafford38.Geometry.DirectSummandInputOfActualChart
public import Stafford38.Geometry.A0ChartFormalEtale
public import Stafford38.Geometry.A0NormalizedProjectiveCoordinates
public import Stafford38.Geometry.SmoothAffinePointScalarExtension
public import Stafford38.Geometry.ActualCommonOpenCompletionDerivation

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualPointCommonOpenAssembly

open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.ActualOptionCommonOpenColumns
open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.Geometry.PaperDivisorTangent

universe u

/-- The prescribed local completion arc sends every element outside the
chosen maximal ideal to a unit. This is the localization property needed to
extend the same arc to the generic common open. -/
theorem pointLocalArc_unit_of_not_mem
    {k B : Type u} [Field k] {d : ℕ}
    [CommRing B] [Algebra k B]
    [Algebra (MvPolynomial (Option (Fin d)) k) B]
    [IsScalarTower k (MvPolynomial (Option (Fin d)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) B]
    (M : Ideal B) [M.IsMaximal]
    (eM : (B ⧸ M) ≃ₐ[k] k) (α : Fin d → k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (Localization.AtPrime M)]
    (b : B) (hb : b ∉ M) :
    IsUnit (originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := B) M eM α b) := by
  let T := Localization.AtPrime M
  have hu : IsUnit (algebraMap B T b) :=
    IsLocalization.map_units T (M := M.primeCompl) ⟨b, hb⟩
  exact IsUnit.map
    (pointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := B) M eM α).toRingHom hu

#print axioms pointLocalArc_unit_of_not_mem


/-- Turn one already-selected prescribed-point tilt and the three genuine
common-open column identities into the paper-facing direct-summand input.
The chart relation is the checked affine-overlap coordinate identity; closure
and smoothness are the two outputs of the same homogenized smooth-open
numerator argument. This wrapper does not choose a second tilt or assume a
tangent-cone identity. -/
theorem exists_directSummandInput_of_selected_axis_lift
    {k E : Type u} [Field k] [CommRing E] {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) k)}
    [Algebra k E]
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
      (a b : ℕ)
      (beta alpha : Fin d → k)
      (u₀ u₁ : MvPowerSeries (Fin (d + 1)) k)
      (hqchartPre : qPre chart = 1)
      (hdata : SelectedCoordinateAxisLiftData qPre rows chart 0 axis.succ a b
        beta alpha u₀ u₁)
      (hposition : ∀ i, rho (qC i) =
        algebraMap (PowerSeries k) (LaurentSeries k)
          (tiltedArc (k := k) alpha (qPre i)))
      (htransverse : ∀ j i,
        coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
          (L := LaurentSeries k) (some j) (qC i) =
          algebraMap (PowerSeries k) (LaurentSeries k)
            (tiltedTransverseDerivativeMatrix (k := k) alpha qPre i j))
      (hraw : ∀ i, algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.derivative (R := k) (tiltedArc (k := k) alpha (qPre i))) =
          coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
            (L := LaurentSeries k) none (qC i) +
          ∑ j : Fin d,
            algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C (alpha j)) *
              coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
                (L := LaurentSeries k) (some j) (qC i))
      (hchart : ∀ i, qC i.succ = qC 0 *
        algebraMap (MvPolynomial (Fin n) k ⧸ I) E
          (Ideal.Quotient.mk I (MvPolynomial.X i)))
      (hprime : I.IsPrime)
      (hclosure : dehomogenizedPoint (laurentColumn
        (fun i => tiltedArc (k := k) alpha (qPre i))) ∈
          MvPolynomial.zeroLocus (LaurentSeries k)
            (I.map (scalarPolynomialMap (k := k)
              (K := LaurentSeries k) (Fin n))))
      (hsmooth : SmoothAffinePoint
        (I.map (scalarPolynomialMap (k := k)
          (K := LaurentSeries k) (Fin n)))
        (dehomogenizedPoint (laurentColumn
          (fun i => tiltedArc (k := k) alpha (qPre i))))) ,
      ∃ (tau : Fin (n + 1) → PowerSeries k)
        (C : Matrix (FormalTangentColumn (Fin d)) (Fin (n + 1))
          (PowerSeries k)),
        C * formalTangentMatrix
            (fun i => tiltedArc (k := k) alpha (qPre i))
            (tiltedTransverseDerivativeMatrix (k := k) alpha qPre) tau = 1 ∧
        (∀ j, PowerSeries.constantCoeff
          (formalTangentMatrix
            (fun i => tiltedArc (k := k) alpha (qPre i))
            (tiltedTransverseDerivativeMatrix (k := k) alpha qPre)
            tau axis.succ j) = 0) ∧
        ∃ D : DirectSummandInput (dimY := d + 1) I
          (fun i => tiltedArc (k := k) alpha (qPre i))
          (normalizedTangentLattice
            (fun i => tiltedArc (k := k) alpha (qPre i))
            (tiltedTransverseDerivativeMatrix (k := k) alpha qPre) tau),
          D.axis = axis := by
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
  intro qC qPre rows chart axis a b beta alpha u₀ u₁ hqchartPre hdata
    hposition htransverse hraw hchart hprime hclosure hsmooth
  rcases hdata with ⟨hq0factor, hu₀, hqaxis, hu₁, hrowsArc, hminorRows,
    hdet, c, tau, C, ell, hc, hselected, htauChart, htauRows,
    hfactor, hprimitive, haxisZero, haxisColumns, hCB, hEll, hEllRes⟩
  let qArc : Fin (n + 1) → PowerSeries k :=
    fun i => tiltedArc (k := k) alpha (qPre i)
  let Z : Matrix (Fin (n + 1)) (Fin d) (PowerSeries k) :=
    tiltedTransverseDerivativeMatrix (k := k) alpha qPre
  have hqchart : qArc chart = 1 := by
    change tiltedArc (k := k) alpha (qPre chart) = 1
    rw [hqchartPre]
    exact map_one (tiltedArcMap (k := k) alpha)
  have hq0nonzero : qArc 0 ≠ 0 := by
    change tiltedArc (k := k) alpha (qPre 0) ≠ 0
    rw [hq0factor]
    have hu : tiltedArc (k := k) alpha u₀ ≠ 0 := by
      intro hz
      have hc0 := congrArg (PowerSeries.constantCoeff) hz
      exact hu₀ (by simpa using hc0)
    exact mul_ne_zero (pow_ne_zero a (PowerSeries.X_ne_zero)) hu
  have hq0chart :
      algebraMap E (LaurentSeries k) (qC 0) ≠ 0 := by
    have hq0map :
        algebraMap (PowerSeries k) (LaurentSeries k) (qArc 0) ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).ne
          hq0nonzero
    calc
      algebraMap E (LaurentSeries k) (qC 0) = rho (qC 0) :=
        congrArg (fun φ : E →+* LaurentSeries k => φ (qC 0))
          (RingHom.algebraMap_toAlgebra' rho (by intro x y; exact mul_comm _ _))
      _ = algebraMap (PowerSeries k) (LaurentSeries k) (qArc 0) := by
        simpa [qArc] using hposition 0
      _ ≠ 0 := hq0map
  have hcorrection : ∀ i,
      PowerSeries.derivative (R := k) (qArc i) - Z.mulVec
        (fun j => PowerSeries.C (alpha j)) i =
          (PowerSeries.X : PowerSeries k) ^ c * tau i := by
    simpa [qArc, Z] using hfactor
  have haxis : ∀ j,
      PowerSeries.constantCoeff
        (formalTangentMatrix qArc Z tau axis.succ j) = 0 := by
    simpa [qArc, Z] using haxisColumns
  refine ⟨tau, C, hCB, haxis, ?_⟩
  exact DirectSummandInputOfActualChart.directSummandInput_of_actual_chart_columns
    (rho := rho) hground qC qArc Z tau (fun j => PowerSeries.C (alpha j)) c
    hcorrection hposition htransverse hraw hq0chart hchart chart hqchart hq0nonzero
    axis C hCB haxis hprime hclosure hsmooth

#print axioms exists_directSummandInput_of_selected_axis_lift

end Stafford38.Geometry.ActualPointCommonOpenAssembly
end
