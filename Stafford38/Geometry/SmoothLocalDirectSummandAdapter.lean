module
public import Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
public import Stafford38.Geometry.PaperDivisorTangent

@[expose] public section

/-!
# Conditional adapter from the smooth local axis lift

The full local lift constructs the split lattice, its rank, and its residue
axis condition.  It does not contain an affine ideal or generic geometry, so
the prime, arc equations, generic smoothness, and exact tangent-cone identity
remain explicit inputs here.
-/

namespace Stafford38.Geometry.SmoothLocalDirectSummandAdapter

set_option autoImplicit false

open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.PaperDivisorTangent
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometrySplitTangentMatrix

set_option maxHeartbeats 4000000

noncomputable section

variable {k : Type*} [Field k]

/-- Convert the relevant fields of the full smooth local axis-lift output into
the exact paper-facing direct-summand input.  `hCB` and `haxis` are output by
the lift; `hqzero` and `hu₀` are its zeroth-coordinate factorization and unit
coefficient.  The dimensions are independent: the ambient projective space
has dimension `n`, while the `d+2` split columns give `dimY=d+1`. -/
theorem directSummandInput_of_tiltedAxisLiftFields
    {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (α : Fin d → k)
    (chart : Fin (n + 1)) (axis : Fin n)
    (a : ℕ)
    (u₀ : MvPowerSeries (Fin (d + 1)) k)
    (hqchart : q chart = 1)
    (hqzero : tiltedArc (k := k) α (q 0) =
      (PowerSeries.X : PowerSeries k) ^ a * tiltedArc (k := k) α u₀)
    (hu₀ : PowerSeries.constantCoeff (tiltedArc (k := k) α u₀) ≠ 0)
    (tau : Fin (n + 1) → PowerSeries k)
    (C : Matrix (FormalTangentColumn (Fin d)) (Fin (n + 1)) (PowerSeries k))
    (hCB : C * formalTangentMatrix
      (fun i => tiltedArc (k := k) α (q i))
      (tiltedTransverseDerivativeMatrix (k := k) α q) tau = 1)
    (haxis : ∀ j, PowerSeries.constantCoeff
      (formalTangentMatrix
        (fun i => tiltedArc (k := k) α (q i))
        (tiltedTransverseDerivativeMatrix (k := k) α q) tau axis.succ j) = 0)
    (hprime : I.IsPrime)
    (hclosure : dehomogenizedPoint
      (laurentColumn (fun i => tiltedArc (k := k) α (q i))) ∈
      MvPolynomial.zeroLocus (LaurentSeries k)
        (I.map (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n))))
    (hsmooth : SmoothAffinePoint
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (dehomogenizedPoint
        (laurentColumn (fun i => tiltedArc (k := k) α (q i)))))
    (hcone : genericFibre (K := LaurentSeries k)
      (normalizedTangentLattice
        (fun i => tiltedArc (k := k) α (q i))
        (tiltedTransverseDerivativeMatrix (k := k) α q) tau) =
      projectiveTangentCone
        (laurentColumn (fun i => tiltedArc (k := k) α (q i)))
        (zariskiTangentSpace
          (dehomogenizedPoint
            (laurentColumn (fun i => tiltedArc (k := k) α (q i))))
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin n))))) :
    Nonempty (DirectSummandInput (dimY := d + 1) I
      (fun i => tiltedArc (k := k) α (q i))
      (normalizedTangentLattice
        (fun i => tiltedArc (k := k) α (q i))
        (tiltedTransverseDerivativeMatrix (k := k) α q) tau)) := by
  let qα : Fin (n + 1) → PowerSeries k :=
    fun i => tiltedArc (k := k) α (q i)
  let Zα : Matrix (Fin (n + 1)) (Fin d) (PowerSeries k) :=
    tiltedTransverseDerivativeMatrix (k := k) α q
  let Lα : Submodule (PowerSeries k) (Fin (n + 1) → PowerSeries k) :=
    normalizedTangentLattice qα Zα tau
  have hqchartα : qα chart = 1 := by
    dsimp [qα]
    rw [hqchart]
    simp [tiltedArc]
  have hq0 : qα 0 ≠ 0 := by
    rw [show qα 0 =
      (PowerSeries.X : PowerSeries k) ^ a * tiltedArc (k := k) α u₀ by
        simpa [qα] using hqzero]
    apply mul_ne_zero
    · exact pow_ne_zero a PowerSeries.X_ne_zero
    · intro hu
      apply hu₀
      rw [hu]
      simp
  have hq0Laurent : laurentColumn qα 0 ≠ 0 :=
    laurentColumn_ne_zero_of_ne_zero qα hq0
  have harc : FormalProjectiveArcInClosure I qα := by
    refine ⟨⟨chart, ?_⟩, ?_⟩
    · rw [hqchartα]
      exact isUnit_one
    · exact (projectiveClosureAtZero_iff
        (I.map (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n)))
        (laurentColumn qα) hq0Laurent).mpr hclosure
  have hCBα : C * formalTangentMatrix qα Zα tau = 1 := by
    simpa [qα, Zα] using hCB
  have haxisα : ∀ j, PowerSeries.constantCoeff
      (formalTangentMatrix qα Zα tau axis.succ j) = 0 := by
    simpa [qα, Zα] using haxis
  have hconeα : genericFibre (K := LaurentSeries k) Lα =
      projectiveTangentCone (laurentColumn qα)
        (zariskiTangentSpace (dehomogenizedPoint (laurentColumn qα))
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin n)))) := by
    simpa [qα, Zα, Lα] using hcone
  refine ⟨⟨axis,
    normalizedTangentLattice_isComplemented qα Zα tau C hCBα,
    ?_, hprime, hq0, harc, hsmooth, hconeα,
    normalizedTangentLattice_residue_axis qα Zα tau axis haxisα⟩⟩
  rw [normalizedTangentLattice_finrank qα Zα tau C hCBα]
  simp [FormalTangentColumn]
  omega

/-- The full local avoidance/lift theorem supplies the selected arc and its
split columns.  This wrapper packages them as the existing exact input once
the caller supplies the actual affine equations and the two generic
geometric assertions on the selected arc.  No second conclusion-carrying
record is introduced. -/
theorem exists_directSummandInput_of_tilted_local_axis_lift
    [Infinite k] [CharZero k]
    {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (bad : MvPowerSeries (Fin (d + 1)) k) (hbad : bad ≠ 0)
    (rows : Fin d ↪ Fin (n + 1))
    (chart : Fin (n + 1)) (axis : Fin n)
    (a b : ℕ)
    (u₀ u₁ : MvPowerSeries (Fin (d + 1)) k)
    (hqchart : q chart = 1)
    (ha : 0 < a) (hab : a < b)
    (hqzero : q 0 = (MvPowerSeries.X 0) ^ a * u₀)
    (hu₀ : MvPowerSeries.constantCoeff u₀ ≠ 0)
    (hqaxis : q axis.succ = (MvPowerSeries.X 0) ^ b * u₁)
    (hu₁ : MvPowerSeries.constantCoeff u₁ ≠ 0)
    (hminor : MvPowerSeries.constantCoeff
      (selectedMinor (localTransverseDerivativeMatrix (k := k) q) rows).det ≠ 0)
    (hprime : I.IsPrime)
    (hclosure : ∀ α : Fin d → k, tiltedArc (k := k) α bad ≠ 0 →
      dehomogenizedPoint
          (laurentColumn (fun i => tiltedArc (k := k) α (q i))) ∈
        MvPolynomial.zeroLocus (LaurentSeries k)
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin n))))
    (hsmooth : ∀ α : Fin d → k,
      tiltedArc (k := k) α bad ≠ 0 →
      SmoothAffinePoint
        (I.map (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n)))
        (dehomogenizedPoint
          (laurentColumn (fun i => tiltedArc (k := k) α (q i)))))
    (hcone : ∀ (α : Fin d → k), tiltedArc (k := k) α bad ≠ 0 →
      ∀ (lambda : Fin d → PowerSeries k) (c : ℕ)
        (tau : Fin (n + 1) → PowerSeries k)
        (C : Matrix (FormalTangentColumn (Fin d))
          (Fin (n + 1)) (PowerSeries k)),
      (∀ i, PowerSeries.derivative (R := k) (tiltedArc (k := k) α (q i)) -
          (tiltedTransverseDerivativeMatrix (k := k) α q).mulVec lambda i =
        (PowerSeries.X : PowerSeries k) ^ c * tau i) →
      C * formalTangentMatrix
          (fun i => tiltedArc (k := k) α (q i))
          (tiltedTransverseDerivativeMatrix (k := k) α q) tau = 1 →
      (∀ j, PowerSeries.constantCoeff
        (formalTangentMatrix
          (fun i => tiltedArc (k := k) α (q i))
          (tiltedTransverseDerivativeMatrix (k := k) α q) tau
          axis.succ j) = 0) →
      genericFibre (K := LaurentSeries k)
          (normalizedTangentLattice
            (fun i => tiltedArc (k := k) α (q i))
            (tiltedTransverseDerivativeMatrix (k := k) α q) tau) =
        projectiveTangentCone
          (laurentColumn (fun i => tiltedArc (k := k) α (q i)))
          (zariskiTangentSpace
            (dehomogenizedPoint
              (laurentColumn (fun i => tiltedArc (k := k) α (q i))))
            (I.map (scalarPolynomialMap
              (k := k) (K := LaurentSeries k) (Fin n))))) :
    ∃ α : Fin d → k, ∃ tau : Fin (n + 1) → PowerSeries k,
      Nonempty (DirectSummandInput (dimY := d + 1) I
        (fun i => tiltedArc (k := k) α (q i))
        (normalizedTangentLattice
          (fun i => tiltedArc (k := k) α (q i))
          (tiltedTransverseDerivativeMatrix (k := k) α q) tau)) := by
  obtain ⟨α, hbadArc, hqzeroArc, hu₀Arc, _hqaxisArc, _hu₁Arc,
      _hminorArc, _lambda, _c, tau, C, _ell, _hlambda, _hselected,
      _htauchart, _htauselected, _hc, hfactor, _hprimitive, _htauaxis,
      haxiscolumns, hCB, _hell, _hellres⟩ :=
    exists_tilted_local_axis_lift (k := k) q bad hbad rows chart 0 axis.succ
      a b u₀ u₁ hqchart ha hab hqzero hu₀ hqaxis hu₁ hminor
  have hgenericCone := hcone α hbadArc _lambda _c tau C hfactor hCB haxiscolumns
  exact ⟨α, tau,
    directSummandInput_of_tiltedAxisLiftFields
      I q α chart axis a u₀ hqchart hqzeroArc hu₀Arc tau C hCB
      haxiscolumns hprime (hclosure α hbadArc) (hsmooth α hbadArc) hgenericCone⟩

end

end Stafford38.Geometry.SmoothLocalDirectSummandAdapter
