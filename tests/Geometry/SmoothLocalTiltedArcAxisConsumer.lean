module
public import Stafford38.Geometry.SmoothLocalTiltedArcAxisLift

@[expose] public section

open Stafford38.GeometrySplitTangentMatrix
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryRetractionSpecialization
open Stafford38.GeometryPowerSeriesTangentLimit
set_option autoImplicit false
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift

noncomputable section

private def literalQ : Fin 4 → MvPowerSeries (Fin 2) ℚ := fun i =>
  if i = 0 then MvPowerSeries.X 0 else
  if i = 1 then (MvPowerSeries.X 0) ^ 2 else
  if i = 2 then 1 else MvPowerSeries.X 1

private def literalBad : MvPowerSeries (Fin 2) ℚ :=
  MvPowerSeries.X 1

private def literalRows : Fin 1 ↪ Fin 4 :=
  ⟨fun _ => 3, by intro i j h; exact Subsingleton.elim _ _⟩

private theorem literalMinor : MvPowerSeries.constantCoeff
    (selectedMinor (localTransverseDerivativeMatrix literalQ) literalRows).det ≠ 0 := by
  rw [Matrix.det_fin_one]
  change MvPowerSeries.constantCoeff
    (MvPowerSeries.pderiv ℚ (Fin.succ 0) (literalQ (literalRows 0))) ≠ 0
  have hrow : literalRows (0 : Fin 1) = (3 : Fin 4) := rfl
  rw [hrow]
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  norm_num [literalQ, h30, h31, h32]

theorem literal_tilted_lift_reads_returned_conormal :
    ∃ (α : Fin 1 → ℚ),
      tiltedArc (k := ℚ) α literalBad ≠ 0 ∧
      tiltedArc (k := ℚ) α (literalQ 0) =
        (PowerSeries.X : PowerSeries ℚ) ^ 1 * tiltedArc (k := ℚ) α 1 ∧
      PowerSeries.constantCoeff (tiltedArc (k := ℚ) α 1) ≠ 0 ∧
      tiltedArc (k := ℚ) α (literalQ 1) =
        (PowerSeries.X : PowerSeries ℚ) ^ 2 * tiltedArc (k := ℚ) α 1 ∧
      PowerSeries.constantCoeff (tiltedArc (k := ℚ) α 1) ≠ 0 ∧
      PowerSeries.constantCoeff (selectedMinor
        (tiltedTransverseDerivativeMatrix (k := ℚ) α literalQ) literalRows).det ≠ 0 ∧
      ∃ (lambda : Fin 1 → PowerSeries ℚ) (c : ℕ)
      (tau : Fin 4 → PowerSeries ℚ)
      (C : Matrix (FormalTangentColumn (Fin 1)) (Fin 4) (PowerSeries ℚ))
      (ell : Fin 4 → PowerSeries ℚ),
      (∀ i,
        PowerSeries.derivative ℚ (tiltedArc (k := ℚ) α (literalQ i)) -
          (tiltedTransverseDerivativeMatrix (k := ℚ) α literalQ).mulVec lambda i =
            (PowerSeries.X : PowerSeries ℚ) ^ c * tau i) ∧
      C * formalTangentMatrix (fun i => tiltedArc (k := ℚ) α (literalQ i))
        (tiltedTransverseDerivativeMatrix (k := ℚ) α literalQ) tau = 1 ∧
      rowMul ell (formalTangentMatrix (fun i => tiltedArc (k := ℚ) α (literalQ i))
        (tiltedTransverseDerivativeMatrix (k := ℚ) α literalQ) tau) = 0 ∧
      residueColumn ell = axisRow (k := ℚ) (1 : Fin 4) := by
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have h22 : (2 : Fin 4) = 2 := rfl
  obtain ⟨α, havoid, hqzero, hu₀, hqaxis, hu₁, hminor, lambda, c, tau, C, ell,
    hlambda, hselected, htauchart, htauselected, hc, hfactor, hprimitive,
    haxis, haxiscolumns, hCB, hell, hellres⟩ :=
    exists_tilted_local_axis_lift (k := ℚ) literalQ literalBad
      (by
        intro hz
        have hc := congrArg
          (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)) hz
        simpa [literalBad] using hc) literalRows 2 0 1 1 2 1 1
      (by norm_num [literalQ, h20, h21, h22]) (by norm_num) (by norm_num)
      (by norm_num [literalQ]) (by norm_num) (by norm_num [literalQ])
      (by norm_num) literalMinor
  exact ⟨α, havoid, hqzero, hu₀, hqaxis, hu₁, hminor,
    lambda, c, tau, C, ell, hfactor, hCB, hell, hellres⟩

#print axioms literal_tilted_lift_reads_returned_conormal
