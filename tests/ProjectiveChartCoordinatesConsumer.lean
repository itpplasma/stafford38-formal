module
public import Stafford38.Geometry.ChartArcAnnihilation
public import Stafford38.Geometry.ComponentFunctionFieldBoundary
public import Stafford38.Geometry.ProjectiveEquationFormalChart

@[expose] public section

open Stafford38.Geometry.ChartArcAnnihilation
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.ProjectiveEquationFormalChart
open Stafford38.Geometry.AsymptoticChartArcAdapter

universe u

variable {K : Type u} [Field K]

/-- The fixed chart-zero API retains the standard coordinate order. -/
example {m : ℕ} (p : MvPolynomial (Fin (m + 1)) K) :
    projectiveDehomogenize (n := m) p =
      MvPolynomial.aeval (Fin.cases 1 fun i ↦ MvPolynomial.X i) p := by
  simp [projectiveDehomogenize]

/-- The arbitrary-chart API still uses its existing complementary ordering,
and evaluation agrees with the corresponding inserted point. -/
example {m : ℕ} (chart : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) K) (y : Fin m → K) :
    MvPolynomial.eval y (projectiveDehomogenizeAt chart p) =
      MvPolynomial.eval (projectiveChartPoint chart y) p :=
  eval_projectiveDehomogenizeAt chart p y

/-- At chart zero, the historical arbitrary-chart ordering is explicitly
transported to the fixed `Fin.succ` ordering. -/
example {m : ℕ} (y : Fin m → K) :
    projectiveChartPoint (0 : Fin (m + 1)) y =
      insertProjectiveChart (0 : Fin (m + 1)) (zerothChartEquiv (m := m))
        (fun i ↦ y ((zerothChartEquiv (m := m)).trans
          (chartAffineCoordinateEquiv (0 : Fin (m + 1))).symm i)) := by
  simpa [projectiveChartPoint] using
    insertProjectiveChart_zero_transport
      (chartAffineCoordinateEquiv (0 : Fin (m + 1))) y

example {m : ℕ} :
    (MvPolynomial.renameEquiv K
        ((zerothChartEquiv (m := m)).trans
          (chartAffineCoordinateEquiv (0 : Fin (m + 1))).symm)).toAlgHom.comp
        (projectiveDehomogenize (n := m)) = projectiveDehomogenizeAt 0 := by
  simpa [projectiveDehomogenize, projectiveDehomogenizeAt] using
    dehomogenizeProjectiveChart_zero_transport
      (chartAffineCoordinateEquiv (0 : Fin (m + 1)))

/-- The fixed zeroth-chart equation ideal is the definitional specialization
of the shared chart construction, with its established `Fin.succ` order. -/
example {m : ℕ} (equations : Unit → MvPolynomial (Fin (m + 1)) K) :
    Stafford38.Geometry.ProjectiveEquationFormalChart.dehomogenizedEquationIdeal
        (n := m) equations =
      Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedEquationIdeal
        0 (zerothChartEquiv (m := m)) equations := rfl

/-- The arbitrary-chart ideal preserves its existing complement ordering as a
definitional specialization of the same owner. -/
example {m : ℕ} (chart : Fin (m + 1))
    (equations : Unit → MvPolynomial (Fin (m + 1)) K) :
    Stafford38.Geometry.ChartArcAnnihilation.chartDehomogenizedEquationIdeal
        chart equations =
      Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedEquationIdeal
        chart (chartAffineCoordinateEquiv chart) equations := rfl

/-- A concrete value check catches the chart-zero substitution order:
`X₀ + 2 X₁` dehomogenizes to `1 + 2 X`, hence evaluates to seven at `X=3`.
-/
theorem projectiveChart_zero_literal_oracle :
    MvPolynomial.eval (fun _ : Fin 1 ↦ (3 : K))
      (projectiveDehomogenize (n := 1)
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (Fin.succ 0) +
          MvPolynomial.X (Fin.succ 0))) = 7 := by
  rw [show projectiveDehomogenize (n := 1)
      (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (Fin.succ 0) +
        MvPolynomial.X (Fin.succ 0)) =
      dehomogenizeProjectiveChart (0 : Fin 2) (zerothChartEquiv (m := 1))
        (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 1) by
    simp [projectiveDehomogenize]]
  rw [eval_dehomogenizeProjectiveChart]
  have hpoint :
      insertProjectiveChart (0 : Fin 2) (zerothChartEquiv (m := 1))
          (fun _ : Fin 1 ↦ (3 : K)) =
        fun a : Fin 2 ↦ if a = 0 then 1 else 3 := by
    funext a
    rcases Fin.eq_zero_or_eq_succ a with ha | ⟨i, ha⟩
    · subst a
      simp [insertProjectiveChart]
    · subst a
      simp [insertProjectiveChart]
  rw [hpoint]
  norm_num [MvPolynomial.eval_X]

/-- A function-field component's projective point is the checked chart-zero
specialization, with the original field-valued coordinate family. -/
example {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    componentProjectivePoint P =
      Fin.cases 1 (fun i ↦ componentCoordinate P i) := by
  simp [componentProjectivePoint]

example {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    componentProjectivePoint P 0 = 1 := by
  simp [componentProjectivePoint]

example {k : Type u} [Field k] {m : ℕ} (i : Fin m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    componentProjectivePoint P i.succ = componentCoordinate P i := by
  simp [componentProjectivePoint]

/-- In chart Z1=1, the point (4,1,9) evaluates Z0*Z2+Z1 to37. -/
theorem projectiveChart_middle_literal_oracle :
    let e := chartAffineCoordinateEquiv (1 : Fin 3)
    MvPolynomial.eval (fun i : Fin 2 ↦ if (e i).val = 0 then (4 : ℚ) else 9)
      (dehomogenizeProjectiveChart (1 : Fin 3) e
        (MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) +
          MvPolynomial.X (1 : Fin 3))) = 37 := by
  dsimp only
  rw [eval_dehomogenizeProjectiveChart]
  simp only [map_add, map_mul, MvPolynomial.eval_X]
  have h0 : (0 : Fin 3) ≠ 1 := by decide
  have h2 : (2 : Fin 3) ≠ 1 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  simp only [insertProjectiveChart, h0, h2,
    Equiv.apply_symm_apply]
  norm_num [h20]

/-- The generic ideal transport uses that same middle-chart point: its
generator `X₀ X₂ - 36` vanishes at `(4,1,9)`, so every member of the
dehomogenized equation ideal evaluates to zero at the affine chart point. -/
theorem projectiveChart_middle_ideal_literal_oracle :
    let e := chartAffineCoordinateEquiv (1 : Fin 3)
    let y := fun i : Fin 2 ↦ if (e i).val = 0 then (4 : ℚ) else 9
    ∀ f ∈ Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizedEquationIdeal
        (1 : Fin 3) e
        (fun _ : Unit ↦ MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) +
          MvPolynomial.X (1 : Fin 3) - 37),
      MvPolynomial.eval y f = 0 := by
  dsimp only
  intro f hf
  have hvalue := projectiveChart_middle_literal_oracle
  dsimp only at hvalue
  rw [eval_dehomogenizeProjectiveChart] at hvalue
  apply Stafford38.Geometry.ProjectiveChartCoordinates.eval_eq_zero_of_mem_dehomogenizedEquationIdeal
    (1 : Fin 3) (chartAffineCoordinateEquiv (1 : Fin 3))
    (fun _ : Unit ↦ MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) +
      MvPolynomial.X (1 : Fin 3) - 37)
    (fun i : Fin 2 ↦ if (chartAffineCoordinateEquiv (1 : Fin 3) i).val = 0 then (4 : ℚ) else 9)
    ?_ f hf
  intro _
  have hsub : MvPolynomial.eval
      (insertProjectiveChart (1 : Fin 3) (chartAffineCoordinateEquiv 1)
        (fun i : Fin 2 ↦
          if (chartAffineCoordinateEquiv (1 : Fin 3) i).val = 0 then (4 : ℚ) else 9))
      (MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) +
        MvPolynomial.X (1 : Fin 3) - 37) =
      MvPolynomial.eval
        (insertProjectiveChart (1 : Fin 3) (chartAffineCoordinateEquiv 1)
          (fun i : Fin 2 ↦
            if (chartAffineCoordinateEquiv (1 : Fin 3) i).val = 0 then (4 : ℚ) else 9))
        (MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) +
          MvPolynomial.X (1 : Fin 3)) - 37 := by
    simp
  rw [hsub, hvalue]
  norm_num

#print axioms projectiveChart_middle_literal_oracle
#print axioms projectiveChart_middle_ideal_literal_oracle
#print axioms Stafford38.Geometry.ProjectiveChartCoordinates.eval_eq_zero_of_mem_dehomogenizedEquationIdeal

#print axioms projectiveChart_zero_literal_oracle
#print axioms Stafford38.Geometry.ProjectiveChartCoordinates.eval_dehomogenizeProjectiveChart
#print axioms Stafford38.Geometry.ProjectiveChartCoordinates.insertProjectiveChart_zero
#print axioms Stafford38.Geometry.ProjectiveChartCoordinates.insertProjectiveChart_zero_transport
#print axioms Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizeProjectiveChart_zero
#print axioms Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizeProjectiveChart_zero_transport
