import Stafford38.Geometry.ProjectiveEquationFormalChart
import Stafford38.Geometry.LocalizedProjectiveChartTransition
import Stafford38.Geometry.FormalDivisorLaurentConormal

/-!
# Evaluation after homogenization in the zeroth projective chart

These wrappers expose the exact denominator-clearing identity for an arbitrary
affine polynomial and its behavior under the canonical power-series-to-Laurent
embedding. The homogeneous scaling calculation is reused from
`ProjectiveEquationFormalChart`.
-/

namespace Stafford38.Geometry.HomogenizedAffineEvaluation

open Stafford38.Geometry.ProjectiveEquationFormalChart
open Stafford38.Geometry.LocalizedProjectiveChartTransition
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.FormalDivisorLaurentConormal

noncomputable section

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- Homogenization clears the chart denominator by exactly the total-degree
power. -/
theorem eval_homogenizeAtZero_eq_pow_mul_dehomogenizedPoint
    (p : MvPolynomial (Fin n) K) (q : Fin (n + 1) → K)
    (hq₀ : q 0 ≠ 0) :
    MvPolynomial.eval q (homogenizeAtZero p) =
      q 0 ^ p.totalDegree * MvPolynomial.eval (dehomogenizedPoint q) p := by
  rw [eval_eq_pow_mul_eval_normalizedProjectivePoint
    (homogenizeAtZero p) p.totalDegree
    (homogenizeAtZero_isHomogeneous p) q (q 0) hq₀]
  rw [normalizedProjectivePoint_eq_chartPoint q hq₀,
    ← eval_projectiveDehomogenize (homogenizeAtZero p)
      (dehomogenizedPoint q),
    projectiveDehomogenize_homogenizeAtZero]

/-- For a nonzero zeroth coordinate, homogenizing preserves nonvanishing of
the original affine evaluation. -/
theorem eval_homogenizeAtZero_ne_zero_iff
    (p : MvPolynomial (Fin n) K) (q : Fin (n + 1) → K)
    (hq₀ : q 0 ≠ 0) :
    MvPolynomial.eval q (homogenizeAtZero p) ≠ 0 ↔
      MvPolynomial.eval (dehomogenizedPoint q) p ≠ 0 := by
  rw [eval_homogenizeAtZero_eq_pow_mul_dehomogenizedPoint p q hq₀]
  constructor
  · intro h
    exact (mul_ne_zero_iff.mp h).2
  · intro h
    exact mul_ne_zero (pow_ne_zero _ hq₀) h

/-- Coefficient maps commute with taking a homogeneous component. -/
private theorem map_homogeneousComponent
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (d : ℕ) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map f (MvPolynomial.homogeneousComponent d p) =
      MvPolynomial.homogeneousComponent d (MvPolynomial.map f p) := by
  classical
  ext e
  by_cases h : e.degree = d
  · simp [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent, h]
  · simp [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent, h]

private theorem totalDegree_map_eq_of_injective
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hf : Function.Injective f)
    (p : MvPolynomial (Fin n) R) :
    (MvPolynomial.map f p).totalDegree = p.totalDegree := by
  classical
  simp [MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective p hf]

/-- Coefficient maps between fields commute with zeroth-chart homogenization. -/
theorem map_homogenizeAtZero
    {R S : Type*} [Field R] [Field S]
    (f : R →+* S) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map f (homogenizeAtZero p) =
      homogenizeAtZero (MvPolynomial.map f p) := by
  have hf : Function.Injective f := RingHom.injective f
  simp only [homogenizeAtZero, map_sum, map_mul, map_pow,
    MvPolynomial.map_X, MvPolynomial.map_rename, map_homogeneousComponent]
  rw [totalDegree_map_eq_of_injective f hf p]

variable {κ : Type u} [Field κ]

/-- The denominator-clearing identity after embedding power-series coordinates
and polynomial coefficients into Laurent series. -/
theorem laurent_eval_map_homogenizeAtZero_eq_pow_mul_dehomogenizedPoint
    (p : MvPolynomial (Fin n) κ)
    (q : Fin (n + 1) → PowerSeries κ) (hq₀ : q 0 ≠ 0) :
    MvPolynomial.eval (laurentColumn q)
        (MvPolynomial.map (algebraMap κ (LaurentSeries κ))
          (homogenizeAtZero p)) =
      (laurentColumn q 0) ^ p.totalDegree *
    MvPolynomial.eval (dehomogenizedPoint (laurentColumn q))
          (MvPolynomial.map (algebraMap κ (LaurentSeries κ)) p) := by
  calc
    MvPolynomial.eval (laurentColumn q)
        (MvPolynomial.map (algebraMap κ (LaurentSeries κ))
          (homogenizeAtZero p)) =
        MvPolynomial.eval (laurentColumn q)
          (homogenizeAtZero
            (MvPolynomial.map (algebraMap κ (LaurentSeries κ)) p)) := by
          rw [map_homogenizeAtZero]
    _ = (laurentColumn q 0) ^
          (MvPolynomial.map (algebraMap κ (LaurentSeries κ)) p).totalDegree *
        MvPolynomial.eval (dehomogenizedPoint (laurentColumn q))
          (MvPolynomial.map (algebraMap κ (LaurentSeries κ)) p) :=
      eval_homogenizeAtZero_eq_pow_mul_dehomogenizedPoint
        (MvPolynomial.map (algebraMap κ (LaurentSeries κ)) p)
        (laurentColumn q)
        (laurentColumn_ne_zero_of_ne_zero q hq₀)
    _ = (laurentColumn q 0) ^ p.totalDegree *
        MvPolynomial.eval (dehomogenizedPoint (laurentColumn q))
          (MvPolynomial.map (algebraMap κ (LaurentSeries κ)) p) := by
      rw [totalDegree_map_eq_of_injective
        (algebraMap κ (LaurentSeries κ))
        (algebraMap κ (LaurentSeries κ)).injective p]

/-- The Laurent-series evaluation of a homogenized numerator is nonzero
exactly when the original affine evaluation at the dehomogenized Laurent point
is nonzero. -/
theorem laurent_eval_map_homogenizeAtZero_ne_zero_iff
    (p : MvPolynomial (Fin n) κ)
    (q : Fin (n + 1) → PowerSeries κ) (hq₀ : q 0 ≠ 0) :
    MvPolynomial.eval (laurentColumn q)
        (MvPolynomial.map (algebraMap κ (LaurentSeries κ))
          (homogenizeAtZero p)) ≠ 0 ↔
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q))
          (MvPolynomial.map (algebraMap κ (LaurentSeries κ)) p) ≠ 0 := by
  rw [laurent_eval_map_homogenizeAtZero_eq_pow_mul_dehomogenizedPoint
    p q hq₀]
  constructor
  · intro h
    exact (mul_ne_zero_iff.mp h).2
  · intro h
    exact mul_ne_zero
      (pow_ne_zero _ (laurentColumn_ne_zero_of_ne_zero q hq₀)) h

end

end Stafford38.Geometry.HomogenizedAffineEvaluation
