import Stafford38.Geometry.HomogenizedAffineEvaluation
import Mathlib.Tactic.NormNum

open Stafford38.Geometry.HomogenizedAffineEvaluation
open Stafford38.Geometry.LocalizedProjectiveChartTransition
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.FormalDivisorLaurentConormal

universe u

/-- A separate importer confirms that the generic iff is available to an
original affine equation, independently of any projective-closure ideal. -/
theorem original_affine_open_survives_homogenization
    {K : Type u} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (q : Fin (n + 1) → K)
    (hq₀ : q 0 ≠ 0) :
    MvPolynomial.eval q (homogenizeAtZero p) ≠ 0 ↔
      MvPolynomial.eval (dehomogenizedPoint q) p ≠ 0 :=
  eval_homogenizeAtZero_ne_zero_iff p q hq₀

/-- The same importer-level nonvanishing criterion for a power-series
projective column evaluated in its Laurent field. -/
theorem original_affine_open_survives_laurent_arc
    {κ : Type u} [Field κ] {n : ℕ}
    (p : MvPolynomial (Fin n) κ)
    (q : Fin (n + 1) → PowerSeries κ) (hq₀ : q 0 ≠ 0) :
    MvPolynomial.eval (laurentColumn q)
        (MvPolynomial.map (algebraMap κ (LaurentSeries κ))
          (homogenizeAtZero p)) ≠ 0 ↔
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q))
          (MvPolynomial.map (algebraMap κ (LaurentSeries κ)) p) ≠ 0 :=
  laurent_eval_map_homogenizeAtZero_ne_zero_iff p q hq₀

#print axioms original_affine_open_survives_homogenization
#print axioms original_affine_open_survives_laurent_arc

/-- A concrete nontrivial chart: x=6/3=2, so homogenizing x gives 6. -/
theorem rational_homogenized_coordinate_oracle :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (3 : ℚ) else 6)
      (homogenizeAtZero (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ)) = 6 := by
  rw [eval_homogenizeAtZero_eq_pow_mul_dehomogenizedPoint]
  · norm_num [MvPolynomial.totalDegree_X, dehomogenizedPoint]
  · norm_num

#print axioms rational_homogenized_coordinate_oracle
#print axioms Stafford38.Geometry.HomogenizedAffineEvaluation.map_homogenizeAtZero
