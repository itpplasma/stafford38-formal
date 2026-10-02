import proofs.weyl_pure_power
import Stafford38.EvolutionaryCertificate

/-! Public Euler-product identities for the Weyl pair calculation.

This module reuses the generic rising/falling calculus in
`Stafford38.EvolutionaryCertificate` and exports the explicit polynomial
evaluation identities used by the paper.
-/

namespace Stafford38.Weyl.EulerProductIdentities

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℚ A]

def fallingEulerPolynomial : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => fallingEulerPolynomial n * (Polynomial.X - Polynomial.C (n : ℚ))

def risingEulerPolynomial : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => risingEulerPolynomial n *
      (Polynomial.X + Polynomial.C ((n + 1 : ℕ) : ℚ))

/-- The falling polynomial is the product of the Euler factors `X-i`. -/
theorem fallingEulerPolynomial_eq_prod (n : ℕ) :
    fallingEulerPolynomial n = ∏ i ∈ Finset.range n,
      (Polynomial.X - Polynomial.C (i : ℚ)) := by
  induction n with
  | zero => simp [fallingEulerPolynomial]
  | succ n ih =>
      rw [fallingEulerPolynomial, ih, Finset.prod_range_succ]

/-- The rising polynomial is the product of the Euler factors `X+(i+1)`. -/
theorem risingEulerPolynomial_eq_prod (n : ℕ) :
    risingEulerPolynomial n = ∏ i ∈ Finset.range n,
      (Polynomial.X + Polynomial.C ((i + 1 : ℕ) : ℚ)) := by
  induction n with
  | zero => simp [risingEulerPolynomial]
  | succ n ih =>
      rw [risingEulerPolynomial, ih, Finset.prod_range_succ]

private theorem fallingEulerPolynomial_eq_owner (n : ℕ) :
    fallingEulerPolynomial n = Stafford38.Evolution.fallingPoly ℚ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [fallingEulerPolynomial, Stafford38.Evolution.fallingPoly_succ, ih]

private theorem risingEulerPolynomial_eq_owner (n : ℕ) :
    risingEulerPolynomial n = Stafford38.Evolution.risingPoly ℚ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [risingEulerPolynomial, Stafford38.Evolution.risingPoly_succ, ih]
      push_cast
      rfl

/-- Evaluation of the explicit falling Euler product gives `x^n * d^n`. -/
theorem eulerPolynomialEval_falling (x d : A)
    (h : d * x = x * d + 1) (n : ℕ) :
    Stafford.eulerPolynomialEval x d (fallingEulerPolynomial n) = x ^ n * d ^ n := by
  rw [fallingEulerPolynomial_eq_owner]
  change Polynomial.aeval (Stafford38.Evolution.euler x d)
    (Stafford38.Evolution.fallingPoly ℚ n) = x ^ n * d ^ n
  rw [Stafford38.Evolution.aeval_fallingPoly]
  simpa [Stafford38.Evolution.euler] using
    (Stafford38.Evolution.pow_mul_pow_eq_falling (x := x) (p := d) h n).symm

/-- Evaluation of the explicit rising Euler product gives `d^n * x^n`. -/
theorem eulerPolynomialEval_rising (x d : A)
    (h : d * x = x * d + 1) (n : ℕ) :
    Stafford.eulerPolynomialEval x d (risingEulerPolynomial n) = d ^ n * x ^ n := by
  rw [risingEulerPolynomial_eq_owner]
  change Polynomial.aeval (Stafford38.Evolution.euler x d)
    (Stafford38.Evolution.risingPoly ℚ n) = d ^ n * x ^ n
  rw [Stafford38.Evolution.aeval_risingPoly]
  simpa [Stafford38.Evolution.euler] using
    (Stafford38.Evolution.pow_mul_pow_eq_rising (x := x) (p := d) h n).symm

/-- Evaluation of the falling product written with a finite-product sign. -/
theorem eval_fallingEulerProduct (x d : A)
    (h : d * x = x * d + 1) (n : ℕ) :
    Stafford.eulerPolynomialEval x d
      (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (i : ℚ))) =
        x ^ n * d ^ n := by
  rw [← fallingEulerPolynomial_eq_prod n]
  exact eulerPolynomialEval_falling x d h n

/-- Evaluation of the rising product written with a finite-product sign. -/
theorem eval_risingEulerProduct (x d : A)
    (h : d * x = x * d + 1) (n : ℕ) :
    Stafford.eulerPolynomialEval x d
      (∏ i ∈ Finset.range n,
        (Polynomial.X + Polynomial.C ((i + 1 : ℕ) : ℚ))) =
          d ^ n * x ^ n := by
  rw [← risingEulerPolynomial_eq_prod n]
  exact eulerPolynomialEval_rising x d h n

#print axioms eulerPolynomialEval_falling
#print axioms eulerPolynomialEval_rising
#print axioms eval_fallingEulerProduct
#print axioms eval_risingEulerProduct

end

end Stafford38.Weyl.EulerProductIdentities
