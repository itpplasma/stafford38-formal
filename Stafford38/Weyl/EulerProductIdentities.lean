import proofs.weyl_pure_power

/-! Public Euler-product identities for the Weyl pair calculation.

The source proof's rising/falling recurrences were private. This module repeats
those short recurrences and exports the explicit polynomial-evaluation identities
used by the paper, without changing the upstream proof module.
-/

namespace Stafford38.Weyl.EulerProductIdentities

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℚ A]

private def theta (x d : A) : A := x * d

private def falling (x d : A) : ℕ → A
  | 0 => 1
  | n + 1 => falling x d n * (theta x d - (n : A))

private def fallingShift (x d : A) : ℕ → A
  | 0 => 1
  | n + 1 => fallingShift x d n * (theta x d - ((n + 1 : ℕ) : A))

private def rising (x d : A) : ℕ → A
  | 0 => 1
  | n + 1 => rising x d n * (theta x d + ((n + 1 : ℕ) : A))

private def risingShift (x d : A) : ℕ → A
  | 0 => 1
  | n + 1 => risingShift x d n * (theta x d + ((n + 2 : ℕ) : A))

def fallingEulerPolynomial : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => fallingEulerPolynomial n * (Polynomial.X - Polynomial.C (n : ℚ))

def risingEulerPolynomial : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => risingEulerPolynomial n * (Polynomial.X + Polynomial.C ((n + 1 : ℕ) : ℚ))

/-- The falling polynomial is the product of the Euler factors `X-i`. -/
theorem fallingEulerPolynomial_eq_prod (n : ℕ) :
    fallingEulerPolynomial n = ∏ i ∈ Finset.range n,
      (Polynomial.X - Polynomial.C (i : ℚ)) := by
  induction n with
  | zero => simp [fallingEulerPolynomial]
  | succ n ih => rw [fallingEulerPolynomial, ih, Finset.prod_range_succ]

/-- The rising polynomial is the product of the Euler factors `X+(i+1)`. -/
theorem risingEulerPolynomial_eq_prod (n : ℕ) :
    risingEulerPolynomial n = ∏ i ∈ Finset.range n,
      (Polynomial.X + Polynomial.C ((i + 1 : ℕ) : ℚ)) := by
  induction n with
  | zero => simp [risingEulerPolynomial]
  | succ n ih => rw [risingEulerPolynomial, ih, Finset.prod_range_succ]

private lemma x_mul_theta_sub_nat
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    x * (theta x d - (n : A)) =
      (theta x d - ((n + 1 : ℕ) : A)) * x := by
  have hxt : x * theta x d = (theta x d - 1) * x := by
    dsimp [theta]
    have h' : x * d = d * x - 1 := by
      simp [h]
    calc
      x * (x * d) = x * (d * x - 1) := by rw [h']
      _ = x * d * x - x := by noncomm_ring
      _ = (x * d - 1) * x := by noncomm_ring
  have hn : (n : A) * x = x * (n : A) := by
    simpa using (Algebra.commutes (n : ℚ) x)
  rw [mul_sub, hxt]
  push_cast
  rw [← hn]
  noncomm_ring

private lemma d_mul_theta_add_nat
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    d * (theta x d + ((n + 1 : ℕ) : A)) =
      (theta x d + ((n + 2 : ℕ) : A)) * d := by
  have hdt : d * theta x d = (theta x d + 1) * d := by
    dsimp [theta]
    calc
      d * (x * d) = (d * x) * d := by noncomm_ring
      _ = (x * d + 1) * d := by rw [h]
      _ = (theta x d + 1) * d := rfl
  have hn : (n : A) * d = d * (n : A) := by
    simpa using (Algebra.commutes (n : ℚ) d)
  rw [mul_add, hdt]
  push_cast
  simp only [mul_add]
  rw [← hn]
  noncomm_ring

private lemma x_mul_falling
    (x d : A) (h : d * x = x * d + 1) : ∀ n : ℕ,
    x * falling x d n = fallingShift x d n * x
  | 0 => by simp [falling, fallingShift]
  | n + 1 => by
      change x * (falling x d n * (theta x d - (n : A))) =
        (fallingShift x d n * (theta x d - ((n + 1 : ℕ) : A))) * x
      calc
        x * (falling x d n * (theta x d - (n : A))) =
            (x * falling x d n) * (theta x d - (n : A)) := by
              noncomm_ring
        _ = (fallingShift x d n * x) *
            (theta x d - (n : A)) := by rw [x_mul_falling x d h n]
        _ = fallingShift x d n *
            ((theta x d - ((n + 1 : ℕ) : A)) * x) := by
              calc
                fallingShift x d n * x * (theta x d - (n : A)) =
                    fallingShift x d n *
                      (x * (theta x d - (n : A))) := by rw [mul_assoc]
                _ = fallingShift x d n *
                    ((theta x d - ((n + 1 : ℕ) : A)) * x) := by
                      rw [x_mul_theta_sub_nat x d h n]
        _ = (fallingShift x d n *
            (theta x d - ((n + 1 : ℕ) : A))) * x := by
              noncomm_ring

private lemma d_mul_rising
    (x d : A) (h : d * x = x * d + 1) : ∀ n : ℕ,
    d * rising x d n = risingShift x d n * d
  | 0 => by simp [rising, risingShift]
  | n + 1 => by
      change d * (rising x d n * (theta x d + ((n + 1 : ℕ) : A))) =
        (risingShift x d n * (theta x d + ((n + 2 : ℕ) : A))) * d
      calc
        d * (rising x d n * (theta x d + ((n + 1 : ℕ) : A))) =
            (d * rising x d n) *
              (theta x d + ((n + 1 : ℕ) : A)) := by noncomm_ring
        _ = (risingShift x d n * d) *
            (theta x d + ((n + 1 : ℕ) : A)) := by rw [d_mul_rising x d h n]
        _ = risingShift x d n *
            ((theta x d + ((n + 2 : ℕ) : A)) * d) := by
              calc
                risingShift x d n * d *
                      (theta x d + ((n + 1 : ℕ) : A)) =
                    risingShift x d n *
                      (d * (theta x d + ((n + 1 : ℕ) : A))) := by
                        rw [mul_assoc]
                _ = risingShift x d n *
                    ((theta x d + ((n + 2 : ℕ) : A)) * d) := by
                      rw [d_mul_theta_add_nat x d h n]
        _ = (risingShift x d n *
            (theta x d + ((n + 2 : ℕ) : A))) * d := by
              noncomm_ring

private lemma fallingShift_mul_theta
    (x d : A) : ∀ n : ℕ,
    fallingShift x d n * theta x d = falling x d (n + 1)
  | 0 => by simp [falling, fallingShift]
  | n + 1 => by
      change (fallingShift x d n *
          (theta x d - ((n + 1 : ℕ) : A))) * theta x d =
        falling x d (n + 2)
      calc
        (fallingShift x d n *
            (theta x d - ((n + 1 : ℕ) : A))) * theta x d =
            (fallingShift x d n * theta x d) *
              (theta x d - ((n + 1 : ℕ) : A)) := by
                have hn : ((n + 1 : ℕ) : A) * theta x d =
                    theta x d * ((n + 1 : ℕ) : A) := by
                  simpa using (Algebra.commutes ((n + 1 : ℕ) : ℚ) (theta x d))
                calc
                  (fallingShift x d n *
                      (theta x d - ((n + 1 : ℕ) : A))) * theta x d =
                      fallingShift x d n *
                        ((theta x d - ((n + 1 : ℕ) : A)) * theta x d) := by
                          rw [mul_assoc]
                  _ = fallingShift x d n *
                        (theta x d *
                          (theta x d - ((n + 1 : ℕ) : A))) := by
                          congr 1
                          rw [mul_sub, sub_mul, hn]
                  _ = (fallingShift x d n * theta x d) *
                        (theta x d - ((n + 1 : ℕ) : A)) := by
                          rw [mul_assoc]
        _ = falling x d (n + 1) *
              (theta x d - ((n + 1 : ℕ) : A)) := by
                rw [fallingShift_mul_theta x d n]
        _ = falling x d (n + 2) := by rfl

private lemma risingShift_mul_theta_add_one
    (x d : A) : ∀ n : ℕ,
    risingShift x d n * (theta x d + 1) = rising x d (n + 1)
  | 0 => by simp [rising, risingShift]
  | n + 1 => by
      change (risingShift x d n *
          (theta x d + ((n + 2 : ℕ) : A))) *
            (theta x d + 1) = rising x d (n + 2)
      calc
        (risingShift x d n *
            (theta x d + ((n + 2 : ℕ) : A))) *
              (theta x d + 1) =
            (risingShift x d n * (theta x d + 1)) *
              (theta x d + ((n + 2 : ℕ) : A)) := by
                have hn : ((n + 2 : ℕ) : A) * theta x d =
                    theta x d * ((n + 2 : ℕ) : A) := by
                  simpa only [map_natCast] using
                    (Algebra.commutes ((n + 2 : ℕ) : ℚ) (theta x d))
                calc
                  (risingShift x d n *
                      (theta x d + ((n + 2 : ℕ) : A))) *
                        (theta x d + 1) =
                      risingShift x d n *
                        ((theta x d + ((n + 2 : ℕ) : A)) *
                          (theta x d + 1)) := by
                            rw [mul_assoc]
                  _ = risingShift x d n *
                        ((theta x d + 1) *
                          (theta x d + ((n + 2 : ℕ) : A))) := by
                            congr 1
                            simp only [add_mul, mul_add]
                            rw [hn]
                            noncomm_ring
                  _ = (risingShift x d n * (theta x d + 1)) *
                        (theta x d + ((n + 2 : ℕ) : A)) := by
                            rw [mul_assoc]
        _ = rising x d (n + 1) *
              (theta x d + ((n + 2 : ℕ) : A)) := by
                rw [risingShift_mul_theta_add_one x d n]
        _ = rising x d (n + 2) := by rfl

private lemma x_pow_mul_d_pow
    (x d : A) (h : d * x = x * d + 1) : ∀ n : ℕ,
    x ^ n * d ^ n = falling x d n
  | 0 => by simp [falling]
  | n + 1 => by
      calc
        x ^ (n + 1) * d ^ (n + 1) = x * (x ^ n * d ^ n) * d := by
          rw [pow_succ', pow_succ]
          simp only [mul_assoc]
        _ = x * falling x d n * d := by rw [x_pow_mul_d_pow x d h n]
        _ = fallingShift x d n * (x * d) := by
          rw [x_mul_falling x d h n]
          noncomm_ring
        _ = falling x d (n + 1) := by
          simpa [theta] using fallingShift_mul_theta x d n

private lemma d_pow_mul_x_pow
    (x d : A) (h : d * x = x * d + 1) : ∀ n : ℕ,
    d ^ n * x ^ n = rising x d n
  | 0 => by simp [rising]
  | n + 1 => by
      calc
        d ^ (n + 1) * x ^ (n + 1) = d * (d ^ n * x ^ n) * x := by
          rw [pow_succ', pow_succ]
          simp only [mul_assoc]
        _ = d * rising x d n * x := by rw [d_pow_mul_x_pow x d h n]
        _ = risingShift x d n * (d * x) := by
          rw [d_mul_rising x d h n]
          noncomm_ring
        _ = rising x d (n + 1) := by
          rw [h]
          simpa [theta] using risingShift_mul_theta_add_one x d n

private lemma eval_fallingEulerPolynomial
    (x d : A)
    (ev : Polynomial ℚ →+* A)
    (hev : ev Polynomial.X = theta x d)
    (hC : ∀ q : ℚ, ev (Polynomial.C q) = (algebraMap ℚ A) q)
    (n : ℕ) :
    ev (fallingEulerPolynomial n) = falling x d n := by
  induction n with
  | zero => simp [fallingEulerPolynomial, falling]
  | succ n ih =>
      rw [fallingEulerPolynomial, map_mul, map_sub, hev, hC]
      push_cast
      rw [ih]
      simp [falling]

private lemma eval_risingEulerPolynomial
    (x d : A)
    (ev : Polynomial ℚ →+* A)
    (hev : ev Polynomial.X = theta x d)
    (hC : ∀ q : ℚ, ev (Polynomial.C q) = (algebraMap ℚ A) q)
    (n : ℕ) :
    ev (risingEulerPolynomial n) = rising x d n := by
  induction n with
  | zero => simp [risingEulerPolynomial, rising]
  | succ n ih =>
      rw [risingEulerPolynomial, map_mul, map_add, hev, hC]
      push_cast
      rw [ih]
      simp [rising]


/-- Evaluation of the explicit falling Euler product gives `x^n * d^n`. -/
theorem eulerPolynomialEval_falling (x d : A)
    (h : d * x = x * d + 1) (n : ℕ) :
    Stafford.eulerPolynomialEval x d (fallingEulerPolynomial n) = x ^ n * d ^ n := by
  rw [eval_fallingEulerPolynomial x d (Stafford.eulerPolynomialEval x d)
    (by simp [theta])
    (by intro q; exact Stafford.eulerPolynomialEval_C x d q) n]
  exact (x_pow_mul_d_pow x d h n).symm

/-- Evaluation of the explicit rising Euler product gives `d^n * x^n`. -/
theorem eulerPolynomialEval_rising (x d : A)
    (h : d * x = x * d + 1) (n : ℕ) :
    Stafford.eulerPolynomialEval x d (risingEulerPolynomial n) = d ^ n * x ^ n := by
  rw [eval_risingEulerPolynomial x d (Stafford.eulerPolynomialEval x d)
    (by simp [theta])
    (by intro q; exact Stafford.eulerPolynomialEval_C x d q) n]
  exact (d_pow_mul_x_pow x d h n).symm

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
