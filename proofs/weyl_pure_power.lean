import Stafford38.EvolutionaryCertificate
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Algebra.Ring.GeomSum

/-!
# Pure-power Weyl certificates

This file formalizes the all-degree part of the one-variable Weyl--Bézout
calculation. It works in an arbitrary ring containing a Weyl pair
`d * x - x * d = 1`; the only coefficient input is the ordinary polynomial
Bézout relation between the two disjoint Euler products.

The remaining universal monic problem is not hidden here: it is the passage
from a pure power to a general monic polynomial.
-/

namespace Stafford

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℚ A]

private abbrev theta (x d : A) : A := Stafford38.Evolution.euler x d

private abbrev falling (x d : A) : ℕ → A :=
  Stafford38.Evolution.falling (theta x d)

private abbrev rising (x d : A) : ℕ → A :=
  Stafford38.Evolution.rising (theta x d)

private abbrev fallingPoly : ℕ → Polynomial ℚ := Stafford38.Evolution.fallingPoly ℚ

private abbrev risingPoly : ℕ → Polynomial ℚ := Stafford38.Evolution.risingPoly ℚ

private lemma fallingPoly_eq_prod (n : ℕ) :
    fallingPoly n = ∏ i ∈ Finset.range n,
      (Polynomial.X - Polynomial.C (i : ℚ)) := by
  change Stafford38.Evolution.fallingPoly ℚ n = _
  induction n with
  | zero => simp [Stafford38.Evolution.fallingPoly]
  | succ n ih =>
      rw [Stafford38.Evolution.fallingPoly_succ, ih, Finset.prod_range_succ]

private lemma risingPoly_eq_prod (n : ℕ) :
    risingPoly n = ∏ i ∈ Finset.range n,
      (Polynomial.X + Polynomial.C ((i + 1 : ℕ) : ℚ)) := by
  change Stafford38.Evolution.risingPoly ℚ n = _
  induction n with
  | zero => simp [Stafford38.Evolution.risingPoly]
  | succ n ih =>
      rw [Stafford38.Evolution.risingPoly_succ, ih, Finset.prod_range_succ]
      congr 1
      congr 1
      push_cast
      rfl

private lemma falling_factor_coprime_rising_factor (i j : ℕ) :
    IsCoprime (Polynomial.X - Polynomial.C (i : ℚ))
      (Polynomial.X + Polynomial.C ((j + 1 : ℕ) : ℚ)) := by
  have hunit : IsUnit ((i : ℚ) - -((j + 1 : ℕ) : ℚ)) := by
    apply isUnit_iff_ne_zero.mpr
    have hi : 0 ≤ (i : ℚ) := by positivity
    have hj : 0 < ((j + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.succ_pos j
    have hpos : 0 < (i : ℚ) - -((j + 1 : ℕ) : ℚ) := by linarith
    exact ne_of_gt hpos
  convert Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit using 1
  · simp [sub_eq_add_neg]

private lemma fallingPoly_isCoprime_risingPoly (n : ℕ) :
    IsCoprime (fallingPoly n) (risingPoly n) := by
  rw [fallingPoly_eq_prod, risingPoly_eq_prod]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  exact falling_factor_coprime_rising_factor i j

private lemma x_pow_mul_d_pow
    (x d : A) (h : d * x = x * d + 1) : ∀ n : ℕ,
    x ^ n * d ^ n = falling x d n := by
  intro n
  simpa [falling, theta] using
    (Stafford38.Evolution.pow_mul_pow_eq_falling (x := x) (p := d) h n)

private lemma d_pow_mul_x_pow
    (x d : A) (h : d * x = x * d + 1) : ∀ n : ℕ,
    d ^ n * x ^ n = rising x d n := by
  intro n
  simpa [rising, theta] using
    (Stafford38.Evolution.pow_mul_pow_eq_rising (x := x) (p := d) h n)

private lemma eval_fallingPoly
    (x d : A)
    (ev : Polynomial ℚ →+* A)
    (hev : ev Polynomial.X = theta x d)
    (hC : ∀ q : ℚ, ev (Polynomial.C q) = (algebraMap ℚ A) q) :
    ev (fallingPoly n) = falling x d n := by
  induction n with
  | zero => simp [fallingPoly, falling]
  | succ n ih =>
      change ev (Stafford38.Evolution.fallingPoly ℚ (n + 1)) =
        Stafford38.Evolution.falling (Stafford38.Evolution.euler x d) (n + 1)
      rw [Stafford38.Evolution.fallingPoly_succ, map_mul, map_sub, hev, hC]
      push_cast
      rw [ih]
      simp [falling, theta, Stafford38.Evolution.falling_succ]

private lemma eval_risingPoly
    (x d : A)
    (ev : Polynomial ℚ →+* A)
    (hev : ev Polynomial.X = theta x d)
    (hC : ∀ q : ℚ, ev (Polynomial.C q) = (algebraMap ℚ A) q) :
    ev (risingPoly n) = rising x d n := by
  induction n with
  | zero => simp [risingPoly, rising]
  | succ n ih =>
      change ev (Stafford38.Evolution.risingPoly ℚ (n + 1)) =
        Stafford38.Evolution.rising (Stafford38.Evolution.euler x d) (n + 1)
      rw [Stafford38.Evolution.risingPoly_succ, map_mul, map_add, hev, hC]
      push_cast
      rw [ih]
      simp [rising, theta, Stafford38.Evolution.rising_succ]

/-- Evaluation of a rational polynomial at the Euler element `x*d`. -/
def eulerPolynomialEval (x d : A) : Polynomial ℚ →+* A :=
  Polynomial.eval₂RingHom' (algebraMap ℚ A) (theta x d)
    (fun q => Algebra.commutes q (theta x d))

@[simp] theorem eulerPolynomialEval_X (x d : A) :
    eulerPolynomialEval x d Polynomial.X = x * d := by
  change Polynomial.eval₂ (algebraMap ℚ A) (theta x d) Polynomial.X = x * d
  rw [Polynomial.eval₂_X (algebraMap ℚ A) (theta x d)]
  rfl

@[simp] theorem eulerPolynomialEval_C (x d : A) (q : ℚ) :
    eulerPolynomialEval x d (Polynomial.C q) = algebraMap ℚ A q := by
  change Polynomial.eval₂ (algebraMap ℚ A) (theta x d) (Polynomial.C q) =
    algebraMap ℚ A q
  exact Polynomial.eval₂_C (algebraMap ℚ A) (theta x d)

/-- Equal powers `x^n*d^n` are a rational polynomial in the Euler element. -/
theorem exists_eulerPolynomial_x_pow_mul_d_pow
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    ∃ f : Polynomial ℚ,
      eulerPolynomialEval x d f = x ^ n * d ^ n := by
  refine ⟨fallingPoly n, ?_⟩
  rw [eval_fallingPoly x d (eulerPolynomialEval x d)
    (by rw [eulerPolynomialEval_X]; rfl) (by intro q; simp)]
  exact (x_pow_mul_d_pow x d h n).symm

/-- Equal powers `d^n*x^n` are also a rational polynomial in `x*d`. -/
theorem exists_eulerPolynomial_d_pow_mul_x_pow
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    ∃ f : Polynomial ℚ,
      eulerPolynomialEval x d f = d ^ n * x ^ n := by
  refine ⟨risingPoly n, ?_⟩
  rw [eval_risingPoly x d (eulerPolynomialEval x d)
    (by rw [eulerPolynomialEval_X]; rfl) (by intro q; simp)]
  exact (d_pow_mul_x_pow x d h n).symm

/-- The pure-power certificate, assuming the ordinary Euler products are
coprime in the coefficient polynomial ring. -/
theorem pure_power_weyl_certificate
    (x d : A) (h : d * x = x * d + 1) (n : ℕ)
    (a b : Polynomial ℚ)
    (hab : a * fallingPoly n + b * risingPoly n = 1) :
    ∃ p q : A, 1 = p * (x ^ n) + q * (x ^ n * d ^ n) := by
  let θ : A := theta x d
  let ev : Polynomial ℚ →+* A :=
    Polynomial.eval₂RingHom' (algebraMap ℚ A) θ (fun q => Algebra.commutes q θ)
  have hfall : ev (fallingPoly n) = x ^ n * d ^ n := by
    rw [eval_fallingPoly x d ev
      (by change Polynomial.eval₂ (algebraMap ℚ A) θ Polynomial.X = _
          exact Polynomial.eval₂_X (algebraMap ℚ A) θ)
      (by intro q
          change Polynomial.eval₂ (algebraMap ℚ A) θ (Polynomial.C q) = _
          exact Polynomial.eval₂_C (algebraMap ℚ A) θ)]
    exact (x_pow_mul_d_pow x d h n).symm
  have hrise : ev (risingPoly n) = d ^ n * x ^ n := by
    rw [eval_risingPoly x d ev
      (by change Polynomial.eval₂ (algebraMap ℚ A) θ Polynomial.X = _
          exact Polynomial.eval₂_X (algebraMap ℚ A) θ)
      (by intro q
          change Polynomial.eval₂ (algebraMap ℚ A) θ (Polynomial.C q) = _
          exact Polynomial.eval₂_C (algebraMap ℚ A) θ)]
    exact (d_pow_mul_x_pow x d h n).symm
  have hev := congrArg ev hab
  rw [map_add, map_mul, map_mul, hfall, hrise, map_one] at hev
  refine ⟨ev b * d ^ n, ev a, ?_⟩
  rw [mul_assoc]
  rw [add_comm] at hev
  exact hev.symm

/- The Euler products are coprime over `ℚ`, so the coefficient hypothesis in
the transfer theorem is available in every degree. -/
theorem pure_power_weyl_certificate_exists
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    ∃ p q : A, 1 = p * (x ^ n) + q * (x ^ n * d ^ n) := by
  rcases fallingPoly_isCoprime_risingPoly n with ⟨a, b, hab⟩
  exact pure_power_weyl_certificate x d h n a b hab

/-- The two Euler products admit a Bezout identity with right cofactors.
This is the orientation used by the canonical right quotient. -/
theorem euler_products_right_bezout_exists
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    ∃ u v : A,
      (d ^ n * x ^ n) * u + (x ^ n * d ^ n) * v = 1 := by
  rcases fallingPoly_isCoprime_risingPoly n with ⟨a, b, hab⟩
  let θ : A := theta x d
  let ev : Polynomial ℚ →+* A :=
    Polynomial.eval₂RingHom' (algebraMap ℚ A) θ
      (fun q => Algebra.commutes q θ)
  have hfall : ev (fallingPoly n) = x ^ n * d ^ n := by
    rw [eval_fallingPoly x d ev
      (by change Polynomial.eval₂ (algebraMap ℚ A) θ Polynomial.X = _
          exact Polynomial.eval₂_X (algebraMap ℚ A) θ)
      (by intro q
          change Polynomial.eval₂ (algebraMap ℚ A) θ (Polynomial.C q) = _
          exact Polynomial.eval₂_C (algebraMap ℚ A) θ)]
    exact (x_pow_mul_d_pow x d h n).symm
  have hrise : ev (risingPoly n) = d ^ n * x ^ n := by
    rw [eval_risingPoly x d ev
      (by change Polynomial.eval₂ (algebraMap ℚ A) θ Polynomial.X = _
          exact Polynomial.eval₂_X (algebraMap ℚ A) θ)
      (by intro q
          change Polynomial.eval₂ (algebraMap ℚ A) θ (Polynomial.C q) = _
          exact Polynomial.eval₂_C (algebraMap ℚ A) θ)]
    exact (d_pow_mul_x_pow x d h n).symm
  have hpoly : risingPoly n * b + fallingPoly n * a = 1 := by
    rw [mul_comm (risingPoly n) b, mul_comm (fallingPoly n) a, add_comm]
    exact hab
  have hev := congrArg ev hpoly
  rw [map_add, map_mul, map_mul, hrise, hfall, map_one] at hev
  exact ⟨ev b, ev a, hev⟩

#print axioms euler_products_right_bezout_exists

/-- The right Bezout cofactors may be retained as rational polynomials in the
Euler element. -/
theorem euler_products_polynomial_right_bezout_exists
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    ∃ u v : Polynomial ℚ,
      (d ^ n * x ^ n) * eulerPolynomialEval x d u +
        (x ^ n * d ^ n) * eulerPolynomialEval x d v = 1 := by
  rcases fallingPoly_isCoprime_risingPoly n with ⟨a, b, hab⟩
  have hfall : eulerPolynomialEval x d (fallingPoly n) =
      x ^ n * d ^ n := by
    rw [eval_fallingPoly x d (eulerPolynomialEval x d)
      (by rw [eulerPolynomialEval_X]; rfl) (by intro q; simp)]
    exact (x_pow_mul_d_pow x d h n).symm
  have hrise : eulerPolynomialEval x d (risingPoly n) =
      d ^ n * x ^ n := by
    rw [eval_risingPoly x d (eulerPolynomialEval x d)
      (by rw [eulerPolynomialEval_X]; rfl) (by intro q; simp)]
    exact (d_pow_mul_x_pow x d h n).symm
  have hpoly : risingPoly n * b + fallingPoly n * a = 1 := by
    rw [mul_comm (risingPoly n) b, mul_comm (fallingPoly n) a, add_comm]
    exact hab
  have hev := congrArg (eulerPolynomialEval x d) hpoly
  rw [map_add, map_mul, map_mul, hrise, hfall, map_one] at hev
  exact ⟨b, a, hev⟩

#print axioms euler_products_polynomial_right_bezout_exists

theorem pure_power_translate_weyl_certificate_exists
    (x d c : A) (h : d * x = x * d + 1)
    (hcd : Commute c d) (n : ℕ) :
    ∃ p q : A, 1 = p * ((x - c) ^ n) + q * ((x - c) ^ n * d ^ n) := by
  have hshift : d * (x - c) = (x - c) * d + 1 := by
    calc
      d * (x - c) = d * x - d * c := by rw [mul_sub]
      _ = x * d + 1 - c * d := by rw [h, ← hcd.eq]
      _ = (x - c) * d + 1 := by rw [sub_mul]; noncomm_ring
  exact pure_power_weyl_certificate_exists (x - c) d hshift n

/-- A nilpotent central constant can be added to a pure power without losing
the Weyl--Bézout certificate.  This is the formal constant-coefficient
instance of the nilpotent thickening step; the general nilpotent coefficient
ideal is deliberately not hidden in this statement. -/
theorem nilpotent_constant_weyl_certificate_exists
    (x d e : A) (h : d * x = x * d + 1)
    (he : IsNilpotent e) (hcentral : ∀ a : A, Commute e a) (n : ℕ) :
    ∃ p q : A,
      1 = p * (x ^ n - e) + q * ((x ^ n - e) * d ^ n) := by
  rcases fallingPoly_isCoprime_risingPoly n with ⟨a, b, hab⟩
  have hpow := pure_power_weyl_certificate x d h n a b hab
  rcases hpow with ⟨p0, q0, hpow⟩
  let H : A := x ^ n - e
  let r : A := p0 * e + q0 * (e * d ^ n)
  have hrewrite :
      1 - r = p0 * H + q0 * (H * d ^ n) := by
    dsimp [r, H]
    have hx : x ^ n = (x ^ n - e) + e := by noncomm_ring
    rw [hpow, hx]
    noncomm_ring
  have hcomm : Commute e (p0 + q0 * d ^ n) := hcentral _
  have hr : r = e * (p0 + q0 * d ^ n) := by
    dsimp [r]
    calc
      p0 * e + q0 * (e * d ^ n) = e * p0 + (q0 * e) * d ^ n := by
        rw [← hcentral p0 |>.eq]
        noncomm_ring
      _ = e * p0 + (e * q0) * d ^ n := by rw [hcentral q0 |>.eq]
      _ = e * (p0 + q0 * d ^ n) := by noncomm_ring
  have hrnil : IsNilpotent r := by
    rw [hr]
    exact hcomm.isNilpotent_mul_right he
  rcases hrnil with ⟨N, hN⟩
  let g : A := ∑ i ∈ Finset.range N, r ^ i
  have hgeom : g * (1 - r) = 1 - r ^ N := by
    dsimp [g]
    rw [show (1 : A) - r = -(r - 1) by noncomm_ring, mul_neg]
    rw [geom_sum_mul]
    noncomm_ring
  have hone : (1 : A) = g * (1 - r) := by
    rw [hgeom, hN, sub_zero]
  have hfinal :
      1 = (g * p0) * H + (g * q0) * (H * d ^ n) := by
    calc
      1 = g * (1 - r) := hone
      _ = g * (p0 * H + q0 * (H * d ^ n)) := by rw [hrewrite]
      _ = (g * p0) * H + (g * q0) * (H * d ^ n) := by noncomm_ring
  refine ⟨g * p0, g * q0, ?_⟩
  simpa [H] using hfinal

end
end Stafford
