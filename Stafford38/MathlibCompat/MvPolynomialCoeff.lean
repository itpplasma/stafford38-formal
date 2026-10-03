import Mathlib.Algebra.MvPolynomial.Basic

/-! Compatibility spelling for sources using `MvPolynomial.coeff m p`.
The canonical operation is the polynomial's coefficient at `m`. -/
namespace MvPolynomial

abbrev coeff {σ : Type*} {R : Type*} [CommSemiring R]
    (m : σ →₀ ℕ) (p : MvPolynomial σ R) : R := AddMonoidAlgebra.coeff p m

@[simp] theorem coeff_zero_compat {σ : Type*} {R : Type*} [CommSemiring R]
    (m : σ →₀ ℕ) : MvPolynomial.coeff m (0 : MvPolynomial σ R) = 0 := by
  simp [MvPolynomial.coeff]

end MvPolynomial
