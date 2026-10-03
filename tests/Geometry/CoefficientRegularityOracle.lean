module
public import Stafford38.Geometry.ProjectiveCoefficientLocalization
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open Stafford38.Geometry.ProjectiveCoefficientLocalization

namespace Stafford38.Geometry.CoefficientRegularityOracle

set_option autoImplicit false


theorem constants_two_three_multiply_zero (d : ℕ) :
  (MvPolynomial.C (2 : ZMod 6) : Coeff (ZMod 6) d) *
      MvPolynomial.C (3 : ZMod 6) = 0 := by
  rw [← MvPolynomial.C_mul]
  have h : (2 : ZMod 6) * 3 = 0 := by decide
  rw [h]
  simp

theorem constant_three_nonzero (d : ℕ) :
    MvPolynomial.C (3 : ZMod 6) ≠ (0 : Coeff (ZMod 6) d) := by
  intro h
  have h' : (3 : ZMod 6) = 0 :=
    (MvPolynomial.C_injective (Fin d) (ZMod 6)) (by simpa using h)
  exact (by decide : (3 : ZMod 6) ≠ 0) h'

theorem constant_two_not_regular (d : ℕ) :
    (MvPolynomial.C (2 : ZMod 6) : Coeff (ZMod 6) d) ∉
      nonZeroDivisors (Coeff (ZMod 6) d) := by
  intro h
  have hkill :
      (MvPolynomial.C (2 : ZMod 6) : Coeff (ZMod 6) d) *
        MvPolynomial.C (3 : ZMod 6) = 0 := by
    rw [← MvPolynomial.C_mul]
    have h' : (2 : ZMod 6) * 3 = 0 := by decide
    rw [h']
    simp
  have hzero : MvPolynomial.C (3 : ZMod 6) = 0 :=
    (mem_nonZeroDivisors_iff_left.mp h) _ hkill
  have h3 : (3 : ZMod 6) = 0 :=
    (MvPolynomial.C_injective (Fin d) (ZMod 6)) (by simpa using hzero)
  exact (by decide : (3 : ZMod 6) ≠ 0) h3

#print axioms constants_two_three_multiply_zero
#print axioms constant_three_nonzero
#print axioms constant_two_not_regular

end Stafford38.Geometry.CoefficientRegularityOracle
