module
public import Stafford38.Geometry.HomogenizedAffineEvaluation
public import Stafford38.Geometry.GenericSmoothOpen
public import Stafford38.Geometry.SmoothAffinePointScalarExtension
public import Stafford38.Geometry.SmoothAffineConormal
public import Stafford38.Geometry.ScalarExtensionPoints
public import Stafford38.Geometry.ProjectiveConormalDehomogenization
public import Stafford38.Geometry.ProjectiveEquationFormalChart

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Stafford38.Geometry.ActualAffineSmoothPointFromNumerator

open Stafford38.Geometry.HomogenizedAffineEvaluation
open Stafford38.Geometry.ProjectiveEquationFormalChart
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.LocalizedProjectiveChartTransition
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.SmoothAffinePointScalarExtension
open Stafford38.Geometry.SmoothAffineConormal
noncomputable section

universe u

/-- A nonzero homogenized numerator at a nonzero projective coordinate gives
an actual smooth point of the original affine quotient, after dehomogenizing
through the given quotient map. -/
theorem smoothAffinePoint_of_homogenized_eval
    {k L : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    [Field L] [Algebra k L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (p : MvPolynomial (Fin n) k)
    (fbar : MvPolynomial (Fin n) k ⧸ I)
    (hrep : Ideal.Quotient.mk I p = fbar)
    (φ : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] L)
    (q : Fin (n + 1) → L)
    (hdehom : dehomogenizedPoint q =
      fun i => φ (Ideal.Quotient.mk I (MvPolynomial.X i)))
    (hq₀ : q 0 ≠ 0)
    (hsmooth : Algebra.Smooth k (Localization.Away fbar))
    (hnumerator : MvPolynomial.eval q
      (MvPolynomial.map (algebraMap k L) (homogenizeAtZero p)) ≠ 0) :
    SmoothAffinePoint (k := L)
      (I.map (scalarPolynomialMap (k := k) (K := L) (Fin n)))
      (dehomogenizedPoint q) := by
  let φP : MvPolynomial (Fin n) k →ₐ[k] L :=
    φ.comp (Ideal.Quotient.mkₐ k I)
  have hφeval : ∀ r : MvPolynomial (Fin n) k,
      MvPolynomial.eval₂ (algebraMap k L)
        (fun i => φP (MvPolynomial.X i)) r = φP r := by
    intro r
    have hunique := MvPolynomial.aeval_unique φP
    have hpoint : φP = MvPolynomial.aeval (fun i => φP (MvPolynomial.X i)) := by
      convert hunique using 1 <;> rfl
    have heq := congrArg
      (fun ψ : MvPolynomial (Fin n) k →ₐ[k] L => ψ r) hpoint.symm
    simpa only [MvPolynomial.aeval_def] using heq
  have hdehom_eval :
      MvPolynomial.eval (dehomogenizedPoint q)
        (MvPolynomial.map (algebraMap k L) p) = φP p := by
    rw [hdehom]
    rw [← MvPolynomial.eval₂_eq_eval_map]
    change MvPolynomial.eval₂ (algebraMap k L)
      (fun i => φP (MvPolynomial.X i)) p = φP p
    exact hφeval p
  have havoid : φ fbar ≠ 0 := by
    rw [map_homogenizeAtZero] at hnumerator
    rw [eval_homogenizeAtZero_eq_pow_mul_dehomogenizedPoint
      (MvPolynomial.map (algebraMap k L) p) q hq₀,
      hdehom_eval,
      show φP p = φ (Ideal.Quotient.mk I p) from rfl,
      hrep] at hnumerator
    exact (mul_ne_zero_iff.mp hnumerator).2
  rw [hdehom]
  exact smoothAffinePoint_of_quotient_point_avoiding_smooth_away
    (k := k) (L := L) I fbar hsmooth φ havoid


end

end Stafford38.Geometry.ActualAffineSmoothPointFromNumerator
