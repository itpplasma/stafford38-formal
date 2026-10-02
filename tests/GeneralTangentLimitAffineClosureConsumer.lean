import Stafford38.Geometry.GeneralTangentLimitCriterion

/-!
An independent consumer turns the affine zero-locus conclusion into the
pointwise evaluation statement used in vanishing arguments.
-/

namespace GeneralTangentLimitAffineClosureConsumer

open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.ProjectiveConormalDirections

theorem eval_eq_zero_of_directSummand_affine_closure
    {k : Type*} [Field k] [IsAlgClosed k]
    {n dimY : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (L : Submodule (PowerSeries k)
      (Fin (n + 1) → PowerSeries k))
    (D : DirectSummandInput (dimY := dimY) I q L)
    (f : MvPolynomial (Fin n) k)
    (hf : f ∈ MvPolynomial.vanishingIdeal k
      (smoothConormalFibreProjection I)) :
    MvPolynomial.eval
      (fun i : Fin n => if i = D.axis then (1 : k) else 0) f = 0 := by
  have haxis := tangent_limit_affine_fibre_closure_of_directSummand I q L D
  exact (MvPolynomial.mem_zeroLocus_iff.mp haxis) f hf

#print axioms Stafford38.Geometry.GeneralTangentLimitCriterion.tangent_limit_affine_fibre_closure_of_directSummand
#print axioms eval_eq_zero_of_directSummand_affine_closure
#check Stafford38.Geometry.GeneralTangentLimitCriterion.tangent_limit_criterion_of_directSummand

end GeneralTangentLimitAffineClosureConsumer
