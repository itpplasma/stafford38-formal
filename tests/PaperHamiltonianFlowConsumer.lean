module
public import Stafford38.Geometry.PaperHamiltonianFlow

@[expose] public section

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.PaperHamiltonianFlow
open Stafford38.Geometry.PointwiseConormalContainment

/-! The expected positive shift is fixed independently by the paper's
Hamiltonian convention: at x=2, df for f=x² is 4, so time 5 sends ξ=3 to 23. -/
example :
    MvPolynomial.eval
      (paperHamiltonianFlowPoint
        (Sum.elim (fun _ : Fin 1 => (2 : ℚ)) (fun _ : Fin 1 => (3 : ℚ)))
        (MvPolynomial.X (0 : Fin 1) ^ 2) 5)
      (MvPolynomial.X (Sum.inr (0 : Fin 1))) = 23 := by
  norm_num [paperHamiltonianFlowPoint, differentialAt, MvPolynomial.pderiv_pow]

example {k : Type*} [Field k] [CharZero k] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n ⊕ Fin n) k))
    (hJ : IsBaseRelativePoisson J) (z : (Fin n ⊕ Fin n) → k)
    (hz : ∀ q ∈ J, MvPolynomial.eval z q = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (t : k) :
    ∀ q ∈ J, MvPolynomial.eval
      (Sum.elim (fun i => z (Sum.inl i))
        (fun i => z (Sum.inr i) + t * differentialAt (fun j => z (Sum.inl j)) f i)) q = 0 := by
  intro q hq
  have hpoint : paperHamiltonianFlowPoint z f t =
      Sum.elim (fun i => z (Sum.inl i))
        (fun i => z (Sum.inr i) + t * differentialAt (fun j => z (Sum.inl j)) f i) := by
    funext i
    cases i <;> rfl
  rw [← hpoint]
  exact paperHamiltonianFlow_preserves_commonZero J hJ z hz f hf q hq t

/-! At x=2, the combined differential of 5*x²+x³ is 20+12=32.
The zero-start combination therefore has fibre 32, and applying the two
flows to fibre 3 gives 35. These values are independent coordinate oracles. -/
example :
    MvPolynomial.eval
      (paperHamiltonianFlowsPoint
        (Sum.elim (fun _ : Fin 1 => (2 : ℚ)) (fun _ : Fin 1 => (3 : ℚ)))
        (fun j : Fin 2 =>
          if j = 0 then MvPolynomial.X (0 : Fin 1) ^ 2
          else MvPolynomial.X (0 : Fin 1) ^ 3)
        (fun j : Fin 2 => if j = 0 then 5 else 1) Finset.univ)
      (MvPolynomial.X (Sum.inr (0 : Fin 1))) = 35 := by
  norm_num [paperHamiltonianFlowsPoint, differentialAt, MvPolynomial.pderiv_pow]

example :
    differentialCombinationPoint
      (fun _ : Fin 1 => (2 : ℚ))
      (fun j : Fin 2 => if j = 0 then 5 else 1)
      (fun j : Fin 2 =>
        if j = 0 then MvPolynomial.X (0 : Fin 1) ^ 2
        else MvPolynomial.X (0 : Fin 1) ^ 3)
      (Sum.inr (0 : Fin 1)) = 32 := by
  rw [differentialCombinationPoint_inr]
  norm_num [differentialAt, MvPolynomial.pderiv_pow]

#print axioms paperHamiltonianFlow_preserves_commonZero
#print axioms paperHamiltonianFlows_preserve_commonZero
#print axioms affineConormal_coordinatePoint_isCommonZero
