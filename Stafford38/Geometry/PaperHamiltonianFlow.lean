module
public import Stafford38.Characteristic.BaseRelativePoisson
public import Stafford38.Geometry.AffineConormalSpan

@[expose] public section

/-!
# Hamiltonian flows in the paper's proof

The paper moves a common zero along the Hamiltonian flow of a base equation.
This file proves that statement directly from the base-relative Poisson
condition, by finite Taylor expansion on the affine fibre line.  The argument
does not assume translation stability as an axiom or as a prior theorem.
-/

namespace Stafford38.Geometry.PaperHamiltonianFlow

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.PointwiseConormalContainment

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

/-- Public paper-route name for the canonical affine fibre-line polynomial
from `CoisotropicTranslation`. -/
abbrev affineFibreLinePolynomial
    (y xi v : Fin n → k) (g : SymbolRing k n) : Polynomial k :=
  Stafford38.Geometry.CoisotropicTranslation.affineFibreLinePolynomial y xi v g

theorem affineFibreLinePolynomial_eq_canonical
    (y xi v : Fin n → k) (g : SymbolRing k n) :
    affineFibreLinePolynomial y xi v g =
      Stafford38.Geometry.CoisotropicTranslation.affineFibreLinePolynomial y xi v g := rfl

@[simp] theorem affineFibreLinePolynomial_C
    (y xi v : Fin n → k) (a : k) :
    affineFibreLinePolynomial y xi v (MvPolynomial.C a) = Polynomial.C a := by
  simp [affineFibreLinePolynomial, Stafford38.Geometry.CoisotropicTranslation.affineFibreLinePolynomial]

@[simp] theorem affineFibreLinePolynomial_zero
    (y xi v : Fin n → k) :
    affineFibreLinePolynomial y xi v 0 = 0 := by
  simp [affineFibreLinePolynomial, Stafford38.Geometry.CoisotropicTranslation.affineFibreLinePolynomial]

@[simp] theorem affineFibreLinePolynomial_add
    (y xi v : Fin n → k) (g h : SymbolRing k n) :
    affineFibreLinePolynomial y xi v (g + h) =
      affineFibreLinePolynomial y xi v g + affineFibreLinePolynomial y xi v h := by
  simp [affineFibreLinePolynomial, Stafford38.Geometry.CoisotropicTranslation.affineFibreLinePolynomial]

@[simp] theorem affineFibreLinePolynomial_mul
    (y xi v : Fin n → k) (g h : SymbolRing k n) :
    affineFibreLinePolynomial y xi v (g * h) =
      affineFibreLinePolynomial y xi v g * affineFibreLinePolynomial y xi v h := by
  simp [affineFibreLinePolynomial, Stafford38.Geometry.CoisotropicTranslation.affineFibreLinePolynomial]

theorem affineFibreLinePolynomial_sum {ι : Type*} [Fintype ι]
    (y xi v : Fin n → k) (g : ι → SymbolRing k n) :
    affineFibreLinePolynomial y xi v (∑ i, g i) =
      ∑ i, affineFibreLinePolynomial y xi v (g i) := by
  simp [affineFibreLinePolynomial, Stafford38.Geometry.CoisotropicTranslation.affineFibreLinePolynomial]

@[simp] theorem affineFibreLinePolynomial_X_base
    (y xi v : Fin n → k) (i : Fin n) :
    affineFibreLinePolynomial y xi v (MvPolynomial.X (Sum.inl i)) =
      Polynomial.C (y i) := by
  simp [affineFibreLinePolynomial, Stafford38.Geometry.CoisotropicTranslation.affineFibreLinePolynomial]

@[simp] theorem affineFibreLinePolynomial_X_fibre
    (y xi v : Fin n → k) (i : Fin n) :
    affineFibreLinePolynomial y xi v (MvPolynomial.X (Sum.inr i)) =
      Polynomial.C (xi i) + Polynomial.C (v i) * Polynomial.X := by
  simp [affineFibreLinePolynomial, Stafford38.Geometry.CoisotropicTranslation.affineFibreLinePolynomial]

theorem derivative_affineFibreLinePolynomial
    (y xi v : Fin n → k) (g : SymbolRing k n) :
    Polynomial.derivative (affineFibreLinePolynomial y xi v g) =
      affineFibreLinePolynomial y xi v (verticalDeriv v g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [verticalDeriv]
  | add p q hp hq =>
      simp only [affineFibreLinePolynomial_add, Polynomial.derivative_add, hp, hq]
      rw [verticalDeriv_add, affineFibreLinePolynomial_add]
  | mul_X p i hp =>
      rcases i with i | i
      · simp only [affineFibreLinePolynomial_mul, affineFibreLinePolynomial_X_base,
          Polynomial.derivative_mul, Polynomial.derivative_C, hp]
        simp [verticalDeriv_mul]
      · simp only [affineFibreLinePolynomial_mul, affineFibreLinePolynomial_X_fibre,
          Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_C,
          Polynomial.derivative_mul, Polynomial.derivative_X, zero_mul, zero_add,
          mul_one, hp]
        simp [verticalDeriv_mul]

theorem eval_affineFibreLinePolynomial (y xi v : Fin n → k)
    (g : SymbolRing k n) (t : k) :
    Polynomial.eval t (affineFibreLinePolynomial y xi v g) =
      MvPolynomial.eval (Sum.elim y (fun i => xi i + t * v i)) g := by
  exact Stafford38.Geometry.CoisotropicTranslation.eval_affineFibreLinePolynomial
    y xi v g t

theorem eval_zero_affineFibreLinePolynomial (y xi v : Fin n → k)
    (g : SymbolRing k n) :
    Polynomial.eval 0 (affineFibreLinePolynomial y xi v g) =
      MvPolynomial.eval (Sum.elim y xi) g := by
  rw [eval_affineFibreLinePolynomial]
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  rcases i with i | i <;> simp

theorem affineFibreLinePolynomial_baseLift
    (y xi v : Fin n → k) (f : MvPolynomial (Fin n) k) :
    affineFibreLinePolynomial y xi v (baseLift f) =
      Polynomial.C (MvPolynomial.eval y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [baseLift, affineFibreLinePolynomial]
  | add p q hp hq => simp [hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
      rw [map_mul, affineFibreLinePolynomial_mul, hp,
        MvPolynomial.eval_mul, MvPolynomial.eval_X]
      simp [baseLift]

theorem affineFibreLinePolynomial_baseLift_pderiv
    (y xi v : Fin n → k) (f : MvPolynomial (Fin n) k) (i : Fin n) :
    affineFibreLinePolynomial y xi v
      (MvPolynomial.pderiv (Sum.inl i) (baseLift f)) =
        Polynomial.C (differentialAt y f i) := by
  rw [pderiv_baseLift_base, affineFibreLinePolynomial_baseLift]
  rfl

theorem affineFibreLinePolynomial_poissonBracket_baseLift
    (y xi : Fin n → k) (f : MvPolynomial (Fin n) k) (g : SymbolRing k n) :
    affineFibreLinePolynomial y xi (differentialAt y f)
      (poissonBracket (baseLift f) g) =
    affineFibreLinePolynomial y xi (differentialAt y f)
      (verticalDeriv (differentialAt y f) g) := by
  simp only [poissonBracket, pderiv_baseLift_base, pderiv_baseLift_fibre, zero_mul,
    sub_zero, verticalDeriv]
  rw [affineFibreLinePolynomial_sum, affineFibreLinePolynomial_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [← pderiv_baseLift_base, affineFibreLinePolynomial_baseLift_pderiv]

theorem iterate_derivative_affineFibreLinePolynomial
    (y xi : Fin n → k) (f : MvPolynomial (Fin n) k)
    (g : SymbolRing k n) (m : ℕ) :
    (Polynomial.derivative^[m])
      (affineFibreLinePolynomial y xi (differentialAt y f) g) =
        affineFibreLinePolynomial y xi (differentialAt y f) (hamiltonIter f m g) := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [Function.iterate_succ_apply', hm, derivative_affineFibreLinePolynomial,
        ← affineFibreLinePolynomial_poissonBracket_baseLift]
      rfl

/-- The paper's Hamiltonian map: base fixed and fibre translated by `t df_y`.
This is the arbitrary-start specialization of the shared affine fibre-point map. -/
abbrev paperHamiltonianFlowPoint (z : PhaseVar n → k)
    (f : MvPolynomial (Fin n) k) (t : k) : PhaseVar n → k :=
  Stafford38.Geometry.CoisotropicTranslation.affineFibreTranslatePoint
    (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i))
    (differentialAt (fun j => z (Sum.inl j)) f) t

theorem paperHamiltonianFlowPoint_eq_affineFibreTranslatePoint
    (z : PhaseVar n → k) (f : MvPolynomial (Fin n) k) (t : k) :
    paperHamiltonianFlowPoint z f t =
      Stafford38.Geometry.CoisotropicTranslation.affineFibreTranslatePoint
        (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i))
        (differentialAt (fun j => z (Sum.inl j)) f) t := rfl

/-- Apply a finite family of the paper's commuting Hamiltonian translations.
Since each flow fixes the base coordinates, this is the canonical affine
fibre translation whose direction is the sum of the individual directions. -/
abbrev paperHamiltonianFlowsPoint {ι : Type*} [DecidableEq ι]
    (z : PhaseVar n → k) (f : ι → MvPolynomial (Fin n) k)
    (t : ι → k) (s : Finset ι) : PhaseVar n → k :=
  affineFibreTranslatePoint
    (fun i => z (Sum.inl i))
    (fun i => z (Sum.inr i))
    (fun i => s.sum (fun j =>
      t j * differentialAt (fun l => z (Sum.inl l)) (f j) i))
    1

@[simp] theorem paperHamiltonianFlowsPoint_inl {ι : Type*} [DecidableEq ι]
    (z : PhaseVar n → k) (f : ι → MvPolynomial (Fin n) k)
    (t : ι → k) (s : Finset ι) (i : Fin n) :
    paperHamiltonianFlowsPoint z f t s (Sum.inl i) = z (Sum.inl i) := rfl

@[simp] theorem paperHamiltonianFlowsPoint_inr {ι : Type*} [DecidableEq ι]
    (z : PhaseVar n → k) (f : ι → MvPolynomial (Fin n) k)
    (t : ι → k) (s : Finset ι) (i : Fin n) :
    paperHamiltonianFlowsPoint z f t s (Sum.inr i) =
      z (Sum.inr i) + s.sum (fun j =>
        t j * differentialAt (fun l => z (Sum.inl l)) (f j) i) := by
  simp [paperHamiltonianFlowsPoint, affineFibreTranslatePoint]

theorem paperHamiltonianFlowPoint_paperHamiltonianFlowsPoint_insert
    {ι : Type*} [DecidableEq ι]
    (z : PhaseVar n → k) (f : ι → MvPolynomial (Fin n) k)
    (t : ι → k) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    paperHamiltonianFlowPoint (paperHamiltonianFlowsPoint z f t s) (f i) (t i) =
      paperHamiltonianFlowsPoint z f t (insert i s) := by
  funext q
  rcases q with q | q
  · rfl
  · simp [paperHamiltonianFlowPoint, affineFibreTranslatePoint,
      paperHamiltonianFlowsPoint, Finset.sum_insert, hi]
    ring

/-- One Hamiltonian flow preserves a common zero of a base-relatively Poisson
ideal. The proof is finite Taylor on the affine fibre line through `z`. -/
theorem paperHamiltonianFlow_preserves_commonZero
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (hJ : IsBaseRelativePoisson J)
    (z : PhaseVar n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval z g = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) (t : k) :
    MvPolynomial.eval (paperHamiltonianFlowPoint z f t) g = 0 := by
  let y : Fin n → k := fun i => z (Sum.inl i)
  let xi : Fin n → k := fun i => z (Sum.inr i)
  have hz : Sum.elim y xi = z := by
    funext i
    rcases i with i | i <;> simp [y, xi]
  have hline : affineFibreLinePolynomial y xi (differentialAt y f) g = 0 := by
    apply polynomial_eq_zero_of_eval_iterate_derivative_zero
    intro m
    rw [iterate_derivative_affineFibreLinePolynomial,
      eval_zero_affineFibreLinePolynomial]
    rw [hz]
    exact hzero _ (hamiltonIter_mem_of_isBaseRelativePoisson J hJ f hf g hg m)
  have heval :
      MvPolynomial.eval (paperHamiltonianFlowPoint z f t) g =
        Polynomial.eval t (affineFibreLinePolynomial y xi (differentialAt y f) g) := by
    rw [eval_affineFibreLinePolynomial]
    apply MvPolynomial.eval₂_congr
    intro i c hi hc
    rcases i with i | i <;> simp [paperHamiltonianFlowPoint, affineFibreTranslatePoint, y, xi]
  rw [heval, hline]
  exact Polynomial.eval_zero

/-- Any finite composition preserves a common zero, from an arbitrary starting
covector. -/
theorem paperHamiltonianFlows_preserve_commonZero
    [CharZero k] {ι : Type*} [DecidableEq ι]
    (J : Ideal (SymbolRing k n)) (hJ : IsBaseRelativePoisson J)
    (z : PhaseVar n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval z g = 0)
    (f : ι → MvPolynomial (Fin n) k)
    (hf : ∀ i, baseLift (f i) ∈ J) (t : ι → k) (s : Finset ι) :
    ∀ g ∈ J, MvPolynomial.eval (paperHamiltonianFlowsPoint z f t s) g = 0 := by
  induction s using Finset.induction_on with
  | empty =>
      intro g hg
      have hpoint : paperHamiltonianFlowsPoint z f t ∅ = z := by
        funext q
        rcases q with q | q <;> simp [paperHamiltonianFlowsPoint]
      rw [hpoint]
      exact hzero g hg
  | @insert i s hi ih =>
      intro g hg
      rw [← paperHamiltonianFlowPoint_paperHamiltonianFlowsPoint_insert
        z f t s i hi]
      exact paperHamiltonianFlow_preserves_commonZero J hJ
        (paperHamiltonianFlowsPoint z f t s) ih (f i) (hf i) g hg (t i)

/-- The affine conormal consumer using the paper's finite successive-flow
argument. Every covector in the equation-defined conormal space is a finite
linear combination of equation differentials. -/
theorem affineConormal_coordinatePoint_isCommonZero
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (hJ : IsBaseRelativePoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hlift : ∀ f : I, baseLift f.1 ∈ J)
    (xi : Fin n → k)
    (hxi : coordinateCovector xi ∈ affineConormalSpace y I) :
    ∀ g ∈ J, MvPolynomial.eval (Sum.elim y xi) g = 0 := by
  classical
  obtain ⟨c, hc⟩ :=
    coordinate_mem_affineConormalSpace_exists_finsupp y xi I hxi
  let ι := {f : I // f ∈ c.support}
  let equations : ι → MvPolynomial (Fin n) k := fun f => f.1.1
  let parameters : ι → k := fun f => c f.1
  have hflows :
      paperHamiltonianFlowsPoint (zeroSectionPoint y) equations parameters
        Finset.univ = differentialCombinationPoint y parameters equations := by
    funext q
    rcases q with i | i
    · simp [zeroSectionPoint, paperHamiltonianFlowsPoint,
        differentialCombinationPoint]
    · simp [paperHamiltonianFlowsPoint, differentialCombinationPoint,
        parameters, equations, zeroSectionPoint, differentialAt_baseLinearCombination]
  have hpoint : differentialCombinationPoint y parameters equations = Sum.elim y xi := by
    funext q
    rcases q with i | i
    · rfl
    · rw [differentialCombinationPoint_inr]
      simp only [parameters, equations, Sum.elim_inr]
      rw [hc i]
      exact (Finset.sum_subtype c.support (by simp)
        (fun f => c f * differentialAt y f.1 i)).symm
  rw [← hpoint, ← hflows]
  exact paperHamiltonianFlows_preserve_commonZero J hJ (zeroSectionPoint y)
    hzero equations (fun f => hlift f.1) parameters Finset.univ

theorem paperHamiltonianFlowPoint_compose
    (z : PhaseVar n → k) (f g : MvPolynomial (Fin n) k) (s t : k) :
    paperHamiltonianFlowPoint (paperHamiltonianFlowPoint z f s) g t =
      Sum.elim (fun i => z (Sum.inl i))
        (fun i => z (Sum.inr i) + s * differentialAt (fun j => z (Sum.inl j)) f i +
          t * differentialAt (fun j => z (Sum.inl j)) g i) := by
  funext i
  rcases i with i | i <;> simp [paperHamiltonianFlowPoint, affineFibreTranslatePoint]

theorem paperHamiltonianFlowPoint_commute
    (z : PhaseVar n → k) (f g : MvPolynomial (Fin n) k) (s t : k) :
    paperHamiltonianFlowPoint (paperHamiltonianFlowPoint z f s) g t =
      paperHamiltonianFlowPoint (paperHamiltonianFlowPoint z g t) f s := by
  rw [paperHamiltonianFlowPoint_compose, paperHamiltonianFlowPoint_compose]
  congr 1
  funext i
  ring

/-- One Hamiltonian flow preserves a common zero of a base-relatively Poisson
ideal.  The proof is finite Taylor on the affine fibre line through `z`. -/
theorem two_paperHamiltonianFlows_preserve_commonZero
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (hJ : IsBaseRelativePoisson J)
    (z : PhaseVar n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval z g = 0)
    (f g : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J) (hg : baseLift g ∈ J)
    (s t : k) (h : SymbolRing k n) (hh : h ∈ J) :
    MvPolynomial.eval
      (paperHamiltonianFlowPoint (paperHamiltonianFlowPoint z f s) g t) h = 0 := by
  apply paperHamiltonianFlow_preserves_commonZero J hJ _ _ g hg h hh t
  intro q hq
  exact paperHamiltonianFlow_preserves_commonZero J hJ z hzero f hf q hq s

#print axioms derivative_affineFibreLinePolynomial
#print axioms iterate_derivative_affineFibreLinePolynomial
#print axioms paperHamiltonianFlowPoint_compose
#print axioms paperHamiltonianFlowPoint_commute
#print axioms paperHamiltonianFlow_preserves_commonZero
#print axioms two_paperHamiltonianFlows_preserve_commonZero
#print axioms paperHamiltonianFlows_preserve_commonZero
#print axioms affineConormal_coordinatePoint_isCommonZero

end

end Stafford38.Geometry.PaperHamiltonianFlow
