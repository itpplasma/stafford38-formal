module

public import Stafford38.Paper.Section2.Geometry
public import Stafford38.Characteristic.SymplecticCompletion
public import Stafford38.Characteristic.PostScalarExtensionPoisson
public import Stafford38.Paper.Support.Gabber
public import Stafford38.Paper.Section2.CharacteristicVariety

@[expose] public section

/-!
# Section 2 of the paper: Definitions 2.8–2.10 and Theorem 2.11

Definition 2.8 (symplectic forms, the standard form  on ,
symplectic bases, Gram matrices), Definition 2.9 (the Poisson bracket),
Definition 2.10 (involutive ideals and closed sets) and Theorem 2.11 (Gabber).
-/

open LinearMap (BilinForm)
open Module

namespace Stafford38.Paper.Section2

open Stafford38.Characteristic
open Stafford38.CharacteristicSymplecticCompletion
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylSymplectic

noncomputable section

universe u v w

section Abstract

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

/-- **Definition 2.8 (symplectic form).** `ω` is antisymmetric and
nondegenerate (`ω(u, ·) = 0` forces `u = 0`). -/
def IsSymplectic (ω : BilinForm k V) : Prop :=
  (∀ x y, ω x y = -ω y x) ∧ ω.Nondegenerate

/-- **Definition 2.8 (Gram matrix).** `J = (ω(b_i, b_j))_{ij}`. -/
def gramMatrix {ι : Type*} (ω : BilinForm k V) (b : ι → V) : Matrix ι ι k :=
  fun i j => ω (b i) (b j)

/-- **Definition 2.8 (symplectic basis).** `e_1, …, e_n, f_1, …, f_n` with
`ω(e_i, f_j) = δ_ij` and `ω(e_i, e_j) = ω(f_i, f_j) = 0`. -/
def IsSymplecticBasis {n : ℕ} (ω : BilinForm k V) (b : Basis (Fin n ⊕ Fin n) k V) :
    Prop :=
  (∀ i j, ω (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) ∧
    (∀ i j, ω (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
    (∀ i j, ω (b (Sum.inr i)) (b (Sum.inr j)) = 0)

/-- In characteristic zero an antisymmetric form is alternating. -/
theorem alternating_of_antisymmetric [CharZero k] (ω : BilinForm k V)
    (hanti : ∀ x y, ω x y = -ω y x) (x : V) : ω x x = 0 := by
  have h := hanti x x
  have h2 : (2 : k) * ω x x = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

end Abstract

variable (k : Type u) [Field k]

/-- **Definition 2.8 (standard symplectic form).** On `𝕍 = k^{2n}` with basis
`x_1, …, x_n, ∂_1, …, ∂_n`, `ω(u, v) = ∑_i (u_{x_i} v_{∂_i} - u_{∂_i} v_{x_i})`,
so `ω(x_i, ∂_j) = δ_ij` and `ω(x_i, x_j) = ω(∂_i, ∂_j) = 0`.  It is the
negative of the repository's `phasePairing`, which uses the opposite sign
convention. -/
def omega (n : ℕ) : BilinForm k (PhaseVar n → k) :=
  LinearMap.mk₂ k (fun u v => -phasePairing k u v)
    (fun u v w => by rw [phasePairing_add_left, neg_add])
    (fun c u v => by rw [phasePairing_smul_left, smul_eq_mul, mul_neg])
    (fun u v w => by rw [phasePairing_add_right, neg_add])
    (fun c u v => by rw [phasePairing_smul_right, smul_eq_mul, mul_neg])

theorem omega_apply {n : ℕ} (u v : PhaseVar n → k) :
    omega k n u v = -phasePairing k u v := rfl

theorem omega_antisymm {n : ℕ} (u v : PhaseVar n → k) :
    omega k n u v = -omega k n v u := by
  simp only [omega_apply, phasePairing_skew k u v, neg_neg]

theorem omega_nondegenerate (n : ℕ) : (omega k n).Nondegenerate := by
  constructor
  · intro x hx
    by_contra hxne
    obtain ⟨z, hz⟩ := exists_phasePairing_right_ne_zero k hxne
    exact hz (neg_eq_zero.mp (hx z))
  · intro y hy
    by_contra hyne
    obtain ⟨z, hz⟩ := exists_phasePairing_left_ne_zero k hyne
    exact hz (neg_eq_zero.mp (hy z))

theorem finrank_phaseSpace (n : ℕ) :
    Module.finrank k (PhaseVar n → k) = 2 * n := by
  rw [Module.finrank_eq_card_basis (Pi.basisFun k (PhaseVar n))]
  simp [two_mul]

/-- The Gram matrix of `ω` in the generator basis is `-J`, where `J` is the
matrix of the Weyl commutators `[u_i, u_j]`. -/
theorem omega_toMatrix (n : ℕ) :
    LinearMap.BilinForm.toMatrix' (omega k n) = -standardForm k n := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix'_apply]
  have hsingle (i : PhaseVar n) : Pi.single i (1 : k) = phaseBasis k i := by
    funext l
    simp [Pi.single_apply, phaseBasis]
  rw [hsingle, hsingle, omega_apply, phasePairing_basis]
  rfl

/-- The Gram matrix of `ω` in the generator basis `x_1, …, ∂_n` is `-J`, where
`J` is the matrix of Weyl commutators `[u_i, u_j]` (`standardForm`). -/
theorem gramMatrix_omega (n : ℕ) :
    gramMatrix (omega k n) (Pi.basisFun k (PhaseVar n)) = -standardForm k n := by
  rw [← omega_toMatrix]
  ext i j
  rw [LinearMap.BilinForm.toMatrix'_apply]
  simp [gramMatrix]

theorem omega_isSymplectic (n : ℕ) : IsSymplectic (omega k n) :=
  ⟨omega_antisymm k, omega_nondegenerate k n⟩

/-- **Definition 2.9 (Poisson bracket).**
`{f, g} = ∑_i (∂f/∂x_i ∂g/∂ξ_i - ∂f/∂ξ_i ∂g/∂x_i)` on `k[x, ξ]`. -/
def poisson {n : ℕ} (f g : SymbolRing k n) : SymbolRing k n :=
  ∑ i : Fin n,
    (MvPolynomial.pderiv (Sum.inl i) f * MvPolynomial.pderiv (Sum.inr i) g -
      MvPolynomial.pderiv (Sum.inr i) f * MvPolynomial.pderiv (Sum.inl i) g)

/-- The printed bracket is the repository's `Characteristic.poissonBracket`,
with the same sign. -/
theorem poisson_eq {n : ℕ} (f g : SymbolRing k n) : poisson k f g = poissonBracket f g :=
  rfl

/-- **Definition 2.10 (involutive ideal).** `{J, J} ⊆ J`. -/
def IsInvolutive {n : ℕ} (J : Ideal (SymbolRing k n)) : Prop :=
  ∀ f ∈ J, ∀ g ∈ J, poisson k f g ∈ J

/-- The printed notion is the repository's
`PostScalarExtensionPoisson.IsInvolutive`. -/
theorem isInvolutive_iff {n : ℕ} (J : Ideal (SymbolRing k n)) :
    IsInvolutive k J ↔ Stafford38.Characteristic.PostScalarExtensionPoisson.IsInvolutive J :=
  Iff.rfl

/-- **Definition 2.10 (involutive closed set).** A closed set `W ⊆ K^{2n}` of
closed points is involutive if `I(W)` is. -/
def IsInvolutiveSet {n : ℕ} (W : Set (PhaseVar n → k)) : Prop :=
  IsInvolutive k (vanishingIdealOf k W)

/-- **Theorem 2.11 (Gabber).** Let `K` be a field of characteristic zero and `M`
a finitely generated right `A_n(K)`-module with a good order filtration `M_•`
(Definition 2.4, `IsGoodFiltration`: compatible and exhaustive, `gr M` finitely
generated over `K[x, ξ]`).  Then `J = √(Ann_{K[x,ξ]} gr M)` is involutive.  The cited result
[Gab81] is proved in `Stafford38.Paper.Support.Gabber`, by reduction to cyclic
modules and the repository's proof of the cyclic case. -/
theorem theorem_2_11 (K : Type u) [Field K] [CharZero K] (n : ℕ)
    {M : Type w} [AddCommGroup M] [Module (Stafford38Challenge.WeylAlg K n)ᵐᵒᵖ M] [Module K M]
    [IsScalarTower K (Stafford38Challenge.WeylAlg K n)ᵐᵒᵖ M]
    [Module.Finite (Stafford38Challenge.WeylAlg K n)ᵐᵒᵖ M]
    (Γ : ℕ → Submodule K M) (hgood : IsGoodFiltration K n Γ) :
    IsInvolutive K (Module.annihilator (SymbolRing K n)
      (Stafford38.Paper.Support.Gabber.GrModule Γ)).radical :=
  (isInvolutive_iff K _).2 (Stafford38.Paper.Support.Gabber.theorem_2_11_general K n Γ
    hgood.compatible hgood.finite)

/-- Theorem 2.11 for the cyclic module `M = A_n(K)/I` with `M_m = qF_m`, the case
used in the proof of Theorem 1.1 (for `Q_K`): for this filtration `gr M` is
`grCyclic` as a `K[x, ξ]`-module. -/
theorem theorem_2_11_cyclic (K : Type u) [Field K] [CharZero K] (n : ℕ)
    (I : RightIdeal (PresentedWeyl K n)) :
    IsInvolutive K (Module.annihilator (SymbolRing K n) (grCyclic K I)).radical := by
  have : Module.Finite (PresentedWeyl K n)ᵐᵒᵖ (RightQuotient I) :=
    Stafford38.Paper.Support.Gabber.rightQuotient_finite I
  rw [← Stafford38.Paper.Support.Gabber.annihilator_qFilt]
  exact theorem_2_11 K n (Stafford38.Paper.Support.Gabber.qFilt K I) (qFilt_isGoodFiltration K I)

#print axioms theorem_2_11
#print axioms theorem_2_11_cyclic

end

end Stafford38.Paper.Section2
