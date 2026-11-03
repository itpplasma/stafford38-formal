module

public import Stafford38.Paper.Section3.Symplectic
public import Stafford38.Weyl.SymbolCompatibility
public import Stafford38.Weyl.Universal

@[expose] public section

/-!
# The standard symplectic space `𝕍` and the automorphism `Φ_g`

`𝕍 = k^{2n}` is identified with the Bernstein-degree-one part of `A_n(k)`:
the coordinate `Sum.inl i` of a vector is the coefficient of `x_{i+1}`, the
coordinate `Sum.inr i` that of `∂_{i+1}`.  It carries the standard symplectic
form `ω` of Definition 2.8 (`Stafford38.Paper.Section2.omega`).

For `g` preserving `ω`, the paper's `Φ_g` is the algebra automorphism of
`A_n(k)` extending `u ↦ g(u)` on generators.  We record `g` by the matrix
`M` whose rows are the images of the generators, `g(u_i) = ∑_j M_ij u_j`
(as in the proof of Proposition 3.2); `ω`-preservation of `g` is
`M ∈ Sp(2n, k)`.
-/

open LinearMap (BilinForm)

namespace Stafford38.Paper.Section3

open Stafford
open Stafford38.Characteristic
open Stafford38.CharacteristicSymplecticCompletion
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylSymplectic
open Stafford38.Paper.Section2

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- An `ω`-preserving linear map has symplectic matrix: from
`hᵀ J h = J` the inversion argument of the proof of Proposition 3.2 gives
`h J hᵀ = J`, i.e. `h ∈ Sp(2n, k)`. -/
theorem toMatrix_mem_symplecticGroup {n : ℕ}
    (h : (PhaseVar n → k) →ₗ[k] PhaseVar n → k)
    (hpres : ∀ x y, omega k n (h x) (h y) = omega k n x y) :
    LinearMap.toMatrix' h ∈ Matrix.symplecticGroup (Fin n) k := by
  have hcomp : (omega k n).comp h h = omega k n := by
    apply (LinearMap.BilinForm.ext_iff_basis (Pi.basisFun k (PhaseVar n))).2
    intro i j
    exact hpres _ _
  have hmatrix := LinearMap.BilinForm.toMatrix'_comp (omega k n) h h
  have hgram : LinearMap.BilinForm.toMatrix' (omega k n) = -standardForm k n := by
    rw [← gramMatrix_omega]
    ext i j
    rw [LinearMap.BilinForm.toMatrix'_apply]
    simp [gramMatrix]
  rw [hcomp, hgram] at hmatrix
  have hT : Matrix.transpose (LinearMap.toMatrix' h) * standardForm k n *
      LinearMap.toMatrix' h = standardForm k n := by
    have := congrArg Neg.neg hmatrix
    simpa [Matrix.mul_neg, Matrix.neg_mul] using this.symm
  exact SymplecticGroup.mem_iff'.2 hT

/-- **The automorphism `Φ_g`.**  For `g ∈ Sp(2n, k)`, given by the matrix of
its rows `g(u_i) = ∑_j g_ij u_j`, `Φ_g` is the algebra automorphism of
`A_n(k)` extending `u_i ↦ g(u_i)`; its inverse is built from `g⁻¹`. -/
def phiG {n : ℕ} (g : Matrix.symplecticGroup (Fin n) k) :
    PresentedWeyl k n ≃ₐ[k] PresentedWeyl k n :=
  standardSymplecticAlgEquivOfInverse k g.1 (g⁻¹).1
    (SymplecticGroup.mem_iff.mp g.2) (SymplecticGroup.mem_iff.mp (g⁻¹).2)
    (by
      calc g.1 * (g⁻¹).1 = ((g * g⁻¹ : Matrix.symplecticGroup (Fin n) k) : Matrix _ _ k) :=
            rfl
        _ = 1 := by rw [mul_inv_cancel]; rfl)
    (by
      calc (g⁻¹).1 * g.1 = ((g⁻¹ * g : Matrix.symplecticGroup (Fin n) k) : Matrix _ _ k) :=
            rfl
        _ = 1 := by rw [inv_mul_cancel]; rfl)

theorem phiG_apply {n : ℕ} (g : Matrix.symplecticGroup (Fin n) k) (z : PresentedWeyl k n) :
    phiG k g z = standardSymplecticAlgHom k g.1 (SymplecticGroup.mem_iff.mp g.2) z :=
  rfl

theorem phiG_symm_apply {n : ℕ} (g : Matrix.symplecticGroup (Fin n) k)
    (z : PresentedWeyl k n) :
    (phiG k g).symm z =
      standardSymplecticAlgHom k (g⁻¹).1 (SymplecticGroup.mem_iff.mp (g⁻¹).2) z :=
  rfl

/-- **Construction of `Φ_g` (paragraph after Lemma 3.1).**  Because the
`g(u_i)` satisfy the Weyl relations, `u ↦ g(u)` extends to a unique
`k`-algebra endomorphism `Φ_g`; it is an automorphism with
`Φ_g⁻¹ = Φ_{g⁻¹}`. -/
theorem step_phi_g {n : ℕ} (g : Matrix.symplecticGroup (Fin n) k) :
    (∀ i, phiG k g (freeWeylGenerator (standardForm k n) i) =
      freeWeylLinearCombination g.1 (freeWeylGenerator (standardForm k n)) i) ∧
    (∀ f : PresentedWeyl k n →ₐ[k] PresentedWeyl k n,
      (∀ i, f (freeWeylGenerator (standardForm k n) i) =
        freeWeylLinearCombination g.1 (freeWeylGenerator (standardForm k n)) i) →
      f = (phiG k g).toAlgHom) ∧
    (phiG k g).symm = phiG k g⁻¹ := by
  refine ⟨fun i => by rw [phiG_apply, standardSymplecticAlgHom_generator], ?_, ?_⟩
  · intro f hf
    apply Stafford38.WeylUniversal.freeWeyl_algHom_ext
    intro i
    rw [hf i]
    change _ = phiG k g _
    rw [phiG_apply, standardSymplecticAlgHom_generator]
  · apply AlgEquiv.ext
    intro z
    rw [phiG_symm_apply, phiG_apply]

/-- `Φ_g` maps Bernstein pieces into themselves (proof of Proposition 3.2). -/
theorem phiG_mem_bernsteinPiece {n N : ℕ} (g : Matrix.symplecticGroup (Fin n) k)
    {z : PresentedWeyl k n} (hz : z ∈ Stafford38.WeylFiltration.bernsteinPiece k n N) :
    phiG k g z ∈ Stafford38.WeylFiltration.bernsteinPiece k n N := by
  rw [phiG_apply]
  exact Stafford38.WeylSymbolCompatibility.standardSymplecticAlgHom_preserves_bernsteinPiece
    k g.1 _ hz

/-- The Bernstein symbol of `Φ_g(z)` is `s ∘ M`: substitute `u_i ↦ ∑_j M_ij u_j`
in the symbol `s` of `z` (proof of Proposition 3.2). -/
theorem phiG_principal {n N : ℕ} (g : Matrix.symplecticGroup (Fin n) k)
    {z : PresentedWeyl k n} (hz : z ∈ Stafford38.WeylFiltration.bernsteinPiece k n N) :
    Stafford38.WeylLeadingSymbol.presentedPrincipalComponent k
        (@Stafford38.WeylFiltration.bernsteinWeight n) N (phiG k g z) =
      Stafford38.CharacteristicLinearAction.symbolLinearAlgHom k g.1
        (Stafford38.WeylLeadingSymbol.presentedPrincipalComponent k
          (@Stafford38.WeylFiltration.bernsteinWeight n) N z) := by
  rw [phiG_apply]
  exact Stafford38.WeylSymbolCompatibility.standardSymplecticAlgHom_principal_compatibility
    k g.1 _ hz

end

end Stafford38.Paper.Section3
