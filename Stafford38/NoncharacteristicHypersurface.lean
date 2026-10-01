import Stafford38.NoncharacteristicHyperplane
import Stafford38.Characteristic.CanonicalTangentialRingEquivalence

/-!
# Finiteness of the principal-symbol hypersurface on the hyperplane

The normal principal symbol is monic in the normal covariable.  After the
normal base coordinate is set to zero, its hypersurface coordinate ring is
finite over the tangential cotangent-coordinate ring.
-/

namespace Stafford38.NoncharacteristicHypersurface

open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalNormalSymbolFiniteness
open Stafford38.Characteristic.CanonicalTangentialSymbolFiniteness
open Stafford38.Characteristic.CanonicalTangentialRingEquivalence
open Stafford38.Characteristic.NormalSymbolPolynomial
open Stafford38.Characteristic.CanonicalOldTangentialFiniteness
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicInitialIdeal
open Stafford38.NoncharacteristicHyperplane
open Stafford38.WeylEulerResidue
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBWMonicBridge

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
variable {k : Type*} [Field k]

def canonicalPrincipalHypersurfaceIdeal (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) : Ideal (SymbolRing k (n + 1)) :=
  Ideal.span ({presentedPrincipalComponent k (@orderWeight (n + 1)) N d} :
    Set (SymbolRing k (n + 1))) ⊔
  Ideal.span ({(MvPolynomial.X (.inl (0 : Fin (n + 1))) : SymbolRing k (n + 1))} :
    Set (SymbolRing k (n + 1)))

def normalCoefficientRingEquiv (n : ℕ) :
    normalCoeffRing (k := k) n ≃+*
      Polynomial (oldTangentialCoeffRing (k := k) n) :=
  (normalCoeffTangentialAlgEquiv (k := k) n).toRingEquiv.trans
    (Polynomial.mapEquiv
      (oldSymbolTangentialAlgEquiv (k := k) n).symm.toRingEquiv)

def normalMomentumPolynomialEquiv (n : ℕ) :
    SymbolRing k (n + 1) ≃+*
      Polynomial (Polynomial (oldTangentialCoeffRing (k := k) n)) :=
  (normalSymbolAlgEquiv (k := k) n).toRingEquiv.trans
    (Polynomial.mapEquiv (normalCoefficientRingEquiv (k := k) n))

set_option maxHeartbeats 800000 in
theorem normalMomentumPolynomialEquiv_normalCoordinate (n : ℕ) :
    normalMomentumPolynomialEquiv (k := k) n
      (MvPolynomial.X (.inl (0 : Fin (n + 1))) : SymbolRing k (n + 1)) =
      Polynomial.C (Polynomial.X : Polynomial (oldTangentialCoeffRing (k := k) n)) := by
  have hsym : (normalCoeffTangentialAlgEquiv (k := k) n).symm Polynomial.X =
      MvPolynomial.X
        (⟨Sum.inl (0 : Fin (n + 1)), by simp⟩ : NormalVar n) := by
    apply (normalCoeffTangentialAlgEquiv (k := k) n).injective
    rw [(normalCoeffTangentialAlgEquiv (k := k) n).apply_symm_apply]
    simp [normalCoeffTangentialAlgEquiv, tangentialVariableEquiv]
  have hev : (normalCoeffTangentialAlgEquiv (k := k) n)
      (MvPolynomial.X
        (⟨Sum.inl (0 : Fin (n + 1)), by simp⟩ : NormalVar n)) =
      Polynomial.X := by
    rw [← hsym, (normalCoeffTangentialAlgEquiv (k := k) n).apply_symm_apply]
  simp [normalMomentumPolynomialEquiv, normalCoefficientRingEquiv,
    normalSymbolAlgEquiv_otherVariable, normalCoeffTangentialAlgEquiv,
    tangentialVariableEquiv, oldSymbolTangentialAlgEquiv]

/-- The iterated normal-coordinate splitting restricts on the old phase
variables to the canonical tangential-coordinate inclusion. -/
theorem normalMomentumPolynomialEquiv_tangentialMap (n : ℕ) :
    (normalMomentumPolynomialEquiv (k := k) n).toRingHom.comp
        (tangentialSymbolMap (k := k) n) =
      (Polynomial.C : Polynomial (oldTangentialCoeffRing (k := k) n) →+*
        Polynomial (Polynomial (oldTangentialCoeffRing (k := k) n))).comp
        (Polynomial.C : oldTangentialCoeffRing (k := k) n →+*
          Polynomial (oldTangentialCoeffRing (k := k) n)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change (normalMomentumPolynomialEquiv (k := k) n)
        (tangentialSymbolMap (k := k) n (MvPolynomial.C c)) =
      Polynomial.C (Polynomial.C (MvPolynomial.C c))
    simp [tangentialSymbolMap, tangentialPolynomialActionHom,
      normalMomentumPolynomialEquiv, normalCoefficientRingEquiv,
      normalSymbolAlgEquiv, normalCoeffTangentialAlgEquiv,
      tangentialVariableEquiv, oldSymbolTangentialAlgEquiv,
      normalPolynomialActionHom]
  · intro i
    change (normalMomentumPolynomialEquiv (k := k) n)
        (((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C)
          (oldSymbolTangentialAlgEquiv (k := k) n (MvPolynomial.X i))) =
      Polynomial.C (Polynomial.C (MvPolynomial.X i))
    rw [tangentialCoeffActionHom_oldSymbol_X]
    have hnon : oldIndex i ≠ Sum.inr (0 : Fin (n + 1)) := by
      cases i with
      | inl j => simp [oldIndex]
      | inr j => simp [oldIndex]
    have hnot : oldIndex i ≠ Sum.inl (0 : Fin (n + 1)) := by
      cases i with
      | inl j => simp [oldIndex]
      | inr j => simp [oldIndex]
    have hnot' : (⟨oldIndex i, hnon⟩ : NormalVar n) ≠
        ⟨Sum.inl (0 : Fin (n + 1)), by simp⟩ := by
      intro h
      apply hnot
      exact congrArg Subtype.val h
    have hvar : oldTangentialVarEquiv n i =
        ⟨⟨oldIndex i, hnon⟩, hnot'⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    change Polynomial.map (normalCoefficientRingEquiv (k := k) n).toRingHom
        (normalSymbolAlgEquiv (k := k) n
          (MvPolynomial.X (oldIndex i))) = _
    rw [normalSymbolAlgEquiv_otherVariable (k := k) n (oldIndex i) hnon]
    simp [normalCoefficientRingEquiv, normalCoeffTangentialAlgEquiv,
      tangentialVariableEquiv, oldSymbolTangentialAlgEquiv,
      oldTangentialVarEquiv_apply, hnot, hvar]
    rw [← hvar]
    exact (oldTangentialVarEquiv n).symm_apply_apply i

/-- The literal ring `R/(P,x₀)` for the canonical principal symbol is finite
 over the coordinate ring of `T^*H`. -/
theorem canonical_principal_hypersurface_finite
    {n N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Module.Finite (oldTangentialCoeffRing (k := k) n)
      (SymbolRing k (n + 1) ⧸
        canonicalPrincipalHypersurfaceIdeal (k := k) n N d) := by
  let T := oldTangentialCoeffRing (k := k) n
  let U := Polynomial T
  let A := Polynomial U
  let R := SymbolRing k (n + 1)
  let P := presentedPrincipalComponent k (@orderWeight (n + 1)) N d
  let K := canonicalPrincipalHypersurfaceIdeal (k := k) n N d
  let E := R ⧸ K
  let e := normalMomentumPolynomialEquiv (k := k) n
  let fA : A →+* E := (Ideal.Quotient.mk K).comp e.symm
  let g : A := Polynomial.map
    (normalCoefficientRingEquiv (k := k) n).toRingHom
    (canonicalNormalPolynomial (k := k) (n := n) (N := N) d)
  have hg : g.Monic := by
    exact Polynomial.Monic.map _
      (canonicalNormalPolynomial_monic (k := k) (n := n) (N := N)
        (d := d) hd)
  have heP : e P = g := by
    change Polynomial.map (normalCoefficientRingEquiv (k := k) n).toRingHom
      (normalSymbolAlgEquiv (k := k) n P) = _
    rfl
  have hxK : (MvPolynomial.X (.inl (0 : Fin (n + 1))) : R) ∈ K := by
    exact Ideal.mem_sup_right (Ideal.subset_span (by simp [K]))
  have hPK : P ∈ K := by
    exact Ideal.mem_sup_left (Ideal.subset_span (by simp [K, P]))
  letI : Module A E := Module.compHom E fA
  let fU : U →+* E := fA.comp Polynomial.C
  letI : Module U E := Module.compHom E fU
  have hdouble (t : T) :
      e.symm (Polynomial.C (Polynomial.C t)) =
        tangentialSymbolMap (k := k) n t := by
    have h := congrArg (fun f : T →+* A => f t)
      (normalMomentumPolynomialEquiv_tangentialMap (k := k) n)
    change e (tangentialSymbolMap (k := k) n t) =
      Polynomial.C (Polynomial.C t) at h
    rw [← h, e.symm_apply_apply]
  have hT : fU.comp Polynomial.C =
      (Ideal.Quotient.mk K).comp (tangentialSymbolMap (k := k) n) := by
    apply RingHom.ext
    intro t
    change Ideal.Quotient.mk K (e.symm (Polynomial.C (Polynomial.C t))) = _
    rw [hdouble t]
    simp only [RingHom.comp_apply]
  have hT_apply (t : T) : fU (Polynomial.C t) =
      Ideal.Quotient.mk K (tangentialSymbolMap (k := k) n t) := by
    have h := congrArg (fun f : T →+* E => f t) hT
    exact h
  letI : Module T E :=
    restrictedSymbolRing_tangentialModule (k := k) n K
  letI : IsScalarTower U A E := ⟨by
    intro u a z
    rw [Polynomial.smul_eq_C_mul]
    change fA (Polynomial.C u * a) * z =
      fU u * (fA a * z)
    rw [map_mul]
    exact mul_assoc _ _ _⟩
  letI : IsScalarTower T U E := ⟨by
    intro t u z
    rw [Polynomial.smul_eq_C_mul]
    change fU (Polynomial.C t * u) * z =
      (Ideal.Quotient.mk K (tangentialSymbolMap (k := k) n t)) *
        (fU u * z)
    rw [map_mul]
    rw [hT_apply t]
    exact mul_assoc _ _ _⟩
  have hfiniteA : Module.Finite A E := by
    let cyclic : A →ₗ[A] E := LinearMap.toSpanSingleton A E (1 : E)
    have hsurj : Function.Surjective cyclic := by
      intro z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := K) z
      refine ⟨e r, ?_⟩
      change Ideal.Quotient.mk K (e.symm (e r) * 1) = Ideal.Quotient.mk K r
      rw [e.symm_apply_apply, mul_one]
    exact Module.Finite.of_surjective cyclic hsurj
  have hkill : ∀ z : E, g • z = 0 := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | _ r =>
        change Ideal.Quotient.mk K (e.symm g * r) = 0
        rw [← heP, e.symm_apply_apply]
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact Ideal.mul_mem_right r K hPK
  have hfiniteU : Module.Finite U E :=
    AlgebraicAnalysis.MonicAnnihilatorFinite.finite_of_monic_annihilator
      g hg hkill
  have hXkill : ∀ z : E, (Polynomial.X : U) • z = 0 := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | _ r =>
        change Ideal.Quotient.mk K
          (e.symm (Polynomial.C (Polynomial.X : U)) * r) = 0
        rw [← normalMomentumPolynomialEquiv_normalCoordinate (k := k) n,
          e.symm_apply_apply]
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact Ideal.mul_mem_right r K hxK
  exact AlgebraicAnalysis.MonicAnnihilatorFinite.finite_of_variable_annihilates
    hXkill

#print axioms normalCoefficientRingEquiv
#print axioms normalMomentumPolynomialEquiv_normalCoordinate
#print axioms canonical_principal_hypersurface_finite

end
end Stafford38.NoncharacteristicHypersurface
