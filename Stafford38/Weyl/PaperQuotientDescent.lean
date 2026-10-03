module
public import Stafford38.Weyl.FilteredScalarLifting
public import Stafford38.Characteristic.EmptySupportVanishing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

@[expose] public section

/-!
# Paper-facing scalar extension and quotient descent

This file records the algebraic descent steps in the paper's proof.  The
coefficient extension is an arbitrary field extension (so an algebraic
closure is available as the paper's closed coefficient field).  It keeps the
actual filtered quotient, its associated graded annihilator, and the
unfiltered right quotient distinct.
-/

namespace Stafford38.PaperQuotientDescent

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicEmptySupportVanishing
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Weyl.PresentedScalarExtension
open Stafford38.Weyl.FilteredScalarLifting
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylUniversal

noncomputable section

set_option maxRecDepth 5000

universe u v

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

section TensorQuotient

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- Moving the field-extension factor to the left identifies the image of a
subspace quotient kernel with ordinary linear base change. -/
theorem comm_map_tensorSubmodule_range (J : Submodule k M) :
    Submodule.map (TensorProduct.comm k M K).toLinearMap
      (LinearMap.range (TensorProduct.map J.subtype
        (LinearMap.id : K →ₗ[k] K))) = (J.baseChange K).restrictScalars k := by
  have hcomp :
      (TensorProduct.comm k M K).toLinearMap.comp
          (TensorProduct.map J.subtype (LinearMap.id : K →ₗ[k] K)) =
        ((J.subtype.baseChange K).restrictScalars k).comp
          (TensorProduct.comm k J K).toLinearMap := by
    ext j c
    simp [LinearMap.comp_apply]
  rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp]
  rw [LinearEquiv.range, Submodule.map_top]
  change LinearMap.range ((J.subtype.baseChange K).restrictScalars k) =
    Submodule.restrictScalars k (J.subtype.baseChange K).range
  rw [LinearMap.range_restrictScalars]

end TensorQuotient

/-- Scalar extension of the actual canonical quotient is the quotient by the
scalar-extended canonical right ideal.  The proof goes through the tensor
quotient equivalence and the already-checked PBW identification. -/
def canonicalRightQuotient_scalarExtension_equiv
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    TensorProduct k (PresentedWeyl k (n + 1) ⧸
      rightIdealKSubmodule k
        (canonicalRightIdeal (presentedCoordinate k n) d N)) K ≃ₗ[k]
      RightQuotient
        (canonicalRightIdeal (presentedCoordinate K n)
          (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N) := by
  let I := canonicalRightIdeal (presentedCoordinate k n) d N
  let J := rightIdealKSubmodule k I
  let eK := pbwTensorEquiv (k := k) (K := K) (n + 1)
  let IK := canonicalRightIdeal (presentedCoordinate K n)
    (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N
  let JK := rightIdealKSubmodule K IK
  let f := (TensorProduct.comm k (PresentedWeyl k (n + 1)) K).trans
    (LinearEquiv.restrictScalars k eK)
  have hf : f.toLinearMap =
      (LinearEquiv.restrictScalars k eK).toLinearMap.comp
        (TensorProduct.comm k (PresentedWeyl k (n + 1)) K).toLinearMap := by
    ext z
    rfl
  let D := LinearMap.range (TensorProduct.map J.subtype
    (LinearMap.id : K →ₗ[k] K))
  have hden : Submodule.map f.toLinearMap D = JK.restrictScalars k := by
    rw [hf, Submodule.map_comp]
    rw [comm_map_tensorSubmodule_range]
    calc
      Submodule.map (LinearEquiv.restrictScalars k eK).toLinearMap
        (Submodule.restrictScalars k (J.baseChange K)) =
        Submodule.restrictScalars k
          (Submodule.map eK.toLinearMap (J.baseChange K)) := by
          symm
          exact Submodule.restrictScalars_map eK.toLinearMap (J.baseChange K)
      _ = Submodule.restrictScalars k JK := by
        rw [pbwTensorEquiv_map_canonicalRightIdeal]
  have hquot :
      TensorProduct k (PresentedWeyl k (n + 1) ⧸ J) K ≃ₗ[k]
        (PresentedWeyl K (n + 1) ⧸ JK.restrictScalars k) :=
    (TensorProduct.quotientTensorEquiv K J).trans
      (Submodule.Quotient.equiv D (JK.restrictScalars k) f hden)
  exact hquot.trans
    ((Submodule.Quotient.restrictScalarsEquiv k JK).trans
      (LinearEquiv.restrictScalars k
        (filteredRightQuotientEquivRightQuotient K IK)))

/-- Faithfully flat field extension descends vanishing of the actual right
quotient.  The scalar-extension equivalence above is the concrete bridge; the
last step is the standard faithful-flat reflection of a zero module. -/
theorem canonicalRightQuotient_subsingleton_of_scalarExtension
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hK : Subsingleton (RightQuotient
      (canonicalRightIdeal (presentedCoordinate K n)
        (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N))) :
    Subsingleton (RightQuotient
      (canonicalRightIdeal (presentedCoordinate k n) d N)) := by
  let I := canonicalRightIdeal (presentedCoordinate k n) d N
  let e0 := filteredRightQuotientEquivRightQuotient k I
  let e := (TensorProduct.congr e0 (LinearEquiv.refl k K)).trans
    (canonicalRightQuotient_scalarExtension_equiv (k := k) (K := K) n N d)
  have htensor : Subsingleton (TensorProduct k (RightQuotient I) K) :=
    (Equiv.subsingleton_congr e.toEquiv).mpr hK
  exact Module.FaithfullyFlat.rTensor_reflects_triviality k K (RightQuotient I)

/-- The paper's support descent, stated for the canonical quotient: empty
support after a field extension implies empty support before extension.  It
factors through vanishing of the actual quotient on both fields. -/
theorem canonicalSupport_empty_of_scalarExtension_empty
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hK : orderCharacteristicSupport K
      (canonicalRightIdeal (presentedCoordinate K n)
        (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N) = ∅) :
    orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N) = ∅ := by
  apply (orderCharacteristicSupport_eq_empty_iff_rightQuotient_subsingleton k
    (canonicalRightIdeal (presentedCoordinate k n) d N)).mpr
  apply canonicalRightQuotient_subsingleton_of_scalarExtension
    (k := k) (K := K) n N d
  exact rightQuotient_subsingleton_of_orderCharacteristicSupport_eq_empty K _ hK

/-- The canonical-support descent contract used by the official assembly,
proved through vanishing of the concrete canonical right quotient. -/
theorem canonicalSupportDescent_via_quotient :
    Stafford38.CanonicalSupportVanishingReduction.CanonicalSupportDescent.{u} := by
  intro hclosed
  intro k _ _ n N d hN hd
  let e := presentedWeylScalarExtension (k := k)
    (K := AlgebraicClosure k) (n + 1)
  have hdK : IsPBWMonicAt (AlgebraicClosure k)
      (.inr (0 : Fin (n + 1))) N (e d) := by
    exact presentedWeylScalarExtension_isPBWMonicAt
      (k := k) (K := AlgebraicClosure k) n N hd
  have hK : orderCharacteristicSupport (AlgebraicClosure k)
      (canonicalRightIdeal (presentedCoordinate (AlgebraicClosure k) n)
        (e d) N) = ∅ := hclosed (AlgebraicClosure k) n N (e d) hN hdK
  exact canonicalSupport_empty_of_scalarExtension_empty
    (k := k) (K := AlgebraicClosure k) n N d hK

#print axioms canonicalRightQuotient_scalarExtension_equiv
#print axioms canonicalRightQuotient_subsingleton_of_scalarExtension
#print axioms canonicalSupport_empty_of_scalarExtension_empty
#print axioms canonicalSupportDescent_via_quotient

/-- The annihilator of the actual order-associated-graded quotient is
compatible with the coefficient-field map for the canonical right ideal.
This is the paper's `gr`/annihilator comparison, with the filtered lifting
equality supplied by `FilteredScalarLifting`. -/
theorem canonicalAssociatedGraded_annihilator_scalarExtension
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    (Module.annihilator (SymbolRing k (n + 1))
      (OrderAssociatedGradedModule k
        (canonicalRightIdeal (presentedCoordinate k n) d N))).map
        (symbolScalarExtension (k := k) (K := K) (n + 1)).toRingHom =
      Module.annihilator (SymbolRing K (n + 1))
        (OrderAssociatedGradedModule K
          (canonicalRightIdeal (presentedCoordinate K n)
            (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N)) := by
  rw [annihilator_orderAssociatedGradedModule,
    annihilator_orderAssociatedGradedModule,
    presentedWeylScalarExtension_map_orderInitialIdeal_eq]

#print axioms canonicalAssociatedGraded_annihilator_scalarExtension

end

end Stafford38.PaperQuotientDescent
