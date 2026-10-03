module
public import Stafford38.PaperCyclicity
public import Stafford38.TorsionCyclicity
public import Stafford38.Weyl.PaperQuotientDescent
public import Stafford38.FoundationClosure

@[expose] public section

/-! Independent paper-facing consumers for the matrix reduction and field
descent interfaces.  They spell out the quantifiers at the public boundary. -/

open Stafford38.TorsionCyclicity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylEulerResidue
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.EulerSurjectivity

noncomputable section

example {A M : Type*} [Ring A] [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (hdomain : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hidentity : ∀ d : A, d ≠ 0 → ∃ F R S : A, 1 = d * R + F * d * S)
    (htorsion : IsRightTorsion (A := A) (M := M)) (x y : M) :
    ∃ z : M, Submodule.span Aᵐᵒᵖ ({z} : Set M) =
      Submodule.span Aᵐᵒᵖ ({x, y} : Set M) :=
  Stafford38.PaperCyclicity.exists_span_singleton_eq_span_pair_via_matrix
    hdomain hidentity htorsion x y

example {A : Type*} [Ring A] (a F : A) :
    Submodule.span Aᵐᵒᵖ
      ({(a, 1 - F * a), (1, -F)} : Set (A × A)) = ⊤ :=
  Stafford38.PaperCyclicity.paper_matrix_pair_spans a F

example {k : Type*} [Field k] [CharZero k] (n : ℕ)
    (M : Type*) [AddCommGroup M]
    [Module (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    [Module.Finite (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    (hM : IsRightTorsion (A := Stafford38.WeylAlg k n) (M := M)) :
    ∃ z : M, Submodule.span (Stafford38.WeylAlg k n)ᵐᵒᵖ ({z} : Set M) = ⊤ :=
  Stafford38.PaperCyclicity.paper_torsion_module_is_cyclic k n M hM

example {k : Type*} [Field k] [CharZero k] (n : ℕ)
    (M : Type*) [AddCommGroup M]
    [Module (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    [Module.Finite (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    (hM : IsRightTorsion (A := Stafford38.WeylAlg k n) (M := M)) :
    ∃ z : M, Submodule.span (Stafford38.WeylAlg k n)ᵐᵒᵖ ({z} : Set M) = ⊤ :=
  Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion k n M hM

example {k K : Type*} [Field k] [Field K] [Algebra k K]
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    TensorProduct k (PresentedWeyl k (n + 1) ⧸ rightIdealKSubmodule k
      (canonicalRightIdeal (presentedCoordinate k n) d N)) K ≃ₗ[k]
    RightQuotient (canonicalRightIdeal (presentedCoordinate K n)
      (Stafford38.Weyl.PresentedScalarExtension.presentedWeylScalarExtension
        (k := k) (K := K) (n + 1) d) N) :=
  Stafford38.PaperQuotientDescent.canonicalRightQuotient_scalarExtension_equiv
    (k := k) (K := K) n N d

example {k K : Type*} [Field k] [Field K] [Algebra k K]
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hK : orderCharacteristicSupport K
      (canonicalRightIdeal (presentedCoordinate K n)
        (Stafford38.Weyl.PresentedScalarExtension.presentedWeylScalarExtension
          (k := k) (K := K) (n + 1) d) N) = ∅) :
    orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N) = ∅ :=
  Stafford38.PaperQuotientDescent.canonicalSupport_empty_of_scalarExtension_empty
    (k := k) (K := K) n N d hK

#print axioms Stafford38.PaperCyclicity.exists_span_singleton_eq_span_pair_via_matrix
#print axioms Stafford38.PaperCyclicity.paper_matrix_pair_spans
#print axioms Stafford38.PaperCyclicity.exists_common_right_annihilator_of_torsion
#print axioms Stafford38.PaperCyclicity.span_adjusted_pair_eq_span_pair_via_matrix
#print axioms Stafford38.PaperCyclicity.paper_torsion_module_is_cyclic
#print axioms Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion
#print axioms Stafford38.PaperQuotientDescent.canonicalRightQuotient_scalarExtension_equiv
#print axioms Stafford38.PaperQuotientDescent.canonicalRightQuotient_subsingleton_of_scalarExtension
#print axioms Stafford38.PaperQuotientDescent.canonicalSupport_empty_of_scalarExtension_empty
#print axioms Stafford38.PaperQuotientDescent.canonicalAssociatedGraded_annihilator_scalarExtension
#print axioms Stafford38.PaperQuotientDescent.canonicalSupportDescent_via_quotient
#print axioms Stafford38.FoundationClosure.canonicalSupportVanishingViaGeneralCoisotropic
#print axioms Stafford38.universalStatement

end
