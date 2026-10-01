import Stafford38.TorsionCyclicity
import Stafford38.Weyl.FilteredScalarLifting

/- Independent paper-facing consumers spell out the expected conclusions. -/
set_option autoImplicit false

open MulOpposite

example {A M : Type*} [Ring A] [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (hdomain : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hidentity : ∀ d : A, d ≠ 0 → ∃ F R S : A, 1 = d * R + F * d * S)
    (htorsion : Stafford38.TorsionCyclicity.IsRightTorsion (A := A) (M := M))
    (x y : M) :
    ∃ F : A, Submodule.span Aᵐᵒᵖ ({x - op F • y} : Set M) =
      Submodule.span Aᵐᵒᵖ ({x, y} : Set M) :=
  Stafford38.TorsionCyclicity.exists_span_adjusted_pair hdomain hidentity htorsion x y

open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylUniversal Stafford38.Weyl.PresentedScalarExtension
open Stafford38.CharacteristicInitialIdeal Stafford38.WeylEulerResidue

example {k K : Type*} [Field k] [Field K] [Algebra k K]
    (n N : Nat) (d : PresentedWeyl k (n + 1)) :
    (orderInitialIdeal k
      (canonicalRightIdeal (presentedCoordinate k n) d N)).map
      (symbolScalarExtension (k := k) (K := K) (n + 1)).toRingHom =
    orderInitialIdeal K
      (canonicalRightIdeal (presentedCoordinate K n)
        (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N) :=
  Stafford38.Weyl.FilteredScalarLifting.presentedWeylScalarExtension_map_orderInitialIdeal_eq n N d

#print axioms Stafford38.TorsionCyclicity.exists_span_adjusted_pair
#print axioms Stafford38.Weyl.FilteredScalarLifting.presentedWeylScalarExtension_map_orderInitialIdeal_eq
