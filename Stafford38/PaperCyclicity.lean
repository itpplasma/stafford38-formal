module
public import Stafford38.FoundationClosure
public import Stafford38.Weyl.Domain
public import Stafford38.TorsionModule
public import Stafford38.LinearAlgebra.PairReplacement

@[expose] public section

/-!
# Paper-facing torsion-module cyclicity lemmas

The generic right-module matrix and finite-generation arguments live in
`LinearAlgebra.PairReplacement`. This file preserves the paper-facing names
and specializes those results to the Weyl algebra and its Stafford identity.
-/

namespace Stafford38.PaperCyclicity

universe u v

variable {A : Type u} [Ring A]

/-- The paper's two displayed vectors generate the free rank-two right module. -/
theorem paper_matrix_pair_spans (a F : A) :
    Submodule.span Aᵐᵒᵖ
      ({(a, 1 - F * a), (1, -F)} : Set (A × A)) = ⊤ :=
  Stafford38.LinearAlgebra.PairReplacement.matrix_pair_spans a F

/-- Two individual torsion annihilators have a common nonzero right multiple. -/
theorem exists_common_right_annihilator_of_torsion
    {M : Type v} [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (htorsion : Stafford38.TorsionCyclicity.IsRightTorsion
      (A := A) (M := M)) (x y : M)
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0) :
    ∃ d : A, d ≠ 0 ∧
      (MulOpposite.op d : Aᵐᵒᵖ) • x = 0 ∧
      (MulOpposite.op d : Aᵐᵒᵖ) • y = 0 :=
  Stafford38.LinearAlgebra.PairReplacement.common_right_annihilator
    htorsion x y hmul

/-- The matrix calculation gives pair replacement for a specified common
annihilator and certificate. -/
theorem span_adjusted_pair_eq_span_pair_via_matrix
    {M : Type v} [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (x y : M) (d F R S : A)
    (hxann : (MulOpposite.op d : Aᵐᵒᵖ) • x = 0)
    (hyann : (MulOpposite.op d : Aᵐᵒᵖ) • y = 0)
    (hcert : (1 : A) = d * R + F * d * S) :
    Submodule.span Aᵐᵒᵖ
        ({x - (MulOpposite.op F : Aᵐᵒᵖ) • y} : Set M) =
      Submodule.span Aᵐᵒᵖ ({x, y} : Set M) :=
  Stafford38.LinearAlgebra.PairReplacement.span_adjusted_pair_eq_span_pair
    x y d F R S hxann hyann hcert

/-- Apply the paper's certificate and matrix calculation to two torsion
module elements. -/
theorem exists_span_adjusted_pair_via_matrix
    {M : Type v} [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : Stafford38.TorsionCyclicity.IsRightTorsion
      (A := A) (M := M)) (x y : M) :
    ∃ F : A, Submodule.span Aᵐᵒᵖ
      ({x - (MulOpposite.op F : Aᵐᵒᵖ) • y} : Set M) =
        Submodule.span Aᵐᵒᵖ ({x, y} : Set M) :=
  Stafford38.LinearAlgebra.PairReplacement.exists_adjusted_pair
    hmul hone htorsion x y

/-- Forget the explicit coefficient and retain its generated singleton. -/
theorem exists_span_singleton_eq_span_pair_via_matrix
    {M : Type v} [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : Stafford38.TorsionCyclicity.IsRightTorsion
      (A := A) (M := M)) (x y : M) :
    ∃ z : M, Submodule.span Aᵐᵒᵖ ({z} : Set M) =
      Submodule.span Aᵐᵒᵖ ({x, y} : Set M) :=
  Stafford38.LinearAlgebra.PairReplacement.exists_singleton_eq_span_pair
    hmul hone htorsion x y

/-- Exact cyclicity statement in the Weyl-algebra presentation. -/
theorem paper_torsion_module_is_cyclic
    (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (M : Type v) [AddCommGroup M]
    [Module (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    [Module.Finite (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    (hM : Stafford38.TorsionCyclicity.IsRightTorsion
      (A := Stafford38.WeylAlg k n) (M := M)) :
    ∃ z : M,
      Submodule.span (Stafford38.WeylAlg k n)ᵐᵒᵖ ({z} : Set M) = ⊤ :=
  Stafford38.LinearAlgebra.PairReplacement.finite_torsion_module_is_cyclic
    (A := Stafford38.WeylAlg k n) (M := M)
    (fun _ _ ha hb => Stafford38.WeylDomain.mul_ne_zero ha hb)
    (Stafford38.universalStatement (k := k) n) hM

#print axioms paper_matrix_pair_spans
#print axioms exists_common_right_annihilator_of_torsion
#print axioms span_adjusted_pair_eq_span_pair_via_matrix
#print axioms exists_span_adjusted_pair_via_matrix
#print axioms exists_span_singleton_eq_span_pair_via_matrix
#print axioms paper_torsion_module_is_cyclic

end Stafford38.PaperCyclicity
