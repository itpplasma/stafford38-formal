module
public import Stafford38.LinearAlgebra.PairReplacement

@[expose] public section

/-! Independent exact-type consumers for the Mathlib-only pair argument. -/

namespace Stafford38PairReplacementConsumer

open Stafford38.LinearAlgebra.PairReplacement

example {A : Type*} [Ring A] (a F : A) :
    Submodule.span Aᵐᵒᵖ
      ({(a, 1 - F * a), (1, -F)} : Set (A × A)) = ⊤ :=
  matrix_pair_spans a F

example {A M : Type*} [Ring A] [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : ∀ m : M, ∃ d : A, d ≠ 0 ∧
      (MulOpposite.op d : Aᵐᵒᵖ) • m = 0) [Module.Finite Aᵐᵒᵖ M] :
    ∃ z : M, Submodule.span Aᵐᵒᵖ ({z} : Set M) = ⊤ :=
  finite_torsion_module_is_cyclic hmul hone htorsion

#print axioms Stafford38.LinearAlgebra.PairReplacement.matrix_pair_spans
#print axioms Stafford38.LinearAlgebra.PairReplacement.span_adjusted_pair_eq_span_pair
#print axioms Stafford38.LinearAlgebra.PairReplacement.finite_torsion_module_is_cyclic

end Stafford38PairReplacementConsumer
