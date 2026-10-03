module
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.Opposite

@[expose] public section

/-! Supplementary statement of the paper generator step. This is not the
main Stafford Challenge, introduces no proof hole, and imports only Mathlib. -/
namespace Stafford38PaperPairChallenge
universe u v

def pairGeneratorStatement : Prop :=
  ∀ (A : Type u) [Ring A] (M : Type v) [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (x y : M) (d F R S : A),
    (MulOpposite.op d : Aᵐᵒᵖ) • x = 0 →
    (MulOpposite.op d : Aᵐᵒᵖ) • y = 0 →
    (1 : A) = d * R + F * d * S →
    Submodule.span Aᵐᵒᵖ ({x - (MulOpposite.op F : Aᵐᵒᵖ) • y} : Set M) =
      Submodule.span Aᵐᵒᵖ ({x, y} : Set M)

end Stafford38PaperPairChallenge
