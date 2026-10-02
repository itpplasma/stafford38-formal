import Stafford38.FoundationClosure
import Stafford38.Weyl.Domain
import Stafford38.TorsionModule
import Stafford38.PaperCyclicity
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Cyclicity of finitely generated torsion right Weyl modules

The paper-facing matrix argument and its finite-generation induction are
implemented in `PaperCyclicity`; this module retains the established public
names as derived interfaces.
-/

namespace Stafford38.TorsionCyclicity

universe u v

variable {A : Type u} {M : Type v} [Ring A]
  [AddCommGroup M] [Module Aᵐᵒᵖ M]

/-- The paper's generator calculation for a specified common annihilator and
certificate, derived from the canonical matrix proof. -/
theorem span_adjusted_pair_eq_span_pair
    (x y : M) (d F R S : A)
    (hxann : (MulOpposite.op d : Aᵐᵒᵖ) • x = 0)
    (hyann : (MulOpposite.op d : Aᵐᵒᵖ) • y = 0)
    (hcert : (1 : A) = d * R + F * d * S) :
    Submodule.span Aᵐᵒᵖ
        ({x - (MulOpposite.op F : Aᵐᵒᵖ) • y} : Set M) =
      Submodule.span Aᵐᵒᵖ ({x, y} : Set M) :=
  Stafford38.PaperCyclicity.span_adjusted_pair_eq_span_pair_via_matrix
    x y d F R S hxann hyann hcert

/-- The paper generator collapses any torsion pair to one adjusted generator. -/
theorem exists_span_adjusted_pair
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : IsRightTorsion (A := A) (M := M)) (x y : M) :
    ∃ F : A,
      Submodule.span Aᵐᵒᵖ
        ({x - (MulOpposite.op F : Aᵐᵒᵖ) • y} : Set M) =
        Submodule.span Aᵐᵒᵖ ({x, y} : Set M) :=
  Stafford38.PaperCyclicity.exists_span_adjusted_pair_via_matrix
    hmul hone htorsion x y

/-- Forget the displayed coefficient and keep the generated singleton. -/
theorem exists_span_singleton_eq_span_pair
    (hmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (hone : ∀ d : A, d ≠ 0 →
      ∃ F R S : A, (1 : A) = d * R + F * d * S)
    (htorsion : IsRightTorsion (A := A) (M := M)) (x y : M) :
    ∃ z : M,
      Submodule.span Aᵐᵒᵖ ({z} : Set M) =
        Submodule.span Aᵐᵒᵖ ({x, y} : Set M) :=
  Stafford38.PaperCyclicity.exists_span_singleton_eq_span_pair_via_matrix
    hmul hone htorsion x y

/-- Every finitely generated torsion right module over a Weyl algebra is
cyclic. The main theorem supplies the coefficient identity used at each
pair-replacement step in the finite-generator induction. -/
theorem weyl_isCyclic_of_isRightTorsion
    (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (M : Type v) [AddCommGroup M]
    [Module (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    [Module.Finite (Stafford38.WeylAlg k n)ᵐᵒᵖ M]
    (hM : IsRightTorsion (A := Stafford38.WeylAlg k n) (M := M)) :
    ∃ z : M,
      Submodule.span (Stafford38.WeylAlg k n)ᵐᵒᵖ ({z} : Set M) = ⊤ :=
  Stafford38.PaperCyclicity.paper_torsion_module_is_cyclic
    (k := k) (n := n) (M := M) hM

#print axioms span_adjusted_pair_eq_span_pair
#print axioms exists_span_adjusted_pair
#print axioms exists_span_singleton_eq_span_pair
#print axioms weyl_isCyclic_of_isRightTorsion

end Stafford38.TorsionCyclicity
