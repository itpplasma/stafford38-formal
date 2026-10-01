import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Cyclicity of torsion modules over Weyl algebras

J. T. Stafford, *Module structure of Weyl algebras*, J. London Math. Soc. (2)
18 (1978), 429–442, observes on pages 437–438 that Conjecture 3.8 implies that
finitely generated torsion modules over `Aₙ(k)` are cyclic. This file states
that consequence for right modules, using only Mathlib and the same
presentation of the Weyl algebra as `Challenge.lean`.

A right `Aₙ(k)`-module is a module over the opposite ring `Aₙ(k)ᵐᵒᵖ`; the right
action `m a` is `MulOpposite.op a • m`. The module is torsion when every
element has a nonzero right annihilator, and cyclic when one element spans it.
The compared theorem is `torsionCyclicStatement`; its `sorry` is the deliberate
hole filled by `CorollarySolution.lean`.
-/

namespace Stafford38CorollaryChallenge

/-- Index type of the `2n` generators: `Sum.inl i` is `xᵢ`, `Sum.inr i` is `∂ᵢ`. -/
abbrev PhaseVar (n : ℕ) := Fin n ⊕ Fin n

/-- The Weyl commutator relations, exactly as in `Challenge.lean`. -/
def relation {k : Type*} [Field k] {n : ℕ}
    (omega : Matrix (PhaseVar n) (PhaseVar n) k)
    (a b : FreeAlgebra k (PhaseVar n)) : Prop :=
  ∃ i j,
    a = FreeAlgebra.ι k i * FreeAlgebra.ι k j -
      FreeAlgebra.ι k j * FreeAlgebra.ι k i ∧
    b = algebraMap k (FreeAlgebra k (PhaseVar n)) (omega i j)

/-- The `n`th Weyl algebra `Aₙ(k)`. -/
abbrev WeylAlg (k : Type*) [Field k] (n : ℕ) :=
  RingQuot (relation (k := k) (n := n) (Matrix.J (Fin n) k))

/-- Every finitely generated torsion right `Aₙ(k)`-module is cyclic, for every
field `k` of characteristic zero and every `n`. -/
def TorsionCyclicStatement : Prop :=
  ∀ (k : Type*) [Field k] [CharZero k] (n : ℕ) (M : Type*) [AddCommGroup M]
    [Module (WeylAlg k n)ᵐᵒᵖ M] [Module.Finite (WeylAlg k n)ᵐᵒᵖ M],
    (∀ m : M, ∃ a : WeylAlg k n, a ≠ 0 ∧ MulOpposite.op a • m = 0) →
      ∃ g : M, Submodule.span (WeylAlg k n)ᵐᵒᵖ {g} = ⊤

/-- The compared theorem. The proof is supplied by `CorollarySolution.lean`. -/
theorem torsionCyclicStatement : TorsionCyclicStatement := by
  sorry

end Stafford38CorollaryChallenge
