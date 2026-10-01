import Stafford38.TorsionCyclicity

namespace Stafford38CorollaryChallenge

abbrev PhaseVar (n : ℕ) := Fin n ⊕ Fin n

def relation {k : Type*} [Field k] {n : ℕ}
    (omega : Matrix (PhaseVar n) (PhaseVar n) k)
    (a b : FreeAlgebra k (PhaseVar n)) : Prop :=
  ∃ i j,
    a = FreeAlgebra.ι k i * FreeAlgebra.ι k j -
      FreeAlgebra.ι k j * FreeAlgebra.ι k i ∧
    b = algebraMap k (FreeAlgebra k (PhaseVar n)) (omega i j)

abbrev WeylAlg (k : Type*) [Field k] (n : ℕ) :=
  RingQuot (relation (k := k) (n := n) (Matrix.J (Fin n) k))

def TorsionCyclicStatement : Prop :=
  ∀ (k : Type*) [Field k] [CharZero k] (n : ℕ) (M : Type*) [AddCommGroup M]
    [Module (WeylAlg k n)ᵐᵒᵖ M] [Module.Finite (WeylAlg k n)ᵐᵒᵖ M],
    (∀ m : M, ∃ a : WeylAlg k n, a ≠ 0 ∧ MulOpposite.op a • m = 0) →
      ∃ g : M, Submodule.span (WeylAlg k n)ᵐᵒᵖ {g} = ⊤

theorem torsionCyclicStatement : TorsionCyclicStatement := by
  intro k _ _ n M _ hmod hfin hM
  -- `WeylAlg k n` is definitionally `Stafford38.WeylAlg k n` (same `RingQuot`
  -- presentation, as in `Solution.lean`); the module instances are passed explicitly.
  exact @Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion k _ _ n M _ hmod hfin hM

end Stafford38CorollaryChallenge
