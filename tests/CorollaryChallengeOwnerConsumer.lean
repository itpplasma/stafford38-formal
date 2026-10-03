module
public import CorollaryChallenge

@[expose] public section

namespace Stafford38CorollaryChallengeOwnerConsumer

universe u v

theorem phaseVar_alias (n : ℕ) :
    Stafford38CorollaryChallenge.PhaseVar n = Stafford38Challenge.PhaseVar n := rfl

theorem relation_alias {k : Type u} [Field k] {n : ℕ}
    (omega : Matrix (Stafford38Challenge.PhaseVar n)
      (Stafford38Challenge.PhaseVar n) k)
    (a b : FreeAlgebra k (Stafford38Challenge.PhaseVar n)) :
    Stafford38CorollaryChallenge.relation omega a b =
      Stafford38Challenge.relation omega a b := rfl

theorem algebra_alias (k : Type u) [Field k] (n : ℕ) :
    Stafford38CorollaryChallenge.WeylAlg k n = Stafford38Challenge.WeylAlg k n := rfl

theorem rightTorsion_alias {A : Type u} {M : Type v} [Ring A]
    [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    Stafford38CorollaryChallenge.IsRightTorsion (A := A) (M := M) =
      Stafford38.TorsionCyclicity.IsRightTorsion (A := A) (M := M) := rfl

theorem cyclicity_statement_uses_canonical_owners :
    Stafford38CorollaryChallenge.torsionCyclicStatement.{u, v} =
      (∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
        (M : Type v) [AddCommGroup M]
        [Module (Stafford38Challenge.WeylAlg k n)ᵐᵒᵖ M]
        [Module.Finite (Stafford38Challenge.WeylAlg k n)ᵐᵒᵖ M],
        Stafford38.TorsionCyclicity.IsRightTorsion
          (A := Stafford38Challenge.WeylAlg k n) (M := M) →
          ∃ z : M, Submodule.span (Stafford38Challenge.WeylAlg k n)ᵐᵒᵖ
            ({z} : Set M) = ⊤) := by
  unfold Stafford38CorollaryChallenge.torsionCyclicStatement
  rfl

#print axioms phaseVar_alias
#print axioms relation_alias
#print axioms algebra_alias
#print axioms rightTorsion_alias
#print axioms cyclicity_statement_uses_canonical_owners

end Stafford38CorollaryChallengeOwnerConsumer
