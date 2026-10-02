import proofs.stafford38_reduction
import proofs.weyl_symplectic
import Stafford38.ChallengeDefinitions

/-!
# The universal Stafford 3.8 target

This file gives proof-side aliases of the Mathlib-only challenge definitions
in `Stafford38.ChallengeDefinitions`. The end-to-end theorem proves this
shared statement; its certificate retains the written multiplication order.
-/

namespace Stafford38

/-- The presented `n`th Weyl algebra with its standard symplectic form. -/
abbrev WeylAlg (k : Type*) [Field k] (n : ℕ) :=
  Stafford38Challenge.WeylAlg k n

/-- Exact proposition required for the publication theorem. -/
abbrev UniversalStatement.{u} : Prop := Stafford38Challenge.UniversalStatement.{u}

/-- The paper-facing name is definitionally the literal challenge predicate. -/
theorem challenge_universalStatement_iff.{u} :
    Stafford38Challenge.UniversalStatement.{u} ↔ UniversalStatement.{u} := Iff.rfl

end Stafford38
