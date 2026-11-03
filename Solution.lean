module
public import Stafford38.ChallengeDefinitions
public import Stafford38.ChallengeBridge
public import Stafford38.Paper.Main

@[expose] public section

/-!
# Solution: the proof along the paper

The three compared theorems are proved by the paper-route declarations
`Stafford38.Paper.theorem_1_1`, `Stafford38.Paper.theorem_1_1_fixedSource` and
`Stafford38.Paper.corollary_6_3` (Sections 3–6, `Stafford38/Paper/Main.lean`).
`Stafford38.ChallengeBridge` turns the identity and fixed-source forms into the
printed statement of Theorem 1.1 (`A_n = dA_n + FdA_n`, `F = Φ_g^{-1}(x₁)^{deg_B d}`).
-/

namespace Stafford38Challenge

theorem universalStatement : UniversalStatement :=
  Stafford38.Paper.theorem_1_1

theorem theorem_1_1 : PaperTheorem_1_1 :=
  paperTheorem_1_1_of Stafford38.Paper.theorem_1_1 Stafford38.Paper.theorem_1_1_fixedSource

theorem corollary_6_3 : PaperCorollary_6_3 := by
  intro k _ _ n M _ _ _ hM
  exact Stafford38.Paper.corollary_6_3 k n M hM

end Stafford38Challenge

#print axioms Stafford38Challenge.universalStatement
#print axioms Stafford38Challenge.theorem_1_1
#print axioms Stafford38Challenge.corollary_6_3
