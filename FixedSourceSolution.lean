module
public import Stafford38.ChallengeDefinitions
public import Stafford38.Paper.Main

@[expose] public section

/-!
# Solution for the exact-source challenge: the proof along the paper

The statement is the "moreover" part of Theorem 1.1, proved by
`Stafford38.Paper.theorem_1_1_fixedSource` along Sections 3–6 of the paper.
-/

namespace Stafford38FixedSourceChallenge

theorem universalFixedSourceStatement : UniversalFixedSourceStatement :=
  Stafford38.Paper.theorem_1_1_fixedSource

end Stafford38FixedSourceChallenge

#print axioms Stafford38FixedSourceChallenge.universalFixedSourceStatement
