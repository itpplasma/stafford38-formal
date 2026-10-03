module
public import Stafford38.ChallengeDefinitions
public import Stafford38.FoundationClosure
public import Stafford38.FixedSourceChallengeTransport

@[expose] public section

/-!
# Generic/Laurent solution variant for the fixed-source challenge

This module proves the unchanged fixed-source statement through the
historical generic-prime/Laurent route retained in
`Stafford38.GenericLaurentVariant`.
-/

namespace Stafford38FixedSourceChallenge

universe u

theorem universalFixedSourceStatement : UniversalFixedSourceStatement := by
  intro k _ _ n d hd
  obtain ⟨ell, R, S, hell, hcert⟩ :=
    Stafford38.GenericLaurentVariant.universalFixedSourceStatement (k := k) n d hd
  have hdeg := Stafford38FixedSourceChallengeTransport.bernsteinDegree_eq k d
  refine ⟨ell, R, S,
    (Stafford38FixedSourceChallengeTransport.isLinearWeylCoordinate_iff
      k n ell).mpr hell, ?_⟩
  rw [hdeg]
  exact hcert

end Stafford38FixedSourceChallenge

#print axioms Stafford38FixedSourceChallenge.universalFixedSourceStatement
