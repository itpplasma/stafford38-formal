module
public import Stafford38.ChallengeDefinitions
public import Stafford38.FoundationClosure

@[expose] public section

/-!
# Generic/Laurent solution variant

This module proves the unchanged Stafford challenge statement through the
historical generic-prime/Laurent route retained in
`Stafford38.GenericLaurentVariant`.
-/

namespace Stafford38Challenge

theorem universalStatement : UniversalStatement := by
  intro k _ _ n d hd
  exact Stafford38.GenericLaurentVariant.universalStatement (k := k) n d hd

end Stafford38Challenge

#print axioms Stafford38Challenge.universalStatement
