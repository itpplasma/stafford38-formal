module
public import Stafford38.ChallengeDefinitions
public import Stafford38.FoundationClosure

@[expose] public section

namespace Stafford38Challenge

/-- The exact Mathlib-only challenge statement is the theorem already proved
by the substantive Stafford development; the two Weyl presentations reduce
definitionally to the same shared RingQuot. -/
theorem universalStatement : UniversalStatement := by
  intro k _ _ n d hd
  exact Stafford38.universalStatement (k := k) n d hd

end Stafford38Challenge
