import Stafford38.ChallengeDefinitions

/-!
# Stafford's exact fixed-source strengthening

This file states the exact fixed-source challenge using the shared Mathlib-only
Weyl presentation and definitions from `Stafford38.ChallengeDefinitions`.
The Bernstein filtration is the span of images of the ordered PBW words of
bounded total word degree, and `bernsteinDegree` is its least membership
level. Thus the exponent is attached to the presented element itself; it is
not an extra degree or supplied normal-form datum.
-/

namespace Stafford38FixedSourceChallenge

/-- The compared theorem. `FixedSourceSolution.lean` supplies the proof. -/
theorem universalFixedSourceStatement : UniversalFixedSourceStatement := by
  sorry

end Stafford38FixedSourceChallenge
