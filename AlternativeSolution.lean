module
public import Stafford38.ChallengeDefinitions
public import Stafford38.ChallengeBridge
public import Stafford38.FoundationClosure
public import Stafford38.TorsionCyclicity
public import AlternativeFixedSourceSolution

@[expose] public section

/-!
# Alternative solution: the earlier route

The same three compared theorems, proved by the substantive development that
preceded the paper-route formalization: `Stafford38.universalStatement`, the
fixed-source theorem of `AlternativeFixedSourceSolution` and
`Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion`, with the
equivalences of `Stafford38.ChallengeBridge`.
-/

namespace Stafford38Challenge

theorem universalStatement : UniversalStatement := by
  intro k _ _ n d hd
  exact Stafford38.universalStatement (k := k) n d hd

theorem theorem_1_1 : PaperTheorem_1_1 :=
  paperTheorem_1_1_of universalStatement
    Stafford38FixedSourceChallenge.universalFixedSourceStatement

theorem corollary_6_3 : PaperCorollary_6_3 :=
  paperCorollary_6_3_of fun k _ _ n M _ _ _ hM =>
    Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion k n M hM

end Stafford38Challenge

#print axioms Stafford38Challenge.universalStatement
#print axioms Stafford38Challenge.theorem_1_1
#print axioms Stafford38Challenge.corollary_6_3
