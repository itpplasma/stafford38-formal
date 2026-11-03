module

public import Stafford38.Paper.Section6.Avoidance
public import Stafford38.Paper.Section6.BaseChange
public import Stafford38.Paper.Section6.Proof
public import Stafford38.Paper.Section6.Ore
public import Stafford38.Paper.Section6.Cyclicity

@[expose] public section

/-!
# Section 6 of the paper: proof of Theorem 1.1

* `Stafford38.Paper.Section6.Avoidance`: Proposition 6.1
  (`proposition_6_1`, steps `step_6_1_*`), from Corollary 4.11.
* `Stafford38.Paper.Section6.BaseChange`: Lemma 6.2 (`lemma_6_2`, steps
  `step_6_2_*`).
* `Stafford38.Paper.Section6.Proof`: the proof of Theorem 1.1, one `step_W_*`
  per bullet, `theorem_6_Q_eq_zero` (`Q = 0`), `theorem_1_1_paper` and
  `theorem_1_1_fixedSource_paper`.
* `Stafford38.Paper.Section6.Ore`: `A_n(k)` is a right Ore domain
  (`weyl_rightOreCondition`), cited in the proof of Corollary 6.3.
* `Stafford38.Paper.Section6.Cyclicity`: the steps `step_6_3_*` and
  `corollary_6_3_of`, the proof of Corollary 6.3, and the proofs
  (`two_generators_of_identity`, `stably_generated_of_identity`) of the cited
  [Sta78, Thm. 3.7]; Corollary 6.3 and `stafford_1978_theorem_3_7` are stated
  in `Stafford38.Paper.Main`.
-/

namespace Stafford38.Paper.Section6

#print axioms proposition_6_1
#print axioms lemma_6_2
#print axioms theorem_6_Q_eq_zero
#print axioms theorem_1_1_paper
#print axioms theorem_1_1_fixedSource_paper
#print axioms weyl_rightOreCondition
#print axioms corollary_6_3_of

end Stafford38.Paper.Section6
