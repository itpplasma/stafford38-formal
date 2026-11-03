module

public import Stafford38.Paper.Section3.Symplectic
public import Stafford38.Paper.Section3.PhiG
public import Stafford38.Paper.Section3.RightDecomposition
public import Stafford38.Paper.Section3.MonicForm
public import Stafford38.Paper.Section3.Monic
public import Stafford38.Paper.Section3.Transport
public import Stafford38.Paper.Section3.OrderSymbol

@[expose] public section

/-!
# Section 3 of the paper: mapping to a normal form

* `Stafford38.Paper.Section3.Symplectic`: symplectic bases and Lemma 3.1
  (`lemma_3_1`, steps `step_lemma_3_1_*`).
* `Stafford38.Paper.Section3.PhiG`: the standard form `ω` on `𝕍 = k^{2n}` and
  the automorphism `Φ_g` (`phiG`, `step_phi_g`).
* `Stafford38.Paper.Section3.RightDecomposition`: `d = ∑_{j≤N} p^j a_j` with
  `deg_B a_j ≤ N - j` for `d ∈ B_N` (`exists_bounded_decomposition`).
* `Stafford38.Paper.Section3.MonicForm`: the normal form (3.1)
  (`IsMonicNormalForm`) and the symbols of `p^j a` with `a ∈ C`.
  Notation, filtrations and `deg_B` are those of Section 2
  (`Stafford38.Paper.Section2`).
* `Stafford38.Paper.Section3.Monic`: the opening paragraph
  (`step_scalar_case`) and Proposition 3.2 (`proposition_3_2`, steps
  `step_3_2_*`).
* `Stafford38.Paper.Section3.Transport`: Remark 3.3 (`remark_3_3`,
  `remark_3_3_of_Q_eq_zero`), the ideal `𝓘` and module `Q` of (3.2)
  (`idealI`, `Q`) and `section_3_reduction` for the final assembly.
* `Stafford38.Paper.Section3.OrderSymbol`: Definition 3.4 (`IsMonicInXi1`),
  Lemma 3.5 (`lemma_3_5`, steps `step_3_5_*`) and Proposition 3.6
  (`proposition_3_6`, steps `step_3_6_*`).
-/

namespace Stafford38.Paper.Section3

#print axioms lemma_3_1
#print axioms step_phi_g
#print axioms step_scalar_case
#print axioms proposition_3_2
#print axioms remark_3_3
#print axioms remark_3_3_of_Q_eq_zero
#print axioms section_3_reduction
#print axioms lemma_3_5
#print axioms lemma_3_5_eval_axis
#print axioms proposition_3_6

end Stafford38.Paper.Section3
