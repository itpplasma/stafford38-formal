module

public import Stafford38.Paper.Section4.Euler
public import Stafford38.Paper.Section4.Residue
public import Stafford38.Paper.Section4.Surjectivity
public import Stafford38.Paper.Section4.Support
public import Stafford38.Paper.Section4.Setup
public import Stafford38.Paper.Section4.TangentialFiniteness
public import Stafford38.Paper.Section4.PageInequality
public import Stafford38.Paper.Section4.StrictInequality
public import Stafford38.Paper.Section4.Vanishing

@[expose] public section

/-!
# Section 4 of the paper: `x₁` as a surjective map

* `Stafford38.Paper.Section4.Euler`: the Euler grading paragraph (equation
  (nonnegative-pbw), normality of `x₁` in `A_{≥0}`) and Lemma 4.1.
* `Stafford38.Paper.Section4.Residue`: Lemma 4.2, `1 + u₀x₁ ∈ 𝓘`.
* `Stafford38.Paper.Section4.Surjectivity`: Proposition 4.3, `Q = Qx₁`.
* `Stafford38.Paper.Section4.Support`: Definitions 4.4–4.6 and Lemma 4.7.
* `Stafford38.Paper.Section4.Setup`: the objects `M = gr Q`, `f`, `V`, `U`, `T`.
* `Stafford38.Paper.Section4.TangentialFiniteness`: Lemma 4.8.
* `Stafford38.Paper.Section4.PageInequality`: Lemma 4.9.
* `Stafford38.Paper.Section4.StrictInequality`: Lemma 4.10.
* `Stafford38.Paper.Section4.Vanishing`: Corollary 4.11.

As in the paper, every statement from Lemma 4.2 on assumes `d̃` in the form
(3.1) (`Section3.IsMonicNormalForm`, with `N ≥ 1` where the proof needs it), and
Lemma 4.1 is stated for `x₁, ∂₁ ∈ A_n(k)`; the proofs pass to the PBW-monic
consequence `Section3.isPBWMonicAt_of_isMonicNormalForm` internally.

Each printed proof is assembled from `step_*` declarations, one per paragraph,
and calls the paper declarations it cites: Proposition 4.3 uses Lemma 4.2 (which
uses Lemma 4.1); Lemma 4.8 uses Lemma 4.7; Lemma 4.9 uses Lemma 4.8 and
Proposition 4.3; Lemma 4.10 uses Lemma 4.8; Corollary 4.11 uses Lemmas 4.8–4.10.
-/

namespace Stafford38.Paper.Section4

#print axioms proposition_4_3
#print axioms corollary_4_11
#print axioms corollary_4_11_quotSMulTop

end Stafford38.Paper.Section4
