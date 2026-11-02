module

public import Stafford38.Paper.Section5.Place
public import Stafford38.Paper.Section5.ResidueBasis
public import Stafford38.Paper.Section5.TangentCone
public import Stafford38.Paper.Section5.GenericTangentRank
public import Stafford38.Paper.Section5.Steps
public import Stafford38.Paper.Section5.Proof
public import Stafford38.Geometry.ProjectiveConormalDirections

@[expose] public section

/-!
# Section 5.2 of the paper: Theorem 5.7 and its lemmas

The paper's lemmas are stated and proved in
`Stafford38.Paper.Section5.Place` (Lemmas 5.9, 5.10),
`Stafford38.Paper.Section5.ResidueBasis` (Lemma 5.11),
`Stafford38.Paper.Section5.TangentCone` and
`Stafford38.Paper.Section5.GenericTangentRank` (Lemmas 5.12, 5.13).

The paragraphs of the proof of Theorem 5.7(i) between those lemmas are stated
and proved in `Stafford38.Paper.Section5.Steps`; the theorems
`witness_lemma_*` there apply Lemmas 5.11–5.13 to the discrete valuation ring
and the Laurent column `q(t)` of the proof.
`Stafford38.Paper.Section5.Proof` chains the paragraphs into
`theorem_5_7_i_paper`, which `theorem_5_7_i` below restates.  The terminal
theorem in `GeneralAsymptoticConormal` proves the same statement by a second,
chart-based route and is kept unchanged.
-/

namespace Stafford38.Paper.Section5

open Stafford38.Geometry.ProjectiveConormalDirections

noncomputable section

universe u

/-- **Theorem 5.7(i).** If `Y = V(𝔭)` is nonempty, irreducible and avoids
`H = {x_1 = 0}`, every polynomial vanishing on the conormal cone `N(Y)` over the
smooth locus vanishes at `(1, 0, …, 0)`.  Proved paragraph by paragraph in
`theorem_5_7_i_paper`. -/
theorem theorem_5_7_i
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal)) :=
  theorem_5_7_i_paper hm I havoid

/-- **Theorem 5.7(ii).** `[dx_1] ∈ Dir(Y)`. -/
theorem theorem_5_7_ii
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    Projectivization.mk k
        (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0)
        (by intro h; have := congrFun h ⟨0, hm⟩; simp at this) ∈
      projectiveHomogeneousClosure
        (projectivizedDirectionSet (smoothConormalDirectionSet I.asIdeal)) :=
  mk_mem_projectiveHomogeneousClosure_of_fibre_zeroLocus I.asIdeal _ _
    (theorem_5_7_i hm I havoid)

#print axioms theorem_5_7_i
#print axioms theorem_5_7_ii

end

end Stafford38.Paper.Section5
