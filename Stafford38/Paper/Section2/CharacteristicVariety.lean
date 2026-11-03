module

public import Stafford38.Paper.Section2.Geometry
public import Stafford38.Paper.Support.Gabber

@[expose] public section

/-!
# Definitions 2.4 and 2.7 for finitely generated modules

For a right `A_n(k)`-module `M` (a `(A_n(k))ᵐᵒᵖ`-module with compatible `k`-structure)
and a filtration `M_•` compatible with the order filtration, `gr M` is
`Support.Gabber.GrModule M_•`, a graded module over `gr A_n = k[x, ξ]`.

* `IsGoodFiltration`: Definition 2.4, good means `gr M` finitely generated over
  `k[x, ξ]`.
* `CharOf`: Definition 2.7, `Char(M) = V(Ann_{k[x,ξ]} gr M)`.
* `definition_2_7_independent`: `Char(M)` does not depend on the good filtration
  [HTT, Lemma D.3.1].  Two good filtrations satisfy `F_j ⊆ G_{j+c}` and
  `G_j ⊆ F_{j+c'}` (`Support.Gabber.exists_shift_le`), hence the radicals of the
  annihilators agree (`Support.Gabber.radical_annihilator_eq_of_shift`), and
  `V(J) = V(√J)`.
* `Char`: the special case `M = A_n(k)/I` with `M_m = qF_m` used in Sections 3–6;
  `Char_eq` is the repository's description `V(Ann gr Q)` with `gr Q = grCyclic`.
-/

namespace Stafford38.Paper.Section2

open Stafford38.Characteristic
open Stafford38.Paper.Support.Gabber
open Stafford38.WeylIteratedEquivalence
open Stafford38.EulerSurjectivity

noncomputable section

universe u w

section General

variable (k : Type u) [Field k] (n : ℕ)
variable {M : Type w} [AddCommGroup M] [Module (PresentedWeyl k n)ᵐᵒᵖ M] [Module k M]
  [IsScalarTower k (PresentedWeyl k n)ᵐᵒᵖ M]

/-- **Definition 2.4 (good filtration).** A filtration `M_•` of a right
`A_n(k)`-module `M`, compatible with the order filtration `F_•`, is good if
`gr M = ⊕_i M_i/M_{i-1}` is finitely generated over `gr^F A_n = k[x, ξ]`. -/
structure IsGoodFiltration (Γ : ℕ → Submodule k M) : Prop where
  compatible : IsCompatibleFiltration (orderFiltration k n) Γ
  finite : Module.Finite (SymbolRing k n) (GrModule Γ)

/-- **Definition 2.7 (characteristic variety).** For a finitely generated
`A_n(k)`-module `M` with a good order filtration `M_•`,
`Char(M) = V(Ann_{k[x,ξ]} gr M) ⊆ T^*X = Spec k[x, ξ]`. -/
def CharOf (Γ : ℕ → Submodule k M) : Set (CotangentBundle k n) :=
  V (Module.annihilator (SymbolRing k n) (GrModule Γ))

variable {k n}

/-- **Definition 2.7, last sentence.** `Char(M)` is independent of the choice of
the good filtration [HTT, Lemma D.3.1]. -/
theorem definition_2_7_independent {Γ Γ' : ℕ → Submodule k M}
    (hΓ : IsGoodFiltration k n Γ) (hΓ' : IsGoodFiltration k n Γ') :
    CharOf k n Γ = CharOf k n Γ' := by
  rw [CharOf, CharOf, V, V, ← PrimeSpectrum.zeroLocus_radical,
    radical_annihilator_eq_of_good hΓ.compatible hΓ'.compatible hΓ.finite hΓ'.finite,
    PrimeSpectrum.zeroLocus_radical]

end General

section Cyclic

variable (k : Type u) [Field k] {n : ℕ}

/-- **Definition 2.4, example.** For `Q = A_n(k)/I`, the filtration `Q_m = qF_m`
induced by the generator `q = [1]` is good. -/
theorem qFilt_isGoodFiltration (I : RightIdeal (PresentedWeyl k n)) :
    IsGoodFiltration k n (qFilt k I) :=
  ⟨cyclicFiltration_order_isCompatible k I, qFilt_good k I⟩

/-- `Char(A_n(k)/I)`, Definition 2.7 for `M = A_n(k)/I` with its good filtration
`Q_m = qF_m`; by `definition_2_7_independent` any good filtration gives the same set
(`Char_eq_charOf`). -/
def Char (I : RightIdeal (PresentedWeyl k n)) : Set (CotangentBundle k n) :=
  CharOf k n (qFilt k I)

/-- `Char(A_n/I) = V(Ann_{k[x,ξ]} gr Q)` with `gr Q` the repository's `grCyclic`. -/
theorem Char_eq (I : RightIdeal (PresentedWeyl k n)) :
    Char k I = V (Module.annihilator (SymbolRing k n) (grCyclic k I)) := by
  rw [Char, CharOf, annihilator_qFilt]

/-- `Char(A_n/I)` computed from any good filtration of `A_n/I`. -/
theorem Char_eq_charOf (I : RightIdeal (PresentedWeyl k n))
    {Γ : ℕ → Submodule k (RightQuotient I)} (hΓ : IsGoodFiltration k n Γ) :
    Char k I = CharOf k n Γ :=
  definition_2_7_independent (qFilt_isGoodFiltration k I) hΓ

/-- `gr Q` is finitely generated over `k[x, ξ]` because `Q_m = qF_m` is good. -/
theorem grCyclic_finite_of_good (I : RightIdeal (PresentedWeyl k n)) :
    Module.Finite (SymbolRing k n) (grCyclic k I) :=
  have := (qFilt_isGoodFiltration k I).finite
  Module.Finite.equiv (grCyclicEquivS k I).symm

end Cyclic

#print axioms definition_2_7_independent
#print axioms qFilt_isGoodFiltration
#print axioms Char_eq
#print axioms Char_eq_charOf
#print axioms grCyclic_finite_of_good

end

end Stafford38.Paper.Section2
