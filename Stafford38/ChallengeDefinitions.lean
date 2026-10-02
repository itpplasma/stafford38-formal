import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Order.Lattice.Nat

/-!
# Shared Mathlib-only Stafford challenge definitions

The challenge statements and the proof development use the same presented
Weyl algebra and certificate predicate. This file is the single owner of that
presentation, the generic single-element conclusion, the right-torsion
predicate, and the literal fixed-source challenge definitions. It imports no
proof module and no challenge theorem with a placeholder, so both solution files can
use it directly.
-/

namespace Stafford

variable {k A ι : Type*} [Field k] [Ring A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]

/-- Linear combination of an indexed family by the rows of a matrix. -/
def linearCombination (M : Matrix ι ι k) (z : ι → A) (i : ι) : A :=
  ∑ j, algebraMap k A (M i j) * z j

variable {k ι : Type*} [Field k]

/-- The commutator relations presenting a Weyl-type algebra. -/
def freeWeylRelation (omega : Matrix ι ι k)
    (a b : FreeAlgebra k ι) : Prop :=
  ∃ i j,
    a = FreeAlgebra.ι k i * FreeAlgebra.ι k j -
      FreeAlgebra.ι k j * FreeAlgebra.ι k i ∧
    b = algebraMap k (FreeAlgebra k ι) (omega i j)

/-- The free algebra modulo the commutator relations encoded by `omega`. -/
abbrev FreeWeyl (k : Type*) [Field k] (ι : Type*)
    (omega : Matrix ι ι k) := RingQuot (freeWeylRelation omega)

/-- The canonical generators of the presented Weyl-type algebra. -/
def freeWeylGenerator (omega : Matrix ι ι k) (i : ι) : FreeWeyl k ι omega :=
  RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k i)

end Stafford

namespace Stafford
namespace Reduction

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- Stafford 3.8 for one element, in written operator order. -/
def Stafford38 (e : A) : Prop := ∃ F R S : A, (1 : A) = e * R + F * e * S

end Reduction
end Stafford

namespace Stafford38Challenge

universe u

/-- Index type of the coordinate and momentum generators. -/
abbrev PhaseVar (n : ℕ) := Fin n ⊕ Fin n

/-- The Weyl commutator relation for the standard symplectic matrix. -/
abbrev relation {k : Type*} [Field k] {n : ℕ}
    (omega : Matrix (PhaseVar n) (PhaseVar n) k)
    (a b : FreeAlgebra k (PhaseVar n)) : Prop :=
  Stafford.freeWeylRelation omega a b

/-- The standard presented Weyl algebra, shared with the substantive proof. -/
abbrev WeylAlg (k : Type*) [Field k] (n : ℕ) :=
  Stafford.FreeWeyl k (PhaseVar n) (Matrix.J (Fin n) k)

/-- Stafford's Conjecture 3.8 in its intended nonzero form. -/
def UniversalStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (d : WeylAlg k n),
    d ≠ 0 → Stafford.Reduction.Stafford38 d

/-- A named generator in the canonical presentation. -/
abbrev generator (k : Type*) [Field k] (n : ℕ) (i : PhaseVar n) : WeylAlg k n :=
  Stafford.freeWeylGenerator (Matrix.J (Fin n) k) i

/-- The standard symplectic form used for the fixed-source coordinate. -/
abbrev standardForm (k : Type*) [Field k] (n : ℕ) :
    Matrix (PhaseVar n) (PhaseVar n) k := Matrix.J (Fin n) k

end Stafford38Challenge

namespace Stafford38FixedSourceChallenge

universe u

/-- The fixed-source challenge uses the same phase variables and Weyl
presentation as the ordinary challenge. -/
abbrev PhaseVar (n : ℕ) := Stafford38Challenge.PhaseVar n

abbrev relation {k : Type u} [Field k] {n : ℕ}
    (omega : Matrix (PhaseVar n) (PhaseVar n) k)
    (a b : FreeAlgebra k (PhaseVar n)) : Prop :=
  Stafford38Challenge.relation omega a b

abbrev WeylAlg (k : Type u) [Field k] (n : ℕ) :=
  Stafford38Challenge.WeylAlg k n

abbrev generator (k : Type u) [Field k] (n : ℕ) (i : PhaseVar n) : WeylAlg k n :=
  Stafford38Challenge.generator k n i

/-- Insert an old phase variable after the newest coordinate or momentum. -/
def oldIndex {n : ℕ} : PhaseVar n → PhaseVar (n + 1)
  | .inl i => .inl i.succ
  | .inr i => .inr i.succ

@[simp] theorem oldIndex_inl {n : ℕ} (i : Fin n) :
    oldIndex (.inl i) = .inl i.succ := rfl

@[simp] theorem oldIndex_inr {n : ℕ} (i : Fin n) :
    oldIndex (.inr i) = .inr i.succ := rfl

/-- Insert an old free-algebra word into the next-rank free algebra. -/
def freeOldMap (k : Type u) [Field k] (n : ℕ) :
    FreeAlgebra k (PhaseVar n) →ₐ[k] FreeAlgebra k (PhaseVar (n + 1)) :=
  FreeAlgebra.lift k (fun i => FreeAlgebra.ι k (oldIndex i))

/-- Ordered PBW words, with old pairs followed by the newest pair. -/
def freeOrderedMonomial (k : Type u) [Field k] :
    (n : ℕ) → (Fin n → ℕ) → (Fin n → ℕ) → FreeAlgebra k (PhaseVar n)
  | 0, _, _ => 1
  | n + 1, a, p =>
      freeOldMap k n
          (freeOrderedMonomial k n (fun i => a i.succ) (fun i => p i.succ)) *
        FreeAlgebra.ι k (.inl (0 : Fin (n + 1))) ^ a 0 *
        FreeAlgebra.ι k (.inr (0 : Fin (n + 1))) ^ p 0

/-- The image of an ordered PBW word in the shared Weyl quotient. -/
def orderedMonomial (k : Type u) [Field k] (n : ℕ)
    (a p : Fin n → ℕ) : WeylAlg k n :=
  RingQuot.mkAlgHom k (relation (k := k) (n := n) (Matrix.J (Fin n) k))
    (freeOrderedMonomial k n a p)

/-- Total degree of a split coordinate/momentum exponent. -/
def phaseDegree {n : ℕ} (a p : Fin n → ℕ) : ℕ :=
  (∑ i, a i) + ∑ i, p i

/-- Span of the ordered Weyl words of total degree at most `N`. -/
def bernsteinPiece (k : Type u) [Field k] (n N : ℕ) :
    Submodule k (WeylAlg k n) :=
  Submodule.span k
    {z | ∃ a p : Fin n → ℕ,
      phaseDegree a p ≤ N ∧ z = orderedMonomial k n a p}

/-- The intrinsic Bernstein degree of a presented element: its least piece. -/
noncomputable def bernsteinDegree (k : Type u) [Field k] {n : ℕ}
    (d : WeylAlg k n) : ℕ :=
  sInf {N : ℕ | d ∈ bernsteinPiece k n N}

/-- The shared matrix-row combination used to name a linear source. -/
abbrev linearCombination (k : Type u) [Field k] {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (z : PhaseVar n → WeylAlg k n) (i : PhaseVar n) : WeylAlg k n :=
  Stafford.linearCombination M z i

abbrev standardForm (k : Type u) [Field k] (n : ℕ) :
    Matrix (PhaseVar n) (PhaseVar n) k := Stafford38Challenge.standardForm k n

/-- A source coordinate obtained from an invertible symplectic linear change
of the canonical Weyl generators. -/
def IsLinearWeylCoordinate (k : Type u) [Field k] (n : ℕ)
    (ell : WeylAlg k (n + 1)) : Prop :=
  ∃ (M N : Matrix (PhaseVar (n + 1)) (PhaseVar (n + 1)) k)
      (_hM : M * standardForm k (n + 1) * Matrix.transpose M =
        standardForm k (n + 1))
      (_hN : N * standardForm k (n + 1) * Matrix.transpose N =
        standardForm k (n + 1))
      (_hMN : M * N = 1) (_hNM : N * M = 1),
      ell = linearCombination k N (generator k (n + 1))
        (.inl (0 : Fin (n + 1)))

/-- Shared template for the fixed-source proposition, parameterized only by
the chosen degree function. -/
def UniversalFixedSourceStatementWithDegree
    (degree : ∀ (k : Type u) [Field k] {n : ℕ}, WeylAlg k n → ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (d : WeylAlg k (n + 1)), d ≠ 0 →
      ∃ ell R S : WeylAlg k (n + 1),
        IsLinearWeylCoordinate k n ell ∧
          (1 : WeylAlg k (n + 1)) =
            d * R + ell ^ degree k d * d * S

/-- The exact fixed-source challenge, using the intrinsic degree. -/
abbrev UniversalFixedSourceStatement : Prop :=
  UniversalFixedSourceStatementWithDegree.{u} bernsteinDegree

end Stafford38FixedSourceChallenge

namespace Stafford38.TorsionCyclicity

universe u v

/-- Every element of a right module is killed by some nonzero right scalar. -/
def IsRightTorsion {A : Type u} {M : Type v} [Ring A]
    [AddCommGroup M] [Module Aᵐᵒᵖ M] : Prop :=
  ∀ m : M, ∃ d : A, d ≠ 0 ∧ (MulOpposite.op d : Aᵐᵒᵖ) • m = 0

end Stafford38.TorsionCyclicity
