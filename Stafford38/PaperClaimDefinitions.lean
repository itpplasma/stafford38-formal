module
public import Stafford38.ChallengeDefinitions
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

/-!
# Shared Mathlib-only definitions of the further paper claims

Stable cyclicity in Corollary 6.3 and the Section 7 consequences of Theorem 1.1.
`Challenge.lean` repeats these definitions after those of
`Stafford38.ChallengeDefinitions`; the solution side reaches them here.
-/

namespace Stafford38Challenge

universe u v

/-- Stafford's *stably cyclic* [Sta78, p. 435], as quoted in the proof of
Corollary 6.3 (tex line 1619): "given `l ≥ 1` and `a_1, …, a_{l+1} ∈ T` that
generate `T`, there exist `f_i ∈ A_n` such that `a_i + a_{l+1} f_i`,
`i = 1, …, l`, also generate `T`". -/
def IsStablyCyclic (A : Type u) (T : Type v) [Ring A] [AddCommGroup T] [Module Aᵐᵒᵖ T] :
    Prop :=
  ∀ l ≥ 1, ∀ a : Fin (l + 1) → T, Submodule.span Aᵐᵒᵖ (Set.range a) = ⊤ →
    ∃ f : Fin l → A, Submodule.span Aᵐᵒᵖ
      (Set.range fun i : Fin l => a i.castSucc + (MulOpposite.op (f i) : Aᵐᵒᵖ) • a (Fin.last l)) =
        ⊤

/-- **Corollary 6.3, stable cyclicity** (tex lines 75, 108, 1619).  Every
finitely generated torsion right `A_n(k)`-module is stably cyclic. -/
def PaperCorollary_6_3_stablyCyclic : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (M : Type v) [AddCommGroup M]
    [Module (WeylAlg k n)ᵐᵒᵖ M] [Module.Finite (WeylAlg k n)ᵐᵒᵖ M],
    Stafford38.TorsionCyclicity.IsRightTorsion (A := WeylAlg k n) (M := M) →
      IsStablyCyclic (WeylAlg k n) M

/-- **Section 7, left-handed identity** (tex lines 1629–1630): every nonzero
`d ∈ A_n(k)` has `R, S, F` with `1 = Rd + SdF`. -/
def LeftHandedIdentity : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (d : WeylAlg k n), d ≠ 0 →
    ∃ R S F : WeylAlg k n, (1 : WeylAlg k n) = R * d + S * d * F

/-- Every element of a left module is killed by some nonzero scalar. -/
def IsLeftTorsion (A : Type u) (M : Type v) [Ring A] [AddCommGroup M] [Module A M] : Prop :=
  ∀ m : M, ∃ d : A, d ≠ 0 ∧ d • m = 0

/-- A left module `M` is cyclic: `M = Am` for some `m ∈ M`. -/
def IsLeftCyclicModule (A : Type u) (M : Type v) [Ring A] [AddCommGroup M] [Module A M] :
    Prop :=
  ∃ m : M, ∀ x : M, ∃ a : A, x = a • m

/-- **Section 7, Corollary 6.3 for left torsion modules** (tex line 1630):
every finitely generated torsion left `A_n(k)`-module is cyclic. -/
def LeftCorollary_6_3 : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (M : Type v) [AddCommGroup M]
    [Module (WeylAlg k n) M] [Module.Finite (WeylAlg k n) M],
    IsLeftTorsion (WeylAlg k n) M → IsLeftCyclicModule (WeylAlg k n) M

/-- `P` is a `k`-linear differential operator of order at most `N` on the
commutative `k`-algebra `B` (Grothendieck): every iterated commutator
`[…[[P, b₀], b₁], …, b_N]` with multiplication operators vanishes, where
`[Q, b] = Q ∘ b − b ∘ Q`. -/
def IsDifferentialOperatorOfOrder (k : Type u) (B : Type v) [CommRing k] [CommRing B]
    [Algebra k B] (N : ℕ) (P : Module.End k B) : Prop :=
  ∀ b : List B, b.length = N + 1 →
    b.foldl (fun Q c => Q * LinearMap.mulLeft k c - LinearMap.mulLeft k c * Q) P = 0

/-- `P` is a `k`-linear differential operator of finite order on `B`. -/
def IsDifferentialOperator (k : Type u) (B : Type v) [CommRing k] [CommRing B]
    [Algebra k B] (P : Module.End k B) : Prop :=
  ∃ N, IsDifferentialOperatorOfOrder k B N P

/-- The identity `1 = dR + FdS` in the ring `D_k(B)` of finite-order
`k`-linear differential operators on `B`: for every nonzero `d ∈ D_k(B)` there
are `F, R, S ∈ D_k(B)` with `1 = dR + FdS`. -/
def HasDifferentialIdentity (k : Type u) (B : Type v) [CommRing k] [CommRing B]
    [Algebra k B] : Prop :=
  ∀ d : Module.End k B, IsDifferentialOperator k B d → d ≠ 0 →
    ∃ F R S : Module.End k B, IsDifferentialOperator k B F ∧ IsDifferentialOperator k B R ∧
      IsDifferentialOperator k B S ∧ (1 : Module.End k B) = d * R + F * d * S

/-- **Section 7, localizations** (tex lines 1630–1631): the identity for
finite-order differential operators on every localization `B = S⁻¹k[x_1, …, x_n]`. -/
def LocalizedDifferentialIdentity : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (S : Submonoid (MvPolynomial (Fin n) k))
    (B : Type v) [CommRing B] [Algebra (MvPolynomial (Fin n) k) B] [Algebra k B]
    [IsScalarTower k (MvPolynomial (Fin n) k) B] [IsLocalization S B],
    HasDifferentialIdentity k B

/-- **Section 7, evolutionary identity** (tex lines 1631–1634): for `r ≥ 1`, in
every `k`-algebra `D` with `px = xp + 1`, the element
`d = p^r − ∑_j a_j x^{m_j}`, each `a_j` commuting with `x` and `p`, has
`R, S` with `1 = dR + x^r d S`. -/
def EvolutionaryIdentity : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (D : Type v) [Ring D] [Algebra k D] (x p : D),
    p * x = x * p + 1 → ∀ r : ℕ, 1 ≤ r → ∀ (J : ℕ) (a : Fin J → D) (m : Fin J → ℕ),
      (∀ j, a j * x = x * a j) → (∀ j, a j * p = p * a j) →
        ∃ R S : D, (1 : D) = (p ^ r - ∑ j, a j * x ^ m j) * R +
          x ^ r * (p ^ r - ∑ j, a j * x ^ m j) * S

end Stafford38Challenge
