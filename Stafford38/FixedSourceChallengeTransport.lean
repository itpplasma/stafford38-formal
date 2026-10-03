module
public import Stafford38.FixedSourceStatement
public import Stafford38.ChallengeDefinitions
public import Mathlib.Order.Lattice.Nat

/-!
# Transport for the Mathlib-only exact-source challenge

`FixedSourceChallenge.lean` states the exact fixed-source theorem using only
Mathlib: the Weyl algebra is the `RingQuot` of the free algebra by the Weyl
commutator relation, the Bernstein filtration is the span of the images of the
ordered PBW words of bounded total degree, and the Bernstein degree of an
element is the least filtration level containing it.

The challenge and this transport import their unique definitions from the
Mathlib-only `Stafford38.ChallengeDefinitions` module; this file does not
public import the placeholder challenge. It proves that the literal definitions

agree with the substantive development:

* the challenge quotient is definitionally the presented Weyl algebra
  `Stafford38.WeylIteratedEquivalence.PresentedWeyl`;
* the challenge ordered words are the development's
  `Stafford38.WeylPBW.presentedOrderedMonomial`;
* the challenge filtration is the development's Bernstein filtration
  `Stafford38.WeylFiltration.bernsteinPiece`;
* the challenge degree is the development's checked PBW normal-form degree
  `Stafford38.FixedSource.bernsteinDegree`;
* the two linear-coordinate predicates are definitionally the same.

`FixedSourceSolution.lean` combines these identifications with the proved
theorem `Stafford38.universalFixedSourceStatement`. No degree and no
normal-form datum is supplied as a hypothesis anywhere.
-/

@[expose] public section

namespace Stafford38FixedSourceChallengeTransport

open Stafford
open Stafford38.WeylPBW
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence

universe u

variable (k : Type u) [Field k]

/-- The challenge quotient is the presented Weyl algebra, definitionally. -/
theorem weylAlg_eq (n : ℕ) :
    Stafford38FixedSourceChallenge.WeylAlg k n = PresentedWeyl k n := rfl

/-- The challenge generators are the presented generators, definitionally. -/
theorem generator_eq (n : ℕ) (i : Stafford38FixedSourceChallenge.PhaseVar n) :
    Stafford38FixedSourceChallenge.generator k n i =
      freeWeylGenerator (Matrix.J (Fin n) k) i := rfl

theorem oldIndex_eq {n : ℕ} (i : Stafford38FixedSourceChallenge.PhaseVar n) :
    Stafford38FixedSourceChallenge.oldIndex i =
      Stafford38.WeylIteratedEquivalence.oldIndex i := by
  cases i <;> rfl

/-- Inserting an old free word and passing to the quotient agrees with the
development's rank-shift embedding of the old quotient. -/
theorem mkAlgHom_freeOldMap (n : ℕ)
    (x : FreeAlgebra k (Stafford38FixedSourceChallenge.PhaseVar n)) :
    RingQuot.mkAlgHom k
        (Stafford38FixedSourceChallenge.relation (k := k) (n := n + 1)
          (Matrix.J (Fin (n + 1)) k))
        (Stafford38FixedSourceChallenge.freeOldMap k n x) =
      previousWeylEmbedding k n
        (RingQuot.mkAlgHom k
          (Stafford38FixedSourceChallenge.relation (k := k) (n := n)
            (Matrix.J (Fin n) k)) x) := by
  have h :
      (RingQuot.mkAlgHom k
          (Stafford38FixedSourceChallenge.relation (k := k) (n := n + 1)
            (Matrix.J (Fin (n + 1)) k))).comp
          (Stafford38FixedSourceChallenge.freeOldMap k n) =
        (previousWeylEmbedding k n).comp
          (RingQuot.mkAlgHom k
            (Stafford38FixedSourceChallenge.relation (k := k) (n := n)
              (Matrix.J (Fin n) k))) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, AlgHom.comp_apply,
      Stafford38FixedSourceChallenge.freeOldMap, FreeAlgebra.lift_ι_apply]
    change freeWeylGenerator (Matrix.J (Fin (n + 1)) k)
        (Stafford38FixedSourceChallenge.oldIndex i) =
      previousWeylEmbedding k n (freeWeylGenerator (Matrix.J (Fin n) k) i)
    rw [previousWeylEmbedding_generator, oldIndex_eq]
    rfl
  exact DFunLike.congr_fun h x

/-- The challenge ordered words are the development's ordered PBW words. -/
theorem orderedMonomial_eq :
    ∀ (n : ℕ) (a p : Fin n → ℕ),
      Stafford38FixedSourceChallenge.orderedMonomial k n a p =
        presentedOrderedMonomial k n a p := by
  intro n
  induction n with
  | zero =>
      intro a p
      simp only [Stafford38FixedSourceChallenge.orderedMonomial,
        Stafford38FixedSourceChallenge.freeOrderedMonomial,
        presentedOrderedMonomial, map_one]
  | succ n ih =>
      intro a p
      have htail := ih (fun i => a i.succ) (fun i => p i.succ)
      rw [Stafford38FixedSourceChallenge.orderedMonomial] at htail
      simp only [Stafford38FixedSourceChallenge.orderedMonomial,
        Stafford38FixedSourceChallenge.freeOrderedMonomial, map_mul, map_pow,
        presentedOrderedMonomial]
      rw [mkAlgHom_freeOldMap, htail]
      rfl

/-- The Bernstein weight of a split exponent is the challenge's total phase
degree. -/
theorem monomialWeight_bernstein_phaseExponent {n : ℕ} (a p : Fin n → ℕ) :
    monomialWeight (@bernsteinWeight n) (phaseExponent a p) =
      Stafford38FixedSourceChallenge.phaseDegree a p := by
  unfold monomialWeight bernsteinWeight Stafford38FixedSourceChallenge.phaseDegree
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp [Fintype.sum_sum_type]

/-- The challenge filtration is the development's Bernstein filtration. -/
theorem bernsteinPiece_eq (n N : ℕ) :
    Stafford38FixedSourceChallenge.bernsteinPiece k n N =
      Stafford38.WeylFiltration.bernsteinPiece k n N := by
  rw [Stafford38FixedSourceChallenge.bernsteinPiece,
    Stafford38.WeylFiltration.bernsteinPiece, presentedWeightPiece_eq_span]
  congr 1
  ext z
  simp only [presentedWeightBasisSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, p, hdeg, rfl⟩
    refine ⟨phaseExponent a p, ?_, ?_⟩
    · rw [monomialWeight_bernstein_phaseExponent]
      exact hdeg
    · rw [presentedPBWBasis_apply, orderedMonomial_eq]
      rfl
  · rintro ⟨m, hdeg, rfl⟩
    refine ⟨fun i => m (.inl i), fun i => m (.inr i), ?_, ?_⟩
    · rw [← monomialWeight_bernstein_phaseExponent, phaseExponent_split]
      exact hdeg
    · rw [presentedPBWBasis_apply, orderedMonomial_eq]

/-- The challenge's intrinsic degree is the development's checked PBW
normal-form degree. -/
theorem bernsteinDegree_eq {n : ℕ} (d : PresentedWeyl k n) :
    Stafford38FixedSourceChallenge.bernsteinDegree k d =
      Stafford38.FixedSource.bernsteinDegree k d := by
  have hmem' : d ∈ presentedWeightPiece k (@bernsteinWeight n)
      (Stafford38.FixedSource.bernsteinDegree k d) :=
    (mem_presentedWeightPiece k _ _ d).mpr fun m hm =>
      MvPolynomial.le_weightedTotalDegree _
        (MvPolynomial.mem_support_iff.mpr hm)
  have hmem : d ∈ Stafford38FixedSourceChallenge.bernsteinPiece k n
      (Stafford38.FixedSource.bernsteinDegree k d) := by
    rw [bernsteinPiece_eq]
    exact hmem'
  have hle : ∀ N, d ∈ Stafford38FixedSourceChallenge.bernsteinPiece k n N →
      Stafford38.FixedSource.bernsteinDegree k d ≤ N := by
    intro N hN
    rw [bernsteinPiece_eq] at hN
    have hN' : d ∈ presentedWeightPiece k (@bernsteinWeight n) N := hN
    rw [mem_presentedWeightPiece] at hN'
    apply Finset.sup_le
    intro m hm
    exact hN' m (MvPolynomial.mem_support_iff.mp hm)
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · exact le_csInf ⟨_, hmem⟩ hle

/-- The two linear symplectic coordinate predicates are definitionally the
same. -/
theorem isLinearWeylCoordinate_iff (n : ℕ)
    (ell : Stafford38FixedSourceChallenge.WeylAlg k (n + 1)) :
    Stafford38FixedSourceChallenge.IsLinearWeylCoordinate k n ell ↔
      Stafford38.FixedSource.IsLinearWeylCoordinate k n ell :=
  Iff.rfl

/-- The literal fixed-source challenge and the substantive exact-source
proposition are equivalent, including the intrinsic degree and source
coordinate clauses. -/
theorem universalFixedSourceStatement_iff :
    Stafford38FixedSourceChallenge.UniversalFixedSourceStatement.{u} ↔
      Stafford38.FixedSource.UniversalFixedSourceStatement.{u} := by
  constructor
  · intro h k _ _ n d hd
    obtain ⟨ell, R, S, hcoord, hcert⟩ := h k n d hd
    have hdeg := bernsteinDegree_eq (k := k) d
    refine ⟨ell, R, S,
      (isLinearWeylCoordinate_iff (k := k) n ell).mp hcoord, ?_⟩
    rw [hdeg] at hcert
    exact hcert
  · intro h k _ _ n d hd
    obtain ⟨ell, R, S, hcoord, hcert⟩ := h k n d hd
    have hdeg := bernsteinDegree_eq (k := k) d
    refine ⟨ell, R, S,
      (isLinearWeylCoordinate_iff (k := k) n ell).mpr hcoord, ?_⟩
    change 1 = d * R + ell ^ Stafford38.FixedSource.bernsteinDegree k d * d * S at hcert
    rw [← hdeg] at hcert
    exact hcert

#print axioms orderedMonomial_eq
#print axioms bernsteinPiece_eq
#print axioms bernsteinDegree_eq
#print axioms isLinearWeylCoordinate_iff
#print axioms universalFixedSourceStatement_iff

end Stafford38FixedSourceChallengeTransport
