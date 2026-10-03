module
public import Stafford38.ChallengeDefinitions
public import proofs.stafford38_reduction

@[expose] public section

universe u

theorem reduction_predicate_keeps_exact_certificate
    {k A : Type*} [Field k] [Ring A] [Algebra k A] (e : A) :
    Stafford.Reduction.Stafford38 e ↔
      ∃ F R S : A, (1 : A) = e * R + F * e * S := Iff.rfl

theorem challenge_uses_canonical_predicate :
    Stafford38Challenge.UniversalStatement.{u} =
      (∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
        (d : Stafford38Challenge.WeylAlg k n),
        d ≠ 0 → Stafford.Reduction.Stafford38 d) := rfl

theorem challenge_keeps_original_operator_order :
    Stafford38Challenge.UniversalStatement.{u} =
      (∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
        (d : Stafford38Challenge.WeylAlg k n),
        d ≠ 0 → ∃ F R S : Stafford38Challenge.WeylAlg k n,
          (1 : Stafford38Challenge.WeylAlg k n) = d * R + F * d * S) := rfl

theorem old_reduction_api_still_targets_canonical_predicate
    {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (hM : Stafford.Reduction.Monicization k A)
    (hE : Stafford.Reduction.ExponentHypothesis A) :
    ∀ e : A, e ≠ 0 → Stafford.Reduction.Stafford38 e :=
  Stafford.Reduction.stafford38_of_hypotheses hM hE

#print axioms reduction_predicate_keeps_exact_certificate
#print axioms challenge_uses_canonical_predicate
#print axioms challenge_keeps_original_operator_order
#print axioms old_reduction_api_still_targets_canonical_predicate
