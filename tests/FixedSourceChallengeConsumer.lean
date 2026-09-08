import FixedSourceSolution

/-!
# Consumers for the exact-source challenge statement

These are literal downstream uses of the compared theorem
`Stafford38FixedSourceChallenge.universalFixedSourceStatement` at the concrete
field `ℚ` and Weyl rank one.  They check three things independently of the
transport's own bookkeeping:

* the intrinsic degree of the unit is `0`, once directly from the challenge's
  definition (the unit is an ordered word of total degree zero, so the least
  filtration level is zero) and once through the transport;
* the intrinsic degree of the coordinate generator is `1`;
* the compared theorem instantiates at both elements with the exponent
  evaluated, so the source is `ell ^ 0` for the unit and `ell ^ 1` for the
  coordinate, and the written order `d * R + ell ^ e * d * S` is kept.
-/

namespace Stafford38FixedSourceChallengeConsumer

open Stafford38FixedSourceChallenge
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBW

/-- Intrinsic computation, with no transport: the unit lies in the challenge's
degree-zero piece, so the least level is zero. -/
theorem unit_degree_intrinsic : bernsteinDegree ℚ (1 : WeylAlg ℚ 1) = 0 := by
  apply Nat.sInf_eq_zero.mpr
  left
  show (1 : WeylAlg ℚ 1) ∈ bernsteinPiece ℚ 1 0
  apply Submodule.subset_span
  refine ⟨0, 0, le_rfl, ?_⟩
  show (1 : WeylAlg ℚ 1) = orderedMonomial ℚ (0 + 1) 0 0
  simp only [orderedMonomial, freeOrderedMonomial, Pi.zero_apply, pow_zero,
    mul_one, map_one]

/-- The same value through the transport to the checked normal form. -/
theorem unit_degree : bernsteinDegree ℚ (1 : WeylAlg ℚ 1) = 0 := by
  apply Eq.trans (Stafford38FixedSourceChallengeTransport.bernsteinDegree_eq ℚ
    (1 : WeylAlg ℚ 1))
  change MvPolynomial.weightedTotalDegree (1 : PhaseVar 1 → ℕ)
    (presentedNormalFormLinearEquiv ℚ 1 (1 : PresentedWeyl ℚ 1)) = 0
  rw [presentedNormalFormLinearEquiv_one, MvPolynomial.weightedTotalDegree_one,
    MvPolynomial.totalDegree_one]

/-- The coordinate generator `x₀` has intrinsic degree one. -/
theorem coordinate_degree :
    bernsteinDegree ℚ (generator ℚ 1 (.inl (0 : Fin 1))) = 1 := by
  rw [Stafford38FixedSourceChallengeTransport.generator_eq,
    Stafford38FixedSourceChallengeTransport.bernsteinDegree_eq ℚ
      (Stafford.freeWeylGenerator (Matrix.J (Fin 1) ℚ) (.inl (0 : Fin 1)))]
  change MvPolynomial.weightedTotalDegree (1 : PhaseVar 1 → ℕ)
    (presentedNormalFormLinearEquiv ℚ 1
      (Stafford.freeWeylGenerator (Matrix.J (Fin 1) ℚ) (.inl (0 : Fin 1)))) = 1
  rw [presentedNormalFormLinearEquiv_generator,
    MvPolynomial.weightedTotalDegree_one, MvPolynomial.totalDegree_X]

theorem one_ne_zero_rank_one : (1 : WeylAlg ℚ 1) ≠ 0 := by
  intro h
  have h' : presentedNormalFormLinearEquiv ℚ 1 (1 : PresentedWeyl ℚ 1) =
      presentedNormalFormLinearEquiv ℚ 1 (0 : PresentedWeyl ℚ 1) :=
    congrArg _ h
  rw [presentedNormalFormLinearEquiv_one, map_zero] at h'
  exact one_ne_zero h'

theorem coordinate_ne_zero_rank_one :
    generator ℚ 1 (.inl (0 : Fin 1)) ≠ 0 := by
  intro h
  have h' : presentedNormalFormLinearEquiv ℚ 1
        (Stafford.freeWeylGenerator (Matrix.J (Fin 1) ℚ) (.inl (0 : Fin 1))) =
      presentedNormalFormLinearEquiv ℚ 1 (0 : PresentedWeyl ℚ 1) :=
    congrArg _ h
  rw [presentedNormalFormLinearEquiv_generator, map_zero] at h'
  exact MvPolynomial.X_ne_zero _ h'

/-- The compared theorem at `d = 1`: the source exponent is the intrinsic
degree `0`, so the multiplier is `ell ^ 0`. -/
theorem rank_one_unit_consumer :
    ∃ ell R S : WeylAlg ℚ 1,
      IsLinearWeylCoordinate ℚ 0 ell ∧
        (1 : WeylAlg ℚ 1) = 1 * R + ell ^ 0 * 1 * S := by
  have h := Stafford38FixedSourceChallenge.universalFixedSourceStatement
    ℚ 0 (1 : WeylAlg ℚ 1) one_ne_zero_rank_one
  rw [unit_degree] at h
  exact h

/-- The compared theorem at `d = x₀`: the source exponent is the intrinsic
degree `1`, so the multiplier is `ell ^ 1`, to the left of `d`. -/
theorem rank_one_coordinate_consumer :
    ∃ ell R S : WeylAlg ℚ 1,
      IsLinearWeylCoordinate ℚ 0 ell ∧
        (1 : WeylAlg ℚ 1) =
          generator ℚ 1 (.inl (0 : Fin 1)) * R +
            ell ^ 1 * generator ℚ 1 (.inl (0 : Fin 1)) * S := by
  have h := Stafford38FixedSourceChallenge.universalFixedSourceStatement
    ℚ 0 (generator ℚ 1 (.inl (0 : Fin 1))) coordinate_ne_zero_rank_one
  rw [coordinate_degree] at h
  exact h

end Stafford38FixedSourceChallengeConsumer

#print axioms Stafford38FixedSourceChallengeConsumer.unit_degree_intrinsic
#print axioms Stafford38FixedSourceChallengeConsumer.unit_degree
#print axioms Stafford38FixedSourceChallengeConsumer.coordinate_degree
#print axioms Stafford38FixedSourceChallengeConsumer.rank_one_unit_consumer
#print axioms Stafford38FixedSourceChallengeConsumer.rank_one_coordinate_consumer
