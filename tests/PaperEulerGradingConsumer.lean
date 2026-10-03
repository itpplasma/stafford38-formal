module
public import Stafford38.Weyl.QuotientTransport
public import Stafford38.Weyl.PaperEulerGrading

@[expose] public section

/-! A separate client pins the intended public statements of the paper Euler
grading bridge and confirms the official quotient path retains the same
literal surjectivity type. -/

open Stafford38.OrePairStage
open Stafford38.OreIteratedPairStage
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylEulerResidue
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport
open Stafford38.EulerSurjectivity

example (b : ℚ) (a c : ℕ) :
    Stafford38.PaperEulerGrading.eulerAdjoint ℚ
        (pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ c) =
      ((a : ℤ) - c) • (pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ c) := by
  exact Stafford38.PaperEulerGrading.orderedPBWMonomial_eulerWeight ℚ b a c

example : Stafford38.PaperEulerGrading.pbwNonnegativeEulerPart ℚ =
    Stafford38.WeylEulerSubring.pairEulerSubring ℚ := by
  exact Stafford38.PaperEulerGrading.pbwNonnegativeEulerPart_eq_transverseEulerSubring ℚ

example (b : ℚ) (a c : ℕ) (hca : c < a) :
    ∃ U : Stafford38.PaperEulerGrading.pbwNonnegativeEulerPart ℚ,
      pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ c =
        (U : PairStage (B := ℚ)) * pairCoordinate := by
  exact Stafford38.PaperEulerGrading.orderedPBWMonomial_positive_eulerFactor
    ℚ b a c hca

example (n N : ℕ) {d : PresentedWeyl ℚ (n + 1)}
    (hd : IsPBWMonicAt ℚ (.inr (0 : Fin (n + 1))) N d) :
    Function.Surjective
      (rightMul
        (canonicalRightIdeal (pairCoordinate (B := IteratedPairStage ℚ n))
          (presentedToIterated ℚ (n + 1) d) N)
        (pairCoordinate (B := IteratedPairStage ℚ n))) := by
  exact Stafford38.PaperEulerGrading.presentedCanonicalQuotient_rightMul_coordinate_surjective
    ℚ n N hd

#print axioms Stafford38.PaperEulerGrading.orderedPBWMonomial_eulerWeight
#print axioms Stafford38.PaperEulerGrading.pbwNonnegativeEulerPart_eq_transverseEulerSubring
#print axioms Stafford38.PaperEulerGrading.orderedPBWMonomial_positive_eulerFactor
#print axioms Stafford38.PaperEulerGrading.presentedCanonicalQuotient_rightMul_coordinate_surjective
#print axioms presentedCanonicalRightQuotient_rightMul_coordinate_surjective
