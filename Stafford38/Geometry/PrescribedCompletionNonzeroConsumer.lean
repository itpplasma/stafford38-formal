module
public import Stafford38.MathlibCompat.MvPolynomialCoeff
public import Stafford38.Geometry.PrescribedAffineResidueCompletionConsumer
public import Stafford38.Geometry.PrescribedCompletionNonzero

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.PrescribedCompletionNonzeroConsumer

open Stafford38.Geometry.PrescribedAffineResidueCompletion
open Stafford38.Geometry.PrescribedAffineResidueCompletionConsumer
open Stafford38.Geometry.PrescribedCompletionNonzero

noncomputable section

variable {k σ B : Type*} [Field k] [Fintype σ] [CommRing B] [Algebra k B]
  [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B]

local notation "R" => MvPolynomial σ k

/-- A centered coordinate vanishes at the chosen residue point but gives the
corresponding nonzero formal variable in the completed local chart. This is a
concrete check that bad-locus nonvanishing in the completion does not require
the closed point to avoid that locus. -/
theorem centeredCoordinate_vanishes_but_series_is_nonzero
    (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.EssFiniteType R B]
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    [IsDomain B]
    (hinjR : Function.Injective (algebraMap R B))
    (i : σ) :
    residueEvaluation (σ := σ) M eM
        (MvPolynomial.X i -
          MvPolynomial.C (residueCoordinates (σ := σ) M eM i)) = 0 ∧
    (powerSeriesCompletionAtGroundPoint (σ := σ) M eM).symm
      (AdicCompletion.of
        (IsLocalRing.maximalIdeal (Localization.AtPrime M))
        (Localization.AtPrime M)
        (algebraMap R (Localization.AtPrime M)
          (MvPolynomial.X i -
            MvPolynomial.C (residueCoordinates (σ := σ) M eM i)))) =
      MvPowerSeries.X i ∧
    (powerSeriesCompletionAtGroundPoint (σ := σ) M eM).symm
      (AdicCompletion.of
        (IsLocalRing.maximalIdeal (Localization.AtPrime M))
        (Localization.AtPrime M)
        (algebraMap R (Localization.AtPrime M)
          (MvPolynomial.X i -
            MvPolynomial.C (residueCoordinates (σ := σ) M eM i)))) ≠ 0 := by
  let f : R := MvPolynomial.X i -
    MvPolynomial.C (residueCoordinates (σ := σ) M eM i)
  have hpoint : residueEvaluation (σ := σ) M eM f = 0 := by
    rw [residueEvaluation_eq_aeval]
    simp [f]
  have hf : f ≠ 0 := by
    intro h
    have hi : Finsupp.single i 1 ≠ (0 : σ →₀ ℕ) := by
      intro hsingle
      have hcoord := congrArg (fun d : σ →₀ ℕ => d i) hsingle
      simp at hcoord
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) h
    dsimp [f] at hc
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_X_same,
      MvPolynomial.coeff_C_of_ne_zero hi] at hc
    exact one_ne_zero (sub_eq_zero.mp hc)
  have hB : algebraMap R B f ≠ 0 := by
    intro h
    apply hf
    exact hinjR (by simpa using h)
  have hmap :
      algebraMap R (Localization.AtPrime M) f =
        algebraMap B (Localization.AtPrime M) (algebraMap R B f) :=
    IsScalarTower.algebraMap_apply R B (Localization.AtPrime M) f
  let E := powerSeriesCompletionAtGroundPoint (σ := σ) M eM
  have hcoordinate : E (MvPowerSeries.X i) =
      AdicCompletion.of
        (IsLocalRing.maximalIdeal (Localization.AtPrime M))
        (Localization.AtPrime M) (algebraMap R (Localization.AtPrime M) f) := by
    simpa [E, f] using prescribedCompletion_centeredGenerator (σ := σ) M eM i
  have hseries : E.symm
      (AdicCompletion.of
        (IsLocalRing.maximalIdeal (Localization.AtPrime M))
        (Localization.AtPrime M) (algebraMap R (Localization.AtPrime M) f)) =
      MvPowerSeries.X i := by
    apply E.injective
    rw [RingEquiv.apply_symm_apply]
    exact hcoordinate.symm
  refine ⟨?_, ?_, ?_⟩
  · simpa [f] using hpoint
  · simpa [f, E] using hseries
  · have hnonzero :=
      prescribedSeries_image_ne_zero (k := k) (σ := σ) (B := B) M eM
        (algebraMap R B f) hB
    rw [← hmap] at hnonzero
    exact hnonzero

#print axioms centeredCoordinate_vanishes_but_series_is_nonzero

end
end Stafford38.Geometry.PrescribedCompletionNonzeroConsumer
