module
public import Stafford38.Characteristic.PaperSymplecticBasis
public import Stafford38.Characteristic.SymplecticCompletion
public import Stafford38.Weyl.PaperRightMonic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

open LinearMap (BilinForm)
open Stafford
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPaperRightMonic
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylPBW
open Stafford38.WeylUniversal
open Stafford38.Characteristic
open Stafford38.WeylFiltration
open Stafford38.OreIteratedPairStage
open Stafford38.OreCoordinateStage
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreRightPBW
open AlgebraicAnalysis.OreRightQuotient



abbrev Plane := Fin 2 → ℚ

def skewPlaneMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![0, 3; -3, 0]

def skewPlaneForm : BilinForm ℚ Plane := Matrix.toBilin' skewPlaneMatrix

def planeQ : Plane := Pi.single 0 1

def planeP : Plane := (1 / 3 : ℚ) • Pi.single 1 1

/-- A scaled, nonstandard alternating form: the prescribed dual partner must
be divided by 3, and the pairing order fixes the sign. -/
theorem paperBasis_literal_plane_oracle :
    ∃ b : Module.Basis (Fin 1 ⊕ Fin 1) ℚ Plane,
    b (Sum.inl 0) = planeQ ∧ b (Sum.inr 0) = planeP ∧
      skewPlaneForm (b (Sum.inl 0)) (b (Sum.inr 0)) = 1 ∧
      skewPlaneForm (b (Sum.inr 0)) (b (Sum.inl 0)) = -1 := by
  have hAlt : ∀ x : Plane, skewPlaneForm x x = 0 := by
    intro x
    simp [skewPlaneForm, skewPlaneMatrix, Matrix.toBilin'_apply, Fin.sum_univ_two]
    ring
  have hdet : skewPlaneMatrix.det ≠ 0 := by
    norm_num [skewPlaneMatrix, Matrix.det_fin_two]
  have hB : skewPlaneForm.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  have hdim : Module.finrank ℚ Plane = 2 * (0 + 1) := by
    rw [Module.finrank_eq_card_basis (Pi.basisFun ℚ (Fin 2))]
    norm_num
  have hp : skewPlaneForm planeQ planeP = 1 := by
    norm_num [skewPlaneForm, skewPlaneMatrix, planeQ, planeP,
      Matrix.toBilin'_apply, Fin.sum_univ_two]
  obtain ⟨b, _, _, _, hq, hP⟩ :=
    Stafford38.CharacteristicPaperSymplecticBasis.exists_symplectic_basis_with_pair
      0 skewPlaneForm hAlt hB hdim planeQ planeP hp
  refine ⟨b, hq, hP, ?_, ?_⟩
  · rw [hq, hP]
    exact hp
  · rw [hP, hq]
    norm_num [skewPlaneForm, skewPlaneMatrix, planeQ, planeP,
      Matrix.toBilin'_apply, Fin.sum_univ_two]

/-- The degree-one right-monic decomposition for `p + x` returns the literal
coordinate coefficient at degree zero. This checks the opposite-module
coefficient slot, rather than merely accepting the theorem's existential. -/
theorem rightMonic_degreeOne_literal_oracle :
    ∃ a : ℕ → CoordinateStage (B := IteratedPairStage ℚ 0),
    (∀ j, j < 1 → a j ∈ coordinateBernsteinPiece ℚ 0 (1 - j)) ∧
    a 0 = normalVariable (zeroDerivation : OreDivisionDerivation (IteratedPairStage ℚ 0)) ∧
    presentedToIterated ℚ 1 (presentedMomentum ℚ 0 + presentedCoordinate ℚ 0) =
      rightPBWMonomial (coordinateDerivation :
        OreDivisionDerivation (CoordinateStage (B := IteratedPairStage ℚ 0))) 1 +
      MulOpposite.op (normalVariable (zeroDerivation : OreDivisionDerivation (IteratedPairStage ℚ 0))) •
        rightPBWMonomial (coordinateDerivation :
          OreDivisionDerivation (CoordinateStage (B := IteratedPairStage ℚ 0))) 0 := by
  let x : CoordinateStage (B := IteratedPairStage ℚ 0) :=
    normalVariable (zeroDerivation : OreDivisionDerivation (IteratedPairStage ℚ 0))
  have genMem (i : PhaseVar 1) :
      freeWeylGenerator (Matrix.J (Fin 1) ℚ) i ∈ bernsteinPiece ℚ 1 1 := by
    have heq : freeWeylGenerator (Matrix.J (Fin 1) ℚ) i =
        presentedPBWBasis ℚ 1 (Finsupp.single i 1) := by
      apply (presentedNormalFormLinearEquiv ℚ 1).injective
      rw [presentedNormalFormLinearEquiv_generator,
        presentedNormalFormLinearEquiv_basis]
      rw [← MvPolynomial.X_pow_eq_monomial]
      rw [pow_one]
    rw [heq, bernsteinPiece]
    apply (presentedPBWBasis_mem_weightPiece_iff ℚ bernsteinWeight 1
      (Finsupp.single i 1)).2
    cases i <;> norm_num [monomialWeight, bernsteinWeight]
  have hp : presentedMomentum ℚ 0 ∈ bernsteinPiece ℚ 1 1 := by
    simpa [presentedMomentum] using genMem (.inr 0)
  have hx : presentedCoordinate ℚ 0 ∈ bernsteinPiece ℚ 1 1 := by
    simpa [presentedCoordinate] using genMem (.inl 0)
  have hpiece :
      presentedMomentum ℚ 0 + presentedCoordinate ℚ 0 ∈ bernsteinPiece ℚ 1 1 :=
    (bernsteinPiece ℚ 1 1).add_mem hp hx
  have hnf : presentedNormalFormLinearEquiv ℚ 1
      (presentedMomentum ℚ 0 + presentedCoordinate ℚ 0) =
        MvPolynomial.X (.inr (0 : Fin 1)) + MvPolynomial.X (.inl (0 : Fin 1)) := by
    simp [presentedMomentum, presentedCoordinate, presentedNormalFormLinearEquiv_generator]
  have hcoef : MvPolynomial.coeff (Finsupp.single (.inr (0 : Fin 1)) 1)
      (presentedNormalFormLinearEquiv ℚ 1
        (presentedMomentum ℚ 0 + presentedCoordinate ℚ 0)) = 1 := by
    rw [hnf]
    simp [MvPolynomial.coeff, MvPolynomial.coeff_X]
    intro h
    have hv := congrArg
      (fun f : (Fin 1 ⊕ Fin 1) →₀ ℕ => f (Sum.inr (0 : Fin 1))) h
    simp at hv
  have hmonic : IsPBWMonicAt ℚ (.inr (0 : Fin 1)) 1
      (presentedMomentum ℚ 0 + presentedCoordinate ℚ 0) := ⟨hpiece, hcoef⟩
  obtain ⟨a, ha, hdecomp⟩ :=
    presentedOuter_right_monic_decomposition ℚ 0 1
      (presentedMomentum ℚ 0 + presentedCoordinate ℚ 0) hmonic
  have hp1 : rightPBWMonomial (coordinateDerivation :
      OreDivisionDerivation (CoordinateStage (B := IteratedPairStage ℚ 0))) 1 =
      stageMomentum ℚ 0 := by
    change normalForm coordinateDerivation (Polynomial.X ^ 1) =
      normalVariable coordinateDerivation
    rw [pow_one]
    rfl
  have hp0 : rightPBWMonomial (coordinateDerivation :
      OreDivisionDerivation (CoordinateStage (B := IteratedPairStage ℚ 0))) 0 = 1 := by
    simp [rightPBWMonomial]
  have hxstage : stageCoordinate ℚ 0 = normalCoefficient coordinateDerivation x := by
    rfl
  have hknown : presentedToIterated ℚ 1
      (presentedMomentum ℚ 0 + presentedCoordinate ℚ 0) =
        rightPBWMonomial (coordinateDerivation :
          OreDivisionDerivation (CoordinateStage (B := IteratedPairStage ℚ 0))) 1 +
          MulOpposite.op x • rightPBWMonomial (coordinateDerivation :
            OreDivisionDerivation (CoordinateStage (B := IteratedPairStage ℚ 0))) 0 := by
    simp only [map_add, presentedToIterated_momentum, presentedToIterated_coordinate]
    rw [hp1]
    simp [hxstage, x]
    rfl
  have hlower : MulOpposite.op x • rightPBWMonomial (coordinateDerivation :
      OreDivisionDerivation (CoordinateStage (B := IteratedPairStage ℚ 0))) 0 =
      ∑ j ∈ Finset.range 1, MulOpposite.op (a j) • rightPBWMonomial
        (coordinateDerivation :
          OreDivisionDerivation (CoordinateStage (B := IteratedPairStage ℚ 0))) j := by
    exact add_left_cancel (hknown.symm.trans hdecomp)
  have hcoeff : normalCoefficient coordinateDerivation x =
      normalCoefficient coordinateDerivation (a 0) := by
    simpa [rightPBWMonomial_op_smul] using hlower
  have ha0 : x = a 0 := (normalCoefficient_injective coordinateDerivation) hcoeff
  refine ⟨a, ha, ?_, ?_⟩
  · simpa [x] using ha0.symm
  · exact hknown

#print axioms paperBasis_literal_plane_oracle
#print axioms rightMonic_degreeOne_literal_oracle
