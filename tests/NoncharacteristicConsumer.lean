module
public import Stafford38.NoncharacteristicHyperplane

@[expose] public section

open Stafford38
open Stafford38.NoncharacteristicHyperplane
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylEulerResidue
open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Characteristic.CanonicalOldTangentialFiniteness
open Stafford38.WeylFiltration
open Stafford38.WeylPBW
open Stafford38.WeylPBWMonicBridge

private theorem rankOne_normal_momentum_isPBWMonic :
    IsPBWMonicAt ℚ (.inr (0 : Fin 1)) 1 (presentedMomentum ℚ 0) := by
  constructor
  · change presentedMomentum ℚ 0 ∈ bernsteinPiece ℚ 1 1
    simpa [presentedMomentum, Stafford38.WeylTransposition.momentum] using
      Stafford38.WeylTranspositionFiltration.momentum_mem_bernsteinPiece
        (k := ℚ) (n := 1) (0 : Fin 1)
  · simp [presentedMomentum, presentedNormalFormLinearEquiv_generator]

noncomputable def rankOneCanonicalCharacteristicIdeal : Ideal (SymbolRing ℚ 1) :=
  Module.annihilator (SymbolRing ℚ 1)
    (OrderAssociatedGradedModule ℚ
      (canonicalRightIdeal (presentedCoordinate ℚ 0)
        (presentedMomentum ℚ 0) 1))

/-- The literal restricted ring `R/(J+(x₀))` is finite over the coefficient
ring of `T*H`, for the rank-one normal-momentum example. -/
theorem rankOne_literal_restricted_coordinate_ring_finite :
    Module.Finite (oldTangentialCoeffRing (k := ℚ) 0)
      (SymbolRing ℚ 1 ⧸
        (rankOneCanonicalCharacteristicIdeal ⊔
          Ideal.span ({(MvPolynomial.X (.inl (0 : Fin 1)) : SymbolRing ℚ 1)} :
            Set (SymbolRing ℚ 1)))) := by
  change Module.Finite (oldTangentialCoeffRing (k := ℚ) 0)
    (SymbolRing ℚ 1 ⧸ restrictedCoordinateIdeal (k := ℚ) 0
      (Module.annihilator (SymbolRing ℚ 1)
        (OrderAssociatedGradedModule ℚ
          (canonicalRightIdeal (presentedCoordinate ℚ 0)
            (presentedMomentum ℚ 0) 1))))
  exact canonical_finite_restrictedCoordinateQuotient (k := ℚ) (n := 0)
    (N := 1) (d := presentedMomentum ℚ 0) rankOne_normal_momentum_isPBWMonic

/-- In one variable there are no tangential covariables, so the support theorem
forces the normal covariable to vanish at every support prime. -/
theorem rankOne_conormal_support_zero_momentum
    {p : PrimeSpectrum (SymbolRing ℚ 1)}
    (hp : p ∈ orderCharacteristicSupport ℚ
      (canonicalRightIdeal (presentedCoordinate ℚ 0)
        (presentedMomentum ℚ 0) 1)) :
    MvPolynomial.X (.inr (0 : Fin 1)) ∈ p.asIdeal := by
  apply canonicalSupport_conormal_subset_zeroSection
    (k := ℚ) (n := 0) (N := 1) (d := presentedMomentum ℚ 0)
      rankOne_normal_momentum_isPBWMonic hp
  intro i hi
  exact False.elim (hi (Fin.eq_zero i))

#print axioms rankOne_literal_restricted_coordinate_ring_finite
#print axioms rankOne_conormal_support_zero_momentum
