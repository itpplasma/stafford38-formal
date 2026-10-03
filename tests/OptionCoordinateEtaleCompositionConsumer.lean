module
public import Stafford38.Geometry.OptionCoordinateEtaleComposition

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.OptionCoordinateEtaleCompositionConsumer

open IsLocalRing

abbrev k := ℚ
abbrev Selected := {i : Fin 4 // i.val ≠ 0}
abbrev A := MvPolynomial Selected k
abbrev E := FractionRing A
abbrev Rsrc := MvPolynomial (Option Selected) k
abbrev P := Polynomial E
abbrev p := Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E
abbrev T := Localization.AtPrime p

private def polynomialEvalValues : Option Selected → Polynomial k := fun i =>
  match i with
  | none => Polynomial.X
  | some _ => 0

private def polynomialEvalMap : Rsrc →ₐ[k] Polynomial k :=
  MvPolynomial.aeval polynomialEvalValues

local instance : Algebra Rsrc (Polynomial k) := polynomialEvalMap.toRingHom.toAlgebra

local instance : IsScalarTower k Rsrc (Polynomial k) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro a
  change algebraMap k (Polynomial k) a = polynomialEvalMap (algebraMap k Rsrc a)
  exact (polynomialEvalMap.commutes' a).symm

/-- A literal non-identity coordinate map checks finite presentation over the
finite-variable polynomial source. -/
theorem polynomial_target_finitePresentation :
    Algebra.FinitePresentation Rsrc (Polynomial k) := by
  exact OptionCoordinateEtaleComposition.finitePresentation_of_finiteType_target
    (k := k) (σ := Selected) (B := Polynomial k) inferInstance

section LocalChart

local instance : Algebra P T := inferInstance
local instance : Algebra k P := inferInstance
local instance : Algebra k T :=
  ((algebraMap P T).comp (algebraMap k P)).toAlgebra
local instance : SMul P T := (inferInstance : Algebra P T).toSMul
local instance : SMul k T := (inferInstance : Algebra k T).toSMul
local instance : IsScalarTower k P T := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro a
  rfl

private def localChartValues : Option Selected → T := fun j =>
  match j with
  | none => algebraMap P T (Polynomial.X : P)
  | some i => algebraMap P T
      (Polynomial.C (algebraMap A E (MvPolynomial.X i)))

private def localChartMap : Rsrc →ₐ[k] T := MvPolynomial.aeval localChartValues

local instance : Algebra Rsrc T := localChartMap.toRingHom.toAlgebra

/-- In the local polynomial model, the root uniformizer theorem supplies the
second stage, and the actual option-chart map has the required generator images. -/
theorem selected_local_chart_formallyEtale :
    Algebra.FormallyEtale Rsrc T := by
  have hnone : localChartMap (MvPolynomial.X none) =
      algebraMap P T (Polynomial.X : P) := by
    simp [localChartMap, localChartValues]
  have hsome (i : Selected) : localChartMap (MvPolynomial.X (some i)) =
      algebraMap P T (Polynomial.C (algebraMap A E (MvPolynomial.X i))) := by
    simp [localChartMap, localChartValues]
  have hX0 : algebraMap P P Polynomial.X ≠ 0 := by
    change (Polynomial.X : P) ≠ 0
    exact Polynomial.X_ne_zero
  have hparam : (p).map (algebraMap P T) = maximalIdeal T := by
    exact IsLocalization.AtPrime.map_eq_maximalIdeal p T
  have hpmax : (p).IsMaximal := by
    change (Ideal.span {(Polynomial.X : P)}).IsMaximal
    exact PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  letI : (p).IsMaximal := hpmax
  have hsepE : Algebra.IsSeparable E (p).ResidueField :=
    DVRParameterSmoothness.residueField_isSeparable_of_maximal_finiteType p
  have hsecond : Algebra.FormallyEtale P T :=
    DVRParameterSmoothness.formallyEtale_localization_of_polynomial_uniformizer
      (E := E) (S := P) p hX0 hparam hsepE
  exact OptionCoordinateEtaleComposition.formallyEtale_of_optionCoordinate_generator_images
    (k := k) (σ := Selected) (E := E) localChartMap hnone hsome hsecond

end LocalChart

#print axioms polynomial_target_finitePresentation
#print axioms selected_local_chart_formallyEtale
#print axioms OptionCoordinateEtaleComposition.formallyEtale_of_optionCoordinate_generator_images
#print axioms OptionCoordinateEtaleComposition.finitePresentation_of_finiteType_target

end Stafford38.Geometry.OptionCoordinateEtaleCompositionConsumer
