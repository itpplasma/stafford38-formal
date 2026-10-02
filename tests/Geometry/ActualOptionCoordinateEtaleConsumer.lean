import Stafford38.Geometry.ActualOptionCoordinateEtale

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualOptionCoordinateEtaleConsumer

open Polynomial

abbrev k := ℚ
abbrev σ := Fin 1
abbrev A := MvPolynomial σ k
abbrev E := FractionRing A
abbrev S := Polynomial E
abbrev P := Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E
abbrev T := Localization.AtPrime P
abbrev B := MvPolynomial (Option σ) k

private def actualChartMap : B →ₐ[k] T :=
  (IsScalarTower.toAlgHom k S T).comp
    (Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap
      (k := k) (E := E) (σ := σ))

private def actualCoordinate (i : Option σ) : B := MvPolynomial.X i

private def actualMap : B →ₐ[k] T :=
  MvPolynomial.aeval (fun i => actualChartMap (actualCoordinate i))

theorem actual_map_formallyEtale :
    let f : B →ₐ[k] T := MvPolynomial.aeval (fun i => actualChartMap (actualCoordinate i))
    letI : Algebra B T := f.toRingHom.toAlgebra
    Algebra.FormallyEtale B T := by
  letI : Algebra A E := inferInstance
  letI : Algebra k E := inferInstance
  letI : IsScalarTower k A E := inferInstance
  letI : IsLocalization (nonZeroDivisors A) E := inferInstance
  letI : Algebra E S := inferInstance
  letI : Algebra S T := inferInstance
  letI : Algebra k T := inferInstance
  letI : IsScalarTower k S T := inferInstance
  letI : Algebra.FiniteType E S := inferInstance
  letI : P.IsPrime :=
    Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime_isPrime E
  letI : P.IsMaximal := by
    change (Ideal.span {(Polynomial.X : Polynomial E)}).IsMaximal
    exact PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  have hparam : P.map (algebraMap S T) = IsLocalRing.maximalIdeal T :=
    IsLocalization.AtPrime.map_eq_maximalIdeal (R := S) (p := P) (Rₚ := T)
  have hsep : Algebra.IsSeparable E P.ResidueField :=
    Stafford38.Geometry.DVRParameterSmoothness.residueField_isSeparable_of_maximal_finiteType P
  let ρ : B →ₐ[k] T := actualChartMap
  let q : Option σ → B := actualCoordinate
  let e : T ≃ₐ[S] T := (AlgEquiv.refl : T ≃ₐ[S] T)
  have hnone : e (algebraMap S T (Polynomial.X : S)) = ρ (q none) := by
    simp [e, ρ, q, actualChartMap, actualCoordinate,
      Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap_X_none]
  have hsome : ∀ i : σ,
      e (algebraMap S T
        (Polynomial.C (algebraMap A E (MvPolynomial.X i)))) = ρ (q (some i)) := by
    intro i
    simp [e, ρ, q, actualChartMap, actualCoordinate,
      Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap_X_some]
  simpa [ρ, q, actualCoordinate] using
    Stafford38.Geometry.ActualOptionCoordinateEtale.formallyEtale_of_uniformizer_model
      (k := k) (σ := σ) (E := E) (S := S) (p := P)
      Polynomial.X_ne_zero hparam hsep (T := T) (B := B)
      (ρ := ρ) (q := q) e hnone hsome

/-- A mixed-coordinate oracle: the divisor coordinate stays polynomial, while
the selected coefficient coordinate is constant in it. -/
theorem mixed_coordinate_behavior :
    actualMap
        (MvPolynomial.X none * MvPolynomial.X (some (0 : σ)) + MvPolynomial.C (3 : k)) =
      algebraMap S T
        (Polynomial.X * Polynomial.C (algebraMap A E (MvPolynomial.X (0 : σ))) +
          Polynomial.C (algebraMap k E (3 : k))) := by
  simp [actualMap, actualChartMap, actualCoordinate,
    Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap]
  have hC : (Polynomial.C (3 : E) : S) = algebraMap k S (3 : k) := by
    simp
  have hconst : algebraMap k T (3 : k) =
      algebraMap S T (Polynomial.C (3 : E)) := by
    rw [hC]
    exact (IsScalarTower.algebraMap_apply k S T (3 : k)).symm
  rw [mul_comm, hconst]

#print axioms actual_map_formallyEtale
#print axioms mixed_coordinate_behavior

end Stafford38.Geometry.ActualOptionCoordinateEtaleConsumer
