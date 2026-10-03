module
public import Stafford38.Geometry.ProjectiveCoefficientLocalization
public import Stafford38.Geometry.DVRParameterSmoothness

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.OptionCoordinateEtaleComposition

open IsLocalRing

universe u v w x

/-- If an actual coordinate map sends the distinguished variable to the
polynomial parameter and each selected coordinate to its coefficient-field
image, it is exactly the composition through the coefficient localization.
Consequently it is formally etale whenever the second map is. -/
theorem formallyEtale_of_optionCoordinate_generator_images
    {k : Type u} [CommRing k] {σ : Type w} {E : Type v} [CommRing E]
    {T : Type x} [CommRing T]
    [Algebra (MvPolynomial σ k) E] [Algebra k E]
    [IsScalarTower k (MvPolynomial σ k) E]
    [IsLocalization (nonZeroDivisors (MvPolynomial σ k)) E]
    [Algebra k T] [Algebra (Polynomial E) T]
    [IsScalarTower k (Polynomial E) T]
    (f : MvPolynomial (Option σ) k →ₐ[k] T)
    (hnone : f (MvPolynomial.X none) =
      algebraMap (Polynomial E) T (Polynomial.X : Polynomial E))
    (hsome : ∀ i : σ, f (MvPolynomial.X (some i)) =
      algebraMap (Polynomial E) T
        (Polynomial.C (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i))))
    (hsecond : Algebra.FormallyEtale (Polynomial E) T) :
    letI : Algebra (MvPolynomial (Option σ) k) T := f.toRingHom.toAlgebra
    Algebra.FormallyEtale (MvPolynomial (Option σ) k) T := by
  let optionMap := Stafford38.Geometry.ProjectiveCoefficientLocalization.optionCoordinateMap
    (k := k) (E := E) (σ := σ)
  letI : Algebra (MvPolynomial (Option σ) k) (Polynomial E) :=
    optionMap.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Option σ) k) T := f.toRingHom.toAlgebra
  have hfactor : f = (IsScalarTower.toAlgHom k (Polynomial E) T).comp optionMap := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
        simpa [optionMap, ProjectiveCoefficientLocalization.optionCoordinateMap_X_none]
          using hnone
    | some j =>
        simpa [optionMap, ProjectiveCoefficientLocalization.optionCoordinateMap_X_some]
          using hsome j
  have hscalarMap :
      algebraMap (MvPolynomial (Option σ) k) T =
        (algebraMap (Polynomial E) T).comp
          (algebraMap (MvPolynomial (Option σ) k) (Polynomial E)) := by
    apply RingHom.ext
    intro r
    change f r = algebraMap (Polynomial E) T (optionMap r)
    have hr := congrArg (fun g : MvPolynomial (Option σ) k →ₐ[k] T => g r) hfactor
    simpa [IsScalarTower.toAlgHom_apply] using hr
  letI : IsScalarTower (MvPolynomial (Option σ) k) (Polynomial E) T :=
    IsScalarTower.of_algebraMap_eq' hscalarMap
  have hfirst : Algebra.FormallyEtale (MvPolynomial (Option σ) k) (Polynomial E) := by
    exact ProjectiveCoefficientLocalization.optionCoordinateMap_formallyEtale
      (k := k) (E := E) (σ := σ)
  exact Algebra.FormallyEtale.comp (MvPolynomial (Option σ) k) (Polynomial E) T

/-- If the target is finite type over the coefficient ring and the coordinate
map extends its coefficient algebra structure, then it is finitely presented
over the finite-variable polynomial source. This uses Noetherianity of that
source and does not require formal-etaleness. -/
theorem finitePresentation_of_finiteType_target
    {k : Type u} [CommRing k] [IsNoetherianRing k]
    {σ : Type w} [Fintype σ] {B : Type x} [CommRing B]
    [Algebra k B] [Algebra (MvPolynomial (Option σ) k) B]
    [IsScalarTower k (MvPolynomial (Option σ) k) B]
    (hB : Algebra.FiniteType k B) :
    Algebra.FinitePresentation (MvPolynomial (Option σ) k) B := by
  letI : Algebra.FiniteType k B := hB
  letI : Algebra.FiniteType (MvPolynomial (Option σ) k) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType k
      (MvPolynomial (Option σ) k) B
  exact (Algebra.FinitePresentation.of_finiteType (R := MvPolynomial (Option σ) k)
    (A := B)).mp inferInstance

end Stafford38.Geometry.OptionCoordinateEtaleComposition
