module
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis

universe u v w

variable {k : Type u} [Field k]

/-- The standard variables are a transcendence basis in the fraction field of a polynomial ring
over any finite index type. `ULift` gives the indexing type the universe of the coefficient field,
as required by the cardinality API for transcendence degree. -/
theorem standardVariables_isTranscendenceBasis_of_fintype {σ : Type v} [Fintype σ] :
    IsTranscendenceBasis k
      (fun i : ULift.{u} σ =>
        algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))
          (MvPolynomial.X i.down)) := by
  let A := MvPolynomial σ k
  let E := FractionRing A
  have hAE : Algebra.IsAlgebraic A E :=
    (IsFractionRing.isAlgebraic_iff' A A E).mp inferInstance
  letI : Algebra.IsAlgebraic A E := hAE
  have hσ : IsTranscendenceBasis k
      (fun i : σ => algebraMap A E (MvPolynomial.X i)) := by
    exact (IsTranscendenceBasis.mvPolynomial σ k).algebraMap_comp
  apply (isTranscendenceBasis_equiv
    (Equiv.ulift.symm : σ ≃ ULift.{u} σ)).mp
  simpa [Function.comp_def] using hσ

/-- The canonical fraction field of a finite-variable polynomial algebra has the expected finite
transcendence degree. -/
theorem trdeg_eq_of_fintype {σ : Type v} [Fintype σ] :
    Algebra.trdeg k (FractionRing (MvPolynomial σ k)) = Fintype.card σ := by
  rw [← (standardVariables_isTranscendenceBasis_of_fintype (k := k) (σ := σ)).cardinalMk_eq_trdeg]
  simp

theorem trdeg_lt_aleph0_of_fintype {σ : Type v} [Fintype σ] :
    Algebra.trdeg k (FractionRing (MvPolynomial σ k)) < Cardinal.aleph0 := by
  rw [trdeg_eq_of_fintype (k := k) (σ := σ)]
  exact Cardinal.natCast_lt_aleph0

/-- If the images of the polynomial variables in a field extension form a transcendence basis,
then the fraction-field algebra they induce is the whole extension up to algebraic extension.
The algebra structure on the fraction field is the given one; the variable family is required to
be its actual image, so no extra range-identification hypothesis is hidden here. -/
theorem isAlgebraic_fractionRing_of_variable_images_isTranscendenceBasis
    {σ : Type v} {κ : Type w} [Field κ] [Algebra k κ]
    [Algebra (FractionRing (MvPolynomial σ k)) κ]
    [IsScalarTower k (FractionRing (MvPolynomial σ k)) κ]
    (hvars : IsTranscendenceBasis k
      (fun i : σ =>
        algebraMap (FractionRing (MvPolynomial σ k)) κ
          (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))
            (MvPolynomial.X i)))) :
    Algebra.IsAlgebraic (FractionRing (MvPolynomial σ k)) κ := by
  let A := MvPolynomial σ k
  let E := FractionRing A
  let x : σ → κ := fun i =>
    algebraMap E κ (algebraMap A E (MvPolynomial.X i))
  have hx : IsTranscendenceBasis k x := by
    simpa [x] using hvars
  let K : IntermediateField k κ := IntermediateField.adjoin k (Set.range x)
  let A₀ : Subalgebra k κ := Algebra.adjoin k (Set.range x)
  have hA₀κ : Algebra.IsAlgebraic A₀ κ := by
    simpa [A₀] using hx.isAlgebraic
  let e : E ≃ₐ[k] K := hx.1.aevalEquivField
  have hA₀K : A₀ ≤ K.toSubalgebra :=
    IntermediateField.algebra_adjoin_le_adjoin k (Set.range x)
  have hKκ : Algebra.IsAlgebraic K κ := by
    letI : Algebra A₀ K := (Subalgebra.inclusion hA₀K).toAlgebra
    letI : IsScalarTower A₀ K κ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact hA₀κ.extendScalars (Subalgebra.inclusion_injective hA₀K)
  have hpoly :
      (IsScalarTower.toAlgHom k E κ).comp (IsScalarTower.toAlgHom k A E) =
        MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [x, IsScalarTower.toAlgHom]
  letI : IsFractionRing A E := inferInstance
  have hforward :
      (algebraMap K κ).comp e.toRingEquiv.toRingHom = algebraMap E κ := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro p
    change ((e (algebraMap A E p) : K) : κ) = algebraMap E κ (algebraMap A E p)
    rw [hx.1.aevalEquivField_algebraMap_apply_coe]
    exact (DFunLike.congr_fun hpoly p).symm
  have hback :
      (algebraMap E κ).comp e.symm.toRingEquiv.toRingHom =
        (RingHom.id κ).comp (algebraMap K κ) := by
    ext z
    have hz := DFunLike.congr_fun hforward (e.symm z)
    simpa using hz.symm
  exact
    (Algebra.isAlgebraic_ringHom_iff_of_comp_eq
      e.symm.toRingEquiv (RingEquiv.refl κ) hback).mpr hKκ

/-- The legacy `Fin d` spelling is a specialization of the finite-index theorem. -/
theorem standardVariables_isTranscendenceBasis (d : ℕ) :
    IsTranscendenceBasis k
      (fun i : ULift.{u} (Fin d) =>
        algebraMap (MvPolynomial (Fin d) k)
          (FractionRing (MvPolynomial (Fin d) k)) (MvPolynomial.X i.down)) :=
  standardVariables_isTranscendenceBasis_of_fintype (k := k) (σ := Fin d)

theorem trdeg_eq (d : ℕ) :
    Algebra.trdeg k (FractionRing (MvPolynomial (Fin d) k)) = d := by
  simpa using (trdeg_eq_of_fintype (k := k) (σ := Fin d))

theorem trdeg_lt_aleph0 (d : ℕ) :
    Algebra.trdeg k (FractionRing (MvPolynomial (Fin d) k)) < Cardinal.aleph0 := by
  exact trdeg_lt_aleph0_of_fintype (k := k) (σ := Fin d)

end Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis
