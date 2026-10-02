import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Algebraic.Basic

noncomputable section
set_option autoImplicit false

open scoped TensorProduct

namespace Stafford38.Geometry.ResidueBasisLocalization

/-- Inverting a coefficient domain inside a finite-type algebra is a base change to its
fraction field, hence remains finite type over that field. -/
theorem finiteType_fractionField_localization
    {k R A : Type*} [Field k] [CommRing R] [IsDomain R] [CommRing A]
    [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
    [Algebra.FiniteType k A] :
    Algebra.FiniteType (FractionRing R)
      (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) := by
  letI : Algebra.FiniteType R A :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := k) (S := R) (A := A)
  let e : (FractionRing R ⊗[R] A) ≃ₐ[FractionRing R]
      Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) :=
    Localization.tensorRightAlgEquiv (nonZeroDivisors R) A
  exact Algebra.FiniteType.equiv
    (inferInstance : Algebra.FiniteType (FractionRing R) (FractionRing R ⊗[R] A)) e

/-- The localized coefficient field remains embedded when the original coefficient domain
embeds in the finite-type domain. -/
theorem fractionField_localization_isDomain
    {k R A : Type*} [Field k] [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
    (hinj : Function.Injective (algebraMap R A)) :
    IsDomain (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) := by
  have hM : Algebra.algebraMapSubmonoid A (nonZeroDivisors R) ≤ nonZeroDivisors A := by
    change (nonZeroDivisors R).map (algebraMap R A) ≤ nonZeroDivisors A
    rw [Submonoid.map_le_iff_le_comap]
    intro r hr
    apply mem_nonZeroDivisors_of_ne_zero
    intro hzero
    apply (mem_nonZeroDivisors_iff_ne_zero.mp hr)
    exact hinj (by simpa using hzero)
  exact IsLocalization.isDomain_of_le_nonZeroDivisors
    (R := A) (S := Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) hM

/-- A prime ideal which is the kernel of a map to a field algebraic over the ground field is
maximal. This is the center-maximality step after the residue transcendence basis is inverted. -/
theorem ker_isMaximal_of_algebraic_residue
    {E A K : Type*} [Field E] [CommRing A] [Field K]
    [Algebra E A] [Algebra E K] [Algebra.IsAlgebraic E K]
    (f : A →ₐ[E] K) : (RingHom.ker (f : A →+* K)).IsMaximal := by
  let p : Ideal A := RingHom.ker (f : A →+* K)
  have hzero : ∀ a : A, a ∈ p → f a = 0 := fun _ ha => RingHom.mem_ker.mp ha
  let g : (A ⧸ p) →ₐ[E] K := Ideal.Quotient.liftₐ p f hzero
  have hginj : Function.Injective (g : (A ⧸ p) →+* K) := by
    apply RingHom.lift_injective_of_ker_le_ideal p hzero
    exact le_rfl
  let e : (A ⧸ p) ≃ₐ[E] g.range := AlgEquiv.ofInjective g hginj
  have hrange : IsField g.range := Subalgebra.isField_of_algebraic (A := g.range)
  exact Ideal.Quotient.maximal_of_isField p (e.toMulEquiv.isField hrange)

#print axioms finiteType_fractionField_localization
#print axioms fractionField_localization_isDomain
#print axioms ker_isMaximal_of_algebraic_residue

end Stafford38.Geometry.ResidueBasisLocalization
