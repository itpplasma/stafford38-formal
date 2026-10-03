module
public import Mathlib.RingTheory.Ideal.Over

@[expose] public section

set_option autoImplicit false

/-!
# Contraction of the localized residue kernel

The normalization-center calculation is made before coefficient
localization.  Once the residue map of the localization is known to restrict
to the retained residue map on the normalization, this file identifies the
contracted kernel without adding any geometric assumptions.
-/

namespace Stafford38.Geometry.ActualChartCenterContraction

universe u v w

/-- Contracting the kernel of a map on an algebra is the kernel of its
restriction to the original algebra. -/
theorem under_ker_eq_ker_comp
    {B : Type u} {A : Type v} {K : Type w}
    [CommSemiring B] [CommSemiring A] [CommSemiring K] [Algebra B A]
    (ρ : A →+* K) :
    Ideal.under B (RingHom.ker ρ) =
      RingHom.ker (ρ.comp (algebraMap B A)) := by
  ext b
  simp [Ideal.under_def]

/-- If a localized residue map extends the retained residue map, its kernel
contracts to the original retained-residue kernel. -/
theorem under_ker_eq_ker_of_restriction
    {B : Type u} {A : Type v} {K : Type w}
    [CommSemiring B] [CommSemiring A] [CommSemiring K] [Algebra B A]
    (ρA : A →+* K) (ρB : B →+* K)
    (hρ : ρA.comp (algebraMap B A) = ρB) :
    Ideal.under B (RingHom.ker ρA) = RingHom.ker ρB := by
  rw [under_ker_eq_ker_comp, hρ]

#print axioms under_ker_eq_ker_comp
#print axioms under_ker_eq_ker_of_restriction

end Stafford38.Geometry.ActualChartCenterContraction
