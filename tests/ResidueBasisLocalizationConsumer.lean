import Stafford38.Geometry.ResidueBasisLocalization

noncomputable section
set_option autoImplicit false

open Stafford38.Geometry.ResidueBasisLocalization

example (k : Type*) [Field k] :
    Algebra.FiniteType (FractionRing (Polynomial k))
      (Localization
        (Algebra.algebraMapSubmonoid (Polynomial k)
          (nonZeroDivisors (Polynomial k)))) :=
  finiteType_fractionField_localization (k := k) (R := Polynomial k) (A := Polynomial k)

example (k : Type*) [Field k] :
    IsDomain (Localization
      (Algebra.algebraMapSubmonoid (Polynomial k)
        (nonZeroDivisors (Polynomial k)))) :=
  fractionField_localization_isDomain (k := k) (R := Polynomial k) (A := Polynomial k)
    (fun _ _ h => h)

example (k : Type*) [Field k] :
    (RingHom.ker ((AlgHom.id k k : k →ₐ[k] k) : k →+* k)).IsMaximal := by
  letI : Algebra.IsAlgebraic k k :=
    ⟨fun x => isAlgebraic_algebraMap x⟩
  exact ker_isMaximal_of_algebraic_residue (AlgHom.id k k)

#print axioms Stafford38.Geometry.ResidueBasisLocalization.finiteType_fractionField_localization
#print axioms Stafford38.Geometry.ResidueBasisLocalization.fractionField_localization_isDomain
#print axioms Stafford38.Geometry.ResidueBasisLocalization.ker_isMaximal_of_algebraic_residue

/-- The evaluation kernel at 2 is maximal, and the independent polynomial
calculation identifies a nonzero element in it while excluding 1. -/
theorem rational_evaluation_kernel :
    (RingHom.ker ((Polynomial.aeval (2 : ℚ) : Polynomial ℚ →ₐ[ℚ] ℚ))).IsMaximal ∧
    Polynomial.X - Polynomial.C (2 : ℚ) ∈
      RingHom.ker ((Polynomial.aeval (2 : ℚ) : Polynomial ℚ →ₐ[ℚ] ℚ)) ∧
    (1 : Polynomial ℚ) ∉ RingHom.ker ((Polynomial.aeval (2 : ℚ) : Polynomial ℚ →ₐ[ℚ] ℚ)) := by
  letI : Algebra.IsAlgebraic ℚ ℚ := ⟨fun x => isAlgebraic_algebraMap x⟩
  refine ⟨ker_isMaximal_of_algebraic_residue (E := ℚ) ((Polynomial.aeval (2 : ℚ) : Polynomial ℚ →ₐ[ℚ] ℚ)), ?_, ?_⟩
  · simp [RingHom.mem_ker]
  · simp [RingHom.mem_ker]


#print axioms rational_evaluation_kernel
