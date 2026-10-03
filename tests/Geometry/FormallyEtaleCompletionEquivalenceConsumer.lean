module
public import Stafford38.Geometry.FormallyEtaleCompletionEquivalence

@[expose] public section

open Polynomial

namespace Stafford38.Geometry.FormallyEtaleCompletionEquivalenceConsumer

noncomputable section

abbrev R := Polynomial ℚ
abbrev I : Ideal R := Ideal.span {(X : R)}

example : Algebra.FormallyUnramified R R := by infer_instance

example : Algebra R (AdicCompletion I R) := by infer_instance

def identityCompletionEquiv : AdicCompletion I R ≃+* AdicCompletion I R := by
  let hJ : I = I.map (algebraMap R R) := by simp
  let ψ : R →ₐ[R] AdicCompletion I R := IsScalarTower.toAlgHom R R _
  have hres :
      (Stafford38.Geometry.FormallyEtaleCompletionEquivalence.forwardStage
        I I hJ 1).comp
      (Stafford38.Geometry.FormallyEtaleCompletionEquivalence.reverseStage
            I I hJ ψ 1) = AlgHom.id R (R ⧸ I ^ 1) := by
    apply Ideal.Quotient.algHom_ext R
    ext
  exact Stafford38.Geometry.FormallyEtaleCompletionEquivalence.formalEtaleCompletionEquiv
    I I hJ ψ hres

-- Behavioral oracle: the induced equivalence fixes the actual completed coordinate.
example : identityCompletionEquiv (AdicCompletion.of I R X) = AdicCompletion.of I R X := by
  simp [identityCompletionEquiv,
    Stafford38.Geometry.FormallyEtaleCompletionEquivalence.formalEtaleCompletionEquiv,
    Stafford38.Geometry.FormallyEtaleCompletionEquivalence.forwardCompletionMap]

#print axioms identityCompletionEquiv

end
end Stafford38.Geometry.FormallyEtaleCompletionEquivalenceConsumer
