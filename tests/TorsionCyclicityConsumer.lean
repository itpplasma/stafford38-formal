import CorollaryChallenge
import Stafford38.TorsionCyclicity

/-! An independent consumer checks the literal Mathlib-only corollary statement. -/

namespace Stafford38CorollaryChallenge

/-- The substantive right-module theorem proves the standalone corollary
statement in the independent `RingQuot` presentation. -/
theorem torsionCyclicStatement_consumer : torsionCyclicStatement := by
  intro k _ _ n M _ _ _ hM
  let e : WeylAlg k n ≃ₐ[k] Stafford38.WeylAlg k n := AlgEquiv.refl
  letI : Module (Stafford38.WeylAlg k n)ᵐᵒᵖ M :=
    Module.compHom M ((RingEquiv.op e.toRingEquiv).symm.toRingHom)
  letI : Module.Finite (Stafford38.WeylAlg k n)ᵐᵒᵖ M := by
    change Module.Finite (WeylAlg k n)ᵐᵒᵖ M
    infer_instance
  have hM' : Stafford38.TorsionCyclicity.IsRightTorsion
      (A := Stafford38.WeylAlg k n) (M := M) := hM
  exact Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion
    (k := k) (n := n) (M := M) hM'

#print axioms torsionCyclicStatement_consumer

end Stafford38CorollaryChallenge
