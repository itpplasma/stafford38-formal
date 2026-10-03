module
public import Stafford38.LinearAlgebra.SymplecticComplement

@[expose] public section

open LinearMap (BilinForm)
open Module

universe u v

example {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (B : BilinForm k V)
    (hAlt : ∀ x, B x x = 0) (hB : B.Nondegenerate)
    (v w : V) (hvw : B v w = 1) :
    (B.restrict (Stafford38.LinearAlgebra.SymplecticComplement.pairPlane v w)).Nondegenerate ∧
      IsCompl
        (Stafford38.LinearAlgebra.SymplecticComplement.pairPlane v w)
        (B.orthogonal
          (Stafford38.LinearAlgebra.SymplecticComplement.pairPlane v w)) ∧
      (B.restrict
        (B.orthogonal
          (Stafford38.LinearAlgebra.SymplecticComplement.pairPlane v w))).Nondegenerate ∧
      finrank k (B.orthogonal
        (Stafford38.LinearAlgebra.SymplecticComplement.pairPlane v w)) + 2 = finrank k V := by
  exact Stafford38.LinearAlgebra.SymplecticComplement.pairComplementData B hAlt hB v w hvw

#print axioms Stafford38.LinearAlgebra.SymplecticComplement.pairComplementData
