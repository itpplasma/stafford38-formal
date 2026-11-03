module

public import Stafford38.Characteristic.CanonicalKoszulContradiction

@[expose] public section

/-!
# The setup paragraph before Lemma 4.8 (tex 672–683)

`M = gr Q`, `f : M → M` the action of `x₁`, `V = ker f`, `U = coker f = M/x₁M`,
`T = k[x₂,…,xₙ,ξ₂,…,ξₙ]`, with `T[x₁,ξ₁] = k[x,ξ]`.

Lean indexes the coordinates from `0`, so paper `n` is Lean `n+1`, and
`T = MvPolynomial (Fin n ⊕ Fin n) k` (for paper `n = 1` this is `k`).  `T` acts
on `M` through `oldSymbolTangentialAlgEquiv : T ≃ k[x₂,…,ξₙ] ⊆ k[x,ξ]`, and `f`
is `oldCoordinateMap`, the `T`-linear action of the symbol `X (inl 0) = x₁`.
-/

namespace Stafford38.Paper.Section4

open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalGradedTangentialEquivalences
open Stafford38.Characteristic.CanonicalOldTangentialFiniteness
open Stafford38.WeylIteratedEquivalence

noncomputable section

variable (k : Type*) [Field k] (n N : ℕ) (d : PresentedWeyl k (n + 1))

/-- `M = gr Q`, the order-associated graded module of `Q = A_n/𝓘`. -/
abbrev GrQ := Graded k n N d

/-- `T = k[x₂,…,xₙ,ξ₂,…,ξₙ]`. -/
abbrev Tangential := T k n

/-- `k[x,ξ] = T[x₁,ξ₁]`, the symbol ring acting on `M`. -/
abbrev Symbol := SymbolRing k (n + 1)

/-- The symbol `x₁ ∈ k[x,ξ]`. -/
abbrev symbolCoordinate : Symbol k n := MvPolynomial.X (.inl (0 : Fin (n + 1)))

attribute [local instance] CanonicalKoszulContradiction.gradedModule
  CanonicalKoszulContradiction.coefficientAlgebra CanonicalKoszulContradiction.coefficientTower

/-- `f : M → M`, right multiplication by `x₁`, as a `T`-linear map. -/
abbrev coordinateMap : GrQ k n N d →ₗ[Tangential k n] GrQ k n N d :=
  oldCoordinateMap (k := k) n (GrQ k n N d)

/-- `V = ker f`. -/
abbrev kernelV := LinearMap.ker (coordinateMap k n N d)

/-- `U = coker f = M/x₁M`. -/
abbrev cokernelU := GrQ k n N d ⧸ LinearMap.range (coordinateMap k n N d)

/-- On `M = gr Q`, `f` is the action of the symbol `x₁`, i.e. right
multiplication by `x₁` on `gr Q`. -/
theorem setup_coordinateMap_apply (z : GrQ k n N d) :
    coordinateMap k n N d z = symbolCoordinate k n • z := rfl

/-- `f` is the restriction to `T` of the `k[x,ξ]`-linear multiplication by `x₁`. -/
theorem setup_coordinateMap_eq :
    (LinearMap.lsmul (Symbol k n) (GrQ k n N d) (symbolCoordinate k n)).restrictScalars
        (Tangential k n) = coordinateMap k n N d := rfl

#print axioms setup_coordinateMap_eq

end

end Stafford38.Paper.Section4
