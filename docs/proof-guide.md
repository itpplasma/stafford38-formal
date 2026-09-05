# Proof guide

The theorem concerns right ideals in a Weyl algebra. Throughout the formal
development, products retain their written order. In particular, the target

```text
1 = d R + F d S
```

means that `1` belongs to the right ideal `dA + FdA`; no commutation of `d`,
`F`, `R`, or `S` is used.

## Statement and Weyl presentation

[`Stafford38.WeylAlg`](../Stafford38/Statement.lean) is the quotient of the
free algebra on `Fin n ⊕ Fin n` by the standard symplectic commutator
relations encoded by `Matrix.J`. The two summands are the coordinate and
momentum generators. The sign convention is fixed by the presentation rather
than imported from informal differential-operator notation.

[`Stafford38.UniversalStatement`](../Stafford38/Statement.lean) states

```lean
∀ (k : Type*) [Field k] [CharZero k] (n : ℕ) (d : WeylAlg k n),
  d ≠ 0 → ∃ F R S : WeylAlg k n, 1 = d * R + F * d * S
```

Thus the coefficient field is arbitrary of characteristic zero and `n = 0`
is included. The rank-zero Weyl algebra is the field, so its branch follows
from inversion of the nonzero scalar.

## Symplectic monic reduction

For positive rank, the top Bernstein part of a non-scalar `d` is a nonzero
homogeneous polynomial on phase space. A vector at which it does not vanish is
completed to a symplectic basis. The resulting Weyl automorphism makes `d`
monic in one momentum coordinate.

The main reduction is
[`Stafford38.WeylMonicNormalization.scalar_or_normalized_symplectic_image`](../Stafford38/Weyl/MonicNormalization.lean).
The PBW bridge records that the monic degree is the Bernstein degree of `d`.
This equality supplies the exponent in the stronger fixed-source theorem.

## Canonical quotient and Euler residue

After normalization, write the distinguished Weyl pair as `x,p` and the monic
degree as `N`. The canonical right ideal is

```text
I = dA + xᴺ dA,
```

and the corresponding right quotient is `Q = A/I`.

[`Stafford38.WeylEulerResidue.positiveEulerResidue_identity`](../Stafford38/Weyl/EulerResidue.lean)
constructs the positive Euler-product identity with its exact factor order.
Together with the negative-weight divisibility calculation and the right
normal form for the outer Ore variable, it yields
[`Stafford38.WeylEulerRemainder.presentedCanonicalQuotient_rightMul_coordinate_surjective`](../Stafford38/Weyl/EulerRemainder.lean):
right multiplication by `x` on `Q` is surjective.

## Filtered noncharacteristic argument

The order filtration on `Q` produces a two-term filtered complex for right
multiplication by `x`. At a minimal prime of the relevant support, one
calculation bounds the localized kernel length by the cokernel length. A
second calculation, using the surjectivity above and the monic symbol, gives
the strict inequality in the opposite direction.

The contradiction is assembled in
[`Stafford38.Characteristic.CanonicalKoszulContradiction.canonical_support_avoidance`](../Stafford38/Characteristic/CanonicalKoszulContradiction.lean).
Its conclusion says that the transposed order-characteristic support of the
canonical quotient is disjoint from the coordinate hyperplane. This is the
precise Lean form consumed later; the proof does not assume a general
noncharacteristic inverse-image theorem.

## Involutivity of the reduced support

The associated-graded annihilator of a cyclic Weyl quotient lies in the
commutative symbol ring. The formal Gabber block proves that its radical is
closed under the Poisson bracket:

[`Stafford38.Characteristic.GabberGlobalAssembly.weylAssociatedGradedRadicalInvolutivity`](../Stafford38/Characteristic/GabberGlobalAssembly.lean).

This declaration is field-generic and is proved from Lean and Mathlib. In the
terminal proof it is applied to the canonical right ideal; no citation-shaped
axiom remains in the theorem's dependency graph.

## Tangent limits and asymptotic conormals

The geometric block studies an irreducible affine variety avoiding a
coordinate hyperplane. Its normalized projective closure has a boundary
divisor at which the selected coordinate has a strict order gap. A formal arc
through that divisor supplies a lattice of projective tangent columns.

[`Stafford38.Geometry.GeneralTangentLimitCriterion.tangent_limit_criterion_of_directSummand`](../Stafford38/Geometry/GeneralTangentLimitCriterion.lean)
turns a direct-summand tangent lattice whose reduction lies in the selected
coordinate hyperplane into the corresponding projective conormal direction.
The statement includes the formal arc, generic smoothness, lattice splitting,
dehomogenization, and closure data used in the argument.

The global result is
[`Stafford38.Geometry.GeneralAsymptoticConormal.coordinate_axis_mem_projective_conormal_directions`](../Stafford38/Geometry/GeneralAsymptoticConormal.lean).
It places the coordinate covector in the projective closure of smooth
conormal directions. Base points may tend to infinity; the argument does not
claim that a finite affine conormal fibre already contains this direction.

## Coisotropic exclusion

Let `W` be a nonempty closed fibre-conical subset of phase space whose
vanishing ideal is stable under the required Poisson brackets. Fibre
conicality supplies its zero section over the base projection. Poisson
stability supplies the conormal translations along each irreducible base
component. The asymptotic conormal theorem then forces a point of `W` over the
selected coordinate hyperplane whenever a fibre-only homogeneous equation is
nonzero at the matching momentum axis.

This conclusion is
[`Stafford38.Geometry.GeneralCoisotropicSets.exists_zero_base_coordinate_of_isFibreConical`](../Stafford38/Geometry/GeneralCoisotropicSets.lean).
The canonical adapter applies it to the zero locus of the radical order-support
ideal. Homogeneity gives fibre-conicality, and the involutivity theorem gives
Poisson stability. The resulting endpoint is
[`algebraicallyClosedCanonicalSupportVanishing_of_generalCoisotropic`](../Stafford38/Geometry/GeneralCoisotropicCanonicalAdapter.lean).

## Descent and certificate extraction

The geometric argument is first made after extension to an algebraic closure.
[`Stafford38.Weyl.FilteredScalarLifting.canonicalSupportDescent`](../Stafford38/Weyl/FilteredScalarLifting.lean)
descends empty canonical support to the original characteristic-zero field.

Empty order-characteristic support makes the canonical quotient trivial.
[`exists_fixedSource_certificate_of_orderCharacteristicSupport_eq_empty`](../Stafford38/Characteristic/CanonicalCertificate.lean)
therefore extracts the literal identity with `F = xᴺ`. The universal assembly
undoes the symplectic coordinate change and preserves multiplication order:
[`universalStatement_of_canonicalSupportVanishing`](../Stafford38/UniversalAssembly.lean).

[`FoundationClosure.lean`](../Stafford38/FoundationClosure.lean) supplies the
canonical support-vanishing input and exports both final theorems:

- `Stafford38.universalStatement` gives an unrestricted witness `F` for every
  rank;
- `Stafford38.universalFixedSourceStatement` records the linear coordinate and
  exact Bernstein-degree exponent in the positive-rank branch.

## Corollaries

[`Stafford38.LocalizationCorollaries.s38_rightOreLocalization`](../Stafford38/LocalizationCorollaries.lean)
clears a right Ore denominator without changing cofactor order.
[`Stafford38.LeftHandedCorollary.leftHanded_of_universalStatement`](../Stafford38/LeftHandedCorollary.lean)
uses the formal adjoint to obtain `1 = R d + S d F`.

[`Stafford38.LocalizedDifferentialCorollaries.s38_unconditional_localized_differential`](../Stafford38/LocalizedDifferentialCorollaries.lean)
applies the theorem to intrinsic finite-order differential operators on
polynomial localizations. Its concrete consumers cover principal opens,
partial Laurent localizations, and fraction fields under their stated
localization hypotheses.

The evolution result is logically independent of the geometric Stafford
proof. [`Stafford38.Evolution.evolutionaryCorollary`](../Stafford38/EvolutionaryCorollary.lean)
and [`Stafford38.Evolution.tensorEvolutionaryCorollary`](../Stafford38/EvolutionaryCorollary.lean)
give the corresponding certificate for an abstract Weyl pair and for a tensor
product with the first Weyl algebra.

## Formal and manuscript statements

The separate manuscript expresses characteristic support and conormal geometry
in conventional geometric notation. Lean uses prime spectra, polynomial zero
loci, homogeneous ideals, and explicit projective closure predicates. The
release correspondence audit must match these formulations theorem by theorem.
The signed private source checkpoint contains the declarations above and has
passed the full 229-checker manuscript replay. Both formalization phase-open
lists are empty, and the independent tangent-limit review returned `PASS`.
Only the clean-repository extraction and its fresh reproducibility run remain
to be recorded after cutover.
