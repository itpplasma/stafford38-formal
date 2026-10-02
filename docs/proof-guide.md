# Proof guide

The theorem concerns right ideals in a Weyl algebra. Multiplication order is preserved throughout: the target identity is 1 = d R + F d S, so 1 belongs to dA + FdA. The factors are not commuted.

## Main statement

For every field k of characteristic zero, rank n including n = 0, and nonzero d in the Weyl algebra A, there are F, R, S in A such that

```text
1 = d R + F d S.
```

For positive rank, the fixed-source result uses F = ell^N for a linear Weyl coordinate ell and N equal to the intrinsic Bernstein degree of d. The fixed-source comparison proves that this degree agrees with the formal filtration degree.

## Terminal theorem route

The verified terminal proof proceeds as follows.

1. The top Bernstein symbol of a non-scalar operator is a nonzero homogeneous polynomial on phase space. A direction where it is nonzero extends to a symplectic basis, and the associated Weyl automorphism makes the operator monic in one momentum coordinate. The monic degree is the Bernstein degree.
2. For normalized d and paired coordinate x, form the right quotient Q = A/(dA + x^N dA). The Euler-product identity, negative-weight divisibility, and right normal form show that right multiplication by x on Q is surjective.
3. A filtered two-term complex compares localized kernel and cokernel lengths at a minimal support prime. The monic symbol and surjectivity force the strict inequality that excludes the coordinate hyperplane from transposed order-characteristic support.
4. The radical of the associated-graded annihilator is Poisson involutive by a formal Gabber argument proved in the development.
5. Fibre conicality, Poisson stability, and asymptotic conormal geometry imply that nonempty support would meet the selected coordinate hyperplane. This contradicts support avoidance.
6. Scalar descent carries empty support back from an algebraic closure. The quotient becomes trivial, yielding the ordered certificate; the symplectic coordinate change is then undone. At rank zero, inversion in the field gives the result.

The declaration dependencies for this route are in proof-graph.yaml. The receipt in verification-results.json applies to source revision f6915782d2281e3d3b51011b97ace866928053b9.

## Manuscript correspondence

The paper-route review tracks the visible divisor, local-frame, and cyclicity arguments. The [paper-route map](paper-route-alignment.json) links printed claims to Lean statements, hypotheses, and constructions, and records where the proof routes differ. A shared terminal theorem alone does not establish full correspondence. The [definition-owner registry](definition-owners.md) describes the shared mathematical objects. Review inputs and responsibilities are in [proof-source provenance](proof-source-provenance.md).

## Other formalized results

Right Ore localization, formal adjoints, differential operators on polynomial localizations, evolutionary identities, and torsion-module cyclicity are formalized as related results. Their hypotheses and dependencies remain attached to their declarations; they are not additional steps in the terminal route above.
