"""Exact finite-field oracle for filtered two-term page indices.

Enumerate every filtration-preserving endomorphism of the three-dimensional
standard flag over F_2. Compute subquotient dimensions from sets, independently
of Lean's quotient maps. This tests examples, not the universal theorem.
"""
from itertools import product


def dim(space):
    assert len(space) & (len(space) - 1) == 0
    return len(space).bit_length() - 1


def flag(p):
    return {x for x in range(8) if x % (1 << max(0, min(3, p))) == 0}


def plus(a, b):
    return {x ^ y for x in a for y in b}


checked = 0
for columns in product(flag(0), flag(1), flag(2)):
    def f(x):
        y = 0
        for i in range(3):
            if x & (1 << i):
                y ^= columns[i]
        return y

    def cycles(r, p):
        return {x for x in flag(p) if f(x) in flag(p + r)}

    def boundaries(r, p):
        return plus(flag(p) & {f(x) for x in flag(p - r + 1)}, flag(p + 1))

    def source_dim(r, p):
        z = cycles(r, p)
        return dim(z) - dim(z & flag(p + 1))

    def target_dim(r, p):
        return dim(flag(p)) - dim(boundaries(r, p))

    for r in range(1, 5):
        for p in range(-3, 4):
            q = p + r
            image = {f(x) for x in cycles(r, p)}
            boundary = boundaries(r, q)
            rank = dim(plus(image, boundary)) - dim(boundary)
            assert source_dim(r + 1, p) == source_dim(r, p) - rank
            assert target_dim(r + 1, q) == target_dim(r, q) - rank
            checked += 1
print(f"FILTERED PAGE ORACLE PASS: {checked} exact successor kernel/cokernel cases")
