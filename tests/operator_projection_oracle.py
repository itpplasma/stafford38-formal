"""Exact PBW checks of projection/reconstruction; not a universal proof."""
from fractions import Fraction
from math import comb, factorial


def add(a, b):
    out = dict(a)
    for monomial, coefficient in b.items():
        out[monomial] = out.get(monomial, 0) + coefficient
    return {m: c for m, c in out.items() if c}


def scale(c, a):
    return {m: c * v for m, v in a.items() if c * v}


def mul(a, b):
    # D^j x^r = sum_t binom(j,t) r!/(r-t)! x^(r-t) D^(j-t).
    out = {}
    for (i, j), c in a.items():
        for (r, s), e in b.items():
            for t in range(min(j, r) + 1):
                value = c * e * comb(j, t) * (factorial(r) // factorial(r - t))
                out = add(out, {(i + r - t, j + s - t): value})
    return out


X = {(1, 0): 1}
D = {(0, 1): 1}


def delta(a):
    return add(mul(a, X), scale(-1, mul(X, a)))


def projection(a, m, sign=-1):
    out, derivative = {}, a
    for j in range(m + 1):
        out = add(out, scale(Fraction(sign**j, factorial(j)),
                             mul(derivative, {(0, j): 1})))
        derivative = delta(derivative)
    return out


assert delta(D) == {(0, 0): 1}
count = 0
for i in range(6):
    for j in range(7):
        p = {(i, j): 1}
        for m in range(j, 9):
            assert projection(p, m) == (p if j == 0 else {})
            restored, derivative = {}, p
            for a in range(m + 1):
                restored = add(restored, scale(Fraction(1, factorial(a)),
                    mul(projection(derivative, m), {(0, a): 1})))
                derivative = delta(derivative)
            assert restored == p, (i, j, m)
            count += 1
assert delta(projection(D, 1, sign=1)), "wrong-sign control failed"
print(f"OPERATOR PROJECTION ORACLE PASS: {count} exact PBW cases; wrong sign rejected")
