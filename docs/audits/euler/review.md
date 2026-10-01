# Independent review: Euler-product identities

Status: review in progress. No source edits or promotion were made.

## Frozen candidate

- Formal repository: `/home/ert/proj/stafford38-formal`
- Base commit: `aaa4b5c5cc6e5ed4eb8b124c7c6fc8062590aa22`
- Candidate file: `Stafford38/Weyl/EulerProductIdentities.lean` (untracked at the frozen base)
- Candidate SHA-256: `6948ed251237554bb255f07cd86086d9cc2c3af6462746d8918f59919b03cde2`
- Imported source at the base: `proofs/weyl_pure_power.lean`, Git blob `b7c2d9b81c8d9adbe42e5c92b303be7ebca6bc32`
- Scope: recurrence signs, finite-product indexing, evaluation in arbitrary `ℚ`-algebras, and endpoint checks. No Stafford theorem audit.

## Preliminary derivation

Let `θ = x*d` and assume `d*x = x*d + 1` in a ring equipped with an algebra structure over `ℚ`. Then `x*θ = (θ-1)*x` and `d*θ = (θ+1)*d`. The candidate's falling recurrence uses factors `θ-n`; its rising recurrence uses `θ+(n+1)`. Moving one `x` or `d` across those factors shifts the index in the indicated direction. The finite products are indexed as `∏_{i<n}(X-i)` and `∏_{i<n}(X+(i+1))`, respectively.

## Completed audit

**VERDICT: PASS.**

**REVIEWED SCOPE:** The exported falling/rising polynomial identities and their evaluation for any `A` with `[Ring A] [Algebra ℚ A]`, assuming `h : d*x = x*d + 1`.

**FIRST BAD BRIDGE:** None found.

**EVIDENCE:** With `θ=x*d`, the hypotheses give `x*θ=(θ-1)*x` and `d*θ=(θ+1)*d`. The candidate's shift lemmas therefore have the correct signs:

- `x*(θ-n)=(θ-(n+1))*x`, so moving `x` across the falling factors shifts each factor down by one.
- `d*(θ+(n+1))=(θ+(n+2))*d`, so moving `d` across the rising factors shifts each factor up by one.

The induction steps then give `x^n*d^n=∏_{i=0}^{n-1}(θ-i)` and `d^n*x^n=∏_{i=1}^{n}(θ+i)`. The polynomial recurrences and `Finset.range` products use exactly those indices. Evaluation sends `X` to `θ` and each rational constant `C q` to `algebraMap ℚ A q`; the latter is central in any `ℚ`-algebra, which is the only coefficient-commutation input used. The endpoint checks agree: at `n=0` both sides are `1`; at `n=1` they are `θ` and `θ+1=d*x`; at `n=2` they are `θ(θ-1)` and `(θ+1)(θ+2)`. The general recurrences prove the same identities for every natural `n`.

I independently ran `lake env lean Stafford38/Weyl/EulerProductIdentities.lean` at the frozen base plus candidate file; it exited 0. Its four `#print axioms` outputs list only `propext`, `Classical.choice`, and `Quot.sound`. The candidate contains no `sorry`, `admit`, or custom `axiom`. Compilation corroborates the handwritten audit; it is not its substitute.

**REPLACEMENT ARGUMENT:** None needed.

**CONDITIONAL SUFFIX THAT SURVIVES:** The full induction and exported evaluation theorems follow under the stated ring, rational-algebra, and Weyl-relation hypotheses.

**UNNECESSARY DEPENDENCIES:** The import of `proofs.weyl_pure_power` is used to reuse its public evaluation hom and constant-evaluation lemma; the candidate does not rely on its private falling/rising identities. This is an integration dependency, not a mathematical gap.

**NON-CLAIMS:** This review does not re-audit the Stafford theorem, the imported module's other proofs, or the repository's release/verifier status.

**REOPENING CONDITION:** Re-audit only if the candidate bytes, the imported evaluation definitions, or the stated hypotheses change.
