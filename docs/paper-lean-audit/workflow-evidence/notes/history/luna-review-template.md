# Luna hostile review

Review exactly one proposed frontier delta.

## Claim

[Insert the exact claim]

## Evidence

[Insert file paths, commands, computation output, or references]

## Verdict

Return exactly one: `PASS`, `NEEDS FIX`, or `INVALID / CIRCULAR`.

## Mandatory audit

Check:

1. quantifiers and field assumptions.
2. equality in `A` versus equality in `A/dA`.
3. right and left sidedness.
4. whether a premise already implies the conclusion.
5. every external theorem's hypotheses.
6. whether computations were executed.
7. whether the result closes or refutes the named ledger leaf.
8. whether the result merely repackages a blacklisted route.

If the verdict is not `PASS`, identify the first fatal inference only.
