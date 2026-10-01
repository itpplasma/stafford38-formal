# Luna review protocol

Every claimed frontier delta, milestone promotion, cross-component interface,
or end-to-end claim receives independent parallel review in the applicable
scopes below. A milestone or end-to-end claim requires `PASS` in every
relevant scope. `NEEDS FIX` or `INVALID / CIRCULAR` downgrades the claim and
blocks promotion until repaired.

## Review tiers

### Ephemeral micro-review

Use one cheap fresh Luna review for an ordinary meaningful lemma, computation,
or route check when an adversarial sanity check is useful. The review may stay
in working context and is not a claim record, evidence-gate promotion, or
commit requirement. Do not invoke it for routine PDF reading, scratch work,
failed attempts, or `NO_PROGRESS` unless a result is being made durable.

### Focused parallel review

Use the applicable independent scopes in parallel for a durable theorem or
refutation claim, a major frontier promotion, a significant computational
certificate, a milestone, or an end-to-end claim. All required scopes must
return `PASS` before promotion.

## Review scopes

### MATHEMATICAL

Audit the exact statement, quantifiers, field assumptions, dependencies,
and whether the result closes the named task rather than a stronger-looking
but circular condition.

### SIDEDNESS

Audit right versus left ideals/modules, every equality in `A` versus `A/dA`,
explicit right-`dA` cofactors, and any opposite-ring or `tau` transport.

### NOVELTY

Audit circularity, route duplication, blacklisted inferences, scope of
special classes, and whether a bounded result is being promoted to a
universal claim.

### REPRODUCIBILITY

Audit the actual command, tool version, input/output trace, hashes, fixture
immutability, independent oracle, and clean-checkout reproduction. A source
file or commit message alone is not evidence.

## Packet

Send each reviewer:

- one exact claim and task ID;
- changed paths;
- declared verifier command and captured output;
- prerequisites and evidence paths;
- strongest adversarial test;
- explicit scope of what remains open.

Each reviewer returns exactly `PASS`, `NEEDS FIX`, or `INVALID / CIRCULAR` and,
if not `PASS`, identifies the first fatal issue only.

## Acceptance

Record verdicts with the claim or milestone. Do not commit a mathematical
`PASS` without the applicable review records. Control-plane-only changes may
use a documentation consistency review, but must not change mathematical
claim status.
