---
name: proof-audit
description: Independently audit a substantive mathematical proof or proof candidate, identify the first invalid bridge, preserve valid downstream structure, and supply an exact repair when possible. Not for journal-style manuscript refereeing.
---

# Proof Audit

Use for an independent correctness audit of a load-bearing mathematical claim,
especially an open-problem candidate. Use `referee` instead for a journal-ready
manuscript report.

## Freeze the candidate

Review an immutable proof packet: exact statement, hypotheses, conventions,
revision or patch digest, cited premises, and claimed scope. Do not infer the
controller's preferred verdict and do not edit or promote authoritative state.

Divide review scopes only when they are mathematically distinct. Do not send
multiple reviewers the same question merely to obtain votes; one fatal issue
cannot be outvoted.

## Audit in dependency order

Reconstruct the proof from its first nontrivial implication. Check:

- quantifiers, base field, finiteness, regularity, and edge cases;
- left/right, variance, quotient, localization, filtration, and grading
  conventions;
- whether every external theorem has the hypotheses actually available;
- whether computation or formalization verifies the intended statement;
- hidden circularity, especially when an intermediate lemma is equivalent to
  the terminal claim;
- descent, lifting, closure, genericity, and limit arguments at their exact
  strength;
- whether each conclusion follows from containment or requires equality.

Stop at the first invalid or unsupported bridge, but inspect enough of the
suffix to state what remains valid conditionally.

## Repair is a first-class verdict

Return `REPAIR` when the candidate's central mechanism is sound and the first
gap has an exact replacement argument under the claimed hypotheses. A repair
must display the replacement lemma and its proof; silently strengthening the
hypotheses is not a repair.

If the gap is not repaired, distinguish:

- `FAIL WITH SCOPE`: this candidate fails, while a conditional suffix or
  narrower theorem survives;
- `INVALID`: the claimed object, evidence, or statement is fundamentally
  mismatched;
- `PASS`: no unsupported load-bearing inference remains in the reviewed scope.

Blacklist only the failed implication. State the new input that would justify
reopening the route.

## Dependency minimization

For a passing or repaired proof, remove unnecessary machinery. Ask which
hypotheses and prior lemmas are actually used, whether a stronger direct
statement is available, and whether an intermediate special dimension or
finiteness assumption can be eliminated.

For a terminal claim, recommend separate audits for genuinely different
components—such as geometry and module theory—followed by one integration
review checking faithful composition, frozen revisions, and scope. Review does
not replace an independent behavioral oracle or source verification.

## Output

```text
VERDICT: PASS | REPAIR | FAIL WITH SCOPE | INVALID
REVIEWED SCOPE:
FIRST BAD BRIDGE: none | exact implication
EVIDENCE:
REPLACEMENT ARGUMENT: none | complete repair
CONDITIONAL SUFFIX THAT SURVIVES:
UNNECESSARY DEPENDENCIES:
NON-CLAIMS:
REOPENING CONDITION:
```
