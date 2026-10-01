# Stafford38 formalization status

```yaml
terminal_claim: Stafford Conjecture 3.8 and fixed-source strengthening
phase_i_status: done
phase_ii_status: done at the recorded verification snapshot
paper_status: complete
formal_status: terminal theorem and documented corollaries verified
open_theorem_holes: []
public_release: human review and publication only
```

The README, `docs/proof-guide.md`, `docs/proof-graph.yaml`, and
`docs/verification-results.json` contain the detailed architecture and
evidence. No new theorem formalization is scheduled; preserve the pinned
dependencies and report release/documentation work separately from proof work.

2026-09-30: after the paper--Lean audit (private research archive,
`docs/paper-lean-audit`), the remaining manuscript statements without a Lean
counterpart were formalized: `Stafford38.WeylDomain` (no zero divisors),
`Stafford38.TorsionCyclicity` (cyclicity of finitely generated torsion right
modules, with the Mathlib-only `CorollaryChallenge.lean`/`CorollarySolution.lean`
pair and `comparator-corollary.json`, not intended for Palomar) and
`Stafford38.NoncharacteristicHyperplane` (manuscript Appendix B). They are not
part of a tagged release; the next release must repeat the full verification.
