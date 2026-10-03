# Stafford38 formalization status

```yaml
terminal_claim: Stafford Conjecture 3.8 and fixed-source strengthening
phase_i_status: done
phase_ii_status: done at verified source f6915782
paper_status: author proofs restored on Overleaf and GitHub; formal correspondence being extended
formal_status: terminal theorem and documented corollaries verified
open_theorem_holes: []
public_release: v1.2.3; same mathematical main challenge
active_task: implement Johanna's paper arguments, consolidate all definitions, then verify before final human handover
```

The README, `docs/proof-guide.md`, `docs/proof-graph.yaml`, and
`docs/verification-results.json` contain the detailed architecture and
evidence. The author requested the manuscript cyclicity and noncharacteristic
corollaries, complete cross-links, a verifier replay and an archived release.
The main theorem is complete; these additions retain the pinned dependencies.
Release/documentation checks and mathematical verification are recorded separately.

The current alignment task is recorded in `docs/paper-route-alignment.json`.
A proved headline theorem does not establish correspondence of every intermediate
paper argument. Preserve the author's visible proofs and make local tracked
corrections; implement missing bridges in Lean. Any proposed replacement requires
specific evidence that following the author's route is impractical and the
checked alternative is substantially cleaner. The old release remains a valid
proof of its unchanged challenge; it is not a receipt for this new alignment task.
