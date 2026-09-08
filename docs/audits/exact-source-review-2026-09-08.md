# Exact-source interface and architecture review

A one-shot Claude Fable 5.1 run audited and corrected the candidate against
base `784b59925beb9a480519142336bd6434f6eeef16`. The
[frozen input record](fable-inputs-2026-09-08.json) fixes the tracked patch digest
and untracked source hashes. This was a model review, not a human referee
report or a final release verification.

The review confirmed that the terminal import closure excludes
`GeneralTangentLimitCriterion`. It corrected the proof account to distinguish
the actual visible-frame/finite-gradient/conormal-axis route from the separately
proved tangent-limit lemma, and clarified which frame producer is passed to
the auxiliary `PaperInputs.Inputs` packaging.

The original Challenge and Solution remain unchanged. The new positive-rank
Challenge specifies a symplectic linear coordinate raised to the actual
intrinsic Bernstein degree of the input. The reviewer repaired the free-word
embedding, the ordered PBW-word correspondence, equality of the filtrations,
and equality of the least filtration level with the checked normal-form degree.
The transport does not assume an equivalence or degree as an extra hypothesis.
Four transport endpoint axiom reports used only ordinary Lean foundations.

The review also corrected the scripts, added concrete unit and coordinate
degree consumers, distinguished historical verification from the new candidate,
and repaired the dossier's proof account and overflowing paths. The dossier
built to 12 pages without overfull boxes during the review.

The one-shot run ended before the full build and Comparator checks: the
initial development build shared mutable dependency caches with another task
and failed when an imported object file disappeared. The controller isolated
the build and dependency directories and owns the subsequent checks. The
[machine verification record](../verification-results.json) is the authority
for the exact source snapshot and checks that ultimately passed; this review
record must not be read as a substitute for it.
