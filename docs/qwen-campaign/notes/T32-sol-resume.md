# T32 Sol escalation: common-open candidate

Base: `03c6915930e2c3d9370d6fb9720ef07a5c0779d4` in the campaign worktree.
The failed Luna log is `.lake/campaign-resume/logs/T32-luna-resume-1.log`.
The controller owns every Lean invocation, integration, and promotion.

Candidate source SHA-256: `285b7a7d74e444ff67b0ab17505daca8a1b8a1237a3c3ae36871140b65217d1c`.
Consumer SHA-256: `fdd4982c7e63eca36b5c1bd6eed51957dbec7f698fa1b74f576af64e8169d757` (unchanged).

Changes reuse existing definition owners and Mathlib `IsScalarTower.of_algHom`.
Namespace openings resolve existing arc, coordinate, component-field and
common-open map declarations. Point-local maps name their normalization source
explicitly. Local notation scopes the retained witness's ambient action and DVR
local-ring proof only while elaborating the existing column owner; it creates
no declaration and does not install a second action in concrete theorem proofs.
The column specification is scoped the same way.

The old `hfactor` field incorrectly used a theorem proof as its type and had an
unbound `g`. It now spells out that theorem's existential conclusion. The final
constructor applies the existing theorem. The map-data helper now returns its
proved `hqA`, which the final constructor previously referenced out of scope.
No target hypotheses were added and the literal consumer target is unchanged.

Source analysis performed: project provenance, campaign sections 0–4 and 6,
T32/STATE, definition owners, existing Mathlib tower declaration,
AlgebraicAnalysis search, and the existing project column/arc/map owners.
This is a candidate pending the controller's guarded module and trust-zero
literal-consumer checks; source hashing is not proof evidence.

## First guarded Sol check and syntax repair

Controller check: exit 1, wall 7 seconds, peak 2126 MiB, 8 GiB/two CPU cap.
Log: `.lake/campaign-resume/logs/T32-sol-resume-1.log`.
First errors were notation quotation prechecking of `letI` and macro application
syntax, followed by cascades. The next candidate scopes `quotPrecheck false`
to the two notation declarations, gives them maximum parsing precedence,
parenthesizes function macros before applying column indices, and uses `(w)`
projections so quotation substitutes the bound argument rather than retaining
an unresolved dotted identifier. This changes syntax prechecking only.
The existing internal selected-coordinate helper now declares the algebraic
closedness already required to type its `ChartSetup` argument.
Latest source SHA-256: `b4bdc0e890c612766eda5265b00e5b07265b752a8fe7b85bc069c0ece7765fe1`.
The final construction target and consumer remain unchanged.

## Second guarded Sol check and declaration split

Controller check: exit 1, wall 63 seconds, peak 2961 MiB, 8 GiB/two CPUs.
Log: `.lake/campaign-resume/logs/T32-sol-resume-2.log`.
First local-ring failures concerned the retained differential orders, now
scoped by order/gap notation exactly as the existing column owner. The bundle
hit a deterministic whnf timeout at 1.6 million heartbeats; that limit remains.
The revised candidate splits it into inherited point and selected-chart records
and the remaining common-open record. Existing exported projections remain
available through inheritance.

New definition-owner proposals (controller to integrate after acceptance):
- `CommonOpenPointData`: same file; isolates retained point/axis output from the common-open maps.
- `CommonOpenChartData`: same file; isolates selected quotient columns from point and arc data.
- `CommonOpenArcFactors`: same file; abstract-ring certificate for the existing factor theorem's full conclusion, avoiding a heavy inline proposition in the concrete record.

The abstract certificate's unit proof explicitly maps the point-local unit
through the point-local arc, rather than mapping it through the original-ring
arc whose domain is different. The chart-denominator identity now uses
congruence of the fixed normalization map instead of dependent rewriting of an
Ore-localization carrier.

## Third guarded check: composition repair

Controller check: exit 1, wall 108 seconds, peak 3018 MiB, 8 GiB/two CPUs.
Log: `.lake/campaign-resume/logs/T32-sol-resume-3.log`.
The point/chart parent records passed their elaboration surface, but extending
them reproduced a deterministic whnf timeout in `CommonOpenData`. The next
candidate uses composition with four certificates and tiny projection aliases;
it no longer copies the dependent fields into an extending record. The existing
Cq/U type aliases are reducible abbreviations so their canonical localization
instances remain visible without installing new actions.

Additional definition-owner proposals:
- `CommonOpenMapData`: same file; bounds the common-open maps independently of axis and arc evidence.
- `CommonOpenArcCompatibility`: same file; bounds the abstract factors certificate independently of the concrete map record.
- `CommonOpenData` projection abbreviations: same file; preserve exported notation for the composed certificates, with no new mathematical content.

The remaining dependent rewrite was in the base-map proof, not the previously
repaired denominator identity. It now applies congruence under the fixed
`algebraMap Cq U` to the existing `genericOpenBMap_base_eq` theorem.
Latest source SHA-256: `e68a625b113a569d51a1dd080d9532cd8b775472c1cada13edaa66d26efd1c05`.
No limits were raised; final target and consumer remain unchanged.

The new arc compatibility certificate is named `CommonOpenArcCompatibility`;
the existing T33 `CommonOpenArcData` owner remains untouched. Repository and
definition-owner searches confirmed that the replacement name is unoccupied.

## Resource stops on the composed candidate

The frozen source SHA-256 is `2fc6d54524c7db6906ef2a3a9a7e9a3ae270039d2ced3b7307a94fd60658e299`. Mac checks 4, 5 and 6 stopped at the CPU watchdog before reporting a Lean error. Check 4 used the normal two-thread/two-CPU budget (66 seconds, 3544 MiB). Check 5 reduced threads to one, which also inherited a one-CPU watchdog (44 seconds, 2289 MiB). Check 6 explicitly retained the original two-CPU cap with one Lean thread (66 seconds, 3550 MiB), but parallel Lake work still crossed that cap. None is acceptance, and no resource ceiling was raised. The unchanged source is now checking under the Linux guard’s hard two-CPU affinity.

## Linux/Mac diagnostics and retained-action repair

Linux module check: exit 1, module 299 seconds, total 466.5 seconds, peak
4791 MiB. Independent Mac direct trust-zero check reproduced the errors:
exit 1, wall 139 seconds, peak 3539 MiB. Log:
`.lake/campaign-resume/logs/T32-direct-sol-resume-1.log`.
The five map/arc getter failures now scope the stored point maximality proof.

The first substantive action mismatch exposed a missing interface invariant:
CoordinatePresentation stored an arbitrary fFin unrelated to fOption and τ,
while the axis-output theorem uses their exact reindexing composition.
The controller authorized the necessary T31 repair. The free field is replaced
by an exposed reducible `CoordinatePresentation.fFin` accessor computing that
composition and retaining the dot API. The producer no longer stores it;
its target and literal consumer are unchanged. No new hypothesis is needed.

The point producer is a separate bounded theorem; the final common-open
producer assembles separately typed point/chart/maps/arc certificates.
An abstract-ring factors theorem derives CommonOpenArcFactors from the existing
tilted-product theorem. Its application recovers the intended action from the
expected certificate, without installing concrete scalar actions.

New helper owner proposals: `nonempty_commonOpenPointData` isolates retained
axis output; `commonOpenArcFactors_of_tiltedProduct` packages the existing
abstract factor theorem under the certificate type. Both have mathematical
docstrings and bounded proofs. The computed fFin accessor is the sole owner
of the reindexed coordinate map.

Frozen source SHA-256:
- CoordinatePresentation: `3ffef86177fc2e6b2d552264f47af08553823e4562ad58d51c65fb2cc6d29016`.
- CommonOpen: `eeb116e7807c5bb7ff28a516ea66ecf838d086239c13982ae8a70100f1b4e176`.
Literal consumers are unchanged; T31 recheck and T32 module/consumer checks
are pending the controller. No heartbeat or resource limits were raised.
