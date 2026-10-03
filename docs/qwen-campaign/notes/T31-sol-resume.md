# T31 Sol repair

Base WT commit: `c3dccd4b3f931d15df623229771126f6500fb6ea`.

Frozen candidate:

- `Stafford38/Geometry/SameWitness/CoordinatePresentation.lean`: `0c9137eace6de450ab6c0aaa1957f257c58cb1033bdb19576830b2ef9a900bb2`
- `tests/SameWitness/CoordinatePresentationConsumer.lean`: `bfa1d18843c80f023f0c615d1a9ec43a3da62d7b90477247e2706a3d7bc0b5e1`
- Source-path patch SHA-256 against base: `2e3886078a0bdb3ead2906d853f2cafbb5fdb80e13cb04b18dfe8eb28b0a52cf`.

The controller's fresh guarded replay reproduced the saved failures. Its
local log is `.lake/campaign-resume/logs/T31-controller-resume-20261003-path.log`.
The first error was at source line 68:31: elaborating the retained valuation
ring needed the retained `SourceDVR` ambient algebra. The later `D.a`/`D.e`
accessors needed its local-ring instance. This was a dependent accessor
problem, rather than failure of the mathematical prime witness.

The repair scopes the original `W.ambientAlgebra` into the `hOutput` field's
type. In the proof, the local-ring type and value each carry that same
ambient scope, without installing an ambient scalar action in the proof
context. Both scopes use the original retained action. The finite-coordinate
composition supplies `coeff.toAlgebra` explicitly to `AlgHom.comp`, and the
row carrier is `Type u`, matching the actual residue basis. Existing field
names and the existence theorem's mathematical inputs are preserved. No
closure premise, proof hole, axiom, limit increase or duplicated owner was
added. T32 confirmed that the row universe change propagates through its
existing finite polynomial indices.

Sol attempt 1 failed at the nested canonical ambient term's layout, before
the theorem proof elaborated. Guard exit 1, wall 14 s, peak 2172 MiB.
The field type's earlier missing-instance failures were absent. Attempt 2
fixes the nested term layout and splits row injectivity and chart-row
correspondence into named lemmas. The main proof now has 60 lines; its
statement and the consumer remain unchanged.

Sol attempt 2 also failed during nested-term parsing: its over-indented
result was read as an argument to `ambientAlgebra`. Guard exit 1, wall 15 s,
peak 2189 MiB. Attempt 3 adds an explicit semicolon and aligns the result
with the term binder. The mathematical fields remain unchanged.

The controller's third guarded module check passed for the frozen candidate:
`lake build Stafford38.Geometry.SameWitness.CoordinatePresentation`,
3081 jobs, module 13 s. Local receipt:
`.lake/campaign-resume/logs/T31-sol-resume-3.log`.

`GUARD exit=0 reason=finished wall_s=16 peak_rss_gb=2 peak_rss_mb=2183 peak_cpu_percent=197 rss_cap_gb=8 cpu_cap=2 lean_threads=2 free_mem_gb=69 disk_free_gb=647 swap_used_gb=4`.

The literal consumer also passed:
`lake env lean --trust=0 -M 32000 tests/SameWitness/CoordinatePresentationConsumer.lean`.
Local receipt: `.lake/campaign-resume/logs/T31-sol-final-consumer.log`.
Its theorem reports exactly `[propext, Classical.choice, Quot.sound]`.

`GUARD exit=0 reason=finished wall_s=10 peak_rss_gb=3 peak_rss_mb=3144 peak_cpu_percent=50 rss_cap_gb=8 cpu_cap=2 lean_threads=2 free_mem_gb=67 disk_free_gb=647 swap_used_gb=4`.

The controller accepted and committed the scoped T31 source as
`03c6915930e2c3d9370d6fb9720ef07a5c0779d4`; push was underway when this note
was finalized. Acceptance and integration are controller-owned. The worker
ran no Lean commands and made no commit, push or promotion. These receipts
cover T31 and its literal consumer, not the completed closure or terminal
route.
