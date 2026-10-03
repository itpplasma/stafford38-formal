# Verification

Historical source `f6915782d2281e3d3b51011b97ace866928053b9` passed the full verifier and
both Comparator configurations in an isolated clean checkout fetched from
GitHub. Compiled caches were reused; this was not a cold rebuild. All 36
endpoint reports, 17 literal consumers and 101 paper-linked declarations use
only ordinary foundations. Both NanoDa and Lean accepted both compared
solutions. The audit tool passed 34 tests without skips and its complete
snapshot rendering check passed without warnings.

The [historical receipt](verification/f6915782/verification-results.json), SHA-256 `a1cca54a8c46df89797b85dfa24359e3e0b640caa414bcac29c4fd3cc7a81f9d`, records exact
commands, source pins, counts and [compressed logs](verification/f6915782/).
Historical reports remain under `verification/history/`. That receipt records
its own source, dependencies, configurations and verifier scripts. The later rc3 v1.3.0 proof source has its own source-specific receipt section below; fixture results
do not qualify the Stafford proofs. Independent AI reviews
are retained in [the review index](audits/manuscript-corollaries.md); human
mathematical review remains open.

## v1.3.0 proof source verification

The complete pinned Linux run passed at frozen public source
`12ae3cc49152672a48a96f13994314b65ae38197`, using Lean
`leanprover/lean4:v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, and AlgebraicAnalysis
`bbbbf3fc358ca8100b158cec4cf47f336ab70163` (v0.3.3). It included a fresh
4,475-job Lake build, strict dependency inspection of all four terminal roots
with zero forbidden or unavailable dependencies, the complete repository
verifier, retained proof-library build, and all four Palomar comparator
configurations: main, fixed-source, alternative, and alternative fixed-source.
The full verifier passed in allocation3131801, the retained modules in3136492, and the four comparisons plus final integrity in3137241. All used the same frozen source and dependency pins. Completed checks were reused, with their original receipts preserved.

The current primary machine-readable report is [verification-results.json](verification-results.json). The exact C2 run files and logs are retained under [verification/12ae3cc4/](verification/12ae3cc4/).

These checks establish the formal theorem and compared Challenge/Solution
statements only at the named source and configuration. They do not establish
whole-paper proof correspondence. Max’s and Johanna’s human reviews remain
pending; the visible author proof and marked proposals retain their separate
review status.

The review-map compiler check separately passed399 public owner/name checks in4 isolated groups on the same C2 source; its [receipt archive](qwen-campaign/notes/T80-399-public-names-linux-accepted-3139266-20261003.tar.gz) retains the exact inputs and outputs. Eleven private helpers and two Global Stafford references remain explicitly source-only.

The release [code-integrity manifest](qwen-campaign/notes/T91-release-code-congruence-20261003.json) records656 protected files byte-identical to C2. Later documentation and review assets do not constitute another proof replay.

## Logical scope

The universal certificate, exact-degree strengthening, general geometric
theorems, and advertised corollaries use only `propext`, `Classical.choice`,
and `Quot.sound`. The audited declarations contain no project or literature
axioms, proof placeholders, or `Lean.ofReduceBool` dependency.

The ordinary result quantifies over every characteristic-zero field and all
ranks, including zero. The fixed-source result specifies the exact Bernstein
degree at positive rank; its Mathlib-only compared form
`Stafford38FixedSourceChallenge.universalFixedSourceStatement` uses the
intrinsic ordered-word filtration degree of the presented element. The
geometric scope includes arbitrary relevant affine asymptotic conormals,
component conormal containment, and exclusion for closed fibre-conical
coisotropic sets, which the terminal proof imports, and the separately proved
auxiliary tangent-limit criterion, which it does not. Their precise hypotheses
are recorded in the [statement correspondence](paper-lean-specification.md);
the imported route is recorded in the [proof guide](proof-guide.md) and
[proof graph](proof-graph.yaml).

## Reproduction

From the selected commit on Linux with Elan, Python 3.11 or newer, the build
tools, and bubblewrap 0.12.0 installed:

```sh
lake exe cache get
lake build
scripts/verify.sh
scripts/bootstrap-palomar-tools.sh
scripts/verify-palomar.sh comparator.json
scripts/verify-palomar.sh comparator-fixed-source.json
scripts/verify-palomar.sh comparator-alternative.json
scripts/verify-palomar.sh comparator-alternative-fixed-source.json
```

| Component | Pin |
| --- | --- |
| Project Lean | `leanprover/lean4:v4.35.0-rc3`, commit `470d5ce1400764999581fd26d5d72b00d990b0f4` |
| Mathlib | `c55e6e786f49471c72fbddbec5415808896aec1e`, using the same rc3 toolchain |
| AlgebraicAnalysis | `bbbbf3fc358ca8100b158cec4cf47f336ab70163` (`v0.3.3`), using rc3 and the same Mathlib revision |

AlgebraicAnalysis is fetched from its public Git repository. Its source is
external to this package and subject to the same foundational-axiom boundary.
The build needs neither the private research repository nor the paper mirror.
Generated logs and tool builds remain under `.lake/` and are excluded from Git.

## Theorem and consumer gates

[`scripts/verify.sh`](../scripts/verify.sh) resolves every source import against
the checkout, Lean core, or its pinned dependencies. It builds every retained
Stafford module, the aggregate theorem and both Solutions, checks pins, scans
for proof holes, and audits 36 exact endpoint reports under `--trust=0` (the
historical report audited the first 19; the Mathlib-only exact-source
statement is added in `v1.1.0`):

| Group | Reports |
| --- | --- |
| Universal, exact-degree, and Mathlib-only exact-source theorems | 3 |
| Ore localization, formal adjoint, four intrinsic differential-operator results, and two evolutionary results | 8 |
| Tangent limit, asymptotic conormal, component containment, coisotropic exclusion, and canonical application | 5 |
| Independent tangent/coisotropic consumers and the involutive/non-Poisson negative control | 4 |

The separate [`check-consumers.sh`](../scripts/check-consumers.sh) is a required
step of that verifier. Its fourteen axiom reports come from literal statements in
[`CorollaryConsumer.lean`](../tests/CorollaryConsumer.lean),
[`LocalizedDifferentialConsumer.lean`](../tests/LocalizedDifferentialConsumer.lean),
and [`FixedSourceChallengeConsumer.lean`](../tests/FixedSourceChallengeConsumer.lean),
[`TorsionCyclicityConsumer.lean`](../tests/TorsionCyclicityConsumer.lean), and
[`NoncharacteristicConsumer.lean`](../tests/NoncharacteristicConsumer.lean)
(the historical report lists the first nine). They check the exact exponent,
multiplication order, Ore transport, potential coefficient hypotheses, actual
intrinsic differential-operator types, and, for the exact-source Challenge,
the intrinsic degree of the unit (`0`, once computed without the transport) and
of a coordinate (`1`) together with the compared theorem instantiated at both.

Two finite regression oracles supply independent computational checks:
1,792 filtered-page kernel/cokernel cases and 252 PBW projection cases, including
a wrong-sign control. These examples check behavior; the universal results
are established by their Lean proofs.

## Import separation and sandbox

[`check-import-closure.sh`](../scripts/check-import-closure.sh) asks Lean for
`env.header.moduleNames`, so it checks the actual loaded transitive environment.
Each Challenge permits Lean core and the pinned Mathlib dependency closure,
and excludes Stafford and AlgebraicAnalysis. Each Solution excludes both
Challenges. The exact loaded-module counts are in the verification report.

The only deliberate proof placeholders are the compared theorems of
[`Challenge.lean`](../Challenge.lean) and
[`FixedSourceChallenge.lean`](../FixedSourceChallenge.lean), one in each.
Both Weyl presentations use `FreeAlgebra`, `RingQuot`, and the standard
symplectic matrix. [`Solution.lean`](../Solution.lean) transports the proved
Stafford theorem by an algebra equivalence.
[`FixedSourceSolution.lean`](../FixedSourceSolution.lean) uses the
[transport module](../Stafford38/FixedSourceChallengeTransport.lean), which
uses the shared definitions without importing either Challenge and proves
that the intrinsic ordered-word filtration and its least level coincide with
the development's Bernstein filtration and checked PBW normal-form degree.

Comparator exports and compares `Stafford38Challenge.universalStatement`
(`comparator.json`) and
`Stafford38FixedSourceChallenge.universalFixedSourceStatement`
(`comparator-fixed-source.json`) in separate environments, checks the
permitted axioms, and submits the exported proofs to NanoDa, con-ron, and Lean's
default kernel. The current runner uses the rc3 toolchain's bundled
`lake comparator` with bubblewrap and a protected configuration naming both
independent kernels. Submitted configurations cannot select their own kernels.

Both selected Challenges inline the exact code from
[`Stafford38/ChallengeDefinitions.lean`](../Stafford38/ChallengeDefinitions.lean)
because current Palomar policy excludes project-local imports from the
Challenge source closure. The Solutions keep that shared definition owner.
The source gate checks the inlined code against the owner; Comparator must
independently confirm every reached definition and the unchanged theorem type
in separate environments. Max's review should check the Weyl relations,
noncommutative factor order, characteristic-zero and rank hypotheses, and the
intrinsic fixed-source degree in both Challenge copies and the shared owner.

## Verification tools

The bootstrap records SHA-256 digests of bundled `lake`, `lean`, `leanexport`,
`leanchecker`, `nanoda_bin`, and `con-ron`, plus the bubblewrap binary, under
`.lake/palomar-tools/`. Historical receipts retain the earlier separate
Comparator, lean4export, NanoDa, and Landrun pins at their original sources.

The local source preflight vendors the exact source rules from
[PalomarSubmission `65f0154`](https://github.com/PalomarRegistry/PalomarSubmission/tree/65f0154ed776cd26c224254aa57b379137f28b0d).
It checks module headers, UTF-8, regular source files, the 10,000-line limit,
dependency pins, and both Comparator configurations. Independent fixtures
check matching statements, statement mismatches, and an unpermitted proof
axiom; their logs remain under `.lake/verification/palomar-behavior/`.

For the complete official mechanical preflight, dispatch
[`palomar-preflight.yml`](../.github/workflows/palomar-preflight.yml) with the
same full immutable source commit for both configurations. It calls the
pinned PalomarSubmission workflow in full mode, including canonical Challenge
source reconstruction, dependency authentication, metadata and archive
checks, and kernel replay. Retrieve both `mechanical-report` artifacts before
their 90-day expiry and retain them with the source receipt. The workflow
provides advisory verification evidence; registration and editorial review
remain separate Palomar operations.

## Source regression and review

The signed private source commit
`8cc7802cd4355d819d2df4f680ba26d4a339f80e` passed its full 229-checker
manuscript regression. That record supports extraction provenance; the
independent canonical-clone result above verifies this repository's own files.

The [paper/Lean specification](paper-lean-specification.md) records the
statement mapping. Automated and scoped agent reviews do not establish
independent human expert approval, journal acceptance, novelty, or priority.
Those statuses require their own human review records. Palomar registration
and all public release actions require separate authorization.

## v1.3.1 provenance correction

The descriptor’s historical cbb2396 commit/hash now points to [its exact report](verification/history/cbb2396d-verification-results.json). The completed f6915782 isolated-checkout replay and C2 Linux replay remain separate source-scoped results, as recorded above. Package version and provenance metadata changed; mathematical source, statements, dependency pins and verifier programs did not. This correction does not imply a new proof replay.
