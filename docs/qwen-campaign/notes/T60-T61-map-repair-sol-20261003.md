# T60–T61 map repair: current-source candidate, 2026-10-03

Prepared candidate only. No authoritative map, registry, state, theorem or
manuscript was changed. No Lean, repository verifier, cluster or Mac execution
was performed; no publication, push or release was performed.

Artifacts: `/tmp/stafford-final-map-sol/candidate-map.json`,
`definition-owners.patch`, `locator-audit.json`, `source-hashes.txt`,
`pending-compiler-checks.json`, `validation-summary.json`, and `walkthrough.json`.
The rendered diagnostic is
`/tmp/stafford-final-map-sol/render/stafford38-paper-lean-audit.html`.
`repair.mjs` reproduces the locator repair from the Luna candidate and current
source bytes. `snapshot.py` and `diagnostic-map.json` are scratch-only inputs;
the diagnostic commit must never replace the controller's public release pin.

## Repairs

- Both new challenge cards now point to the actual shared Mathlib-only owner,
  `Stafford38/ChallengeDefinitions.lean:78,193`. The main and alternative
  solution entrypoints retain identical exported declaration names, resolved
  by their distinct files. Each entrypoint explicitly expands the corresponding
  unchanged challenge proposition; the challenge propositions expand their
  relevant challenge definitions.
- Re-resolved every declaration reference with the existing renderer's
  namespace-aware resolver. Refreshed 402 source anchors/expansions;
  403 unique declarations resolve with their exact source owners and names.
  The coisotropic helper `GeneralCoisotropicExclusion.exists_zero_base_coordinate`
  is now line 84, correcting the stale line 29. Forwarding challenge modules
  now link to their actual definition owner.
- `commonOpen_position_of_pointColumns` and `genericOpenArc_eq_of_source_eq`
  are public declarations in CommonOpenPositions, at lines 56 and 127.
  Their visibility follows current source. All actual private helpers are
  marked module-private and linked as helpers, without pretending they are
  exported public FQNs.
- All 100 current SameWitness declarations are included on the existing
  geometric-proof card through ordinary `lean` fields. Structures expose
  their fields; all declarations retain exact signatures and their variable,
  namespace, open and local notation contexts. This includes
  CommonOpenDerivativeData, CommonOpenColumnsData, their public getters,
  both column helper theorems and commonOpenColumnsData_of_arc. Technical
  helpers and projection abbreviations use the existing collapsed supporting
  declaration display. No renderer, UI, framework or test changes were added.
- The 55 stable IDs and their order are preserved, with the two challenge
  comparisons immediately after thm:main. Their paper excerpts now include
  the complete theorem and marked formal comparison (lines 95–114), fixing
  the former cut through AIadd. Both use supported review_scope publication;
  the previous unsupported scope hid them under the default review filter.
- The dependency note now identifies AlgebraicAnalysis v0.3.3, exact pin
  bbbbf3fc358ca8100b158cec4cf47f336ab70163, on Lean 4.35.0-rc3.
- The proposed registry patch adds only 14 newly retained contracts: the two
  setup/presentation records; arc factors; the point/chart/map/compatibility/
  composite common-open records; arc transport/data; positions; derivative
  certificate; columns; and etale data. The current registry has no owner for
  these combined contracts. Existing component owners are retained. The patch
  registers no theorem, private helper or projection abbreviation.

## Exact inputs

Paper commit: `daf43041f8363f39f35b3c894e6a7e3cd72cd3cc`.
Selected human_readable_main.tex SHA-256:
`c792f4b651740c3fe94ddbb8ebf8ee7c552637dd52b06746c0b79ec3e2057485`.
Formal observed base: `1a3fcfd7028df83b86cbd9da9e608ca98c03385c`.
Observed `git diff --binary HEAD` SHA-256:
`95a39febfcf84c89c7aa6540cdc65c60c4296f8c2124585e23f303c1bd3bfe1d`.
This patch digest does not cover untracked files; `source-hashes.txt` covers
mapped source bytes and the scratch tree includes every current Lean source.
Scratch-only complete source tree: `dd1d26e8f57f4e0eaebdcb30dd537ec4e65e7e59`.
Scratch-only diagnostic commit: `56343417693deaadfbe18e02d832048b5da73390`.
Renderer public commit: `40967b6740c2ceaf515a2fb47a5ca9571be6495f`.
Candidate-map SHA-256: `44ea542bf8bc17a48db8301070cb4d82e21bbdd997fb60868234d123ce573b1a`.
Registry-patch SHA-256: `ae925d63fbcba6126b78d3f9cac90e430249e9d8d360f040f66a83c0b10b7eea`.
The candidate retains an explicitly pending final formal source pin. Its
observed base is not represented as certifying uncommitted candidate sources.

## Validation and limits

The existing public `build.mjs --check` passed against the pinned paper,
current formal scratch snapshot, exact dependency repositories and archived
global repository: exit 0, zero errors and zero warnings. The original Luna
candidate's failing challenge files and broken markup boundaries were repaired.
The scratch Chromium walkthrough started at the generated starting link,
followed every Next claim link through all 57 cards in order, and confirmed
that all were visible, including both challenge comparison cards. It found
zero unresolved declaration elements. `git apply --check` passed for the
owner-registry proposal against MAIN; the patch was not applied.

Every mapped custom named challenge result is expanded. Eight residual
renderer notices concern standard notions Function.Surjective, Module.Finite,
Subsingleton or Disjoint rather than missing project contracts; the exact
notices are preserved in validation-summary.json. Some existing definition
body excerpts intentionally stop at proof bodies; theorem and producer
signatures remain present. These are disclosure notes, not compiler receipts.

Static unknown or ambiguous declaration locators: none. Compiler acceptance
remains pending for all 394 distinct exported map references, listed by
repo/file/name in pending-compiler-checks.json. The 9 module-private refs
are source-only and must not be submitted as public #check names. Main and
alternative solution modules must be checked separately because they export
the same challenge solution names. The global archived result remains a
separate repository reference. No kernel or transitive axiom claim follows
from the Node audit.

The controller must refresh the candidate once accepted proof sources are
frozen, pin the actual public formal commit, check declarations against the
completed build, and promote the reviewed registry patch. Source resolution,
formal proof verification and Max/Johanna's pending mathematical reviews are
separate gates. This candidate does not claim whole-proof correspondence or
acceptance of the manuscript's marked proposals.
