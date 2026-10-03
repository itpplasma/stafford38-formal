# T22 independent proof audit

VERDICT: PASS

REVIEWED SCOPE: Static audit of the immutable T22 theorem, literal consumer,
patch, and its pinned endpoint dependency. This is not kernel or build
evidence.

Frozen inputs:

- Base: `0340cf2b1601de7a8895c0b450d4bcbbb9867bed`
- Candidate patch SHA-256: `182c0fe987ed862172de18decd620afbc9236a0bebf7022528775b6cbb24f8a6`
- `EndpointOfAlgHoms.lean` SHA-256: `14d8f3abf5119a63a0ee287a6dd9524c8ad1d8c9acf29af84f920052de6dabdd`
- Consumer SHA-256: `6d3b5ab88a2bf74374be91339e1ff1a1a2eccae24b97088e8135957be9d2b4d2`
- Pinned endpoint SHA-256: `32d6cb82af078383adfe0a3cdfc5353e9635bc7fd90e85ee25cc82e6cb55f674`

FIRST BAD BRIDGE: none found.

EVIDENCE:

- The candidate replaces each pinned endpoint algebra action with the
  corresponding hom-induced action: `A₀ →ₐ[k] E` supplies `Algebra A₀ E`,
  its composition with the quotient map supplies `Algebra S E`, and
  `MvPolynomial (Option (Fin d)) k →ₐ[k] E` supplies the polynomial action.
- The three ground towers use the algebra-map equalities induced by
  `φ.comp_algebraMap`, the composed quotient map, and
  `ψ.comp_algebraMap`. The `S → A₀ → E` tower follows because the installed
  `S → E` map is definitionally the composition of the installed `A₀ → E`
  map with the quotient map. These are exactly the four tower assumptions
  required by the pinned endpoint.
- Both formal-etale premises are stated under the exact `toRingHom.toAlgebra`
  instances installed in the proof. The chart equality using `φ` is converted
  to the pinned endpoint's `algebraMap A₀ E` form using that same installed
  algebra. No extra compatibility assumption is needed.
- The Laurent-series prelude retains the pinned endpoint's algebra actions
  and tower. The orientation is correct: `hground` states
  `rho.comp (algebraMap k E) = algebraMap k (LaurentSeries k)`, so its
  symmetry is the equality required by
  `IsScalarTower.of_algebraMap_eq'` for the `E` action induced by `rho`.
- The remaining quantified data, smoothness, numerator nonvanishing, and
  conclusion match the pinned endpoint. The consumer repeats the candidate
  statement and applies it with all arguments in order; its `#print axioms`
  is present. Neither consumer syntax nor the theorem application is kernel
  evidence until the prescribed Lean check runs.

REPLACEMENT ARGUMENT: none needed.

CONDITIONAL SUFFIX THAT SURVIVES: Entire proof suffix is supported, conditional
on the explicitly supplied maps, etale certificates, Laurent map and column
identities, smoothness, and numerator hypothesis.

UNNECESSARY DEPENDENCIES: None identified in this bounded scope. The
field-closure, characteristic-zero, and endpoint data hypotheses are carried
through from the pinned theorem.

NON-CLAIMS: This adapter does not produce `φ`, `ψ`, `rho`, the column
identities, smoothness, or numerator nonvanishing. It does not establish the
unconditional same-witness closure result or manuscript correspondence.
Static review does not replace Lean kernel checking, the consumer check, or
axiom inspection output.

REOPENING CONDITION: Reopen this audit if the frozen source or dependency
changes, or if the prescribed Lean check exposes an elaboration or axiom issue.

## Re-anchored audit: final Sol repair (2026-10-03)

VERDICT: PASS

REVIEWED SCOPE: Final minimal Sol repair against base
`0340cf2b1601de7a8895c0b450d4bcbbb9867bed`, audited by comparison with the
prior frozen packet above and the pinned endpoint.

Final packet identities:

- Candidate patch SHA-256:
  `069840c2f2e97833931de2128be5def4043cfd76ff49e9cee4fc8a926235edf2`
- Source SHA-256:
  `690f8008bee2e7105d208306c91208f46c60d5e32de6040a9cfcda879d91a720`
- Consumer SHA-256, unchanged:
  `6d3b5ab88a2bf74374be91339e1ff1a1a2eccae24b97088e8135957be9d2b4d2`
- Pinned endpoint SHA-256, unchanged:
  `32d6cb82af078383adfe0a3cdfc5353e9635bc7fd90e85ee25cc82e6cb55f674`

FIRST BAD BRIDGE: none found.

EVIDENCE: A direct source diff against the previously audited candidate shows
only removal of the two `rfl` tactics that followed already-closing `congr 1`
steps. The tower congruence and hchart congruence remain. Thus the theorem
statement and all hypotheses are byte-for-byte unchanged from the audited
candidate; the consumer is byte-for-byte unchanged as well. The final source
hash and patch hash match the packet. The final receipt records
`literal_statement_equal: true` and `consumer_unchanged: true`. The recorded
guarded module build and `--trust=0` consumer check both exit 0; the consumer
axiom output is exactly `propext`, `Classical.choice`, and `Quot.sound`. These
are recorded checks from `T22-check.md` and the frozen logs, not commands run
as part of this static re-anchor.

The previous algebra-action, tower-coherence, etale-instance, chart-conversion
and Laurent-series arguments remain unchanged and supported as detailed
above. Removing redundant tactics alters no inference or premise.

REPLACEMENT ARGUMENT: none needed.

CONDITIONAL SUFFIX THAT SURVIVES: Entire theorem, under its stated inputs.

UNNECESSARY DEPENDENCIES: None identified.

NON-CLAIMS: This adapter remains conditional on the maps and geometric data
listed above; the check does not establish the unconditional same-witness
closure result or manuscript correspondence.

REOPENING CONDITION: Reopen if the final frozen source, consumer, or pinned
endpoint changes, or if later integration changes the checked dependencies.
