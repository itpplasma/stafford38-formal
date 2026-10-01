# Model use and evidence

This register records model use during research, formalization, review, and
publication preparation. It belongs to the research provenance and extended
supplement, not the mathematical manuscript.

## Evidence categories

- **Session metadata:** an exact identifier reported in a source session or
  turn record. Preserve it verbatim, with the source hash and event location.
- **Task configuration:** the model requested for a recorded delegated task.
  This records the request, not independently verified backend execution.
- **Author recollection:** a remembered model name not yet matched to a record.

Model changes within a session are separate events. Provider names, agent
nicknames, filenames, and prose mentioning a model are not proof that it ran.
Missing records remain missing. Model use does not establish authorship of an
idea; the contribution account must cite the actual research events.

## Confirmed model metadata

A bounded scan on 2026-09-05 covered 1,439 Codex rollout files and 144 Claude
files with metadata naming the current or legacy Stafford checkout. The
[evidence register](model-use-evidence.json) records selection rules, date
ranges, counts, and digests of the private source-hash manifests.

| Exact Codex identifier | Observed UTC dates |
| --- | --- |
| `gpt-5.5` | 2026-08-18 |
| `gpt-5.6-luna` | 2026-08-14 to 2026-09-05 |
| `gpt-5.6-sol` | 2026-08-14 to 2026-09-05 |
| `gpt-6-astra` | 2026-09-04 to 2026-09-05 |

Project-scoped Claude metadata from 2026-09-01 records `claude-fable-5`,
`claude-haiku-4-5-20251001`, and `claude-opus-5[1m]`. The legacy Stafford
project also records `claude-opus-5`. The bracketed context-window label is
retained as reported; it is not a distinct identity inferred by this archive.

The files contain reused metadata session identifiers, so file counts and
unique session-ID counts are reported separately. Repeated model-bearing
records are not independent contributions. Hashes describe mutable source
snapshots taken during the recorded scan interval, not completed sessions.
Identifiers found only in unrelated project records are excluded. The
sanitized chronological archive still needs to be refreshed through the
publication cutoff; this inventory is not that archive.

## Author recollection

On 2026-09-05 the author recalled the following model families. This list is
an inventory to check, not a claim that every item is already corroborated.

| Recalled name | Evidence disposition |
| --- | --- |
| GPT 5.6 Luna | Confirmed as `gpt-5.6-luna` in the initial inventory |
| GPT 5.6 Terra | Awaiting source-metadata inventory |
| GPT 5.6 Sol | Confirmed as `gpt-5.6-sol` in the initial inventory |
| GPT 6 Astra | Confirmed as `gpt-6-astra` |
| Claude Opus 5 | Confirmed identifiers include `claude-opus-5[1m]` and legacy `claude-opus-5` |
| Claude Fable 5 and 5.1 | `claude-fable-5` confirmed; 5.1 awaits project-scoped evidence |
| Possibly a 4.8 model | Family and exact identifier unconfirmed |
| Possibly Claude Sonnet 5 | Unconfirmed |

## Archival record

The transcript exporter preserves source-reported model fields and turn
metadata without inferring model identities. The release inventory will state
its session coverage, cutoff, exact identifiers, event counts, date ranges,
and safe links into the sanitized archive. It will distinguish source records
from remembered names even when their spelling looks similar.

The supplement will summarize confirmed model use, recorded task roles, and
coverage limitations. Original sessions remain in the restricted evidence
vault; publication-safe exports and hashes permit the disclosed chronology to
be audited without exposing private data.
