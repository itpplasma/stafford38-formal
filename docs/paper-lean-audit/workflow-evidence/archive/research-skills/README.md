# Research-method skill archive

This directory preserves the research-control prompts that shaped the Stafford
program. The files are verbatim snapshots from
[`krystophny/prompts`](https://github.com/krystophny/prompts), whose CC0 1.0
license is reproduced here. They are historical evidence, not active agent
instructions for this repository. `AGENTS.md`, `PLAN.md`, and the current
formalization coverage remain authoritative.

## Snapshots

| Directory | Prompts commit | Contents | Reason retained |
|---|---|---|---|
| `v1-initial` | `8b5ca3fbb6ce251c93f2a109ed1a1dbaba691089` | Initial six-skill research operating system | Preserves the original, more elaborate program lifecycle |
| `v2-trigger-driven` | `0e95c6c6e80b1bb2fabacab714d2bd74d3b9bf47` | Trigger-driven versions of the same six skills | Records the first major simplification |
| `v3-scoped-promotion` | `8d732a9202999edab5442f42c7da7eaf5e3f625f` | The four skills changed by frozen-packet and scoped-promotion rules | Preserves the final integrated suite before lifecycle skills were removed |
| `v4-proof-repair` | `48c4c90c888115995d4bc552250e4d4f3af44809` | Current `math-frontier` and new `proof-audit` | Records the process distilled from the successful proof cycle |

The six-skill suites consist of `program-loop`, `math-frontier`,
`evidence-gate`, `parallel-luna`, `bounded-exploration`, and
`expert-escalation`. Version 3 stores only files whose contents changed from
version 2. Version 4 reflects the later decision to fold lifecycle mechanics
into a smaller frontier skill and to separate proof auditing.

## Exclusions and safety

Private prose-treatment and unrelated operational skills are excluded by
design. The archive also omits mail, local service configuration, source
documents, and private machine data. Before promotion, every retained snapshot
was scanned for local paths, private hostnames, secrets, activation data,
proprietary-software details, and source-document references.
`CHECKSUMS.sha256` fixes the exact archived bytes.
