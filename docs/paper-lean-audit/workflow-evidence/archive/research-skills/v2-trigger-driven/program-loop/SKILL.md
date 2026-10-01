---
name: program-loop
description: Manage long-horizon work with durable mission state, executable tasks, milestone dependencies, and explicit continuation rules.
---

# Program Loop

Use for work with a terminal mission, durable project state, intermediate
tasks, and a need to continue after local success. This skill owns progression,
not domain knowledge.

## Activation and context

At cycle entry read the project map, active task, prerequisites, and declared
verifier. Load the full roadmap, ledgers, review protocol, and evidence record
only for integration or when the active task names them. Project-local state is
authoritative; never replace it with a generic skill state file.

## Fast cycle

1. Select one active `OPEN` task when a pool exists.
2. State its desired result, failure condition, scope, and verifier.
3. Do the smallest direct implementation, derivation, experiment, or check.
4. Run the declared verifier and classify exactly one outcome:
   `PASS`, `FAIL`, `BLOCKED`, `REFUTED`, `CONDITIONAL`, or `NO_PROGRESS`.
5. Persist only a result, blocker, decision, milestone change, or reusable
   artifact that must survive restart.

Routine work, ordinary failures, scratch derivations, and `NO_PROGRESS` need
no note or commit unless continuation depends on them.

## Integration

Integrate after a milestone pass or refutation, four verified deltas, three
`NO_PROGRESS` cycles, a conceptual block, an interface/dependency change, or
an explicit request. Then:

- reconcile state with actual verifier outputs;
- check prerequisites, scope, evidence, and unresolved review issues;
- promote only eligible tasks and retire stale or disproved routes;
- run the relevant regression once inputs or interfaces changed;
- select the next highest-information `OPEN` task.

Use `evidence-gate` and the required `parallel-luna` tier at promotion. Do not
turn a passing intermediate task into terminal mission success.

## Durable synchronization

A restart-relevant commit is complete only when pushed to the configured
upstream and the remote revision is verified. Scratch work need not be pushed.
If a required push fails, report the exact unpushed revision as `BLOCKED` or
`NO_PROGRESS`.

## Blocked leaves

A blocked leaf does not end the mission. Record the exact blocker if it must
survive restart, then select another independent `OPEN` leaf. If none exists,
use `bounded-exploration`; use `expert-escalation` only after its trigger.
`NO_USEFUL_CANDIDATE` ends one exploration episode, never the mission.

## Hard stop

Never self-declare a terminal hard stop. A `MISSION_HARD_STOP_PROPOSED` record
requires an exhausted open-leaf inventory, the required consultation and
independent review, and exact missing external inputs. Continue maintenance or
evidence acquisition afterward until the user, a terminal proof, or a terminal
refutation ends the mission.

## Forbidden pseudo-progress

Do not manufacture code, proofs, tests, notes, reviews, or workers to avoid
`NO_PROGRESS`. The controller alone changes authoritative state, integrates
work, and promotes claims.
