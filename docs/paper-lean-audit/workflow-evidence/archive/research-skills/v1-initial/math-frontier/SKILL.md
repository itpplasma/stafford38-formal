---
name: math-frontier
description: Run a domain-neutral research workflow for open or conjectural mathematics, preserving claim status, counterexamples, proof obligations, formalization faithfulness, and reproducible artifacts.
---

# Mathematical Frontier Research

Use this skill for an open, partially open, conjectural, or frontier
mathematics problem where the project needs genuine research progress rather
than exposition, coursework, routine proof completion, or standard theorem
retrieval.

This skill is domain-neutral. It applies to algebra, analysis, geometry,
topology, combinatorics, number theory, logic, mathematical physics,
computational mathematics, and formal mathematics.

Use with:

    program-loop
    evidence-gate
    parallel-luna
    bounded-exploration
    expert-escalation

and any relevant domain skill such as:

    symbolic
    browse
    referee
    brain

It does not encode any theorem, ring, field, equation, project path,
formalism, or subject-specific convention.

## Activation

Activate when a mathematical project has an unresolved frontier leaf,
conjectural target, incomplete proof dependency, or competing mathematical
routes. Do not use for exposition, coursework, routine proof completion, or
standard theorem retrieval.

## Inputs

Before research begins, locate or create project-local records for:

- formal target;
- ambient objects and conventions;
- established results;
- claim ledger;
- failed routes and counterexamples;
- active frontier leaf;
- available tools;
- literature sources;
- computational or formal artifacts;
- decision log;
- terminal success and hard-stop conditions.

Project-local state is authoritative. Never overwrite it with generic skill
assumptions.

## Claim taxonomy

Every substantive mathematical statement must be classified as exactly one:

    LITERATURE
    ESTABLISHED
    DERIVED
    FORMAL
    COMPUTATIONAL
    CONDITIONAL
    CONJECTURAL
    REFUTED
    OPEN
    BLACKLISTED

Definitions:

- LITERATURE: externally sourced theorem; exact statement and hypotheses
  still require verification in the current setting.
- ESTABLISHED: already accepted in the project with evidence.
- DERIVED: proved in the project from established facts.
- FORMAL: mechanically checked proof artifact.
- COMPUTATIONAL: actually executed finite, symbolic, or numerical result.
- CONDITIONAL: valid only under displayed unproved hypotheses.
- CONJECTURAL: proposed route or statement.
- REFUTED: disproved by an exact counterexample or fatal inference.
- OPEN: current unresolved dependency leaf.
- BLACKLISTED: known invalid inference pattern or route not to replay
  without new external input.

Never silently promote between categories. In particular:

    COMPUTATIONAL != DERIVED
    FORMAL statement validity != informal theorem faithfulness
    special case != universal theorem
    conditional implication != proof of its hypothesis
    literature theorem != verified applicability

## Workflow

Use one research mode per fast-cycle task. Every mode must preserve the active
leaf, record evidence, and return a verifier-bearing next action.

### FOUNDATION

Use for definition audit, convention and side-condition repair, exact
literature extraction, claim classification, theorem-statement
formalization, and dependency-graph construction.

Before attacking a new frontier leaf:

1. Freeze the exact theorem statement: quantifiers, domains, conventions,
   side conditions, ambient structures, permitted tools, and terminal success
   condition.
2. Audit the claim ledger: established, conditional, failed, blacklisted, and
   active-leaf entries.
3. Identify the first unresolved dependency, not merely a restatement of the
   terminal theorem.
4. Write a falsification condition for the proposed route before investing in
   a proof attempt.

If these cannot be stated precisely, the active task is foundation work, not
proof work.

### EXPERIMENT

Use for symbolic checks, finite enumeration, numerical experiments,
counterexample search, low-order examples, test-instance generation,
parameter sweeps, and conjecture discrimination.

Rules:

- define success and failure criteria before execution;
- record input, command, environment, and output;
- state precisely what the finite result establishes;
- never call experimental evidence a proof;
- prefer counterexample search before broad proof machinery.

Valid outputs include an exact counterexample, bounded positive certificate,
bounded negative result, candidate invariant, discriminating family, or
reproducible data artifact.

### PROOF

Use for one precise lemma, a special-class theorem, a consequence of
established hypotheses, a no-go result, or a formal proof artifact.

Rules:

- state all assumptions;
- stop at the first unsupported inference;
- isolate that inference as a new OPEN leaf;
- do not replace it with suggestive prose;
- separate theorem statement, proof, and scope.

Valid outputs include a proved lemma, special-case theorem, exact reduction,
no-go theorem, formal proof, or conditional theorem with its missing
hypothesis displayed.

### REVIEW

Use for adversarial audit, counterexample attempt, proof-gap detection,
side-convention audit, theorem-faithfulness audit, reproducibility audit, and
literature-hypothesis checks.

Valid outputs include PASS, a first fatal flaw, a counterexample, a missing
hypothesis, an invalid theorem statement, or an evidence gap.

### SYNTHESIS

Use only during integration cycles to update the dependency DAG, promote or
reject routes, compare evidence, identify the highest-information next leaf,
and prune obsolete work. SYNTHESIS does not create new proofs or claims.

## Valid outputs

Every mathematical fast-cycle task must produce exactly one of:

    PROVED
    FORMALIZED
    COMPUTED
    REFUTED
    CONDITIONAL
    BLOCKED
    NO_PROGRESS

It must include the active leaf, research mode, exact statement or experiment,
evidence, scope, first remaining blocker, claim-ledger update, and next
executable task.

## Verification

For experiments, record the command, environment, inputs, outputs, and exact
finite scope. For proofs, state every assumption and isolate the first
unsupported inference. For literature, retrieve the exact theorem, source,
edition or version, page or section, hypotheses, checked applicability, and
remaining gap.

When using Lean or another proof assistant:

1. formalize the exact intended statement before treating the proof as
   evidence;
2. record imported axioms and nonstandard definitions;
3. use auxiliary lemmas as unit tests for definitions and interfaces;
4. perform a faithfulness audit of quantifiers, sides, domains, and
   assumptions.

A compiling proof of the wrong theorem is INVALID.

## Forbidden pseudo-progress

Do not silently promote a computation, special case, conditional implication,
or literature citation into a universal theorem. Do not create proof-shaped
prose, formalize a changed theorem without recording the change, replay a
blacklisted inference without new input, or stop after a bounded experiment
merely because it produced a plausible pattern.

Before a general proof route, search for low-dimensional boundary models,
smallest parameter cases, degenerate inputs, symmetry-breaking cases,
counterexamples to proposed implications, failures of side or quotient/lift
passage, failures of uniform degree/rank/bound claims, and examples requiring
an excluded hypothesis. An exact counterexample is successful progress and
marks the relevant inference REFUTED or BLACKLISTED.

## Escalation

Trigger bounded-exploration when the frontier stagnates and its conditions
are met. Trigger expert-escalation only after bounded exploration or two
materially distinct failures, and treat every consultation as CONJECTURAL
until independently verified. A reviewed hard stop must identify the exact
missing theorem, construction, computation, or human decision.

## Composition

Use program-loop to select one active frontier leaf, a relevant domain skill
to perform the task, evidence-gate to classify its result, and parallel-luna
for adversarial review. Use bounded-exploration for new routes and
expert-escalation only at a genuine conceptual block. One controller
integrates claim-state changes serially.

## Parallel work policy

Safe parallel work includes independent counterexample searches, literature
searches for distinct hypotheses, proof-gap audits, separate formalization
attempts for a frozen statement, symbolic computation versus hand derivation,
independent low-order experiments, and review of proof statement versus proof
steps.

Unsafe parallel work includes multiple agents editing the claim ledger,
competing rewrites of the active theorem statement, proofs based on mutable
definitions, agents promoting their own conjectures, or edits to the same
formalization artifact. Freeze inputs and use one controller for all claim-state
changes.

## Candidate route protocol

When a new conceptual route is needed:

1. Generate several qualitatively distinct routes privately.
2. Reject routes that restate the active leaf, assume the desired conclusion,
   revive a blacklisted inference, lack an executable or formal discriminating
   test, or have no clear scope.
3. Rank remaining routes by expected information gain, relevance to the active
   leaf, falsifiability, and feasibility, divided by duplication risk.
4. Promote at most one route into an active task.
5. Preserve rejected routes and reasons in the decision log.

## Integration cycle

During the program-loop integration cycle:

1. Re-read the terminal target.
2. Reconcile claim states with artifacts and reviews.
3. Run relevant formal, symbolic, computational, or regression checks.
4. Promote only verified dependency leaves.
5. Retire duplicate routes, disproved routes, routes dependent on rejected
   assumptions, and special cases subsumed by stronger theorems.
6. Select the next leaf by expected information gain.
7. Trigger bounded-exploration if the frontier stagnated.
8. Trigger expert-escalation only under its defined conditions.

## Completion rule

Do not stop after a special case, counterexample to one route, formal lemma, or
bounded experiment. Continue until the terminal theorem is fully proved with
checked dependencies, fully refuted, or a reviewed hard stop identifies the
exact missing theorem, construction, computation, or human decision.
