# GPT-Sol consultation protocol

GPT-Sol is an independent advisory consultant, not an evidence source.

The controller uses the installed `expert-escalation` skill for the gate and
`bounded-exploration` before escalation. Ordinary work and ephemeral Luna
micro-reviews do not trigger a consultation.

## Escalation gate

Use GPT-Sol only after two materially distinct falsifiable attacks on the
same conceptual open leaf fail, or when the specification is genuinely
underdetermined. Do not use it to generate more boundary prose or to avoid a
declared verifier.

## Packet

Use `notes/history/sol-consult-template.md` and include:

- exactly one open task ID and statement;
- established facts with repository paths and statuses;
- both failed attempts and their exact counterexamples or missing hypotheses;
- all blacklisted inferences;
- the requested executable next action.

Request at most three genuinely distinct mechanisms. For each mechanism,
require an exact intermediate lemma, noncircularity explanation, adversarial
test, first bottleneck, and one action executable by Codex, Lean, M2, or a
literature audit.

## Verification gate

Treat every response as untrusted advice. Codex must independently execute a
new central test or verify the cited theorem and all hypotheses. GPT-Sol advice
cannot itself close or promote a task. Luna review remains mandatory for any
result produced after consultation.
