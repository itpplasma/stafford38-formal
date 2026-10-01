# Independent review: 19-card audit display

## Frozen inputs and checks

- Formal worktree: clean `87bce83806c757ade36d455d785b506ebd03a1b2`.
- Paper snapshot: `e2b0b9fbca4cab61a4a3462ef4289726592de5ca`, `human_readable_main.tex` SHA-256 `e64c5bc0af5876ad8c430f2e8b7bd1012474786d2ab90060501ff8d69911b065`.
- Lean source links: formal `591d4e11e3971577be169e428ac73c44a4ac8a32`; AlgebraicAnalysis `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`.
- Reviewed `/tmp/stafford-audit-display-review-2.json` (SHA-256 `54a9e0c7b2df43e64bc8b99c97cc9993ff9c62508110ed80d24f2e0dc946369c`) and generated HTML (SHA-256 `9ba75eede2022262009f46beef82b64392543d404db5486f7b3cfb9495291c39`). All 100 Lean source references in the 19 cards resolve to the named declaration near the advertised line in the pinned formal/library commit.

## Material display/map repairs

1. **Split paper excerpt (`eq:I-Q`, `euler-grading`).** The ranges `[759,762]` and `[763,784]` cut one `\AIadd{\formalref...}` across cards. In the generated HTML, the I/Q card drops its formal-definition annotation and the Euler-grading card visibly starts with the orphan `= span{d,x^Nd}`. Use I/Q `[759,763]`, Euler `[765,784]`.

2. **Lemma 6.2 route/status.** `lem:tangential-finiteness` is correctly linked to formal finiteness/support/length results, but its `route:same` badge overstates the visible paper proof. The excerpt at lines 965–975 stops at “Since they are annihilated by” and resumes without the missing argument. The ALG-04 comment at 983–992 says a corrected red block follows, but no such block is present in the pinned source/card. Keep the paper proof flagged open; classify the route `similar` at most (the intended Hopfian/support argument is related), and amend the comment/card to say the detailed correction is not included. Do not describe the current excerpt as a complete proof.

3. **Lemma 6.4 route badge.** `lem:strict-support-inequality` says `route:same`, while its own AI addition (lines 1225 onward, just after the card’s range) says the first Gabber step differs: Lean proves involutivity directly for minimal primes rather than using `ithm:gabber` plus `lem:componentwise-involutive`. Use `route:similar` as planned.

4. **Remark 4.3 is not an exact statement-level link.** `rem:transport` is a prose transport observation, but the map gives `statement:exact`, `route:same` and links the whole final assembly theorems at `FixedSourceAssembly.lean:21` and `UniversalAssembly.lean:66`, plus a generator inverse simp lemma. Those links do not declare the displayed identity as a standalone transport result. Mark it `n/a` (prose/no separate proof claim) or `partial`, and label the assembly declarations as downstream context; otherwise add/map an explicit transport lemma.

5. **Definition 6.1 “not formalized” badge is misleading.** The card has `statement_relation:none` and an empty Lean list, while its paper-side annotation says Mathlib `Module.length` / `IsFiniteLength` are used. The pinned page inequality at `CanonicalPageEulerInequality.lean:22–28` uses `Module.length`; Mathlib defines it in `Mathlib/RingTheory/Length.lean:32`. Link that library definition (and the finite-length predicate/result) and mark the concept `exact`/`equivalent`, or narrow the badge wording to “no project-local declaration; standard Mathlib notion used.”

6. **Lemma 5.2 source model needs to be explicit.** The linked `presentedPositiveEulerResidue` at `EulerRemainder.lean:402–408` takes presented `d` but its conclusion lives in `pairEulerSubring (IteratedPairStage ...)` and `canonicalRightIdeal` in the iterated Ore model. The direct paper statement is in the presented Weyl algebra. Explain that the residue identity is established in the Ore model and transported, or classify it `equivalent` and link the transport. The following Proposition 5.3 card already explains that the final surjectivity result is transported.

7. **Conormal-definition card has an unlinked named definition and a prose defect.** `dir-def` correspondence mentions `smoothConormalFibreProjection`, but its Lean links omit that definition (`ProjectiveConormalDirections.lean:44–48`). Add that link if retaining the downstream-use note. In the paper excerpt, lines 1329–1330 currently read “... holds and / homogeneous coordinates ... and embed”; supply a verb (“Choose homogeneous coordinates...”) or recast as a complete sentence.

## Per-card disposition

| Card | Review |
|---|---|
| `prop:monic` | Statement/source match: `HasNormalizedSymplecticChart` plus `IsPBWMonicAt` records the normalized image and coefficient. The card’s equivalence note about the right-form degree bound is accurate. Keep the major issue open pending author acceptance: the corrected proof is an `\AIreplace` proposal, not accepted text. |
| `reduction-k0` | Match: the proposal uses algebraic closure and the formal descent result; it distinguishes the proposed field-handling text from accepted prose. |
| `rem:transport` | See repair 4. |
| `def:monic-xi1` | Match: the paper definition is standard polynomial monicity; the formal normal-symbol polynomial and monicity theorem are appropriate references. |
| `lem:order-symbol` | Match: linked fibre-only, homogeneous, pure-momentum coefficient/axis evaluation results support the paper conclusion under `IsPBWMonicAt`; the card explains the changed hypothesis encoding. |
| `eq:I-Q` | Match for the ideal/quotient definition; excerpt currently clipped by repair 1. The literal Lean right ideal is the span of `d` and `x^N d`. |
| `euler-grading` | Correspondence note accurately says Lean uses the generated subring and one-sided normality, not a formal Euler grading. Excerpt currently begins mid-annotation (repair 1). The paper’s claim that the whole nonnegative part is generated is still unsupported in this excerpt; preserve the open issue. |
| `lem:euler` | Public Lean product identities and the corrected red products match. `paper-wrong` is appropriate only as a flag for the original/blue formulas; keep the critical issue `open pending review` until the `\AIreplace` is accepted. |
| `lem:euler-residue` | Main Lean statement is a real result, but in the iterated Ore model (repair 6). The corrected root sets at paper lines 825–827 are still proposed `\AIreplace` text; retain acceptance-pending status. |
| `prop:x-surjective` | Match: the linked presented quotient theorem gives surjectivity of right multiplication by the coordinate, with the PBW-monic hypothesis explained. The card’s Ore-model proof/transport note is apt. |
| `vc-setup` | Match: the formal graded module, tangential coefficient ring, and coordinate map definitions are relevant; the index shift and field note are visible. |
| `def:length` | See repair 5. The finite-length correction in the excerpt addresses the old “finite module” issue. |
| `lem:tangential-finiteness` | Statement and declaration bundle match, but proof-route/status is misleading/incomplete (repair 2). |
| `lem:page-inequality` | Match: target ≤ source corresponds to paper’s `U≤V` through the linked first-page kernel/cokernel equivalences. Route `similar` is apt. Its two open issues remain material for the unaccepted paper proof; the red AI addition supplies a proposed formalized route, not an accepted rewrite. |
| `lem:strict-support-inequality` | Statement/declaration bundle matches through the generic localized Koszul inequality plus minimal-prime avoidance. Change `same` to `similar` (repair 3); the open Gabber/minimal-prime edit remains proposed. |
| `lem:Uzero` | Match: the Lean `Subsingleton` quotient is `U=0`. The cited finiteness lemma supports the contradiction; keep the minimal-support existence citation issue visible if unaccepted. |
| `cor:charP` | Match: initial-ideal membership and characteristic-support containment are linked. Existing field notation and forward-reference issues are still visible in the excerpt. |
| `prop:char-avoids` | Match: the prime-spectrum/transposed-support formulation is explained and the `xi↦−xi` transfer fixes `x₁`; the card’s equivalent badge is apt. |
| `dir-def` | Core ingredients match the conormal-direction definition (smooth points, annihilator of tangent space, projectivization, homogeneous closure). See repair 7. |

No source/manuscript edits, commits, or theorem-status changes were made during this review.

## Remaining scope in these 19 cards

No theorem statement in this subset was found to lack a Lean counterpart or a linked chain that entails it. The paper’s full Euler grading/nonnegative-part characterization is not defined as such in Lean; the card correctly documents the smaller generated Euler subring and one-sided normality used by the formal proof. Remark 4.3 has no standalone transport declaration, and the Lemma 6.2 paper proof remains incomplete/unaccepted even though its theorem is formalized. Lemma 5.2 is established in the iterated Ore representation and consumed by the transported surjectivity result.
