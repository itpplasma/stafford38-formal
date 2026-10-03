# Solution variant design and candidate record

Date: 2026-10-03. The initial sections record read-only source analysis. The
candidate section below records the bounded worktree implementation. No
challenge statement, verifier, or Comparator configuration was changed; no
build was run.

## Findings

The older proof is substantive and can be identified by its proof root, not by
the current challenge wrapper. At base `3214f5c8f336de67d3e90af0594f420a41e9056b`,
`Stafford38.Geometry.GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure`
calls `exists_groundConormalAxis_of_prime_coordinate_avoidance`, then derives
closure from `residue_mem_residueExtensionFibreClosure_of_laurent_generic`.
Its statement is the axis-in-smooth-fibre-closure proposition also used by the
new retained-witness proof. In the synchronized Qwen candidate,
`Stafford38/Geometry/GeneralAsymptoticConormal.lean` preserves that public
statement but delegates it to
`Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure`.
Therefore preserving the current public theorem alone would not preserve the
old route after this rewire.

The old route's dependency path to the challenge result is:

```
GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure
  -> GeneralCoisotropicExclusion.exists_zero_base_coordinate
  -> GeneralCoisotropicSets.exists_zero_base_coordinate_of_isFibreConical
  -> GeneralCoisotropicCanonicalAdapter.algebraicallyClosedCanonicalSupportVanishing_of_generalCoisotropic
  -> FoundationClosure.canonicalSupportVanishingViaGeneralCoisotropic
  -> UniversalAssembly.universalStatement_of_canonicalSupportVanishing
  -> Stafford38.universalStatement
  -> Stafford38Challenge.universalStatement (Solution.lean wrapper)
```

`Stafford38.universalFixedSourceStatement` uses the same closure input through
`FixedSource.universalFixedSourceStatement_of_canonicalSupportVanishing`.
The current top-level `Solution.lean` and `FixedSourceSolution.lean` are thin
wrappers; renaming or copying either wrapper while leaving its proof rooted at
the current `FoundationClosure` would be a false variant label.

## Smallest sound structure

Avoid cloning the large adapter and closure assembly. Factor the geometric
route into an explicit proof input at the first edge where it is consumed, then
thread that input through the existing exclusion/set/adapter assembly. The
input must be the full existing axis-in-smooth-fibre-closure theorem type (same
binders and conclusion as the theorem above), not a terminal support-vanishing
fact. Retain the current theorem names as wrappers around the retained-witness
input for the main route, and expose a second wrapper using a separately named
legacy generic/Laurent theorem proved with the exact old body. This gives the
two routes independently inspectable proof roots while sharing the downstream
coisotropic and Weyl assembly proofs.

Concretely, the candidate seam is a helper beneath
`GeneralCoisotropicExclusion.exists_zero_base_coordinate`: add an argument
`haxisClosure` with the exact implicit parameters `{k} [Field k] [IsAlgClosed k]
[CharZero k] {m} (hm : 0 < m) (I : PrimeSpectrum (MvPolynomial (Fin m) k))`
and hypotheses `havoid : ∀ y ∈ zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0`, returning
the coordinate-axis member of the vanishing ideal of `smoothConormalFibreProjection I.asIdeal`.
In the body, replace only the direct call at the current `hclosure` binding by
`haxisClosure hm qprime havoid`. Give the helper a route-neutral name and keep
the existing `exists_zero_base_coordinate` API as a wrapper passing the
retained-witness theorem. Add a parallel legacy wrapper passing the
generic/Laurent theorem. Thread those two result theorems through similarly
small wrappers at `GeneralCoisotropicSets` and the canonical adapter; the
underlying proofs in those files need not be copied.

The input's full proposition is:

```lean
∀ {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {m : ℕ} (hm : 0 < m)
  (I : PrimeSpectrum (MvPolynomial (Fin m) k)),
  (∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) →
  (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
    MvPolynomial.zeroLocus k
      (MvPolynomial.vanishingIdeal k
        (smoothConormalFibreProjection I.asIdeal))
```

The bridge wrappers must preserve their current result types: exclusion returns
`∃ q ∈ zeroLocus k J, q (.inl ⟨0, hm⟩) = 0`; the coisotropic-set wrapper
returns `∃ q ∈ W, q (.inl ⟨0, hm⟩) = 0`; and the adapter still returns
`AlgebraicallyClosedCanonicalSupportVanishing`. Only the input argument at
the call sites differs between the main and legacy variants. This pins the
new seam to exactly the geometric lemma being used and prevents it from
becoming an assumption of the terminal theorem.

At the assembly boundary, provide a second named support-vanishing theorem in
`FoundationClosure` which uses the legacy adapter route, then apply the already
existing `UniversalAssembly.universalStatement_of_canonicalSupportVanishing`
and `FixedSource.universalFixedSourceStatement_of_canonicalSupportVanishing`
to it under a distinct namespace such as
`Stafford38.GenericLaurentVariant`. The variant entry points can then remain
small, transparent wrappers with the exact challenge theorem statements:

```
Stafford38Challenge.universalStatement : UniversalStatement
Stafford38FixedSourceChallenge.universalFixedSourceStatement :
  UniversalFixedSourceStatement
```

Their proof bodies should refer to the `Stafford38.GenericLaurentVariant`
theorems. They must not import the main Solution modules. The ordinary
Challenge definitions remain the single statement owners where the packaging
and Comparator setup permits this.

## Comparator and guard implications

The checked-in Comparator configs are fixed to the existing module pairs:
`Challenge`/`Solution` and `FixedSourceChallenge`/`FixedSourceSolution`; the
launcher likewise accepts only those two filenames, and the local Palomar
policy checker hard-codes those exact configs. To compare the old route
separately, add explicitly labeled variant solution module(s) and config(s),
then extend the wrapper/checker and import-closure policy to admit those exact
roots. The solution theorem names stay the same because each Comparator run
compares isolated challenge and solution environments.

Whether a challenge copy is required depends on the Comparator source API's
module-pair contract. Current `check-import-closure.sh` only allows named
top-level modules and `check-palomar-policy.py` only validates the two current
pair configs. If a new solution root can be paired with existing `Challenge`
and `FixedSourceChallenge`, share them; otherwise add byte-identical challenge
copies and a declaration/statement identity check before admitting the new
pairs. Do not import a challenge from its solution. The challenge theorem
placeholder must remain the only allowed placeholder in each copied challenge.

Likely final local checks for each admitted pair are the existing ordered
workflow (`check-palomar-policy`, build both modules, import-closure checks,
Comparator/NanoDa/Lean kernel). For the variants, the decisive structural
guard is an axiom/dependency report showing the variant endpoint reaches the
legacy `exists_groundConormalAxis_of_prime_coordinate_avoidance` and Laurent
residue closure, and does not reach the retained-witness root. Conversely the
main endpoint should reach the same-witness closure root and not the generic
axis producer. The exact dependency-guard command should be set by the
controller after the route-neutral seam and public names are accepted; no
existing receipt covers these proposed variant roots.

## Limits

This is a source-level design, not a checked API patch. In particular, the
source policy, import guard, `lakefile.toml` target list, axiom reports,
Comparator export behavior, and actual closure of the alternate endpoint all
need verification after implementation. Keep the historical `3214f5c` proof
body and its receipt as provenance; neither certifies the new variant package
until the new source is independently checked.

## Bounded worktree candidate

The implementation is in worktree `/home/ert/proj/stafford38-qwen`, based on
`8fa692f4f72c4ff01f4c0d22ff4dd5be6cd22ba7`. The task-owned patch digest is
`74099619fcc7f18e3a20b36536e830a2c3107482876f6afe62b8f75409785b37` (17,465
bytes across the seven assigned paths; unrelated concurrent SameWitness edits
are excluded).

The candidate preserves the generic/Laurent proof body in
`Stafford38/Geometry/AlternativeAsymptoticConormal.lean` under the distinct
namespace `Stafford38.Geometry.AlternativeAsymptoticConormal`. It factors the
old exclusion/set/adapter proofs through the full axis-closure input while
keeping their existing public main-route statements as wrappers around
`GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure`. Parallel
`genericLaurent` wrappers feed the historical theorem into the same existing
coisotropic, quotient-descent, UniversalAssembly and FixedSource APIs. New
entry files `AlternativeSolution.lean` and `AlternativeFixedSourceSolution.lean`
target the unchanged challenge theorem names and do not import the main
solution files. The authorized source paths did not include `lakefile.toml`,
so the controller still needs to decide whether to add explicit Lake roots for
these entry modules before running `lake build`/Comparator.

Task-owned modified source hashes:

| Path | SHA-256 |
| --- | --- |
| `Stafford38/FoundationClosure.lean` | `c476f050bf7467aaa86d6ea864ab60449531d3ff68e4419a278f45994ae144fc` |
| `Stafford38/Geometry/GeneralCoisotropicCanonicalAdapter.lean` | `4dfd046eaf9178cc0f27638df1ce51aa47906c88a049a5c7c5dd78f5f1157c67` |
| `Stafford38/Geometry/GeneralCoisotropicExclusion.lean` | `6ed7a44993cdc3a29bd804cd2b41f0642bc99106ab7deccd63a0e8720ccb118a` |
| `Stafford38/Geometry/GeneralCoisotropicSets.lean` | `a1b7acad72aead9ddfb6fa7c818a80e3f64ed5a1b4fda1ebf0fe719369e18e4e` |
| `Stafford38/Geometry/AlternativeAsymptoticConormal.lean` | `dbe77240848663aed1351c01df92156cf44dad07acd24ec7e343d581c8ef7971` |
| `AlternativeSolution.lean` | `5c04ea38945c3d8b6d13962276475a6535d21bd003e8e39f3b6aba058e260f18` |
| `AlternativeFixedSourceSolution.lean` | `84cc87243901736558ba2e87c764ef873de94409ca8e116a64dcf1e6b6b5c3e5` |

No Lean build was run, as requested while the controller's T32 slot is
occupied. This is a candidate only. The controller must compile both route
roots, verify unchanged statements and import DAGs, and run the independent
literal consumers and comparator/policy checks before acceptance. The
alternative endpoint must depend on the legacy generic axis and Laurent
residue closure, with no dependency on the retained-witness closure; the main
endpoint must show the converse route dependency.
