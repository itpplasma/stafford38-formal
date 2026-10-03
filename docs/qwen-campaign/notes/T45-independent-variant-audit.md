# T45 independent variant audit

VERDICT: PASS

REVIEWED SCOPE: Frozen seven-path candidate from `/home/ert/proj/stafford38-qwen`, based on `8fa692f4f72c4ff01f4c0d22ff4dd5be6cd22ba7`, assigned-patch SHA-256 `74099619fcc7f18e3a20b36536e830a2c3107482876f6afe62b8f75409785b37` (17,465 bytes). I recomputed the digest over the four tracked modified paths plus the three new paths; it matches. Review covers the shared coordinate-axis closure seam, its coisotropic and canonical-support consumers, and both new challenge entry modules. No source changes, Lean execution, SSH, or host compute were used.

FIRST BAD BRIDGE: none found in the reviewed source-level proof path.

EVIDENCE:

- `CoordinateAxisClosureInput` quantifies over every field `k` with `[IsAlgClosed k] [CharZero k]`, every positive `m`, every prime point `I`, and every avoidance hypothesis. Its conclusion is the full original coordinate-axis membership in the vanishing ideal of `smoothConormalFibreProjection I.asIdeal`.
- `exists_zero_base_coordinate_using` and `exists_zero_base_coordinate_of_isFibreConical_using` take that complete proposition as an explicit argument and invoke it at the prime and avoidance proof obtained inside the original arguments. The existing public theorems retain their prior statements and apply the seam with `GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure`; the generic/Laurent wrappers apply it with `AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure`.
- The canonical adapter's `_using` theorem takes the same full input and passes it to the set-level consumer. The two public adapters close that input with their respective named endpoints. `FoundationClosure.canonicalSupportVanishingViaGenericLaurent` supplies the generic/Laurent adapter to the existing quotient descent; `GenericLaurentVariant.universalStatement` and `universalFixedSourceStatement` then call the existing `UniversalAssembly` and `FixedSource` assembly theorems. No explicit axis-closure hypothesis remains in either terminal statement.
- `AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure` has the same statement and proof body as the historical `GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure` at `3214f5c8f336de67d3e90af0594f420a41e9056b`; the namespace and surrounding module documentation differ. Its proof still obtains the generic extension and Laurent witness from `exists_groundConormalAxis_of_prime_coordinate_avoidance`, transfers vanishing through scalar extension, applies the residue-fibre-closure result, and specializes the residue column. The historical projective-direction corollary is not needed by this shared consumer.
- The new challenge wrappers target the existing `UniversalStatement` and `UniversalFixedSourceStatement` types. The existing challenge definitions and `Solution.lean` / `FixedSourceSolution.lean` are unchanged from the candidate base. The new entry files do not import the main solution files, and their proof terms call `Stafford38.GenericLaurentVariant`.
- Source references distinguish the declaration routes: the main wrappers mention `GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure`; the variant wrappers mention `AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure`. `AlternativeAsymptoticConormal` itself contains no `SameWitness` reference. The shared adapter/exclusion modules import and expose both endpoints, so import reachability alone does not establish the terminal declaration route. The requested declaration-closure tooling is a separate check and was not run here.

REPLACEMENT ARGUMENT: none.

CONDITIONAL SUFFIX THAT SURVIVES: The exclusion, canonical-support reduction, quotient descent, and terminal assembly follow from either supplied full endpoint proposition, conditional on Lean accepting the edited sources and on the declaration-level route checks confirming the intended endpoint closure.

UNNECESSARY DEPENDENCIES: No unnecessary proof dependency is established from this bounded source review. The old projective-direction corollary is omitted from the retained variant because the consumer only needs the fibre-closure theorem.

NON-CLAIMS: This is a static proof-source audit, not kernel verification. It does not establish that the new modules compile, that their axioms are acceptable, that Comparator or import-closure checks pass, or that the alternative terminal declaration avoids the `SameWitness` declaration in its transitive proof closure. It says nothing about whole-proof correspondence to the manuscript.

REOPENING CONDITION: Reopen if the kernel build rejects the candidate, or if declaration-dependency tooling shows either terminal variant reaches the wrong coordinate-axis endpoint or leaves an unproved hypothesis in the terminal theorem. Preserve the first complete dependency path or compiler diagnostic for that review.
