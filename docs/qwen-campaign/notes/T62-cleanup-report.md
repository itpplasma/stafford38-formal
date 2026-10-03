# T62 unreachable and duplicate geometry: static preparation

Snapshot: WT `HEAD` = `0340cf2b1601de7a8895c0b450d4bcbbb9867bed`, plus the per-file SHA-256 values below for the uncommitted campaign sources. This is a source-graph and statement review only. No Lean command was run, and no declaration is proposed for deletion in this campaign.

## Reachability

Starting from `Stafford38.lean`, `Solution.lean`, `FixedSourceSolution.lean`, `CorollaryChallenge.lean`, `PaperPairChallenge.lean`, and all 129 `tests/**/*.lean` files, the current source import graph visits 563 existing project modules. It contains 242 existing `Stafford38/Geometry` modules; 239 are reachable. The three currently unreachable files are:

- `Stafford38.Geometry.CommonOpenEvaluation`
- `Stafford38.Geometry.PaperLaurentArcTangency`
- `Stafford38.Geometry.PrescribedCompletionNonzeroConsumer`

The route graph is incomplete in this snapshot: `SameWitness/AffineFibreClosure.lean` imports `Stafford38.Geometry.SameWitness.CommonOpenColumns` and calls `commonOpenColumnsData_of_arc`, but `SameWitness/CommonOpenColumns.lean` is absent. The 239/3 counts cover existing files and do not certify closure of the planned source graph.

## Similar conclusions reviewed by eye

These groups each have fewer than 20 declarations. Their shared output does not by itself make them duplicate proof dependencies; the inputs, statement scope, or proof route differ.

1. The exact original-prime coordinate-axis closure statement occurs in `GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure` and `SameWitness.OriginalPrimeAxis.coordinate_axis_mem_smooth_fibre_closure`. Keep the existing `GeneralAsymptoticConormal` declaration as the public terminal theorem consumed downstream. The SameWitness theorem is its proof-route adapter, needed to keep the terminal module out of the closure module's import graph.

2. The smooth conormal-fibre axis conclusion also occurs in `GeneralConstantCoordinateAxis.coordinate_axis_mem_smooth_fibre_closure_of_coordinate_algebraic`, `ActualSameWitnessAffineFibreEndpoint.axis_mem_smoothConormalFibreProjection_closure_of_actual_columns`, `SameWitness.EndpointOfAlgHoms.axis_mem_smoothConormalFibreProjection_closure_of_algHoms`, `SameWitness.AffineFibreClosure.axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput`, and `GeneralTangentLimitCriterion.tangent_limit_affine_fibre_closure_of_directSummand`. These have distinct contracts: algebraic-coordinate branch; explicit conditional endpoint; abstract ring-map adapter; same-witness data bridge; and direct-summand tangent-limit input. Keep those layer boundaries. The reviewed technical endpoint owner remains `ActualSameWitnessAffineFibreEndpoint` per `definition-owners.md`; the new closure bridge is the campaign's target bridge, not a replacement endpoint.

3. `AffineConormalSpan.differentialCovector_mul` and `CanonicalVisibleDivisorFrameProduction.differentialCovector_mul` have the same statement; the latter delegates directly to the former. The registry already names `AffineConormalSpan.differentialCovector_mul` as canonical owner. The latter is a compatibility wrapper, so it is not a new route duplicate.

4. `CoisotropicTranslation.eval_affineFibreLinePolynomial` and `PaperHamiltonianFlow.eval_affineFibreLinePolynomial` have the same statement; the second delegates to the first. Keep the `CoisotropicTranslation` theorem as owner and retain the paper-flow API if its manuscript-facing name remains useful.

5. `AffineConormalSpan.affineConormal_coordinatePoint_isCommonZero` and `PaperHamiltonianFlow.affineConormal_coordinatePoint_isCommonZero` have matching binders and conclusion but distinct proofs: a finite differential combination versus finite successive Hamiltonian flows. Prefer `AffineConormalSpan` as the reusable algebraic owner; retain the flow proof only as an explicitly reviewed paper-route implementation. This is an owner decision, not authorization to remove either historical proof.

The candidate `ChartSetup`, `CoordinatePresentation`, `CommonOpenData`, `CommonOpenArcData`, `CommonOpenPositionData`, and `CommonOpenEtaleData` structures package different chosen data at successive same-witness stages. They reuse the registered normalization, selected-center, ground-point-output, and common-open owners rather than defining alternate rings or witness constructors. In `CoordinatePresentation`, `hzero` and `haxis` are reflexive equalities and are passed downstream as `rfl`; consider dropping those two fields in a later tidy-up if the accepted interface does not need them.

Static scan of the candidate route finds no `sorry`, `admit`, or axiom declarations, and no terminal theorem statement assumes closure membership. The original-prime wrapper branches through the existing algebraic-coordinate result or supplies the same-witness ground-point output and smooth-open existence to the closure bridge. This is source inspection only; it does not establish kernel acceptance or actual proof dependencies.

## Frozen candidate source snapshot

SHA-256 values identify exactly the drafts reviewed above. A missing source is recorded as such rather than inferred from its import line.

| Source | SHA-256 |
| --- | --- |
| `SameWitness/AwayFactorToAtPrime.lean` | `95263b7f01c0139900c0b53742c2cc5d44f4892dd9fec88332c66dcbcc8a23fd` |
| `SameWitness/AxisLiftFromGroundPoint.lean` | `f691c640061933ac4938bca2b9ee354a8936f3759edd93b9c09e6f385e003727` |
| `SameWitness/ChartGroundMap.lean` | `72295254fb508f4381b4f56b3d0de79fbe4cd096b0579f8f1bbd612cb9cad2fa` |
| `SameWitness/ChartSetup.lean` | `2dcb9b4f5e195cb1a24c4fc16f136f873ddfd48ae35e6d3dd130c48badbefc99` |
| `SameWitness/CoordinatePresentation.lean` | `16bdbe7f809e3ea17e1f53a449afb1b1e8d770c9700f40dfdca89e9c311ad7be` |
| `SameWitness/CommonOpen.lean` | `cb7ee17f23714b663514ca17126a7e8e4c37f9db41e5f6bb1f5fd84873fdf898` |
| `SameWitness/CommonOpenArc.lean` | `5a22db13faa9f1ba3f949f7fe6d09c48bbd24168e3b8e34c55b7d1aee616b489` |
| `SameWitness/CommonOpenPositions.lean` | `382fd5604a28ee6b17c8d4dac4f0cf4dc58bfc0aee6230605b0f52f4570bdbdc` |
| `SameWitness/CommonOpenEtale.lean` | `92cd5a40d072fad48a65ae53dd0825dfbaee0c1cac368a30e3c1b6c9727cedd0` |
| `SameWitness/CommonOpenColumns.lean` | missing |
| `SameWitness/EndpointOfAlgHoms.lean` | `690f8008bee2e7105d208306c91208f46c60d5e32de6040a9cfcda879d91a720` |
| `SameWitness/AffineFibreClosure.lean` | `8d78779253f128f9dd5c77f324b806dd87bcd7cf8039d0b99b451ad7424a0fb2` |
| `SameWitness/OriginalPrimeAxis.lean` | `b117060a59dc58e5aac5b59ece0974127354c3ceadaab63cbd8293a76b89b695` |
| `GeneralAsymptoticConormal.lean` | `a285b9f9744b88e197d791ff5a6df9ca63495eb541de934d3cfcbc2fe91a7cb0` |
| `OriginalPrimeCoordinateAvoidanceWitness.lean` | `a052c69a3712fc2c87a3c6420687fd71397c9af26ba82945d7ed06011a8836bb` |
| `GeneralConstantCoordinateAxis.lean` | `27165b7d40f36af754557f3302a056caf053f8051f08c8142903a1af9357d211` |
| `ActualSameWitnessAffineFibreEndpoint.lean` | `32d6cb82af078383adfe0a3cdfc5353e9635bc7fd90e85ee25cc82e6cb55f674` |

These hashes freeze the read-only T62 snapshot. Campaign workers were editing drafts concurrently, so the final acceptance pass must recompute hashes and reachability over its own frozen inputs.

## Pending final gate

Repeat reachability and duplicate review after T34 supplies the columns interface and T36/T41/T42 candidates are accepted. Then run the prescribed strict declaration-dependency guard (T43), because source imports do not prove that a declaration is in a terminal proof's kernel dependencies. No cleanup or promotion is authorized by this report.
