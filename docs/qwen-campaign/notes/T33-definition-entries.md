# T33 definition entries for controller review

| Name | File | Why no existing owner fits |
| --- | --- | --- |
| `Stafford38.Geometry.SameWitness.CommonOpenArcData` | `Stafford38/Geometry/SameWitness/CommonOpenArc.lean` | Packages the selected point-local Laurent arc after extension to this construction's actual common-open localization, retaining canonical-map equalities and its ground-map and restriction equations for downstream consumers. Existing arc maps and generic-open transport lemmas own the maps themselves; none owns this same-witness package. |

This entry is provisional until the exact dependency on T32's
`CommonOpenData` structure is fixed. No existing registry entry is changed
by this worker.
