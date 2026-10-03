# T36 bounded assembly repair

The T36 source now assembles the residue point and the two completed unit
series through `retainedClosureChartData`, a small adapter over abstract
normalization ring `B`. It receives the canonical T31 `coords.fFin`,
`coords.coeff`, the finite-type certificate, and the retained maximal point,
residue equivalence, formal-etale certificate, and units. Its local algebra and
scalar-tower dictionaries are installed only on abstract variables inside that
adapter, following PLAN 6.2.4. The T36 theorem body has no concrete
`Algebra`/`SMul`/`FormallyEtale` instance installation or `compHom`.

The T36 theorem statement was extracted from the PLAN.md code block and
compared byte-for-byte with the source signature: equal. Both signature SHA-256
values are `daa0a0566670eb1b752ceeffaff9c590cd239828051839f9bed14d96f792f6f2`.
The statement still includes its `hpoint` and `hsmoothOpen` inputs. The literal
consumer is unchanged and remains unconditional, deriving both inputs from
the existing producers.

T33 now exposes the stable `CommonOpenArcData` getters through its transport
record; T36 continues to use `arc.rhoU`, `arc.hgroundU`, and `arc.common`.
T35's maps and certificates remain the same T22 inputs. T36 source and
consumer hashes at this freeze:

| File | SHA-256 |
| --- | --- |
| `Stafford38/Geometry/SameWitness/AffineFibreClosure.lean` | `f1bd490fe370a955699d132d5f3896397e515f5b32504e68d4e707d326a435a8` |
| `tests/SameWitness/AffineFibreClosureConsumer.lean` | `abd7675321fc67fff024e800530810c9c17fa07b6334073fff6d2185d36c5f60` |

No Lean command was run for this change because Sol owns the exclusive Linux
slot. `git diff --check` passes. Module and consumer compilation, including the
consumer's `#print axioms`, remain pending.
