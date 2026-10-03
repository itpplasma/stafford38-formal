# T32 CommonOpen candidate

The candidate is in `WT/Stafford38/Geometry/SameWitness/CommonOpen.lean` with
its literal consumer in `WT/tests/SameWitness/CommonOpenConsumer.lean`.
`CommonOpenData` is parameterized by the accepted `ChartSetup` and
`CoordinatePresentation`; `nonempty_commonOpenData` consumes the retained
ground-point output and returns the maximal center, same axis lift, selected
quotient coordinates, common-open chart map, column identifications, and
factorization package.

The construction reuses `exists_axis_lift_of_groundPointChartOutput`,
`actual_witness_selected_chart_quotient_equiv`,
`actual_witness_selected_chart_q_coordinates_in_actual_algebra`,
`actualColumn_eq_chartImage`, `pointLocal_commonOpen_column`,
`q_column_commonOpen_coordinates`, and
`genericOpenBMap_base_eq`. The output retains the ring-map identity from
`Q → B → U` as the composite `Q → Cq → U`; it does not create a second
`Algebra Q U` action. The factorization conclusion is stored directly from
`commonOpen_factors_ne_zero_of_tiltedProduct` for T33 to unpack.

The coordinate quotient step and common-open map step are split into named
lemmas so the main construction only assembles the axis lift with those two
outputs. The ring aliases `g`, `Cq`, `U`, `qU`, `qT`, and `φ` are reducible
namespace definitions computed from the stored data, not default-valued record
fields; this keeps every `CommonOpenData` value tied to the canonical maps.
The current source SHA-256 is
`0d1c0cd2c03c91f352377cfdcc175c77d42c991ce51b4c753cf4203695594308`; the
consumer SHA-256 is
`fdd4982c7e63eca36b5c1bd6eed51957dbec7f698fa1b74f576af64e8169d757`.

The residue equivalence retains the explicit coefficient-induced `Algebra k B`.
The hEtM certificate and the arc/axis data carry the exact `fFin`-induced
`Algebra R B`, scalar tower, finite-type structure, and point-local map
context from the ground-point chart output. No extra closure, smoothness,
column, or avoidance premise is introduced.

Lean execution is pending the controller's exclusive queue slot. The
consumer must report only `propext`, `Classical.choice`, and `Quot.sound`.
