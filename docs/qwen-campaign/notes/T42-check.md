# T42 terminal theorem rewire candidate

Added the public import of `Stafford38.Geometry.SameWitness.OriginalPrimeAxis` and replaced only the proof body of `coordinate_axis_mem_smooth_fibre_closure` with a direct call to that wrapper. The theorem statement was extracted at the parsed theorem boundary before editing (not by fixed line numbers) and compares byte-for-byte after the edit. The following `coordinate_axis_mem_projective_conormal_directions` declaration compares byte-for-byte with HEAD.

Frozen statement SHA-256: `c2c4b5117f933835399e3370528b960c7c831e0216a51d1a16a6242e668b262e`

Lean build remains pending the controller’s Lean slot and T36 closure. The required terminal build has not run; T42 acceptance is pending.
