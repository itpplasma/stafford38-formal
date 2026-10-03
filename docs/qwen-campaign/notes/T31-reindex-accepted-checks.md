# T31 canonical reindexing repair receipt

The first T32 construction check exposed a missing relationship between the retained `fOption` and an arbitrary stored `fFin`. The accepted T31 repair computes `CoordinatePresentation.fFin` as the canonical composition with the selected index equivalence. It preserves the downstream dot API and removes recomputable data from the bundle. The public construction theorem and literal consumer statements are unchanged.

Input base: `fcd866f9dcf736d624b96a8fd5ea086ca910f9ad` plus the included source patch. Coordinate source SHA-256: `3ffef86177fc2e6b2d552264f47af08553823e4562ad58d51c65fb2cc6d29016`. Consumer SHA-256: `bfa1d18843c80f023f0c615d1a9ec43a3da62d7b90477247e2706a3d7bc0b5e1` (unchanged).

Linux guarded module and `--trust=0 -M 8000` consumer both exited zero, at peak 2507.6 and 4099.5 MiB respectively. The unchanged consumer reports only `propext`, `Classical.choice`, and `Quot.sound`. The independent Mac module build exited zero in 23 seconds at peak 2182 MiB, with one Lean thread and the original two-CPU/eight-GiB ceiling. No resource or heartbeat ceiling was raised.

The checked patch is included with complete logs and terminal Linux receipts in `T31-reindex-accepted-checks.tar.gz`, SHA-256 `108998df1fc9cca56411e44eda857c2a123ba32e7f0eb089d170782a803f8392`. This supersedes the current T31 source selection without rewriting the earlier historical receipts. T32 and the complete route remain under verification; this is scoped evidence only.
