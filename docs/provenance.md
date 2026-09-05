# Provenance

Formal commit `219668ef77b4ffddc1a503fd1ce61dbd48aa4b17` was checked from an independent clone; its
[verification record](verification-results.json) is `df7c23125820af9a23e8c2f01e4fa9873341f2d29be6dc46eb833180d183166a`.
The Stafford sources derive from signed private source commit
`8cc7802cd4355d819d2df4f680ba26d4a339f80e`, which passed the complete
229-checker manuscript regression. The canonical repository is a clean source
snapshot, with source inventory and extraction correspondence retained.

## Ownership

| Repository | Authority |
| --- | --- |
| [algebraic-analysis](https://github.com/itpplasma/algebraic-analysis) | Public reusable mathematics, pinned at `2fdc928835347a2638b6c85a4bfa770e3f70ed9e` |
| [stafford38-formal](https://github.com/itpplasma/stafford38-formal) | Public canonical Stafford-specific proof, Palomar interface, and reproducibility documentation |
| [stafford38-paper](https://github.com/itpplasma/stafford38-paper) | Private synchronized backup of the Overleaf manuscript authority |
| [stafford38](https://github.com/itpplasma/stafford38) | Private research history and provenance archive |

Stafford compatibility wrappers preserve the Stafford API while importing the
single reusable implementation from AlgebraicAnalysis. No implementation of
that external library is vendored here. The ownership model assigns active
Stafford proof sources to this formal repository and research history to the
private archive. Retirement of the research workspace's former active copies
is a separate cutover transaction, certified by its external receipt. Neither
the research workspace nor the paper repository is a build input.

## Manuscript correspondence

The paper mirror at `b3f3edf0741b6a70b6e5011690e16bf58561cffb` was verified
as synchronized with Overleaf. The manuscript, bibliography, and proof-map
supplement remain under that separate authority. This formal package includes
the [statement correspondence](paper-lean-specification.md), without copying
the manuscript sources. No public preprint or arXiv identifier is assigned.

J. T. Stafford's *Module structure of Weyl algebras*, Journal of the London
Mathematical Society (2) 18 (1978), 429–442, is the source of Conjecture 3.8.
It supplies historical attribution, not the new proof. The formal development
proves its required mathematical inputs from Lean and Mathlib, retaining no
literature axioms.

## Dependencies and assistance

The project uses Lean `4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and AlgebraicAnalysis
`2fdc928835347a2638b6c85a4bfa770e3f70ed9e`. Exact verification-tool revisions
and the separate Comparator toolchain are recorded in [verification](verification.md).

Christopher Albert is the recorded human author and maintainer. AI assistance
supported mathematical research, Lean development, counterexamples, and scoped
reviews. [`formalization.yaml`](../formalization.yaml) preserves the model
identifiers corroborated by project metadata and describes the limits of that
record. Assistance does not assign authorship of an idea. Human direction and
release authority are distinct from independent human expert review; no
completed expert review or journal acceptance is claimed.

## Licenses

Formal code and documentation are Apache-2.0. Dependency licenses and
attributions remain with their respective projects; [NOTICE](../NOTICE)
records the adapted Palomar wrapper. The separate manuscript and supplements
remain CC BY 4.0. No research conversations, private correspondence, third-party
literature files, or generated manuscript artifacts form part of this package.
