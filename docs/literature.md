# Literature and proof index

This index is for readers tracing the theorem from its source problem through
its mathematical ingredients to the checked declarations. A bibliographic
reference identifies ancestry or a theorem being implemented; the imported
Lean declarations, with their explicit hypotheses, determine proof dependence.

## Reading order

Start with Stafford’s Conjecture 3.8 [Sta78], then the two
[formal statements](../Stafford38/FixedSourceStatement.lean), the
[proof guide](proof-guide.md), and the [proof graph](proof-graph.yaml).
The [correspondence](paper-lean-specification.md) relates the internal exposition
to Lean. The [dossier PDF](dossier/stafford38-challenge-dossier.pdf) includes the
clickable map and a bibliography. Internal manuscript drafts are records of
this research development, not separately published literature.

## Sources mapped to the proof

| Ingredient and role | Literature | Lean entry points |
| --- | --- | --- |
| Original conjecture; ordinary and exact-degree endpoints | [Sta78](#sta78); the exact-degree strengthening belongs to this project | [Statement](../Stafford38/Statement.lean), [FixedSourceStatement](../Stafford38/FixedSourceStatement.lean), [FoundationClosure](../Stafford38/FoundationClosure.lean) |
| Symplectic monicization and right Euler division | Ore/PBW background [Ore33](#ore33); project certificate calculation | [MonicNormalization](../Stafford38/Weyl/MonicNormalization.lean), [EulerRemainder](../Stafford38/Weyl/EulerRemainder.lean) |
| Filtered support avoidance | Characteristic-variety background [HTT08](#htt08); the exact localized Koszul argument is proved here | [CanonicalKoszulContradiction](../Stafford38/Characteristic/CanonicalKoszulContradiction.lean) |
| Radical involutivity | Classical theorem [Gab81](#gab81), implemented for cyclic Weyl quotients | [GabberGlobalAssembly](../Stafford38/Characteristic/GabberGlobalAssembly.lean) |
| Visible frame → finite-gradient certificate → conormal axis | Project geometry; conormal context [HTT08](#htt08) | [ExactDivisorialVisibleFrameExistence](../Stafford38/Geometry/ExactDivisorialVisibleFrameExistence.lean), [FiniteGradientResidueExtension](../Stafford38/Geometry/FiniteGradientResidueExtension.lean), [GeneralConormalAxis](../Stafford38/Geometry/GeneralConormalAxis.lean) |
| Coisotropic exclusion and certificate extraction | Consumes the proved involutivity and project geometry above | [GeneralCoisotropicCanonicalAdapter](../Stafford38/Geometry/GeneralCoisotropicCanonicalAdapter.lean), [CanonicalCertificate](../Stafford38/Characteristic/CanonicalCertificate.lean) |
| Intrinsic differential-operator corollaries | Definition background [StacksD](#stacksd) | [LocalizedDifferentialCorollaries](../Stafford38/LocalizedDifferentialCorollaries.lean) |
| Status and constructive neighboring results | [Bel26](#bel26), [Ley04](#ley04) | Context only; no import edge |

The tangent-limit criterion is a separately checked auxiliary result. It has
no edge into the terminal visible-frame/finite-gradient route. The graph marks
that distinction explicitly. None of the general conjecture, exact-degree
strengthening, Euler certificate, or visible-frame construction is attributed
to a textbook merely because its vocabulary is standard.

## Formal foundations

The manifest pins Mathlib at `db584cd6d46c92f209a44c0f1c829460d327499d`
and AlgebraicAnalysis at `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`.
See the [AlgebraicAnalysis source index](https://github.com/itpplasma/algebraic-analysis/blob/main/docs/literature.md)
for the Ore/PBW, filtered-module, localization and differential-operator APIs,
and [provenance](provenance.md) for extraction history. Documentation on main
can evolve; the manifest and verification report determine the consumed code.

## Bibliography

<a id="sta78"></a>

**[Sta78]** J. T. Stafford, *[Module Structure of Weyl Algebras](https://doi.org/10.1112/jlms/s2-18.3.429)*, Journal of the London Mathematical Society (2) 18 (1978), 429–442.

Source of Conjecture 3.8 (p. 438). The 1978 conjecture is the target, not a proof of its general case.

<a id="bel26"></a>

**[Bel26]** Gwyn Bellamy, *[Module structure of Weyl algebras](https://doi.org/10.1112/jlms.70373)*, Journal of the London Mathematical Society 113 (2026), no. 1, e70373.

Historical status and adjacent results, especially Sections 3 and 6; not an imported proof theorem.

<a id="gab81"></a>

**[Gab81]** Ofer Gabber, *[The Integrability of the Characteristic Variety](https://doi.org/10.2307/2374101)*, American Journal of Mathematics 103 (1981), no. 3, 445–468.

Classical involutivity theorem. The required Weyl-quotient version is proved in Lean by the Gabber block; the citation is not an axiom.

<a id="htt08"></a>

**[HTT08]** Ryoshi Hotta, Kiyoshi Takeuchi, and Toshiyuki Tanisaki, *[D-Modules, Perverse Sheaves, and Representation Theory](https://doi.org/10.1007/978-0-8176-4523-6)*, Progress in Mathematics 236, Birkhäuser, 2008.

Background for differential operators, good filtrations and characteristic varieties (Chapters 1–2). No claim of a line-by-line formalization of this book.

<a id="ore33"></a>

**[Ore33]** Øystein Ore, *[Theory of Non-Commutative Polynomials](https://doi.org/10.2307/1968173)*, Annals of Mathematics (2) 34 (1933), no. 3, 480–508.

Historical foundation for skew polynomial rings. The library implements the derivation case with explicit coefficient order, rather than all skew-polynomial generality.

<a id="stacksd"></a>

**[StacksD]** The Stacks Project Authors, *[Finite order differential operators](https://stacks.math.columbia.edu/tag/09CH)*, The Stacks Project, Section 10.133, tag 09CH (accessed 2026-09-09).

Background for the recursive commutator definition and localization of finite-order differential operators; Lean implementations and hypotheses are indexed below.

<a id="ley04"></a>

**[Ley04]** Anton Leykin, *[Algorithmic Proofs of Two Theorems of Stafford](https://doi.org/10.1016/j.jsc.2004.07.003)*, Journal of Symbolic Computation 38 (2004), 1535–1550.

Constructive prior art for classical Stafford results; not a proof source for the general Conjecture 3.8 or exact-degree strengthening.
