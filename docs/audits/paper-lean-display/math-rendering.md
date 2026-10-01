# Euler issue math display

Map version 2026-10-01.5 marks the mathematical expressions in issue S5-05
and its suggested fix as inline TeX, rendered by the existing KaTeX path.
The issue previously used raw ASCII products and subscripts. The manuscript,
Lean source, other audit cards and renderer are unchanged.

A Chromium check of the regenerated HTML finds 13 KaTeX expressions in this
issue, including three in the suggested fix, and zero rendering errors.
The independently specified TeX for both product identities and the shift
identity matches the rendered formula annotations. The issue has no horizontal
overflow at viewport widths 1,400 and 600 pixels. Its screenshot was inspected.
Both product index ranges and the original-versus-corrected convention remain
explicit. The PDF was regenerated with the same corrected annotation.

The earlier verification.json describes the preceding all-card audit artifact;
its immutable hashes are historical and are not hashes of this refreshed HTML.
