# Strict dependency inspection repair: scoped acceptance

The exact patch on public source `45037fbc16329df7a208eb3de91aca31d720f03c`
passed the actual strict production guard on scluster3129931. All four terminal
roots reached 54872, 54873, 54880 and 54902 declarations, with zero forbidden
hits and zero unavailable dependencies after 13 owner-loading expansions.
The earlier missing private Mathlib declaration body loaded successfully.
No theorem, statement, proof, dependency pin or resource cap changed.

The independent behavioral fixtures also passed: safe and required routes
were accepted, while hidden forbidden producers, incomplete bodies, missing
required producers, extra axioms and Challenge placeholders were rejected.
Luna independently reviewed the frozen patch against the pinned Lean APIs.
The environment inspection selects private visibility; a validated private
name supplies only its module owner for loading. An absent body still fails.
Diagnostic parsing now excludes embedded newlines and preserves full raw
output when requested. No incomplete dependency is exempted.

Base/patch: `45037fbc16329df7a208eb3de91aca31d720f03c` /
`899582b242d69ef2a790cceb39273778c14b763d6084e3577d29ea245e595490`.
Production log SHA-256: `d0211e38e3515c5bd521abaf3a762ba25a0459575bd9cef2942c5945892dd1a8`.
Fixture log SHA-256: `faa9faa6410088756a97185081ad02375210c7b703702851f23e2ee95059a732`.
Packet SHA-256: `2260cdeed55373165b8d6f2cf9e670f13fadf28400170c917de0a6247a597b1f`.

These are scoped source/behavior receipts. The same allocation continues
bounded main/alternative route checks; its terminal/drain and full raw logs
will be retained separately. The next immutable public source still requires
the complete repository verifier and all four actual Palomar comparisons.
All earlier failed run receipts remain preserved.
