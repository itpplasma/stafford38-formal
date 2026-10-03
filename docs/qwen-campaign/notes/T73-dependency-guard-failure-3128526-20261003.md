# Final verifier dependency inspection failure

The resumed immutable public45037fb checkout passed exact source identity, all10dependency pins, tooling, cache and heavyEtaleprebuild. Its actual full library build passed4475jobs. The final verifier then failed the strict terminal dependency guard because referenced private Mathlib bodies were unavailable in the inspected public environment view. The permitted-axiom and forbidden-route checks were not bypassed; no full acceptance or comparator result is claimed. All four actual comparators remained unexecuted.

Job3128526 finished normally with command/guardexit1, peak3463704576bytes, zero swap growth, no stop cause or surviving children. Acceptance of scoped modules and assembly remains separate from this failed final verifier. The full build log and every completed verifier, stage and guard record are retained.

ArchiveSHA256: `f32daefa2bff445970e92e086d59e0d43055dcbbc837d4983c127ba45c80bf7d`. Sol identified the pinned Lean environment API’s public/private inspection switch and prepares a minimal guard repair, plus a marker-regex newline correction. The next bounded check exercises actual terminal inspection before any new frozen full verifier; no body/owner/axiom failure is permitted or ignored.
