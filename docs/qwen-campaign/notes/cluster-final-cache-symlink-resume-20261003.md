# Bounded public-source resume after generated cache failure

The resume is restricted to the exact drained pre-verifier failure3131361
at publicC2 12ae3cc49152672a48a96f13994314b65ae38197. It requires all eleven
prior stages to have exited0, the exact generated-cache diagnostic, original
source identity and pins, normal drain/no survivors, and no prior verifier
or comparator stage. It reuses that public checkout and cache with a distinct
receipt directory. No source or manuscript pin changes.

The driver validates the generated `.lake` symlink's exact canonical contained
donor and requires it to be the only untracked path. It appends only `/.lake`
to Git's private metadata exclusion. Every tracked raw byte is then compared
with its Git blob, every executable mode is checked using lstat, and the
source manifest must equal the original2c697217 receipt before and after.
All Lean/package pins, source policy, complete repository verifier, retained
proof library and four actual Palomar comparator gates remain unchanged.

Independent Luna static review and Bash syntax checking passed. The actual
Git oracle passed: directory-only ignore misses the symlink, the precise
metadata exclusion handles it, while tracked byte/mode tampering, another
untracked file and a wrong cache target are rejected. Its exact executed
source and review are preserved in the adjacent packet. This preparation is
not a successful replay receipt.

Driver SHA-256: `5720dadbec8254d7441378935c11a4f67c954e0ca9c4912f18444bf7ce5d2d08`.

Review packet SHA-256: `6bb601a28cf31ad7bacbc6dce2561ce0979a1146b68bfafde26b51c2953e37a3`.
