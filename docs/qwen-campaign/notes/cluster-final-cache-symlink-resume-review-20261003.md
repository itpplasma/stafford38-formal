# Independent bounded review: C2 cache-symlink resume

Verdict: **PASS** for the stated narrow resume delta. This is a static review of the exact script and its stated prior receipts, not a verifier/comparator receipt. No cluster allocation or proof command was run.

## Frozen inputs

- Resume script: `/tmp/cluster-final-cache-symlink-resume-20261003.sh`
- Resume SHA-256: `5720dadbec8254d7441378935c11a4f67c954e0ca9c4912f18444bf7ce5d2d08`
- Original guarded script: `/home/ert/proj/stafford38-formal/docs/qwen-campaign/notes/cluster-final-guard-repaired-20261003.sh`
- Original SHA-256: `1b861f175547cb8e0073aa636af9bfd54f481d56c2b59e0ee0bfb77467a7f838`
- Frozen source commit: `12ae3cc49152672a48a96f13994314b65ae38197`
- Expected complete tracked-source manifest SHA-256: `2c697217e318b576775dea866ea45e4e53d1ec3964475953bb4dd5070e08a325`
- Lean commit and lake-manifest SHA-256 remain `470d5ce1400764999581fd26d5d72b00d990b0f4` and `29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc`.

## Review findings

- Resume is gated on the specific failed T70 commit, prior dependency-materialization failure, exact Lean/source-manifest/lake-manifest identity, prior completed stages, and the outer guard’s finished/failed/drained record plus the exact `?? .lake` failure diagnostic. It also requires that mathlib cache, prebuild, full verifier, proof library, and all four comparators have no prior stage artifacts. The new receipt directory is distinct; the original failed receipt remains intact.
- The reused `.lake` target must be a symlink whose resolved target is the non-symlink donor directory, with the resolved donor contained under the run root. The resumed source path must still have exactly the frozen HEAD and only the expected untracked `.lake` symlink.
- The only source-worktree cleanliness adjustment is a root-anchored `/.lake` line in that clone’s `.git/info/exclude`, addressing the generated symlink missed by directory-only `.lake/`. This Git metadata change does not exempt tracked source: manifest generation still walks every tracked blob, checks regular-file `lstat` type and executable mode, checks each byte stream against `git hash-object --no-filters`, and requires the full manifest SHA to match before and after Lake update and again at final integrity.
- The resumed sequence preserves toolchain, package pin, source-policy, tooling, dependency materialization, mathlib cache, common-open-etale prebuild, full verifier, proof-library build, four comparator commands, final source-manifest and package-head checks. `run_stage` timeout remains 19,800 seconds with 60-second kill grace. No trust flag, cap, or success condition is relaxed.
- `bash -n` passes. The diff is limited to resume-specific prior-failure gates, a new receipt path, stronger tracked-byte validation, and the local `.git/info/exclude` workaround; the verifier/comparator stage commands and order are unchanged.

No specific defect found. Full verifier, proof-library and four comparison receipts remain required before any proof-promotion claim.
