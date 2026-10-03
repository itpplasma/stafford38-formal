# Generated cache symlink: final replay setup failure

PublicC2 12ae3cc49152672a48a96f13994314b65ae38197 passed source identity,
Lean/tooling, cache reuse, dependency materialization and all ten package pins
in scluster3131361. The post-update source-cleanliness gate then rejected the
generated `.lake` symlink as untracked: Git's directory-only `.lake/` ignore
rule does not cover a symlink. No complete verifier, proof-library or actual
Palomar comparator stage ran. This is a replay setup failure.

The allocation drained normally after2minutes26seconds: guard/commandexit1,
peak933187584bytes, zero swap growth, no stop cause or surviving children.
All failed receipts, before-source manifest and guard/Slurm logs are retained
in the adjacent archive. Sol prepares a bounded same-public-source resume,
with a narrow Git metadata exclusion for the verified generated cache path;
every tracked source byte/mode, pin, verifier and comparator gate is retained.
No mathematical source, paper pin or proof statement changes.

Archive SHA-256: `d95eaeb6ba21d62196d815dfaadcf8519f713cdb18c3202b5f76885164419289`.
