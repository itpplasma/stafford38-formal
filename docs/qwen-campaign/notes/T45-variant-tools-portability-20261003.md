# T45 variant tooling portability freeze

Date: 2026-10-03. This supplements the earlier T45 tooling resume note; that
note remains unchanged. The runner now resolves the pinned Lean binary beneath
`ELAN_HOME`, falling back to `~/.elan` when the variable is unset or empty. It
does not consult `PATH` for Lean. It checks both RC3 and commit
`470d5ce1400764999581fd26d5d72b00d990b0f4` before starting guard work.

The independent fake-executable oracle passes these cases: exact pinned Lean
under an isolated `ELAN_HOME`; unchanged default-home resolution; a missing
isolated binary does not fall through to a same-named `PATH` executable; and a
wrong commit under the pinned path is rejected. Python compilation, shell
syntax, and whitespace checks also pass. No Lean command was run.

The updated T45 tooling patch remains based on
`8fa692f4f72c4ff01f4c0d22ff4dd5be6cd22ba7`; its scoped SHA-256 is
`cc9bda48c51e897bb72a4f471f0fa79c0b41369b4f6f937bba471d08aaa3a35b`
(38,865 patch bytes). This includes the earlier T45 tooling and the isolated
toolchain check, and excludes proof-worker files and unrelated worktree edits.
