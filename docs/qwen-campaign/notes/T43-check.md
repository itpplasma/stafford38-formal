# T43 strict dependency guard preparation

## Frozen inputs

- WT base commit: `0340cf2b1601de7a8895c0b450d4bcbbb9867bed`.
- Current WT patch SHA-256: `6c54483ad2a7dfc2673d549c2c51a438c0acb84dfa924414e5d5401407108f7e`.
- Archived integration patch SHA-256: `5e6f4a9de617957469571540dbc64d882dda8f70ea65f4a3a7908cae1fa62d1e`.
- Controller compared the 18 archived integration payload files against WT: 18/18 identical, zero mismatches. Guard sources were reused without edits.

## Wiring and static checks

Applied `palomar-verifier-guard-wiring.patch` after `git apply --check` succeeded. It adds the fixture behavior command after the Palomar behavior check and the production guard after the retained-module build in `scripts/verify.sh`.

Static checks passed: `git diff --check`; `bash -n scripts/verify.sh`; in-memory `compile()` of `run_guard.py` and `test_behavior.py`. These checks do not execute the guard or fixtures.

The guard's default path removes inherited `STAFFORD_ALLOW_OLD_ROUTE`; only the explicit diagnostic `--allow-old-route` option sets it again. Qualification uses `python3 scripts/dependency-guard/run_guard.py` with no diagnostic flag, so it remains strict. The checker names the old module owner and five banned producers, checks four terminal roots, and uses the explicit standard axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`). The fixture oracle also checks transitive opaque-owner expansion, unavailable bodyless declarations, banned owners/producers, and `sorryAx` in challenge roots.

## Pending guarded checks

No Lean-invoking command was run. Fixture behavior needs the exclusive guarded slot; the controller reports available memory at 25 GiB, below the guard's 60 GiB start threshold, with no Lean process active. Production guard remains pending T42. T43 is not complete until fixture behavior prints `PASS:` and the production guard exits 0 on the final terminal roots.
