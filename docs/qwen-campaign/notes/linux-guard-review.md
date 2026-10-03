# Linux local guard review

Reviewed on `mailuefterl` against the preserved execution contract at
`docs/audits/paused-2026-10-02/palomar/stafford38-linux-execution-contract-20261002.json`.
That contract applies to the final replay: exact frozen source, fresh
`/mnt/storage/stafford38-final-replay-20261002.XXXXXX` stage, pinned rc3
toolchain and package commits, fresh Linux `lake update` and Mathlib cache,
ordered verifier/comparator gates, per-heavy-command 19,800-second ceiling,
and full source/log receipts. It records a 94 GiB / 32-core host inventory.
The separate T71 gate requires at least 64 GiB available RAM and 100 GiB
free on `/mnt/storage` before replay.

The untracked `cluster-guard.py` is a Slurm allocation guard, not suitable for
this `mailuefterl` local bootstrap: it refuses whenever `SLURM_JOB_ID` is
absent. It checks actual affinity and allocated CPUs, memory reservation,
RSS, node reserve, PSI, incremental swap use and descendants. Its source is
preserved unchanged; SHA-256:
`b51301f9d3c015effdcecbfd43efffd9b18227f3063c2d1d84bc7b4cc73f047f`.

I added `docs/qwen-campaign/linux-guard.py` for one local Linux slot. It
requires at least 100 GiB free on `/mnt/storage` and at least `8 GiB + max(8
GiB, 5% of node RAM)` available RAM to start; it assigns two allowed CPUs,
sets Lean and native thread counts to two, takes an atomic `flock` slot,
tracks aggregate process-group RSS against 8 GiB, and stops only its group
when available RAM falls below the reserve, PSI reaches the contract
threshold, swap grows by 1 GiB, free disk drops below 50 GiB, or timeout
expires. It records a terminal JSON receipt plus two-second progress JSON and
monitors both the working filesystem and `/mnt/storage` for disk pressure.
Pre-existing swap is recorded as a baseline and does not trigger an absolute
swap limit. PSI absence remains unknown while the RAM reserve is enforced.

Observed preflight: `hostname=mailuefterl`, 81.7 GiB available RAM, 13.6 GiB
used swap, 696 GiB free on `/mnt/storage`, 169 GiB free on `/`, 96 GiB total
RAM, 32 CPUs visible, and two permitted CPUs `[0,1]`. The campaign worktree's
`.lake` points into `/mnt/storage`, so both filesystems are checked. Both pass
archived T71's memory/disk thresholds and the new local guard. No Lean or
Lake process was observed.

Independent synthetic behavioral probes (no Lean) passed for normal child
execution with CPU affinity/thread settings, aggregate RSS refusal, timeout
with process-group child cleanup, node-reserve refusal, start-disk refusal,
and one-slot refusal. Python byte-compilation and live `linux-guard.py check`
also passed. The RSS test used a 16 MiB synthetic cap and a 64 MiB allocation;
it does not approach the production 8 GiB cap. The timeout probe used a
one-second limit and a `sleep` descendant. No repository verifier or Lean
command was run.

Recommended bounded bootstrap after the controller grants the specific Lean
run: run `python3 docs/qwen-campaign/linux-guard.py check`, then invoke each
command separately, for example:

```sh
python3 docs/qwen-campaign/linux-guard.py run --timeout 900 \
  --log /mnt/storage/<fresh-stage>/logs/lake-update.log \
  --cwd <fresh-rc3-worktree> -- lake update
python3 docs/qwen-campaign/linux-guard.py run --timeout 900 \
  --log /mnt/storage/<fresh-stage>/logs/mathlib-cache.log \
  --cwd <fresh-rc3-worktree> -- lake exe cache get
```

Recheck the exact `lake-manifest.json`, package HEADs and source freeze
between dependency setup and proof checks. Use the contract's ordered final
driver and 19,800-second caps for the T72 replay; the local guard bootstrap
does not replace that final replay receipt. Do not copy a Mac `.lake` cache.

SHA-256 evidence:

- `cluster-guard.py`: `b51301f9d3c015effdcecbfd43efffd9b18227f3063c2d1d84bc7b4cc73f047f`
- `linux-guard.py`: `2b1d5dba1dd19c476c7d0caf2d3f44a43404a340218e023faa0e50460cd3b685`
- synthetic test script: `4f635c74aefbd0b6a9df9d6fc3219ddba6f2738511d5a44a2586231ae3d575af`
- archived Linux contract: `3347c3fa51e3819330a4fcc33b9b4d46f906a11de0799eb389b044125fbeffe8`
