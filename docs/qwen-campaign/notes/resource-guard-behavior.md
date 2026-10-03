# Resource guard behavior checks

Ran through `/Users/ert/proj/stafford38-formal/docs/qwen-campaign/guard.sh`. Scratch helper and logs are under `/Users/ert/proj/stafford38-qwen/.lake/qwen/guard-tests/`. No Lean command was invoked.

| Check | Expected | Observed |
| --- | --- | --- |
| Normal child exit | Child code 7 propagates; `reason=finished` | Exit 7; `GUARD exit=7 reason=finished`. |
| Atomic slot race | First long command owns lock; concurrent second is refused with 90 | First completed with exit 0. Second exited 90 with `GUARD REFUSED: local slot locked`; final `guard.sh check` reported no active Lean process and `GUARD OK`. |
| Timeout/process group | Timeout returns 93 and kills parent and child | Exit 93, `reason=timeout`; recorded child PID 45731 was gone. |
| Aggregate RSS | 1 GiB override cap kills a process allocating 1.5 GiB; return 91 / `rss-cap` | Exit 91, `reason=rss-cap`, peak 1545 MiB; no RSS helper process remained. |
| Aggregate CPU | 1 CPU override with parent plus three busy children returns 95 / `cpu-cap` and kills group | Exit 95, `reason=cpu-cap`, measured peak 397%; all three recorded children were gone. |

The normal, timeout, and lock-race cases used defaults. RSS overrode only `RSS_CAP_GB=1`; CPU overrode only `LEAN_NUM_THREADS=1 CPU_CAP=1`. No processes were killed manually. Final `guard.sh check`: 52 GiB free memory, 652 GiB disk free, 0 GiB swap, pressure level 1, no lake/lean processes, `GUARD OK`.

## Log hashes

- `normal.log`: `7ca2f060ebe1280c7beb39e4c0bb33a9eee79501efeafdd088b6fd9ad990d156`
- `race-first.log`: `ef0aff5274096d62fdcc6e8f788e20873c489f0698bcde8e6d4a3606284d1615`
- `race-second.log`: `9b4459820afcc1c0b5d987fd3a07d76a32316adc04eb42bb721c773bb197321c`
- `timeout.log`: `85eb1aec48ccd6619d7133f3d0495561f1869f611b119f80cfb0e2f7ad64ecae`
- `rss-cap.log`: `04b61325a5758de22d7c2e7f35a1629c6f7a8a0427d6e22b630f3a939bf1c4e0`
- `cpu-cap.log`: `46420879fb868c3fcc7afae687d592db60e538e691d853cae62a30277594eee3`

## Revised guard replay

After the guard revision, its source SHA-256 was `b6eebe8c6d0133f6dffccda31dd1ab14594b7b354908babd57705c6e8daa43d4`. The earlier leader-exit fixture had exposed a gap: the leader returned while its child remained, and a second invocation acquired the released slot. That owned child (PID 48899, PGID 48897) was then cleaned up. On the revised guard, a parent exited 7 after starting a child that slept 5 seconds. The guard retained the slot, a concurrent invocation was refused with 90, and the first returned 7 after 6 seconds when the child exited. The child was gone afterward.

The revised timeout fixture returned 93 and its child was gone. Two owned children each allocated and touched 600 MiB under a 1 GiB RSS cap; the guard returned 91 / `rss-cap` at an aggregate peak of 1226 MiB, and both children were gone. This verifies the aggregate process-group RSS check. The CPU fixture returned 95 / `cpu-cap` with a measured `ps` peak of 399%; macOS reports a decaying CPU average, so this confirms the watchdog trigger path and does not establish a hard CPU quota. The terminal SIGINT fixture had a verified child PID 55525 before Ctrl-C; the guard session exited 130, the child was gone, and the slot was released. A guarded child also confirmed `LEAN_NUM_THREADS`, `OMP_NUM_THREADS`, `OPENBLAS_NUM_THREADS`, `MKL_NUM_THREADS`, and `VECLIB_MAXIMUM_THREADS` were all `2` by default.

Final revised-run guard check: `GUARD OK`, no lake/lean processes, 55 GiB free memory, 652 GiB disk free, 0 GiB swap. No Lean process was invoked. The exclusive guard slot was released.

Revised log hashes:

- `v2-normal.log`: `da3c7d7e0bc0a66a8f1420e15b2d653f98fa6f4c6cc49d68b77e05353ff0cfe8`
- `v2-race-first.log`: `9dc0d75a8358bdec616a2a243a1bb690a731ea78bbff27a15ddf7040d74906bb`
- `v2-race-second.log`: `9b4459820afcc1c0b5d987fd3a07d76a32316adc04eb42bb721c773bb197321c`
- `v2-orphan-first.log`: `db3d46f9f3e2c6ba205809de9d3220222267d5e57860a3197668571ce740add1`
- `v2-orphan-second.log`: `9b4459820afcc1c0b5d987fd3a07d76a32316adc04eb42bb721c773bb197321c`
- `v2-timeout.log`: `0f513ce1042cbc6525934e3a9ac2e0b53172fe71577df8548605b0538fc80fe3`
- `v2-rss-group.log`: `1a78410416889941e69d2a6618b5cbc79b4915b4ec95ff834b620bbd070de0ed`
- `v2-cpu-cap.log`: `e8db72acd1aa602e0a9c10943a965fb6172c992b760ae3552a64f14197d477d0`
- `v2-signal2.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (the SIGINT trap exits before emitting a GUARD summary line)
- `v2-thread-env.log`: `08c7b761d2642a9eb88af2d327c73e4a197bca4c3ef32e1b373668eeada2a0c8`

## Controller archive

The controller independently verified the final guard hash and 10 revised log hashes. The helper scripts, revised logs and exact guard source are archived in `resource-guard-diagnostics.tar.gz` (SHA-256 `2717e8849740597dda1e9840749c287a82bb865c773e36631d041c645d436150`). This is resource-control evidence; it does not establish a mathematical theorem.
