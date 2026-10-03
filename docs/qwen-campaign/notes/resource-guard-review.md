# Resource guard candidate review

Read-only review of `guard.sh` after the controller's resource update. No
Lean or guard fixtures were run because T43 owns the behavioral-test slot.

## Findings

The candidate uses the requested defaults: 2 Lean threads, an 8 GiB RSS cap,
12 GiB start threshold and 4 GiB free-memory floor. `mkdir` on the fixed
per-user `/tmp` lock path is atomic for concurrent `run` invocations on this
host. The lock is acquired before preflight and released on normal shell exit.

The RSS/CPU sampler gets PIDs from the launched process group, which captures
ordinary Lake and Lean children. However, it shells out to `ps` twice for
every PID at every one-second poll. One `ps -axo pid=,pgid=,rss=,%cpu=` sample
filtered by the group ID would reduce sampling skew and overhead; sum RSS and
CPU as floating-point values in one `awk` pass. RSS is reported in KiB by
macOS `ps`, as expected by the GiB threshold.

CPU accounting needs a semantic correction or a narrower claim. On this
machine, `man ps` documents `%cpu` as a decaying average over up to a minute.
Reading that same rolling average three consecutive seconds does not prove
three seconds of sustained CPU use. In addition, `printf "%d"` truncates
each process's fractional percentage before aggregation. For an actual
three-poll sustained test, sample aggregate process CPU-time counters and
compare their delta with elapsed wall time. If the controller keeps `%cpu`,
sum decimals from one process-group snapshot, call it a delayed watchdog
heuristic, and fixture its false-trip behavior explicitly.

The main loop and cleanup are keyed to the leader PID (`kill -0 "$pid"`),
not to whether the process group still exists. If the command leader exits
while a same-group child remains, the loop exits and the EXIT trap releases
the lock while that child is still running. The INT/TERM handler similarly
sends TERM, sleeps one second, sends KILL, and exits; EXIT cleanup removes the
lock without confirming that the group drained. Install signal handling
before spawning, track the PGID separately, and keep the lock until no group
members remain. If a member cannot be reaped, fail closed and leave a
diagnosable lock rather than admitting a second job. A SIGKILL or host reboot
also leaves a stale lock; this is safe but needs an explicit owner-checked
recovery procedure, not automatic removal based only on a reused PID.

`LEAN_NUM_THREADS=2` limits Lean's internal worker pool per Lean process; it
does not itself limit the number of Lean subprocesses Lake schedules. Pinned
Lake 5.0.0 `lake --help` and `lake build --help` expose no `--jobs` option.
The process-group CPU watchdog is post-facto termination, not a scheduler
limit. Keep the aggregate RSS cap as the hard resource guard. Before claiming
that Lake concurrency is bounded to two, verify a supported Lake config key
or use a separate scheduler limit; do not infer that from `LEAN_NUM_THREADS`.

## Behavioral fixtures

Use a test-only fake `PATH` for `vm_stat`, `df`, `sysctl`, and `ps` so the
fixtures do not need large real allocations or depend on live Mac pressure.
Keep real `mkdir`, `kill`, `sleep`, and process-group behavior. Assert exit
codes, reason fields, observed child liveness, and lock state; source hashes
or file comparisons are not oracles.

- **Aggregate RSS cap:** run a harmless sleeping command in the guarded
  process group; have fake `ps` report two same-PGID children at 600 MiB each
  under a 1 GiB fixture cap. Require exit 91 / `reason=rss-cap`, both children
  gone, and the lock released. Each child alone is below the cap, so this
  catches per-process instead of aggregate accounting.
- **Concurrent slot:** start one guarded sleeping command and wait for its
  start marker; start a second `run`. Require exactly one command marker,
  the loser to exit 90 with slot-locked, then verify a third run can enter
  after the first exits.
- **Timeout and cleanup:** run `sleep` past a short timeout. Require exit 93,
  no surviving PGID members, and lock release. Also test INT/TERM and a
  command whose leader exits while a same-PGID child remains; the guard must
  keep supervising/cleaning that child and hold the slot until the group is
  empty.
- **CPU limit:** have fake process-group stats present aggregate load just
  below and above the configured budget, including fractional per-process
  values. Require one or two high samples not to trip and three genuine
  consecutive over-budget samples to trip. For a CPU-time-delta sampler,
  have the fixture advance counters at controlled rates and include a
  falling-load case.

For `acluster` and `scluster`, keep the Mac guard separate. Request scheduler
memory and CPU allocations and verify cgroup enforcement where available;
otherwise use the documented ghost-CPU reservation plus an aggregate RSS
watchdog. The local `/tmp` lock cannot coordinate independent hosts.

## Frozen guard repair review

Reviewed the controller's frozen candidate at base MAIN
`b938a7d51e2ea6eee1f425519f0bc2692dd7dc49`. The guard file SHA-256 is
`b6eebe8c6d0133f6dffccda31dd1ab14594b7b354908babd57705c6e8daa43d4`.
The guard-only binary diff is frozen at
`/Users/ert/proj/stafford38-qwen/.lake/qwen/review/guard-only-b938a7d-to-b6eebe8.patch`,
SHA-256 `65054635c8c4722ef69a184adbbf30a3663bd6cfd3819c4d9c0d96e6a58b86f6`
(147 lines). The file hash matches the supplied frozen hash.

The earlier leader-only lifecycle gap is repaired: `group_alive` uses the
launched PGID, the main loop continues while the leader or any group member
exists, and EXIT cleanup retains the lock when the group survives. Timeout,
RSS/resource termination and INT/TERM all use `kill_group`; it sends TERM,
then KILL, and polls for group disappearance. If members remain after those
polls, the shell exits but leaves the lock and owner file in place. This is
fail-closed and avoids admitting another guarded job, though it leaves no
active watchdog or automatic stale-lock recovery. One narrow race remains:
the INT/TERM trap is installed just after the process is spawned; installing
it before spawn would also cover interruption in that interval.

CPU aggregation now retains hundredths per process before adding them, and
the source explicitly documents `ps %cpu` as a decaying-average watchdog
signal, not an instantaneous quota. Local `man ps` confirms the average may
cover up to one minute. Three above-limit polls can therefore repeat the same
rolling high average; they do not certify three seconds of continuous CPU
oversubscription. The per-PID conversion also truncates below one hundredth
before summing, so a single `ps` snapshot summed as floating point would be
more accurate. Keep the no-hard-Mac-quota caveat; this check reacts to
overuse rather than constraining scheduler concurrency.

The guard header still says the run log's last line is always a GUARD summary.
That is false for preflight refusal and the INT/TERM trap: the latter exits
before line 147 writes the summary. Nonblocking controller documentation
correction after the active job slot: narrow the claim to launched commands
that reach normal/watchdog completion, or add a separate trap summary without
changing the signal exit code. Do not change the guard during the occupied
T43 fixture slot.

The controller's behavior note reports passing leader-exit, aggregate
600-MiB-child RSS, timeout and SIGINT fixtures. I did not rerun them. The
separate guarded Lean build measurement was 1883 MiB RSS, 75% CPU and two
threads; it failed on proof-extra tactics, not on resources. No full Mac CPU
quota is claimed. Pinned Lake 5.0.0 help exposes no `--jobs` option, and
`LEAN_NUM_THREADS=2` remains a per-Lean-process setting; aggregate PGID
monitoring is the only current cap over concurrent Lake children.
