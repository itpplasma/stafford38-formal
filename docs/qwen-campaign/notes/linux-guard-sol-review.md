# Linux guard Sol repair evidence

The controller rejected the earlier local guard because it lacked foreign
Lean/Lake refusal, interruption cleanup, check-mode lock inspection, nested
log-directory creation and an explicit guard exit receipt. Sol repaired only
`docs/qwen-campaign/linux-guard.py`; cluster-guard.py is untouched.

The atomic flock covers preflight, the complete owned process group and
cleanup. Check mode probes the same lock. Both entry points refuse live
processes whose Linux comm name is exactly lean or lake without signaling
those processes. Parent exit does not release the slot while descendants
remain live. SIGTERM and SIGINT are blocked across child creation, handled
by the supervisor and ignored during final group draining. Owned-group
TERM is followed by KILL after two seconds; the slot remains held until
no live group members remain. Uninterruptible kernel tasks can therefore
hold the slot while exiting; the guard does not falsely declare cleanup.

The existing production 8 GiB RSS cap, two-CPU affinity, node RAM reserve,
relative swap-growth threshold, PSI thresholds and disk budgets are unchanged.
Nested log directories are created, and terminal JSON includes
`guard_exit_code` beside the command return code.

Independent behavioral suite:
`.lake/campaign-resource-scratch/test_linux_guard_sol.py`.
Receipt: `.lake/campaign-resource-scratch/linux-guard-sol-receipt.txt`.
The suite invokes no Lean and does not alter production caps. Actual child
code asserts two-CPU affinity and thread environment. A controlled Python
process temporarily named lean proves foreign refusal in check and run and
remains alive after refusal. A parent that exits leaving a sleep child proves
the slot remains busy until timeout drains descendants. Actual SIGTERM and
SIGINT produce guard exits 143 and 130 with no live owned child. Simulated
9 GiB process-group RSS telemetry exercises the unchanged 8 GiB production
boundary, exit 91; this is a watchdog decision test, not a 9 GiB allocation.
Timeout returns 93. All cases passed. Byte compilation and live check passed.

Live check on mailuefterl reported 78.5 GiB available RAM, 13.6 GiB baseline
swap, 166.8 GiB free on the working filesystem, 696.0 GiB on /mnt/storage,
8 GiB reserve and CPUs [0, 1]. This is guard evidence, not theorem verification.

SHA-256 guard: `cd072bba9e2dead893791503bb6115299ba0a65eb106b126a376a1ab948b7b87`.
SHA-256 suite: `9a59422a9158ea7fbf2614ca3f0f6d030839a2e68c16cfc6185a0f346f18cbb3`.
