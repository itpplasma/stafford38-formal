# Linux cluster allocation smoke receipts

Both controller-submitted allocation smokes passed on 3 October 2026.
Acluster job21805715 ran on node14; scluster job3107729 ran on node2.
Each reserved one node/task, two CPUs and 8GiB; the srun step observed exactly
affinity[0,1]. Guard receipts identify the actual job/step cgroup, exit0,
zero swap growth and no surviving child. The child independently exercised
pidfd support and verified contention on the guard's shared-home flock.
Startup/runtime disk and node RAM safeguards were active. No Lean, installation
or campaign compute ran on a Mac or either cluster login host.

Guard source: linux-slurm-guard.py SHA256
`ca59b4b7c067851dca28aaff59b3919ec9224bda16a324fa2233d29d1c898506`.
Source local watchdog SHA256
`cd072bba9e2dead893791503bb6115299ba0a65eb106b126a376a1ab948b7b87`.
Evidence archive SHA256: `31831e546031d8693edff430b39801ac2a0a5e1862207ea8faeb46dd8c0195f6`.

Subsequent isolated rc3 bootstrap allocations are acluster21805716(node14)
and scluster3108325(node1), both frozen at WTda00639. Their results are pending;
these smoke receipts do not certify proof modules or the final source replay.
