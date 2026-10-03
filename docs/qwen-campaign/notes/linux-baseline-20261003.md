# Independent Linux prerequisite checks

These are mutable campaign-worktree checks, separate from the final frozen Linux replay (T72–T73). The source base is `fcd866f9dcf736d624b96a8fd5ea086ca910f9ad`; the checked T22, T30 and T31 modules and their literal consumers had no uncommitted changes.

Fresh rc3 dependencies were bootstrapped on mailuefterl under `docs/qwen-campaign/linux-guard.py`. The manifest remained byte-identical (SHA-256 `29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc`), and all ten package HEADs matched the recorded pins. The old MAIN 4.33 cache was not used.

| Check | Exit | Wall seconds | Peak RSS MiB |
| --- | --- | --- | --- |
| lake-update | 0 | 75.6 | 2435.0 |
| mathlib-cache | 0 | 4.2 | 916.1 |
| T22-T30-linux-baseline | 0 | 986.7 | 4363.3 |
| T31-linux-module | 0 | 114.1 | 3894.8 |
| T31-linux-consumer | 0 | 2.8 | 4018.2 |
| T22-linux-consumer | 0 | 4.2 | 2730.0 |
| T30-linux-consumer | 0 | 2.0 | 2725.7 |

All three literal consumers ran with `--trust=0 -M 8000` and reported only `propext`, `Classical.choice`, and `Quot.sound`. The module build checked 3031 targets; no process survived the guard. Checks used two-CPU affinity, an 8 GiB aggregate RSS cap, and no swap growth.

Evidence packet: `linux-baseline-20261003.tar.gz`, SHA-256 `c1e377acda67ec86ae775cb086305165f5c9feb1ddd0632313025544f2c06e68`. It contains each full command log and its terminal guard receipt. No full-route or release claim follows from these scoped checks.
