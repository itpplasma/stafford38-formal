# Independent review: Linux cluster final replay candidate

Review target: controller-designated patch
`15b0bbc9d4a243f5a40bd7cb32cd124c1e2a3cd0c03f03f91adb850b397a3c1c`
against base `b926401a6c03370790bc071db3258598f59d4d9d`; current MAIN HEAD
when reviewed: `9ea34980e32d3a399fc5f061fcf7009b30c501d8`.
Reviewed candidate file SHA-256 values:

- Driver: `cluster-final-replay-20261003.sh`,
  `6f764eb28333efac591d3b7ff515b87cf87f90b9f4e832001eb010ef9170b321`.
- Contract: `cluster-final-replay-20261003.json`,
  `4c5804d2f4bc499ea79a1a05548d546d2ff65eeecbbc0c1cc8facb4af505a034`.
- Walkthrough: `cluster-final-replay-20261003.md`,
  `bc6dde71c0b730da29ed398ac2875577d956b1a317faa28b041055f8e01aba5b`.
- Fake-tool harness:
  `cluster-final-replay-behavior-20261003.py`,
  `b68183876c0d5c1cced4bad9474b3d46bc1c2f0b7cacaf3c9b2e8664724e7e81`.

## Blocking findings

1. **Manifest does not independently verify the checked-out executable mode.**
   In the driver's `write_source_manifest`, the mode field comes from
   `git ls-tree`; `lstat` only checks that the file is regular, and the
   manifest records the Git mode without comparing it to the filesystem
   executable bit. Chmod detection is left to `git status`, whose behavior
   depends on `core.filemode` and filesystem support. With filemode detection
   disabled, an executable-bit change can leave status clean and the before /
   after manifests identical. Compare actual `st_mode & 0o111` with whether
   the tree mode is `100755` before accepting each file. The harness's fake
   `git status` always compares executable bits, so its mode-mutation test
   does not model this failure case.

2. **Run-root containment is lexical and permits escape.** The shell case at
   driver lines 13–16 accepts any string beginning
   `/home/ert/stafford38-campaign/`. For example,
   `/home/ert/stafford38-campaign/../outside` passes and resolves to
   `/home/ert/outside`; a symlink below the allowed prefix can likewise
   redirect writes. Since the driver creates `final-receipts` below this
   value, it can write outside the intended campaign storage. Require an
   existing directory, resolve it canonically (for example, `realpath -e`),
   then enforce that canonical path is beneath the campaign root before any
   write. Add a fake-tool negative test for traversal and symlink escape.

The harness documentation says negative argument/root cases are exercised;
the checked-in harness currently has no such cases. The traversal finding
above makes this coverage gap consequential.

I reproduced the mode issue with a disposable copy of the fake harness whose
fake `git status` ignores executable-bit differences (the behavior of
`core.filemode=false`). The mode-mutated replay then incorrectly completed
with status zero and unchanged source-manifest identities.

## Checks that passed

- `bash -n` on the replay driver.
- The fake-tool behavioral harness passed its wrong-source, wrong-Lean,
  failing-cache-stage, content-mutation, mode-mutation, clean-manifest, and
  four-comparator-order oracles. The mode oracle has the limitation described
  above.
- JSON syntax validation and `git apply --check` of the owner proposal are
  unrelated to this replay review; no Lean, SSH, scheduler, or system action
  was taken.
- Lock file SHA-256 is
  `29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc`,
  matching the candidate contract. The archived mailuefterl contract and
  companion driver are byte-identical to base
  `b926401a6c03370790bc071db3258598f59d4d9d`.

The candidate has a sound staged gate order, explicit immutable package-rev
checks, all four comparator invocations in the requested order, failure
receipts, and a separate outer-guard result contract. These positives do not
clear the two containment/integrity findings. This is not approval to launch.
