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

## Repaired candidate re-review (2026-10-03)

Re-reviewed the controller-designated repaired patch
`15b0bbc9d4a243f5a40bd7cb32cd124c1e2a3cd0c03f03f91adb850b397a3c1c` against
the original base above, at MAIN HEAD
`b79f0c98ee3a58211594711547ea8cb733511f95`. The four review inputs matched
the supplied hashes: driver `b11d6e57e5ea809340e5298c1d51c07b3cbfb8037a1a9259ea2a1f5807917ef9`,
harness `209aab6fff4a5719bf7e854869cd8f9743677c8184937aa6fc8171f969913167`,
contract `8ec186faa3598e37895a2d4fe9bf8be75f89c29fd0d79a146b2c058d0e738b8d`,
and walkthrough `866d75ad6e6d5ca7ba0feb696934e4ed645d546c40e1e2fa43bd5a2aafefaf82`.

The driver now compares each actual filesystem executable bit against the
Git-tree mode, and resolves the existing run root strictly before requiring a
proper descendant of the canonical campaign directory. These checks precede
creation of receipts or source checkout. The fake Git status intentionally
ignores executable-mode changes; the harness tests adding and removing that
mode, invalid argument/root cases, traversal and symlink escapes, and confirms
they fail before writes.

Validation passed: `bash -n`, JSON parsing, and the fake-tool behavioral
harness. The harness reported passing mode mutation/removal under mode-blind
Git status, root traversal/symlink rejection, wrong source/Lean pin,
fail-stage receipts, clean manifest identity, and all four ordered comparator
invocations. The lock SHA still matches. The archived mailuefterl contract
and companion driver remain byte-identical to the original base.

**Scoped result: PASS for the repaired driver/contract/harness review.** This
is not a cluster execution or launch authorization; the controller still owns
the outer-guard review, resource check, and any replay.

## Single-dependency prebuild re-review (2026-10-03)

Compared the replay-stage delta against `322ad06`. The driver adds exactly one
stage, `lake build Stafford38.Geometry.SameWitness.CommonOpenEtale`, after
Mathlib cache loading and before `bash scripts/verify.sh`. The authoritative
verifier, retained proof-library build, and four comparators keep their prior
relative order. Existing caps, immutable pins, root checks, fail-closed
receipts, and terminal verification are unchanged. The 7406 MiB T35 peak
leaves 786 MiB under the existing 8 GiB cap; the recorded Lake audit found no
supported job limit, so prebuilding this dependency lets the verifier reuse its
actual trace.

The updated fake-tool harness passed and asserts both the full gate order and
that a failed CommonOpenEtale prebuild stops before every downstream gate.
`bash -n` passed; the replay contract parses as JSON. Driver SHA-256 is
`43666f950d7de083a32ff2207c21b730179accf3bf1eaebc5c180e4dfe42db53` and
harness SHA-256 is
`8cebc5ff3e1111500e75ca03b3fff0a64ceb642c98f0b53f4d0ac13b33af43c0`.
**Scoped result: PASS for the added prebuild stage.** No Lean, network, SSH,
scheduler, or cluster action was run.
