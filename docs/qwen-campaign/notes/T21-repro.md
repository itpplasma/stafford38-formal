# T21 minimal tower reproducer

Run on 2026-10-03 in `/Users/ert/proj/stafford38-qwen`; no production Lean
source, campaign state, pins, or packages were changed. The worktree remained
clean. The final scratch contains only the successful quotient-tower and
abstract-hom examples. The intentional failure is preserved in a separate
scratch file.

## Result

Part 1 succeeds: Mathlib supplies
`IsScalarTower k (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k ⧸ P)`.

Part 2 succeeds over abstract `E`. After locally installing
`φ.toRingHom.toAlgebra`, the tower follows from
`IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm`. The local instance is
installed inside the result telescope as required, so the scalar action is
available while Lean elaborates the target.

Part 3 reproduces the action mismatch. The frozen failing file first binds
`oldTower` using the existing polynomial algebra on `E`, then installs
`Algebra.compHom E (algebraMap S A₀)` and tries to assign `oldTower` to the
new tower target. Lean reports:

```text
Type mismatch
  oldTower
has type
  @IsScalarTower k S E AddMonoidAlgebra.algebra.toSMul
    (@Algebra.toSMul S E ... inst✝¹) inst✝².toSMul
but is expected to have type
  @IsScalarTower k S E AddMonoidAlgebra.algebra.toSMul
    (@Algebra.toSMul S E ... this) inst✝².toSMul
```

The old tower is indexed by the original `Algebra S E`; after the duplicate
`compHom` installation, the target is indexed by that new algebra instance.
This is the concrete mismatch T21 was intended to isolate.

## Frozen sources and checks

`TowerRepro-failing.lean` is the exact negative diagnostic source. Its only
error is the intended final tower assignment; parts 1 and 2 elaborate first.
`TowerRepro.lean` comments out that failing part and compiles successfully.
Both files import only the three Mathlib modules specified in the plan.

```text
Command: guard.sh run --timeout 900 --log .lake/qwen/logs/T21-luna-1.log -- lake env lean -M 32000 .lake/qwen/TowerRepro-failing.lean
Result: Lean exit 1 (expected diagnostic); GUARD exit=1 reason=finished wall_s=10 peak_rss_gb=0 free_mem_gb=91 disk_free_gb=553 swap_used_gb=0
Source SHA-256: 13e29be35d696db98cb8a4810e2ae46130aead03909a32f3078fb1926f26af22
Log SHA-256: 3b58184d444e29000a90353ff599050c2a8033dcd37e00a7468ae62d151521b1

Command: guard.sh run --timeout 900 --log .lake/qwen/logs/T21-luna-2.log -- lake env lean -M 32000 .lake/qwen/TowerRepro.lean
Result: Lean exit 0; GUARD exit=0 reason=finished wall_s=10 peak_rss_gb=0 free_mem_gb=89 disk_free_gb=553 swap_used_gb=0
Source SHA-256: 3c6936055be51f82c3391d73e3df34401cf492cec2474cd14fa01832bc8b0737
Log SHA-256: 8e1419c836ab5c6268c42874df5af64f2b682d4060c66b72790d388127e67ca4
```

No theorem hypotheses, axioms, or sorry placeholders were added. The Lean
slot is released.
