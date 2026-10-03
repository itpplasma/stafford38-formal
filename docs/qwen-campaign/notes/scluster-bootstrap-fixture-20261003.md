# Scluster bootstrap and guard fixture checkpoint

Job3109567 completed on node6 with guard and child exit0, elapsed44m38s,
peak3353079808bytes, two actual CPUs, 8GiB cap, zero swap growth,
zero node PSI and no surviving children. The isolated pinned rc3 toolchain,
manifest SHA29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc,
and all ten package revisions passed. The frozen T32 module and its literal
trust-zero consumer passed, reporting only propext, Classical.choice and
Quot.sound. This validates the bootstrap and scoped T32 replay; it is not
final immutable-source campaign replay.

Job3111465 failed before fixture compilation because the fixture runner used
the default ~/.elan path while this job deliberately uses isolated ELAN_HOME.
Sol repaired the fixture to reuse and validate the production guard's exact
pinned executable resolution, preserving fail-closed/no-PATH-fallback behavior.
Fake-executable positive and negative oracles passed.

Job3112549 reached the real compiler and failed at DependencyClosureCore.lean
line125: the quotation binder used the newly introduced keyword required.
Sol renamed the binder to requiredDecl; traversal and all rejection conditions
remain unchanged. That source remains a candidate pending actual fixture retry.

T34 positions job3112555 runs independently on node20. The next guard fixture
retry is scheduled only after it terminates. T35 on acluster remains separate.
Historical failed jobs and their diagnostics are retained in this packet.

Packet SHA256: 2774808e4603941c885c3c515e2a3c649cca9a0c7281765b6700d29aeffeade7

Checked package pins:

- PIN_OK algebraicAnalysis bbbbf3fc358ca8100b158cec4cf47f336ab70163
- PIN_OK mathlib c55e6e786f49471c72fbddbec5415808896aec1e
- PIN_OK plausible fb13df72ecefd8ddbf9291021d7f33a8673eb57b
- PIN_OK LeanSearchClient 29ff470276c725ae01505d55b17148c18fc7dfd3
- PIN_OK importGraph 7e81a29bda33a6b257bd37557a6aa6aebe175d96
- PIN_OK proofwidgets c643bbb3c24f8a25f9c14e3a6b1ceb13d01f3de1
- PIN_OK aesop a90fbf7b02ff06a0deebf74088dff9e5fe02c9ea
- PIN_OK Qq 37b0ba0b26109cf9f9c541f0f9557e50cfa1a3b9
- PIN_OK batteries 3b7c8101932390d60e92a3f3d917901d5b5a773b
- PIN_OK Cli 843844fa601dd56767b1eb22b7ada5b64d5e567a
