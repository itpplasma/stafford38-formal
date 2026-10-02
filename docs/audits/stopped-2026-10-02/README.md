# Stopped-state checkpoint

Work stopped at the owner's request on 2 October 2026. No proof, migration or verification job remains running. The candidate files below preserve unfinished source and evidence for later resumption. The Euler-owner cleanup was subsequently promoted to `main` and passed a focused `--trust=0` compile; the other archived candidates remain unpromoted.

The canonical development remains Lean 4.33.0. The unpromoted rc3 patch is against commit `b62f8cc0663a57d2baa51e333504a57da8fb5612`; applying it in an isolated checkout reconstructs candidate tree `3b844a0ea9dc5a0ecea65d33da70f3d41ca05f26`. Its complete all-module build and verifier have not passed after the latest merge. The coefficient/support lemma in CanonicalMonicSaturation passed a focused rc3 source check.

The geometry archive includes the unfinished same-witness affine-fibre closure and its private source helpers. Its last compile failed first at line 208 (`change` did not match); later coefficient and recursion-depth errors remain. It must not be substituted for a proved endpoint. The dependency guard and Palomar verifier archives contain saved candidates and fixture evidence, not a receipt for the final submission.

The 9,181-job canonical module build passed at the exact input checkpoint recorded in module-build-inputs.json. The 900-second full verifier reached serial consumer checks and then timed out with exit 124. Its remaining consumer, declaration, source and terminal audit stages are not collectively verified by this run. Historical full receipts keep their original scope.

The Euler-owner patch remains archived as the exact source delta and verification provenance for the cleanup now integrated in `Stafford38/Weyl/EulerProductIdentities.lean`. Archive hashes, file hashes and limitations are recorded in `manifest.json`. Restore any remaining candidate work in isolated worktrees; do not overwrite the canonical proof or the preserved manuscript. No new formal or supplementary release was published, and no final review handover email was sent.
