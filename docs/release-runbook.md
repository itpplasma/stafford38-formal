# Release procedure

A release records one immutable, verified source tree. The controller selects the target revision and release scope. Do not create or move a tag, publish an archive, or claim a DOI until the exact source and release assets pass the checks below.

## Verify the source

Start from a clean clone of the selected commit. Preserve Lean, Mathlib, AlgebraicAnalysis, all four Comparator configurations, and verifier scripts at the exact revisions named by the source manifest. Run one full Linux repository verifier and all four Palomar comparisons, covering the main and alternative solutions for the two unchanged challenges. The verifier includes the endpoint and consumer axiom reports, paper-linked declaration audit, and import checks. Reuse accepted caches; do not duplicate the full run on another cluster. Record commands, exit statuses, source hashes, log hashes, and whether compiled caches were reused. Keep historic receipts in docs/verification/history/ with their original source revisions.

A successful replay establishes only its listed declarations and configuration. Human review of the mathematics and manuscript correspondence is separate. The existing Palomar record certifies its named theorem and source; local verification does not create a new registry version.

## Freeze and publish

Build every release artifact from the verified source, including the challenge dossier when it is part of the release scope. Check references and layout, and retain the artifact and verification receipt with the release. Confirm that source, map, dependency pins, Comparator configurations, and submitted bundle all correspond to the same frozen revision.

Create a new signed, immutable tag after verification of the selected release scope. Verify the signature before publishing. Never move an existing tag. Publish the matching GitHub release and required assets, then retrieve the archived source bundle and compare its files with the tagged tree. Record a DOI only after the archive has been published and verified; update citation metadata in a subsequent commit without moving the release tag.

## Manuscript and review surfaces

Overleaf remains the manuscript editing authority. Freeze the annotated manuscript and its paper map together for human review. Keep proposed edits visible in this review edition; freeze the accepted text separately for journal submission. The paper comparison must cover the whole selected proof and both Challenge/Solution statements. A different terminal Lean route does not establish proof-route correspondence for intermediate paper claims. Preserve marked author proposals until accepted or revised.

Keep the proof-source, dependency, artifact, and citation pins consistent across the release bundle. Maintain historical release records and receipts unchanged.
