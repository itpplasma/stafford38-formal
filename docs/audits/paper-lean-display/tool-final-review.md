# Final read-only repair check

Reviewed `/home/ert/proj/stafford38-formal` at base `87bce83806c757ade36d455d785b506ebd03a1b2` and the tool patch digest recorded in `docs/audits/paper-lean-display/verification.json`. All six listed tool-file SHA-256 values match the current worktree. The HTML and PDF at `/tmp/stafford-audit-display-final-reviewed/` match their frozen artifact SHA-256 values. No files were modified.

1. Active declaration context is surfaced in source-linked “Ambient source declarations,” explicitly labeled as available context rather than a list of required hypotheses. Tests cover scope closure, universes/variables, local instances, notation, and `open`.
2. Definition extraction keeps blank-separated pattern branches and structure fields; regression tests cover both.
3. A body beginning with `by` after whitespace/comments and a line break following `:=` is withheld and marked truncated; a regression test covers this.
4. Automatic predicate expansion avoids a result shadowed by a local variable, follows supported plain `open` scopes, and fails closed on ambiguous duplicate FQNs; tests cover all three.
5. The generated column header now describes declaration-level repository pins. The final-reviewed Global Stafford card uses that header and labels its theorem `GlobalStafford @ e676cae`; the old formal-only card header is absent there.
6. Sign-off hashes include review criteria, vocabulary, and generator inputs. Regression tests confirm rubric and vocabulary edits change the digest.

Independent check: `npm test` in `tools/paper_lean_audit` passes 48/48. I found no remaining material defect among the six reviewed findings. The older `/tmp/stafford-audit-display-final/` artifact is pre-review scratch; the frozen final-reviewed HTML/PDF are the matching artifacts.
