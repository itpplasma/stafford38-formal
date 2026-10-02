#!/usr/bin/env python3
"""Behavior oracle for the exact vendored Palomar source-requirements policy."""
from __future__ import annotations

import tempfile
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scripts.source_requirements import (
    MAX_LEAN_SOURCE_LINES,
    has_module_header,
    inspect_lean_sources,
    physical_lines,
    source_issues,
)


def codes(text: str, name: str) -> set[str]:
    return {issue.code for issue in source_issues(text, name)}


assert "source.module_required" in codes("theorem answer : True := by trivial\n", "NoModule.lean")
assert not codes("-- generated\n/- ordinary /- nested -/ block -/\nmodule Accepted\n", "Accepted.lean")
assert "source.module_required" in codes(
    "/- module Fake /- nested -/ comment -/\ntheorem answer : True := by trivial\n", "CommentTrap.lean"
)
assert "source.module_required" in codes("/-- module documentation -/\nmodule Documented\n", "DocComment.lean")
assert "source.module_required" in codes("/-! module documentation -/\nmodule ModuleDoc\n", "ModuleDoc.lean")
assert "source.module_required" in codes("\ufeffmodule Bom\n", "Bom.lean")
crlf = "-- CRLF comment\r\nmodule CRLF\r\n"
assert has_module_header(crlf)
assert physical_lines("module One\r\n-- two\r\n") == 2
assert physical_lines("module One") == 1
assert "source.module_required" in codes("moduleName IsNotAHeader\n", "Boundary.lean")

at_limit = "module Limit\n" + "-- line\n" * (MAX_LEAN_SOURCE_LINES - 1)
over_limit = at_limit + "-- extra\n"
assert physical_lines(at_limit) == MAX_LEAN_SOURCE_LINES
assert "source.file_too_long" not in codes(at_limit, "Limit.lean")
assert "source.file_too_long" in codes(over_limit, "OverLimit.lean")
assert "source.module_required" not in codes("not a Lean module\n", "sub/lakefile.lean")
assert "source.file_too_long" in codes("x\n" * (MAX_LEAN_SOURCE_LINES + 1), "lakefile.lean")

with tempfile.TemporaryDirectory(prefix="palomar-source-policy-") as temp:
    temp_root = Path(temp)
    root = temp_root / "root"
    root.mkdir()
    (root / "Good.lean").write_text("module Good\n", encoding="utf-8")
    (root / "Bad.lean").write_text("def noHeader := 1\n", encoding="utf-8")
    (root / "lakefile.lean").write_text("set_option autoImplicit false\n", encoding="utf-8")
    (root / "lakefile-too-long.lean").write_text("x\n" * (MAX_LEAN_SOURCE_LINES + 1), encoding="utf-8")
    (root / ".lake").mkdir()
    (root / ".lake" / "Ignored.lean").write_text("no module\n", encoding="utf-8")
    (root / ".git").mkdir()
    (root / ".git" / "Ignored.lean").write_text("no module\n", encoding="utf-8")
    hidden = temp_root / "hidden"
    hidden.mkdir()
    (hidden / "Ignored.lean").write_text("no module\n", encoding="utf-8")
    (root / "linked-dir").symlink_to(hidden, target_is_directory=True)
    (root / "Linked.lean").symlink_to(root / "Good.lean")
    (root / "InvalidUTF8.lean").write_bytes(b"module Invalid\n\xff")
    report, issues = inspect_lean_sources(root)
    codes_seen = {issue.code for issue in issues}
    assert report["files_checked"] == 6
    assert codes_seen == {
        "source.module_required", "source.file_too_long", "source.symlink_not_allowed", "source.invalid_utf8"
    }
    assert {issue.path for issue in issues} == {
        "Bad.lean", "lakefile-too-long.lean", "Linked.lean", "InvalidUTF8.lean"
    }

print("PASS: module/comment parsing, CRLF/LF counts, 10,000-line boundary, lakefile exemption, symlink traversal and invalid UTF-8 match pinned Palomar policy")
