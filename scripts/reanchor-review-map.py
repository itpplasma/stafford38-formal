#!/usr/bin/env python3
"""Refresh candidate paper line anchors and visible AI comments in a review map.

Usage: reanchor-review-map.py --paper PATH --map PATH [--commit REV]
PATH may be the manuscript file or its Git repository root. When it is a
repository root, human_readable_main.tex is used unless --paper-file is given.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ENVIRONMENTS = ("theorem", "lemma", "proposition", "corollary", "definition",
                "convention", "remark")
PROOF_LABELS = {
    "lem:componentwise-involutive", "lem:sympcompl", "prop:monic",
    "lem:order-symbol", "lem:euler", "lem:euler-residue", "prop:x-surjective",
    "lem:tangential-finiteness", "lem:page-inequality",
    "lem:strict-support-inequality", "lem:Uzero", "cor:charP",
    "prop:char-avoids", "lem:tangent-limit", "thm:coisotropic-exclusion",
    "lem:initial-base-change", "prop:noncar",
}

class Anchors:
    def __init__(self, lines: list[str]):
        self.lines = lines

    def find(self, needle: str, start: int = 1) -> int:
        for n in range(start, len(self.lines) + 1):
            if needle in self.lines[n - 1]:
                return n
        raise ValueError(f"anchor text not found: {needle!r}")

    def maybe(self, needle: str, start: int = 1) -> int | None:
        try:
            return self.find(needle, start)
        except ValueError:
            return None

    def label(self, name: str) -> int:
        return self.find(f"\\label{{{name}}}")

    def section(self, needle: str) -> int:
        for n, line in enumerate(self.lines, 1):
            if re.search(r"\\(?:sub)*section\*?\{", line) and needle in line:
                return n
        raise ValueError(f"section not found: {needle!r}")

    def env_range(self, label: str, include_proof: bool = False) -> list[int]:
        label_line = self.label(label)
        opener = None
        for n in range(label_line, max(0, label_line - 10), -1):
            for env in ENVIRONMENTS:
                if f"\\begin{{{env}}}" in self.lines[n - 1]:
                    opener = (n, env)
                    break
            if opener:
                break
        if not opener:
            raise ValueError(f"no statement environment found for label {label}")
        start, env = opener
        depth, end = 0, None
        for n in range(start, len(self.lines) + 1):
            line = self.lines[n - 1]
            depth += line.count(f"\\begin{{{env}}}")
            depth -= line.count(f"\\end{{{env}}}")
            if depth == 0:
                end = n
                break
        if end is None:
            raise ValueError(f"unclosed {env} for label {label}")
        if include_proof:
            # AI additions/comments may sit between the statement and proof.
            # Stop at the next section or a new ordinary statement environment.
            for n in range(end + 1, min(len(self.lines), end + 100) + 1):
                line = self.lines[n - 1]
                if "\\section{" in line:
                    break
                if "\\begin{proof}" in line:
                    depth = 0
                    for k in range(n, len(self.lines) + 1):
                        depth += self.lines[k - 1].count("\\begin{proof}")
                        depth -= self.lines[k - 1].count("\\end{proof}")
                        if depth == 0:
                            end = k
                            break
                    break
                if label != "thm:coisotropic-exclusion" and any(
                    f"\\begin{{{other}}}" in line for other in ENVIRONMENTS
                ):
                    break
        return [start, end]

    def through_before(self, start: int, next_needle: str) -> list[int]:
        end = self.find(next_needle, start + 1) - 1
        return [start, end]

    def preceding_section(self, start: int, next_section: str) -> list[int]:
        end = self.section(next_section) - 1
        return [start, end]

def resolve_paper(path: Path, paper_file: str | None, requested_commit: str | None) -> tuple[Path, Path, str]:
    path = path.resolve()
    if path.is_file():
        tex = path
        repo = Path(subprocess.check_output(
            ["git", "-C", str(tex.parent), "rev-parse", "--show-toplevel"], text=True
        ).strip())
        rel = tex.relative_to(repo).as_posix()
    else:
        repo = Path(subprocess.check_output(
            ["git", "-C", str(path), "rev-parse", "--show-toplevel"], text=True
        ).strip())
        rel = paper_file or "human_readable_main.tex"
        tex = repo / rel
    if not tex.is_file():
        raise SystemExit(f"manuscript file does not exist: {tex}")
    revision = requested_commit or "HEAD"
    commit = subprocess.check_output(
        ["git", "-C", str(repo), "rev-parse", revision], text=True
    ).strip()
    return repo, tex, commit

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--paper", required=True, type=Path, help="manuscript file or paper Git repository")
    ap.add_argument("--paper-file", help="file path relative to repo when --paper is a directory")
    ap.add_argument("--commit", help="manuscript source commit; defaults to repository HEAD")
    ap.add_argument("--map", required=True, type=Path, help="paper-lean-map.json to update")
    args = ap.parse_args()

    repo, tex, commit = resolve_paper(args.paper, args.paper_file, args.commit)
    # Freeze the selected Git object, even if the checkout has later edits.
    raw = subprocess.check_output([
        "git", "-C", str(repo), "show", commit + ":" + tex.relative_to(repo).as_posix()
    ])
    lines = raw.decode("utf-8").splitlines()
    a = Anchors(lines)
    data = json.loads(args.map.read_text(encoding="utf-8"))
    items = {item["id"]: item for item in data["items"]}

    # Stable, labelled statement cards. Proof-bearing cards include a matched
    # proof environment where the proof belongs to that statement.
    for item in data["items"]:
        label = item.get("label")
        if not label:
            continue
        if item["id"] == "cotangent":
            item["tex_lines"] = [a.label(label), a.label("def:filtration") - 1]
        elif label == "app:ai-workflow":
            item["tex_lines"] = [a.label(label), a.section("Further work") - 1]
        elif label in {"eq:I-Q", "eq:nonnegative-pbw"}:
            n = a.label(label)
            env = "equation" if label == "eq:I-Q" else "align"
            begin = next(k for k in range(n, max(0, n - 10), -1)
                         if f"\\begin{{{env}}}" in lines[k - 1])
            end = next(k for k in range(n, len(lines) + 1)
                       if f"\\end{{{env}}}" in lines[k - 1])
            item["tex_lines"] = [begin, end]
        else:
            item["tex_lines"] = a.env_range(label, label in PROOF_LABELS)

    # Excerpts without labels use text/neighboring-label boundaries so they
    # survive annotation line shifts and removal of AI comment boxes.
    def set_range(i: str, pair: list[int]) -> None:
        items[i]["tex_lines"] = pair

    abstract = a.find("\\begin{abstract}")
    set_range("abstract", [abstract, a.find("\\end{abstract}", abstract)])
    # The introductory issue note precedes the theorem environment but belongs
    # to the main theorem card's statement context.
    global_start = a.find("The machine-checked proof of this result")
    set_range("thm:main", [a.section("Introduction") + 1, global_start - 1])
    set_range("global-stafford", a.through_before(global_start, "\\textit{Proof sketch:}"))
    sketch = a.find("\\textit{Proof sketch:}")
    prior = a.find("Constructive predecessors concern Stafford")
    set_range("intro-proof-sketch", [sketch, prior - 1])
    set_range("context-prior-art", a.through_before(prior, "\\section{\\texorpdfstring"))
    formal = a.section("Formal verification")
    notation = a.section("Notation and definitions")
    set_range("formal-verification", [formal, notation - 1])
    set_range("conv:H", [a.env_range("conv:H")[0], a.section("Cotangent space") - 1])
    set_range("def:involutive", [a.env_range("def:involutive")[0], a.section("Gabber's theorem") - 1])
    set_range("ithm:gabber", [a.env_range("ithm:gabber")[0], a.env_range("lem:componentwise-involutive")[0] - 1])
    set_range("lem:componentwise-involutive", [a.env_range("lem:componentwise-involutive")[0], a.section("Mapping to a monic normal form") - 1])
    set_range("lem:sympcompl", [a.env_range("lem:sympcompl")[0], a.env_range("prop:monic")[0] - 1])
    field_anchor = a.maybe("All coefficients involved belong") or a.find("Sections~\\ref{sec:monic}--\\ref{sec:char} work over")
    set_range("prop:monic", [a.env_range("prop:monic")[0], field_anchor - 1])
    scalar = a.find("If $N=0$")
    symplectic = a.find("We want to construct a well-behaved automorphism")
    set_range("monic-scalar", [scalar, symplectic - 1])
    symp_label = a.label("lem:sympcompl")
    phi = a.find("We want to construct a well-behaved automorphism")
    set_range("phi-g", [phi, symp_label - 1])
    try:
        field = a.find("Sections~\\ref{sec:monic}--\\ref{sec:char} work over")
        rem = a.label("rem:transport")
        set_range("reduction-k0", [field, rem - 1])
    except ValueError:
        # The explanatory paragraph may be removed after author acceptance.
        start = a.env_range("prop:monic")[1] + 1
        set_range("reduction-k0", [start, a.label("rem:transport") - 1])
    iq = a.label("eq:I-Q")
    set_range("eq:I-Q", [iq - 1, a.find("\\end{equation}", iq) + 1])
    euler = a.find("The adjoint action of $E$ defines a grading")
    set_range("euler-grading", [euler, a.env_range("lem:euler")[0] - 1])
    vc = a.section("Vanishing cokernel")
    set_range("vc-setup", [vc, a.env_range("def:length")[0] - 1])
    set_range("lem:tangential-finiteness", [a.env_range("lem:tangential-finiteness")[0],
                                             a.env_range("lem:page-inequality")[0] - 1])
    set_range("lem:page-inequality", [a.env_range("lem:page-inequality")[0],
                                      a.env_range("lem:strict-support-inequality")[0] - 1])
    set_range("lem:euler-residue", [a.env_range("lem:euler-residue")[0],
                                    a.env_range("prop:x-surjective")[0] - 1])
    set_range("prop:x-surjective", [a.env_range("prop:x-surjective")[0], vc - 1])
    set_range("lem:strict-support-inequality", [a.env_range("lem:strict-support-inequality")[0],
                                                a.env_range("lem:Uzero")[0] - 1])
    conormal = a.section("A conormal direction at infinity")
    set_range("prop:char-avoids", [a.env_range("prop:char-avoids")[0], conormal - 1])
    tangent = a.env_range("lem:tangent-limit")
    tangent_end = a.env_range("thm:asymptotic-conormal")[0] - 1
    set_range("dir-def", [conormal, tangent[0] - 1])
    set_range("lem:tangent-limit", [tangent[0], tangent_end])
    thm8 = a.env_range("thm:asymptotic-conormal")
    proof8_start = a.find("\\begin{proof}", thm8[1])
    depth, proof8_end = 0, None
    for n in range(proof8_start, len(lines) + 1):
        depth += lines[n - 1].count("\\begin{proof}") - lines[n - 1].count("\\end{proof}")
        if depth == 0:
            proof8_end = n
            break
    route_comment = a.maybe("\\AIcomment{ROUTE-01}", thm8[1])
    involutive = a.section("The involutive obstruction")
    set_range("thm:asymptotic-conormal-proof", [route_comment or proof8_start, involutive - 1])
    assembly = a.section("Proof of Theorem")
    set_range("thm:coisotropic-exclusion", [a.env_range("thm:coisotropic-exclusion")[0], assembly - 1])
    base_change = a.env_range("lem:initial-base-change")[0]
    base_change_wrapper = a.find("\\begin{AIaddition}{Base change of the order initial ideal}")
    set_range("proof-main", [assembly, base_change_wrapper - 1])
    set_range("lem:initial-base-change", [base_change_wrapper,
                                          a.find("as Stafford already showed") - 1])
    cyclicity = a.env_range("cor:cyclic")[0]
    set_range("cyclicity", [cyclicity, a.section("Outlook") - 1])
    set_range("lem:Uzero", [a.env_range("lem:Uzero")[0], a.env_range("cor:charP")[0] - 1])
    outlook = a.section("Outlook")
    further = a.section("Further work")
    clearpage = a.find("\\clearpage", outlook)
    set_range("outlook", [outlook, clearpage - 1])
    set_range("further-work", [further, a.section("Noncharacteristic H") - 1])

    # Four appendix claims are keyed to their prose labels and neighboring
    # paragraph labels, not the movable AI comment box.
    refs = [
        ("appendix-right-ore", "identity in every right Ore localization", "the left-handed identity"),
        ("appendix-left-handed", "the left-handed identity", "the identity for finite-order differential operators"),
        ("appendix-localized-differential", "the identity for finite-order differential operators", "and, independently of the geometric argument"),
        ("appendix-evolutionary", "and, independently of the geometric argument", "\\subsection{Noncharacteristic H}"),
    ]
    for iid, start_text, end_text in refs:
        start = a.find(start_text)
        end = a.find(end_text, start + 1) - 1
        set_range(iid, [start, end])

    # Refresh visible comment IDs/lines while retaining existing verdicts/notes.
    previous = {comment["id"]: comment for comment in data.get("aicomments", [])}
    comments = []
    for n, line in enumerate(lines, 1):
        match = re.search(r"\\AIcomment\{([^}]+)\}", line)
        if not match:
            continue
        cid = match.group(1)
        comment = dict(previous.get(cid, {
            "id": cid,
            "verdict": "Author proposal",
            "note": "Current manuscript annotation; author acceptance is separate from machine verification.",
        }))
        comment["line"] = n
        comments.append(comment)
    data["aicomments"] = comments

    candidate = data.setdefault("candidate", {})
    candidate["status"] = "pending-final-source-pins"
    candidate["manuscript"] = {
        "repo": "itpplasma/stafford38-paper",
        "commit": commit,
        "file": tex.relative_to(repo).as_posix(),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }
    candidate["note"] = (
        "Line anchors refer to the manuscript bytes above. Historical paper and formal pins remain listed under sources; "
        "final proof-source pins and complete paper-to-Lean correspondence are pending. This map is a candidate, "
        "not a completed whole-paper audit."
    )
    # Keep the established one-space JSON style used by the map.
    args.map.write_text(json.dumps(data, indent=1, ensure_ascii=True) + "\n", encoding="utf-8")
    print(f"Updated {args.map}: {len(items)} cards, {len(comments)} visible comments")
    print(f"Manuscript {candidate['manuscript']['commit']} sha256 {candidate['manuscript']['sha256']}")

if __name__ == "__main__":
    main()
