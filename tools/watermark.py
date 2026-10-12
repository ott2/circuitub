#!/usr/bin/env python3
"""Watermark Markdown files with the repository and current git commit.

Inserts (or updates) one line after the first level-1 heading:

    $\\tiny\\color{transparent}\\text{provenance: github.com/OWNER/REPO, PATH, on top of commit HASH (DATE)}$

The line is inline TeX math, which GitHub renders with MathJax as invisible
text; it stays in the source, so copies of the file keep their provenance.
A file cannot contain the hash of the commit that adds it, so the hash is that
of HEAD when the tool runs (the commit the edit is written on top of).

Re-running replaces the existing watermark line, recognized by the tag
"provenance:", so the files carry one watermark each.  Legacy HTML-comment
watermarks of the form "<!-- Source: ... -->" are replaced too.

Usage:
    tools/watermark.py FILE.md [FILE.md ...]      # update in place
    tools/watermark.py --check FILE.md ...         # exit 1 if any would change
    tools/watermark.py --style phantom FILE.md     # \\phantom instead of \\color
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

TAG = "provenance:"
# Characters kept in the payload.  MathJax shows `_` literally inside \text, so
# paths keep it; TeX specials such as { } \ $ # % & ^ ~ are dropped.
SAFE = re.compile(r"[^A-Za-z0-9 ./:,()+_-]")
MARK_RE = re.compile(r"^\$.*\\text\{" + re.escape(TAG) + r".*\}\$\s*$")
LEGACY_START = re.compile(r"^<!--\s*Source:")


def git(*args, cwd):
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True,
                          text=True).stdout.strip()


def repo_name(url):
    """git@github.com:o/r.git or https://github.com/o/r(.git) -> github.com/o/r"""
    m = re.match(r"^(?:\w+://)?(?:[^@/]+@)?([^:/]+)[:/](.+?)(?:\.git)?/?$", url)
    return f"{m.group(1)}/{m.group(2)}" if m else url


def safe(s):
    return SAFE.sub("", s)


def mark_line(text, style):
    if style == "phantom":
        return f"$\\tiny\\phantom{{\\text{{{text}}}}}$"
    return f"$\\tiny\\color{{transparent}}\\text{{{text}}}$"


def strip_marks(lines):
    """Remove existing watermark lines and legacy HTML comments, with one blank after."""
    out, i = [], 0
    while i < len(lines):
        line = lines[i]
        if MARK_RE.match(line):
            i += 1
        elif LEGACY_START.match(line):
            while i < len(lines) and "-->" not in lines[i]:
                i += 1
            i += 1
        else:
            out.append(line)
            i += 1
            continue
        if i < len(lines) and lines[i].strip() == "" and out and out[-1].strip() == "":
            i += 1
    return out


def insert_at(lines):
    """Index after the first '# ' heading outside code fences, else 0."""
    fence = False
    for i, line in enumerate(lines):
        if line.lstrip().startswith(("```", "~~~")):
            fence = not fence
        elif not fence and line.startswith("# "):
            return i + 1
    return 0


def watermark(path, style, rev):
    path = Path(path).resolve()
    root = Path(git("rev-parse", "--show-toplevel", cwd=path.parent))
    try:
        url = git("remote", "get-url", "origin", cwd=root)
    except subprocess.CalledProcessError:
        url = root.name
    commit = git("rev-parse", rev, cwd=root)
    date = git("show", "-s", "--format=%cs", commit, cwd=root)
    rel = path.relative_to(root).as_posix()
    text = safe(f"{TAG} {repo_name(url)}, {rel}, on top of commit {commit} ({date})")

    old = path.read_text()
    lines = strip_marks(old.splitlines())
    k = insert_at(lines)
    block = [mark_line(text, style)]
    if k > 0:
        block = [""] + block
    if k < len(lines) and lines[k].strip() != "":
        block = block + [""]
    lines[k:k] = block
    new = "\n".join(lines) + ("\n" if old.endswith("\n") or not old else "")
    return old, new


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("files", nargs="+")
    ap.add_argument("--check", action="store_true", help="report, do not write")
    ap.add_argument("--style", choices=["color", "phantom"], default="color")
    ap.add_argument("--rev", default="HEAD", help="commit to record (default HEAD)")
    a = ap.parse_args()
    changed = 0
    for f in a.files:
        old, new = watermark(f, a.style, a.rev)
        if old != new:
            changed += 1
            print(("would update " if a.check else "updated ") + f)
            if not a.check:
                Path(f).write_text(new)
    return 1 if a.check and changed else 0


if __name__ == "__main__":
    sys.exit(main())
