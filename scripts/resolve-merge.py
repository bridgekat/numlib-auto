#!/usr/bin/env python3
"""Resolve the two merge conflicts every agent branch produces.

    python scripts/resolve-merge.py

Sub-agents work in worktrees on disjoint modules, so their Lean and their plan files merge
cleanly. Two files still collide every time, and both have a mechanical resolution:

* `Numlib.lean` and `NumlibSurface.lean` are the libraries' root import files, and each surface has
  a book index module beside its directory (`NumlibSurface/SaadSparse.lean` and its siblings).
  Every branch that adds a module appends an import, and git cannot know the order. They are all
  *generated*: this regenerates every `X.lean` that has a sibling directory `X/`, imports sorted
  and the module doc comment kept verbatim, which is the rule `README.md` states -- the index file
  is regenerated on main rather than edited on branches.
* `notes/lean-lessons.md` is append-only by construction: every branch adds bullets to the same
  handful of sections. Both sides are kept, ours first.

Anything else conflicting is a real disagreement and is left alone for a human -- or for the
orchestrator -- to read.
"""

import io
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIBS = ("Numlib", "NumlibSurface")
LESSONS = "notes/lean-lessons.md"


def conflicted() -> list[str]:
    out = subprocess.run(
        ["git", "diff", "--diff-filter=U", "--name-only"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    )
    return [line for line in out.stdout.split("\n") if line]


def index_modules() -> list[str]:
    """Every `X.lean` that has a sibling directory `X/`: the library roots and the book indices."""
    out = list(LIBS)
    for lib in LIBS:
        for d in sorted((ROOT / lib).iterdir()):
            if d.is_dir() and d.with_suffix(".lean").exists():
                out.append(str(d.relative_to(ROOT)).replace("\\", "/"))
    return out


def regenerate_root(lib: str) -> None:
    """Rewrite `<lib>.lean` as every module under `<lib>/`, sorted, plus its own doc comment."""
    path = ROOT / f"{lib}.lean"
    text = io.open(path, encoding="utf-8", newline="").read()
    # The doc comment survives; the import list is rebuilt. In a conflicted file the markers can
    # fall inside neither, so take the doc comment from the first `/-!` onwards.
    i = text.find("/-!")
    doc = text[i:] if i != -1 else ""
    for marker in ("<<<<<<<", "=======", ">>>>>>>"):
        doc = "\n".join(line for line in doc.split("\n") if not line.startswith(marker))
    modules = sorted(
        ".".join(p.relative_to(ROOT).with_suffix("").parts)
        for p in (ROOT / lib).rglob("*.lean")
    )
    body = "".join(f"import {m}\n" for m in modules)
    io.open(path, "w", encoding="utf-8", newline="").write(body + "\n" + doc.lstrip("\n"))
    print(f"regenerated {lib}.lean with {len(modules)} imports")


def keep_both(path: pathlib.Path) -> None:
    """Keep both sides of every conflict hunk, ours first."""
    text = io.open(path, encoding="utf-8", newline="").read()
    pattern = re.compile(
        r"<<<<<<< [^\n]*\n(?P<ours>.*?)\n?=======\n(?P<theirs>.*?)>>>>>>> [^\n]*\n",
        re.S,
    )
    text, n = pattern.subn(lambda m: m.group("ours").rstrip("\n") + "\n" + m.group("theirs"), text)
    io.open(path, "w", encoding="utf-8", newline="").write(text)
    print(f"kept both sides of {n} hunk(s) in {path.relative_to(ROOT)}")


def main() -> None:
    files = conflicted()
    left = []
    # Regenerate both roots every time, conflict or no conflict: a branch that adds a module to one
    # library and touches nothing else merges *cleanly* into a root file another branch has already
    # rewritten, and the new import is then silently absent. A module nobody imports still builds
    # and is invisible to the tracker, which reports its nodes as `open` with no explanation.
    indices = index_modules()
    for lib in indices:
        regenerate_root(lib)
    for f in files:
        if f in (f"{lib}.lean" for lib in indices):
            pass
        elif f == LESSONS:
            keep_both(ROOT / f)
        else:
            left.append(f)
    subprocess.run(["git", "add", "--"] + [f"{lib}.lean" for lib in indices]
                   + [f for f in files if f not in left], cwd=ROOT, check=True)
    if left:
        print("\nleft for you to resolve by hand:")
        for f in left:
            print("   ", f)
        sys.exit(1)


if __name__ == "__main__":
    main()
