#!/usr/bin/env python3
"""Book coverage: the numbered results of each book against the surface declarations.

    python scripts/coverage.py [--gaps CHAPTER]

The books' OCR text is expected beside the repository, at `../numlib-books/`. A book result is
counted as covered when a surface declaration is *named* for it -- `theorem_6_29` for Saad's
Theorem 6.29, `theorem_5_4_2` for Atkinson-Han's Theorem 5.4.2 -- which is the convention
`plans/README.md` fixes for surface nodes. Declarations named for their content rather than their
number (`lebesgue_lemma`) are therefore invisible here, so the figure is a *lower* bound; it is
still the right instrument for the question it answers, which is which chapters have been reached
at all.

`--gaps 6` lists the uncovered results of one chapter, which is how a planning agent finds its
next slice.
"""

import argparse
import collections
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent.parent
BOOKS_DIR = HERE.parent / "numlib-books"

# book key -> (surface library subdirectory, OCR file, regex for a numbered result)
BOOKS = {
    "SaadSparse": (
        "iterative-methods-for-sparse-linear-systems-saad",
        r"\b(THEOREM|Theorem|PROPOSITION|Proposition|LEMMA|Lemma|COROLLARY|Corollary"
        r"|DEFINITION|Definition)\s+(\d+\.\d+)\b",
    ),
    "AtkinsonHan": (
        "theoretical-numerical-analysis-atkinson-han",
        r"\b(Theorem|Proposition|Lemma|Corollary|Definition)\s+(\d+\.\d+\.\d+)\b",
    ),
    "FongSaunders": (
        "cg-versus-minres-an-empirical-comparison",
        r"\b(Theorem|Proposition|Lemma|Corollary|Definition)\s+(\d+\.\d+)\b",
    ),
}

DECL = re.compile(
    r"\b(theorem|proposition|lemma|corollary|definition|example|exercise|equation|remark|algorithm)"
    r"_(\d+)_(\d+)(?:_(\d+))?"
)


def book_results(key: str) -> set[str]:
    subdir, pattern = BOOKS[key]
    path = BOOKS_DIR / subdir / f"{subdir}.md"
    if not path.exists():
        sys.exit(f"missing OCR text: {path}")
    text = path.read_text(encoding="utf-8", errors="replace")
    return {m.group(2) for m in re.finditer(pattern, text)}


def surface_numbers(key: str) -> set[str]:
    root = HERE / "NumlibSurface" / key
    out: set[str] = set()
    for f in root.rglob("*.lean"):
        for m in DECL.finditer(f.read_text(encoding="utf-8", errors="replace")):
            _, a, b, c = m.groups()
            out.add(f"{a}.{b}.{c}" if c else f"{a}.{b}")
    return out


def chapter(num: str) -> int:
    return int(num.split(".")[0])


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--gaps", metavar="CHAPTER", help="list the uncovered results of one chapter")
    ap.add_argument("--book", help="restrict to one book")
    args = ap.parse_args()

    for key in BOOKS:
        if args.book and args.book != key:
            continue
        results = book_results(key)
        covered = surface_numbers(key) & results
        by_chapter: dict[int, list[int]] = collections.defaultdict(lambda: [0, 0])
        for n in results:
            by_chapter[chapter(n)][1] += 1
        for n in covered:
            by_chapter[chapter(n)][0] += 1

        total = len(results)
        pct = 100.0 * len(covered) / total if total else 0.0
        print(f"== {key}: {len(covered)}/{total} numbered results ({pct:.0f}%)")
        for ch in sorted(by_chapter):
            done, all_ = by_chapter[ch]
            bar = "#" * round(20 * done / all_) if all_ else ""
            print(f"   ch {ch:>2}  {done:>3}/{all_:<3} {bar}")

        if args.gaps:
            want = int(args.gaps)
            missing = sorted(
                (n for n in results - covered if chapter(n) == want),
                key=lambda n: [int(p) for p in n.split(".")],
            )
            print(f"   uncovered in chapter {want}: {', '.join(missing) or 'none'}")


if __name__ == "__main__":
    main()
