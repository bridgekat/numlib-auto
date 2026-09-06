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

# Chapters the plans put out of scope *in full*, each with the reason recorded in the document
# named. These are excluded from the "in scope" figure, which is the one that answers whether a
# book is mostly formalized; the raw figure is reported beside it so the exclusions stay visible.
#
# Only whole-chapter exclusions belong here. Atkinson-Han Chapter 10, for instance, is mostly out
# of scope -- its error estimates need Sobolev spaces, Bramble-Hilbert and elliptic regularity --
# but its 10.4 is planned and partly proved, so the chapter is counted and simply reads low.
OUT_OF_SCOPE: dict[str, dict[int, str]] = {
    "AtkinsonHan": {
        7: "Sobolev spaces on a domain: Mathlib has no weak derivative on an open set "
           "(plans/proposals/atkinsonhan-ch5-onward.md §3)",
        13: "boundary integral equations: needs Sobolev spaces on a boundary (plans/backbone.md §0.2)",
    },
    "SaadSparse": {
        11: "parallel implementations: verified section by section to state no theorem "
            "(plans/proposals/plan-saad10.md)",
    },
    "FongSaunders": {},
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
    # A citation to another work -- "[10, Lemma 5.4.1]" -- is not a result of this book, and a
    # two-component pattern would otherwise read it as "Lemma 5.4". Drop anything inside a
    # bracketed reference, and anything that is the prefix of a longer number.
    return {
        m.group(2)
        for m in re.finditer(pattern, text)
        if not re.search(r"\[\d+,\s*$", text[max(0, m.start() - 24):m.start()])
        and not re.match(r"\.\d", text[m.end():m.end() + 2])
    }


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

        skipped = OUT_OF_SCOPE[key]
        total = len(results)
        pct = 100.0 * len(covered) / total if total else 0.0
        in_scope = {n for n in results if chapter(n) not in skipped}
        in_pct = 100.0 * len(covered & in_scope) / len(in_scope) if in_scope else 0.0
        print(f"== {key}: {len(covered)}/{total} numbered results ({pct:.0f}%)"
              f" -- in scope {len(covered & in_scope)}/{len(in_scope)} ({in_pct:.0f}%)")
        for ch in sorted(by_chapter):
            done, all_ = by_chapter[ch]
            if ch in skipped:
                print(f"   ch {ch:>2}  {'':>3} {all_:<3} out of scope: {skipped[ch]}")
                continue
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
