import NumlibSurface.AtkinsonHan
import NumlibSurface.AtkinsonHan.Chapter01.Section01
import NumlibSurface.AtkinsonHan.Chapter01.Section02
import NumlibSurface.AtkinsonHan.Chapter01.Section05
import NumlibSurface.AtkinsonHan.Chapter01.Section06
import NumlibSurface.AtkinsonHan.Chapter02.Section01
import NumlibSurface.AtkinsonHan.Chapter02.Section03
import NumlibSurface.AtkinsonHan.Chapter02.Section04
import NumlibSurface.AtkinsonHan.Chapter02.Section05
import NumlibSurface.AtkinsonHan.Chapter02.Section06
import NumlibSurface.AtkinsonHan.Chapter02.Section09
import NumlibSurface.AtkinsonHan.Chapter03.Section03
import NumlibSurface.AtkinsonHan.Chapter03.Section04
import NumlibSurface.AtkinsonHan.Chapter03.Section06
import NumlibSurface.AtkinsonHan.Chapter03.Section07
import NumlibSurface.AtkinsonHan.Chapter05.Section01
import NumlibSurface.AtkinsonHan.Chapter05.Section02
import NumlibSurface.AtkinsonHan.Chapter05.Section03
import NumlibSurface.AtkinsonHan.Chapter05.Section04
import NumlibSurface.AtkinsonHan.Chapter05.Section06
import NumlibSurface.AtkinsonHan.Chapter08.Section02
import NumlibSurface.AtkinsonHan.Chapter08.Section03
import NumlibSurface.AtkinsonHan.Chapter08.Section07
import NumlibSurface.AtkinsonHan.Chapter09.Section01
import NumlibSurface.AtkinsonHan.Chapter09.Section02
import NumlibSurface.AtkinsonHan.Chapter09.Section03
import NumlibSurface.AtkinsonHan.Chapter09.Section04
import NumlibSurface.FongSaunders
import NumlibSurface.FongSaunders.Section1
import NumlibSurface.FongSaunders.Section2
import NumlibSurface.FongSaunders.Section3
import NumlibSurface.FongSaunders.Section4
import NumlibSurface.FongSaunders.Section5
import NumlibSurface.SaadSparse
import NumlibSurface.SaadSparse.Chapter01.Section11
import NumlibSurface.SaadSparse.Chapter01.Section12
import NumlibSurface.SaadSparse.Chapter01.Section13
import NumlibSurface.SaadSparse.Chapter04.Section01
import NumlibSurface.SaadSparse.Chapter04.Section02
import NumlibSurface.SaadSparse.Chapter05.Section01
import NumlibSurface.SaadSparse.Chapter05.Section03
import NumlibSurface.SaadSparse.Chapter05.Section04
import NumlibSurface.SaadSparse.Chapter06.Common
import NumlibSurface.SaadSparse.Chapter06.Section02
import NumlibSurface.SaadSparse.Chapter06.Section03
import NumlibSurface.SaadSparse.Chapter06.Section04
import NumlibSurface.SaadSparse.Chapter06.Section05
import NumlibSurface.SaadSparse.Chapter06.Section06
import NumlibSurface.SaadSparse.Chapter06.Section07
import NumlibSurface.SaadSparse.Chapter06.Section08
import NumlibSurface.SaadSparse.Chapter06.Section09
import NumlibSurface.SaadSparse.Chapter06.Section10
import NumlibSurface.SaadSparse.Chapter06.Section11
import NumlibSurface.SaadSparse.Chapter09.Section01
import NumlibSurface.SaadSparse.Common

/-!
# NumlibSurface

The surface layer of the numerical-analysis library: one directory per textbook, aligned to that
text section by section. The backbone it stands on is `Numlib`, a separate library.

A surface proves almost nothing of its own. Each declaration instantiates a backbone result at the
book's own hypotheses, so a surface reads as an integration test of the backbone against a published
account of the subject. If a surface result does not specialize something, that is a demand on the
backbone rather than licence to do new mathematics here. Citing a book by number is correct in this
layer and wrong outside it, where a doc comment names its source in full.

The dependency runs one way, and the split into two Lake libraries is what enforces it: a surface
imports the backbone, the backbone imports no surface, and nothing can quietly reverse that.

## The books

`NumlibSurface.SaadSparse` is Y. Saad, *Iterative Methods for Sparse Linear Systems* (SIAM, 2nd
ed., 2003), covering §1.11–1.13, §4.1–4.2 and Chapters 5 and 6. `NumlibSurface.FongSaunders` is
D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical comparison* (2012), complete.
`NumlibSurface.AtkinsonHan` is K. Atkinson and W. Han, *Theoretical Numerical Analysis: A
Functional Analysis Framework* (Springer, 3rd ed., 2009), covering §2.3–2.5, §3.3–3.7, §5.1–5.4,
§5.6, §8.2–8.3, §8.7 and Chapter 9. Each book's root module is its index: the section-by-section
outline, the ambient conventions, what is deferred, and the places where formalizing the book
corrected it.

## How it is organized

One module is one section of its book, at the book's own numbering: `SaadSparse.Chapter06.Section05`
is Saad §6.5. A module named `Common` is not a section but the vocabulary its siblings share.

**Surface declarations are named for the results they state**, so the name is the index:
`theorem_6_29` is Saad's Theorem 6.29 and `equation_6_43` is his (6.43). Where one numbered result
needs several declarations — its clauses, its CG and its MINRES form, a strict beside a nonstrict
version — a trailing word distinguishes them, as in `theorem_2_2_a` and `theorem_3_1_minres`. A
book's declarations sit in one flat namespace, and `ChapterNN.SectionNN` is the module for §NN.NN.

Each book's reasoning — its conventions, how each book-specific definition maps to the backbone,
what was deferred and why — is in the Markdown at the root of the plan directory:
`saadsparse-ch1-4-5.md`, `saadsparse-ch6.md`, `fongsaunders.md`, `atkinsonhan-ch2-3.md`,
`atkinsonhan-ch5.md`, `atkinsonhan-ch8-9.md`.

## References

* K. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd
  edition, Springer, 2009.
* D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical comparison*, SQU Journal for
  Science 17 (2012) 44–62.
* Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003.
-/
