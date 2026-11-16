/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.AppendixB.Chapter02
import NumlibSurface.CartisGouldToint.AppendixB.Chapter03
import NumlibSurface.CartisGouldToint.AppendixB.Chapter04
import NumlibSurface.CartisGouldToint.AppendixB.Chapter05
import NumlibSurface.CartisGouldToint.AppendixB.Chapter07
import NumlibSurface.CartisGouldToint.AppendixB.Chapter08
import NumlibSurface.CartisGouldToint.AppendixB.Chapter10
import NumlibSurface.CartisGouldToint.AppendixB.Chapter12

/-!
# Cartis, Gould and Toint, Appendix B: Technical Results from Individual Chapters

This module collects the formalization of Appendix B of [cartis2022evaluation]. The appendix mostly
contains proofs of results of the chapters, and those proofs belong to the declarations of the
chapters. Only the separately numbered lemmas B.N.k are declarations here, in one module
`AppendixB.ChapterNN` for each chapter that has them, in the namespace `CartisGouldToint.AppendixB`.
Where a result of a chapter needs such a lemma, both specialize a common backbone result, so the
dependencies of the library still run forward in the order of the book. The appendices to Chapters
9, 13 and 14 contain no separately numbered lemmas. The module imports the section modules and adds
nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| Appendix B, Chapter 2 | `AppendixB.Chapter02` | Lemmas B.2.1–B.2.6, zig-zag example |
| Appendix B, Chapter 3 | `AppendixB.Chapter03` | Lemma B.3.1 |
| Appendix B, Chapter 4 | `AppendixB.Chapter04` | Lemma B.4.1, derivatives of $\|s\|^{p+\beta}$ |
| Appendix B, Chapter 5 | `AppendixB.Chapter05` | Lemma B.5.1, the exponents $\iota_j$ |
| Appendix B, Chapter 7 | `AppendixB.Chapter07` | Lemma B.7.1 |
| Appendix B, Chapter 8 | `AppendixB.Chapter08` | Lemmas B.8.1–B.8.2, Newton and secant |
| Appendix B, Chapter 10 | `AppendixB.Chapter10` | Lemma B.10.1, tridiagonal inverses |
| Appendix B, Chapter 12 | `AppendixB.Chapter12` | Lemma B.12.1 |
-/
