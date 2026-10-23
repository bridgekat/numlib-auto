import NumlibSurface.CartisGouldToint.AppendixA.Section08
import NumlibSurface.CartisGouldToint.AppendixA.Section09
import NumlibSurface.CartisGouldToint.AppendixA.Section10
import NumlibSurface.CartisGouldToint.AppendixB.Chapter02
import NumlibSurface.CartisGouldToint.AppendixB.Chapter03
import NumlibSurface.CartisGouldToint.AppendixB.Chapter05
import NumlibSurface.CartisGouldToint.AppendixB.Chapter07
import NumlibSurface.CartisGouldToint.AppendixB.Chapter08
import NumlibSurface.CartisGouldToint.AppendixB.Chapter12
import NumlibSurface.CartisGouldToint.Chapter01.Section01
import NumlibSurface.CartisGouldToint.Chapter02.Section02
import NumlibSurface.CartisGouldToint.Chapter02.Section03
import NumlibSurface.CartisGouldToint.Chapter02.Section04
import NumlibSurface.CartisGouldToint.Chapter03.Section02
import NumlibSurface.CartisGouldToint.Chapter03.Section03
import NumlibSurface.CartisGouldToint.Chapter04.Section01
import NumlibSurface.CartisGouldToint.Chapter04.Section02
import NumlibSurface.CartisGouldToint.Chapter05.Section01
import NumlibSurface.CartisGouldToint.Chapter07.Section01
import NumlibSurface.CartisGouldToint.Chapter12.Section01
import NumlibSurface.CartisGouldToint.Chapter12.Section02
import NumlibSurface.CartisGouldToint.Chapter13.Section01
import NumlibSurface.CartisGouldToint.Chapter13.Section03
import NumlibSurface.CartisGouldToint.Chapter14.Section01
import NumlibSurface.CartisGouldToint.Chapter14.Section02

/-!
# Cartis–Gould–Toint, *Evaluation Complexity of Algorithms for Nonconvex Optimization*

The surface library for [cartis2022evaluation], organized by the book's chapters,
sections and appendices. The structured plans cover all **232 numbered lemmas,
theorems and corollaries** in the supplied OCR Markdown. There are no separately
numbered definitions or propositions in that transcription. Essential definitions,
models and algorithm traces have additional plan nodes.

This is a partial formalization. A plan entry records a specification, not a proof;
unimplemented results retain their descriptions and dependencies in the plans.
Only declarations imported here have Lean implementations. The tracker distinguishes
proved, open and incorrect-as-transcribed statements.

## Conventions

The namespace is `CartisGouldToint`. Result names retain the source numbering, such
as `lemma_2_3_1` or `lemma_A_10_1`. Surface vector spaces are Euclidean real spaces;
general analytical and algorithm-independent estimates live in `Numlib`.

Iteration prefixes contain precisely the indices `i < N`, so `N` updates take a
parameter from its initial value to its value at index `N`. The inclusive source
set `S_k` corresponds to this prefix with `N = k + 1`. This removes the source
proof's off-by-one shorthand in Lemmas 2.3.1 and 2.4.1. Their hypotheses record the
exact parameter-update component of the algorithms; objective-model selection is
irrelevant to these two counting results.

## Source discrepancies

The supplied Markdown is the source of the plans; a discrepancy has not necessarily
been checked against the printed edition. Corrections and counterexamples are
recorded on the relevant plan nodes. In particular:

* The converse of Theorem 1.1.2 is false for arbitrary closed convex sets when
  critical directions are restricted to actual feasible displacements. Its
  necessary conditions and a corrected tangent-cone sufficiency statement are
  planned separately.
* Strict second-order sufficiency in (1.1.15) and (1.1.18) requires nonzero
  directions. Bounds in Theorem 2.2.2 need to account for small initial steps and
  the first function trial.
* Negative criticality signs are missing in (6.1.5) and (6.1.9). Strictness of
  transformed secular estimates in Chapter 8 needs nonzero data and separate
  treatment of the affine endpoint exponent.
* The isolated-Taylor-minimum claim of Theorem 12.1.5 and the printed constraint
  qualification of Theorem 14.3.1 have explicit counterexamples. Their original
  statements remain marked incorrect in the plans.
* The residual-only uniform bound in Lemma B.2.1 fails for constant polynomials
  of arbitrary height. Its counterexample and a corrected theorem with bounds
  on the initial endpoint data are formalized separately.
* Theorem 12.2.5's all-order stopping conclusion uses the corresponding
  `φ_{f,j}` for each order `j`; the printed repeated `φ_{f,q}` is an index typo.
* Lemma B.8.1 needs a simple root for the stated rates. In the concave
  increasing case the initial residuals have negative sign. Finite termination
  is covered by keeping the root and extending subsequent error ratios by zero.
* The unnumbered cubic Hessian after (3.3.2) is missing a factor `1/2`.
  The corrected actual derivative preserves Lemma 3.3.8's printed bound.
  In Theorem 3.3.9, the derivative budget is `+2`, as its proof and one part
  of its inconsistent display state: one final successful trial and initialization.
* The norm constant in (B.4.3), part of Lemma B.4.1, fails already in dimension two.
  It remains marked incorrect rather than being represented by a false axiom.

No claim of completeness is made for the open analytic estimates, algorithm
complexity theorems or sharpness constructions.
-/
