import NumlibSurface.CartisGouldToint.AppendixA.Section08
import NumlibSurface.CartisGouldToint.AppendixA.Section09
import NumlibSurface.CartisGouldToint.AppendixA.Section10
import NumlibSurface.CartisGouldToint.AppendixB.Chapter02
import NumlibSurface.CartisGouldToint.AppendixB.Chapter03
import NumlibSurface.CartisGouldToint.AppendixB.Chapter05
import NumlibSurface.CartisGouldToint.AppendixB.Chapter07
import NumlibSurface.CartisGouldToint.AppendixB.Chapter08
import NumlibSurface.CartisGouldToint.AppendixB.Chapter10
import NumlibSurface.CartisGouldToint.AppendixB.Chapter12
import NumlibSurface.CartisGouldToint.Chapter01.Section01
import NumlibSurface.CartisGouldToint.Chapter02.Section02
import NumlibSurface.CartisGouldToint.Chapter02.Section03
import NumlibSurface.CartisGouldToint.Chapter02.Section04
import NumlibSurface.CartisGouldToint.Chapter03.Section01
import NumlibSurface.CartisGouldToint.Chapter03.Section02
import NumlibSurface.CartisGouldToint.Chapter03.Section03
import NumlibSurface.CartisGouldToint.Chapter03.Section04
import NumlibSurface.CartisGouldToint.Chapter03.Section05
import NumlibSurface.CartisGouldToint.Chapter04.Section01
import NumlibSurface.CartisGouldToint.Chapter04.Section02
import NumlibSurface.CartisGouldToint.Chapter05.Section01
import NumlibSurface.CartisGouldToint.Chapter05.Section03
import NumlibSurface.CartisGouldToint.Chapter07.Section01
import NumlibSurface.CartisGouldToint.Chapter08.Section01
import NumlibSurface.CartisGouldToint.Chapter08.Section02
import NumlibSurface.CartisGouldToint.Chapter08.Section03
import NumlibSurface.CartisGouldToint.Chapter09.Section01
import NumlibSurface.CartisGouldToint.Chapter09.Section03
import NumlibSurface.CartisGouldToint.Chapter10.Section01
import NumlibSurface.CartisGouldToint.Chapter10.Section02
import NumlibSurface.CartisGouldToint.Chapter10.Section03
import NumlibSurface.CartisGouldToint.Chapter12.Section01
import NumlibSurface.CartisGouldToint.Chapter12.Section02
import NumlibSurface.CartisGouldToint.Chapter13.Section01
import NumlibSurface.CartisGouldToint.Chapter13.Section03
import NumlibSurface.CartisGouldToint.Chapter14.Section01
import NumlibSurface.CartisGouldToint.Chapter14.Section02
import NumlibSurface.CartisGouldToint.Chapter14.Section03

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
* The unscaled Hessian bound (9.3.14c) in Theorem 9.3.2 is false for a general
  metric matrix. Its corrected companion uses the metric-scaled Hessian, as
  the preceding prose requests, and recovers the Euclidean bound for `M=I`.
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
* The nonempty-direction guards in Algorithms 4.1.1 and 5.1.1 can prevent
  termination at a stationary point, where no strictly improving model step exists.
  Theorems 4.1.5 and 5.1.7 are marked incorrect as written; separate corrected
  companions remove these guards. The least-squares counterexample uses an actual
  smooth positive residual and satisfies the printed integer restrictions.
* Corollaries 8.3.1–2 use the full shifted kernel when the least eigenvalue
  is repeated. Their generalized inverse is metric-orthogonal; an ordinary
  Euclidean Moore–Penrose inverse need not give that particular vector. Singular
  interior trust-region minimizers at zero multiplier need only be feasible,
  so the boundary-radius equation is imposed only for positive multipliers.
* The derivative vectors in Algorithm 9.1.1 use the minus sign from (8.2.29).
  With this sign restored they are the actual secular-solution derivatives. The
  scalar outputs also admit a literal plus-sign interpretation with alternating
  vector signs. The following Cholesky prose has an extra factor two: its odd
  output is `−β‖y‖²`, as the algorithm itself gives.
* In Theorem 9.3.1 the starting projection must use the metric inner product.
  The printed Euclidean projection permits an actual two-dimensional run whose
  shifts square and fail to converge, however close the initial shift is to
  the target. The printed statement is marked incorrect; its metric-projection
  companion remains a separate target.
* The final similarity equality in (B.10.4) need only be an inequality.
  Similarity does not preserve the ordinary operator norm. The proved bound
  on the self-adjoint metric operator gives the exact coefficient required
  by Theorem 10.2.2 without adding a spectral premise.
* The short-step accuracy guard in Algorithm 13.1.2 makes the printed parameter
  bounds in Lemmas 13.1.14 and 13.3.5 false when the initial accuracy cap exceeds
  the step-accuracy coefficient. Formal one-trial counterexamples use the zero
  objective and raise the parameter from 32 to 64, above the printed bounds 60
  and 32. Corrected bounds use `max(κs,κh)`; the printed constants are recovered
  under `κh≤κs`. The final Step 2 derivative range is repaired from `1:q` to
  `1:p`, as required by its referenced equation (13.1.46). The literal short-step
  guard is retained despite conflicting preceding prose.
* The norm constant in (B.4.3), part of Lemma B.4.1, fails already in dimension two.
  It remains marked incorrect rather than being represented by a false axiom.

* The unrounded real iteration bound in Theorem 14.3.3 can be smaller than
  one despite a required inner call; its companion uses a natural ceiling.
  Theorem 14.3.4's displayed evaluation constant also fails for arbitrary allowed
  exponents: a smooth affine-residual execution satisfies every actual inner and
  outer test and each per-call count bound, but its two counts sum to 34203,
  above the printed bound of about 31407.86. The valid geometric companion
  retains the primal and dual accuracy exponents.

* Lemma 14.3.5's simultaneous multiplier conclusions fail for a bounded sine
  objective and a linear equality constraint on the Euclidean plane. An actual
  phase-one return, inner solve and target reset pass every merit stopping check.
  The first Lagrangian bound forces the multiplier to zero, where a feasible
  tangent direction refutes the printed second-order bound.

* Theorem 5.3.9's current-measure convergence claim fails for a smooth objective
  and a continuous measure on the Euclidean plane: all trials can satisfy the
  historical-minimum decrease while the current measures equal one at every
  even iterate. Objective gaps and historical measures still converge to zero.
* Lemma 14.1.7's residual value error needs a factor of two in the general
  composite transfer bound. An actual outer-algorithm run with an exact global
  model solve and a legal small radius refutes the displayed coefficient.
  The optional detailed solver's convex unit-radius choice excludes that run;
  the lemma does not impose it. A separate companion uses both value errors.
* Lemma 12.2.11's proved obstruction assumes failure of the true optimality
  certificate. The original statement based on observable nontermination
  remains open. Theorem 12.2.14 only promises to produce a certified iterate,
  and its proved complexity bound preserves that conclusion.

No claim of completeness is made for the open analytic estimates, algorithm
complexity theorems or sharpness constructions.
-/
