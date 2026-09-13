import NumlibSurface.Rockafellar.Part1
import NumlibSurface.Rockafellar.Part2
import NumlibSurface.Rockafellar.Part3
import NumlibSurface.Rockafellar.Part4
import NumlibSurface.Rockafellar.Part5
import NumlibSurface.Rockafellar.Part6
import NumlibSurface.Rockafellar.Part7
import NumlibSurface.Rockafellar.Part8

/-!
# Rockafellar, *Convex Analysis*

The surface library for R. T. Rockafellar, *Convex Analysis* [rockafellar1970convex]:
thirty-nine modules, one per section of the book, grouped into its eight Parts. Each states the
book's results in the book's own terms and proves them from `Numlib.Analysis.Convex`, the general
backbone. Little is proved here that is not proved there — the surface exists to test the backbone
against a published account of the subject, and to give a reader of the book a Lean name for every
result in it.

**466 of the book's 471 numbered results are formalized.** The five exceptions are in §22.

This module imports the eight Part modules and adds nothing of its own.

## Naming

A declaration is named for the result it states, so the name is the index: `theorem_33_1` is
Theorem 33.1 and `corollary_37_5_2` is Corollary 37.5.2. Where one numbered result needs several
declarations — its separate clauses, or the two directions of an equivalence — a trailing word
tells them apart, as in `theorem_37_5_a` and `theorem_34_2_dom₁`. Everything is in the flat
`Rockafellar` namespace, and `PartN.SectionNN` is the module for §NN.

## The outline

| Part | § | subject |
|---|---|---|
| **I** Basic Concepts | 1 | Affine Sets |
| | 2 | Convex Sets and Cones |
| | 3 | The Algebra of Convex Sets |
| | 4 | Convex Functions |
| | 5 | Functional Operations |
| **II** Topological Properties | 6 | Relative Interiors of Convex Sets |
| | 7 | Closures of Convex Functions |
| | 8 | Recession Cones and Unboundedness |
| | 9 | Some Closedness Criteria |
| | 10 | Continuity of Convex Functions |
| **III** Duality Correspondences | 11 | Separation Theorems |
| | 12 | Conjugates of Convex Functions |
| | 13 | Support Functions |
| | 14 | Polars of Convex Sets |
| | 15 | Polars of Convex Functions |
| | 16 | Dual Operations |
| **IV** Representation and Inequalities | 17 | Carathéodory's Theorem |
| | 18 | Extreme Points and Faces of Convex Sets |
| | 19 | Polyhedral Convex Sets and Functions |
| | 20 | Some Applications of Polyhedral Convexity |
| | 21 | Helly's Theorem and Systems of Inequalities |
| | 22 | Linear Inequalities |
| **V** Differential Theory | 23 | Directional Derivatives and Subgradients |
| | 24 | Differential Continuity and Monotonicity |
| | 25 | Differentiability of Convex Functions |
| | 26 | The Legendre Transformation |
| **VI** Constrained Extremum Problems | 27 | The Minimum of a Convex Function |
| | 28 | Ordinary Convex Programs and Lagrange Multipliers |
| | 29 | Bifunctions and Generalized Convex Programs |
| | 30 | Adjoint Bifunctions and Dual Programs |
| | 31 | Fenchel's Duality Theorem |
| | 32 | The Maximum of a Convex Function |
| **VII** Saddle-Functions and Minimax | 33 | Saddle-Functions |
| | 34 | Closures and Equivalence Classes |
| | 35 | Continuity and Differentiability of Saddle-Functions |
| | 36 | Minimax Problems |
| | 37 | Conjugate Saddle-Functions and Minimax Theorems |
| **VIII** Convex Algebra | 38 | The Algebra of Bifunctions |
| | 39 | Convex Processes |

Numbered results formalized, by Part: I 49, II 84, III 77, IV 65 of 70, V 49, VI 63, VII 58,
VIII 21.

## The ambient space

The book works throughout in `ℝⁿ`. Here `Rn n` is `EuclideanSpace ℝ (Fin n)` and `pairing n` is its
inner product read as a bilinear map, both from `NumlibSurface.Common.Euclidean`. The backbone
states its duality theory for an abstract dual pair of vector spaces, and that one pair
instantiates all of it, which is why the book can state everything without qualification. Where the
backbone is more general still — a bare real vector space, or a topological one — the surface
simply names the finite-dimensional case.

## Where the book needs correcting

Formalizing a book tests it. Six printed statements do not survive; each section module states the
correction, and where a counterexample exists it is a declaration of its own.

* §7 — `epi (cl f) = cl (epi f)`, which the book asserts "by definition", fails for improper convex
  `f`. It holds for the lower semicontinuous hull with no hypothesis, and for `cl f` exactly when
  `f` is proper.
* §13 — the interior clause of Theorem 13.1 needs `C ≠ ∅`, which the book omits: over the zero
  space the stated condition is vacuous while `int ∅ = ∅`.
* §17 — Corollaries 17.1.4 and 17.1.6 are false as printed, with counterexamples on `ℝ` in
  `corollary_17_1_4_false` and `corollary_17_1_6_false`; Theorem 17.3 needs `0 ∉ S*`.
* §29 — the perturbation clause of Corollary 29.4.1 is false as printed.
* §30 — Theorem 30.4(i) and (j) are false as the book states them, and clause (g) needs `F₀` proper.
* §32 — the finiteness clause of Corollary 32.3.2 is false as printed.

A smaller class of divergence is recorded on the declarations themselves: a hypothesis the book
carries and the proof does not need, or one it omits and the proof does. Each such declaration says
so in its own doc comment.

## Not formalized

§22's elementary-vector development — Lemmas 22.4 and 22.5, Corollary 22.4.1, and Theorems 22.6 and
22.7 — is combinatorial matroid theory, which the book itself presents as independent of the rest
of its subject. Those five results are the whole of the gap.

## References

* [rockafellar1970convex].
-/
