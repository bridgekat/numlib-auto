import NumlibSurface.Rockafellar.Chapter01
import NumlibSurface.Rockafellar.Chapter02
import NumlibSurface.Rockafellar.Chapter03
import NumlibSurface.Rockafellar.Chapter04
import NumlibSurface.Rockafellar.Chapter05
import NumlibSurface.Rockafellar.Chapter06
import NumlibSurface.Rockafellar.Chapter07
import NumlibSurface.Rockafellar.Chapter08

/-!
# Rockafellar, *Convex Analysis*

The surface library for R. T. Rockafellar, *Convex Analysis* [rockafellar1970convex]:
thirty-nine modules, one per section of the book, grouped into its eight Parts. Each states the
book's results in the book's own terms and proves them from `Numlib.Analysis.Convex`, the general
backbone. Little is proved here that is not proved there — the surface exists to test the backbone
against a published account of the subject, and to give a reader of the book a Lean name for every
result in it.

**466 of the book's 471 numbered results are formalized.** The five exceptions are in §22.

This module imports the eight Chapter modules and adds nothing of its own.

## Naming

A declaration is named for the result it states, so the name is the index: `theorem_33_1` is
Theorem 33.1 and `corollary_37_5_2` is Corollary 37.5.2. Where one numbered result needs several
declarations — its separate clauses, or the two directions of an equivalence — a trailing word
tells them apart, as in `theorem_37_5_a` and `theorem_34_2_dom₁`. Everything is in the flat
`Rockafellar` namespace, and `ChapterNN.SectionMM` is the module for §MM.

## The outline

**The directories `ChapterNN` are the book's Parts I–VIII.** The book groups its material into
Parts and numbers its sections continuously 1–39 across them; `ChapterNN` is the surface layout
every book in this project uses, and the section modules inside keep the book's own global numbers.

| § | module | subject |
|---|---|---|
| | `Common.Euclidean` | conventions: `Rn n`, the pairing `⟨·, ·⟩`, `linFn` |
| **I** | | *Basic Concepts* |
| 1 | `Chapter01.Section01` | Affine sets |
| 2 | `Chapter01.Section02` | Convex sets and cones |
| 3 | `Chapter01.Section03` | The algebra of convex sets |
| 4 | `Chapter01.Section04` | Convex functions |
| 5 | `Chapter01.Section05` | Functional operations |
| **II** | | *Topological Properties* |
| 6 | `Chapter02.Section06` | Relative interiors of convex sets |
| 7 | `Chapter02.Section07` | Closures of convex functions |
| 8 | `Chapter02.Section08` | Recession cones and unboundedness |
| 9 | `Chapter02.Section09` | Some closedness criteria |
| 10 | `Chapter02.Section10` | Continuity of convex functions |
| **III** | | *Duality Correspondences* |
| 11 | `Chapter03.Section11` | Separation theorems |
| 12 | `Chapter03.Section12` | Conjugates of convex functions |
| 13 | `Chapter03.Section13` | Support functions |
| 14 | `Chapter03.Section14` | Polars of convex sets |
| 15 | `Chapter03.Section15` | Polars of convex functions |
| 16 | `Chapter03.Section16` | Dual operations |
| **IV** | | *Representation and Inequalities* |
| 17 | `Chapter04.Section17` | Carathéodory's theorem |
| 18 | `Chapter04.Section18` | Extreme points and faces of convex sets |
| 19 | `Chapter04.Section19` | Polyhedral convex sets and functions |
| 20 | `Chapter04.Section20` | Some applications of polyhedral convexity |
| 21 | `Chapter04.Section21` | Helly's theorem and systems of inequalities |
| 22 | `Chapter04.Section22` | Linear inequalities |
| **V** | | *Differential Theory* |
| 23 | `Chapter05.Section23` | Directional derivatives and subgradients |
| 24 | `Chapter05.Section24` | Differential continuity and monotonicity |
| 25 | `Chapter05.Section25` | Differentiability of convex functions |
| 26 | `Chapter05.Section26` | The Legendre transformation |
| **VI** | | *Constrained Extremum Problems* |
| 27 | `Chapter06.Section27` | The minimum of a convex function |
| 28 | `Chapter06.Section28` | Ordinary convex programs and Lagrange multipliers |
| 29 | `Chapter06.Section29` | Bifunctions and generalized convex programs |
| 30 | `Chapter06.Section30` | Adjoint bifunctions and dual programs |
| 31 | `Chapter06.Section31` | Fenchel's duality theorem |
| 32 | `Chapter06.Section32` | The maximum of a convex function |
| **VII** | | *Saddle-Functions and Minimax Theory* |
| 33 | `Chapter07.Section33` | Saddle-functions |
| 34 | `Chapter07.Section34` | Closures and equivalence classes |
| 35 | `Chapter07.Section35` | Continuity and differentiability of saddle-functions |
| 36 | `Chapter07.Section36` | Minimax problems |
| 37 | `Chapter07.Section37` | Conjugate saddle-functions and minimax theorems |
| **VIII** | | *Convex Algebra* |
| 38 | `Chapter08.Section38` | The algebra of bifunctions |
| 39 | `Chapter08.Section39` | Convex processes |

Numbered results formalized, by Part: I 49, II 84, III 77, IV 65 of 70, V 49, VI 63, VII 58,
VIII 21.

## The ambient space

The book works throughout in `ℝⁿ`. Here `Rn n` is `EuclideanSpace ℝ (Fin n)` and `pairing n` is its
inner product read as a bilinear map, both from `Rockafellar.Common.Euclidean`, the one module here
that is not a section of the book. The backbone states its duality theory for an abstract dual pair
of vector spaces, and that one pair instantiates all of it, which is why the book can state
everything without qualification. Where the backbone is more general still — a bare real vector
space, or a topological one — the surface simply names the finite-dimensional case.

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
