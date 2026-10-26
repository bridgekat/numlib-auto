import NumlibSurface.CartisGouldToint.Chapter01
import NumlibSurface.CartisGouldToint.Chapter02
import NumlibSurface.CartisGouldToint.Chapter03
import NumlibSurface.CartisGouldToint.Chapter04
import NumlibSurface.CartisGouldToint.Chapter05
import NumlibSurface.CartisGouldToint.Chapter06
import NumlibSurface.CartisGouldToint.Chapter07
import NumlibSurface.CartisGouldToint.Chapter08
import NumlibSurface.CartisGouldToint.Chapter09
import NumlibSurface.CartisGouldToint.Chapter10
import NumlibSurface.CartisGouldToint.Chapter11
import NumlibSurface.CartisGouldToint.Chapter12
import NumlibSurface.CartisGouldToint.AppendixA
import NumlibSurface.CartisGouldToint.AppendixB

/-!
# Cartis–Gould–Toint, *Evaluation Complexity of Algorithms for Nonconvex Optimization*

The surface library for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization: Theory, Computation and Perspectives*, MOS–SIAM Series on
Optimization 30, SIAM, 2022 [cartis2022evaluation]. Each module states the book's results in the
book's own terms and proves them from Mathlib and the general backbone `Numlib` — chiefly
`Numlib.Optimization` (generic trust-region and adaptive-regularization runs, evaluation counting,
Taylor models, criticality measures, slow-example constructions, the subproblem theory) — so that
the surface tests the backbone against a published account of the subject and gives a reader of
the book a Lean name for every numbered result of the chapters it covers.

The book bounds the number of evaluations of the objective and its derivatives that an algorithm
needs to find an approximate first-, second- or higher-order critical point of a smooth nonconvex
function, shows that the bounds are sharp, and treats the subproblems that the algorithms solve.

This module imports the chapter index modules and adds nothing of its own; each chapter index
lists its sections, how its numbered items map to declarations, and its deviations from the book.

## Naming

A declaration is named for the item it states: `theorem_3_3_5` is Theorem 3.3.5, `lemma_B_4_1_i`
is Lemma B.4.1 (i), `corollary_8_2_4`, `example_12_2_2`, `eq_A_16` is the display (A.16), and
`algorithm_2_3_1` is Algorithm 2.3.1 as a run predicate. Clauses of one result are told apart by a
roman-numeral or descriptive suffix (`theorem_4_1_5_ii`, `theorem_12_1_5_counterexample`). The
book's named assumptions are structures `AssumptionXY` (f.gL is `AssumptionGL`, f.DpL is
`AssumptionDpL`), and its constants are definitions named for their symbols (`kappaSDBA`,
`sigmaMaxAR2`). Module `ChapterNN.SectionMM` is §N.M (namespace `CartisGouldToint.ChapterNN`),
`AppendixA.SectionMM` is §A.M (namespace `CartisGouldToint.AppendixA`), and `AppendixB.ChapterNN`
holds the separately numbered Lemmas B.N.k (namespace `CartisGouldToint.AppendixB`). Within the
library dependencies run forward in the book's order.

## The outline

| | module | subject |
|---|---|---|
| 1 | `Chapter01` | Introduction: optimality conditions, criticality measures |
| **I** | | *Evaluation complexity for low-order optimality* |
| 2 | `Chapter02` | Methods using first derivatives: SDBA, SDEX, TR1, AR1 |
| 3 | `Chapter03` | Methods using second derivatives: Newton, TR2, AR2, TRε, iRN, the class `𝓜` |
| 4 | `Chapter04` | Methods using third derivatives and beyond: ARp, a lower bound |
| 5 | `Chapter05` | Structured problems: least squares, measure domination, ARp-H |
| 6 | `Chapter06` | Convexly constrained problems: ARp-CC, ARp1-CC, ARpLE-CC |
| 7 | `Chapter07` | Problems with nonconvex constraints: TPp-GC |
| 8 | `Chapter08` | Subproblem fundamentals: the secular function, the hard case |
| 9 | `Chapter09` | Step computation with factorizations |
| 10 | `Chapter10` | Step computation without factorizations: Lanczos, Krylov subspace solutions |
| 11 | `Chapter11` | Variable scaling and other practicalities |
| **II** | | *Evaluation complexity for higher-order optimality* |
| 12 | `Chapter12` | Finding high-order approximate minimizers: `φ^δ_{f,j}`, TRq, ARqp |
| A | `AppendixA` | Taylor's theorem, Hermite interpolation, series bounds |
| B | `AppendixB` | the separately numbered lemmas of the chapter appendices |

Chapters 13 ("Inexact function values and derivatives") and 14 ("Composite and constrained
problems") are not yet part of the library; their plans are under
`plans/NumlibSurface/CartisGouldToint/`. Part III ("Conclusions and perspectives") has no numbered
items.

## Conventions

* Problems live on `ℝⁿ = EuclideanSpace ℝ (Fin n)`. Gradients are `gradient f x`, higher
  derivatives `iteratedFDeriv ℝ j f x` with the operator norm of multilinear maps as the tensor
  norm (A.7), `λ_min[∇²f(x)]` is `minCurvature (iteratedFDeriv ℝ 2 f x)`
  (`Chapter01.hessianMinEig`), and Taylor models are built from `ftaylorSeries ℝ f x`.
* **Algorithms are run predicates**: a run is a sequence of iterates (with radii, regularization
  weights, …) obeying the algorithm's rules at every iteration before the first one that passes
  the termination test, with the book's nondeterministic choices (inexact subproblem solutions,
  parameter updates within ranges) left as hypotheses. Every algorithm has an existence theorem,
  or a counterexample where runs need not exist.
* **Complexity theorems** assert the existence of the first termination index and explicit bounds
  on the evaluation counts `Optimization.funEvalCount` and `Optimization.derivEvalCount`.
  **Sharpness theorems** exhibit a function in the class and a run whose first termination index
  is the claimed count.
* Infinite tolerances: `ε₂ = +∞` is `none : Option ℝ` (Chapters 3–4), or the order `q` of the
  sought minimizer is explicit and the higher-order tests are switched off (Chapters 5, 6 and 12).
* In Chapters 8–11, `H` is symmetric, `M` symmetric positive definite, and every statement is
  transported through the `M`-inner product space `Subproblem.ScaledSpace` to the operator
  backbone.

## Where the book needs correcting

Each section module lists its deviations, and each chapter index summarizes them. The most
significant are statements that are false as printed, each with a counterexample declaration
where one exists:

* **Theorem 1.1.2, converse**: strict curvature on the radial directions does not give a local
  minimizer on a convex set (`Chapter01.theorem_1_1_2_iv_counterexample`); the tangent cone is
  needed.
* **Theorem 2.2.2**: the SDBA evaluation bound (2.2.8) vanishes for small `t_ini`; corrected.
* **Lemma 5.4.2**: the step bound (5.4.8) is false; the constant `κ_s = 2(1 + θ₁)/λ_*` replaces it.
* **Theorems 3.4.6, 3.4.12, Lemma 7.2.6, Theorem 7.2.7**: counting arguments that do not count
  every iteration. For TRε and iRN the bounds hold with a factor `2`. For TPp-GC the gap is not
  closed: the "bad" outer iterations, at which no decrease is guaranteed, are unbounded by the
  book's argument, and `Chapter07.theorem_7_2_7` carries their number as a parameter.
* **Third-order ARp and the convexly constrained ARp-CC are not always well posed**: admissible
  steps need not exist (`Chapter04.not_exists_algorithm_4_1_1_third_order`,
  `Chapter06.algorithm_6_2_1_not_exists_step`); the complexity theorems are statements about runs.
  The requirement `𝓜_k ≠ ∅` of the third-order tests of ARp and ARpLE is dropped (with it, runs can
  get stuck and the counting fails).
* **Theorem 4.2.6**: only `#_ε ≥ k̄` (not `2k̄`) follows; (4.2.6) has a misprinted first term.
* **Theorem 12.1.5**: an isolated minimizer of the Taylor model need not be uniformly isolated
  (`Chapter12.theorem_12_1_5_counterexample`); a growth hypothesis is added.
* **Theorem 12.2.15 for `q ≥ 3`**: its own example violates its hypothesis
  (`Chapter12.theorem_12_2_15_counterexample`); it is stated for a global-step scenario that is a
  genuine ARqp run for `q ≤ 2`. Lemmas 12.2.11–12.2.13 need `θ < ς` and a corrected constant `κ̂`.
* **Lemma B.4.1 (B.4.3)**: false for `β < 1` (`AppendixB.lemma_B_4_1_iii_false`); true for `β = 1`,
  the case the book uses.
* **Theorem 9.3.2** is false with the Euclidean `λ_min` when `M ≠ I`, and **Theorem 9.3.1** omits
  its hypothesis `z₀ ∈ 𝒵₁` (to be read in the `M`-inner product); Lemma B.8.1 needs
  `θ'(λ*) ≠ 0`.
* **Chapter 11**: (11.2.3), (11.2.5) and the regularization case of §11.1.3 are printed inverted
  or with wrong exponents.

Smaller repairs — OCR damage restored, index slips, constants recomputed, the ARqp Step-1 test
normalized to `>`, hypotheses the proofs do not need dropped — are recorded in the section modules
and on the declarations.

## Not formalized

* Lemma 4.2.5 (iv), explicit growth `L^D_p ≤ exp(5/2 p log p + c₁ p)` of the hard function's
  constant (the lemma itself is proved with an explicit constant).
* The starting values (right limits at `λₛ`) of Corollary 8.2.4.
* The norm comparisons `‖H‖₂ ≤ min(‖H‖_∞, ‖H‖_F)`, `|λᵢ| ≤ ‖H‖_F` quoted in §9.3.1, the heuristic
  procedure of §9.3.7 and the tests (9.4.2)–(9.4.4).
* Discussion without numbered results: the variants of §2.2.3, §4.1.3, §7.2.3, the qualitative parts
  of §§5.3.1, 12.1.6, 12.3, the `O(·)` restatements and Table 12.2.1, and the weak approximate
  minimizers (12.1.40) of the Notes.
* Chapters 13 and 14.
-/
