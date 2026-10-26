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
import NumlibSurface.CartisGouldToint.Chapter13
import NumlibSurface.CartisGouldToint.Chapter14
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
| 13 | `Chapter13` | Inexact function values and derivatives: TRqIDA, ARqpIDA, TRqEDA, ARqpEDA |
| 14 | `Chapter14` | Composite and constrained problems: ARqpC, `-SC` variants, LENq-SC, TPqp-GC |
| A | `AppendixA` | Taylor's theorem, Hermite interpolation, series bounds |
| B | `AppendixB` | the separately numbered lemmas of the chapter appendices |

Part III ("Conclusions and perspectives") has no numbered items.

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
  sought minimizer is explicit and the higher-order tests are switched off (Chapters 5, 6 and
  12–14).
* Inexact derivatives (Chapter 13) are jets `FormalMultilinearSeries ℝ ℝⁿ ℝ` within the error
  model `Optimization.JetApprox` of the exact `ftaylorSeries ℝ f x`; methods without a
  termination rule (TRqIDA, ARqpIDA) are bounded up to the first truly approximately optimal
  iterate.
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
* **Theorems 13.1.19 and 13.3.8**: the printed radius-one conclusion `φ^1_{f,j}(x_ε) ≤ ε_j/j!`
  is not what the proof certifies (it conflates the radii before and after Step 1); the theorems
  are stated for some radii in `(0, 1]^q`, from which radius one follows for `q ≤ 2`. Lemma 13.1.17
  needs a corrected constant `κ̂`.
* **ARqpEDA (Lemma 13.3.7, Theorem 13.3.8)**: the book reuses Lemma 13.1.16, whose hypothesis
  does not follow from non-termination; the corrected argument needs `θ < ς/2`, with `ς/2 - θ`
  for `1 - θ` in the constants. The orders are unchanged.
* **Lemmas 14.1.7–14.1.9, Theorem 14.1.10**: `(1 - θ)` must be `(ς - θ)`, with `θ < ς`, as in
  Lemma 12.2.11; (14.1.30) misses a factor `2` and (14.1.31) a factor `ε_j^{(j+1)/(p+1)}`.
* **Theorem 14.3.1**: the descriptor arcs must be feasible for `X ∩ {c = 0}`, not only for `X`;
  as printed the theorem fails for `c(x) = x₁² + x₂²`, `f(x) = -x₁`, `x⋆ = 0`. Example 14.3.1's
  origin is a minimizer, not a saddle point.
* **Theorem 14.3.4** (and Lemma 14.3.7, Theorem 14.3.9): the proof uses
  `∑_k max_j ≤ max_j ∑_k`, which is false; the bounds hold with `∑_j` for `max_j`.
* **Lemma 14.3.5**: (14.3.43) and (14.3.46) are false (e.g. `c ≡ 0`, `X = [-1, 1]`,
  `f(x) = x/4 - 25x²/8`, `Chapter14.lemma_14_3_5_counterexample`); they are corrected with terms
  of order `(‖∇f‖δ)²/(f(x_ε) - t_ε)`.
  When Phase 2 ends with `f(x_ε) = t_ε`, only the first-order part of (14.3.41) follows.
* **Lemma 14.3.8, Theorem 14.3.9**: TPqp-GC has the same counting gap as TPp-GC: the bad outer
  iterations are not bounded by the book's argument, and `Chapter14.theorem_14_3_9` carries
  their number as a parameter. INNER's certificate closes the gap when `β < θ` (the book allows
  `β = θ`) and the derivatives of `f` are bounded: every case-(b) iteration then lowers the target
  by a fixed amount (`Chapter14.IsTPqpGCPhase2.kbCount_le`), and the constructed runs with
  INNER = ARqp-SC satisfy Theorem 14.3.9 without the parameter
  (`Chapter14.exists_algorithm_14_3_2_complexity_certified`).
* **Lemma B.4.1 (B.4.3)**: false for `β < 1` (`AppendixB.lemma_B_4_1_iii_false`); true for `β = 1`,
  the case the book uses.
* **Theorem 9.3.2** is false with the Euclidean `λ_min` when `M ≠ I`, and **Theorem 9.3.1** omits
  its hypothesis `z₀ ∈ 𝒵₁` (to be read in the `M`-inner product); Lemma B.8.1 needs
  `θ'(λ*) ≠ 0`.
* **Chapter 11**: (11.2.3), (11.2.5) and the regularization case of §11.1.3 are printed inverted
  or with wrong exponents.

Evaluation counts are recounted throughout: several derivative bounds omit the initial evaluation
or the last accuracy-improving iteration (Lemma 7.2.2, Theorems 13.1.8, 13.1.19, 13.3.4, 13.3.8:
`κ^F + 2`, resp. `+ 3`), the constant `κ^C` of Theorem 13.1.19 misses a factor
`1 + |log γ₁|/log γ₂`, and Theorem 13.3.4's garbled constants are a factor `2`.

Smaller repairs — OCR damage restored, index slips, constants recomputed, the ARqp Step-1 test
normalized to `>`, hypotheses the proofs do not need dropped — are recorded in the section modules
and on the declarations.

## Not formalized

* The sharpness of the ARqpIDA-SC row of Theorem 14.2.4 in the lower-bound mode of the radii control
  for `3 ≤ q < p` and for `q = 2 < p` on `X ≠ ℝⁿ` (on `ℝⁿ` the mode-`False` bound is not attained
  for `q = 2 < p`, `theorem_14_2_4_arqpida_le_two`); existence and complexity of LENq-SC and TPqp-GC
  runs under the book's anchored (rather than global) Lipschitz assumptions, and their complexity
  with the ARqp-SC unit-radii exponents for `q = 2` on `ℝⁿ` (the "otherwise" exponents are
  proved for every `q`; for `q = 1` only with the additive Phase-1 constants of footnote 114).
* The heuristic procedure of §9.3.7, the stopping advice built on the tests (9.4.3)–(9.4.4), and
  the Gertz–Gill criterion (9.4.8) quoted in §9.4.
* Discussion without numbered results: the variants of §2.2.3, §4.1.3, §7.2.3, the qualitative parts
  of §§5.3.1, 12.1.6, 12.3, the `O(·)` restatements and Table 12.2.1, and the weak approximate
  minimizers (12.1.40) of the Notes.
-/
