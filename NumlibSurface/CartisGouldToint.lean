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
book's named assumptions are `AssumptionXY` (f.gL is `AssumptionGL`, f.DpL is `AssumptionDpL`);
the smoothness assumptions on the derivatives are, where they fit, the library's anchored
assumption `LipschitzDerivsAnchored` on the whole space together with the bound on the constants.
The book's constants are definitions named for their symbols (`kappaSDBA`, `sigmaMaxAR2`).
Module `ChapterNN.SectionMM` is §N.M (namespace `CartisGouldToint.ChapterNN`),
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

Each correction is of one of four kinds:

* **false**: the printed statement is false; the counterexample is a declaration, or is
  described when it is immediate;
* **gap**: the printed proof does not give the statement; it is proved under an extra hypothesis,
  with a weaker bound or a corrected constant, or left open where stated;
* **typo**: a misprint, notation slip or garbled constant whose intended meaning is clear;
* **reading**: an unspecified or ambiguous point settled by a choice (including hypotheses that
  the proofs do not need and that are dropped).

Each chapter index lists all of its items in this form, one per bullet, and the section modules
give the details. The false statements and proof gaps, all of them, are:

* Theorem 1.1.2, converse: **false** (`Chapter01.theorem_1_1_2_iv_counterexample`); proved with
  the curvature condition on the tangent cone (`Chapter01.theorem_1_1_2_iv`).
* Theorem 2.2.2, (2.2.8): **false**, the bound vanishes for small `t_ini`; corrected bound with
  `Chapter02.kappaSDBA` (`Chapter02.theorem_2_2_2`).
* (2.2.7): **false** when `t_ini < t_low/2`; `min(t_ini, t_low/2)` (`Chapter02.lemma_2_2_1_index`).
* Theorem 2.2.5: **gap**, the book's corridor function gives only a first local line minimizer
  (`Chapter02.theorem_2_2_5`, `AppendixB.lemma_B_2_6`).
* Theorem 2.3.8: **false** example, `B_k = 2t⁻¹` violates (2.3.4); `B_k = t⁻¹ I`
  (`Chapter02.theorem_2_3_8`).
* Theorem 3.2.2 (and Theorem 3.1.1): **false** claim `‖∇f(x_{k_ε})‖ > ε₁` for the data (3.1.4);
  the example prescribes `∇f(x_{k_ε}) = 0` (`Chapter03.theorem_3_2_2`, `Chapter03.theorem_3_1_1`).
* (3.3.30): **false** with `+ 1`; proved with `+ 2` (`Chapter03.theorem_3_3_9`).
* Theorems 3.4.6, 3.4.12: **gap** in the counting; a factor `2` on the leading terms
  (`Chapter03.theorem_3_4_6`, `Chapter03.theorem_3_4_12`).
* Theorems 3.4.11, 3.4.12: **gap**, constants `κ^A = κ^S (M + 1)`, `κ^B = M + 2`, `κ^D = 2M + 3`
  (`Chapter03.theorem_3_4_11`, `Chapter03.theorem_3_4_12`).
* Corollary 3.5.5: **gap**, for iRN the data (3.5.12) must be rescaled
  (`Chapter03.irn_slow_example`, `Chapter03.corollary_3_5_5_iii`).
* (4.1.8)–(4.1.9) and Algorithm 5.1.1, `𝓜_k ≠ ∅`: **gap**, runs can get stuck; read vacuously
  (`Chapter04.algorithm_4_1_1`, `Chapter05.ARpLEStop`).
* Algorithm 4.1.1 with `ε₃ < ∞`: **false** that admissible steps exist
  (`Chapter04.not_exists_algorithm_4_1_1_third_order`); Theorem 4.1.5 (iii) is about runs.
* Theorem 4.1.6 (iii): **gap**, sign of `λ_min`; proved for `σ₀ ≤ (p-2)! min(θ₂, θ₃)`
  (`Chapter04.theorem_4_1_6_iii`).
* Theorem 4.2.6: **gap**, only `#_ε ≥ k̄` (not `2k̄`) follows (`Chapter04.theorem_4_2_6_i`).
* Lemma 5.4.2, (5.4.8): **false**; proved with `κ_s = 2(1 + θ₁)/λ_*` (`Chapter05.lemma_5_4_2`).
* Lemma 5.4.3, Theorem 5.4.4: **false** count, one too small; `⌈log₂ log₂(ζ_*/ε)⌉₊`
  (`Chapter05.lemma_5_4_3`, `Chapter05.theorem_5_4_4`).
* §6.1, "C.CNe ensures that (6.1.1) has a solution": **false**
  (`Chapter06.not_assumptionCNe_imp_exists_minimizer`).
* Algorithm 6.2.1, Step 2 for `q ≥ 2`: **false** that it is feasible
  (`Chapter06.algorithm_6_2_1_not_exists_step`); Theorem 6.2.3 is about runs.
* Lemma 6.2.1, (6.2.18)–(6.2.19): **gap**, need `‖d‖ ≤ 1` (`Chapter06.lemma_6_2_1_iii`).
* Algorithm 7.2.1, Phase 2: **gap**, ARp1-CC, not ARp-CC (`Chapter07.IsTPpGCPhase2`).
* Algorithm 7.2.1, Step 2(a): **false** with `<`, Lemma 7.2.1 fails; the test is `≤ θε₀`
  (`Chapter07.lemma_7_2_1`).
* Lemma 7.2.6, Theorem 7.2.7: **gap**, the "bad" outer iterations are not bounded by the book's
  argument; their number is a parameter of `Chapter07.theorem_7_2_7`, and under bounded gradients
  `Chapter07.theorem_7_2_7_of_gradient_le` bounds them by `N_b = O(ε₀⁻¹ε₁⁻¹)`, within the order
  of (7.2.50) (for `ε₀ = ε₁`) iff `p ≤ 2`.
* Lemma 8.2.3, Theorem 8.2.5: **false** strictness for `g = 0` and some `β = -1/2` cases
  (`Chapter08.lemma_8_2_3_strict`, `Chapter08.theorem_8_2_5_strict`).
* Corollary 8.2.4: **gap**, needs `g ≠ 0`; right limits (`Chapter08.corollary_8_2_4`).
* §8.3, `𝓝`, `𝓛`, `𝓖`: **false** set-builder forms when `λ₁ > 0`; interval forms
  (`Chapter08.setL_tr_union_setG_tr`).
* Corollaries 8.3.1–8.3.2: **gap** for multiple `λ₁` (`Chapter08.corollary_8_3_1`); the boundary
  form of Corollary 8.3.2 is **false** for `λ* = 0` (`Chapter08.corollary_8_3_2`).
* Algorithm 9.2.1: **gap**, contraction factor and finite termination
  (`Chapter09.algorithm_9_2_1_terminates`).
* Theorem 9.3.1: **gap**, the hypothesis `z₀ ∈ 𝒵₁` (in the `M`-inner product) is missing
  (`Chapter09.theorem_9_3_1`).
* Theorem 9.3.2: **false** with the Euclidean `λ_min` when `M ≠ I`; `M`-scaled
  (`Chapter09.theorem_9_3_2`).
* (9.3.6), middle term: **false**; the outer inequality (`Chapter09.exists_abs_sub_le_of_eigen`).
  (9.4.5) as an equivalence: **false**; the implication holds.
* Corollaries 10.2.3, 10.3.3: **false** bounds for negative logarithms and `κ* = 1`; `⌈·⌉₊`
  (`Chapter10.corollary_10_2_3`, `Chapter10.corollary_10_3_3`).
* Theorem 12.1.5: **false** (`Chapter12.theorem_12_1_5_counterexample`); proved under a growth
  hypothesis (`Chapter12.theorem_12_1_5`).
* Example 12.1.3 (iv): **false** in `n` variables; holds in one (`Chapter12.example_12_1_3`).
* Theorem 12.1.6 (ii): **gap**, needs `C²` (`Chapter12.theorem_12_1_6_ii`).
* Theorem 12.2.6: **false** slow data of Appendix B; corrected
  (`Optimization.exists_slowTRq_interpolant`, `Chapter12.theorem_12_2_6`).
* Lemmas 12.2.11–12.2.13: **gap**; `θ < ς` and the constant `κ̂` (`Chapter12.lemma_12_2_11`,
  `Chapter12.lemma_12_2_12`, `Chapter12.lemma_12_2_13`).
* Theorem 12.2.15, `q ≥ 3`: **false** hypothesis for its own example
  (`Chapter12.theorem_12_2_15_counterexample`); stated for the global-step scenario
  (`Chapter12.theorem_12_2_15`), an ARqp run for `q ≤ 2` (`Chapter12.corollary_12_2_16`).
* Lemmas 13.1.1, 13.1.9: **false** for `k = 0`; the hypothesis is at `Δ_{k+1}` (`σ_{k+1}`)
  (`Chapter13.lemma_13_1_1`, `Chapter13.lemma_13_1_9`).
* Algorithm 13.1.2, Step 2: **gap**, (13.1.46) must be checked for `i ∈ [1, p]` and long steps
  (`Optimization.ARqpDAStep`, `Chapter13.lemma_13_1_14`).
* Lemma 13.1.17: **gap**, corrected constant `κ̂` (`Chapter13.lemma_13_1_17`).
* Theorems 13.1.19, 13.3.8: **gap**, the proof certifies some radii in `(0, 1]^q`, not radius one;
  stated so (`Chapter13.theorem_13_1_19_i`, `Chapter13.theorem_13_3_8_i`), radius one for `q ≤ 2`.
* Lemma 13.3.7, Theorem 13.3.8 (ARqpEDA): **gap**, the reused Lemma 13.1.16 does not apply;
  proved with `θ < ς/2` (`Chapter13.lemma_13_3_7`, `Chapter13.theorem_13_3_8_ii`).
* Derivative-evaluation counts of Lemma 7.2.2, Theorems 5.5.7, 13.1.8, 13.1.19, 13.3.4, 13.3.8:
  **false** by small additive constants (the initial evaluation, the last accuracy-improving
  iteration); recounted in each theorem.
* (14.1.2): **gap**, a factor `√m` with componentwise c.D1pL (`Chapter14.lemma_14_1_1`).
* Lemma 14.1.3: **gap**, the radius bound is also needed for `j = 1` (`Chapter14.lemma_14_1_3`).
* Lemmas 14.1.7–14.1.9, Theorem 14.1.10: **gap**, `(1 - θ)` must be `(ς - θ)` with `θ < ς`
  (`Chapter14.lemma_14_1_7`, `Chapter14.theorem_14_1_10_i`).
* Theorem 14.2.4, sharpness: **gap**, the book's reduction to `X = ℝⁿ` does not reach `q = 2`,
  `X ≠ ℝⁿ` (`Chapter14.theorem_14_2_4_sharp_arqp_otherwise`).
* Theorem 14.3.1: **false** with arcs feasible only for `X` (`c(x) = x₁² + x₂²`, `f(x) = -x₁`,
  `x⋆ = 0`); arcs in `X ∩ {c = 0}` (`Chapter14.theorem_14_3_1`).
* Example 14.3.1: **false** saddle; the origin is a minimizer (`Chapter14.example_14_3_1`).
* Theorem 14.3.4, Lemma 14.3.7, Theorem 14.3.9: **gap**, `∑_k max_j ≤ max_j ∑_k` is false; proved
  with `∑_j` for `max_j` (`Chapter14.theorem_14_3_4`, `Chapter14.lemma_14_3_7`).
* (14.3.20)–(14.3.21), the multiplicative INNER cost contract: **false** for INNER = ARqp-SC with
  `q = 1`, `p ≥ 2`, and for any INNER spending at least one evaluation per call when every
  `π_j < 2` (`Chapter14.exists_algorithm_14_3_1_cost_contract_counterexample`); it holds for
  ARqp-SC with the ARqpC-SC exponents `j + 1` (`Chapter14.IsARqpSCOutputCost.cost_le_anchored`)
  and, for LENq-SC calls, with the ARqp-SC exponents `j(p+1)/p` when `q ≥ 2`
  (`Chapter14.IsARqpSCOutputCost.cost_le_arqp_lenq`,
  `Chapter14.IsARqpSCOutputCost.cost_le_arqp_anchored`); the additive form with the constants of
  Theorem 14.2.4 holds in all cases and is used (`Chapter14.theorem_14_3_4_add`).
* Lemma 14.3.5, (14.3.43) and (14.3.46): **false** (`Chapter14.lemma_14_3_5_counterexample`);
  corrected with terms `(‖∇f‖δ)²/(f(x_ε) - t_ε)` (`Chapter14.lemma_14_3_5`).
* Lemma 14.3.8: **gap**, its decreases do not bound the bad outer iterations
  (`Chapter14.lemma_14_3_8_proof_gap_counterexample`).
* Theorem 14.3.9, by INNER class:
  * nonspecific INNER: **false** under the per-call reading of the INNER hypotheses
    (`Chapter14.theorem_14_3_9_false`), vacuous for `π₁ < 2` under the uniform reading
    (`Chapter14.theorem_14_3_9_cost_hypothesis_unsatisfiable`); **gap**, proved for INNER
    satisfying Lemma 14.2.2 as stated with radii bounded below, with an extra term
    `O(ε₀^{-1} + max_j (ε₀ ε_j ρ_j^{j-1})^{-1})` (`Chapter14.theorem_14_3_9`);
  * ARqp-SC: the printed order for the exponents `j + 1` and, with `j(p+1)/p`, for `q = p`
    (`Chapter14.theorem_14_3_9_arqpc`, `Chapter14.theorem_14_3_9_arqp`); **false** for `q = 1`,
    `p ≥ 4` and `q = 2`, `p ≥ 5` for runs re-initialising `μ` at Step 2.1 of Algorithm 14.1.2
    (`Chapter14.theorem_14_3_9_arqp_printed_false`); open for `μ` bounded below;
  * TRq-SC: proved with the exponents `π_j = q + 1` and a factor `1 + |log(ε₀ ε_min)|` on the
    function evaluations only (`Chapter14.theorem_14_3_9_trq`), which is needed for `q = 1`
    (`Chapter14.theorem_14_3_9_trq_log_necessary`); the printed order is **false** for every
    `q ≥ 2` on fixed problems, even with the logarithmic factor
    (`Chapter14.theorem_14_3_9_trq_printed_false`,
    `Chapter14.theorem_14_3_9_trq_printed_false_phase2`), and so is the TRq-SC row `j + 1` of
    (14.2.12) per iteration for `q = 2` (`Chapter14.lemma_14_2_2_trq_printed_false_uniform`).
* Theorem A.8.5: **false** for `L < 0` on `ℝ⁰` (`AppendixA.theorem_A_8_5`). Theorem A.8.2:
  **gap**, needs `h ≠ 0` (`AppendixA.theorem_A_8_2`).
* Lemma B.2.1: **gap**, the bound needs `|f₀|, |g₀|, |H₀| ≤ κ_f` (`AppendixB.lemma_B_2_1_bound`).
* Lemma B.4.1, (B.4.3): **false** for `β < 1` (`AppendixB.lemma_B_4_1_iii_false`); true for
  `β = 1`, the case the book uses (`AppendixB.lemma_B_4_1_iii`).
* Lemma B.8.1: **gap**, needs `θ'(λ*) ≠ 0` (`AppendixB.lemma_B_8_1`).

## Not formalized

* The heuristic procedure of §9.3.7, the stopping advice built on the tests (9.4.3)–(9.4.4), and
  the Gertz–Gill criterion (9.4.8) quoted in §9.4.
* Discussion without numbered results: the variants of §2.2.3, §4.1.3, §7.2.3, the qualitative parts
  of §§5.3.1, 12.1.6, 12.3, the `O(·)` restatements and Table 12.2.1, and the weak approximate
  minimizers (12.1.40) of the Notes.
-/
