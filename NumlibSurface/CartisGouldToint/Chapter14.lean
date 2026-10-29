import NumlibSurface.CartisGouldToint.Chapter14.Section01
import NumlibSurface.CartisGouldToint.Chapter14.Section02
import NumlibSurface.CartisGouldToint.Chapter14.Section02Sharp
import NumlibSurface.CartisGouldToint.Chapter14.Section03

/-!
# Cartis–Gould–Toint, Chapter 14: Composite and Constrained Problems

Surface of [cartis2022evaluation] Chapter 14, the last chapter of Part II: high-order
approximate minimizers and their evaluation complexity for composite problems
`min f(x) + h(c(x))` with a nonsmooth `h` (the regularization method ARqpC), for problems with
simple (inexpensive) constraints `x ∈ X` (the `-SC` variants of the methods of Chapter 12 and
§14.1), and for problems with nonconvex equality constraints `c(x) = 0`, `x ∈ X` (curve-based
necessary conditions, the least-norm method LENq-SC and the two-phase method TPqp-GC). This
module imports the section modules and adds nothing of its own.

* §14.1, `Chapter14.Section01`: the composite problem (14.1.1), assumptions c.D1pL, h.L, h.S0,
  w.Bb (`AssumptionCD1pL`, `AssumptionHLip`, `AssumptionHS0`, `AssumptionWBb`), ARqpC
  (Algorithms 14.1.1–14.1.2, `algorithm_14_1_1`, `algorithm_14_1_2`); Lemma 14.1.1, Example
  14.1.1, Lemmas 14.1.2–14.1.9, Theorem 14.1.10 (`theorem_14_1_10_i`, `theorem_14_1_10_ii`);
  existence of runs (`exists_isARqpCRun`) and the radius policy (14.1.28) for every run
  (`algorithm_14_1_1.radius_policy`); Corollary 14.1.11 (`corollary_14_1_11`, with the
  admissibility of the slow steps for `|c|` that the book does not check). The algorithm and its
  analysis are the backbone `Numlib.Optimization.ModelBased.HighOrder.ARqpC` and
  `Numlib.Optimization.ModelBased.HighOrder.ARqpCComplexity` (normed spaces, anchored
  assumptions `LipschitzDerivsAnchored` on `f` and `c`), of which the book items are instances
* §14.2, `Chapter14.Section02`: simple constraints; assumptions X.CNe, f.D1qLaB.X (and
  variants), f.bB.X; Theorem 14.2.1, Lemma 14.2.5 (sparse first-order measure); the ARqpC-SC,
  TRq-SC and ARqp-SC rows of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4 (`lemma_14_2_2_arqpc`,
  `lemma_14_2_2_trq`, `lemma_14_2_2_arqp`, `lemma_14_2_3`, `lemma_14_2_3_trq`,
  `lemma_14_2_3_arqpc`, `theorem_14_2_4_trq`, `theorem_14_2_4_arqp`, `theorem_14_2_4_arqpc`,
  `theorem_14_2_4_arqpc_convex`; the ARqp-SC rows in either radii mode, unit radii or (12.2.51)
  at every order, `Optimization.arqpPiOf`), the TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC rows
  (`lemma_14_2_2_trqida`, …, `theorem_14_2_4_arqpeda`, from the Chapter 13 runs with a feasible
  set; the regularization rows in either radii mode, unit radii or (12.2.51) at every order,
  `Optimization.ARqpDARadiiControl`; on `ℝⁿ` with `q ≤ 2` every ARqpIDA-SC run attains the
  unit-radii bound in either mode, `theorem_14_2_4_arqpida_le_two`); the TRq-SC and ARqp-SC rows
  also under the anchored f.D1qLaB.X / f.D1pLaB.X (`lemma_14_2_2_trq_anchored`, …,
  `theorem_14_2_4_arqp_anchored`, from the anchored Chapter 12 analysis), and the
  dynamic-accuracy rows also under the anchored f.D0qLaB.X / f.D0pLaB.X
  (`lemma_14_2_2_trqida_anchored`, …, `theorem_14_2_4_arqpeda_anchored`, from the anchored
  Chapter 13 analysis; the iterates of all four methods stay in the sublevel set `𝓛_f(x₀)`)
* §14.2, `Chapter14.Section02Sharp`: sharpness of the TRq-SC, ARqp-SC, ARqpC-SC (`q = 1`, convex
  `h`), TRqIDA-SC and TRqEDA-SC orders, of the ARqp-SC order of the lower-bound mode for every `q`
  on a closed nonconvex `X ⊂ ℝ` (the "otherwise" entries for `q ≤ 2`), of the ARqpIDA-SC and
  ARqpEDA-SC orders of the unit-radii mode (`q ≤ 2`), of the ARqpEDA-SC order of the lower-bound
  mode (every `q`) and of the ARqpIDA-SC order of the lower-bound mode for `q = p ≥ 3` and, on a
  closed nonconvex `X ⊂ ℝ²`, for every `q` (`theorem_14_2_4_sharp`,
  `theorem_14_2_4_sharp_arqp`, `theorem_14_2_4_sharp_arqp_otherwise`,
  `theorem_14_2_4_sharp_trqida`, `theorem_14_2_4_sharp_trqeda`,
  `theorem_14_2_4_sharp_arqpida`, `theorem_14_2_4_sharp_arqpeda`,
  `theorem_14_2_4_sharp_arqpeda_otherwise`, `theorem_14_2_4_sharp_arqpida_otherwise`,
  `theorem_14_2_4_sharp_arqpida_otherwise_constrained`)
* §14.3, `Chapter14.Section03`: the problem (14.3.1), X.CQ (`AssumptionXCQ`), Theorems
  14.3.1–14.3.2, Example 14.3.1; LENq-SC (`algorithm_14_3_1`), Theorems 14.3.3–14.3.4; TPqp-GC
  (`algorithm_14_3_2`), Lemmas 14.3.5–14.3.8 and Theorem 14.3.9 for an abstract INNER satisfying
  the contract of Lemma 14.2.2 (`theorem_14_3_9`); existence of runs and Theorem 14.3.9 for runs
  whose INNER calls are runs of ARqp-SC (`theorem_14_3_9_arqpc`, `theorem_14_3_9_arqp`), of ARqp
  with unit radii on `ℝⁿ` (`theorem_14_3_9_arqp_unit`) and of TRq-SC (`theorem_14_3_9_trq`); and
  the counterexamples to the printed statements listed below. Phase 2 of TPqp-GC and its INNER
  contracts are the backbone `Constrained.IsHighOrderTargetRun` and
  `Constrained.HighOrderTargetSeq.IsMeritContract`.

The composite Taylor model `T_{f,j}(x, s) + h(T_{c,j}(x, s))` and its measure `φ^δ_{w,j}` (14.1.6)
are the backbone `Optimization.compositeTaylorDecrement` and
`Optimization.compositeTaylorMeasure`; ARqpC is the backbone ARqp run `Optimization.IsARqpRun`
with composite model data `Optimization.ARqpData.ofComposite`, carrying a closed feasible set
`X` (`X = univ` is ARqpC, a general `X` is ARqpC-SC). The constrained measure (14.2.2) is
`Optimization.taylorMeasure (ftaylorSeries ℝ f x) j δ {d | x + d ∈ X}`; "simple constraints" is
an oracle-cost convention without a declaration of its own (the evaluation counts never charge
the subproblems). In §14.3 the Lagrangian is `Constrained.lagrangianFn f c y`
(`ℒ = f - ⟨y, c⟩`), the Phase-2 residual and merit are `Constrained.targetResidual`,
`Constrained.targetMerit`; Phase 1 of TPqp-GC is LENq-SC on `c`, and the INNER calls of both
algorithms are described by cost and decrease contracts (`innerEvalBound`,
`IsInnerPhaseRunStrong`).
Appendix B's Chapter 14 part contains only proofs, so there is no `AppendixB.Chapter14`.

## Deviations from the book

* Lemma 14.1.1 needs only a local minimizer and differentiability at `x⋆`. c.D1pL is stated
  componentwise as printed, so (14.1.2) carries a factor `√m` that the book drops.
* Lemma 14.1.3: the radius lower bound `δ_{s,j} ≥ κ_δ(σ) ε_j` is also needed (and holds) for
  `j = 1` when `h` or `X` is nonconvex; the book lists only `j ∈ [2 : q]`.
* **Lemmas 14.1.7–14.1.9, Theorem 14.1.10**: Step 1 only certifies `φ_{w,j} > ς ε_j δ^j/j!` at a
  non-terminal iterate, so the factor `(1 - θ)` must be `(ς - θ)`, with `θ < ς`. The
  `‖s_k‖^{p+1}` term of (14.1.30) carries a factor `2`; the second case of (14.1.31) misses
  `ε_j^{(j+1)/(p+1)}`; Lemma 14.1.9 reads `L_{f,p}`, `f` for `L_{w,p}`, `w` and holds at
  successful iterations not followed by termination; `3j!` in the constants of Theorem 14.1.10
  reads `3q!`. The radius policies the book assumes for Theorem 14.1.10 are proved for every
  run; part 1 needs `δ_{0,1} = 1`.
* Theorem 14.2.1: the Lipschitz condition is on the closed ball of radius `δ_j`, and the printed
  `δ^j` of (14.2.6) is `δ_j^j`. (14.2.18)–(14.2.19) print `max ℓ(d)` for the minimum.
* Theorem 14.2.4: the IDA/EDA regularization rows are stated by radii mode; on `ℝⁿ` with `q ≤ 2`
  every ARqpIDA run attains the unit-radii bound in either mode (`theorem_14_2_4_arqpida_le_two`,
  strengthening Theorem 13.1.19 (1)), so the mode-`False` bound is not sharp there for
  `q = 2 < p`. The book's sharpness argument (reduction to `X = ℝⁿ`) does not reach the
  "otherwise" entries with `q ≤ 2` (`q = 2`, `X ≠ ℝⁿ`).
* **Theorem 14.3.1** is false as printed (arcs feasible only for `X`; `X = ℝ²`,
  `c(x) = x₁² + x₂²`, `f(x) = -x₁`, `x⋆ = 0`); the arcs must stay in `X ∩ {c = 0}`. Example 14.3.1's
  origin is a minimizer, with multiplier `y₀ = (-1, 0)`.
* Theorem 14.3.2: the neighbourhood is the closed ball of radius `δ_j`; Theorem 14.3.3 needs a
  ceiling.
* **Theorem 14.3.4**, Lemma 14.3.7, Theorem 14.3.9: `∑_k max_j ≤ max_j ∑_k` is false; the bounds
  hold with `∑_j` for `max_j`.
* **(14.3.20)–(14.3.21)**: the multiplicative cost contract fails for INNER = ARqp-SC with
  `q = 1`, `p ≥ 2`, and for any INNER spending at least one evaluation per call when every
  `π_j < 2` (`exists_algorithm_14_3_1_cost_contract_counterexample`); it holds for ARqp-SC with the
  exponents `j + 1` and, with the ARqp-SC exponents, for `q ≥ 2`
  (`IsARqpSCOutputCost.cost_le_arqp_anchored`); the additive form is used.
* **Lemma 14.3.5**: (14.3.43) and (14.3.46) are false (`lemma_14_3_5_counterexample`) and are
  corrected with terms `(‖∇f‖δ)²/(f(x_ε) - t_ε)`. Lemma 14.3.6: (14.3.63) bounds `∇^j μ`.
* **Lemma 14.3.8**: the decreases used by its proof do not bound the bad outer iterations
  (`lemma_14_3_8_proof_gap_counterexample`).
* **Theorem 14.3.9** is proved for INNER satisfying Lemma 14.2.2 as stated (decrease unless
  INNER's own test holds), with an extra term `O(ε₀^{-1} + max_j (ε₀ ε_j ρ_j^{j-1})^{-1})`
  (`theorem_14_3_9`). As printed it fails for a nonspecific INNER under the per-call reading of
  its hypotheses and is vacuous for `π₁ < 2` under the uniform reading
  (`theorem_14_3_9_false`, `theorem_14_3_9_cost_hypothesis_unsatisfiable`). For runs of ARqp-SC
  that re-initialise `μ` at Step 2.1 of Algorithm 14.1.2 the printed order fails for `q = 1`,
  `p ≥ 4` and `q = 2`, `p ≥ 5` (`theorem_14_3_9_arqp_printed_false`); for runs of TRq-SC it fails
  for every `q ≥ 2` (`theorem_14_3_9_trq_printed_false`), the proved order needs a factor
  `1 + |log(ε₀ ε_min)|` for `q = 1` (`theorem_14_3_9_trq_log_necessary`), and the TRq-SC row of
  (14.2.12) fails per iteration for `q = 2` (`lemma_14_2_2_trq_printed_false_uniform`).
* Algorithm 14.3.2: the INNER calls of Phase 2 are described by their iterates; with INNER =
  ARqp-SC the radii returned at a Step-2 termination certify (14.3.19), which the book's
  `δ_{s_k}` need not (`IsARqpSCCallOut`).

## Not formalized

* The `O(·)` restatements of Theorems 14.3.4 and 14.3.9 (the bounds are stated with constants
  chosen before `ε`).
* Theorem 14.3.9 with INNER = ARqp-SC in the printed order for `q = 1 < p ≤ 3`, `q = 2 < p ≤ 4`,
  `3 ≤ q < p`, for runs whose `μ` at Step 2.1 is bounded below, and with unit radii for `q < p`;
  with INNER = TRq-SC, whether the logarithmic factor is needed for `q ≥ 2`; TRqIDA-SC and
  TRqEDA-SC as INNER.
-/
