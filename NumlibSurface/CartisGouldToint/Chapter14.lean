import NumlibSurface.CartisGouldToint.Chapter14.Section01
import NumlibSurface.CartisGouldToint.Chapter14.Section02
import NumlibSurface.CartisGouldToint.Chapter14.Section02Sharp
import NumlibSurface.CartisGouldToint.Chapter14.Section03
import NumlibSurface.CartisGouldToint.Chapter14.Section03BadIter
import NumlibSurface.CartisGouldToint.Chapter14.Section03Anchored

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
  admissibility of the slow steps for `|c|` that the book does not check)
* §14.2, `Chapter14.Section02`: simple constraints; assumptions X.CNe, f.D1qLaB.X (and
  variants), f.bB.X; Theorem 14.2.1, Lemma 14.2.5 (sparse first-order measure); the ARqpC-SC,
  TRq-SC and ARqp-SC rows of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4 (`lemma_14_2_2_arqpc`,
  `lemma_14_2_2_trq`, `lemma_14_2_2_arqp`, `lemma_14_2_3`, `lemma_14_2_3_trq`,
  `lemma_14_2_3_arqpc`, `theorem_14_2_4_trq`, `theorem_14_2_4_arqp`, `theorem_14_2_4_arqpc`,
  `theorem_14_2_4_arqpc_convex`; the ARqp-SC rows in either radii mode, unit radii or (12.2.51)
  at every order, `Chapter12.arqpPiOf`), the TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC rows
  (`lemma_14_2_2_trqida`, …, `theorem_14_2_4_arqpeda`, from the Chapter 13 runs with a feasible
  set; the regularization rows in either radii mode, unit radii or (12.2.51) at every order,
  `Chapter13.RadiiControlOf`; on `ℝⁿ` with `q ≤ 2` every ARqpIDA-SC run attains the unit-radii
  bound in either mode, `theorem_14_2_4_arqpida_le_two`); the TRq-SC and ARqp-SC rows also under
  the anchored f.D1qLaB.X / f.D1pLaB.X (`lemma_14_2_2_trq_anchored`, …,
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
* §14.3, `Chapter14.Section03`: the problem (14.3.1), assumption X.CQ (`AssumptionXCQ`);
  Theorems 14.3.1–14.3.2, Example 14.3.1; LENq-SC (Algorithm 14.3.1, `algorithm_14_3_1`),
  Theorems 14.3.3–14.3.4; TPqp-GC (Algorithm 14.3.2, `algorithm_14_3_2`), Lemmas 14.3.5–14.3.8
  (`lemma_14_3_6_i`, `lemma_14_3_6_ii`), Theorem 14.3.9; existence of LENq-SC and TPqp-GC runs
  (`exists_algorithm_14_3_1`, `exists_algorithm_14_3_2`) with INNER = ARqp-SC, which satisfy the
  INNER contracts (`IsARqpSCOutputCost.cost_le`, `exists_isTPqpGCPhase2_isInnerPhaseRun`) and
  hence Theorems 14.3.4 and 14.3.9 (`exists_algorithm_14_3_1_complexity`,
  `exists_algorithm_14_3_2_complexity` with the ARqpC-SC exponents `j + 1`;
  `exists_algorithm_14_3_1_complexity_arqp`, `exists_algorithm_14_3_2_complexity_arqp` with the
  ARqp-SC exponents `j(p+1)/p` for `q ≥ 2`; `exists_algorithm_14_3_1_complexity_arqp_add`,
  `exists_algorithm_14_3_2_complexity_arqp_add` for every `q`, with the additive constants of
  Theorem 14.2.4 kept in Phase 1); the bad outer iterations of TPqp-GC are bounded under
  INNER's certificate
  (`IsTPqpGCPhase2.kbCount_le`, `IsTPqpGCPhase2.complexity_of_certified`), which the constructed
  runs carry, so that for `β < θ` Theorem 14.3.9 holds for them without the bad-iteration
  parameter (`exists_algorithm_14_3_2_complexity_certified`), and for every `β ≤ θ` under the
  certificate (`IsTPqpGCPhase2.kbCount_le_of_le`, `IsTPqpGCPhase2.complexity_of_certified_le`);
  with the INNER contract keyed on INNER's own test (14.3.19), as Lemma 14.2.2 states it, for
  every run (`IsInnerPhaseRunStrong`, `IsTPqpGCPhase2.complexity_of_strong`,
  `exists_algorithm_14_3_2_complexity_strong`), while the decreases used by the book's proof of
  Lemma 14.3.8 do not bound them (`lemma_14_3_8_proof_gap_counterexample`); on `X = ℝⁿ` with
  `q ≤ 2`,
  INNER runs of Chapter 12 with unit radii give the unit-radius exponents `(p+1)/(p-j+1)`
  (`exists_algorithm_14_3_1_complexity_unit`, `exists_algorithm_14_3_2_complexity_unit`); the
  multiplicative cost contract (14.3.20)–(14.3.21) is false for `q = 1`
  (`exists_algorithm_14_3_1_cost_contract_counterexample`)
* §14.3, `Chapter14.Section03BadIter`: the order of the bad outer iterations of TPqp-GC is not
  implied by the INNER contract (`theorem_14_3_9_order_counterexample`, `arqpPiOf_one_le`)
* §14.3, `Chapter14.Section03Anchored`: existence and complexity of the LENq-SC and TPqp-GC runs
  with INNER = ARqp-SC under the book's anchored assumptions Φ₂.D1pLaB.X, resp. c.D1pLB.X,
  f.D1pLB.X and f.B.Fb (`exists_algorithm_14_3_1_complexity_anchored`,
  `exists_algorithm_14_3_2_complexity_anchored`), from the anchored ARqpC-SC analysis of §14.1
  (`AnchoredCompositeBounds`, `theorem_14_1_10_ii_anchored`) and Lemma 14.3.6
  (`exists_anchoredCompositeBounds_nu_mu`); the certified, strong-contract, ARqp-SC-exponent and
  unit-radius variants under the book's assumptions
  (`exists_algorithm_14_3_1_complexity_arqp_book`,
  `exists_algorithm_14_3_1_complexity_arqp_add_book`,
  `exists_algorithm_14_3_1_complexity_unit_book`,
  `exists_algorithm_14_3_2_complexity_certified_book`,
  `exists_algorithm_14_3_2_complexity_strong_book`,
  `exists_algorithm_14_3_2_complexity_arqp_book`,
  `exists_algorithm_14_3_2_complexity_arqp_add_book`,
  `exists_algorithm_14_3_2_complexity_unit_book`), from their versions under anchored bounds in
  `Chapter14.Section03` (`exists_algorithm_14_3_2_complexity_certified_anchored`, …)

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
algorithms are described by cost and decrease contracts (`innerEvalBound`, `IsInnerPhaseRun`).
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
* **Theorem 14.3.1 is false as printed**: with arcs that only stay in `X` (and satisfy the
  expansion conditions (14.3.3) of `c`), `X = ℝ²`, `c(x) = x₁² + x₂²`, `f(x) = -x₁` and the only
  feasible point `x⋆ = 0` violate (14.3.4) for `s₁ = e₁`. The arcs must stay in `X ∩ {c = 0}`;
  (14.3.3) then holds automatically, and X.CQ is not needed.
* Example 14.3.1: the multiplier is `y₀ = (-1, 0)` for `ℒ = f - ⟨y, c⟩`, and the origin is a
  (non-strict, global) minimizer — `f` vanishes on the feasible curve `(-t², t, t³)` — not a
  high-order saddle point.
* Theorem 14.3.2: "neighbourhood of diameter `δ_j`" is the closed ball of radius `δ_j`.
  Theorem 14.3.3: the iteration bound needs a ceiling.
* **Theorem 14.3.4** (and Lemma 14.3.7, Theorem 14.3.9): the proof bounds `∑_k max_j a_{k,j}` by
  `max_j ∑_k a_{k,j}`, which is invalid; the bounds hold with `∑_j` in place of `max_j` (the same
  order for fixed `q`).
* **Lemma 14.3.5**: (14.3.43) and (14.3.46) are false as printed — the extra terms are not
  bounded by `φ_{ℒ,1} ‖∇f‖ δ`; for instance `c ≡ 0`, `X = [-1, 1]`, `f(x) = x/4 - 25x²/8`,
  `ε₀ = 1/100` give `φ^1_{ℒ,T,2} = 27/8` against the printed `17/32`, for an actual TPqp-GC run
  (`lemma_14_3_5_counterexample`, which also covers (14.3.46) with `q = 3`). They are replaced by
  `(‖∇f‖δ)²/(2τ)` and `(‖∇f‖δ + ‖∇²f‖δ²)‖∇f‖δ/(2τ)`, `τ = f(x_ε) - t_ε`. Second, when Phase 2
  ends with `f(x_ε) = t_ε`, only `‖c(x_ε)‖ ≥ θε₀` and the first-order part of (14.3.41) follow
  (the measures of `ν` and `μ` differ at orders `j ≥ 2`). (14.3.44) and (14.3.47) hold as printed.
* Lemma 14.3.6: (14.3.63) bounds `∇^j μ`, not `∇^j ν`.
* **Lemma 14.3.8, Theorem 14.3.9**: as in Lemma 7.2.6, the block count of the good inner
  iterations also counts the `i = 0` entries and the last iteration of each INNER call (counted
  separately here, with `κ_unc` paid per call), and the number of *bad* outer iterations, whose
  INNER call guarantees no decrease, is not bounded by the book's argument:
  `theorem_14_3_9` (with the INNER contract `IsInnerPhaseRun` of the proof, which exempts a step
  after which the third test of (14.3.32) holds) carries it as a parameter; that contract does
  not bound it (`lemma_14_3_8_proof_gap_counterexample`, whose INNER calls are not ARqp-SC runs).
  With the exemption keyed on INNER's own test, as in Lemma 14.2.2 (`IsInnerPhaseRunStrong`,
  satisfied by the constructed runs), Phase 2 terminates within an explicit bound without the
  parameter for every `β ≤ θ` (`IsTPqpGCPhase2.complexity_of_strong`; the extra term
  `O(ε₀^{-1} + max_j (ε₀ ε_j ρ_j^{j-1})^{-1})`, `ρ` the INNER radii, is within the book's order
  for the exponents `j + 1` but not in general for the ARqp-SC row). When the number of bad
  iterations is bounded independently of `ε`, the
  counts are `O(max(ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}))`; the derivative count acquires an
  `ε₀^{-1}` term. INNER's certificate for the tolerances `β ‖r(x_k, t_k)‖ ε_j`, with bounded
  derivatives of `f`, bounds it: by `O(max_j (ε₀ ε_j)^{-j})` for the ARqpC-SC runs
  (`IsTPqpGCPhase2.kbCount_le`, `β < θ`; within the order for the exponents `j + 1`), for every
  `β ≤ θ` (`IsTPqpGCPhase2.kbCount_le_of_le`), and by `O(max_j (ε₀ ε_j)^{-1})` for the
  unit-radius runs on `ℝⁿ`. The book's
  `f_up - f_low - 1` is `f_up - f_low + 1`, and its `#F₂` misses the `1/(1 - θ)` of the
  `κ^C ε₀^{-1}` term.
* Algorithm 14.3.2: the INNER calls of Phase 2 are described by their iterates; `μ(·, t_k)` does
  not increase along a call, and a call stops as soon as `‖r‖ < θε₀`.

## Not formalized

* The multiplicative Phase-1 cost contract when all `π_j < 2` (false there; the additive form
  is proved), and the `O(·)` restatements of §14.3.
* The bad outer iterations of TPqp-GC are not bounded in the order of the ARqp-SC exponents by
  the INNER contract: `theorem_14_3_9_order_counterexample` (`Chapter14.Section03BadIter`) gives
  runs satisfying `IsInnerPhaseRunStrong` for all exponents `π` (`q = 1`, `π₁ = (p+1)/p`, `p ≥ 2`)
  with `≍ (ε₀ ε₁)^{-1}` such iterations, more than `C max(ε₀^{-1}, ε₀^{1-π₁} ε₁^{-π₁})` for every
  `C`, so the term of `IsTPqpGCPhase2.complexity_of_strong` is attained in order; whether runs of
  ARqp-SC itself satisfy the book's order is not settled.
-/
