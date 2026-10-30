import Numlib.Optimization.ModelBased.HighOrder.TRqCall
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.AnchoredLipschitz
import Numlib.Optimization.Optimality.TaylorStability
import Numlib.Optimization.Subproblem.SparseLinear
import Numlib.Optimization.Complexity.SlowExample.ARqpDARun
import Numlib.Optimization.Complexity.SlowExample.ARqpDASlitRun
import Numlib.Optimization.Complexity.SlowExample.TRqDARun
import Numlib.Optimization.Complexity.SlowExample.TRqSaddle
import NumlibSurface.CartisGouldToint.Chapter13.Section03
import NumlibSurface.CartisGouldToint.Chapter14.Section01

/-!
# Cartis–Gould–Toint §14.2: Problems with simple constraints

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §14.2: minimization of `f` over a
closed nonempty set `X ⊆ ℝⁿ` (14.2.1) whose "simple" constraints are handled without oracle calls.
The constrained measure (14.2.2) `φ^δ_{f,X(x),j}(x)` is the core
`Optimization.taylorMeasure (ftaylorSeries ℝ f x) j δ {d | x + d ∈ X}`.

"Simple constraints" (the Key Definition after Theorem 14.2.1) is an oracle-cost convention
(solving (14.2.2) and ensuring (14.2.5) costs no evaluation of `f`), not a mathematical property:
in the relational formalization of the algorithms the feasible set enters only through the
measures and the feasibility of the iterates, and the evaluation counts never charge the
subproblems. It therefore has no declaration of its own.

## Main definitions

* `AssumptionXCNe X` — X.CNe;
* `sublevel f X x₀` — the sublevel set `𝓛_f(x₀)` (14.2.8);
* `AssumptionD1qLaBX f X X₀ x₀ j₀ q L B` — f.D1qLaB.X (`j₀ = 1`) and its variant f.D1pLaB.X
  (with `j₀ = 0` it also bounds `|f|` on `𝓛_f(x₀)`);
* `AssumptionD0qLaBX f X X₀ x₀ q L B` — f.D0qLaB.X and f.D0pLaB.X ((14.2.9) for `j ∈ [0:q]`,
  (14.2.10) for `j ∈ [1:q]`);
* `AssumptionBbX f X flow` — f.bB.X.

## Main results

* `theorem_14_2_1` — Theorem 14.2.1 (stability of approximate constrained minimizers);
* `sparseMeasure_eq`, `lemma_14_2_5` — the sparse first-order measure (14.2.17)–(14.2.18) and
  Lemma 14.2.5, on `Fin n → ℝ` with the sup norm (the book's `ℓ∞` ball);
* `lemma_14_2_2_arqpc`, `lemma_14_2_3_arqpc`, `theorem_14_2_4_arqpc`,
  `theorem_14_2_4_arqpc_convex` — the ARqpC-SC rows of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4
  (the §14.1 statements carry a general closed `X`);
* `lemma_14_2_2_trq`, `lemma_14_2_3_trq`, `theorem_14_2_4_trq` — the TRq-SC rows (from
  Chapter 12's TRq with a feasible set; Lemma 14.2.3 through Lemma 12.2.3 with a feasible set);
  `lemma_14_2_2_arqp`, `lemma_14_2_3`, `theorem_14_2_4_arqp` — the ARqp-SC rows (from Chapter 12's
  ARqp with a feasible set), in either radii mode `u` (unit radii, order `(p+1)/(p-j+1)`, or
  (12.2.51) at every order, order `j(p+1)/p`; `Optimization.arqpPiOf u`);
* `lemma_14_2_2_trqida`, `lemma_14_2_3_trqida`, `theorem_14_2_4_trqida` (TRqIDA-SC),
  `lemma_14_2_2_trqeda`, `lemma_14_2_3_trqeda`, `theorem_14_2_4_trqeda` (TRqEDA-SC),
  `lemma_14_2_2_arqpida`, `lemma_14_2_3_arqpida`, `theorem_14_2_4_arqpida` (ARqpIDA-SC),
  `lemma_14_2_2_arqpeda`, `lemma_14_2_3_arqpeda`, `theorem_14_2_4_arqpeda` (ARqpEDA-SC) — the
  dynamic-accuracy rows, from the library's runs with a feasible set
  (`Optimization.IsTRqIDARun`, …, `Optimization.IsARqpEDARun`), the
  regularization rows in either mode of the radii control (`Optimization.ARqpDARadiiControl u`: unit
  radii, order `(p+1)/(p-j+1)`, or (12.2.51) at every order, order `j(p+1)/p`);
  `theorem_14_2_4_arqpida_le_two` — on `X = ℝⁿ` with `q ≤ 2`, every ARqpIDA run satisfies the
  bound of the unit-radii mode whatever its radii mode;
* under the anchored assumptions f.D1qLaB.X (TRq-SC) and f.D1pLaB.X (ARqp-SC), the remark after
  (14.2.10): `lemma_14_2_2_trq_anchored`, `lemma_14_2_3_trq_anchored`,
  `theorem_14_2_4_trq_anchored`,
  `lemma_14_2_2_arqp_anchored`, `lemma_14_2_3_anchored`, `theorem_14_2_4_arqp_anchored` (from the
  anchored Chapter 12 analysis, `AssumptionD1qLaBX.toLipschitzDerivsAnchored`); the ARqpC-SC row
  under anchored bounds is `lemma_14_2_2_arqpc_anchored`, `lemma_14_2_3_arqpc_anchored`,
  `theorem_14_2_4_arqpc_anchored`;
* under the anchored assumptions f.D0qLaB.X (TRqIDA-SC, TRqEDA-SC) and f.D0pLaB.X (ARqpIDA-SC,
  ARqpEDA-SC), the remark of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4:
  `lemma_14_2_2_trqida_anchored`, …, `theorem_14_2_4_arqpeda_anchored` (one `…_anchored` per
  dynamic-accuracy row, from the library's anchored analysis,
  `AssumptionD0qLaBX.lipschitzDerivsAnchored`; the rows under f.D0qL on `C ⊇ X` are the instance
  `A = C`). The anchor is the plain sublevel set `𝓛_f(x₀)`
  for all four methods: the objective does not increase along the runs
  (`Optimization.IsTRqIDARun.objective_le`, …, `Optimization.IsARqpEDARun.objective_le`),
  also for the EDA methods with inexact values, since (13.3.5)/(13.3.13) `κ_s ≤ η₁/4` and
  `h_{k,0} ≤ κ_s \overline{ΔT}_k` give a true decrease of at least `η₁/2 \overline{ΔT}_k > 0` on
  successful iterations;
* bridges: `AssumptionD1qLaBX.of_lipschitzOn`, `AssumptionD1qLaBX.lipschitzDerivsAnchored_self`,
  `assumptionBbX_iff_assumptionWBb`;
* sharpness of the orders of Theorem 14.2.4 ("the orders of complexity mentioned in the last
  column of the table are sharp"), by the book's argument ("unconstrained problems are a special
  case of simply constrained ones") with `X = ℝ` or `X = ℝ¹` (`univ`), and on closed nonconvex
  feasible sets for the "otherwise" entries that this argument does not reach:
  - `theorem_14_2_4_sharp` — the TRq-SC, ARqp-SC (`q ≤ 2`) and ARqpC-SC (`q = 1`, convex `h`)
    orders, from Theorem 12.2.6, Corollary 12.2.16 and Corollary 14.1.11 with `X = ℝ`;
    `theorem_14_2_4_sharp_arqp` — the ARqp-SC order for `q ≥ 3` (Theorem 12.2.17);
  - `theorem_14_2_4_sharp_arqp_otherwise` — the ARqp-SC order `ε^{-q(p+1)/p}` of the lower-bound
    radius mode for every `1 ≤ q ≤ p`, on the closed nonconvex `X = (-∞, R] ∪ [R + 2, ∞) ⊂ ℝ`
    (Theorem 12.2.17 restricted to `X`; the "otherwise" entries for `q = 1`, nonconvex `X`, and
    `q = 2`, `X ≠ ℝⁿ`);
  - `theorem_14_2_4_sharp_trqida`, `theorem_14_2_4_sharp_trqeda` — the TRqIDA-SC and TRqEDA-SC
    orders `ε^{-(q+1)}`, from the example of Theorem 12.2.6 lifted to `ℝ¹` (for TRqEDA with `f`
    halved);
  - `theorem_14_2_4_sharp_arqpida`, `theorem_14_2_4_sharp_arqpeda` — the ARqpIDA-SC and
    ARqpEDA-SC order `ε^{-(p+1)/(p-q+1)}` of the unit-radii mode for `q ≤ 2` (for `q = 1` and for
    `q = p = 2` also the order of the lower-bound mode), from the example of Theorem 12.2.15
    lifted to `ℝ¹`;
  - `theorem_14_2_4_sharp_arqpeda_otherwise` — the ARqpEDA-SC order `ε^{-q(p+1)/p}` of the
    lower-bound mode, for every `q ≤ p`, from the example of Theorem 12.2.17 (`r = p`);
  - `theorem_14_2_4_sharp_arqpida_otherwise` — the ARqpIDA-SC order `ε^{-q(p+1)/p}` of the
    lower-bound mode for `q = p ≥ 3`, from pure `p`-th order spikes (Theorem 12.2.15 with
    `q = p`);
  - `theorem_14_2_4_sharp_arqpida_otherwise_constrained` — the ARqpIDA-SC order `ε^{-q(p+1)/p}`
    of the lower-bound mode for every `1 ≤ q ≤ p` (in particular the "otherwise" entries for
    `q = 1`, nonconvex `X`, and `q = 2`, `X ≠ ℝⁿ`), on the closed feasible set
    `X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1} ⊂ ℝ²` (`v 1` the second coordinate: a line and a parallel
    half-plane at distance `ρ ∈ (ε, 2ε]`), from the example of Theorem 12.2.17 on the line.

  The dynamic-accuracy runs are the backbone slow runs (`Optimization.exists_isTRqIDARun_slow`,
  `Optimization.exists_isTRqEDARun_slow`, `Optimization.exists_isARqpIDARun_slow`,
  `Optimization.exists_isARqpEDARun_slow`, `Optimization.exists_isARqpEDARun_slowGrad`,
  `Optimization.exists_isARqpIDARun_slowTop`, `Optimization.exists_isARqpIDARun_slit`): runs of
  the Chapter 13 run predicates with exact derivatives (and values), with class constants
  independent of `ε`.

## Deviations from the book

* Theorem 14.2.1: the Lipschitz condition is required on the closed ball of radius `δ_j` around
  `x_ε` (implied by the printed open ball of radius larger than `δ_j`); `X` closed and nonempty,
  `δ_j ≤ 1` and `ε_j ≤ 1` are not needed. The printed `δ^j` in (14.2.6) is `δ_j^j`. The radius
  condition `‖d‖ ≤ (j+1)ε_j/L_{f,j}` is used in the equivalent form `L_{f,j} ‖d‖ ≤ (j+1) ε_j`.
* (14.2.18)–(14.2.19) print `max ℓ(d)`; the measure (14.2.17) and Lemma 14.2.5 need the minimum
  of `ℓ(d) = ⟨∇f(x), d⟩`.

* (14.2.12) prints `π_j = j + 1` for TRq-SC, which is stronger than what Lemmas 12.2.4, 13.1.5
  and 13.3.2 give and inconsistent with the order `O(max_j ε_j^{-(q+1)})` of Theorem 14.2.4; the
  TR rows of Lemma 14.2.2 (`lemma_14_2_2_trq`, `lemma_14_2_2_trqida`, `lemma_14_2_2_trqeda`) use
  `π_j = q + 1` (the decrease is a multiple of `ε_min^{q+1}`). The printed row is false per
  iteration for `q = 2` with `κ_decr` depending only on the algorithm parameters and the
  f.D1qLaB.X constants (`lemma_14_2_2_trq_printed_false`,
  `lemma_14_2_2_trq_printed_false_uniform`).
* Lemma 14.2.3 is stated with explicit constants: `κ_unc` contains `|log ε_min|` terms (the
  radius lower bound of the TR methods is proportional to `ε_min`, and the number of
  accuracy-improving iterations of the IDA/EDA methods is logarithmic in `ε_min`); for the IDA
  methods, which have no termination rule, the count holds up to the first approximately optimal
  iterate. The ARqpIDA-SC row of Lemma 14.2.2 holds at successful iterations followed by an
  iterate that is not approximately optimal, and the ARqpEDA-SC row needs `θ < ς/2` and holds at
  the successful iterations of Lemma 13.3.7 (the corrections of Lemmas 13.1.18 and 13.3.7).
* The ARqp-SC rows are stated by radii mode `u` (exponents `Optimization.arqpPiOf u`), while the
  table keys them by `(q, X)`: the mode `u = False` ((12.2.51) at every order) gives the
  "otherwise" entries `j(p+1)/p` for every `q` and `X`, and the unit-radii entries
  `(p+1)/(p-j+1)` hold under the hypothesis that the radii are `1`.
* The IDA/EDA regularization rows are stated by radii mode (`Chapter13.ARqpDARadiiControl u`), while
  the table keys them by `(q, X)`. On `ℝⁿ` with `q ≤ 2` every ARqpIDA run satisfies the
  unit-radii bound of the table in either mode (`theorem_14_2_4_arqpida_le_two`, a strengthening
  of Theorem 13.1.19 (1), which assumes unit radii): a failure of the criterion is a failure at
  unit radii, and for `q ≤ 2` the bound (13.1.57) on the model transfers to unit radii (`φ^δ_j/δ^j`
  is nonincreasing in `δ` for `j ≤ 2`). Hence the mode-`False` bound of `theorem_14_2_4_arqpida`
  is not sharp on `ℝⁿ` for `q = 2 < p` (for ARqpEDA it is,
  `theorem_14_2_4_sharp_arqpeda_otherwise`).
  The book's sharpness argument (reduction to `X = ℝⁿ`) does not reach the "otherwise" entries
  with `q ≤ 2` (`q = 2` with `X ≠ ℝⁿ`, `q = 1` with `X` nonconvex); they are attained on closed
  nonconvex sets (`theorem_14_2_4_sharp_arqp_otherwise`,
  `theorem_14_2_4_sharp_arqpida_otherwise_constrained`).
* Sharpness, TRqIDA-SC and TRqEDA-SC. The slow example of Theorem 12.2.6 becomes a run of these
  methods only for suitable constants:
  - `ϑ = Δ₀ = ε`, forced by `ε_min ≤ ϑ ≤ Δ₀`;
  - initial accuracies passing (13.1.9) along the steps (`h_{0,i} ≤ κ_s ε^{q-i+1}`);
  - for TRqEDA, (13.3.8) at radius `ε`.

  The tests (13.1.14) and (13.3.7) have half the threshold of the TRq test, so TRqEDA is run on
  `f/2` to make it terminate at `k_ε`. TRqIDA has no termination rule and is continued after
  `k_ε` by an arbitrary run from `x_{k_ε}`.
* Sharpness, ARqpIDA-SC and ARqpEDA-SC. The Chapter 12 slow runs are not runs of the Chapter 13
  regularization steps. The Step-1 test (13.1.53) has half the threshold of the ARqp test, and the
  model-decrease condition (13.1.54) can fail at the Step-1 displacements: for the example of
  Theorem 12.2.17 with `p = q = 3`, `ς = 1`, near `k_ε`, `Δm̄ = 5ε⁴/192 < ε⁴/24`. The data are
  therefore adapted as follows.
  - **Unit-radii mode** (`q ≤ 2`, Theorem 12.2.15, `σ₀ = p!/(q-1)!`, unit initial radii). The
    Step-1 radius of order `q` is halved from `1` to a dyadic radius `2^{-m}` at the scale of the
    step, where (13.1.54) holds while it fails at twice that radius. This requires `ε` below some
    `ε₀(p, q)`.
  - **Lower-bound mode of ARqpEDA** (Theorem 12.2.17 with `r = p`, radii `ε`). The weight is
    `σ₀ = (3/(p+2))^p/2` instead of (12.2.85), and the Step-1 displacements achieve exactly the
    fraction `ς` of the measures.
  - **Lower-bound mode of ARqpIDA** (`q = p ≥ 3`, `σ₀ = p`, initial radii `ε`). The Step-2 radii
    are `ε/p`.
  - **Lower-bound mode of ARqpIDA with a feasible set** (`1 ≤ q ≤ p`, `σ₀ = (3/(p+2))^p`, all
    radii `ε`). The criterion `Optimization.arqpIDATest` asks for approximate optimality for
    *some* radii, and on the line alone the gradient spikes `β_k ≈ ε^q/q!` meet it at radius `1`.
    A second coordinate with `∂f/∂(v 1) = -1` and the half-plane `{ρ ≤ v 1}` make every radius
    `δ ≥ ρ` fail, while radii `δ < ρ` (including the algorithm's radii `ε`) only see the line;
    `ρ^{q-1} = ε^{q-1}(1 + 1/k_ε)` (`ρ = ε(1 + 1/k_ε)` for `q = 1`) makes the first hit exactly
    `k_ε`. After `k_ε` the run makes one more step, to a point where the derivatives along the
    line vanish, and continues with accuracy-improving iterations there.
  - **Termination and continuation.** ARqpEDA is run on `f/2` so that it terminates at `k_ε`.
    ARqpIDA is continued after `k_ε` by ARqpIDA iterations from the state at `k_ε`
    (`Optimization.exists_arqpDA_steps`).
  - **Accuracies.** The initial accuracies are assumed to pass (13.1.46) along the steps and, for
    ARqpEDA, (13.3.17) at termination.

## Not formalized here

* Sharpness of the "otherwise" entry of the ARqpIDA-SC row on `X = ℝⁿ` for `3 ≤ q < p`. The
  table's claim for this entry is met with a feasible set `X ≠ ℝⁿ`
  (`theorem_14_2_4_sharp_arqpida_otherwise_constrained`); the book's proof, by reduction to
  `X = ℝⁿ`, would also need this case. The example of Theorem 12.2.17 meets the criterion at
  `x₀` (its measures at radius `1` are `β_0 ≤ ε/j!`), and pure `q`-th order spikes fail it at
  every radius but have the order `ε^{-(p+1)/(p-q+1)}`. Heuristically, failing the criterion at
  radius `1` needs a derivative of some order `3 ≤ i ≤ q` of size `≳ ε` at every iterate, and if
  these derivatives are periodic along the run, Taylor consistency of the jets needs steps
  `t ≳ ε^{1/(p-2)} ≫ ε^{q/p}`. The book's statement of Theorem 12.2.17, "for some `δ_ε`", has the
  same caveat.
* Runs satisfying the radius policy of the ARqp-SC rows under the anchored assumptions exist on
  `X = ℝⁿ` (`Optimization.exists_isARqpRun_of_anchored`); for a general closed `X` they are the
  ARqpC-SC runs with `c = 0`, `h = 0` of `Chapter14.Section03` (`exists_algorithm_14_1_1_of_hLip`,
  `Optimization.IsARqpCRun.isARqpRun_zero`), whose radii satisfy (12.2.51) by
  `algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored`; the `¬ u` radius hypothesis of
  `theorem_14_2_4_arqp_anchored` is not discharged for them in this module.
-/

open Set Metric
open scoped Nat

namespace CartisGouldToint.Chapter14

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### Assumptions -/

/-- **Assumption X.CNe** of [cartis2022evaluation], §14.2: the constraint set `X` is closed and
nonempty. -/
def AssumptionXCNe (X : Set ℝⁿ) : Prop := IsClosed X ∧ X.Nonempty

theorem assumptionXCNe_iff {X : Set ℝⁿ} : AssumptionXCNe X ↔ IsClosed X ∧ X.Nonempty := Iff.rfl

/-- The sublevel set `𝓛_f(x₀) = {x ∈ X | f(x) ≤ f(x₀)}` of [cartis2022evaluation], (14.2.8). -/
def sublevel (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (x₀ : ℝⁿ) : Set ℝⁿ := {x ∈ X | f x ≤ f x₀}

theorem mem_sublevel {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {x₀ x : ℝⁿ} :
    x ∈ sublevel f X x₀ ↔ x ∈ X ∧ f x ≤ f x₀ := Iff.rfl

theorem sublevel_subset {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {x₀ : ℝⁿ} : sublevel f X x₀ ⊆ X :=
  fun _ hx => hx.1

/-- **Assumption f.D1qLaB.X** of [cartis2022evaluation], §14.2.1, and its variants: `f` is `q`
times continuously differentiable on an open convex set `X₀ ⊇ X`, and for every order
`j ∈ [j₀ : q]` there are constants `L j ≥ 1`, `B j ≥ 1` with
`‖∇^j f(x) - ∇^j f(y)‖ ≤ L_j ‖x - y‖` (14.2.9) and `‖∇^j f(x)‖ ≤ B_j` (14.2.10) for every `x` in
the sublevel set `𝓛_f(x₀)` (14.2.8) and `y ∈ X₀`. With `j₀ = 1` this is f.D1qLaB.X (and
f.D1pLaB.X with `p` in place of `q`). With `j₀ = 0` it is f.D0qLaB.X (`AssumptionD0qLaBX`, where
(14.2.9) runs over `[0:q]`) strengthened by `|f| ≤ B_{f,0}` on `𝓛_f(x₀)`
(`AssumptionD1qLaBX.toD0qLaBX`). -/
structure AssumptionD1qLaBX (f : ℝⁿ → ℝ) (X X₀ : Set ℝⁿ) (x₀ : ℝⁿ) (j₀ q : ℕ)
    (L B : ℕ → ℝ) : Prop where
  isOpen : IsOpen X₀
  convex : Convex ℝ X₀
  subset : X ⊆ X₀
  contDiffOn : ContDiffOn ℝ q f X₀
  one_le_lip : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ L j
  one_le_bound : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ B j
  /-- The anchored Lipschitz condition (14.2.9). -/
  lipschitzAnchored : ∀ j ∈ Finset.Icc j₀ q,
    IteratedFDerivLipschitzAnchored f j (L j) (sublevel f X x₀) X₀
  /-- The derivative bound (14.2.10). -/
  norm_le : ∀ j ∈ Finset.Icc j₀ q, ∀ x ∈ sublevel f X x₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j

/-- f.D1qLaB.X gives the backbone smoothness hypothesis `LipschitzDerivsAnchored` on `X₀` with
the orders `[j₀ : q]` and the anchor set `𝓛_f(x₀)` (the bound (14.2.10) is not used). -/
theorem AssumptionD1qLaBX.toLipschitzDerivsAnchored {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ}
    {j₀ q : ℕ} {L B : ℕ → ℝ} (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) :
    LipschitzDerivsAnchored f X₀ (sublevel f X x₀) j₀ q L :=
  ⟨h.isOpen, h.convex, sublevel_subset.trans h.subset,
    fun _ hy => h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy), h.lipschitzAnchored⟩

/-- f.D1qLaB.X is the backbone assumption `LipschitzDerivsAnchored` (orders `[j₀ : q]`, anchor
set `𝓛_f(x₀)`) with `X ⊆ X₀`, normalized constants `L_j, B_j ≥ 1` and the bound (14.2.10). -/
theorem assumptionD1qLaBX_iff {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ} {j₀ q : ℕ}
    {L B : ℕ → ℝ} : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B ↔
      LipschitzDerivsAnchored f X₀ (sublevel f X x₀) j₀ q L ∧ X ⊆ X₀ ∧
        (∀ j ∈ Finset.Icc j₀ q, 1 ≤ L j) ∧ (∀ j ∈ Finset.Icc j₀ q, 1 ≤ B j) ∧
        ∀ j ∈ Finset.Icc j₀ q, ∀ x ∈ sublevel f X x₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j :=
  ⟨fun h => ⟨h.toLipschitzDerivsAnchored, h.subset, h.one_le_lip, h.one_le_bound, h.norm_le⟩,
    fun ⟨h, hX, hL, hB, hn⟩ => ⟨h.isOpen, h.convex, hX,
      fun y hy => (h.contDiffAt y hy).contDiffWithinAt, hL, hB, h.lipschitzAnchored, hn⟩⟩

/-- **Assumption f.bB.X** of [cartis2022evaluation], §14.2.1: `f` is bounded below on `X` by
`flow`. -/
def AssumptionBbX (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (flow : ℝ) : Prop := ∀ x ∈ X, flow ≤ f x

theorem assumptionBbX_iff {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {flow : ℝ} :
    AssumptionBbX f X flow ↔ ∀ x ∈ X, flow ≤ f x := Iff.rfl

theorem AssumptionXCNe.isClosed {X : Set ℝⁿ} (h : AssumptionXCNe X) : IsClosed X := h.1

theorem AssumptionXCNe.nonempty {X : Set ℝⁿ} (h : AssumptionXCNe X) : X.Nonempty := h.2

/-- f.bB.X for the composite objective `w = f + h ∘ c` is w.Bb on `X` (§14.1). -/
theorem assumptionBbX_iff_assumptionWBb {m : ℕ} {f : ℝⁿ → ℝ}
    {c : ℝⁿ → EuclideanSpace ℝ (Fin m)} {h : EuclideanSpace ℝ (Fin m) → ℝ} {X : Set ℝⁿ}
    {wlow : ℝ} : AssumptionBbX (fun x => f x + h (c x)) X wlow ↔ AssumptionWBb f c h X wlow :=
  Iff.rfl

/-- Global Lipschitz continuity and boundedness of the derivatives on `X₀` give the anchored
assumption f.D1qLaB.X (the remark after (14.2.10): (14.2.9) is automatic if the derivatives are
Lipschitz on `X₀`). -/
theorem AssumptionD1qLaBX.of_lipschitzOn {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ} {j₀ q : ℕ}
    {L B : ℕ → ℝ} (hX₀ : IsOpen X₀) (hconv : Convex ℝ X₀) (hX : X ⊆ X₀)
    (hf : ContDiffOn ℝ q f X₀) (hL1 : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ L j)
    (hB1 : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ B j)
    (hlip : ∀ j ∈ Finset.Icc j₀ q, IteratedFDerivLipschitzOn f j (L j) X₀)
    (hbd : ∀ j ∈ Finset.Icc j₀ q, ∀ x ∈ X₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    AssumptionD1qLaBX f X X₀ x₀ j₀ q L B where
  isOpen := hX₀
  convex := hconv
  subset := hX
  contDiffOn := hf
  one_le_lip := hL1
  one_le_bound := hB1
  lipschitzAnchored j hj := (hlip j hj).anchored (sublevel_subset.trans hX)
  norm_le j hj x hx := hbd j hj x (hX hx.1)

/-- The anchored assumption gives Lipschitz derivatives on the open convex set `X₀`
(`LipschitzDerivsAnchored` with all of `X₀` as anchors) when, moreover, the anchor is all of `X₀`
(`X₀ ⊆ 𝓛_f(x₀)`). -/
theorem AssumptionD1qLaBX.lipschitzDerivsAnchored_self {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ}
    {q : ℕ} {L B : ℕ → ℝ} (h : AssumptionD1qLaBX f X X₀ x₀ 1 q L B)
    (hsub : X₀ ⊆ sublevel f X x₀) : LipschitzDerivsAnchored f X₀ X₀ 1 q L :=
  ⟨h.isOpen, h.convex, subset_rfl, fun _ hy => h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy),
    fun j hj x hx y hy => h.lipschitzAnchored j hj x (hsub hx) y hy⟩

/-! ### Theorem 14.2.1 -/

/-- **Theorem 14.2.1** of [cartis2022evaluation] (stability of approximate constrained
minimizers). Let `f` be `C^j` near `x_ε` with `∇^j f` Lipschitz with constant `L ≥ 0` on the
closed ball of radius `δ` around `x_ε`, and let
`φ^δ_{f,X(x_ε),j}(x_ε) ≤ ε δ^j / j! + η`. Then
(14.2.6) `f(x_ε + d) ≥ f(x_ε) - 2 ε δ^j/j! - η` for every `d ∈ X(x_ε)` with `‖d‖ ≤ δ` and
`L ‖d‖ ≤ (j + 1) ε` (the book's `‖d‖ ≤ min(δ, (j+1)ε/L)` when `L > 0`); and
(14.2.7) if `L = 0`, `f(x_ε + d) ≥ f(x_ε) - ε δ^j/j! - η` for every `d ∈ X(x_ε)` with `‖d‖ ≤ δ`. -/
theorem theorem_14_2_1 {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {xε : ℝⁿ} {j : ℕ} {δ ε η L : ℝ}
    (hf : ∀ y ∈ closedBall xε δ, ContDiffAt ℝ j f y)
    (hL : IteratedFDerivLipschitzOn f j L (closedBall xε δ)) (hL0 : 0 ≤ L)
    (hφ : Optimization.taylorMeasure (ftaylorSeries ℝ f xε) j δ {d | xε + d ∈ X} ≤
      ε * δ ^ j / j ! + η) :
    (∀ d, xε + d ∈ X → ‖d‖ ≤ δ → L * ‖d‖ ≤ (j + 1) * ε →
      f xε - 2 * ε * δ ^ j / (j ! : ℝ) - η ≤ f (xε + d)) ∧
    (L = 0 → ∀ d, xε + d ∈ X → ‖d‖ ≤ δ → f xε - ε * δ ^ j / (j ! : ℝ) - η ≤ f (xε + d)) := by
  refine ⟨fun d hd hdδ hLd =>
    Optimization.le_of_taylorMeasure_le_of_mul_le hf hL hL0 hφ hd hdδ hLd, ?_⟩
  rintro rfl d hd hdδ
  exact Optimization.le_of_taylorMeasure_le_of_lipschitz_zero hf hL hφ hd hdδ

/-! ### Sparsity constraints (§14.2.2) -/

section Sparse

open Subproblem

variable {nnz : ℕ} {x : Fin n → ℝ} {δ : ℝ}

/-- **The sparse first-order measure** ([cartis2022evaluation], (14.2.17)–(14.2.18), with the
`ℓ∞` ball of `Fin n → ℝ`): for a sparse `x` (`‖x‖₀ ≤ n_nz`) and `δ ≥ 0`, the linear problem
`min {⟨∇f(x), d⟩ | ‖d‖_∞ ≤ δ, ‖x + d‖₀ ≤ n_nz}` has a solution `d⋆`, and the measure
`φ^δ_{f,X(x),1}(x)` equals `-⟨∇f(x), d⋆⟩` (the book's (14.2.18) prints `max ℓ(d)`; the minimum
is meant). Here `∇f(x)` has the coordinates `g_i = ∇f(x)[e_i]`, and `d⋆` is the step (14.2.20) of
an optimal knapsack selection. -/
theorem sparseMeasure_eq (f : (Fin n → ℝ) → ℝ) (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ) :
    ∃ τ, KnapsackFeasible x δ nnz τ ∧
      sparseLinearStep x (fun i => fderiv ℝ f x (Pi.single i 1)) δ τ ∈
        closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz} ∧
      IsMinOn (fun d => ∑ i, fderiv ℝ f x (Pi.single i 1) * d i)
        (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz})
        (sparseLinearStep x (fun i => fderiv ℝ f x (Pi.single i 1)) δ τ) ∧
      Optimization.taylorMeasure (ftaylorSeries ℝ f x) 1 δ {d | x + d ∈ sparseSet n nnz} =
        -∑ i, fderiv ℝ f x (Pi.single i 1) *
          sparseLinearStep x (fun i => fderiv ℝ f x (Pi.single i 1)) δ τ i := by
  obtain ⟨τ, hτ, hopt, hn, hS, hmin⟩ :=
    exists_isMinOn_sparseLinearStep (g := fun i => fderiv ℝ f x (Pi.single i 1)) hx hδ
  refine ⟨τ, hτ, ⟨mem_closedBall_zero_iff.2 hn, hS⟩, hmin, ?_⟩
  rw [taylorMeasure_ftaylorSeries_sparse_eq f hx hδ, sum_mul_sparseLinearStep,
    knapsackValue_eq_knapsackOpt hτ hopt]
  ring

/-- **Lemma 14.2.5** of [cartis2022evaluation] (optimal sparse solution of (14.2.18), as a
minimization): for `‖x‖₀ ≤ n_nz`, a vector `g`, `δ ≥ 0` and a selection `τ` solving the knapsack
problem (14.2.21), the vector `d⋆` of (14.2.20) (`Subproblem.sparseLinearStep x g δ τ`) is
feasible (`‖d⋆‖_∞ ≤ δ`, `‖x + d⋆‖₀ ≤ n_nz`) and minimizes `d ↦ ⟨g, d⟩` over the feasible
displacements. (The hypothesis `‖x‖₀ ≤ n_nz` is not needed: the knapsack constraint keeps
`x + d⋆` sparse.) -/
theorem lemma_14_2_5 {g : Fin n → ℝ} {τ : Fin n → Bool} (hδ : 0 ≤ δ)
    (hτ : KnapsackFeasible x δ nnz τ)
    (hopt : ∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ) :
    ‖sparseLinearStep x g δ τ‖ ≤ δ ∧ x + sparseLinearStep x g δ τ ∈ sparseSet n nnz ∧
      IsMinOn (fun d => ∑ i, g i * d i) (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz})
        (sparseLinearStep x g δ τ) :=
  isMinOn_sparseLinearStep hδ hτ hopt

end Sparse

/-! ### Complexity of the -SC algorithms (§14.2.1)

The rows of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4 for ARqpC-SC, TRq-SC and ARqp-SC are stated
here under smoothness on all of `ℝⁿ` (f.D1pL and c.D1pL of §14.1 for ARqpC-SC) or on an open
convex `C ⊇ X` (`LipschitzDerivsAnchored f C C 1 p L`, for TRq-SC and ARqp-SC); the TRq-SC and
ARqp-SC rows under the anchored f.D1qLaB.X / f.D1pLaB.X follow in the section on anchored
assumptions; the ARqpC-SC row is also stated under anchored bounds
(`lemma_14_2_2_arqpc_anchored`, …). -/

section ARqpCSC

variable {f : ℝⁿ → ℝ} {m : ℕ} {c : ℝⁿ → EuclideanSpace ℝ (Fin m)}
  {h : EuclideanSpace ℝ (Fin m) → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpC-SC row: for an ARqpC-SC run
(`algorithm_14_1_1` with a closed feasible set `X`) under the (global) assumptions of §14.1 and
`θ < ς`, every successful iteration `k` not followed by termination decreases `w` by at least
`η₁ κ_{Δm} ε_j^{j+1}` for some `j ∈ [1 : q]` (`π_j = j + 1`; the radius policy (14.1.28) holds for
every run). The convex case `q = 1` is the first part of `lemma_14_1_9`. -/
theorem lemma_14_2_2_arqpc (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, P.η₁ * (kappaDm2 P Lf Lc Lh p q m * ε j ^ (j + 1)) ≤
      (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1)))) := by
  have hpol := hr.radius_policy hf hc hL hS (fun i hi => hk i hi.le)
    (fun h' => hk k le_rfl (Or.inl h'))
  rw [← (hr.run.radii k hk).1 hsucc] at hpol
  obtain ⟨j, hj, -, hdec⟩ := (lemma_14_1_9 hr hθς hf hc hL hk hsucc h1).2 hpol
  exact ⟨j, hj, hdec⟩

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpC-SC row (Lemma 2.4.1 with the bound
`σ_max` of Lemma 14.1.6): for every iteration `k` reached (up to and including termination),
`k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns = 1 + |log γ₁|/log γ₂` and
`κ_unc = log(σ_max/σ₀)/log γ₂`. -/
theorem lemma_14_2_3_arqpc (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) {k : ℕ} (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRatio
        (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀) / Real.log P.γ₂ :=
  hr.run.toIsARRun.le_succ_count hk (sigma_le_arqpcSigmaMax hr hf hc hL hk k le_rfl)

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpC-SC row (`h` nonconvex or `q > 1`):
Theorem 14.1.10, part 2, for ARqpC-SC runs with a closed feasible set `X` (measures over
`{d | x + d ∈ X}`, w.Bb on `X`), with moreover `x_{k_ε} ∈ X`. -/
theorem theorem_14_2_4_arqpc (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) {mε : ℝ} (hmε0 : 0 < mε)
    (hmε : ∀ j ∈ Finset.Icc 1 q, mε ≤ ε j ^ (j + 1)) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
        Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x kε))
          (ftaylorSeries ℝ c (x kε)) h {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε)) + 2 := by
  obtain ⟨kε, hhit, h2, h3, h4⟩ := theorem_14_1_10_ii hr hθς hf hc hL hS hw hmε0 hmε
  exact ⟨kε, hhit, hr.mem hhit.2, h2, h3, h4⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpC-SC row for `q = 1` with `h` and `X`
convex: Theorem 14.1.10, part 1, for ARqpC-SC runs, with moreover `x_{k_ε} ∈ X`. -/
theorem theorem_14_2_4_arqpc_convex (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) (hq : q = 1) (hconv : ConvexOn ℝ univ h)
    (hXc : Convex ℝ X) (hδ₀ : δ₀ 1 = 1) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧ x kε ∈ X ∧
      Optimization.compositeTaylorMeasure (ftaylorSeries ℝ f (x kε)) (ftaylorSeries ℝ c (x kε))
        h 1 1 {e | x kε + e ∈ X} ≤ ε 1 ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) /
            (P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p)))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) /
          (P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p))) + 2 := by
  obtain ⟨kε, hhit, h2, h3, h4⟩ :=
    theorem_14_1_10_i hr hθς hf hc hL hw hq hconv hXc hδ₀
  exact ⟨kε, hhit, hr.mem hhit.2, h2, h3, h4⟩

variable {X₀ : Set ℝⁿ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpC-SC row, under the anchored assumptions
(`AnchoredCompositeBounds` on the sublevel set of `w` at `x₀`, the book's f.D1pLaB.X, with an
open convex `X₀ ⊇ X`) and `θ < ς`: every successful iteration `k` not followed by termination
decreases `w` by at least `η₁ κ_{Δm} ε_j^{j+1}` for some `j ∈ [1 : q]`. -/
theorem lemma_14_2_2_arqpc_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς)
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, P.η₁ * (kappaDm2 P Lf Lc Lh p q m * ε j ^ (j + 1)) ≤
      (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1)))) := by
  have hpol := hr.kappaDeltaMin_mul_le_radius_anchored hA hX hL hS (fun i hi => hk i hi.le)
    (fun h' => hk k le_rfl (Or.inl h'))
  rw [← (hr.run.radii k hk).1 hsucc] at hpol
  obtain ⟨j, hj, -, hdec⟩ := (lemma_14_1_9_anchored hr hθς hA hX hL hk hsucc h1).2 (Or.inr hpol)
  exact ⟨j, hj, hdec⟩

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpC-SC row, under the anchored assumptions:
for every iteration `k` reached, `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13). -/
theorem lemma_14_2_3_arqpc_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRatio
        (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀) / Real.log P.γ₂ :=
  hr.run.toIsARRun.le_succ_count hk (sigma_le_arqpcSigmaMax_anchored hr hA hX hL hk k le_rfl)

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpC-SC row, under the anchored assumptions
(`theorem_14_1_10_ii_anchored` for ARqpC-SC runs), with moreover `x_{k_ε} ∈ X`. -/
theorem theorem_14_2_4_arqpc_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς)
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) {mε : ℝ} (hmε0 : 0 < mε)
    (hmε : ∀ j ∈ Finset.Icc 1 q, mε ≤ ε j ^ (j + 1)) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
        Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x kε))
          (ftaylorSeries ℝ c (x kε)) h {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε)) + 2 := by
  obtain ⟨kε, hhit, h2, h3, h4⟩ := theorem_14_1_10_ii_anchored hr hθς hA hX hL hS hw hmε0 hmε
  exact ⟨kε, hhit, hr.mem hhit.2, h2, h3, h4⟩

end ARqpCSC

section TRqSC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {X C : Set E}
  {P : Optimization.TRqParams} {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → E} {Δ : ℕ → ℝ}
  {jk : ℕ → ℕ} {d : ℕ → ℕ → E} {L : ℕ → ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRq-SC row: for a TRq-SC run
(`Chapter12.algorithm_12_2_1_feasible`, feasible set `X ⊆ C`, `x₀ ∈ X`) under f.D1qL on an open
convex `C` (`LipschitzDerivsAnchored f C C 1 q L`; the normalization `L_j ≥ 1` is not needed),
every iteration `k` before termination has a Taylor decrease at least
`(ς κ_δ)^{q+1}/q! ε_min^{q+1}`, and successful iterations decrease `f` by `η₁` times this
(Lemma 12.2.4 with a feasible set; `π_j = q + 1`). -/
theorem lemma_14_2_2_trq (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d)
    (hf : LipschitzDerivsAnchored f C C 1 q L) (hXC : X ⊆ C) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i ≤ k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i) :
    (P.ς * Optimization.trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
        Optimization.finMin 1 ε q ^ (q + 1) ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ Chapter12.trqRho f x s jk k →
        P.η₁ * ((P.ς * Optimization.trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
          Optimization.finMin 1 ε q ^ (q + 1)) ≤ f (x k) - f (x (k + 1))) :=
  Optimization.IsTRqRun.taylorDecrement_ge_of_anchored h (hf.mono_left hXC) hXC
    (fun _ hy _ => hy) hx0 hε hϑ hϑ1 hk

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRq-SC row: every TRq-SC run terminates at some
`k_ε` with `x_{k_ε} ∈ X` and the constrained `(ε, δ)`-certificate over `{d | x_{k_ε} + d ∈ X}`,
within the bounds of Theorem 12.2.5 (`O(max_j ε_j^{-(q+1)})`), under f.D1qL on an open convex
`C ⊇ X` without the normalization `L_j ≥ 1`. -/
theorem theorem_14_2_4_trq {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f C C 1 q L) (hXC : X ⊆ C) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d) :
    ∃ kε, Optimization.IsFirstHit (Chapter12.trqStop f P q ε ϑ x Δ d) kε ∧ x kε ∈ X ∧
      min (Δ kε) ϑ ∈ Ioc 0 1 ∧
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε
        (fun _ => min (Δ kε) ϑ) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        Optimization.kappaATRq f P q L ϑ (x 0) * (f (x 0) - flow) /
            Optimization.finMin 1 ε q ^ (q + 1) +
          Optimization.kappaBTRq P * |Real.log (Optimization.finMin 1 ε q)| +
          Optimization.kappaCTRq f P q L ϑ (x 0) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Chapter12.trqRho f x s jk k) kε : ℝ) ≤
        Optimization.kappaSTRq f P q L ϑ (x 0) * (f (x 0) - flow) /
          Optimization.finMin 1 ε q ^ (q + 1) + 1 :=
  Optimization.IsTRqRun.complexity hb (hf.mono_left hXC) hXC
    (fun _ hy _ => hy) hx0 hε hϑ hϑ1 h

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRq-SC row (Lemma 2.3.1 with the radius lower
bound of Lemma 12.2.3 with a feasible set, `Optimization.IsTRqRun.radius_ge_of_anchored`): for a
TRq-SC run under f.D1qL on an open convex `C ⊇ X` (without the normalization `L_j ≥ 1`), `x₀ ∈ X`,
`ε ∈ (0, 1]^q` and `ϑ ∈ [ε_min, 1]`, every iteration `k` reached (up to and including termination)
satisfies `k ≤ κ_uns |𝒮_k| + κ_unc`
(14.2.13) with `κ_uns = 1 + log γ₃/|log γ₂|` and
`κ_unc = |log(min(γ₁ ϑ, κ_Δ ς ε_min)/Δ₀)|/|log γ₂|` (`κ_Δ` of (12.2.14)). -/
theorem lemma_14_2_3_trq (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d)
    (hf : LipschitzDerivsAnchored f C C 1 q L) (hXC : X ⊆ C) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i < k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i) :
    (k : ℝ) ≤
      (Optimization.successSet (fun j => P.η₁ ≤ Chapter12.trqRho f x s jk j) k).card *
          (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (min (P.γ₁ * ϑ) (Optimization.trqKappaDelta f P q L ϑ (x 0) *
          (P.ς * Optimization.finMin 1 ε q)) / P.Δ₀)| / |Real.log P.γ₂| :=
  Optimization.IsTRqRun.le_succ_count_of_anchored h (hf.mono_left hXC) hXC
    (fun _ hy _ => hy) hx0 hε hϑ hϑ1 hk

end TRqSC

section ARqpSC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {X C : Set E}
  {P : Optimization.ARqpParams} {p q : ℕ} {ε δ₀ : ℕ → ℝ} {x s : ℕ → E} {σ : ℕ → ℝ}
  {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {L : ℕ → ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqp-SC row (Lemma 12.2.13 with a feasible set):
for an ARqp-SC run (`Chapter12.algorithm_12_2_2_feasible`, `X ⊆ C`) under f.D1pL on an open convex
`C` and `θ < ς`, every successful iteration `k` not followed by termination decreases `f` by at
least `η₁ κ_{Δm} min_j ε_j^{π_j}`, provided the radius policy holds in radii mode `u`: unit radii
`δ_{k+1,j} = 1` (`u`, `π_j = (p+1)/(p-j+1)`), or a long step or the lower bound (12.2.51) at every
order (`¬ u`, `π_j = j(p+1)/p`), with `π_j = Optimization.arqpPiOf u p j` and
`κ_{Δm} = Optimization.arqpKappaDmOf u`. The mode `u = False` gives the "otherwise" entry
`j(p+1)/p` of the table for every `q` and `X`; the unit-radii entries need `δ_{k,2} = 1` (the
table's `X = ℝⁿ`, `q = 2`) and `δ_{k,1} = 1` (convex `X`), which here is the hypothesis `u` on the
radii. The book's split is the mode `u = (q ≤ 2)` (`Chapter12.arqpPi`, `Chapter12.arqpKappaDm`). -/
theorem lemma_14_2_2_arqp (hf : LipschitzDerivsAnchored f C C 1 p L)
    (hL : ∀ j ∈ Finset.Icc 1 p, 1 ≤ L j) (hXC : X ⊆ C) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i)
    (hs : P.η₁ ≤ Optimization.arqpRho f p x s σ k)
    (hk1 : ¬ Optimization.arqpStop₁ P q ε (Optimization.arqpData f p x σ) δ d (k + 1))
    {u : Prop} [Decidable u] (hrad : (u → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (¬ u → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        Optimization.arqpKappaDelta P (Optimization.finMax 1 L p)
          (Optimization.arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    Optimization.arqpKappaDmOf u P L p q *
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      P.η₁ * (Optimization.arqpKappaDmOf u P L p q *
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q) ≤
        f (x k) - f (x (k + 1)) :=
  Optimization.IsARqpRun.decrease ((hf.mono_left hXC).mono (hq.trans hqp) le_rfl)
    (hL p (Finset.mem_Icc.2 ⟨hq.trans hqp, le_rfl⟩)) hXC (fun _ hy _ => hy) hq hqp hθς hε h hk hs
    hk1 hrad

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqp-SC row (Lemma 2.4.1 with the bound
`σ_max = max(σ₀, γ₃ L_{f,p}/(1 - η₂))` of Lemma 12.2.13's analysis): for every iteration `k`
reached (under f.D1pL on an open convex `C ⊇ X`, without the normalization `L_j ≥ 1`),
`k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns = 1 + |log γ₁|/log γ₂` and
`κ_unc = log(σ_max/σ₀)/log γ₂`. The other rows are `lemma_14_2_3_arqpc`, `lemma_14_2_3_trq`,
`lemma_14_2_3_trqida`, `lemma_14_2_3_trqeda`, `lemma_14_2_3_arqpida` and `lemma_14_2_3_arqpeda`. -/
theorem lemma_14_2_3 (hf : LipschitzDerivsAnchored f C C 1 p L) (hXC : X ⊆ C) (hp : 1 ≤ p)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRho f p x s σ j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂ :=
  h.toIsARRun.le_succ_count hk
    (Optimization.IsARqpRun.sigma_le_of_anchored ((hf.mono_left hXC).mono hp le_rfl)
    hXC (fun _ hy _ => hy) h k hk).2

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqp-SC row (Theorem 12.2.14 with a feasible
set): under f.bB.X, f.D1pL on an open convex `C ⊇ X`, `σ_min > 0`, `θ < ς` and the radius policy
in radii mode `u` (`δ = 1` if `u`, (12.2.51) at every order if `¬ u`), every ARqp-SC run
terminates at some `k_ε` with `x_{k_ε} ∈ X` and an `(ε, δ_ε)`-approximate `q`-th order
certificate over `{d | x_{k_ε} + d ∈ X}`, within the bounds of Theorem 12.2.14 (orders
`O(max_j ε_j^{-π_j})`, `π_j = Optimization.arqpPiOf u p j`). The mode `u = False` gives the
"otherwise" order `j(p+1)/p` of the table for every `q` and `X`; the book's split is the mode
`u = (q ≤ 2)` (`Chapter12.arqpPi`). -/
theorem theorem_14_2_4_arqp {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f C C 1 p L) (hL : ∀ j ∈ Finset.Icc 1 p, 1 ≤ L j)
    (hXC : X ⊆ C) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm)
    {u : Prop} [Decidable u]
    (hrad : (u → (∀ j ∈ Finset.Icc 1 q, δ₀ j = 1) ∧
        ∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) →
          ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      (¬ u → ∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) → ‖s k‖ < 1 →
        ∀ j ∈ Finset.Icc 1 q,
          Optimization.arqpKappaDelta P (Optimization.finMax 1 L p) (σ k) * ε j ≤ δs k j)) :
    ∃ kε, Optimization.IsFirstHit (Optimization.arqpStop f P p q ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δε j ∈ Ioc 0 1) ∧
        Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤ Optimization.kappaAARqpOf u P L p q * (f (x 0) - flow) /
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q +
          Optimization.kappaCARqp P L p ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRho f p x s σ k) kε : ℝ) ≤
        Optimization.kappaSARqpOf u P L p q * (f (x 0) - flow) /
          Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q + 2 :=
  Optimization.IsARqpRun.complexity hb ((hf.mono_left hXC).mono (hq.trans hqp) le_rfl)
    (hL p (Finset.mem_Icc.2 ⟨hq.trans hqp, le_rfl⟩))
    ((hf.mono_left hXC).norm_iteratedFDeriv_le_finMax fun j hj => zero_le_one.trans (hL j hj))
    hXC (fun _ hy _ => hy) hq hqp hσmin hθς hε hδ₀ h hrad

end ARqpSC

/-! ### The TRq-SC and ARqp-SC rows under the anchored assumptions

The remark after (14.2.10) of [cartis2022evaluation]: the rows of Lemmas 14.2.2–14.2.3 and
Theorem 14.2.4 only use the anchored assumption f.D1qLaB.X (TRq-SC) or f.D1pLaB.X (ARqp-SC) with
the starting point `x₀ = x 0`. The iterates lie in the sublevel set `𝓛_f(x₀)` (the objective does
not increase along the runs), the models are built at iterates, and the trial points (in
`X ⊆ X₀`) are related to them by Taylor's theorem anchored at the iterate. The bound (14.2.10) is
not used: the jet bounds at the anchors follow from (14.2.9) at the interior points of `X₀`
(`LipschitzDerivsAnchored.norm_iteratedFDeriv_le_finMax`), and the constants are those of the
rows above with the anchored Lipschitz constants `L_{f,j}`. -/

section Anchored

variable {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {L B : ℕ → ℝ}

/-- **Assumption f.D0qLaB.X** of [cartis2022evaluation], §14.2.1 (and f.D0pLaB.X with `p` in
place of `q`): f.D1qLaB.X (the anchored Lipschitz condition (14.2.9) and the bound (14.2.10) for
`j ∈ [1:q]`), together with (14.2.9) for `j = 0`, `|f(x) - f(y)| ≤ L_{f,0} ‖x - y‖` for
`x ∈ 𝓛_f(x₀)` and `y ∈ X₀`, with `L_{f,0} ≥ 1`. The book extends only the indices of (14.2.9) to
`[0:q]`; `AssumptionD1qLaBX` with `j₀ = 0`, which also bounds `|f|` on `𝓛_f(x₀)`, implies it
(`AssumptionD1qLaBX.toD0qLaBX`). -/
structure AssumptionD0qLaBX (f : ℝⁿ → ℝ) (X X₀ : Set ℝⁿ) (x₀ : ℝⁿ) (q : ℕ) (L B : ℕ → ℝ) : Prop
    extends AssumptionD1qLaBX f X X₀ x₀ 1 q L B where
  /-- `L_{f,0} ≥ 1`. -/
  one_le_lip_zero : 1 ≤ L 0
  /-- (14.2.9) for `j = 0`. -/
  lipschitzAnchored_zero : IteratedFDerivLipschitzAnchored f 0 (L 0) (sublevel f X x₀) X₀

/-- `AssumptionD1qLaBX` with `j₀ = 0` (which also asks `|f| ≤ B_{f,0}` on `𝓛_f(x₀)`) gives
f.D0qLaB.X. -/
theorem AssumptionD1qLaBX.toD0qLaBX {x₀ : ℝⁿ} {q : ℕ} (h : AssumptionD1qLaBX f X X₀ x₀ 0 q L B) :
    AssumptionD0qLaBX f X X₀ x₀ q L B where
  isOpen := h.isOpen
  convex := h.convex
  subset := h.subset
  contDiffOn := h.contDiffOn
  one_le_lip j hj := h.one_le_lip j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj)
  one_le_bound j hj := h.one_le_bound j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj)
  lipschitzAnchored j hj := h.lipschitzAnchored j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj)
  norm_le j hj := h.norm_le j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj)
  one_le_lip_zero := h.one_le_lip 0 (Finset.mem_Icc.2 ⟨le_rfl, Nat.zero_le q⟩)
  lipschitzAnchored_zero := h.lipschitzAnchored 0 (Finset.mem_Icc.2 ⟨le_rfl, Nat.zero_le q⟩)

/-- f.D0qLaB.X with anchor point `x₀` gives the smoothness hypothesis `LipschitzDerivsAnchored`
of the library on `X₀` with the orders `[0:q]` and the anchor set `𝓛_f(x₀)`; the bound (14.2.10)
is not used. -/
theorem AssumptionD0qLaBX.lipschitzDerivsAnchored {x₀ : ℝⁿ} {q : ℕ}
    (h : AssumptionD0qLaBX f X X₀ x₀ q L B) :
    LipschitzDerivsAnchored f X₀ (sublevel f X x₀) 0 q L where
  isOpen := h.isOpen
  convex := h.convex
  subset := sublevel_subset.trans h.subset
  contDiffAt _ hy := h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy)
  lipschitzAnchored j hj := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact h.lipschitzAnchored_zero
    · exact h.lipschitzAnchored j (Finset.mem_Icc.2 ⟨hj0, (Finset.mem_Icc.1 hj).2⟩)

/-- The constants of f.D0qLaB.X are normalized: `L_{f,j} ≥ 1` for `j ∈ [0:q]`. -/
theorem AssumptionD0qLaBX.normalized {x₀ : ℝⁿ} {q : ℕ} (h : AssumptionD0qLaBX f X X₀ x₀ q L B) :
    ∀ j ≤ q, 1 ≤ L j := fun j hj => by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact h.one_le_lip_zero
  · exact h.one_le_lip j (Finset.mem_Icc.2 ⟨hj0, hj⟩)

/-- f.D0qLaB.X is f.D1qLaB.X together with (14.2.9) for `j = 0`, with `L_{f,0} ≥ 1`. -/
theorem assumptionD0qLaBX_iff {x₀ : ℝⁿ} {q : ℕ} : AssumptionD0qLaBX f X X₀ x₀ q L B ↔
    AssumptionD1qLaBX f X X₀ x₀ 1 q L B ∧ 1 ≤ L 0 ∧
      IteratedFDerivLipschitzAnchored f 0 (L 0) (sublevel f X x₀) X₀ :=
  ⟨fun h => ⟨h.toAssumptionD1qLaBX, h.one_le_lip_zero, h.lipschitzAnchored_zero⟩,
    fun ⟨h, h1, h0⟩ => ⟨h, h1, h0⟩⟩

section TRq

variable {P : Optimization.TRqParams} {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → ℝⁿ} {Δ : ℕ → ℝ}
  {jk : ℕ → ℕ} {d : ℕ → ℕ → ℝⁿ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRq-SC row under f.D1qLaB.X (with the anchor point
`x₀ = x 0`; the remark after (14.2.10)): the decreases of `lemma_14_2_2_trq`. -/
theorem lemma_14_2_2_trq_anchored (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d)
    (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 q L B) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i ≤ k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i) :
    (P.ς * Optimization.trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
        Optimization.finMin 1 ε q ^ (q + 1) ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ Chapter12.trqRho f x s jk k →
        P.η₁ * ((P.ς * Optimization.trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
          Optimization.finMin 1 ε q ^ (q + 1)) ≤ f (x k) - f (x (k + 1))) :=
  Optimization.IsTRqRun.taylorDecrement_ge_of_anchored h hf.toLipschitzDerivsAnchored
    hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) hx0 hε hϑ hϑ1 hk

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRq-SC row under f.D1qLaB.X (with the anchor point
`x₀ = x 0`): the bound (14.2.13) of `lemma_14_2_3_trq`. -/
theorem lemma_14_2_3_trq_anchored (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d)
    (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 q L B) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i < k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i) :
    (k : ℝ) ≤
      (Optimization.successSet (fun j => P.η₁ ≤ Chapter12.trqRho f x s jk j) k).card *
          (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (min (P.γ₁ * ϑ) (Optimization.trqKappaDelta f P q L ϑ (x 0) *
          (P.ς * Optimization.finMin 1 ε q)) / P.Δ₀)| / |Real.log P.γ₂| :=
  Optimization.IsTRqRun.le_succ_count_of_anchored h hf.toLipschitzDerivsAnchored
    hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) hx0 hε hϑ hϑ1 hk

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRq-SC row under f.bB.X and f.D1qLaB.X (with the
anchor point `x₀ = x 0`; the remark after (14.2.10)): the conclusion of `theorem_14_2_4_trq`. -/
theorem theorem_14_2_4_trq_anchored {flow : ℝ} (hb : AssumptionBbX f X flow)
    (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 q L B) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d) :
    ∃ kε, Optimization.IsFirstHit (Chapter12.trqStop f P q ε ϑ x Δ d) kε ∧ x kε ∈ X ∧
      min (Δ kε) ϑ ∈ Ioc 0 1 ∧
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε
        (fun _ => min (Δ kε) ϑ) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        Optimization.kappaATRq f P q L ϑ (x 0) * (f (x 0) - flow) /
            Optimization.finMin 1 ε q ^ (q + 1) +
          Optimization.kappaBTRq P * |Real.log (Optimization.finMin 1 ε q)| +
          Optimization.kappaCTRq f P q L ϑ (x 0) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Chapter12.trqRho f x s jk k) kε : ℝ) ≤
        Optimization.kappaSTRq f P q L ϑ (x 0) * (f (x 0) - flow) /
          Optimization.finMin 1 ε q ^ (q + 1) + 1 :=
  Optimization.IsTRqRun.complexity hb hf.toLipschitzDerivsAnchored hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hx0 hε hϑ hϑ1 h

end TRq

section ARqp

variable {P : Optimization.ARqpParams} {p q : ℕ} {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}
  {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqp-SC row under f.D1pLaB.X (with the anchor
point `x₀ = x 0`; the remark after (14.2.10)): the decreases of `lemma_14_2_2_arqp`, in either
radii mode `u`. -/
theorem lemma_14_2_2_arqp_anchored (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 p L B) (hq : 1 ≤ q)
    (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i)
    (hs : P.η₁ ≤ Optimization.arqpRho f p x s σ k)
    (hk1 : ¬ Optimization.arqpStop₁ P q ε (Optimization.arqpData f p x σ) δ d (k + 1))
    {u : Prop} [Decidable u] (hrad : (u → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (¬ u → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        Optimization.arqpKappaDelta P (Optimization.finMax 1 L p)
          (Optimization.arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    Optimization.arqpKappaDmOf u P L p q *
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      P.η₁ * (Optimization.arqpKappaDmOf u P L p q *
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q) ≤
        f (x k) - f (x (k + 1)) :=
  Optimization.IsARqpRun.decrease (hf.toLipschitzDerivsAnchored.mono (hq.trans hqp) le_rfl)
    (hf.one_le_lip p (Finset.mem_Icc.2 ⟨hq.trans hqp, le_rfl⟩)) hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hq hqp hθς hε h hk hs hk1 hrad

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqp-SC row under f.D1pLaB.X (with the anchor
point `x₀ = x 0`): the bound (14.2.13) of `lemma_14_2_3`. -/
theorem lemma_14_2_3_anchored (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 p L B) (hp : 1 ≤ p)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRho f p x s σ j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂ :=
  h.toIsARRun.le_succ_count hk
    (Optimization.IsARqpRun.sigma_le_of_anchored (hf.toLipschitzDerivsAnchored.mono hp le_rfl)
    hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) h k hk).2

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqp-SC row under f.bB.X and f.D1pLaB.X (with
the anchor point `x₀ = x 0`; the remark after (14.2.10)): the conclusion of `theorem_14_2_4_arqp`,
in either radii mode `u`. -/
theorem theorem_14_2_4_arqp_anchored {flow : ℝ} (hb : AssumptionBbX f X flow)
    (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 p L B) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm)
    {u : Prop} [Decidable u]
    (hrad : (u → (∀ j ∈ Finset.Icc 1 q, δ₀ j = 1) ∧
        ∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) →
          ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      (¬ u → ∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) → ‖s k‖ < 1 →
        ∀ j ∈ Finset.Icc 1 q,
          Optimization.arqpKappaDelta P (Optimization.finMax 1 L p) (σ k) * ε j ≤ δs k j)) :
    ∃ kε, Optimization.IsFirstHit (Optimization.arqpStop f P p q ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δε j ∈ Ioc 0 1) ∧
        Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤ Optimization.kappaAARqpOf u P L p q * (f (x 0) - flow) /
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q +
          Optimization.kappaCARqp P L p ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRho f p x s σ k) kε : ℝ) ≤
        Optimization.kappaSARqpOf u P L p q * (f (x 0) - flow) /
          Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q + 2 :=
  Optimization.IsARqpRun.complexity hb (hf.toLipschitzDerivsAnchored.mono (hq.trans hqp) le_rfl)
    (hf.one_le_lip p (Finset.mem_Icc.2 ⟨hq.trans hqp, le_rfl⟩))
    (hf.toLipschitzDerivsAnchored.norm_iteratedFDeriv_le_finMax fun j hj =>
      zero_le_one.trans (hf.one_le_lip j hj)) hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hq hqp hσmin hθς hε hδ₀ h hrad

end ARqp

end Anchored

/-! ### The dynamic-accuracy algorithms with simple constraints

The TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC rows of Lemmas 14.2.2–14.2.3 and
Theorem 14.2.4 are instances of the library's analysis of the runs with a feasible set
(`Optimization.IsTRqIDARun`, …, `Optimization.IsARqpEDARun`; `X = univ` gives the algorithms of
Chapter 13) under `LipschitzDerivsAnchored`. Each row `N` is stated twice: `N` under f.D0qL
(f.D0pL) on an open convex `C ⊇ X` (`LipschitzDerivsAnchored f C C 0 q L` with `L_j ≥ 1`,
anchors `A = C`), and
`N_anchored` under the book's f.D0qLaB.X (f.D0pLaB.X) with the starting point as anchor
(`AssumptionD0qLaBX`, anchors `𝓛_f(x₀)`).
For the IDA algorithms, which have no termination rule, "before termination" reads
"before the first iterate that is approximately optimal on `X`"; for the regularization
algorithms the radius policy is the radii control in either mode
(`Optimization.ARqpDARadiiControl u`): unit radii `δ = 1` (`u`), achievable for `X = ℝⁿ` with
`q ≤ 2` or for `q = 1` with `X` convex, or the (12.2.51)-type bounds at every order (`¬ u`),
available in every case; the radii control of Theorem 13.1.19 (`Optimization.RadiiControl`) is the
mode `u = (q ≤ 2)`. -/

section TRqIDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C A X₀ : Set ℝⁿ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {L B : ℕ → ℝ} {κΔ : ℝ}


/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqIDA-SC row (Lemma 13.1.5 with a feasible set):
for a TRqIDA-SC run (`Optimization.IsTRqIDARun`) under f.D0qL on an open convex
`C ⊇ X` and an admissible `κ_Δ` (`Optimization.IsTRKappaDelta`, `κ_δ = κ_Δ/2`), every successful
iteration `k` (`k ∈ 𝒯`, `ρ_k ≥ η₁`) decreases `f` by at least
`η₁ (ς κ_δ)^{q+1}/(2 q!) ε_min^{q+1}` (`π_j = q + 1`, as for TRq-SC). -/
theorem lemma_14_2_2_trqida (hf : LipschitzDerivsAnchored f C C 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j) (hXC : X ⊆ C)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ} (hk : ¬ acc k)
    (hρ : P.η₁ ≤ trqRatio f D x s jk k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqIDARun.decrease_ge hf hL hXC (fun _ hy _ => hXC hy) hrun
    hκΔ hk).2 hρ

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqIDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_2_trqida`. -/
theorem lemma_14_2_2_trqida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ} (hk : ¬ acc k)
    (hρ : P.η₁ ≤ trqRatio f D x s jk k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqIDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hrun hκΔ hk).2 hρ


/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqIDA-SC row (Lemma 13.1.1 with the radius bound
of Lemma 13.1.4, and the count of accuracy-improving iterations of Theorem 13.1.8): for a
TRqIDA-SC run under f.D0qL on an open convex `C ⊇ X` and an admissible `κ_Δ`, every iteration `k`
up to the first iterate that is approximately optimal on `X` satisfies
`k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13), with `𝒮_k` the successful iterations in `[0, k]`,
`κ_uns = 1 + log γ₃/|log γ₂|` and `κ_unc = |log(ς κ_δ ε_min/Δ₀)|/|log γ₂| + N_𝒜`, where
`N_𝒜 = q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` bounds the number of
accuracy-improving iterations. -/
theorem lemma_14_2_3_trqida (hf : LipschitzDerivsAnchored f C C 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j) (hXC : X ⊆ C)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ trqIDATest f X P ε x Δ j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 1)) :=
  IsTRqIDARun.le_card_succ hf hL hXC (fun _ hy _ => hXC hy) hrun
      hκΔ hk

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqIDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_3_trqida`. -/
theorem lemma_14_2_3_trqida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ trqIDATest f X P ε x Δ j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 1)) :=
  IsTRqIDARun.le_card_succ hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hrun hκΔ hk


/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqIDA-SC row (Theorem 13.1.8 with a feasible
set): under f.bB.X, f.D0qL on an open convex `C ⊇ X` and for an admissible `κ_Δ`, every
TRqIDA-SC run has a first iterate `x_{k_ε} ∈ X` that is an `(ε, δ_ε)`-approximate `q`-th order
minimizer on `X` (`Optimization.trqIDATest`, `δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]`), before which at
most the numbers of function and derivative evaluations of Theorem 13.1.8 are made
(`O(max_j ε_j^{-(q+1)})`). -/
theorem theorem_14_2_4_trqida (hf : LipschitzDerivsAnchored f C C 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) :
    ∃ kε, IsFirstHit (trqIDATest f X P ε x Δ) kε ∧ x kε ∈ X ∧ 0 < trqDARadius P Δ kε ∧
      trqDARadius P Δ kε ≤ 1 ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)| +
          (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 2 := by
  obtain ⟨kε, h1, h2, h3, h4, h5⟩ := IsTRqIDARun.complexity hf
      hL hXC (fun _ hy _ => hXC hy) hb hrun hκΔ
  exact ⟨kε, h1, hrun.mem kε, h2, h3, h4, h5⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqIDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`theorem_14_2_4_trqida`. -/
theorem theorem_14_2_4_trqida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) :
    ∃ kε, IsFirstHit (trqIDATest f X P ε x Δ) kε ∧ x kε ∈ X ∧ 0 < trqDARadius P Δ kε ∧
      trqDARadius P Δ kε ≤ 1 ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)| +
          (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 2 := by
  obtain ⟨kε, h1, h2, h3, h4, h5⟩ := IsTRqIDARun.complexity hf.lipschitzDerivsAnchored
      hf.normalized hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) hb hrun hκΔ
  exact ⟨kε, h1, hrun.mem kε, h2, h3, h4, h5⟩

end TRqIDASC

section TRqEDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C A X₀ : Set ℝⁿ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ}
  {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ} {R : ℕ → Prop}
  {L B : ℕ → ℝ} {κΔ : ℝ}


/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqEDA-SC row (Lemma 13.3.2 with a feasible set):
for a TRqEDA-SC run (`Optimization.IsTRqEDARun`) under f.D0qL on an open convex
`C ⊇ X` and an admissible `κ_Δ` (`κ_{∇,max} = 1`, `κ_δ = κ_Δ/2`), every successful iteration `k`
before termination decreases `f` by at least `η₁ (ς κ_δ)^{q+1}/(2 q!) ε_min^{q+1}`. -/
theorem lemma_14_2_2_trqeda (hf : LipschitzDerivsAnchored f C C 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j) (hXC : X ⊆ C)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqEDARun.decrease_ge hf hL hXC (fun _ hy _ => hXC hy) hrun
    hκΔ hk ha).2 hρ

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqEDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_2_trqeda`. -/
theorem lemma_14_2_2_trqeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqEDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hrun hκΔ hk ha).2 hρ


/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqEDA-SC row (Lemma 13.1.1 with the radius bound
of Lemma 13.1.4 for TRqEDA, and the count of accuracy-improving iterations of Theorem 13.3.4): for
a TRqEDA-SC run under f.D0qL on an open convex `C ⊇ X` and an admissible `κ_Δ`
(`κ_{∇,max} = 1`), every iteration `k` reached (up to and including termination) satisfies
`k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns = 1 + log γ₃/|log γ₂|` and
`κ_unc = |log(ς κ_δ ε_min/Δ₀)|/|log γ₂| + N_𝒜`,
`N_𝒜 = q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem lemma_14_2_3_trqeda (hf : LipschitzDerivsAnchored f C C 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j) (hXC : X ⊆ C)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| / |Real.log P.γh| + 1)) :=
  IsTRqEDARun.le_card_succ hf hL hXC (fun _ hy _ => hXC hy) hrun
      hκΔ hk

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqEDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_3_trqeda`. -/
theorem lemma_14_2_3_trqeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| / |Real.log P.γh| + 1)) :=
  IsTRqEDARun.le_card_succ hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hrun hκΔ hk


/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqEDA-SC row (Theorem 13.3.4 with a feasible
set): under f.bB.X, f.D0qL on an open convex `C ⊇ X` and for an admissible `κ_Δ`
(`κ_{∇,max} = 1`), every TRqEDA-SC run terminates at some `k_ε` with `x_{k_ε} ∈ X` an
`(ε, δ_ε)`-approximate `q`-th order minimizer on `X`, `δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]`, within
the evaluation bounds of Theorem 13.3.4 (`O(max_j ε_j^{-(q+1)})`). -/
theorem theorem_14_2_4_trqeda (hf : LipschitzDerivsAnchored f C C 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) :
    ∃ kε, IsFirstHit (edaStopTR P ε D Δ h dd) kε ∧ x kε ∈ X ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε
        (fun _ => trqDARadius P Δ kε) ∧
      0 < trqDARadius P Δ kε ∧ trqDARadius P Δ kε ≤ 1 ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1)) +
          2 * (1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)|) +
          2 * (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| /
            |Real.log P.γh| + 2 := by
  obtain ⟨kε, h1, h2, h3, h4, h5, h6⟩ := IsTRqEDARun.complexity hf
      hL hXC (fun _ hy _ => hXC hy) hb hrun hκΔ
  exact ⟨kε, h1, hrun.mem fun j hj => h1.2 j hj, h2, h3, h4, h5, h6⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqEDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`theorem_14_2_4_trqeda`. -/
theorem theorem_14_2_4_trqeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) :
    ∃ kε, IsFirstHit (edaStopTR P ε D Δ h dd) kε ∧ x kε ∈ X ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε
        (fun _ => trqDARadius P Δ kε) ∧
      0 < trqDARadius P Δ kε ∧ trqDARadius P Δ kε ≤ 1 ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1)) +
          2 * (1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)|) +
          2 * (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| /
            |Real.log P.γh| + 2 := by
  obtain ⟨kε, h1, h2, h3, h4, h5, h6⟩ := IsTRqEDARun.complexity hf.lipschitzDerivsAnchored
      hf.normalized hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) hb hrun hκΔ
  exact ⟨kε, h1, hrun.mem fun j hj => h1.2 j hj, h2, h3, h4, h5, h6⟩

end TRqEDASC

section ARqpIDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C A X₀ : Set ℝⁿ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ}
  {acc : ℕ → Prop} {L B : ℕ → ℝ} {u : Prop}


/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpIDA-SC row (Lemma 13.1.18 with a feasible set):
for an ARqpIDA-SC run (`Optimization.IsARqpIDARun`) under f.D0pL on an open convex `C ⊇ X`
and the radii control at `k`, every successful iteration `k` whose successor `x_{k+1}` is not
approximately optimal on `X` decreases `f` by at least `½ η₁ κ_{Δm} min_j ε_j^{π_j}`, with
`κ_{Δm}` of Lemma 13.1.18 and the radii control in either mode `u`
(`Optimization.ARqpDARadiiControl`): unit radii `δ_{s_k} = 1` (`u`), which Step 2 guarantees for
`X = ℝⁿ` with `q ≤ 2` or for `q = 1` with `X` convex, with `π_j = (p+1)/(p-j+1)`, or the
(12.2.51)-type lower bounds at every order (`¬ u`), available for every `q` and `X`, with
`π_j = j(p+1)/p` (`π_j = Optimization.arPiOf u p j`; the radii control of Theorem 13.1.19,
`Optimization.RadiiControl`, is the mode `u = (q ≤ 2)`). -/
theorem lemma_14_2_2_arqpida (hf : LipschitzDerivsAnchored f C C 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hXC : X ⊆ C)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {k : ℕ}
    [Decidable u]
    (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k)
    (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arqpIDATest f X P ε x (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
        (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) :=
  (IsARqpIDARun.decrease_ge hf hL hXC (fun _ hy _ => hXC hy)
    hrun hrc hk hρ hnot).2

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpIDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_2_arqpida`. -/
theorem lemma_14_2_2_arqpida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {k : ℕ}
    [Decidable u]
    (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k)
    (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arqpIDATest f X P ε x (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
        (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) :=
  (IsARqpIDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hrun hrc hk hρ hnot).2


/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpIDA-SC row (Lemma 13.1.9 with the bound `σ_max`
of Lemma 13.1.14, and the count of accuracy-improving iterations of Theorem 13.1.19): for an
ARqpIDA-SC run under f.D0pL on an open convex `C ⊇ X` and the radii control, every iteration `k` up
to the first iterate that is approximately optimal on `X` satisfies `k ≤ κ_uns |𝒮_k| + κ_unc`
(14.2.13) with `κ_uns = 1 + |log γ₁|/log γ₂` and `κ_unc = log(σ_max/σ₀)/log γ₂ + N_𝒜`, `N_𝒜 =
p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. The radii control
(`Optimization.ARqpDARadiiControl u`) may be in either mode (unit radii, or the (12.2.51)-type lower
bounds at every order). -/
theorem lemma_14_2_3_arqpida (hf : LipschitzDerivsAnchored f C C 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hXC : X ⊆ C)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ arqpIDATest f X P ε x j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 1)) :=
  IsARqpIDARun.le_card_succ hf hL hXC (fun _ hy _ => hXC hy)
      hrun hrc hk

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpIDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_3_arqpida`. -/
theorem lemma_14_2_3_arqpida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ arqpIDATest f X P ε x j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 1)) :=
  IsARqpIDARun.le_card_succ hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hrun hrc hk


/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpIDA-SC row (Theorem 13.1.19 with a feasible
set): under f.bB.X, f.D0pL on an open convex `C ⊇ X` and the radii control at every iteration, every
ARqpIDA-SC run reaches a first iterate `x_{k_ε} ∈ X` that is an `(ε, δ_ε)`-approximate `q`-th order
minimizer on `X` for some radii `δ_ε ∈ (0, 1]^q` (`Optimization.arqpIDATest`), before which at most
`(1 + |log γ₁|/log γ₂) (f(x₀) - f_low)/c + κ^C` function evaluations and `(f(x₀) - f_low)/c + κ^E
|log ε_min| + κ^F + 3` derivative estimates are made, where `c = ½ η₁ κ_{Δm} min_j ε_j^{π_j}` is the
decrease of Lemma 14.2.2, and the constants are those of Theorem 13.1.19, with the radii control
in either mode `u` (`Optimization.ARqpDARadiiControl`): unit radii `δ_{s_k} = 1` (`u`), which
Step 2 guarantees for `X = ℝⁿ` with `q ≤ 2` or for `q = 1` with `X` convex, with
`π_j = (p+1)/(p-j+1)`, or the (12.2.51)-type lower bounds at every order (`¬ u`), available for
every `q` and `X`, with `π_j = j(p+1)/p` (`π_j = Optimization.arPiOf u p j`; the radii control of
Theorem 13.1.19, `Optimization.RadiiControl`, is the mode `u = (q ≤ 2)`). -/
theorem theorem_14_2_4_arqpida (hf : LipschitzDerivsAnchored f C C 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    [Decidable u]
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) :
    ∃ kε, IsFirstHit (arqpIDATest f X P ε x) kε ∧ x kε ∈ X ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j))) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 :=
  IsARqpIDARun.complexity_of_radiiControl hf hL hXC
      (fun _ hy _ => hXC hy) hb hrun hrc

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpIDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`theorem_14_2_4_arqpida`. -/
theorem theorem_14_2_4_arqpida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    [Decidable u]
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) :
    ∃ kε, IsFirstHit (arqpIDATest f X P ε x) kε ∧ x kε ∈ X ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j))) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 :=
  IsARqpIDARun.complexity_of_radiiControl hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hb hrun
    hrc

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpIDA-SC row on `X = ℝⁿ` with `q ≤ 2`, in
either mode of the radii control (a strengthening of Theorem 13.1.19 (1), which assumes unit
radii): under f.bB and f.D0pL, every
ARqpIDA run on `ℝⁿ` with `q ≤ 2` whose radii satisfy `Optimization.ARqpDARadiiControl u` for
*some* mode `u` (in particular the lower-bound mode `u = False`) satisfies the bounds of the
unit-radii mode, of order `max_j ε_j^{-(p+1)/(p-j+1)}`: a failure of the criterion
`Optimization.arqpIDATest` (approximate optimality for some radii in `(0, 1]^q`) is a failure at
unit radii, and for `q ≤ 2` the bound (13.1.57) on the model transfers to unit radii
(`Optimization.IsARqpIDARun.decrease_ge_unit`). Hence
the mode-`False` bound of `theorem_14_2_4_arqpida`, of order `ε^{-2(p+1)/p}`, is not sharp for
`q = 2 < p` on `ℝⁿ` (it exceeds `ε^{-(p+1)/(p-1)}`). -/
theorem theorem_14_2_4_arqpida_le_two (hf : LipschitzDerivsAnchored f univ univ 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) {flow : ℝ}
    (hb : ∀ y, flow ≤ f y) (hq2 : P.q ≤ 2)
    (hrun : IsARqpIDARun f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) :
    ∃ kε, IsFirstHit (arqpIDATest f univ P ε x) kε ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf True P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf True P.p j))) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf True P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf True P.p j)) +
          P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hLb := hrun.one_le_Lbar hL
  have hA := one_le_arConstA (hL _ le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hC := arStepConstOf_pos (u := True) (q := P.q) (p := P.p) (sub_pos.2 P.θ_lt_one)
    (zero_lt_one.trans_le hA) (arKappaDelta1_pos (Lb := lipMax L P.p + ordMax P.p κg * P.κh)
      (σ := arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (P := P) (by linarith))
  have hm : 0 < epsMin P.q (fun j => ε j ^ arPiOf True P.p j) :=
    Optimization.epsMin_pos P.one_le_q fun j hj => Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf True P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
      epsMin P.q (fun j => ε j ^ arPiOf True P.p j) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := IsARqpIDARun.complexity hf hL
      subset_rfl
    (fun _ hy _ => hy) (fun y _ => hb y) hrun hrc hc fun k hk hρ hnot =>
      IsARqpIDARun.decrease_ge_unit hf hL hq2 hrun hk hρ hnot
  exact ⟨kε, hk, h1, h2⟩

end ARqpIDASC

section ARqpEDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C A X₀ : Set ℝⁿ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop} {L B : ℕ → ℝ} {u : Prop}


/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpEDA-SC row (Lemma 13.3.7 with a feasible set):
for an ARqpEDA-SC run (`Optimization.IsARqpEDARun`) under f.D0pL on an open convex `C ⊇
X`, the radii control at `k` and `θ < ς/2`, every successful iteration `k` before termination with
`‖s_k‖ ≥ 1` or such that Step 1 at `k + 1` does not pass with unchanged radii decreases `f` by at
least `½ η₁ κ'_{Δm} min_j ε_j^{π_j}` (`κ'_{Δm}` of Lemma 13.3.7), with the radii control
in either mode `u` (`Optimization.ARqpDARadiiControl`): unit radii `δ_{s_k} = 1` (`u`), which
Step 2 guarantees for `X = ℝⁿ` with `q ≤ 2` or for `q = 1` with `X` convex, with
`π_j = (p+1)/(p-j+1)`, or the (12.2.51)-type lower bounds at every order (`¬ u`), available for
every `q` and `X`, with `π_j = j(p+1)/p` (`π_j = Optimization.arPiOf u p j`; the radii control of
Theorem 13.1.19, `Optimization.RadiiControl`, is the mode `u = (q ≤ 2)`). -/
theorem lemma_14_2_2_arqpeda (hf : LipschitzDerivsAnchored f C C 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hXC : X ⊆ C)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {k : ℕ} [Decidable u] (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc k)
    (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ)
        (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) /
        2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) :=
  (IsARqpEDARun.decrease_ge hf hL hXC (fun _ hy _ => hXC hy)
    hrun hrc hθ hk ha hρ hgood).2

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpEDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_2_arqpeda`. -/
theorem lemma_14_2_2_arqpeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {k : ℕ} [Decidable u] (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc k)
    (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ)
        (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) /
        2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) :=
  (IsARqpEDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hrun hrc hθ hk ha hρ hgood).2


/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpEDA-SC row (Lemma 13.1.9 with the bound `σ_max`
of Lemma 13.3.5, and the count of accuracy-improving iterations of Theorem 13.3.8): for an
ARqpEDA-SC run under f.D0pL on an open convex `C ⊇ X` and the radii control, every iteration `k`
reached (up to and including termination) satisfies `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns
= 1 + |log γ₁|/log γ₂` and `κ_unc = log(σ_max/σ₀)/log γ₂ + N_𝒜`, `N_𝒜 = p(q+1)/|log γ_h| |log ε_min|
+ |log(κ_acc/κ_h)|/|log γ_h| + 1`. The radii control (`Optimization.ARqpDARadiiControl u`) may be in
either mode (unit radii, or the (12.2.51)-type lower bounds at every order). -/
theorem lemma_14_2_3_arqpeda (hf : LipschitzDerivsAnchored f C C 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hXC : X ⊆ C)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1)) :=
  IsARqpEDARun.le_card_succ hf hL hXC (fun _ hy _ => hXC hy)
      hrun hrc hk

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpEDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_3_arqpeda`. -/
theorem lemma_14_2_3_arqpeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1)) :=
  IsARqpEDARun.le_card_succ hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hrun hrc hk


/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpEDA-SC row (Theorem 13.3.8 with a feasible
set): under f.bB.X, f.D0pL on an open convex `C ⊇ X`, the radii control at every iteration and `θ <
ς/2`, every ARqpEDA-SC run terminates at some `k_ε` with `x_{k_ε} ∈ X` an `(ε,
δ^{(1)}_{k_ε})`-approximate `q`-th order minimizer on `X`, `δ^{(1)}_{k_ε} ∈ (0, 1]^q`, after at most
`2 ((N + M + 1) c_T + log(σ_max/σ₀)/log γ₂)` inexact function evaluations and `N + 2M + 2`
derivative estimates, where `N = (f(x₀) - f_low)/c` with `c = ½ η₁ κ'_{Δm} min_j ε_j^{π_j}` the
decrease of Lemma 14.2.2, `M = p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` and
`c_T = 1 + |log γ₁|/log γ₂` (as in Theorem 13.3.8), with the radii control in either mode `u`
(`Optimization.ARqpDARadiiControl`): unit radii `δ_{s_k} = 1` (`u`), which Step 2 guarantees for
`X = ℝⁿ` with `q ≤ 2` or for `q = 1` with `X` convex, with `π_j = (p+1)/(p-j+1)`, or the
(12.2.51)-type lower bounds at every order (`¬ u`), available for every `q` and `X`, with
`π_j = j(p+1)/p` (`π_j = Optimization.arPiOf u p j`; the radii control of Theorem 13.1.19,
`Optimization.RadiiControl`, is the mode `u = (q ≤ 2)`). -/
theorem theorem_14_2_4_arqpeda (hf : LipschitzDerivsAnchored f C C 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    [Decidable u] (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hθ : P.θ < P.ς / 2) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧ x kε ∈ X ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (((f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
              (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
              epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh)
                  (arqpIDASigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
            (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 :=
  IsARqpEDARun.complexity_of_radiiControl hf hL hXC
      (fun _ hy _ => hXC hy) hb hrun hrc hθ

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpEDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`theorem_14_2_4_arqpeda`. -/
theorem theorem_14_2_4_arqpeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    [Decidable u] (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hθ : P.θ < P.ς / 2) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧ x kε ∈ X ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (((f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
              (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
              epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh)
                  (arqpIDASigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
            (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 :=
  IsARqpEDARun.complexity_of_radiiControl hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hb hrun
    hrc hθ

end ARqpEDASC

/-! ### Sharpness of the orders of Theorem 14.2.4

"The orders of complexity mentioned in the last column of the table are sharp": each row is
attained by a slow example, run with a simple feasible set (`X = ℝ`, `X = ℝ¹`, or a closed
nonconvex `X` for the "otherwise" entries that the reduction to `X = ℝⁿ` does not reach). -/

section Sharp

open Chapter13 Optimization

/-- f.D0qL with a single constant `L ≥ 1` is the library's smoothness hypothesis on the whole
space. -/
private theorem assumptionD0qL_of_lipschitzDerivsAnchored {m q : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ} {L : ℝ}
    (hf : LipschitzDerivsAnchored f univ univ 0 q (fun _ => L)) (hL : 1 ≤ L) :
    AssumptionD0qL f q (fun _ => L) :=
  assumptionD0qL_iff_lipschitzDerivsAnchored.2 ⟨hf, fun _ _ => hL⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness: the orders of the TRq-SC row
(`ε^{-(q+1)}`), of the ARqp-SC row for `q ≤ 2` (`ε^{-(p+1)/(p-q+1)}`) and of the ARqpC-SC row
for `q = 1` and convex `h` (`ε^{-(p+1)/p}`) are attained, by the slow examples of
Theorem 12.2.6, Corollary 12.2.16 and Corollary 14.1.11 run with the (simple) feasible set
`X = ℝ` (`univ`; `X = ℝ¹` and `h = ‖·‖` for ARqpC-SC). The ARqp-SC row for `q ≥ 3` is
`theorem_14_2_4_sharp_arqp`; the TRqIDA-SC and TRqEDA-SC rows are `theorem_14_2_4_sharp_trqida`
and `theorem_14_2_4_sharp_trqeda`, the ARqpIDA-SC and ARqpEDA-SC rows
`theorem_14_2_4_sharp_arqpida`, `theorem_14_2_4_sharp_arqpeda`,
`theorem_14_2_4_sharp_arqpeda_otherwise` and `theorem_14_2_4_sharp_arqpida_otherwise`. -/
theorem theorem_14_2_4_sharp {p q : ℕ} (hq : 1 ≤ q) :
    (∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : Optimization.TRqParams,
      P.Δ₀ = ε → ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f q (fun _ => L) ∧
        ∃ (x s : ℕ → ℝ) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_1_feasible f univ P q (fun j => j ! * ε) 1 x s Δ jk d ∧
          Optimization.IsFirstHit (Chapter12.trqStop f P q (fun j => j ! * ε) 1 x Δ d)
            ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (Optimization.funEvalCount ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ)) ∧
    (q ≤ 2 → q ≤ p → ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ P : Optimization.ARqpParams, P.σ₀ = (p ! : ℝ) / (q - 1)! →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_2_feasible f univ P p q (fun _ => ε) (fun _ => 1) x s σ
            (fun _ _ => 1) (fun _ _ => 1) d (fun _ _ => 0) ∧
          Optimization.IsFirstHit (Optimization.arqpStop f P p q (fun _ => ε) x s σ
              (fun _ _ => 1) d)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊) ∧
    (1 ≤ p → ∀ P : ARqpCParams, ∃ L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1),
        AssumptionCD1pL c p (fun _ => L) ∧ ‖c 0‖ ≤ L ∧
        AssumptionWBb (fun _ => 0) c (fun v => ‖v‖) univ 0 ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ)
          (d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)),
          algorithm_14_1_1 (fun _ => 0) c (fun v => ‖v‖) univ p 1 P (fun _ => ε) (fun _ => 1)
            x s σ δ δs d dm ∧
          Optimization.IsFirstHit
            (arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε) x s σ δ d)
            ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ ∧
          ε ^ (-((p + 1 : ℝ) / p)) + 1 ≤
            (Optimization.funEvalCount ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ : ℝ)) := by
  refine ⟨?_, fun hq2 hqp => ?_, fun hp P => ?_⟩
  · obtain ⟨flow, L, hL, H⟩ := Chapter12.theorem_12_2_6 hq
    refine ⟨flow, L, hL, fun ε hε hε1 P hP => ?_⟩
    obtain ⟨f, hb, hf, x, s, Δ, jk, d, hrun, -, -, hhit, -, hF, -⟩ := H ε hε hε1 P hP
    exact ⟨f, hb, hf, x, s, Δ, jk, d, Chapter12.algorithm_12_2_1_iff_feasible.1 hrun, hhit, hF⟩
  · obtain ⟨flow, L, hL, H⟩ := Chapter12.corollary_12_2_16 hq hq2 hqp
    refine ⟨flow, L, hL, fun ε hε hε1 P hP => ?_⟩
    obtain ⟨f, hb, hf, x, s, σ, d, hrun, -, hhit, -⟩ := H ε hε hε1 P hP
    exact ⟨f, hb, hf, x, s, σ, d, hrun, hhit⟩
  · obtain ⟨-, -, -, -, L, hL, H⟩ := corollary_14_1_11 hp P
    refine ⟨L, hL, fun ε hε hε1 => ?_⟩
    obtain ⟨c, hc, hc0, -, hw, x, s, σ, δ, δs, d, dm, hrun, -, hhit, -, hF, -⟩ := H ε hε hε1
    exact ⟨c, hc, hc0, hw, x, s, σ, δ, δs, d, dm, hrun, hhit, hF⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqp-SC row for `q ≥ 3`
(the "otherwise" order `ε^{-q(p+1)/p}`): the slow example of Theorem 12.2.17 run with the (simple)
feasible set `X = ℝ` (`univ`). For `3 ≤ q ≤ p` there are `f_low` and `L ≥ 1` such that for every
`ε ∈ (0, ½]` and ARqp constants with `σ₀` the weight (12.2.85) there is `f` with f.bB and f.D1pL
and an ARqp-SC run with radii `ε` satisfying the radius hypothesis of `theorem_14_2_4_arqp`
(`δ_{s_k,j} ≥ κ_δ(σ_k) ε_j`) that first terminates at `k_ε = ⌈ε^{-q(p+1)/p}⌉`, after
`k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` evaluations. -/
theorem theorem_14_2_4_sharp_arqp {p q : ℕ} (hq : 2 < q) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ P : Optimization.ARqpParams,
      P.σ₀ = Chapter12.arqpSigmaSharp p q →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_2_feasible f univ P p q (fun _ => ε) (fun _ => ε) x s σ
            (fun _ _ => ε) (fun _ _ => ε) d (fun _ _ => 0) ∧
          (∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d i) →
            ‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 q,
              Optimization.arqpKappaDelta P (Optimization.finMax 1 (fun _ => L) p) (σ k) * ε ≤ ε) ∧
          Optimization.IsFirstHit (Optimization.arqpStop f P p q (fun _ => ε) x s σ
              (fun _ _ => ε) d)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤
            (Optimization.funEvalCount ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := Chapter12.theorem_12_2_17 (r := p) (by omega) hqp le_rfl
  refine ⟨flow, L, hL, fun ε hε hε2 P hP => ?_⟩
  obtain ⟨f, hb, hf, x, s, σ, d, hrun, -, -, hκ, -, hhit, -⟩ := H ε hε hε2 P hP
  refine ⟨f, hb, hf, x, s, σ, d, hrun, fun k _ _ _ _ => hκ k, hhit, ?_⟩
  simp only [Optimization.funEvalCount, Nat.cast_add, Nat.cast_one]
  linarith [Nat.le_ceil (ε ^ (-((q : ℝ) * (p + 1) / p)))]

/-! ### Sharpness of the ARqp-SC row in the lower-bound mode with a constrained feasible set

The slow example of Theorem 12.2.17 never leaves a half-line, so it is also an ARqp-SC run on a
closed nonconvex `X ⊂ ℝ` (`X ≠ ℝ`), which reaches the "otherwise" entries of the table for
`q ≤ 2`. -/

section ARqpOtherwise

open Optimization

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqp-SC row in the lower-bound
mode of the radius policy (the "otherwise" order `ε^{-q(p+1)/p}`) for every `1 ≤ q ≤ p`, with a
closed nonconvex feasible set `X = (-∞, R] ∪ [R + 2, ∞) ⊂ ℝ`: the slow example of
Theorem 12.2.17 (`r = p`) restricted to `X`. For `1 ≤ q ≤ p` there are `f_low` and `L ≥ 1` such
that for every `ε ∈ (0, ½]` and ARqp constants with `σ₀` the weight (12.2.85) there are `R` and
`f` with f.bB and f.D1pL and an ARqp-SC run on `X` with radii `ε` satisfying the radius hypothesis
of the lower-bound mode of `theorem_14_2_4_arqp` (`δ_{s_k,j} ≥ κ_δ(σ_k) ε_j`) that first
terminates at `k_ε = ⌈ε^{-q(p+1)/p}⌉`, after `k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` evaluations. The run
of Theorem 12.2.17 stays in `(-∞, R]` together with its displacements, so it is a run on `X`.
This covers the "otherwise" entries of the table for `q = 1` (nonconvex `X`) and `q = 2`
(`X ≠ ℝⁿ`), which the reduction to `X = ℝⁿ` does not reach; for `q > 2` it complements
`theorem_14_2_4_sharp_arqp` (`X = ℝ`). -/
theorem theorem_14_2_4_sharp_arqp_otherwise {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ P : ARqpParams,
      P.σ₀ = Chapter12.arqpSigmaSharp p q →
      ∃ (R : ℝ) (f : ℝ → ℝ), (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_2_feasible f ({t | t ≤ R} ∪ {t | R + 2 ≤ t}) P p q
            (fun _ => ε) (fun _ => ε) x s σ (fun _ _ => ε) (fun _ _ => ε) d (fun _ _ => 0) ∧
          (∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d i) →
            ‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 q,
              Optimization.arqpKappaDelta P (Optimization.finMax 1 (fun _ => L) p) (σ k) * ε ≤ ε) ∧
          IsFirstHit (Optimization.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤
            (funEvalCount ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := Chapter12.theorem_12_2_17 (r := p) hq hqp le_rfl
  refine ⟨flow, L, hL, fun ε hε hε2 P hP => ?_⟩
  obtain ⟨f, hb, hf, x, s, σ, d, hrun, -, -, hκ, -, hhit, -⟩ := H ε hε hε2 P hP
  set kε := ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊
  set R : ℝ := ∑ k ∈ Finset.range (kε + 1), (|x k| + |s k|) + 2 with hR
  have hxs : ∀ k ≤ kε, |x k| + |s k| ≤ R - 2 := fun k hk => by
    rw [hR, add_sub_cancel_right]
    exact Finset.single_le_sum (f := fun k => |x k| + |s k|) (fun _ _ => by positivity)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  have hX : ∀ k, (∀ i < k, ¬ Optimization.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d i) →
      x k ∈ {t | t ≤ R} ∪ {t | R + 2 ≤ t} ∧
      (∀ j ∈ Finset.Icc 1 q, x k + d k j ∈ {t | t ≤ R} ∪ {t | R + 2 ≤ t}) ∧
      x k + s k ∈ {t | t ≤ R} ∪ {t | R + 2 ≤ t} ∧
      (‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 q,
        x k + s k + (fun _ _ => (0 : ℝ)) k j ∈ {t | t ≤ R} ∪ {t | R + 2 ≤ t}) := by
    intro k hk
    have hkε : k ≤ kε := not_lt.1 fun hlt => hk kε hlt hhit.1
    have h1 := hxs k hkε
    have hxa := le_abs_self (x k)
    have hsa := le_abs_self (s k)
    have hsa' := abs_nonneg (s k)
    refine ⟨Or.inl (by simp only [mem_ofPred_eq]; linarith), fun j hj => Or.inl ?_,
      Or.inl (by simp only [mem_ofPred_eq]; linarith), fun _ j _ => Or.inl (by
        simp only [mem_ofPred_eq, add_zero]; linarith)⟩
    have hd := (hrun.witness k hk j hj).1.1
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at hd
    have := le_abs_self (d k j)
    simp only [mem_ofPred_eq]
    linarith
  refine ⟨R, f, hb, hf, x, s, σ, d,
    IsARqpRun.of_univ hrun (fun _ _ _ => bddAbove_taylorDecrement _ _ _ _)
    (fun _ _ _ => bddAbove_taylorDecrement _ _ _ _) hX,
    fun k _ _ _ _ => hκ k, hhit, ?_⟩
  simp only [funEvalCount, Nat.cast_add, Nat.cast_one]
  linarith [Nat.le_ceil (ε ^ (-((q : ℝ) * (p + 1) / p)))]

end ARqpOtherwise

/-! ### Sharpness of the dynamic-accuracy rows

The orders of the TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC rows are attained by the
library's slow runs of these methods with exact derivatives (and values)
(`Numlib.Optimization.Complexity.SlowExample.TRqDARun`,
`Numlib.Optimization.Complexity.SlowExample.ARqpDARun`,
`Numlib.Optimization.Complexity.SlowExample.ARqpDASlitRun`), with f.D0qL read as
`LipschitzDerivsAnchored f univ univ 0 q (fun _ => L)` and `L ≥ 1`. -/

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the TRqIDA-SC row: the order
`ε^{-(q+1)}` is attained with the (simple) feasible set `X = ℝ¹` (`univ`) and exact derivatives
(`κ_{∇,i} = 0`, so (13.1.2) asks for zero error). For `q ≥ 1` there are `f_low` and `L ≥ 1` such
that, for every `ε ∈ (0, 1/q!]` (tolerances `ε_j = j! ε`) and all TRqIDA constants with `q`,
`Δ₀ = ϑ = ε` and initial accuracies passing (13.1.9) along steps of length `ε`
(`h_{0,i} ≤ κ_s ε^{q-i+1}`), there is `f` with f.bB and f.D0qL (all `L_{f,j} = L`) and a TRqIDA-SC
run with exact derivatives from `x₀ = 0` whose first `(ε, δ_k)`-approximately optimal iterate is
`x_{k_ε}`, `k_ε = ⌈ε^{-(q+1)}⌉`, after `k_ε + 1 ≥ ε^{-(q+1)} + 1` function evaluations and as
many derivative evaluations. The run follows the slow example of Theorem 12.2.6
(`x_k = k ε e₁`, `Δ_k = ε`, `ρ_k = 1`, no accuracy-improving iteration) up to `k_ε`, and continues
as any run from `x_{k_ε}` (`Optimization.exists_trqDA_run`). This is
`Optimization.exists_isTRqIDARun_slow`. -/
theorem theorem_14_2_4_sharp_trqida {q : ℕ} (hq : 1 ≤ q) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : TRqIDAParams, P.q = q →
      P.Δ₀ = ε → P.ϑ = ε → (∀ i ∈ Finset.Icc 1 q, P.h₀ i ≤ P.κs * ε ^ (q - i + 1)) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0qL f q (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
          (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop),
          IsTRqIDARun f univ (fun _ => 0) P (fun j => j ! * ε) 0 x Δ h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          IsFirstHit (trqIDATest f univ P (fun j => j ! * ε) x Δ) ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (derivEvalCount (fun i => ¬ acc i) ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i))
              ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := exists_isTRqIDARun_slow hq
  refine ⟨flow, L, hL, fun ε hε hεq P hPq hΔ₀ hϑ hh₀ => ?_⟩
  obtain ⟨f, hb, hf, H⟩ := H ε hε hεq P hPq hΔ₀ hϑ hh₀
  exact ⟨f, hb, assumptionD0qL_of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the TRqEDA-SC row: the order
`ε^{-(q+1)}` is attained with the (simple) feasible set `X = ℝ¹` (`univ`) and exact function and
derivative values. For `q ≥ 1` there are `f_low` and `L ≥ 1` such that, for every
`ε ∈ (0, 1/q!]` (tolerances `ε_j = j! ε`) and all TRqEDA constants with `q`, `Δ₀ = ϑ = ε`,
(13.3.5) `κ_s ≤ min(η₁, 1 - η₂)/4` and initial accuracies passing (13.1.9) along steps of
length `ε` and the termination test (13.3.8) at radius `ε`
(`∑_{i=1}^q h_{0,i} ε^i/i! ≤ ½ ς ε ε^q/q!`), there is `f` with f.bB and f.D0qL (all
`L_{f,j} = L`) and a TRqEDA-SC run with exact derivatives and function values from `x₀ = 0`
that first terminates at `k_ε = ⌈ε^{-(q+1)}⌉`, after `2 k_ε ≥ 2 ε^{-(q+1)}` function evaluations
(each value recomputed) and `k_ε + 1 ≥ ε^{-(q+1)} + 1` derivative evaluations. The run is the
slow example of Theorem 12.2.6 with `f` halved (`x_k = k ε e₁`, `Δ_k = ε`, `ρ_k = 1`, no
accuracy-improving iteration), the halving making the test (13.3.7), whose threshold is half
that of TRq, pass exactly at `k_ε`.
This is `Optimization.exists_isTRqEDARun_slow`. -/
theorem theorem_14_2_4_sharp_trqeda {q : ℕ} (hq : 1 ≤ q) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : TRqIDAParams, P.q = q →
      P.Δ₀ = ε → P.ϑ = ε → P.κs ≤ min P.η₁ (1 - P.η₂) / 4 →
      (∀ i ∈ Finset.Icc 1 q, P.h₀ i ≤ P.κs * ε ^ (q - i + 1)) →
      ∑ i ∈ Finset.Icc 1 q, P.h₀ i * ε ^ i / i ! ≤ P.ς * ε * ε ^ q / q ! / 2 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0qL f q (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
          (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
          (R : ℕ → Prop),
          IsTRqEDARun f univ P (fun j => j ! * ε) 0 x Δ h D dd jk s acc fx fxs h₀
            R ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k) ∧ fx k = f (x k) ∧ fxs k = f (x k + s k)) ∧
          IsFirstHit (edaStopTR P (fun j => j ! * ε) D Δ h dd) ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          2 * (ε ^ (q + 1))⁻¹ ≤ (edaFunEvalCount acc R ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
            P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i))
              ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := exists_isTRqEDARun_slow hq
  refine ⟨flow, L, hL, fun ε hε hεq P hPq hΔ₀ hϑ hκs hh₀ hsum => ?_⟩
  obtain ⟨f, hb, hf, H⟩ := H ε hε hεq P hPq hΔ₀ hϑ hκs hh₀ hsum
  exact ⟨f, hb, assumptionD0qL_of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpIDA-SC row for `q ∈ {1, 2}`:
the order `ε^{-(p+1)/(p-q+1)}` of the unit-radii mode is attained with the (simple) feasible set
`X = ℝ¹` (`univ`) and exact derivatives (`κ_{∇,i} = 0`). For `1 ≤ q ≤ min(2, p)` there are
`f_low`, `L ≥ 1` and `ε₀ > 0` such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpIDA
constants with orders `p, q`, `σ₀ = p!/(q-1)!`, unit initial radii and initial accuracies
`0 < h_{0,i} ≤ κ_s (ε/2)^{p-i+1}` (so that (13.1.46) passes along the steps), there is `f` with
f.bB and f.D0pL (all `L_{f,j} = L`) and an ARqpIDA-SC run with exact derivatives from `x₀ = 0`
satisfying the radii control in both modes (`Optimization.ARqpDARadiiControl u` for every `u`
and every `L̄ ≥ 1`: unit radii after every short trial step), whose first iterate that is
`(ε, δ)`-approximately optimal for some radii `δ ∈ (0, 1]^q` (`Optimization.arqpIDATest`) is
`x_{k_ε}`, `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, after `k_ε + 1 ≥ ε^{-(p+1)/(p-q+1)} + 1` function and
derivative evaluations. The run follows the slow example of Theorem 12.2.15 (spike jets
`f^{(q)}(x_k) = -(ε + ω_k)`, steps the global model minimizers, `σ_k = σ₀`, `ρ_k = 1`, no
accuracy-improving iteration) up to `k_ε`, the Step-1 radius of order `q` being halved to the
scale of the step (where (13.1.54) holds), and continues as any run from `x_{k_ε}`
(`Optimization.exists_arqpDA_steps`). For `q = 1` and for `q = p = 2` the order is also
the order `ε^{-q(p+1)/p}` of the lower-bound mode.
This is `Optimization.exists_isARqpIDARun_slow`. -/
theorem theorem_14_2_4_sharp_arqpida {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (p ! : ℝ) / (q - 1)! → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = 1) →
      (∀ i ∈ Finset.Icc 1 p, 0 < P.h₀ i ∧ P.h₀ i ≤ P.κs * (ε / 2) ^ (p - i + 1)) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop),
          IsARqpIDARun f univ (fun _ => 0) P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          (∀ (u : Prop) (Lb : ℝ), 1 ≤ Lb → ∀ k, ARqpDARadiiControl u P
              (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (arqpIDATest f univ P (fun _ => ε) x)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) + 1 ≤ (derivEvalCount (fun i => ¬ acc i)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) ∧
          ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i))
              ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) := by
  obtain ⟨flow, L, ε₀, hL, hε₀, H⟩ := exists_isARqpIDARun_slow hq hq2 hqp
  refine ⟨flow, L, ε₀, hL, hε₀, fun ε hε hεε P hPp hPq hσ hδ₀ hh₀ => ?_⟩
  obtain ⟨f, hb, hf, H⟩ := H ε hε hεε P hPp hPq hσ hδ₀ hh₀
  exact ⟨f, hb, assumptionD0qL_of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpEDA-SC row for `q ∈ {1, 2}`:
the order `ε^{-(p+1)/(p-q+1)}` of the unit-radii mode is attained with the (simple) feasible set
`X = ℝ¹` (`univ`) and exact derivatives and function values. For `1 ≤ q ≤ min(2, p)` there are
`f_low`, `L ≥ 1` and `ε₀ > 0` such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpEDA
constants with orders `p, q`, `σ₀ = p!/(q-1)!`, unit initial radii, (13.3.13)
`κ_s ≤ min(η₁, 1 - η₂)/4`, initial accuracies passing (13.1.46) along the steps
(`h_{0,i} ≤ κ_s (ε/2)^{p-i+1}`) and the termination test (13.3.17) at unit radii
(`∑_{i=1}^j h_{0,i}/i! ≤ ½ ς ε/j!`), there is `f` with f.bB and f.D0pL (all `L_{f,j} = L`) and
an ARqpEDA-SC run with exact derivatives and function values from `x₀ = 0` satisfying the radii
control in both modes (`Optimization.ARqpDARadiiControl u` for every `u` and every `L̄ ≥ 1`), which
first terminates at `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, after `2 k_ε ≥ 2 ε^{-(p+1)/(p-q+1)}` function
evaluations (each value recomputed) and `k_ε + 1 ≥ ε^{-(p+1)/(p-q+1)} + 1` derivative
evaluations. The run is the slow example of Theorem 12.2.15 with `f` halved (spike jets
`f^{(q)}(x_k) = -(ε + ω_k)/2`, steps the global model minimizers, `σ_k = σ₀`, `ρ_k = 1`, no
accuracy-improving iteration, the Step-1 radius of order `q` halved to the scale of the step), the
halving making the test (13.1.53), whose threshold is half that of ARqp, pass exactly at
`k_ε`. For `q = 1` and for `q = p = 2` the order is also the order `ε^{-q(p+1)/p}` of the
lower-bound mode.
This is `Optimization.exists_isARqpEDARun_slow`. -/
theorem theorem_14_2_4_sharp_arqpeda {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (p ! : ℝ) / (q - 1)! → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = 1) →
      P.κs ≤ min P.η₁ (1 - P.η₂) / 4 →
      (∀ i ∈ Finset.Icc 1 p, P.h₀ i ≤ P.κs * (ε / 2) ^ (p - i + 1)) →
      (∀ j ∈ Finset.Icc 1 q, ∑ i ∈ Finset.Icc 1 j, P.h₀ i / i ! ≤ P.ς * ε / j ! / 2) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
          (R : ℕ → Prop),
          IsARqpEDARun f univ P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s acc fx fxs
            h₀ R ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k) ∧ fx k = f (x k) ∧ fxs k = f (x k + s k)) ∧
          (∀ (u : Prop) (Lb : ℝ), 1 ≤ Lb → ∀ k, ARqpDARadiiControl u P
              (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (edaStopAR P (fun _ => ε) D δ₁ h dd)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          2 * ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) ≤ (edaFunEvalCount acc R
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) ∧
          ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) + 1 ≤ (derivEvalCount (fun i => acc i ∨
            (¬ acc i ∧ P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i))
              ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) := by
  obtain ⟨flow, L, ε₀, hL, hε₀, H⟩ := exists_isARqpEDARun_slow hq hq2 hqp
  refine ⟨flow, L, ε₀, hL, hε₀, fun ε hε hεε P hPp hPq hσ hδ₀ hκs hh₀ hsum => ?_⟩
  obtain ⟨f, hb, hf, H⟩ := H ε hε hεε P hPp hPq hσ hδ₀ hκs hh₀ hsum
  exact ⟨f, hb, assumptionD0qL_of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpEDA-SC row in the
lower-bound mode of the radii control (the "otherwise" order `ε^{-q(p+1)/p}`), for every
`1 ≤ q ≤ p`, with the (simple) feasible set `X = ℝ¹` (`univ`) and exact derivatives and function
values. There are `f_low`, `L ≥ 1` and `ε₀ > 0` such that, for every `ε ∈ (0, ε₀]` (all
`ε_j = ε`) and all ARqpEDA constants with orders `p, q`, weight `σ₀ = (3/(p+2))^p/2`, initial
radii `δ₀ = ε`, (13.3.13) `κ_s ≤ min(η₁, 1 - η₂)/4`, initial accuracies passing (13.1.46) along
the steps (`h_{0,i} ≤ κ_s ε^{p-i+1}`) and the termination test (13.3.17) at radius `ε`
(`∑_{i=1}^j h_{0,i} ε^i/i! ≤ ½ ς ε ε^j/j!`), there is `f` with f.bB and f.D0pL (all
`L_{f,j} = L`) and an ARqpEDA-SC run with exact derivatives and function values from `x₀ = 0`
satisfying the radii control in the lower-bound mode (`Optimization.ARqpDARadiiControl False` for
every `L̄ ≥ 1`; all radii are `ε`), which first terminates at `k_ε = ⌈ε^{-q(p+1)/p}⌉`, after
`2 k_ε ≥ 2 ε^{-q(p+1)/p}` function evaluations (each value recomputed) and
`k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` derivative evaluations. The run is the slow example of
Theorem 12.2.17 (with `r = p`) with `f` halved and a smaller weight: gradient spikes
`f'(x_k) = -β_k/2`, `β_k = (ε^q + ω_k)/q!`, steps the global model minimizers, `σ_k = σ₀`,
`ρ_k = 1`, no accuracy-improving iteration, and Step-1 displacements achieving exactly the
fraction `ς` of the measures; the weight is small enough for (13.1.54) to hold at these
displacements (unlike with the weight (12.2.85) of Theorem 12.2.17) and for the measures of the
model at its minimizer to vanish at radius `ε` (Example 12.1.3).
This is `Optimization.exists_isARqpEDARun_slowGrad`. -/
theorem theorem_14_2_4_sharp_arqpeda_otherwise {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (3 / ((p : ℝ) + 2)) ^ p / 2 → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = ε) →
      P.κs ≤ min P.η₁ (1 - P.η₂) / 4 →
      (∀ i ∈ Finset.Icc 1 p, P.h₀ i ≤ P.κs * ε ^ (p - i + 1)) →
      (∀ j ∈ Finset.Icc 1 q, ∑ i ∈ Finset.Icc 1 j, P.h₀ i * ε ^ i / i ! ≤
        P.ς * ε * ε ^ j / j ! / 2) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
          (R : ℕ → Prop),
          IsARqpEDARun f univ P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s acc fx fxs
            h₀ R ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k) ∧ fx k = f (x k) ∧ fxs k = f (x k + s k)) ∧
          (∀ Lb : ℝ, 1 ≤ Lb → ∀ k, ARqpDARadiiControl False P (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (edaStopAR P (fun _ => ε) D δ₁ h dd)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          2 * ε ^ (-((q : ℝ) * (p + 1) / p)) ≤
            (edaFunEvalCount acc R ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤ (derivEvalCount (fun i => acc i ∨
            (¬ acc i ∧ P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i))
              ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  obtain ⟨flow, L, ε₀, hL, hε₀, H⟩ := exists_isARqpEDARun_slowGrad hq hqp
  refine ⟨flow, L, ε₀, hL, hε₀, fun ε hε hεε P hPp hPq hσ hδ₀ hκs hh₀ hsum => ?_⟩
  obtain ⟨f, hb, hf, H⟩ := H ε hε hεε P hPp hPq hσ hδ₀ hκs hh₀ hsum
  exact ⟨f, hb, assumptionD0qL_of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpIDA-SC row in the
lower-bound mode of the radii control for `q = p ≥ 3` (the "otherwise" order `ε^{-q(p+1)/p}`,
here `ε^{-(p+1)}`), with the (simple) feasible set `X = ℝ¹` (`univ`) and exact derivatives. There
are `f_low`, `L ≥ 1` and `ε₀ > 0` such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all
ARqpIDA constants with `q = p`, weight `σ₀ = p`, initial radii `δ₀ = ε` and initial accuracies
`0 < h_{0,i} ≤ κ_s ε^{p-i+1}`, there is `f` with f.bB and f.D0pL (all `L_{f,j} = L`) and an
ARqpIDA-SC run with exact derivatives from `x₀ = 0` satisfying the radii control in the lower-bound
mode (`Optimization.ARqpDARadiiControl False`), whose first iterate that is `(ε, δ)`-approximately
optimal for some radii `δ ∈ (0, 1]^q` (`Optimization.arqpIDATest`) is `x_{k_ε}`,
`k_ε = ⌈ε^{-(p+1)}⌉`, after `k_ε + 1 ≥ ε^{-(p+1)} + 1` function and derivative evaluations. The
run follows the slow example of Theorem 12.2.15 with `q = p` (pure `p`-th order spikes
`f^{(p)}(x_k) = -(ε + ω_k)`, which fail the criterion at every radius; steps the global model
minimizers `t*_k = ε + ω_k`, `σ_k = σ₀`, `ρ_k = 1`) with Step-2 radii `δ_{s_k} = ε/p`, at which the
model measures at its minimizer vanish (`Optimization.taylorMeasure_topMonomialRegModel_eq_zero`),
and continues after `k_ε` as any ARqpIDA iteration from the state at `k_ε`
(`Optimization.exists_arqpDA_steps`).
This is `Optimization.exists_isARqpIDARun_slowTop`. -/
theorem theorem_14_2_4_sharp_arqpida_otherwise {p : ℕ} (hp : 3 ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = p → P.σ₀ = p → (∀ j ∈ Finset.Icc 1 p, P.δ₀ j = ε) →
      (∀ i ∈ Finset.Icc 1 p, 0 < P.h₀ i ∧ P.h₀ i ≤ P.κs * ε ^ (p - i + 1)) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop),
          IsARqpIDARun f univ (fun _ => 0) P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          (∀ k, ARqpDARadiiControl False P (fun _ => ε)
            (lipMax (fun _ => L) P.p + ordMax P.p (fun _ => 0) * P.κh) σ δs s acc k) ∧
          IsFirstHit (arqpIDATest f univ P (fun _ => ε) x) ⌈(ε ^ (p + 1))⁻¹⌉₊ ∧
          (ε ^ (p + 1))⁻¹ + 1 ≤ (derivEvalCount (fun i => ¬ acc i) ⌈(ε ^ (p + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (p + 1))⁻¹ + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i))
              ⌈(ε ^ (p + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨flow, L, ε₀, hL, hε₀, H⟩ := exists_isARqpIDARun_slowTop hp
  refine ⟨flow, L, ε₀, hL, hε₀, fun ε hε hεε P hPp hPq hσ hδ₀ hh₀ => ?_⟩
  obtain ⟨f, hb, hf, H⟩ := H ε hε hεε P hPp hPq hσ hδ₀ hh₀
  exact ⟨f, hb, assumptionD0qL_of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpIDA-SC row in the
lower-bound mode of the radii control (the "otherwise" order `ε^{-q(p+1)/p}`) for every
`1 ≤ q ≤ p`, with a closed nonconvex feasible set in `ℝ²` and exact derivatives. There are
`f_low`, `L ≥ 1` and `ε₀ > 0` such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpIDA
constants with orders `p, q`, weight `σ₀ = (3/(p+2))^p`, initial radii `δ₀ = ε` and initial
accuracies `h_{0,i} ≤ κ_s ε^{p-i+1}`, there are `ρ ∈ (ε, 2ε]`, the feasible set
`X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1}` (`v 1` is the second coordinate; a line and a parallel
half-plane at distance `ρ`), `f` with f.bB and f.D0pL (all `L_{f,j} = L`) and an ARqpIDA-SC run
on `X` with exact derivatives from `x₀ = 0` satisfying the radii control in the lower-bound mode
(`Optimization.ARqpDARadiiControl False` for every `L̄ ≥ 1`; all radii are `ε`), whose first
iterate that is `(ε, δ)`-approximately optimal on `X` for some radii `δ ∈ (0, 1]^q`
(`Optimization.arqpIDATest`) is `x_{k_ε}`, `k_ε = ⌈ε^{-q(p+1)/p}⌉`, after
`k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` function and derivative evaluations.

The run follows the slow example of Theorem 12.2.17 (`r = p`) on the line `v 1 = 0`:
`f(v) = G(v 0) + H(v 1)` with gradient spikes `G'(x_k) = -β_k`,
`β_k = (ε^q + ε^q (k_ε - k)/k_ε)/q!`, steps the minimizers of the model on the line (admissible
Step-2 steps, since (13.1.55)–(13.1.57) are local conditions, but not global minimizers of the
model on `X`, which are in the half-plane), `σ_k = σ₀`, `ρ_k = 1`, and `H'(0) = -1`, so that the
half-plane lowers the Taylor models by at least `ρ > ε`. Radii `δ < ρ` only see the line, where
the measure of order `q` is `β_k δ`; with `ρ^n = ε^n (1 + 1/k_ε)`, `n = max(q - 1, 1)`, this
exceeds `ε δ^q/q!` for every `δ < ρ` exactly when `k < k_ε`, and radii `δ ≥ ρ` reach the
half-plane. So the criterion fails at every radius before `k_ε`, while the Step-1 and Step-2 radii
`ε < ρ` only see the line, where the model measures at the steps vanish (Example 12.1.3). After
`k_ε` one more step reaches a point where all derivatives of `G` vanish, and the run continues with
accuracy-improving iterations there. For `q = 1` this is the "otherwise" entry with a nonconvex
`X` (its order `ε^{-(p+1)/p}` coincides with that of the convex entry). The cases `q = 2 < p`
(with `X ≠ ℝⁿ`) and `3 ≤ q < p` are not reached by the book's reduction to unconstrained
problems: on `ℝⁿ` the order is not attained for `q = 2 < p` (`theorem_14_2_4_arqpida_le_two`), and
for `3 ≤ q < p` the case `X = ℝⁿ` is open (see the module doc).
This is `Optimization.exists_isARqpIDARun_slit`. -/
theorem theorem_14_2_4_sharp_arqpida_otherwise_constrained {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (3 / ((p : ℝ) + 2)) ^ p → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = ε) →
      (∀ i ∈ Finset.Icc 1 p, P.h₀ i ≤ P.κs * ε ^ (p - i + 1)) →
      ∃ (ρ : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
        ε < ρ ∧ ρ ≤ 2 * ε ∧ X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1} ∧ IsClosed X ∧
        (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 2)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 2)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 2)) (acc : ℕ → Prop),
          IsARqpIDARun f X (fun _ => 0) P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          (∀ Lb : ℝ, 1 ≤ Lb → ∀ k, ARqpDARadiiControl False P (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (arqpIDATest f X P (fun _ => ε) x)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤
            (derivEvalCount (fun i => ¬ acc i) ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i))
              ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  obtain ⟨flow, L, ε₀, hL, hε₀, H⟩ := exists_isARqpIDARun_slit hq hqp
  refine ⟨flow, L, ε₀, hL, hε₀, fun ε hε hεε P hPp hPq hσ hδ₀ hh₀ => ?_⟩
  obtain ⟨ρ, X, f, hρ, hρ2, hX, hXc, hb, hf, H⟩ := H ε hε hεε P hPp hPq hσ hδ₀ hh₀
  exact ⟨ρ, X, f, hρ, hρ2, hX, hXc, hb, assumptionD0qL_of_lipschitzDerivsAnchored hf hL, H⟩

end Sharp

section TRqPrintedFalse

open scoped ContDiff
open Optimization

set_option hygiene false in
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ### Coordinates of `ℝ²` and the half square, as used in §14.3 -/

/-- `‖s‖² = s₁² + s₂²` on `ℝ²`. -/
theorem trqLog_norm_sq (s : ℝ²) : ‖s‖ ^ 2 = (s 0) ^ 2 + (s 1) ^ 2 :=
  EuclideanSpace.norm_sq_eq_fin_two s

/-- The coordinates are continuous. -/
theorem trqLog_continuous_coord (i : Fin 2) : Continuous (fun v : ℝ² => v i) :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).continuous

/-- `t ↦ t²/2` (`Optimization.halfSq`). -/
noncomputable def trqSadSq : ℝ → ℝ := fun t => t ^ 2 / 2

/-- `(t²/2)' = t`. -/
theorem iteratedDeriv_trqSadSq_one (t : ℝ) : iteratedDeriv 1 trqSadSq t = t :=
  iteratedDeriv_halfSq_one t

/-- `(t²/2)'' = 1`. -/
theorem iteratedDeriv_trqSadSq_two (t : ℝ) : iteratedDeriv 2 trqSadSq t = 1 :=
  iteratedDeriv_halfSq_two t

/-- `t ↦ t²/2` is smooth. -/
theorem contDiff_trqSadSq : ContDiff ℝ ∞ trqSadSq := contDiff_halfSq

/-- `w ↦ w_i²/2` is smooth. -/
theorem trqSad_contDiff_coordSq (i : Fin 2) : ContDiff ℝ ∞ (fun w : ℝ² => trqSadSq (w i)) :=
  contDiff_halfSq_comp_apply i

/-! ### The TRq-SC row `j + 1` of (14.2.12) fails per iteration with uniform constants (`q = 2`)

The example is the backbone `Numlib.Optimization.Complexity.SlowExample.TRqSaddle`. -/

/-- The objective `f_a(x) = x_1²/2 - a x_2²/2` of the example (`Optimization.saddleQuad`). -/
noncomputable abbrev trqSadF (a : ℝ) : ℝ² → ℝ := saddleQuad a

/-- The box `X = [-1, 1]²` of the example (`Optimization.saddleBox`). -/
abbrev trqSadX : Set ℝ² := saddleBox

/-- The trust-region parameters of the example (`Optimization.saddleTRqParams`): `Δ₀ = Δ_max = 1`,
`η₁ = 1/4`, `η₂ = 3/4`, `γ₁ = 1/4`, `γ₂ = 1/2`, `γ₃ = 2`, `ς = 1/2`. -/
noncomputable abbrev trqSadP : Optimization.TRqParams := saddleTRqParams

/-- f.D1qLaB.X (`q = 2`) for `f_a` with `a ∈ [0, 1]`, on `X₀` the ball of radius `2`, with the
constants `L_j = B_j = 4` independent of `a` and of the anchor. -/
theorem trqSadF_assumption {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (x₀ : ℝ²) :
    AssumptionD1qLaBX (trqSadF a) trqSadX (ball 0 2) x₀ 1 2 (fun _ => 4) (fun _ => 4) :=
  AssumptionD1qLaBX.of_lipschitzOn isOpen_ball (convex_ball 0 2) saddleBox_subset_ball
    (fun y _ => (contDiffAt_saddleQuad a 2 y).contDiffWithinAt)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ hj => iteratedFDerivLipschitzOn_saddleQuad ha0 ha1 hj)
    (fun _ hj _ hx => norm_iteratedFDeriv_saddleQuad_le_four ha0 ha1 hj hx)

/-- **(14.2.11) with the printed TRq-SC exponents `π_j = j + 1` is false for `q = 2` with `κ_decr`
depending only on the algorithm parameters, `ϑ` and the f.D1qLaB.X constants**
([cartis2022evaluation], Lemma 14.2.2, (14.2.12); the dependence of the explicit `κ_decr` of Lemma
12.2.4 / (12.2.14)). The objective varies with `κ` within a family with uniform constants; a single
fixed `f` is not treated here. For the TRq parameters `trqSadP`,
the threshold `ϑ = 1`, the box `X = [-1, 1]²` and every `κ > 0` there are `a ∈ (0, 1]` (the
objective `f_a(x) = x_1²/2 - a x_2²/2`, which satisfies f.D1qLaB.X with constants `4` independent of
`a`), tolerances `ε ∈ (0, 1]²` and a TRq-SC run with a successful iteration `k` before termination
that decreases `f_a` by less than `κ min_j ε_j^{j+1}`. With `r = 2^{-N}`, `ε_1 = r²`, `ε_2 = a = r`:
`N` unsuccessful first-order iterations at `(r², 0)` shrink the radius from `1` to `r²`, a
successful step reaches `0`, where the gradient vanishes and the second-order test fails, and the
second-order step `r² e_2` decreases `f_a` by `r⁵/2`, against `κ min(ε_1², ε_2³) = κ r⁴`. The radius
is shared across the orders and is driven down by the first-order failures; the decrease proved in
Lemma 12.2.4 is `κ ε_min^{q+1}` (`Chapter14.lemma_14_2_2_trq`). The run is
`Optimization.exists_isTRqRun_saddleQuad_decrease_lt`. -/
theorem lemma_14_2_2_trq_printed_false {κ : ℝ} (hκ : 0 < κ) :
    ∃ (a : ℝ) (ε : ℕ → ℝ) (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²) (k : ℕ),
      0 < a ∧ a ≤ 1 ∧ (∀ j ∈ Finset.Icc 1 2, ε j ∈ Ioc 0 1) ∧ x 0 ∈ trqSadX ∧
      AssumptionD1qLaBX (trqSadF a) trqSadX (ball 0 2) (x 0) 1 2 (fun _ => 4) (fun _ => 4) ∧
      Chapter12.algorithm_12_2_1_feasible (trqSadF a) trqSadX trqSadP 2 ε 1 x s Δ jk d ∧
      (∀ i ≤ k, ¬ Chapter12.trqStop (trqSadF a) trqSadP 2 ε 1 x Δ d i) ∧
      trqSadP.η₁ ≤ Chapter12.trqRho (trqSadF a) x s jk k ∧
      trqSadF a (x k) - trqSadF a (x (k + 1)) < κ * Optimization.finMin 1 (fun j => ε j ^ (j + 1)) 2
          := by
  obtain ⟨a, ε, x, s, Δ, jk, d, k, ha0, ha1, hε, hx0, hrun, hns, hρ, hlt⟩ :=
    exists_isTRqRun_saddleQuad_decrease_lt hκ
  exact ⟨a, ε, x, s, Δ, jk, d, k, ha0, ha1, hε, hx0, trqSadF_assumption ha0.le ha1 (x 0), hrun,
    hns, hρ, hlt⟩

/-- **No uniform `κ_decr` for the TRq-SC row `j + 1`** ([cartis2022evaluation], (14.2.11)–(14.2.12),
`q = 2`): there is no `κ > 0` such that, for every `a ∈ (0, 1]`, every TRq-SC run (parameters
`trqSadP`, `ϑ = 1`, `X = [-1, 1]²`) on `f_a` satisfying f.D1qLaB.X with the constants `4`, every
`ε ∈ (0, 1]²` and every successful iteration `k` before termination,
`f_a(x_k) - f_a(x_{k+1}) ≥ κ min_j ε_j^{j+1}` (`lemma_14_2_2_trq_printed_false`). -/
theorem lemma_14_2_2_trq_printed_false_uniform :
    ¬ ∃ κ : ℝ, 0 < κ ∧ ∀ (a : ℝ) (ε : ℕ → ℝ) (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ)
      (d : ℕ → ℕ → ℝ²) (k : ℕ), 0 < a → a ≤ 1 → (∀ j ∈ Finset.Icc 1 2, ε j ∈ Ioc 0 1) →
      AssumptionD1qLaBX (trqSadF a) trqSadX (ball 0 2) (x 0) 1 2 (fun _ => 4) (fun _ => 4) →
      Chapter12.algorithm_12_2_1_feasible (trqSadF a) trqSadX trqSadP 2 ε 1 x s Δ jk d →
      (∀ i ≤ k, ¬ Chapter12.trqStop (trqSadF a) trqSadP 2 ε 1 x Δ d i) →
      trqSadP.η₁ ≤ Chapter12.trqRho (trqSadF a) x s jk k →
      κ * Optimization.finMin 1 (fun j => ε j ^ (j + 1)) 2 ≤
        trqSadF a (x k) - trqSadF a (x (k + 1)) := by
  rintro ⟨κ, hκ, H⟩
  obtain ⟨a, ε, x, s, Δ, jk, d, k, ha0, ha1, hε, -, hA, hrun, hns, hsucc, hlt⟩ :=
    lemma_14_2_2_trq_printed_false hκ
  exact absurd (H a ε x s Δ jk d k ha0 ha1 hε hA hrun hns hsucc) (not_le.2 hlt)

end TRqPrintedFalse

end CartisGouldToint.Chapter14
