/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# Cartis, Gould and Toint, Section 14.2: Problems with simple constraints

This module formalizes Section 14.2 of [cartis2022evaluation]: the minimization of a smooth function
$f$ over a closed nonempty set $X \subseteq \mathbb{R}^n$ (14.2.1) whose constraints are simple,
that is, can be handled without evaluations of $f$. For $x \in X$ let $X(x)$ be the set of feasible
displacements $d$, those with $x + d \in X$. The constrained measure (14.2.2) of order $j$ at radius
$\delta$ is $$\phi^\delta_{f,X(x),j}(x) = \sup \{\Delta T_{f,j}(x, d) : d \in X(x),\ \|d\| \le
\delta\},$$ the largest decrease of the Taylor polynomial of degree $j$ of $f$ at $x$ over the
feasible displacements of length at most $\delta$. A point $x$ is an
$(\epsilon, \delta)$-approximate $q$-th order minimizer on $X$ if $\phi^{\delta_j}_{f,X(x),j}(x) \le
\epsilon_j \delta_j^j / j!$ for every $j \in [1:q]$. Theorem 14.2.1 shows that such a point is
approximately optimal in a feasible neighbourhood. Section 14.2.1 then analyses the variants with
simple constraints ("-SC") of the methods ARqpC, TRq, ARqp, TRqIDA, TRqEDA, ARqpIDA and ARqpEDA.
Lemma 14.2.2 gives the decrease $f(x_k) - f(x_{k+1}) \ge \kappa_{\mathrm{decr}} \min_j
\epsilon_j^{\pi_j}$ (14.2.11) on successful iterations, with the exponents $\pi_j$ of each method in
the table (14.2.12). Lemma 14.2.3 gives $k \le \kappa_{\mathrm{uns}} |\mathcal{S}_k| +
\kappa_{\mathrm{unc}}$ (14.2.13), and Theorem 14.2.4 gives the evaluation complexity
$O(\max_j \epsilon_j^{-\pi_j})$ and states that these orders are sharp. Section 14.2.2 treats
sparsity constraints $\|x\|_0 \le n_{\mathrm{nz}}$, for which the first-order measure is the value
of a knapsack problem (Lemma 14.2.5).

The proofs specialize the analyses of the runs with a feasible set in
`Numlib.Optimization.ModelBased.HighOrder.TRqComplexity`,
`Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity` and
`Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqIDA` and its companions, the stability
result of `Numlib.Optimization.Optimality.TaylorStability`, the sparse linear subproblem of
`Numlib.Optimization.Subproblem.SparseLinear`, and the slow examples of
`Numlib.Optimization.Complexity.SlowExample.TRqDARun`,
`Numlib.Optimization.Complexity.SlowExample.ARqpDARun`,
`Numlib.Optimization.Complexity.SlowExample.ARqpDASlitRun` and
`Numlib.Optimization.Complexity.SlowExample.TRqSaddle`.

## Main definitions

* Assumption X.CNe, `CartisGouldToint.Chapter14.AssumptionXCNe`: $X$ is closed and nonempty.
* Equation (14.2.8), `CartisGouldToint.Chapter14.sublevel`: the sublevel set $\mathcal{L}_f(x_0) =
  \{x \in X : f(x) \le f(x_0)\}$.
* Assumptions f.D1qLaB.X and f.D1pLaB.X, `CartisGouldToint.Chapter14.AssumptionD1qLaBX`: the
  derivatives of orders $j_0$ to $q$ satisfy the anchored Lipschitz condition (14.2.9) and the
  bounds (14.2.10) at the points of $\mathcal{L}_f(x_0)$.
* Assumptions f.D0qLaB.X and f.D0pLaB.X, `CartisGouldToint.Chapter14.AssumptionD0qLaBX`: the same
  with (14.2.9) for the orders $0$ to $q$.
* Assumption f.bB.X, `CartisGouldToint.Chapter14.AssumptionBbX`: $f$ is bounded below on $X$.
* Lemma 14.2.2, TRq-SC row, `CartisGouldToint.Chapter14.trqSadF`,
  `CartisGouldToint.Chapter14.trqSadX`, `CartisGouldToint.Chapter14.trqSadP`: the objective
  $f_a(x) = x_1^2/2 - a x_2^2/2$, the box $[-1, 1]^2$ and the trust-region parameters of the
  counterexample to an alternative order-dependent exponent.

## Main results

* Theorem 14.2.1, `CartisGouldToint.Chapter14.theorem_14_2_1`: an approximate minimizer on $X$ is
  approximately optimal on a feasible neighbourhood.
* Remark after (14.2.10), `CartisGouldToint.Chapter14.AssumptionD1qLaBX.of_lipschitzOn`: Lipschitz
  continuous and bounded derivatives on $X_0$ give f.D1qLaB.X.
* Lemma 14.2.2, ARqpC-SC row, `CartisGouldToint.Chapter14.lemma_14_2_2_arqpc`,
  `CartisGouldToint.Chapter14.lemma_14_2_2_arqpc_anchored`: a successful iteration decreases
  $w = f + h \circ c$ by $\eta_1 \kappa_{\Delta m} \epsilon_j^{j+1}$ for some $j$.
* Lemma 14.2.2, TRq-SC row, `CartisGouldToint.Chapter14.lemma_14_2_2_trq`,
  `CartisGouldToint.Chapter14.lemma_14_2_2_trq_anchored`: a successful iteration decreases $f$ by a
  multiple of $\epsilon_{\min}^{q+1}$.
* `CartisGouldToint.Chapter14.lemma_14_2_2_trq_printed_false`,
  `CartisGouldToint.Chapter14.lemma_14_2_2_trq_printed_false_uniform`: the alternative exponents
  $\pi_j = j + 1$ fail for $q = 2$ with uniform constants.
* Lemma 14.2.2, ARqp-SC row, `CartisGouldToint.Chapter14.lemma_14_2_2_arqp`,
  `CartisGouldToint.Chapter14.lemma_14_2_2_arqp_anchored`: the decrease $\eta_1 \kappa_{\Delta m}
  \min_j \epsilon_j^{\pi_j}$ in either radii mode.
* Lemma 14.2.2, dynamic-accuracy rows, `CartisGouldToint.Chapter14.lemma_14_2_2_trqida`,
  `CartisGouldToint.Chapter14.lemma_14_2_2_trqeda`,
  `CartisGouldToint.Chapter14.lemma_14_2_2_arqpida`,
  `CartisGouldToint.Chapter14.lemma_14_2_2_arqpeda` and their `_anchored` forms: the decreases of
  TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC.
* Lemma 14.2.3, `CartisGouldToint.Chapter14.lemma_14_2_3_arqpc`,
  `CartisGouldToint.Chapter14.lemma_14_2_3_trq`, `CartisGouldToint.Chapter14.lemma_14_2_3`,
  `CartisGouldToint.Chapter14.lemma_14_2_3_trqida`,
  `CartisGouldToint.Chapter14.lemma_14_2_3_trqeda`,
  `CartisGouldToint.Chapter14.lemma_14_2_3_arqpida`,
  `CartisGouldToint.Chapter14.lemma_14_2_3_arqpeda` and their `_anchored` forms: the bound (14.2.13)
  on the number of iterations for each row.
* Theorem 14.2.4, `CartisGouldToint.Chapter14.theorem_14_2_4_arqpc`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_arqpc_convex`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_trq`, `CartisGouldToint.Chapter14.theorem_14_2_4_arqp`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_trqida`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_trqeda`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_arqpida`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_arqpeda` and their `_anchored` forms: termination at an
  approximate minimizer on $X$ within the evaluation bounds of each row.
* Theorem 14.2.4, ARqpIDA-SC row, `CartisGouldToint.Chapter14.theorem_14_2_4_arqpida_le_two`: on
  $\mathbb{R}^n$ with $q \le 2$, every ARqpIDA run satisfies the bound of the unit-radii mode.
* Theorem 14.2.4, sharpness, `CartisGouldToint.Chapter14.theorem_14_2_4_sharp`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqp`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqp_otherwise`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_trqida`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_trqeda`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpeda`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpeda_otherwise`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida_otherwise`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida_otherwise_constrained`: the orders of the
  table are attained by slow examples.
* Equations (14.2.17)–(14.2.18), `CartisGouldToint.Chapter14.sparseMeasure_eq`: the sparse
  first-order measure is attained at the step of an optimal knapsack selection.
* Lemma 14.2.5, `CartisGouldToint.Chapter14.lemma_14_2_5`: the step (14.2.20) of an optimal knapsack
  selection minimizes the linear function over the sparse feasible displacements.

## Proof outline

Each row of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4 is the analysis of the corresponding method of
Chapters 12–14.1, run with steps and displacements restricted to $X(x_k)$. For the sharpness of the
orders the source argues that unconstrained problems are a special case of simply constrained ones.
The slow examples of Chapters 12–14.1 are therefore run with $X = \mathbb{R}$ or $X = \mathbb{R}^1$.
This argument does not reach the "otherwise" entries of the table with $q \le 2$ ($q = 2$ with
$X \neq \mathbb{R}^n$, and $q = 1$ with $X$ nonconvex). These entries are attained on closed
nonconvex feasible sets: the slow example of Theorem 12.2.17 stays in a half-line, and an extra
coordinate with a parallel half-plane makes the criterion of ARqpIDA fail at the large radii.

## Conventions

* The methods with simple constraints are runs with a feasible set $X$: TRq-SC is
  `CartisGouldToint.Chapter12.algorithm_12_2_1_feasible`, ARqp-SC is
  `CartisGouldToint.Chapter12.algorithm_12_2_2_feasible`, ARqpC-SC is
  `CartisGouldToint.Chapter14.algorithm_14_1_1`, and TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC
  are `Optimization.IsTRqIDARun`, `Optimization.IsTRqEDARun`, `Optimization.IsARqpIDARun` and
  `Optimization.IsARqpEDARun`. The feasible set `univ` gives the methods of Chapters 12–14.1.
* The feasible displacements $X(x)$ are the set `{d | x + d ∈ X}`, and the measure (14.2.2) is
  `Optimization.taylorMeasure (ftaylorSeries ℝ f x) j δ` of this set.
* $\epsilon_{\min} = \min_{j \in [1:q]} \epsilon_j$ is `Optimization.finMin 1 ε q` or
  `Optimization.epsMin q ε`. For $\epsilon_j \le 1$ the two agree.
* f.D1qL on an open convex set $C \supseteq X$ is `LipschitzDerivsAnchored f C C 1 q L`, and f.D0qL
  on $C$ is `LipschitzDerivsAnchored f C C 0 q L`. The anchored assumptions of the source use the
  anchor set $\mathcal{L}_f(x_0)$ in place of the first $C$.
* The regularization methods have two radii modes, selected by a proposition $u$. If $u$ holds, the
  radii after a short step are $1$ and $\pi_j = (p+1)/(p-j+1)$. If $u$ fails, the radii satisfy a
  lower bound of the type (12.2.51) at every order and $\pi_j = j(p+1)/p$. The exponents are
  `Optimization.arqpPiOf u p j` and `Optimization.arPiOf u p j`. The source associates unit radii
  with $q = 1$ and convex $X$, or with $q = 2$ and $X = \mathbb{R}^n$.
* TRqIDA-SC and ARqpIDA-SC have no termination rule. For them, "before termination" means "before
  the first iterate that is approximately optimal on $X$".
* The evaluation counts are `Optimization.funEvalCount` (one value at $x_0$ and one per iteration),
  `Optimization.derivEvalCount` (one evaluation at $x_0$ and one per iteration of the given kind)
  and `Optimization.edaFunEvalCount` (inexact values of the EDA methods).

## Implementation notes

* Each row is stated twice: under smoothness on an open convex set $C \supseteq X$ (or on all of
  $\mathbb{R}^n$ for ARqpC-SC), and, in the declarations with the suffix `_anchored`, under the
  anchored assumption of the source with the starting point as anchor. The rows under f.D0qL on
  $C \supseteq X$ are the instance of the anchored analysis with anchor set $C$.
* The anchor is the plain sublevel set $\mathcal{L}_f(x_0)$ for all methods, because the objective
  does not increase along the runs (`Optimization.IsTRqIDARun.objective_le`, …,
  `Optimization.IsARqpEDARun.objective_le`). This also holds for the EDA methods with inexact
  values: (13.3.5) and (13.3.13) give $\kappa_s \le \eta_1/4$, and
  $h_{k,0} \le \kappa_s \overline{\Delta T}_k$ then gives a true decrease of at least
  $\eta_1 \overline{\Delta T}_k / 2 > 0$ on successful iterations.
* The bound (14.2.10) is not used by the anchored analyses: the bounds on the jets at the anchors
  follow from (14.2.9) at the interior points of $X_0$
  (`LipschitzDerivsAnchored.norm_iteratedFDeriv_le_finMax`).
* The ARqpC-SC statements of Section 14.1 already carry a general feasible set $X$; the ARqpC-SC
  rows here add $x_{k_\epsilon} \in X$.
* The sparse results are stated on `Fin n → ℝ` with the sup norm, so that the ball of radius
  $\delta$ is the $\ell_\infty$ ball of the source.
* The slow runs of the dynamic-accuracy methods are the backbone runs
  `Optimization.exists_isTRqIDARun_slow`, `Optimization.exists_isTRqEDARun_slow`,
  `Optimization.exists_isARqpIDARun_slow`, `Optimization.exists_isARqpEDARun_slow`,
  `Optimization.exists_isARqpEDARun_slowGrad`, `Optimization.exists_isARqpIDARun_slowTop` and
  `Optimization.exists_isARqpIDARun_slit`. They are runs of the Chapter 13 run predicates with exact
  derivatives (and values), with class constants independent of $\epsilon$.

## Deviations from the source

* **Theorem 14.2.1** (generalization). The Lipschitz condition is required only on the closed ball
  of radius $\delta_j$ around $x_\epsilon$, which the printed open ball of a larger radius implies,
  and $X$ closed and nonempty, $\delta_j \le 1$ and $\epsilon_j \le 1$ are not needed. See
  `CartisGouldToint.Chapter14.theorem_14_2_1`.
* **Theorem 14.2.1, (14.2.6)** (typo). The printed $\delta^j$ is $\delta_j^j$. See
  `CartisGouldToint.Chapter14.theorem_14_2_1`.
* **Theorem 14.2.1, radius condition** (reading). The condition
  $\|d\| \le (j+1)\epsilon_j / L_{f,j}$ is used in the form $L_{f,j} \|d\| \le (j+1)\epsilon_j$. See
  `CartisGouldToint.Chapter14.theorem_14_2_1`.
* **(14.2.18)–(14.2.19)** (typo). The source prints $\max \ell(d)$; the measure (14.2.17) and Lemma
  14.2.5 need the minimum of $\ell(d) = \langle \nabla f(x), d \rangle$. See
  `CartisGouldToint.Chapter14.sparseMeasure_eq`.
* **Lemma 14.2.5** (generalization). The hypothesis $\|x\|_0 \le n_{\mathrm{nz}}$ is not needed. See
  `CartisGouldToint.Chapter14.lemma_14_2_5`.
* **Lemma 14.2.2, TRq-SC row of (14.2.12)** (OCR discrepancy). The original PDF and the Lean
  TR rows all use $\pi_j = q + 1$. The OCR reading $\pi_j = j + 1$ is false per iteration
  for $q = 2$ with a constant depending only on the algorithm and f.D1qLaB.X constants. See
  `CartisGouldToint.Chapter14.lemma_14_2_2_trq_printed_false_uniform`.
* **Equation (14.2.4)** (correction). The model criticality test measures reduction from the
  value of the model at the trial step, $m_k(s)$. The display in the source subtracts from $f(x)$.
* **Lemma 14.2.2, ARqpC-SC row** (reading). The statement for general radii uses the composite
  objective decrease and requires a successful step followed by a failed Step-1 test. The
  convex first-order complexity statement uses a unit initial radius.
* **Lemma 14.2.2, ARqpIDA-SC row** (correction). The decrease holds at the successful iterations
  that are followed by an iterate that is not approximately optimal, as in the correction of Lemma
  13.1.18. See `CartisGouldToint.Chapter14.lemma_14_2_2_arqpida`.
* **Lemma 14.2.2, ARqpEDA-SC row** (correction). The decrease needs $\theta < \varsigma/2$ and holds
  at the successful iterations of Lemma 13.3.7, as in the correction of that lemma. See
  `CartisGouldToint.Chapter14.lemma_14_2_2_arqpeda`.
* **Lemma 14.2.3** (reading). The constants are explicit: $\kappa_{\mathrm{unc}}$ contains
  $|\log \epsilon_{\min}|$ terms, because the radius lower bound of the TR methods is proportional
  to $\epsilon_{\min}$ and the number of accuracy-improving iterations of the IDA and EDA methods is
  logarithmic in $\epsilon_{\min}$. For the IDA methods the bound holds up to the first
  approximately optimal iterate. See `CartisGouldToint.Chapter14.lemma_14_2_3_trq` and
  `CartisGouldToint.Chapter14.lemma_14_2_3_trqida`.
* **Lemma 14.2.2 and Theorem 14.2.4, ARqp-SC rows** (reading). The rows are stated by radii mode
  $u$, while the table keys them by $(q, X)$. The mode in which $u$ fails gives the "otherwise"
  entries $j(p+1)/p$ for every $q$ and $X$, and the unit-radii entries $(p+1)/(p-j+1)$ hold under
  the hypothesis that the radii are $1$. See `CartisGouldToint.Chapter14.lemma_14_2_2_arqp`.
* **Lemma 14.2.2 and Theorem 14.2.4, ARqpIDA-SC and ARqpEDA-SC rows** (reading). The rows are stated
  by the mode of the radii control `Optimization.ARqpDARadiiControl`, while the table keys them by
  $(q, X)$. On $\mathbb{R}^n$ with $q \le 2$ every ARqpIDA run satisfies the unit-radii bound in
  either mode, so the bound of the other mode is not sharp there for $q = 2 < p$. See
  `CartisGouldToint.Chapter14.theorem_14_2_4_arqpida_le_two`.
* **Theorem 14.2.4, sharpness of the TRqIDA-SC and TRqEDA-SC rows** (reading). The slow example of
  Theorem 12.2.6 is a run of these methods only for suitable constants:
  $\vartheta = \Delta_0 = \epsilon$, initial accuracies that pass (13.1.9) along the steps, and for
  TRqEDA the test (13.3.8) at radius $\epsilon$; TRqEDA is run on $f/2$. See
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_trqida` and
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_trqeda`.
* **Theorem 14.2.4, sharpness of the ARqpIDA-SC and ARqpEDA-SC rows** (reading). The slow runs of
  Chapter 12 are not runs of the regularization steps of Chapter 13, so the data are adapted:
  smaller Step-1 radii or weights, $f/2$ for ARqpEDA, and initial accuracies that pass (13.1.46) and
  (13.3.17). See `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpeda`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpeda_otherwise`,
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida_otherwise` and
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida_otherwise_constrained`.

## Not formalized

* **Key Definition after Theorem 14.2.1 (simple constraints).** It is a convention on the cost of
  the oracles (solving (14.2.2) and ensuring (14.2.5) costs no evaluation of $f$), not a
  mathematical property: the feasible set enters the run predicates only through the measures and
  the feasibility of the iterates, and the evaluation counts never charge the subproblems.
* **Theorem 14.2.4, sharpness of the "otherwise" entry of the ARqpC-SC row.** Section 14.1 leaves
  sharpness of (14.1.36)–(14.1.37) open. The convex first-order case is Corollary 14.1.11.
* **Theorem 14.2.4, sharpness of the "otherwise" entry of the ARqpIDA-SC row on $X = \mathbb{R}^n$
  for $3 \le q < p$.** The claim of the table for this entry is met with a feasible set
  $X \neq \mathbb{R}^n$
  (`CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida_otherwise_constrained`), but the
  source's reduction to $X = \mathbb{R}^n$ would also need this case. The example of Theorem 12.2.17
  meets the criterion at $x_0$ (its measures at radius $1$ are $\beta_0 \le \epsilon / j!$), and
  pure $q$-th order spikes fail it at every radius but have the order $\epsilon^{-(p+1)/(p-q+1)}$.
  Heuristically, failing the criterion at radius $1$ needs a derivative of some order
  $3 \le i \le q$ of size at least of order $\epsilon$ at every iterate, and if these derivatives
  are periodic along the run, the Taylor consistency of the jets needs steps of order at least
  $\epsilon^{1/(p-2)}$, much larger than $\epsilon^{q/p}$. The statement of Theorem 12.2.17 in the
  source, "for some $\delta_\epsilon$", has the same caveat.
* **Theorem 14.2.4, ARqp-SC row under the anchored assumptions, existence of runs on a general
  $X$.** Runs that satisfy the radius policy exist on $X = \mathbb{R}^n$
  (`Optimization.exists_isARqpRun_of_anchored`). For a general closed $X$ they are the ARqpC-SC runs
  with $c = 0$ and $h = 0$ of `NumlibSurface.CartisGouldToint.Chapter14.Section01`
  (`CartisGouldToint.Chapter14.exists_algorithm_14_1_1_of_hLip`,
  `Optimization.IsARqpCRun.isARqpRun_zero`), whose radii satisfy (12.2.51) by
  `CartisGouldToint.Chapter14.algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored`. The radius
  hypothesis of the mode in which $u$ fails in
  `CartisGouldToint.Chapter14.theorem_14_2_4_arqp_anchored` is not discharged for these runs in this
  module.
-/

open Set Metric
open scoped Nat

namespace CartisGouldToint.Chapter14

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### Assumptions -/

/-- **Assumption X.CNe** of [cartis2022evaluation], Section 14.2. The feasible set
$X \subseteq \mathbb{R}^n$ is **closed and nonempty**. -/
def AssumptionXCNe (X : Set ℝⁿ) : Prop := IsClosed X ∧ X.Nonempty

/-- X.CNe holds if and only if $X$ is closed and nonempty. -/
theorem assumptionXCNe_iff {X : Set ℝⁿ} : AssumptionXCNe X ↔ IsClosed X ∧ X.Nonempty := Iff.rfl

/-- **Equation (14.2.8)** of [cartis2022evaluation]. The **sublevel set** of $f$ in $X$ at $x_0$ is
$$\mathcal{L}_f(x_0) = \{x \in X : f(x) \le f(x_0)\}.$$
-/
def sublevel (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (x₀ : ℝⁿ) : Set ℝⁿ := {x ∈ X | f x ≤ f x₀}

/-- A point $x$ lies in $\mathcal{L}_f(x_0)$ if and only if $x \in X$ and $f(x) \le f(x_0)$. -/
theorem mem_sublevel {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {x₀ x : ℝⁿ} :
    x ∈ sublevel f X x₀ ↔ x ∈ X ∧ f x ≤ f x₀ := Iff.rfl

/-- The sublevel set $\mathcal{L}_f(x_0)$ is contained in $X$. -/
theorem sublevel_subset {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {x₀ : ℝⁿ} : sublevel f X x₀ ⊆ X :=
  fun _ hx => hx.1

/-- **Assumption f.D1qLaB.X** of [cartis2022evaluation], Section 14.2.1, and its variants. Let
$X \subseteq \mathbb{R}^n$, $x_0 \in \mathbb{R}^n$, $j_0 \le q$, and constants $L_j$ and $B_j$.
The function $f$ satisfies the assumption on $X_0$ if $X_0$ is open and convex,
$X \subseteq X_0$, $f$ is $q$ times continuously differentiable near every point of $X_0$, and
for every order $j \in [j_0 : q]$ we have $L_j \ge 1$, $B_j \ge 1$, $$\|\nabla^j f(x) - \nabla^j
f(y)\| \le L_j \|x - y\| \quad \text{(14.2.9)} \qquad \text{and} \qquad \|\nabla^j f(x)\| \le
B_j \quad \text{(14.2.10)}$$ for every $x$ in the sublevel set $\mathcal{L}_f(x_0)$ of (14.2.8)
and every $y \in X_0$.

With $j_0 = 1$ this is f.D1qLaB.X, and f.D1pLaB.X with $p$ in place of $q$. With $j_0 = 0$ it is
f.D0qLaB.X (`CartisGouldToint.Chapter14.AssumptionD0qLaBX`, where (14.2.9) runs over $[0:q]$)
strengthened by $|f| \le B_0$ on $\mathcal{L}_f(x_0)$; see
`CartisGouldToint.Chapter14.AssumptionD1qLaBX.toD0qLaBX`.

The definition is the anchored smoothness assumption `LipschitzDerivsAnchored` on $X_0$ with the
orders $[j_0 : q]$ and the anchor set $\mathcal{L}_f(x_0)$, together with $X \subseteq X_0$, the
normalizations and the bound (14.2.10). The form of the source is
`CartisGouldToint.Chapter14.AssumptionD1qLaBX.of_contDiffOn`. -/
abbrev AssumptionD1qLaBX (f : ℝⁿ → ℝ) (X X₀ : Set ℝⁿ) (x₀ : ℝⁿ) (j₀ q : ℕ)
    (L B : ℕ → ℝ) : Prop :=
  LipschitzDerivsAnchored f X₀ (sublevel f X x₀) j₀ q L ∧ X ⊆ X₀ ∧
    (∀ j ∈ Finset.Icc j₀ q, 1 ≤ L j) ∧ (∀ j ∈ Finset.Icc j₀ q, 1 ≤ B j) ∧
    ∀ j ∈ Finset.Icc j₀ q, ∀ x ∈ sublevel f X x₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j

namespace AssumptionD1qLaBX

variable {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ} {j₀ q : ℕ} {L B : ℕ → ℝ}

/-- If $f$ satisfies f.D1qLaB.X on $X_0$ with anchor $x_0$, then $f$ satisfies the smoothness
hypothesis `LipschitzDerivsAnchored` on $X_0$ with the orders $[j_0 : q]$ and the anchor set
$\mathcal{L}_f(x_0)$: $X_0$ is open and convex, $f$ is $q$ times continuously differentiable
near every point of $X_0$, and (14.2.9) holds for $x \in \mathcal{L}_f(x_0)$, $y \in X_0$ and
$j \in [j_0 : q]$.

This forgets the normalizations and the bound (14.2.10). -/
theorem toLipschitzDerivsAnchored (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) :
    LipschitzDerivsAnchored f X₀ (sublevel f X x₀) j₀ q L :=
  h.1

/-- Under f.D1qLaB.X on $X_0$, the set $X_0$ is open. -/
theorem isOpen (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) : IsOpen X₀ :=
  h.1.isOpen

/-- Under f.D1qLaB.X on $X_0$, the set $X_0$ is convex. -/
theorem convex (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) : Convex ℝ X₀ :=
  h.1.convex

/-- Under f.D1qLaB.X on $X_0$, the feasible set satisfies $X \subseteq X_0$. -/
theorem subset (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) : X ⊆ X₀ :=
  h.2.1

/-- Under f.D1qLaB.X on $X_0$, the function $f$ is $q$ times continuously differentiable on $X_0$.
-/
theorem contDiffOn (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) : ContDiffOn ℝ q f X₀ :=
  fun y hy => (h.1.contDiffAt y hy).contDiffWithinAt

/-- Under f.D1qLaB.X, the Lipschitz constants satisfy $L_j \ge 1$ for $j \in [j_0 : q]$. -/
theorem one_le_lip (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) :
    ∀ j ∈ Finset.Icc j₀ q, 1 ≤ L j :=
  h.2.2.1

/-- Under f.D1qLaB.X, the bounds satisfy $B_j \ge 1$ for $j \in [j_0 : q]$. -/
theorem one_le_bound (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) :
    ∀ j ∈ Finset.Icc j₀ q, 1 ≤ B j :=
  h.2.2.2.1

/-- Under f.D1qLaB.X, the anchored Lipschitz condition (14.2.9) holds: $\|\nabla^j f(x) - \nabla^j
f(y)\| \le L_j \|x - y\|$ for $j \in [j_0 : q]$, $x \in \mathcal{L}_f(x_0)$ and $y \in X_0$. -/
theorem lipschitzAnchored (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) :
    ∀ j ∈ Finset.Icc j₀ q, IteratedFDerivLipschitzAnchored f j (L j) (sublevel f X x₀) X₀ :=
  h.1.lipschitzAnchored

/-- Under f.D1qLaB.X, the derivative bound (14.2.10) holds: $\|\nabla^j f(x)\| \le B_j$ for
$j \in [j_0 : q]$ and $x \in \mathcal{L}_f(x_0)$. -/
theorem norm_le (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) :
    ∀ j ∈ Finset.Icc j₀ q, ∀ x ∈ sublevel f X x₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j :=
  h.2.2.2.2

/-- f.D1qLaB.X in the form of the source. Let $X_0$ be open and convex with $X \subseteq X_0$, let
$f$ be $q$ times continuously differentiable on $X_0$, let $L_j \ge 1$ and $B_j \ge 1$ for
$j \in [j_0 : q]$, and let (14.2.9) and (14.2.10) hold at the points $x \in \mathcal{L}_f(x_0)$
(with $y \in X_0$ in (14.2.9)) for $j \in [j_0 : q]$. Then $f$ satisfies f.D1qLaB.X. -/
theorem of_contDiffOn (hX₀ : IsOpen X₀) (hconv : Convex ℝ X₀) (hX : X ⊆ X₀)
    (hf : ContDiffOn ℝ q f X₀) (hL1 : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ L j)
    (hB1 : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ B j)
    (hlip : ∀ j ∈ Finset.Icc j₀ q,
      IteratedFDerivLipschitzAnchored f j (L j) (sublevel f X x₀) X₀)
    (hbd : ∀ j ∈ Finset.Icc j₀ q, ∀ x ∈ sublevel f X x₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    AssumptionD1qLaBX f X X₀ x₀ j₀ q L B :=
  ⟨⟨hX₀, hconv, sublevel_subset.trans hX, fun _ hy => hf.contDiffAt (hX₀.mem_nhds hy), hlip⟩,
    hX, hL1, hB1, hbd⟩

end AssumptionD1qLaBX

/-- **Assumption f.bB.X** of [cartis2022evaluation], Section 14.2.1. The function $f$ is **bounded
below on $X$** by $f_{\mathrm{low}}$: $f(x) \ge f_{\mathrm{low}}$ for every $x \in X$. -/
def AssumptionBbX (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (flow : ℝ) : Prop := ∀ x ∈ X, flow ≤ f x

/-- f.bB.X with the bound $f_{\mathrm{low}}$ holds if and only if $f(x) \ge f_{\mathrm{low}}$ for
every $x \in X$. -/
theorem assumptionBbX_iff {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {flow : ℝ} :
    AssumptionBbX f X flow ↔ ∀ x ∈ X, flow ≤ f x := Iff.rfl

/-- A set that satisfies X.CNe is closed. -/
theorem AssumptionXCNe.isClosed {X : Set ℝⁿ} (h : AssumptionXCNe X) : IsClosed X := h.1

/-- A set that satisfies X.CNe is nonempty. -/
theorem AssumptionXCNe.nonempty {X : Set ℝⁿ} (h : AssumptionXCNe X) : X.Nonempty := h.2

/-- For the composite objective $w = f + h \circ c$ of Section 14.1, f.bB.X for $w$ with the bound
$w_{\mathrm{low}}$ is the same as w.Bb on $X$ with the same bound. -/
theorem assumptionBbX_iff_assumptionWBb {m : ℕ} {f : ℝⁿ → ℝ}
    {c : ℝⁿ → EuclideanSpace ℝ (Fin m)} {h : EuclideanSpace ℝ (Fin m) → ℝ} {X : Set ℝⁿ}
    {wlow : ℝ} : AssumptionBbX (fun x => f x + h (c x)) X wlow ↔ AssumptionWBb f c h X wlow :=
  Iff.rfl

/-- **Remark after (14.2.10)** of [cartis2022evaluation]: (14.2.9) is automatic if the derivatives
are Lipschitz on $X_0$. Let $X_0$ be open and convex with $X \subseteq X_0$, let $f$ be $q$
times continuously differentiable on $X_0$, and let $L_j \ge 1$ and $B_j \ge 1$ for
$j \in [j_0 : q]$. If $\|\nabla^j f(x) - \nabla^j f(y)\| \le L_j \|x - y\|$ for all
$x, y \in X_0$ and $\|\nabla^j f(x)\| \le B_j$ for all $x \in X_0$, for every $j \in [j_0 : q]$,
then $f$ satisfies f.D1qLaB.X on $X_0$ for every anchor $x_0$. -/
theorem AssumptionD1qLaBX.of_lipschitzOn {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ} {j₀ q : ℕ}
    {L B : ℕ → ℝ} (hX₀ : IsOpen X₀) (hconv : Convex ℝ X₀) (hX : X ⊆ X₀)
    (hf : ContDiffOn ℝ q f X₀) (hL1 : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ L j)
    (hB1 : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ B j)
    (hlip : ∀ j ∈ Finset.Icc j₀ q, IteratedFDerivLipschitzOn f j (L j) X₀)
    (hbd : ∀ j ∈ Finset.Icc j₀ q, ∀ x ∈ X₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    AssumptionD1qLaBX f X X₀ x₀ j₀ q L B :=
  .of_contDiffOn hX₀ hconv hX hf hL1 hB1
    (fun j hj => (hlip j hj).anchored (sublevel_subset.trans hX))
    fun j hj x hx => hbd j hj x (hX hx.1)

/-- Let $f$ satisfy f.D1qLaB.X on $X_0$ with $j_0 = 1$, and suppose that
$X_0 \subseteq \mathcal{L}_f(x_0)$. Then the derivatives of orders $1$ to $q$ are Lipschitz on
$X_0$: $f$ satisfies `LipschitzDerivsAnchored` on $X_0$ with all of $X_0$ as anchor set. -/
theorem AssumptionD1qLaBX.lipschitzDerivsAnchored_self {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ}
    {q : ℕ} {L B : ℕ → ℝ} (h : AssumptionD1qLaBX f X X₀ x₀ 1 q L B)
    (hsub : X₀ ⊆ sublevel f X x₀) : LipschitzDerivsAnchored f X₀ X₀ 1 q L :=
  ⟨h.isOpen, h.convex, subset_rfl, h.1.contDiffAt,
    fun j hj x hx y hy => h.lipschitzAnchored j hj x (hsub hx) y hy⟩

/-! ### Theorem 14.2.1 -/

/-- **Theorem 14.2.1** of [cartis2022evaluation] (stability of approximate constrained minimizers).
Let $f : \mathbb{R}^n \to \mathbb{R}$, $X \subseteq \mathbb{R}^n$,
$x_\epsilon \in \mathbb{R}^n$, $j \ge 0$ and $\delta, \epsilon, \eta \in \mathbb{R}$. Suppose
that $f$ is $j$ times continuously differentiable at every point of the closed ball
$\bar B(x_\epsilon, \delta)$, that $\nabla^j f$ is Lipschitz on this ball with a constant
$L \ge 0$, and that $$\phi^\delta_{f,X(x_\epsilon),j}(x_\epsilon) \le \frac{\epsilon
\delta^j}{j!} + \eta.$$ Then:

(14.2.6) for every $d \in X(x_\epsilon)$ with $\|d\| \le \delta$ and
$L \|d\| \le (j+1) \epsilon$, $$f(x_\epsilon + d) \ge f(x_\epsilon) - \frac{2 \epsilon
\delta^j}{j!} - \eta;$$

(14.2.7) if $L = 0$, then $f(x_\epsilon + d) \ge f(x_\epsilon) - \epsilon \delta^j / j! - \eta$
for every $d \in X(x_\epsilon)$ with $\|d\| \le \delta$.

**Generalization.** The source asks the Lipschitz condition on an open ball of radius larger
than $\delta$, and $X$ closed and nonempty, $\delta \le 1$ and $\epsilon \le 1$. The closed ball
of radius $\delta$ suffices, and the other conditions are not needed.

**Typo.** The source prints $\delta^j$ in (14.2.6) where $\delta_j^j$ is meant; here the radius
$\delta = \delta_j$ is a single number.

**Reading.** The source's condition $\|d\| \le \min(\delta, (j+1)\epsilon / L)$ for $L > 0$ is
written as $\|d\| \le \delta$ and $L \|d\| \le (j+1) \epsilon$.

The measure is `Optimization.taylorMeasure (ftaylorSeries ℝ f xε) j δ` over the set of $d$ with
$x_\epsilon + d \in X$. -/
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

/-! ### Sparsity constraints (Section 14.2.2) -/

section Sparse

open Subproblem

variable {nnz : ℕ} {x : Fin n → ℝ} {δ : ℝ}

/-- **Equations (14.2.17)–(14.2.18)** of [cartis2022evaluation], the sparse first-order measure. Let
$f : \mathbb{R}^n \to \mathbb{R}$, where $\mathbb{R}^n$ carries the sup norm, let $x$ satisfy
$\|x\|_0 \le n_{\mathrm{nz}}$, let $\delta \ge 0$, and let $g_i = \nabla f(x)[e_i]$. Then there
is a selection $\tau$ that is feasible for the knapsack problem (14.2.21) such that the step
$d^\star$ of (14.2.20) for $\tau$ satisfies $\|d^\star\|_\infty \le \delta$ and
$\|x + d^\star\|_0 \le n_{\mathrm{nz}}$, minimizes $\sum_i g_i d_i$ over all $d$ with
$\|d\|_\infty \le \delta$ and $\|x + d\|_0 \le n_{\mathrm{nz}}$, and
$$\phi^\delta_{f,X(x),1}(x) = -\sum_i g_i d^\star_i,$$ where $X$ is the sparsity set
$\{y : \|y\|_0 \le n_{\mathrm{nz}}\}$ of (14.2.14).

**Typo.** The source prints $\max \ell(d)$ in (14.2.18); the measure (14.2.17) needs the minimum
of $\ell(d) = \langle \nabla f(x), d \rangle$.

The space is `Fin n → ℝ`, whose norm is the sup norm, so that the closed ball of radius $\delta$
is the $\ell_\infty$ ball of the source. The step is `Subproblem.sparseLinearStep` and the
knapsack constraint is `Subproblem.KnapsackFeasible`. No differentiability of $f$ is assumed:
`fderiv` is $0$ where $f$ is not differentiable. -/
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

/-- **Lemma 14.2.5** of [cartis2022evaluation] (optimal sparse solution of (14.2.18)). Let
$x, g \in \mathbb{R}^n$ with the sup norm, $\delta \ge 0$, and let $\tau$ be an optimal solution
of the knapsack problem (14.2.21): $\tau$ is feasible, and its value is at least the value of
every feasible selection. Then the step $d^\star$ of (14.2.20) satisfies
$\|d^\star\|_\infty \le \delta$ and $\|x + d^\star\|_0 \le n_{\mathrm{nz}}$, and it minimizes
$d \mapsto \sum_i g_i d_i$ over all $d$ with $\|d\|_\infty \le \delta$ and
$\|x + d\|_0 \le n_{\mathrm{nz}}$.

**Typo.** The source prints the problem (14.2.18)–(14.2.19) as a maximization of
$\ell(d) = \langle g, d \rangle$; the minimum is meant.

**Generalization.** The source assumes $\|x\|_0 \le n_{\mathrm{nz}}$. This is not needed,
because the knapsack constraint keeps $x + d^\star$ sparse.

The step is `Subproblem.sparseLinearStep x g δ τ`, the knapsack value is
`Subproblem.knapsackValue` and the knapsack constraint is `Subproblem.KnapsackFeasible`. -/
theorem lemma_14_2_5 {g : Fin n → ℝ} {τ : Fin n → Bool} (hδ : 0 ≤ δ)
    (hτ : KnapsackFeasible x δ nnz τ)
    (hopt : ∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ) :
    ‖sparseLinearStep x g δ τ‖ ≤ δ ∧ x + sparseLinearStep x g δ τ ∈ sparseSet n nnz ∧
      IsMinOn (fun d => ∑ i, g i * d i) (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz})
        (sparseLinearStep x g δ τ) :=
  isMinOn_sparseLinearStep hδ hτ hopt

end Sparse

/-!
### Complexity of the -SC algorithms (Section 14.2.1)

The rows of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4 of [cartis2022evaluation] for ARqpC-SC, TRq-SC
and ARqp-SC are stated here under smoothness on all of $\mathbb{R}^n$ (f.D1pL and c.D1pL of Section
14.1, for ARqpC-SC) or on an open convex set $C \supseteq X$ (`LipschitzDerivsAnchored f C C 1 p L`,
for TRq-SC and ARqp-SC). The ARqpC-SC row is also stated under anchored bounds. The TRq-SC and
ARqp-SC rows under the anchored assumptions f.D1qLaB.X and f.D1pLaB.X follow in the section on
anchored assumptions.
-/

section ARqpCSC

variable {f : ℝⁿ → ℝ} {m : ℕ} {c : ℝⁿ → EuclideanSpace ℝ (Fin m)}
  {h : EuclideanSpace ℝ (Fin m) → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpC-SC row. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$c : \mathbb{R}^n \to \mathbb{R}^m$ and $h : \mathbb{R}^m \to \mathbb{R}$ satisfy f.D1pL,
c.D1pL, h.L and h.S0 of Section 14.1 with constants $L_{f,j}$, $L_{c,j}$ and $L_{h,0}$, let
$w = f + h \circ c$, and consider an ARqpC-SC run on a feasible set $X$ with
$\theta < \varsigma$. Let $k$ be a successful iteration ($\rho_k \ge \eta_1$) such that the
termination test fails at the iterations $0, \dots, k$ and the Step-1 test fails at iteration
$k + 1$. Then there is $j \in [1 : q]$ with $$w(x_k) - w(x_{k+1}) \ge \eta_1 \kappa_{\Delta m}
\epsilon_j^{j+1},$$ where $\kappa_{\Delta m}$ is the constant of Lemma 14.1.9 in the general
case. This is the row $\pi_j = j + 1$ of (14.2.12).

The radius policy (14.1.28) holds for every run, so it is not a hypothesis. The constant is
`CartisGouldToint.Chapter14.kappaDm2`. The convex case $q = 1$ is the first part of
`CartisGouldToint.Chapter14.lemma_14_1_9`.

**Correction.** Uses the composite objective, explicit next Step-1 failure and orderwise decrease,
and the corrected constants from Section 14.1.
-/
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

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpC-SC row. Let $f$, $c$ and $h$ satisfy f.D1pL,
c.D1pL and h.L, and consider an ARqpC-SC run on a feasible set $X$. Then every iteration $k$
such that the termination test fails at all iterations before $k$ (so $k$ may be the termination
index) satisfies $$k \le \kappa_{\mathrm{uns}} |\mathcal{S}_k| + \kappa_{\mathrm{unc}} \quad
\text{(14.2.13)}, \qquad \kappa_{\mathrm{uns}} = 1 + \frac{|\log \gamma_1|}{\log \gamma_2},
\quad \kappa_{\mathrm{unc}} = \frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_2},$$ where
$\mathcal{S}_k$ is the set of successful iterations in $[0 : k]$ and $\sigma_{\max}$ is the
bound of Lemma 14.1.6.

This is Lemma 2.4.1 with the bound $\sigma_{\max}$ of Lemma 14.1.6
(`CartisGouldToint.Chapter14.arqpcSigmaMax`).

**Reading.** Adds an explicit ARqpC-SC count on the reached prefix from the regularization parameter
bound.
-/
theorem lemma_14_2_3_arqpc (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) {k : ℕ} (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRatio
        (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀) / Real.log P.γ₂ :=
  hr.run.toIsARRun.le_succ_count hk (sigma_le_arqpcSigmaMax hr hf hc hL hk k le_rfl)

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpC-SC row ($h$ nonconvex or $q > 1$). Let $f$,
$c$ and $h$ satisfy f.D1pL, c.D1pL, h.L and h.S0, let $w = f + h \circ c$ satisfy w.Bb on $X$
with the bound $w_{\mathrm{low}}$, let $\theta < \varsigma$, and let $m_\epsilon > 0$ with
$m_\epsilon \le \epsilon_j^{j+1}$ for every $j \in [1 : q]$. Then every ARqpC-SC run on $X$
terminates at a first iteration $k_\epsilon$, with $x_{k_\epsilon} \in X$, and there are radii
$\delta_\epsilon \in (0, 1]^q$ for which $x_{k_\epsilon}$ is an
$(\epsilon, \delta_\epsilon)$-approximate $q$-th order minimizer of $w$ on $X$ in the sense of
(14.1.9). With $N = (w(x_0) - w_{\mathrm{low}}) / (\eta_1 \kappa_{\Delta m} m_\epsilon)$, the
number of function evaluations is at most $$\Big(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Big)
N + \frac{|\log \gamma_1| + \log(\sigma_{\max}/\sigma_0)}{\log \gamma_2} + 2,$$ and the number
of derivative evaluations is at most $N + 2$.

This is part 2 of Theorem 14.1.10 for ARqpC-SC runs, with the measures taken over the feasible
displacements and the additional conclusion $x_{k_\epsilon} \in X$. The constant
$\kappa_{\Delta m}$ is `CartisGouldToint.Chapter14.kappaDm2` and $\sigma_{\max}$ is
`CartisGouldToint.Chapter14.arqpcSigmaMax`.

**Reading.** Explicit composite counts through first stop using any positive lower bound on the
tolerance powers.
-/
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

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpC-SC row for $q = 1$ with $h$ and $X$ convex.
Let $f$, $c$ and $h$ satisfy f.D1pL, c.D1pL and h.L, let $h$ and $X$ be convex, let
$w = f + h \circ c$ satisfy w.Bb on $X$ with the bound $w_{\mathrm{low}}$, let
$\theta < \varsigma$, $q = 1$ and $\delta_{0,1} = 1$. Then every ARqpC-SC run on $X$ terminates
at a first iteration $k_\epsilon$ with $x_{k_\epsilon} \in X$ and
$\phi^1_{w,X(x_{k_\epsilon}),1}(x_{k_\epsilon}) \le \epsilon_1$. With $N = (w(x_0) -
w_{\mathrm{low}}) / (\eta_1 \kappa_{\Delta m} \epsilon_1^{(p+1)/p})$, the number of function
evaluations is at most $$\Big(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Big) N + \frac{|\log
\gamma_1| + \log(\sigma_{\max}/\sigma_0)}{\log \gamma_2} + 2,$$ and the number of derivative
evaluations is at most $N + 2$.

This is part 1 of Theorem 14.1.10 for ARqpC-SC runs, with the additional conclusion
$x_{k_\epsilon} \in X$. The constant $\kappa_{\Delta m}$ is that of Lemma 14.1.9 in the convex
case, `CartisGouldToint.Chapter14.kappaDm1`.

**Correction.** Uses the corrected first-order composite constants and assumes unit initial radius.
-/
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

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpC-SC row under anchored bounds. Let
$X_0 \supseteq X$ be open and convex, and let $f$ and $c$ satisfy the anchored bounds
`CartisGouldToint.Chapter14.AnchoredCompositeBounds` on $X_0$ with constants $L_{f,j}$,
$L_{c,j}$ and the anchor set $\{y \in X : w(y) \le w(x_0)\}$, the form of f.D1pLaB.X used for
ARqpC-SC. Let $h$ satisfy h.L and h.S0, let $\theta < \varsigma$, and consider an ARqpC-SC run
on $X$. Let $k$ be a successful iteration such that the termination test fails at the iterations
$0, \dots, k$ and the Step-1 test fails at iteration $k + 1$. Then there is $j \in [1 : q]$ with
$$w(x_k) - w(x_{k+1}) \ge \eta_1 \kappa_{\Delta m} \epsilon_j^{j+1},$$ with the constant
$\kappa_{\Delta m}$ (`CartisGouldToint.Chapter14.kappaDm2`) of Lemma 14.1.9 in the general case.

**Correction.** Uses the composite objective, explicit next Step-1 failure and orderwise decrease,
and the corrected constants from Section 14.1.
-/
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

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpC-SC row under anchored bounds. Let
$X_0 \supseteq X$ be open and convex, let $f$ and $c$ satisfy
`CartisGouldToint.Chapter14.AnchoredCompositeBounds` on $X_0$ with the anchor set
$\{y \in X : w(y) \le w(x_0)\}$, and let $h$ satisfy h.L. Then for an ARqpC-SC run on $X$, every
iteration $k$ such that the termination test fails at all iterations before $k$ satisfies $$k
\le \Big(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Big) |\mathcal{S}_k| +
\frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_2} \quad \text{(14.2.13)},$$ with
$\sigma_{\max}$ of Lemma 14.1.6 and $\mathcal{S}_k$ the set of successful iterations in
$[0 : k]$.

**Reading.** Adds an explicit ARqpC-SC count on the reached prefix from the regularization parameter
bound.
-/
theorem lemma_14_2_3_arqpc_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRatio
        (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀) / Real.log P.γ₂ :=
  hr.run.toIsARRun.le_succ_count hk (sigma_le_arqpcSigmaMax_anchored hr hA hX hL hk k le_rfl)

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpC-SC row under anchored bounds. Let
$X_0 \supseteq X$ be open and convex, let $f$ and $c$ satisfy
`CartisGouldToint.Chapter14.AnchoredCompositeBounds` on $X_0$ with the anchor set
$\{y \in X : w(y) \le w(x_0)\}$, let $h$ satisfy h.L and h.S0, let $w = f + h \circ c$ satisfy
w.Bb on $X$ with the bound $w_{\mathrm{low}}$, let $\theta < \varsigma$, and let
$m_\epsilon > 0$ with $m_\epsilon \le \epsilon_j^{j+1}$ for every $j \in [1 : q]$. Then every
ARqpC-SC run on $X$ terminates at a first iteration $k_\epsilon$, with $x_{k_\epsilon} \in X$,
and there are radii $\delta_\epsilon \in (0, 1]^q$ for which $x_{k_\epsilon}$ is an
$(\epsilon, \delta_\epsilon)$-approximate $q$-th order minimizer of $w$ on $X$. With $N =
(w(x_0) - w_{\mathrm{low}}) / (\eta_1 \kappa_{\Delta m} m_\epsilon)$, the number of function
evaluations is at most $$\Big(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Big) N + \frac{|\log
\gamma_1| + \log(\sigma_{\max}/\sigma_0)}{\log \gamma_2} + 2,$$ and the number of derivative
evaluations is at most $N + 2$.

This is `CartisGouldToint.Chapter14.theorem_14_1_10_ii_anchored` for ARqpC-SC runs, with the
additional conclusion $x_{k_\epsilon} \in X$.

**Reading.** Explicit composite counts through first stop using any positive lower bound on the
tolerance powers.
-/
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

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRq-SC row. Let $E$ be a real inner product space,
let $C \subseteq E$ be open and convex with $X \subseteq C$, and let $f$ be $q$ times
continuously differentiable near every point of $C$ with $\|\nabla^j f(x) - \nabla^j f(y)\| \le
L_j \|x - y\|$ for $x, y \in C$ and $j \in [1 : q]$. Let $\epsilon \in (0, 1]^q$, let
$\epsilon_{\min} \le \vartheta \le 1$, and consider a TRq-SC run on $X$ with $x_0 \in X$. Then
at every iteration $k$ such that the termination test fails at the iterations $0, \dots, k$,
$$\Delta T_{f,j_k}(x_k, s_k) \ge \frac{(\varsigma \kappa_\Delta)^{q+1}}{q!}
\epsilon_{\min}^{q+1},$$ and if $k$ is successful ($\rho_k \ge \eta_1$), then
$f(x_k) - f(x_{k+1})$ is at least $\eta_1$ times this bound.

The exponent $\pi_j = q + 1$ for every $j$ agrees with the original table (14.2.12).

This is Lemma 12.2.4 with a feasible set. The normalization $L_j \ge 1$ is not needed. The
constant $\kappa_\Delta$ of (12.2.14) is `Optimization.trqKappaDelta f P q L ϑ (x 0)`, and
$\epsilon_{\min}$ is `Optimization.finMin 1 ε q`.

**Reading.** The q+1 exponent agrees with the PDF. Includes explicit model decrement and
quantitative threshold hypotheses; the pairwise variant uses a general real inner product space.
-/
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

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRq-SC row. Let $E$ be a real inner product space,
let $C \subseteq E$ be open and convex with $X \subseteq C$, and let $f$ be $q$ times
continuously differentiable near every point of $C$ with $\|\nabla^j f(x) - \nabla^j f(y)\| \le
L_j \|x - y\|$ for $x, y \in C$ and $j \in [1 : q]$. Let $f \ge f_{\mathrm{low}}$ on $X$,
$\epsilon \in (0, 1]^q$ and $\epsilon_{\min} \le \vartheta \le 1$. Then every TRq-SC run on $X$
with $x_0 \in X$ terminates at a first iteration $k_\epsilon$ with $x_{k_\epsilon} \in X$, the
radius $\delta = \min(\Delta_{k_\epsilon}, \vartheta)$ lies in $(0, 1]$, and $x_{k_\epsilon}$ is
an $(\epsilon, \delta)$-approximate $q$-th order minimizer on $X$ with the radius $\delta$ at
every order. The number of function evaluations is at most $$\kappa^A_{\mathrm{TRq}}
\frac{f(x_0) - f_{\mathrm{low}}}{\epsilon_{\min}^{q+1}} + \kappa^B_{\mathrm{TRq}} |\log
\epsilon_{\min}| + \kappa^C_{\mathrm{TRq}},$$ and the number of derivative evaluations is at
most $\kappa^S_{\mathrm{TRq}} (f(x_0) - f_{\mathrm{low}}) / \epsilon_{\min}^{q+1} + 1$. So the
order is $O(\max_j \epsilon_j^{-(q+1)})$.

This is Theorem 12.2.5 with a feasible set. The normalization $L_j \ge 1$ is not needed. The
constants are `Optimization.kappaATRq`, `Optimization.kappaBTRq`, `Optimization.kappaCTRq` and
`Optimization.kappaSTRq` of Theorem 12.2.5.

**Reading.** Explicit counts and first stopping certificate, with tolerance-dependent logarithmic
term and first-order through q-th order anchored regularity sufficient.
-/
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

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRq-SC row. Let $E$ be a real inner product space,
let $C \subseteq E$ be open and convex with $X \subseteq C$, and let $f$ be $q$ times
continuously differentiable near every point of $C$ with $\|\nabla^j f(x) - \nabla^j f(y)\| \le
L_j \|x - y\|$ for $x, y \in C$ and $j \in [1 : q]$. Let $\epsilon \in (0, 1]^q$ and
$\epsilon_{\min} \le \vartheta \le 1$, and consider a TRq-SC run on $X$ with $x_0 \in X$. Then
every iteration $k$ such that the termination test fails at all iterations before $k$ satisfies
$$k \le \Big(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\Big) |\mathcal{S}_k| +
\frac{|\log(\min(\gamma_1 \vartheta, \kappa_\Delta \varsigma \epsilon_{\min}) /
\Delta_0)|}{|\log \gamma_2|} \quad \text{(14.2.13)},$$ where $\mathcal{S}_k$ is the set of
successful iterations in $[0 : k]$ and $\kappa_\Delta$ is the constant of (12.2.14).

**Reading.** The source leaves $\kappa_{\mathrm{unc}}$ implicit. Here it is explicit and
contains $|\log \epsilon_{\min}|$, because the radius lower bound of the TR methods is
proportional to $\epsilon_{\min}$.

This is Lemma 2.3.1 with the radius lower bound of Lemma 12.2.3 with a feasible set
(`Optimization.IsTRqRun.radius_ge_of_anchored`). The normalization $L_j \ge 1$ is not needed. -/
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

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqp-SC row. Let $E$ be a real inner product space,
let $C \subseteq E$ be open and convex with $X \subseteq C$, let $f$ be $p$ times continuously
differentiable near every point of $C$ with $\|\nabla^j f(x) - \nabla^j f(y)\| \le L_j \|x -
y\|$ for $x, y \in C$ and $L_j \ge 1$, for $j \in [1 : p]$. Let $1 \le q \le p$,
$\theta < \varsigma$ and $\epsilon \in (0, 1]^q$, and consider an ARqp-SC run on $X$. Let $k$ be
a successful iteration ($\rho_k \ge \eta_1$) such that the termination test fails at the
iterations $0, \dots, k$ and the Step-1 test fails at iteration $k + 1$. Let $u$ be a
proposition (the radii mode), and assume the radius policy at $k + 1$: if $u$ holds,
$\delta_{k+1,j} = 1$ for every $j \in [1 : q]$; if $u$ fails, either $\|s_k\| \ge 1$ or
$\delta_{k+1,j} \ge \kappa_\delta \epsilon_j$ for every $j \in [1 : q]$, where $\kappa_\delta =
\varsigma \theta / (8 (3 \bar L + \sigma_{\max}))$, $\bar L = \max(1, \max_j L_j)$ and
$\sigma_{\max} = \max(\sigma_0, \gamma_3 L_p / (1 - \eta_2))$. Then $$\Delta T_{f,p}(x_k, s_k)
\ge \kappa_{\Delta m} \min_{j \in [1:q]} \epsilon_j^{\pi_j} \qquad \text{and} \qquad f(x_k) -
f(x_{k+1}) \ge \eta_1 \kappa_{\Delta m} \min_{j \in [1:q]} \epsilon_j^{\pi_j},$$ with
$\pi_j = (p+1)/(p-j+1)$ if $u$ holds and $\pi_j = j(p+1)/p$ if $u$ fails, and
$\kappa_{\Delta m}$ the constant of Lemma 12.2.13 in the same mode.

**Reading.** The table (14.2.12) keys the exponents by $q$ and $X$. Here they are keyed by the
radii mode. The mode in which $u$ fails gives the "otherwise" entry $j(p+1)/p$ for every $q$ and
$X$. The unit-radii entries need $\delta_{k,2} = 1$ (the entry for $X = \mathbb{R}^n$, $q = 2$)
and $\delta_{k,1} = 1$ (the entry for convex $X$), which is here the hypothesis $u$ on the
radii. The split of the source is the mode $u = (q \le 2)$ (`CartisGouldToint.Chapter12.arqpPi`,
`CartisGouldToint.Chapter12.arqpKappaDm`).

This is Lemma 12.2.13 with a feasible set. The exponents are `Optimization.arqpPiOf u p j`, the
constant is `Optimization.arqpKappaDmOf u`, and $\kappa_\delta$ is
`Optimization.arqpKappaDelta`. The minimum is `Optimization.finMin 1`, which also contains $1$;
this does not change it, since $\epsilon_j \le 1$. -/
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

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqp-SC row. Let $E$ be a real inner product space,
let $C \subseteq E$ be open and convex with $X \subseteq C$, let $f$ be $p$ times continuously
differentiable near every point of $C$ with $\|\nabla^j f(x) - \nabla^j f(y)\| \le L_j \|x -
y\|$ for $x, y \in C$ and $j \in [1 : p]$, and let $p \ge 1$. Then for an ARqp-SC run on $X$,
every iteration $k$ such that the termination test fails at all iterations before $k$ satisfies
$$k \le \Big(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Big) |\mathcal{S}_k| +
\frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_2} \quad \text{(14.2.13)}, \qquad
\sigma_{\max} = \max\Big(\sigma_0, \frac{\gamma_3 L_p}{1 - \eta_2}\Big),$$ where $\mathcal{S}_k$
is the set of successful iterations in $[0 : k]$.

This is Lemma 2.4.1 with the bound $\sigma_{\max}$ of the analysis of Lemma 12.2.13. The
normalization $L_j \ge 1$ is not needed. The other rows are
`CartisGouldToint.Chapter14.lemma_14_2_3_arqpc`, `CartisGouldToint.Chapter14.lemma_14_2_3_trq`,
`CartisGouldToint.Chapter14.lemma_14_2_3_trqida`,
`CartisGouldToint.Chapter14.lemma_14_2_3_trqeda`,
`CartisGouldToint.Chapter14.lemma_14_2_3_arqpida` and
`CartisGouldToint.Chapter14.lemma_14_2_3_arqpeda`.

**Reading.** Explicit prefix count with logarithm of sigma_max/sigma_0 and matching
algorithm-parameter coefficient.
-/
theorem lemma_14_2_3 (hf : LipschitzDerivsAnchored f C C 1 p L) (hXC : X ⊆ C) (hp : 1 ≤ p)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRho f p x s σ j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂ :=
  h.toIsARRun.le_succ_count hk
    (Optimization.IsARqpRun.sigma_le_of_anchored ((hf.mono_left hXC).mono hp le_rfl)
    hXC (fun _ hy _ => hy) h k hk).2

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqp-SC row. Let $E$ be a real inner product
space, let $C \subseteq E$ be open and convex with $X \subseteq C$, let $f$ be $p$ times
continuously differentiable near every point of $C$ with $\|\nabla^j f(x) - \nabla^j f(y)\| \le
L_j \|x - y\|$ for $x, y \in C$ and $L_j \ge 1$, for $j \in [1 : p]$, and let
$f \ge f_{\mathrm{low}}$ on $X$. Let $1 \le q \le p$, $\sigma_{\min} > 0$, $\theta < \varsigma$,
$\epsilon \in (0, 1]^q$ and $\delta_0 \in (0, 1]^q$, and consider an ARqp-SC run on $X$. Let $u$
be a proposition (the radii mode), and assume the radius policy: if $u$ holds,
$\delta_{0,j} = 1$ and $\delta_{s_k,j} = 1$ for every $j \in [1 : q]$ and every $k$ before
termination; if $u$ fails, $\delta_{s_k,j} \ge \kappa_\delta(\sigma_k) \epsilon_j$ for every
$j \in [1 : q]$ and every $k$ before termination with $\|s_k\| < 1$, where
$\kappa_\delta(\sigma) = \varsigma \theta / (8 (3 \bar L + \sigma))$ and
$\bar L = \max(1, \max_j L_j)$. Then the run terminates at a first iteration $k_\epsilon$ with
$x_{k_\epsilon} \in X$, and there are radii $\delta_\epsilon \in (0, 1]^q$ for which
$x_{k_\epsilon}$ is an $(\epsilon, \delta_\epsilon)$-approximate $q$-th order minimizer on $X$.
With $m_\epsilon = \min_j \epsilon_j^{\pi_j}$, the number of function evaluations is at most
$$\kappa^a \frac{f(x_0) - f_{\mathrm{low}}}{m_\epsilon} + \kappa^c,$$ and the number of
derivative evaluations is at most $\kappa^s (f(x_0) - f_{\mathrm{low}}) / m_\epsilon + 2$, where
$\pi_j = (p+1)/(p-j+1)$ if $u$ holds and $\pi_j = j(p+1)/p$ if $u$ fails. So the order is
$O(\max_j \epsilon_j^{-\pi_j})$.

**Reading.** The table keys the order by $q$ and $X$; here it is keyed by the radii mode, as in
`CartisGouldToint.Chapter14.lemma_14_2_2_arqp`. The mode in which $u$ fails gives the
"otherwise" order $j(p+1)/p$ for every $q$ and $X$. The split of the source is the mode
$u = (q \le 2)$ (`CartisGouldToint.Chapter12.arqpPi`).

This is Theorem 12.2.14 with a feasible set. The constants
$\kappa^s = 1/(\eta_1 \kappa_{\Delta m})$, $\kappa^a = \kappa^s (1 + |\log \gamma_1| / \log
\gamma_2)$ and $\kappa^c = (|\log \gamma_1| + \log(\sigma_{\max}/\sigma_0)) / \log \gamma_2 + 2$
are `Optimization.kappaSARqpOf u`, `Optimization.kappaAARqpOf u` and `Optimization.kappaCARqp`. -/
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

/-!
### The TRq-SC and ARqp-SC rows under the anchored assumptions

The remark after (14.2.10) of [cartis2022evaluation]: the rows of Lemmas 14.2.2–14.2.3 and Theorem
14.2.4 use only the anchored assumption f.D1qLaB.X (TRq-SC) or f.D1pLaB.X (ARqp-SC) with the
starting point $x_0$ as anchor. The iterates lie in the sublevel set $\mathcal{L}_f(x_0)$, because
the objective does not increase along the runs. The models are built at the iterates, and the trial
points, in $X \subseteq X_0$, are related to them by Taylor's theorem anchored at the iterate. The
bound (14.2.10) is not used: the bounds on the jets at the anchors follow from (14.2.9) at the
interior points of $X_0$ (`LipschitzDerivsAnchored.norm_iteratedFDeriv_le_finMax`). The constants
are those of the rows above with the anchored Lipschitz constants $L_{f,j}$.
-/

section Anchored

variable {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {L B : ℕ → ℝ}

/-- **Assumption f.D0qLaB.X** of [cartis2022evaluation], Section 14.2.1, and f.D0pLaB.X with $p$ in
place of $q$. Let $X \subseteq \mathbb{R}^n$, $x_0 \in \mathbb{R}^n$ and constants $L_j$, $B_j$.
The function $f$ satisfies the assumption on $X_0$ if $X_0$ is open and convex,
$X \subseteq X_0$, $f$ is $q$ times continuously differentiable near every point of $X_0$, and
$$\|\nabla^j f(x) - \nabla^j f(y)\| \le L_j \|x - y\| \quad (j \in [0 : q]) \qquad \text{and}
\qquad \|\nabla^j f(x)\| \le B_j \quad (j \in [1 : q])$$ for every $x \in \mathcal{L}_f(x_0)$
and $y \in X_0$, with $L_j \ge 1$ for $j \in [0 : q]$ and $B_j \ge 1$ for $j \in [1 : q]$. For
$j = 0$ the first condition reads $|f(x) - f(y)| \le L_0 \|x - y\|$.

This is f.D1qLaB.X with the indices of the anchored Lipschitz condition (14.2.9) extended to
$[0 : q]$, as in the source, which extends only these indices. It is stated as
`LipschitzDerivsAnchored` on $X_0$ with the orders $[0 : q]$ and the anchor set
$\mathcal{L}_f(x_0)$, together with $X \subseteq X_0$, the normalizations and the bound
(14.2.10). `CartisGouldToint.Chapter14.AssumptionD1qLaBX` with $j_0 = 0$, which also bounds
$|f|$ on $\mathcal{L}_f(x_0)$, implies it
(`CartisGouldToint.Chapter14.AssumptionD1qLaBX.toD0qLaBX`). -/
abbrev AssumptionD0qLaBX (f : ℝⁿ → ℝ) (X X₀ : Set ℝⁿ) (x₀ : ℝⁿ) (q : ℕ) (L B : ℕ → ℝ) :
    Prop :=
  LipschitzDerivsAnchored f X₀ (sublevel f X x₀) 0 q L ∧ X ⊆ X₀ ∧
    (∀ j ∈ Finset.Icc 0 q, 1 ≤ L j) ∧ (∀ j ∈ Finset.Icc 1 q, 1 ≤ B j) ∧
    ∀ j ∈ Finset.Icc 1 q, ∀ x ∈ sublevel f X x₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j

namespace AssumptionD0qLaBX

variable {x₀ : ℝⁿ} {q : ℕ}

/-- If $f$ satisfies f.D0qLaB.X on $X_0$ with anchor $x_0$, then $f$ satisfies the smoothness
hypothesis `LipschitzDerivsAnchored` on $X_0$ with the orders $[0 : q]$ and the anchor set
$\mathcal{L}_f(x_0)$: $X_0$ is open and convex, $f$ is $q$ times continuously differentiable
near every point of $X_0$, and $\|\nabla^j f(x) - \nabla^j f(y)\| \le L_j \|x - y\|$ for
$x \in \mathcal{L}_f(x_0)$, $y \in X_0$ and $j \in [0 : q]$.

This forgets the normalizations and the bound (14.2.10). -/
theorem lipschitzDerivsAnchored (h : AssumptionD0qLaBX f X X₀ x₀ q L B) :
    LipschitzDerivsAnchored f X₀ (sublevel f X x₀) 0 q L :=
  h.1

/-- Under f.D0qLaB.X on $X_0$, the feasible set satisfies $X \subseteq X_0$. -/
theorem subset (h : AssumptionD0qLaBX f X X₀ x₀ q L B) : X ⊆ X₀ :=
  h.2.1

/-- Under f.D0qLaB.X, the Lipschitz constants are normalized: $L_j \ge 1$ for every $j \le q$. -/
theorem normalized (h : AssumptionD0qLaBX f X X₀ x₀ q L B) : ∀ j ≤ q, 1 ≤ L j :=
  fun j hj => h.2.2.1 j (Finset.mem_Icc.2 ⟨Nat.zero_le j, hj⟩)

/-- f.D0qLaB.X implies f.D1qLaB.X with the same set $X_0$, anchor $x_0$ and constants. -/
theorem toAssumptionD1qLaBX (h : AssumptionD0qLaBX f X X₀ x₀ q L B) :
    AssumptionD1qLaBX f X X₀ x₀ 1 q L B :=
  ⟨h.1.mono zero_le_one le_rfl, h.2.1,
    fun j hj => h.2.2.1 j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj), h.2.2.2⟩

/-- Under f.D0qLaB.X, condition (14.2.9) holds for $j = 0$: $|f(x) - f(y)| \le L_0 \|x - y\|$ for
$x \in \mathcal{L}_f(x_0)$ and $y \in X_0$. -/
theorem lipschitzAnchored_zero (h : AssumptionD0qLaBX f X X₀ x₀ q L B) :
    IteratedFDerivLipschitzAnchored f 0 (L 0) (sublevel f X x₀) X₀ :=
  h.1.lipschitzAnchored 0 (Finset.mem_Icc.2 ⟨le_rfl, Nat.zero_le q⟩)

end AssumptionD0qLaBX

/-- If $f$ satisfies `CartisGouldToint.Chapter14.AssumptionD1qLaBX` with $j_0 = 0$, which also asks
$|f| \le B_0$ on $\mathcal{L}_f(x_0)$, then $f$ satisfies f.D0qLaB.X with the same set $X_0$,
anchor $x_0$ and constants. -/
theorem AssumptionD1qLaBX.toD0qLaBX {x₀ : ℝⁿ} {q : ℕ} (h : AssumptionD1qLaBX f X X₀ x₀ 0 q L B) :
    AssumptionD0qLaBX f X X₀ x₀ q L B :=
  ⟨h.1, h.2.1, h.2.2.1, fun j hj => h.2.2.2.1 j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj),
    fun j hj => h.2.2.2.2 j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj)⟩

/-- f.D0qLaB.X holds if and only if f.D1qLaB.X holds (with $j_0 = 1$), $L_0 \ge 1$, and
$|f(x) - f(y)| \le L_0 \|x - y\|$ for every $x \in \mathcal{L}_f(x_0)$ and $y \in X_0$. -/
theorem assumptionD0qLaBX_iff {x₀ : ℝⁿ} {q : ℕ} : AssumptionD0qLaBX f X X₀ x₀ q L B ↔
    AssumptionD1qLaBX f X X₀ x₀ 1 q L B ∧ 1 ≤ L 0 ∧
      IteratedFDerivLipschitzAnchored f 0 (L 0) (sublevel f X x₀) X₀ := by
  refine ⟨fun h => ⟨h.toAssumptionD1qLaBX, h.normalized 0 (Nat.zero_le q),
    h.lipschitzAnchored_zero⟩, fun ⟨h, h1, h0⟩ => ⟨⟨h.isOpen, h.convex, h.1.subset, h.1.contDiffAt,
      fun j hj => ?_⟩, h.subset, fun j hj => ?_, h.one_le_bound, h.norm_le⟩⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact h0
    · exact h.lipschitzAnchored j (Finset.mem_Icc.2 ⟨hj0, (Finset.mem_Icc.1 hj).2⟩)
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact h1
    · exact h.one_le_lip j (Finset.mem_Icc.2 ⟨hj0, (Finset.mem_Icc.1 hj).2⟩)

section TRq

variable {P : Optimization.TRqParams} {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → ℝⁿ} {Δ : ℕ → ℝ}
  {jk : ℕ → ℕ} {d : ℕ → ℕ → ℝⁿ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRq-SC row under f.D1qLaB.X (the remark after
(14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D1qLaB.X on $X_0$ with the anchor
$x_0$, the starting point of the run, and constants $L_j$, $B_j$. Let $\epsilon \in (0, 1]^q$,
$\epsilon_{\min} \le \vartheta \le 1$, and consider a TRq-SC run on $X$ with $x_0 \in X$. Then
at every iteration $k$ such that the termination test fails at the iterations $0, \dots, k$,
$$\Delta T_{f,j_k}(x_k, s_k) \ge \frac{(\varsigma \kappa_\Delta)^{q+1}}{q!}
\epsilon_{\min}^{q+1},$$ and if $k$ is successful ($\rho_k \ge \eta_1$), then
$f(x_k) - f(x_{k+1})$ is at least $\eta_1$ times this bound.

The exponent $\pi_j = q + 1$ agrees with (14.2.12).

The constant $\kappa_\Delta$ of (12.2.14) is `Optimization.trqKappaDelta f P q L ϑ (x 0)`.

**Reading.** The q+1 exponent agrees with the PDF. Includes explicit model decrement and
quantitative threshold hypotheses; the pairwise variant uses a general real inner product space.
-/
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

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRq-SC row under f.D1qLaB.X. Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D1qLaB.X on $X_0$ with the anchor $x_0$, the
starting point of the run, and constants $L_j$, $B_j$. Let $\epsilon \in (0, 1]^q$,
$\epsilon_{\min} \le \vartheta \le 1$, and consider a TRq-SC run on $X$ with $x_0 \in X$. Then
every iteration $k$ such that the termination test fails at all iterations before $k$ satisfies
$$k \le \Big(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\Big) |\mathcal{S}_k| +
\frac{|\log(\min(\gamma_1 \vartheta, \kappa_\Delta \varsigma \epsilon_{\min}) /
\Delta_0)|}{|\log \gamma_2|} \quad \text{(14.2.13)},$$ where $\mathcal{S}_k$ is the set of
successful iterations in $[0 : k]$ and $\kappa_\Delta$ is the constant of (12.2.14).

**Reading.** The prefix count has explicit parameters and the logarithm of the tolerance-dependent
radius floor.
-/
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

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRq-SC row under f.bB.X and f.D1qLaB.X (the remark
after (14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.bB.X with the bound
$f_{\mathrm{low}}$ and f.D1qLaB.X on $X_0$ with the anchor $x_0$, the starting point of the run,
and constants $L_j$, $B_j$. Let $\epsilon \in (0, 1]^q$ and
$\epsilon_{\min} \le \vartheta \le 1$. Then every TRq-SC run on $X$ with $x_0 \in X$ terminates
at a first iteration $k_\epsilon$ with $x_{k_\epsilon} \in X$, the radius
$\delta = \min(\Delta_{k_\epsilon}, \vartheta)$ lies in $(0, 1]$, and $x_{k_\epsilon}$ is an
$(\epsilon, \delta)$-approximate $q$-th order minimizer on $X$ with the radius $\delta$ at every
order. The number of function evaluations is at most $$\kappa^A_{\mathrm{TRq}} \frac{f(x_0) -
f_{\mathrm{low}}}{\epsilon_{\min}^{q+1}} + \kappa^B_{\mathrm{TRq}} |\log \epsilon_{\min}| +
\kappa^C_{\mathrm{TRq}},$$ and the number of derivative evaluations is at most
$\kappa^S_{\mathrm{TRq}} (f(x_0) - f_{\mathrm{low}}) / \epsilon_{\min}^{q+1} + 1$, with the
constants of Theorem 12.2.5 (`Optimization.kappaATRq`, `Optimization.kappaBTRq`,
`Optimization.kappaCTRq`, `Optimization.kappaSTRq`).

**Reading.** Explicit counts and first stopping certificate, with tolerance-dependent logarithmic
term and first-order through q-th order anchored regularity sufficient.
-/
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

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqp-SC row under f.D1pLaB.X (the remark after
(14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D1pLaB.X on $X_0$ with the anchor
$x_0$, the starting point of the run, and constants $L_j$, $B_j$ for $j \in [1 : p]$. Let
$1 \le q \le p$, $\theta < \varsigma$ and $\epsilon \in (0, 1]^q$, and consider an ARqp-SC run
on $X$. Let $k$ be a successful iteration such that the termination test fails at the iterations
$0, \dots, k$ and the Step-1 test fails at iteration $k + 1$, and assume the radius policy at
$k + 1$ in the radii mode $u$: if $u$ holds, $\delta_{k+1,j} = 1$ for every $j \in [1 : q]$; if
$u$ fails, either $\|s_k\| \ge 1$ or $\delta_{k+1,j} \ge \kappa_\delta \epsilon_j$ for every
$j$, with $\kappa_\delta = \varsigma \theta / (8 (3 \bar L + \sigma_{\max}))$,
$\bar L = \max(1, \max_j L_j)$ and $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_p / (1 -
\eta_2))$. Then $$\Delta T_{f,p}(x_k, s_k) \ge \kappa_{\Delta m} \min_{j \in [1:q]}
\epsilon_j^{\pi_j} \qquad \text{and} \qquad f(x_k) - f(x_{k+1}) \ge \eta_1 \kappa_{\Delta m}
\min_{j \in [1:q]} \epsilon_j^{\pi_j},$$ with $\pi_j = (p+1)/(p-j+1)$ if $u$ holds and
$\pi_j = j(p+1)/p$ if $u$ fails, and $\kappa_{\Delta m}$ the constant of Lemma 12.2.13 in the
same mode (`Optimization.arqpKappaDmOf u`).

**Reading.** As in `CartisGouldToint.Chapter14.lemma_14_2_2_arqp`, the exponents are keyed by
the radii mode, not by $q$ and $X$. -/
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

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqp-SC row under f.D1pLaB.X. Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D1pLaB.X on $X_0$ with the anchor $x_0$, the
starting point of the run, and constants $L_j$, $B_j$, and let $p \ge 1$. Then for an ARqp-SC
run on $X$, every iteration $k$ such that the termination test fails at all iterations before
$k$ satisfies $$k \le \Big(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Big) |\mathcal{S}_k| +
\frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_2} \quad \text{(14.2.13)}, \qquad
\sigma_{\max} = \max\Big(\sigma_0, \frac{\gamma_3 L_p}{1 - \eta_2}\Big),$$ where $\mathcal{S}_k$
is the set of successful iterations in $[0 : k]$.

**Reading.** Explicit prefix count with logarithm of sigma_max/sigma_0 and matching
algorithm-parameter coefficient.
-/
theorem lemma_14_2_3_anchored (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 p L B) (hp : 1 ≤ p)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRho f p x s σ j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂ :=
  h.toIsARRun.le_succ_count hk
    (Optimization.IsARqpRun.sigma_le_of_anchored (hf.toLipschitzDerivsAnchored.mono hp le_rfl)
    hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) h k hk).2

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqp-SC row under f.bB.X and f.D1pLaB.X (the
remark after (14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.bB.X with the bound
$f_{\mathrm{low}}$ and f.D1pLaB.X on $X_0$ with the anchor $x_0$, the starting point of the run,
and constants $L_j$, $B_j$. Let $1 \le q \le p$, $\sigma_{\min} > 0$, $\theta < \varsigma$,
$\epsilon \in (0, 1]^q$ and $\delta_0 \in (0, 1]^q$, and consider an ARqp-SC run on $X$. Assume
the radius policy in the radii mode $u$: if $u$ holds, $\delta_{0,j} = 1$ and
$\delta_{s_k,j} = 1$ for every $j \in [1 : q]$ and every $k$ before termination; if $u$ fails,
$\delta_{s_k,j} \ge \kappa_\delta(\sigma_k) \epsilon_j$ for every $j$ and every $k$ before
termination with $\|s_k\| < 1$, where $\kappa_\delta(\sigma) = \varsigma \theta / (8 (3 \bar L +
\sigma))$ and $\bar L = \max(1, \max_j L_j)$. Then the run terminates at a first iteration
$k_\epsilon$ with $x_{k_\epsilon} \in X$, and there are radii $\delta_\epsilon \in (0, 1]^q$ for
which $x_{k_\epsilon}$ is an $(\epsilon, \delta_\epsilon)$-approximate $q$-th order minimizer on
$X$. With $m_\epsilon = \min_j \epsilon_j^{\pi_j}$, the number of function evaluations is at
most $\kappa^a (f(x_0) - f_{\mathrm{low}}) / m_\epsilon + \kappa^c$ and the number of derivative
evaluations is at most $\kappa^s (f(x_0) - f_{\mathrm{low}}) / m_\epsilon + 2$, with $\pi_j$ and
the constants of `CartisGouldToint.Chapter14.theorem_14_2_4_arqp` in the mode $u$.

**Reading.** As in `CartisGouldToint.Chapter14.theorem_14_2_4_arqp`, the order is keyed by the
radii mode, not by $q$ and $X$.

Runs that satisfy the radius hypothesis of the mode in which $u$ fails exist on
$X = \mathbb{R}^n$ (`Optimization.exists_isARqpRun_of_anchored`); for a general $X$ this
hypothesis is not discharged in this module. -/
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

/-!
### The dynamic-accuracy algorithms with simple constraints

The TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC rows of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4
of [cartis2022evaluation] are instances of the analysis of the runs with a feasible set
(`Optimization.IsTRqIDARun`, …, `Optimization.IsARqpEDARun`; the feasible set `univ` gives the
algorithms of Chapter 13) under `LipschitzDerivsAnchored`. Each row is stated twice: under f.D0qL
(f.D0pL) on an open convex set $C \supseteq X$, that is, `LipschitzDerivsAnchored f C C 0 q L` with
$L_j \ge 1$, and, with the suffix `_anchored`, under the f.D0qLaB.X (f.D0pLaB.X) of the source with
the starting point as anchor. For the IDA algorithms, which have no termination rule, "before
termination" means "before the first iterate that is approximately optimal on $X$". For the
regularization algorithms the radius policy is the radii control `Optimization.ARqpDARadiiControl u`
in either mode: unit radii (if $u$ holds), achievable for $X = \mathbb{R}^n$ with $q \le 2$ or for
$q = 1$ with $X$ convex, or lower bounds of the type (12.2.51) at every order (if $u$ fails),
available in every case. The radii control of Theorem 13.1.19 (`Optimization.RadiiControl`) is the
mode $u = (q \le 2)$.
-/

section TRqIDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C A X₀ : Set ℝⁿ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {L B : ℕ → ℝ} {κΔ : ℝ}


/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqIDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, and let $f$ be $q$ times continuously differentiable near
every point of $C$ with $\|\nabla^j f(x) - \nabla^j f(y)\| \le L_j \|x - y\|$ for $x, y \in C$
and $L_j \ge 1$, for $j \in [0 : q]$ (f.D0qL on $C$). Consider a TRqIDA-SC run on $X$, and let
$\kappa_\Delta$ be admissible: $0 < \kappa_\Delta \le 1$ and $\kappa_\Delta \le \gamma_1 (1 -
\eta_2) / (L_f + 4 (q+1)! \kappa_s \kappa_{\nabla,\max})$, where $L_f = \max_{j \in [0:q]} L_j$
and $\kappa_{\nabla,\max} = \max_i \kappa_{\nabla,i}$. Then every successful iteration $k$ (not
accuracy-improving, with $\rho_k \ge \eta_1$) satisfies $$f(x_k) - f(x_{k+1}) \ge \frac{\eta_1
(\varsigma \kappa_\delta)^{q+1}}{2 \, q!} \epsilon_{\min}^{q+1}, \qquad \kappa_\delta =
\kappa_\Delta / 2.$$

The exponent $\pi_j = q + 1$ is the TRq-SC exponent in (14.2.12).

This is Lemma 13.1.5 with a feasible set. The admissibility of $\kappa_\Delta$ is
`Optimization.IsTRKappaDelta`, and `Optimization.epsMin q ε` is $\epsilon_{\min}$. -/
theorem lemma_14_2_2_trqida (hf : LipschitzDerivsAnchored f C C 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j) (hXC : X ⊆ C)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ} (hk : ¬ acc k)
    (hρ : P.η₁ ≤ trqRatio f D x s jk k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqIDARun.decrease_ge hf hL hXC (fun _ hy _ => hXC hy) hrun
    hκΔ hk).2 hρ

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqIDA-SC row under f.D0qLaB.X (the remark after
(14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0qLaB.X on $X_0$ with the anchor
$x_0$, the starting point of the run, and constants $L_j$, $B_j$. Consider a TRqIDA-SC run on
$X$ from $x_0$, and let $\kappa_\Delta$ be admissible: $0 < \kappa_\Delta \le 1$ and
$\kappa_\Delta \le \gamma_1 (1 - \eta_2) / (L_f + 4 (q+1)! \kappa_s \kappa_{\nabla,\max})$,
where $L_f = \max_{j \in [0:q]} L_j$ and $\kappa_{\nabla,\max} = \max_i \kappa_{\nabla,i}$. Then
every successful iteration $k$ satisfies $$f(x_k) - f(x_{k+1}) \ge \frac{\eta_1 (\varsigma
\kappa_\Delta / 2)^{q+1}}{2 \, q!} \epsilon_{\min}^{q+1}.$$

**Correction.** As in `CartisGouldToint.Chapter14.lemma_14_2_2_trqida`, the exponents are
$\pi_j = q + 1$. -/
theorem lemma_14_2_2_trqida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ} (hk : ¬ acc k)
    (hρ : P.η₁ ≤ trqRatio f D x s jk k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqIDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hrun hκΔ hk).2 hρ


/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqIDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, let $f$ satisfy f.D0qL on $C$ with constants $L_j \ge 1$,
consider a TRqIDA-SC run on $X$, and let $\kappa_\Delta$ be admissible as in
`CartisGouldToint.Chapter14.lemma_14_2_2_trqida`, with $\kappa_\delta = \kappa_\Delta / 2$. Then
every iteration $k$ such that no iterate before $x_k$ is approximately optimal on $X$ satisfies
$$k \le \Big(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\Big) |\mathcal{S}_k| +
\frac{|\log(\varsigma \kappa_\delta \epsilon_{\min} / \Delta_0)|}{|\log \gamma_2|} +
N_{\mathcal{A}} \quad \text{(14.2.13)},$$ where $\mathcal{S}_k$ is the set of successful
iterations in $[0 : k]$ that are not accuracy-improving, and $$N_{\mathcal{A}} =
\frac{q(q+1)}{|\log \gamma_h|} |\log \epsilon_{\min}| + \frac{|\log(\kappa_{\mathrm{acc}} /
\kappa_h)|}{|\log \gamma_h|} + 1$$ bounds the number of accuracy-improving iterations.

**Reading.** The source leaves $\kappa_{\mathrm{unc}}$ implicit and has no termination rule for
TRqIDA. Here $\kappa_{\mathrm{unc}}$ is explicit, it contains $|\log \epsilon_{\min}|$ terms,
and the count holds up to the first approximately optimal iterate.

This is Lemma 13.1.1 with the radius bound of Lemma 13.1.4 and the count of accuracy-improving
iterations of Theorem 13.1.8. The constant $\kappa_{\mathrm{acc}}$ is `Optimization.trKappaAcc`
of $\kappa_\Delta$, $L_f + \kappa_{\nabla,\max} \kappa_h$ and $\kappa_{\nabla,\max}$, and the
approximate optimality test is `Optimization.trqIDATest`. -/
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

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqIDA-SC row under f.D0qLaB.X. Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0qLaB.X on $X_0$ with the anchor $x_0$, the
starting point of the run, and constants $L_j$, $B_j$. Consider a TRqIDA-SC run on $X$ from
$x_0$, and let $\kappa_\Delta$ be admissible as in
`CartisGouldToint.Chapter14.lemma_14_2_2_trqida`, with $\kappa_\delta = \kappa_\Delta / 2$. Then
every iteration $k$ such that no iterate before $x_k$ is approximately optimal on $X$ satisfies
$$k \le \Big(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\Big) |\mathcal{S}_k| +
\frac{|\log(\varsigma \kappa_\delta \epsilon_{\min} / \Delta_0)|}{|\log \gamma_2|} +
N_{\mathcal{A}} \quad \text{(14.2.13)},$$ with $\mathcal{S}_k$ and $N_{\mathcal{A}}$ as in
`CartisGouldToint.Chapter14.lemma_14_2_3_trqida`.

**Reading.** Before first approximately optimal iterate, with explicit logarithmic radius and
accuracy overhead.
-/
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


/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqIDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, let $f$ satisfy f.D0qL on $C$ with constants $L_j \ge 1$,
let $f \ge f_{\mathrm{low}}$ on $X$, consider a TRqIDA-SC run on $X$ from $x_0$, and let
$\kappa_\Delta$ be admissible as in `CartisGouldToint.Chapter14.lemma_14_2_2_trqida`. Then there
is a first iterate $x_{k_\epsilon}$ that is an $(\epsilon, \delta)$-approximate $q$-th order
minimizer on $X$ with the radius $\delta = \min(\Delta_{k_\epsilon}, \vartheta)$, and
$x_{k_\epsilon} \in X$ and $0 < \delta \le 1$. With $c_T = 1 + \log \gamma_3 / |\log \gamma_2|$,
$\kappa^S = 2 \, q! / (\eta_1 (\varsigma \kappa_\Delta / 2)^{q+1})$ and $N = \kappa^S c_T
(f(x_0) - f_{\mathrm{low}}) / \epsilon_{\min}^{q+1}$, the number of function evaluations before
$k_\epsilon$ (one at $x_0$ and one per trial iteration) is at most $$N + \frac{|\log
\epsilon_{\min}|}{|\log \gamma_2|} + \frac{|\log(\varsigma \kappa_\Delta / (2 \Delta_0))|}{|\log
\gamma_2|} + 1,$$ and the number of derivative evaluations (one at $x_0$ and one per successful
or accuracy-improving iteration) is at most $$N + \frac{q(q+1)}{|\log \gamma_h|} |\log
\epsilon_{\min}| + \frac{|\log(\kappa_{\mathrm{acc}} / \kappa_h)|}{|\log \gamma_h|} + 2.$$ So
the order is $O(\max_j \epsilon_j^{-(q+1)})$.

This is Theorem 13.1.8 with a feasible set. The constants are `Optimization.trKappaS` and
`Optimization.trKappaAcc` as in `CartisGouldToint.Chapter14.lemma_14_2_3_trqida`; the counts are
`Optimization.derivEvalCount` of the trial iterations and of the successful or
accuracy-improving iterations.

**Reading.** First approximately optimal iterate and explicit function and derivative counts with
logarithmic overhead.
-/
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

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqIDA-SC row under f.D0qLaB.X (the remark after
(14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0qLaB.X on $X_0$ with the anchor
$x_0$, the starting point of the run, and constants $L_j$, $B_j$, let $f \ge f_{\mathrm{low}}$
on $X$, consider a TRqIDA-SC run on $X$ from $x_0$, and let $\kappa_\Delta$ be admissible as in
`CartisGouldToint.Chapter14.lemma_14_2_2_trqida`. Then there is a first iterate $x_{k_\epsilon}$
that is an $(\epsilon, \delta)$-approximate $q$-th order minimizer on $X$ with
$\delta = \min(\Delta_{k_\epsilon}, \vartheta)$, and $x_{k_\epsilon} \in X$ and
$0 < \delta \le 1$. With $c_T$, $\kappa^S$, $N$ and $\kappa_{\mathrm{acc}}$ as in
`CartisGouldToint.Chapter14.theorem_14_2_4_trqida`, the number of function evaluations is at
most $$N + \frac{|\log \epsilon_{\min}|}{|\log \gamma_2|} + \frac{|\log(\varsigma \kappa_\Delta
/ (2 \Delta_0))|}{|\log \gamma_2|} + 1,$$ and the number of derivative evaluations is at most
$$N + \frac{q(q+1)}{|\log \gamma_h|} |\log \epsilon_{\min}| + \frac{|\log(\kappa_{\mathrm{acc}}
/ \kappa_h)|}{|\log \gamma_h|} + 2.$$

**Reading.** First approximately optimal iterate and explicit function and derivative counts with
logarithmic overhead.
-/
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


/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqEDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, let $f$ satisfy f.D0qL on $C$ with constants $L_j \ge 1$
for $j \in [0 : q]$, consider a TRqEDA-SC run on $X$, and let $\kappa_\Delta$ be admissible with
$\kappa_{\nabla,\max} = 1$: $0 < \kappa_\Delta \le 1$ and $\kappa_\Delta \le \gamma_1 (1 -
\eta_2) / (L_f + 4 (q+1)! \kappa_s)$, where $L_f = \max_{j \in [0:q]} L_j$. Then every
successful iteration $k$ before termination (not accuracy-improving, with the inexact ratio
(13.3.10) at least $\eta_1$) satisfies $$f(x_k) - f(x_{k+1}) \ge \frac{\eta_1 (\varsigma
\kappa_\delta)^{q+1}}{2 \, q!} \epsilon_{\min}^{q+1}, \qquad \kappa_\delta = \kappa_\Delta /
2.$$

The exponent $\pi_j = q + 1$ is the TRq-SC exponent in (14.2.12).

This is Lemma 13.3.2 with a feasible set. The termination test is `Optimization.edaStopTR` and
the ratio is `Optimization.edaRatio`. -/
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

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqEDA-SC row under f.D0qLaB.X (the remark after
(14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0qLaB.X on $X_0$ with the anchor
$x_0$, the starting point of the run, and constants $L_j$, $B_j$. Consider a TRqEDA-SC run on
$X$ from $x_0$, and let $\kappa_\Delta$ be admissible with $\kappa_{\nabla,\max} = 1$, as in
`CartisGouldToint.Chapter14.lemma_14_2_2_trqeda`. Then every successful iteration $k$ before
termination satisfies $$f(x_k) - f(x_{k+1}) \ge \frac{\eta_1 (\varsigma \kappa_\Delta /
2)^{q+1}}{2 \, q!} \epsilon_{\min}^{q+1}.$$

**Correction.** As in `CartisGouldToint.Chapter14.lemma_14_2_2_trqeda`, the exponents are
$\pi_j = q + 1$. -/
theorem lemma_14_2_2_trqeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqEDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hrun hκΔ hk ha).2 hρ


/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqEDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, let $f$ satisfy f.D0qL on $C$ with constants $L_j \ge 1$,
consider a TRqEDA-SC run on $X$, and let $\kappa_\Delta$ be admissible with
$\kappa_{\nabla,\max} = 1$, as in `CartisGouldToint.Chapter14.lemma_14_2_2_trqeda`, with
$\kappa_\delta = \kappa_\Delta / 2$. Then every iteration $k$ such that the termination test
fails at all iterations before $k$ satisfies $$k \le \Big(1 + \frac{\log \gamma_3}{|\log
\gamma_2|}\Big) |\mathcal{S}_k| + \frac{|\log(\varsigma \kappa_\delta \epsilon_{\min} /
\Delta_0)|}{|\log \gamma_2|} + N_{\mathcal{A}} \quad \text{(14.2.13)},$$ where $\mathcal{S}_k$
is the set of successful iterations in $[0 : k]$ that are not accuracy-improving,
$$N_{\mathcal{A}} = \frac{q(q+1)}{|\log \gamma_h|} |\log \epsilon_{\min}| +
\frac{|\log(\kappa_{\mathrm{acc}} / \kappa_h)|}{|\log \gamma_h|} + 1,$$ and
$\kappa_{\mathrm{acc}}$ is `Optimization.trKappaAcc` of $\kappa_\Delta$, $L_f + \kappa_h$ and
$1$, with $L_f = \max_{j \in [0:q]} L_j$.

**Reading.** The source leaves $\kappa_{\mathrm{unc}}$ implicit. Here it is explicit and
contains $|\log \epsilon_{\min}|$ terms.

This is Lemma 13.1.1 with the radius bound of Lemma 13.1.4 for TRqEDA and the count of
accuracy-improving iterations of Theorem 13.3.4. -/
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

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqEDA-SC row under f.D0qLaB.X. Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0qLaB.X on $X_0$ with the anchor $x_0$, the
starting point of the run, and constants $L_j$, $B_j$. Consider a TRqEDA-SC run on $X$ from
$x_0$, and let $\kappa_\Delta$ be admissible with $\kappa_{\nabla,\max} = 1$, with
$\kappa_\delta = \kappa_\Delta / 2$. Then every iteration $k$ such that the termination test
fails at all iterations before $k$ satisfies $$k \le \Big(1 + \frac{\log \gamma_3}{|\log
\gamma_2|}\Big) |\mathcal{S}_k| + \frac{|\log(\varsigma \kappa_\delta \epsilon_{\min} /
\Delta_0)|}{|\log \gamma_2|} + N_{\mathcal{A}} \quad \text{(14.2.13)},$$ with $\mathcal{S}_k$
and $N_{\mathcal{A}}$ as in `CartisGouldToint.Chapter14.lemma_14_2_3_trqeda`.

**Reading.** Explicit prefix bound shows tolerance-dependent radius and accuracy overhead.
-/
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


/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqEDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, let $f$ satisfy f.D0qL on $C$ with constants $L_j \ge 1$,
let $f \ge f_{\mathrm{low}}$ on $X$, consider a TRqEDA-SC run on $X$ from $x_0$, and let
$\kappa_\Delta$ be admissible with $\kappa_{\nabla,\max} = 1$, as in
`CartisGouldToint.Chapter14.lemma_14_2_2_trqeda`. Then the run terminates at a first iteration
$k_\epsilon$ with $x_{k_\epsilon} \in X$, and $x_{k_\epsilon}$ is an
$(\epsilon, \delta)$-approximate $q$-th order minimizer on $X$ with the radius $\delta =
\min(\Delta_{k_\epsilon}, \vartheta) \in (0, 1]$ at every order. With
$c_T = 1 + \log \gamma_3 / |\log \gamma_2|$, $\kappa^S = 2 \, q! / (\eta_1 (\varsigma
\kappa_\Delta / 2)^{q+1})$ and $N = \kappa^S c_T (f(x_0) - f_{\mathrm{low}}) /
\epsilon_{\min}^{q+1}$, the number of inexact function evaluations is at most $$2 N + \frac{2
|\log \epsilon_{\min}|}{|\log \gamma_2|} + 2 \Big(\frac{|\log(\varsigma \kappa_\Delta / (2
\Delta_0))|}{|\log \gamma_2|} + 1\Big),$$ and the number of derivative evaluations is at most
$$N + \frac{q(q+1)}{|\log \gamma_h|} |\log \epsilon_{\min}| + \frac{|\log(\kappa_{\mathrm{acc}}
/ \kappa_h)|}{|\log \gamma_h|} + 2,$$ with $\kappa_{\mathrm{acc}}$ as in
`CartisGouldToint.Chapter14.lemma_14_2_3_trqeda`. So the order is
$O(\max_j \epsilon_j^{-(q+1)})$.

This is Theorem 13.3.4 with a feasible set. The function evaluations are counted by
`Optimization.edaFunEvalCount`.

**Reading.** Explicit first stopping certificate and inexact value and derivative counts, including
logarithmic terms.
-/
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

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqEDA-SC row under f.D0qLaB.X (the remark after
(14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0qLaB.X on $X_0$ with the anchor
$x_0$, the starting point of the run, and constants $L_j$, $B_j$, let $f \ge f_{\mathrm{low}}$
on $X$, consider a TRqEDA-SC run on $X$ from $x_0$, and let $\kappa_\Delta$ be admissible with
$\kappa_{\nabla,\max} = 1$. Then the run terminates at a first iteration $k_\epsilon$ with
$x_{k_\epsilon} \in X$, and $x_{k_\epsilon}$ is an $(\epsilon, \delta)$-approximate $q$-th order
minimizer on $X$ with $\delta = \min(\Delta_{k_\epsilon}, \vartheta) \in (0, 1]$. With $N$ and
$\kappa_{\mathrm{acc}}$ as in `CartisGouldToint.Chapter14.theorem_14_2_4_trqeda`, the number of
inexact function evaluations is at most $$2 N + \frac{2 |\log \epsilon_{\min}|}{|\log
\gamma_2|} + 2 \Big(\frac{|\log(\varsigma \kappa_\Delta / (2 \Delta_0))|}{|\log \gamma_2|} +
1\Big),$$ and the number of derivative evaluations is at most $$N + \frac{q(q+1)}{|\log
\gamma_h|} |\log \epsilon_{\min}| + \frac{|\log(\kappa_{\mathrm{acc}} / \kappa_h)|}{|\log
\gamma_h|} + 2.$$

**Reading.** Explicit first stopping certificate and inexact value and derivative counts, including
logarithmic terms.
-/
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


/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpIDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, and let $f$ be $p$ times continuously differentiable near
every point of $C$ with $\|\nabla^j f(x) - \nabla^j f(y)\| \le L_j \|x - y\|$ for $x, y \in C$
and $L_j \ge 1$, for $j \in [0 : p]$ (f.D0pL on $C$). Consider an ARqpIDA-SC run on $X$, and let
$\bar L = L_f + \kappa_{\nabla,\max} \kappa_h$ with $L_f = \max_{j \in [0:p]} L_j$. Let $k$ be a
successful iteration (not accuracy-improving, with $\rho_k \ge \eta_1$) such that $x_{k+1}$ is
not approximately optimal on $X$, and assume the radii control at $k$ in the mode $u$: if
$\|s_k\| < 1$, then $\delta_{s_k,j} = 1$ for every $j \in [1 : q]$ if $u$ holds, and
$\delta_{s_k,j} \ge \varsigma \theta \epsilon_j / (24 \max(\bar L, \sigma_k))$ for every
$j \in [1 : q]$ if $u$ fails. Then $$f(x_k) - f(x_{k+1}) \ge \frac{\eta_1 \kappa_{\Delta m}}{2}
\min_{j \in [1:q]} \epsilon_j^{\pi_j},$$ with $\pi_j = (p+1)/(p-j+1)$ if $u$ holds and
$\pi_j = j(p+1)/p$ if $u$ fails, and $\kappa_{\Delta m} = \sigma_{\min} c_u / (p+1)!$, where
$c_u$ is the step-length constant of Lemma 13.1.18 in the mode $u$ for $a = 1 - \theta$, $A =
L_p + \sigma_{\max} + 3 \kappa_{\nabla,\max} \kappa_s$ and $\kappa = \varsigma \theta / (24
\max(\bar L, \sigma_{\max}))$, and $\sigma_{\max}$ is the bound (13.1.77).

**Correction.** As in the correction of Lemma 13.1.18, the decrease holds at the successful
iterations that are followed by an iterate that is not approximately optimal.

**Reading.** The table keys the exponents by $q$ and $X$; here they are keyed by the mode of the
radii control. Step 2 guarantees unit radii for $X = \mathbb{R}^n$ with $q \le 2$ or for $q = 1$
with $X$ convex; the lower bounds are available for every $q$ and $X$. The radii control of
Theorem 13.1.19 (`Optimization.RadiiControl`) is the mode $u = (q \le 2)$.

This is Lemma 13.1.18 with a feasible set. The radii control is
`Optimization.ARqpDARadiiControl u`, the exponents are `Optimization.arPiOf u p j`, $c_u$ is
`Optimization.arStepConstOf u q p (1 - θ)` with `Optimization.arConstA` and
`Optimization.arKappaDelta1`, and `Optimization.arqpIDASigmaMax` is $\sigma_{\max}$. Approximate
optimality is `Optimization.arqpIDATest`. -/
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

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpIDA-SC row under f.D0pLaB.X (the remark after
(14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0pLaB.X on $X_0$ with the anchor
$x_0$, the starting point of the run, and constants $L_j$, $B_j$. Consider an ARqpIDA-SC run on
$X$ from $x_0$, let $k$ be a successful iteration such that $x_{k+1}$ is not approximately
optimal on $X$, and assume the radii control at $k$ in the mode $u$, with
$\bar L = L_f + \kappa_{\nabla,\max} \kappa_h$, as in
`CartisGouldToint.Chapter14.lemma_14_2_2_arqpida`. Then $$f(x_k) - f(x_{k+1}) \ge \frac{\eta_1
\kappa_{\Delta m}}{2} \min_{j \in [1:q]} \epsilon_j^{\pi_j},$$ with $\pi_j$ and
$\kappa_{\Delta m}$ as in `CartisGouldToint.Chapter14.lemma_14_2_2_arqpida`.

**Correction.** As in `CartisGouldToint.Chapter14.lemma_14_2_2_arqpida`, the decrease holds at
the successful iterations followed by an iterate that is not approximately optimal. -/
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


/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpIDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, let $f$ satisfy f.D0pL on $C$ with constants $L_j \ge 1$,
and consider an ARqpIDA-SC run on $X$ that satisfies the radii control at every iteration, in
either mode, with $\bar L = L_f + \kappa_{\nabla,\max} \kappa_h$. Then every iteration $k$ such
that no iterate before $x_k$ is approximately optimal on $X$ satisfies $$k \le \Big(1 +
\frac{|\log \gamma_1|}{\log \gamma_2}\Big) |\mathcal{S}_k| +
\frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_2} + N_{\mathcal{A}} \quad \text{(14.2.13)},$$
where $\mathcal{S}_k$ is the set of successful iterations in $[0 : k]$ that are not
accuracy-improving, $\sigma_{\max}$ is the bound (13.1.77) of Lemma 13.1.14, and
$$N_{\mathcal{A}} = \frac{p(q+1)}{|\log \gamma_h|} |\log \epsilon_{\min}| +
\frac{|\log(\kappa_{\mathrm{acc}} / \kappa_h)|}{|\log \gamma_h|} + 1$$ bounds the number of
accuracy-improving iterations.

**Reading.** The source leaves $\kappa_{\mathrm{unc}}$ implicit and has no termination rule for
ARqpIDA. Here $\kappa_{\mathrm{unc}}$ is explicit, it contains $|\log \epsilon_{\min}|$ terms,
and the count holds up to the first approximately optimal iterate.

This is Lemma 13.1.9 with the bound $\sigma_{\max}$ of Lemma 13.1.14 and the count of
accuracy-improving iterations of Theorem 13.1.19. The constant $\kappa_{\mathrm{acc}}$ is
`Optimization.arKappaAcc` of $\kappa^{(1)}_\delta(\sigma_{\max})$, $\bar L$, $\sigma_{\max}$ and
$\kappa_{\nabla,\max}$. -/
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

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpIDA-SC row under f.D0pLaB.X. Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0pLaB.X on $X_0$ with the anchor $x_0$, the
starting point of the run, and constants $L_j$, $B_j$, and consider an ARqpIDA-SC run on $X$
from $x_0$ that satisfies the radii control at every iteration, in either mode. Then every
iteration $k$ such that no iterate before $x_k$ is approximately optimal on $X$ satisfies $$k
\le \Big(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Big) |\mathcal{S}_k| +
\frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_2} + N_{\mathcal{A}} \quad \text{(14.2.13)},$$
with $\mathcal{S}_k$, $\sigma_{\max}$ and $N_{\mathcal{A}}$ as in
`CartisGouldToint.Chapter14.lemma_14_2_3_arqpida`.

**Reading.** Counts only up to first approximately optimal iterate and shows accuracy-improvement
overhead.
-/
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


/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpIDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, let $f$ satisfy f.D0pL on $C$ with constants $L_j \ge 1$,
let $f \ge f_{\mathrm{low}}$ on $X$, and consider an ARqpIDA-SC run on $X$ from $x_0$ that
satisfies the radii control at every iteration in the mode $u$, with
$\bar L = L_f + \kappa_{\nabla,\max} \kappa_h$. Then there is a first iterate $x_{k_\epsilon}$
that is an $(\epsilon, \delta_\epsilon)$-approximate $q$-th order minimizer on $X$ for some
radii $\delta_\epsilon \in (0, 1]^q$, and $x_{k_\epsilon} \in X$. With the decrease $c = \eta_1
\kappa_{\Delta m} \min_j \epsilon_j^{\pi_j} / 2$ of
`CartisGouldToint.Chapter14.lemma_14_2_2_arqpida`, the number of function evaluations before
$k_\epsilon$ is at most $$\Big(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Big) \frac{f(x_0) -
f_{\mathrm{low}}}{c} + \kappa^C, \qquad \kappa^C = \frac{\log(\sigma_{\max}/\sigma_0)}{\log
\gamma_2} + 2 + \frac{|\log \gamma_1|}{\log \gamma_2},$$ and the number of derivative estimates
is at most $(f(x_0) - f_{\mathrm{low}}) / c + \kappa^E |\log \epsilon_{\min}| + \kappa^F + 3$,
with $\kappa^E = p(q+1) / |\log \gamma_h|$ and $\kappa^F = |\log(\kappa_{\mathrm{acc}} /
\kappa_h)| / |\log \gamma_h|$, as in Theorem 13.1.19. Here $\pi_j = (p+1)/(p-j+1)$ if $u$ holds
and $\pi_j = j(p+1)/p$ if $u$ fails.

**Reading.** The table keys the order by $q$ and $X$; here it is keyed by the mode of the radii
control. Step 2 guarantees unit radii for $X = \mathbb{R}^n$ with $q \le 2$ or for $q = 1$ with
$X$ convex; the lower bounds are available for every $q$ and $X$. The radii control of Theorem
13.1.19 (`Optimization.RadiiControl`) is the mode $u = (q \le 2)$.

This is Theorem 13.1.19 with a feasible set. The constants $\sigma_{\max}$ and
$\kappa_{\mathrm{acc}}$ are those of `CartisGouldToint.Chapter14.lemma_14_2_3_arqpida`. -/
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

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpIDA-SC row under f.D0pLaB.X (the remark after
(14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0pLaB.X on $X_0$ with the anchor
$x_0$, the starting point of the run, and constants $L_j$, $B_j$, let $f \ge f_{\mathrm{low}}$
on $X$, and consider an ARqpIDA-SC run on $X$ from $x_0$ that satisfies the radii control at
every iteration in the mode $u$. Then there is a first iterate $x_{k_\epsilon}$ that is an
$(\epsilon, \delta_\epsilon)$-approximate $q$-th order minimizer on $X$ for some radii
$\delta_\epsilon \in (0, 1]^q$, and $x_{k_\epsilon} \in X$. With $c$, $\kappa^C$, $\kappa^E$ and
$\kappa^F$ as in `CartisGouldToint.Chapter14.theorem_14_2_4_arqpida`, the number of function
evaluations is at most $(1 + |\log \gamma_1| / \log \gamma_2) (f(x_0) - f_{\mathrm{low}}) / c +
\kappa^C$, and the number of derivative estimates is at most $(f(x_0) - f_{\mathrm{low}}) / c +
\kappa^E |\log \epsilon_{\min}| + \kappa^F + 3$.

**Reading.** As in `CartisGouldToint.Chapter14.theorem_14_2_4_arqpida`, the order is keyed by
the mode of the radii control. -/
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

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpIDA-SC row on $X = \mathbb{R}^n$ with
$q \le 2$, in either mode of the radii control. Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy
f.D0pL with constants $L_j \ge 1$ and f.bB with the bound $f_{\mathrm{low}}$, and let $q \le 2$.
Consider an ARqpIDA run on $\mathbb{R}^n$ whose radii satisfy the radii control at every
iteration in some mode $u$, in particular in the lower-bound mode. Then the run satisfies the
bounds of `CartisGouldToint.Chapter14.theorem_14_2_4_arqpida` in the unit-radii mode: there is a
first approximately optimal iterate $x_{k_\epsilon}$, the number of function evaluations before
$k_\epsilon$ is at most $(1 + |\log \gamma_1| / \log \gamma_2) (f(x_0) - f_{\mathrm{low}}) / c +
\kappa^C$, and the number of derivative estimates is at most $(f(x_0) - f_{\mathrm{low}}) / c +
\kappa^E |\log \epsilon_{\min}| + \kappa^F + 3$, where $c = \eta_1 \kappa_{\Delta m} \min_j
\epsilon_j^{(p+1)/(p-j+1)} / 2$ with the constant $\kappa_{\Delta m}$ of the unit-radii mode. So
the order is $\max_j \epsilon_j^{-(p+1)/(p-j+1)}$.

This strengthens Theorem 13.1.19 (1), which assumes unit radii. A failure of the criterion
`Optimization.arqpIDATest` (approximate optimality for some radii in $(0, 1]^q$) is a failure at
unit radii, and for $q \le 2$ the bound (13.1.57) on the model transfers to unit radii
(`Optimization.IsARqpIDARun.decrease_ge_unit`), because $\phi^\delta_j / \delta^j$ is
nonincreasing in $\delta$ for $j \le 2$. Hence the bound of
`CartisGouldToint.Chapter14.theorem_14_2_4_arqpida` in the lower-bound mode, of order
$\epsilon^{-2(p+1)/p}$, is not sharp for $q = 2 < p$ on $\mathbb{R}^n$: it exceeds
$\epsilon^{-(p+1)/(p-1)}$. For ARqpEDA, in contrast, the order of the lower-bound mode is
attained on $X = \mathbb{R}^1$
(`CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpeda_otherwise`).

**Reading.** Derives the unit-radius rates for every unconstrained run at orders one and two even
when the recorded radii use the other mode.
-/
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


/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpEDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, let $f$ satisfy f.D0pL on $C$ with constants $L_j \ge 1$
for $j \in [0 : p]$, and consider an ARqpEDA-SC run on $X$ with $\theta < \varsigma / 2$. Let
$\bar L = L_f + \kappa_h$ with $L_f = \max_{j \in [0:p]} L_j$. Let $k$ be a successful iteration
before termination (not accuracy-improving, with the inexact ratio (13.3.19) at least $\eta_1$)
such that $\|s_k\| \ge 1$ or Step 1 at iteration $k + 1$ does not pass all its tests with
unchanged radii, and assume the radii control at $k$ in the mode $u$ with $\bar L$, as in
`CartisGouldToint.Chapter14.lemma_14_2_2_arqpida`. Then $$f(x_k) - f(x_{k+1}) \ge \frac{\eta_1
\kappa'_{\Delta m}}{2} \min_{j \in [1:q]} \epsilon_j^{\pi_j},$$ with $\pi_j = (p+1)/(p-j+1)$ if
$u$ holds and $\pi_j = j(p+1)/p$ if $u$ fails, and $\kappa'_{\Delta m} = \sigma_{\min} c_u /
(p+1)!$, where $c_u$ is the step-length constant in the mode $u$ for
$a = \varsigma / 2 - \theta$, $A = L_p + \sigma_{\max} + 4 \kappa_s$ and $\kappa = \varsigma
\theta / (24 \max(\bar L, \sigma_{\max}))$, and $\sigma_{\max}$ is the bound (13.1.77) with
$\kappa_{\nabla,\max} = 1$.

**Correction.** As in the correction of Lemma 13.3.7, the decrease needs
$\theta < \varsigma / 2$ and holds at the successful iterations of that lemma.

**Reading.** The exponents are keyed by the mode of the radii control, not by $q$ and $X$, as in
`CartisGouldToint.Chapter14.lemma_14_2_2_arqpida`.

This is Lemma 13.3.7 with a feasible set. The constant $A$ is `Optimization.arEDAConstA`, and
Step 1 with unchanged radii is `Optimization.edaPassUnchanged`. -/
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

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpEDA-SC row under f.D0pLaB.X (the remark after
(14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0pLaB.X on $X_0$ with the anchor
$x_0$, the starting point of the run, and constants $L_j$, $B_j$, and consider an ARqpEDA-SC run
on $X$ from $x_0$ with $\theta < \varsigma / 2$. Let $k$ be a successful iteration before
termination such that $\|s_k\| \ge 1$ or Step 1 at iteration $k + 1$ does not pass with
unchanged radii, and assume the radii control at $k$ in the mode $u$ with
$\bar L = L_f + \kappa_h$. Then $$f(x_k) - f(x_{k+1}) \ge \frac{\eta_1 \kappa'_{\Delta m}}{2}
\min_{j \in [1:q]} \epsilon_j^{\pi_j},$$ with $\pi_j$ and $\kappa'_{\Delta m}$ as in
`CartisGouldToint.Chapter14.lemma_14_2_2_arqpeda`.

**Correction.** As in `CartisGouldToint.Chapter14.lemma_14_2_2_arqpeda`, the decrease needs
$\theta < \varsigma / 2$. -/
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


/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpEDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, let $f$ satisfy f.D0pL on $C$ with constants $L_j \ge 1$,
and consider an ARqpEDA-SC run on $X$ that satisfies the radii control at every iteration, in
either mode, with $\bar L = L_f + \kappa_h$. Then every iteration $k$ such that the termination
test fails at all iterations before $k$ satisfies $$k \le \Big(1 + \frac{|\log \gamma_1|}{\log
\gamma_2}\Big) |\mathcal{S}_k| + \frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_2} +
N_{\mathcal{A}} \quad \text{(14.2.13)},$$ where $\mathcal{S}_k$ is the set of successful
iterations in $[0 : k]$ that are not accuracy-improving, $\sigma_{\max}$ is the bound of Lemma
13.3.5 (the bound (13.1.77) with $\kappa_{\nabla,\max} = 1$), and $$N_{\mathcal{A}} =
\frac{p(q+1)}{|\log \gamma_h|} |\log \epsilon_{\min}| + \frac{|\log(\kappa_{\mathrm{acc}} /
\kappa_h)|}{|\log \gamma_h|} + 1.$$

**Reading.** The source leaves $\kappa_{\mathrm{unc}}$ implicit. Here it is explicit and
contains $|\log \epsilon_{\min}|$ terms.

This is Lemma 13.1.9 with the bound $\sigma_{\max}$ of Lemma 13.3.5 and the count of
accuracy-improving iterations of Theorem 13.3.8. The constant $\kappa_{\mathrm{acc}}$ is
`Optimization.arKappaAcc` of $\kappa^{(1)}_\delta(\sigma_{\max})$, $\bar L$, $\sigma_{\max}$ and
$1$. -/
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

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpEDA-SC row under f.D0pLaB.X. Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0pLaB.X on $X_0$ with the anchor $x_0$, the
starting point of the run, and constants $L_j$, $B_j$, and consider an ARqpEDA-SC run on $X$
from $x_0$ that satisfies the radii control at every iteration, in either mode. Then every
iteration $k$ such that the termination test fails at all iterations before $k$ satisfies $$k
\le \Big(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Big) |\mathcal{S}_k| +
\frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_2} + N_{\mathcal{A}} \quad \text{(14.2.13)},$$
with $\mathcal{S}_k$, $\sigma_{\max}$ and $N_{\mathcal{A}}$ as in
`CartisGouldToint.Chapter14.lemma_14_2_3_arqpeda`.

**Reading.** Explicit prefix bound includes accuracy-improving iterations and logarithmic dependence
on tolerance.
-/
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


/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpEDA-SC row. Let $C \subseteq \mathbb{R}^n$ be
open and convex with $X \subseteq C$, let $f$ satisfy f.D0pL on $C$ with constants $L_j \ge 1$,
let $f \ge f_{\mathrm{low}}$ on $X$, let $\theta < \varsigma / 2$, and consider an ARqpEDA-SC
run on $X$ from $x_0$ that satisfies the radii control at every iteration in the mode $u$, with
$\bar L = L_f + \kappa_h$. Then the run terminates at a first iteration $k_\epsilon$ with
$x_{k_\epsilon} \in X$, the radii $\delta^{(1)}_{k_\epsilon}$ lie in $(0, 1]^q$, and
$x_{k_\epsilon}$ is an $(\epsilon, \delta^{(1)}_{k_\epsilon})$-approximate $q$-th order
minimizer on $X$. Let $c = \eta_1 \kappa'_{\Delta m} \min_j \epsilon_j^{\pi_j} / 2$ be the
decrease of `CartisGouldToint.Chapter14.lemma_14_2_2_arqpeda`,
$N = (f(x_0) - f_{\mathrm{low}}) / c$, $M = p(q+1) |\log \epsilon_{\min}| / |\log \gamma_h| +
|\log(\kappa_{\mathrm{acc}} / \kappa_h)| / |\log \gamma_h| + 1$ and
$c_T = 1 + |\log \gamma_1| / \log \gamma_2$. Then the number of inexact function evaluations is
at most $$2 \Big((N + M + 1) c_T + \frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_2}\Big),$$
and the number of derivative estimates is at most $N + 2M + 2$, as in Theorem 13.3.8. Here
$\pi_j = (p+1)/(p-j+1)$ if $u$ holds and $\pi_j = j(p+1)/p$ if $u$ fails.

**Reading.** The table keys the order by $q$ and $X$; here it is keyed by the mode of the radii
control. Step 2 guarantees unit radii for $X = \mathbb{R}^n$ with $q \le 2$ or for $q = 1$ with
$X$ convex; the lower bounds are available for every $q$ and $X$. The radii control of Theorem
13.1.19 (`Optimization.RadiiControl`) is the mode $u = (q \le 2)$.

This is Theorem 13.3.8 with a feasible set. The constants $\sigma_{\max}$ and
$\kappa_{\mathrm{acc}}$ are those of `CartisGouldToint.Chapter14.lemma_14_2_3_arqpeda`. -/
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

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpEDA-SC row under f.D0pLaB.X (the remark after
(14.2.10)). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D0pLaB.X on $X_0$ with the anchor
$x_0$, the starting point of the run, and constants $L_j$, $B_j$, let $f \ge f_{\mathrm{low}}$
on $X$, let $\theta < \varsigma / 2$, and consider an ARqpEDA-SC run on $X$ from $x_0$ that
satisfies the radii control at every iteration in the mode $u$. Then the run terminates at a
first iteration $k_\epsilon$ with $x_{k_\epsilon} \in X$, the radii $\delta^{(1)}_{k_\epsilon}$
lie in $(0, 1]^q$, and $x_{k_\epsilon}$ is an
$(\epsilon, \delta^{(1)}_{k_\epsilon})$-approximate $q$-th order minimizer on $X$. With $N$, $M$
and $c_T$ as in `CartisGouldToint.Chapter14.theorem_14_2_4_arqpeda`, the number of inexact
function evaluations is at most $2 ((N + M + 1) c_T + \log(\sigma_{\max}/\sigma_0) / \log
\gamma_2)$, and the number of derivative estimates is at most $N + 2M + 2$.

**Reading.** As in `CartisGouldToint.Chapter14.theorem_14_2_4_arqpeda`, the order is keyed by
the mode of the radii control. -/
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

/-!
### Sharpness of the orders of Theorem 14.2.4

"The orders of complexity mentioned in the last column of the table are sharp"
([cartis2022evaluation], Theorem 14.2.4). Each row is attained by a slow example, run with a simple
feasible set: $X = \mathbb{R}$, $X = \mathbb{R}^1$, or a closed nonconvex $X$ for the "otherwise"
entries that the reduction to $X = \mathbb{R}^n$ does not reach.
-/

section Sharp

open Chapter13 Optimization

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the TRq-SC row, of the ARqp-SC row
for $q \le 2$, and of the ARqpC-SC row for $q = 1$ and convex $h$. Let $q \ge 1$.

(TRq-SC, order $\epsilon^{-(q+1)}$.) There are $f_{\mathrm{low}}$ and $L \ge 1$ such that for
every $\epsilon \in (0, 1/q!]$ and all TRq parameters with $\Delta_0 = \epsilon$ there is
$f : \mathbb{R} \to \mathbb{R}$ with $f \ge f_{\mathrm{low}}$ and f.D1pL of order $q$ with all
constants $L$, and a TRq-SC run on $X = \mathbb{R}$ with tolerances
$\epsilon_j = j! \, \epsilon$ and $\vartheta = 1$ that terminates first at
$k_\epsilon = \lceil \epsilon^{-(q+1)} \rceil$, after at least $\epsilon^{-(q+1)} + 1$ function
evaluations.

(ARqp-SC, order $\epsilon^{-(p+1)/(p-q+1)}$.) If $q \le 2$ and $q \le p$, there are
$f_{\mathrm{low}}$ and $L \ge 1$ such that for every $\epsilon \in (0, 1]$ and all ARqp
parameters with $\sigma_0 = p!/(q-1)!$ there is $f : \mathbb{R} \to \mathbb{R}$ with
$f \ge f_{\mathrm{low}}$ and f.D1pL of order $p$ with all constants $L$, and an ARqp-SC run on
$X = \mathbb{R}$ with $\epsilon_j = \epsilon$ and all radii $1$ that terminates first at
$k_\epsilon = \lceil \epsilon^{-(p+1)/(p-q+1)} \rceil$.

(ARqpC-SC, order $\epsilon^{-(p+1)/p}$.) If $p \ge 1$, then for all ARqpC parameters there is
$L \ge 1$ such that for every $\epsilon \in (0, 1]$ there is $c : \mathbb{R}^1 \to \mathbb{R}^1$
with c.D1pL with all constants $L$ and $\|c(0)\| \le L$, for which $w = \|c\|$ (that is, $f = 0$
and $h = \|\cdot\|$) satisfies w.Bb with the bound $0$, and an ARqpC-SC run on
$X = \mathbb{R}^1$ with $q = 1$, $\epsilon_1 = \epsilon$ and $\delta_{0,1} = 1$ that terminates
first at $k_\epsilon = \lceil \epsilon^{-(p+1)/p} \rceil$, after at least
$\epsilon^{-(p+1)/p} + 1$ function evaluations.

The examples are those of Theorem 12.2.6, Corollary 12.2.16 and Corollary 14.1.11, with the
feasible set `univ`. In the ARqpC-SC part the constant $L$ depends on the parameters. The
ARqp-SC row for $q \ge 3$ is `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqp`; the
dynamic-accuracy rows are `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_trqida`,
`CartisGouldToint.Chapter14.theorem_14_2_4_sharp_trqeda`,
`CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida`,
`CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpeda`,
`CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpeda_otherwise` and
`CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida_otherwise`. -/
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

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqp-SC row for $q \ge 3$, with
the "otherwise" order $\epsilon^{-q(p+1)/p}$. Let $3 \le q \le p$. There are $f_{\mathrm{low}}$
and $L \ge 1$ such that for every $\epsilon \in (0, 1/2]$ and all ARqp parameters with
$\sigma_0$ the weight (12.2.85) there is $f : \mathbb{R} \to \mathbb{R}$ with
$f \ge f_{\mathrm{low}}$ and f.D1pL of order $p$ with all constants $L$, and an ARqp-SC run on
$X = \mathbb{R}$ with $\epsilon_j = \epsilon$ and all radii $\epsilon$, such that:

* the run satisfies the radius hypothesis of the lower-bound mode of
  `CartisGouldToint.Chapter14.theorem_14_2_4_arqp`, $\delta_{s_k,j} \ge \kappa_\delta(\sigma_k)
  \epsilon_j$, at every iteration $k$ before termination with $\|s_k\| < 1$;
* the run terminates first at $k_\epsilon = \lceil \epsilon^{-q(p+1)/p} \rceil$, after at least
  $\epsilon^{-q(p+1)/p} + 1$ function evaluations.

The example is that of Theorem 12.2.17, with the feasible set `univ`. The weight (12.2.85) is
`CartisGouldToint.Chapter12.arqpSigmaSharp p q`. -/
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

/-!
### Sharpness of the ARqp-SC row in the lower-bound mode with a constrained feasible set

The slow example of Theorem 12.2.17 of [cartis2022evaluation] never leaves a half-line, so it is
also an ARqp-SC run on a closed nonconvex set $X \subset \mathbb{R}$ with $X \neq \mathbb{R}$. This
reaches the "otherwise" entries of the table for $q \le 2$.
-/

section ARqpOtherwise

open Optimization

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqp-SC row in the lower-bound
mode of the radius policy, with the "otherwise" order $\epsilon^{-q(p+1)/p}$, on a closed
nonconvex feasible set. Let $1 \le q \le p$. There are $f_{\mathrm{low}}$ and $L \ge 1$ such
that for every $\epsilon \in (0, 1/2]$ and all ARqp parameters with $\sigma_0$ the weight
(12.2.85) there are $R \in \mathbb{R}$, $f : \mathbb{R} \to \mathbb{R}$ with
$f \ge f_{\mathrm{low}}$ and f.D1pL of order $p$ with all constants $L$, and an ARqp-SC run on
$$X = (-\infty, R] \cup [R + 2, \infty)$$ with $\epsilon_j = \epsilon$ and all radii $\epsilon$,
such that the run satisfies the radius hypothesis of the lower-bound mode of
`CartisGouldToint.Chapter14.theorem_14_2_4_arqp` ($\delta_{s_k,j} \ge \kappa_\delta(\sigma_k)
\epsilon_j$ at every iteration $k$ before termination with $\|s_k\| < 1$), and terminates first
at $k_\epsilon = \lceil \epsilon^{-q(p+1)/p} \rceil$, after at least $\epsilon^{-q(p+1)/p} + 1$
function evaluations.

The run is the slow example of Theorem 12.2.17 with $r = p$, which stays in $(-\infty, R]$
together with its displacements, so it is a run on $X$. This covers the "otherwise" entries of
the table for $q = 1$ (nonconvex $X$) and $q = 2$ ($X \neq \mathbb{R}^n$), which the source's
reduction to $X = \mathbb{R}^n$ does not reach. For $q > 2$ it complements
`CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqp`, which uses $X = \mathbb{R}$.

**Reading.** Exhibits the rate for all positive q by imposing the small-radius mode directly,
including in unconstrained cases.
-/
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

/-!
### Sharpness of the dynamic-accuracy rows

The orders of the TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC rows are attained by the slow runs
of these methods with exact derivatives (and values) in
`Numlib.Optimization.Complexity.SlowExample.TRqDARun`,
`Numlib.Optimization.Complexity.SlowExample.ARqpDARun` and
`Numlib.Optimization.Complexity.SlowExample.ARqpDASlitRun`. The assumption f.D0qL is
`LipschitzDerivsAnchored f univ univ 0 q (fun _ => L)` with $L \ge 1$.
-/

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the TRqIDA-SC row, with the order
$\epsilon^{-(q+1)}$. Let $q \ge 1$. There are $f_{\mathrm{low}}$ and $L \ge 1$ such that for
every $\epsilon \in (0, 1/q!]$ and all TRqIDA parameters with order $q$,
$\Delta_0 = \vartheta = \epsilon$ and initial accuracies $h_{0,i} \le \kappa_s \epsilon^{q-i+1}$
for $i \in [1 : q]$, there are $f : \mathbb{R}^1 \to \mathbb{R}$ with $f \ge f_{\mathrm{low}}$
and f.D0qL with all constants $L$, and a TRqIDA-SC run on $X = \mathbb{R}^1$ with
$\kappa_{\nabla,i} = 0$, tolerances $\epsilon_j = j! \, \epsilon$ and $x_0 = 0$, whose jets are
the exact Taylor jets, such that the first iterate that is $(\epsilon, \delta_k)$-approximately
optimal is $x_{k_\epsilon}$ with $k_\epsilon = \lceil \epsilon^{-(q+1)} \rceil$, and both the
number of function evaluations and the number of derivative evaluations before $k_\epsilon$ are
at least $\epsilon^{-(q+1)} + 1$.

**Reading.** The slow example of Theorem 12.2.6 is a run of TRqIDA only for suitable constants:
$\vartheta = \Delta_0 = \epsilon$ is forced by $\epsilon_{\min} \le \vartheta \le \Delta_0$, and
the initial accuracies must pass (13.1.9) along the steps. TRqIDA has no termination rule; the
run is continued after $k_\epsilon$ by an arbitrary run from $x_{k_\epsilon}$.

The run follows the slow example of Theorem 12.2.6 ($x_k = k \epsilon e_1$,
$\Delta_k = \epsilon$, $\rho_k = 1$, no accuracy-improving iteration) up to $k_\epsilon$, and
continues as any run from $x_{k_\epsilon}$ (`Optimization.exists_trqDA_run`). With
$\kappa_{\nabla,i} = 0$ the accuracy condition (13.1.2) asks for zero error. This is
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
  exact ⟨f, hb, AssumptionD0qL.of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the TRqEDA-SC row, with the order
$\epsilon^{-(q+1)}$. Let $q \ge 1$. There are $f_{\mathrm{low}}$ and $L \ge 1$ such that for
every $\epsilon \in (0, 1/q!]$ and all TRqEDA parameters with order $q$,
$\Delta_0 = \vartheta = \epsilon$, $\kappa_s \le \min(\eta_1, 1 - \eta_2)/4$ (13.3.5), initial
accuracies $h_{0,i} \le \kappa_s \epsilon^{q-i+1}$ for $i \in [1 : q]$ and $$\sum_{i=1}^q
\frac{h_{0,i} \epsilon^i}{i!} \le \frac{\varsigma \epsilon}{2} \frac{\epsilon^q}{q!},$$ there
are $f : \mathbb{R}^1 \to \mathbb{R}$ with $f \ge f_{\mathrm{low}}$ and f.D0qL with all
constants $L$, and a TRqEDA-SC run on $X = \mathbb{R}^1$ with tolerances
$\epsilon_j = j! \, \epsilon$ and $x_0 = 0$, with exact jets and exact function values, that
terminates first at $k_\epsilon = \lceil \epsilon^{-(q+1)} \rceil$, after at least
$2 \epsilon^{-(q+1)}$ function evaluations (each value recomputed) and at least
$\epsilon^{-(q+1)} + 1$ derivative evaluations.

**Reading.** The slow example of Theorem 12.2.6 is a run of TRqEDA only for suitable constants:
$\vartheta = \Delta_0 = \epsilon$, initial accuracies that pass (13.1.9) along the steps of
length $\epsilon$, and the termination test (13.3.8) at radius $\epsilon$. The tests (13.1.14)
and (13.3.7) have half the threshold of the TRq test, so TRqEDA is run on $f/2$ to make it
terminate at $k_\epsilon$.

The run is the slow example of Theorem 12.2.6 with $f$ halved ($x_k = k \epsilon e_1$,
$\Delta_k = \epsilon$, $\rho_k = 1$, no accuracy-improving iteration). This is
`Optimization.exists_isTRqEDARun_slow`. -/
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
  exact ⟨f, hb, AssumptionD0qL.of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpIDA-SC row for
$q \in \{1, 2\}$, with the order $\epsilon^{-(p+1)/(p-q+1)}$ of the unit-radii mode. Let
$1 \le q \le \min(2, p)$. There are $f_{\mathrm{low}}$, $L \ge 1$ and $\epsilon_0 > 0$ such that
for every $\epsilon \in (0, \epsilon_0]$ and all ARqpIDA parameters with orders $p$ and $q$,
$\sigma_0 = p!/(q-1)!$, unit initial radii and initial accuracies
$0 < h_{0,i} \le \kappa_s (\epsilon/2)^{p-i+1}$ for $i \in [1 : p]$, there are
$f : \mathbb{R}^1 \to \mathbb{R}$ with $f \ge f_{\mathrm{low}}$ and f.D0pL with all constants
$L$, and an ARqpIDA-SC run on $X = \mathbb{R}^1$ with $\kappa_{\nabla,i} = 0$,
$\epsilon_j = \epsilon$ and $x_0 = 0$, whose jets are the exact Taylor jets, such that:

* the run satisfies the radii control in both modes and for every $\bar L \ge 1$ (unit radii
  after every short trial step);
* the first iterate that is $(\epsilon, \delta)$-approximately optimal for some radii
  $\delta \in (0, 1]^q$ is $x_{k_\epsilon}$ with $k_\epsilon = \lceil \epsilon^{-(p+1)/(p-q+1)}
  \rceil$;
* the numbers of function and of derivative evaluations before $k_\epsilon$ are at least
  $\epsilon^{-(p+1)/(p-q+1)} + 1$.

For $q = 1$ and for $q = p = 2$ the order is also the order $\epsilon^{-q(p+1)/p}$ of the
lower-bound mode.

**Reading.** The slow runs of Chapter 12 are not runs of the regularization steps of Chapter 13:
the Step-1 test (13.1.53) has half the threshold of the ARqp test, and the model-decrease
condition (13.1.54) can fail at the Step-1 displacements. Here the Step-1 radius of order $q$ is
halved from $1$ to a dyadic radius $2^{-m}$ at the scale of the step, where (13.1.54) holds
while it fails at twice that radius. This requires $\epsilon \le \epsilon_0(p, q)$, and the
initial accuracies must pass (13.1.46) along the steps.

The run follows the slow example of Theorem 12.2.15 (spike jets
$f^{(q)}(x_k) = -(\epsilon + \omega_k)$, steps the global model minimizers,
$\sigma_k = \sigma_0$, $\rho_k = 1$, no accuracy-improving iteration) up to $k_\epsilon$, and
continues as any run from $x_{k_\epsilon}$ (`Optimization.exists_arqpDA_steps`). This is
`Optimization.exists_isARqpIDARun_slow`. -/
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
  exact ⟨f, hb, AssumptionD0qL.of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpEDA-SC row for
$q \in \{1, 2\}$, with the order $\epsilon^{-(p+1)/(p-q+1)}$ of the unit-radii mode. Let
$1 \le q \le \min(2, p)$. There are $f_{\mathrm{low}}$, $L \ge 1$ and $\epsilon_0 > 0$ such that
for every $\epsilon \in (0, \epsilon_0]$ and all ARqpEDA parameters with orders $p$ and $q$,
$\sigma_0 = p!/(q-1)!$, unit initial radii, $\kappa_s \le \min(\eta_1, 1 - \eta_2)/4$ (13.3.13),
initial accuracies $h_{0,i} \le \kappa_s (\epsilon/2)^{p-i+1}$ for $i \in [1 : p]$, and
$$\sum_{i=1}^j \frac{h_{0,i}}{i!} \le \frac{\varsigma \epsilon}{2 \, j!} \qquad (j \in [1 :
q]),$$ there are $f : \mathbb{R}^1 \to \mathbb{R}$ with $f \ge f_{\mathrm{low}}$ and f.D0pL with
all constants $L$, and an ARqpEDA-SC run on $X = \mathbb{R}^1$ with $\epsilon_j = \epsilon$ and
$x_0 = 0$, with exact jets and exact function values, such that:

* the run satisfies the radii control in both modes and for every $\bar L \ge 1$;
* the run terminates first at $k_\epsilon = \lceil \epsilon^{-(p+1)/(p-q+1)} \rceil$;
* the number of function evaluations is at least $2 \epsilon^{-(p+1)/(p-q+1)}$ (each value
  recomputed), and the number of derivative evaluations is at least
  $\epsilon^{-(p+1)/(p-q+1)} + 1$.

For $q = 1$ and for $q = p = 2$ the order is also the order $\epsilon^{-q(p+1)/p}$ of the
lower-bound mode.

**Reading.** As in `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida`, the Step-1 radius
of order $q$ is halved to the scale of the step. ARqpEDA is run on $f/2$ so that the test
(13.1.53), whose threshold is half that of ARqp, passes exactly at $k_\epsilon$, and the initial
accuracies must pass (13.1.46) along the steps and (13.3.17) at termination.

The run is the slow example of Theorem 12.2.15 with $f$ halved (spike jets
$f^{(q)}(x_k) = -(\epsilon + \omega_k)/2$, steps the global model minimizers,
$\sigma_k = \sigma_0$, $\rho_k = 1$, no accuracy-improving iteration). This is
`Optimization.exists_isARqpEDARun_slow`. -/
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
  exact ⟨f, hb, AssumptionD0qL.of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpEDA-SC row in the lower-bound
mode of the radii control, with the "otherwise" order $\epsilon^{-q(p+1)/p}$. Let
$1 \le q \le p$. There are $f_{\mathrm{low}}$, $L \ge 1$ and $\epsilon_0 > 0$ such that for
every $\epsilon \in (0, \epsilon_0]$ and all ARqpEDA parameters with orders $p$ and $q$, weight
$\sigma_0 = (3/(p+2))^p / 2$, initial radii $\delta_{0,j} = \epsilon$,
$\kappa_s \le \min(\eta_1, 1 - \eta_2)/4$ (13.3.13), initial accuracies
$h_{0,i} \le \kappa_s \epsilon^{p-i+1}$ for $i \in [1 : p]$, and $$\sum_{i=1}^j \frac{h_{0,i}
\epsilon^i}{i!} \le \frac{\varsigma \epsilon}{2} \frac{\epsilon^j}{j!} \qquad (j \in [1 : q]),$$
there are $f : \mathbb{R}^1 \to \mathbb{R}$ with $f \ge f_{\mathrm{low}}$ and f.D0pL with all
constants $L$, and an ARqpEDA-SC run on $X = \mathbb{R}^1$ with $\epsilon_j = \epsilon$ and
$x_0 = 0$, with exact jets and exact function values, such that:

* the run satisfies the radii control in the lower-bound mode for every $\bar L \ge 1$ (all
  radii are $\epsilon$);
* the run terminates first at $k_\epsilon = \lceil \epsilon^{-q(p+1)/p} \rceil$;
* the number of function evaluations is at least $2 \epsilon^{-q(p+1)/p}$ (each value
  recomputed), and the number of derivative evaluations is at least $\epsilon^{-q(p+1)/p} + 1$.

**Reading.** The slow run of Theorem 12.2.17 is not a run of the regularization steps of Chapter
13: the model-decrease condition (13.1.54) can fail at the Step-1 displacements. For the example
of Theorem 12.2.17 with $p = q = 3$ and $\varsigma = 1$, near $k_\epsilon$, the model decrease
is $5 \epsilon^4 / 192 < \epsilon^4 / 24$. Here the weight is $\sigma_0 = (3/(p+2))^p / 2$
instead of (12.2.85), the Step-1 displacements achieve exactly the fraction $\varsigma$ of the
measures, and ARqpEDA is run on $f/2$ so that it terminates at $k_\epsilon$.

The run is the slow example of Theorem 12.2.17 (with $r = p$) with $f$ halved and a smaller
weight: gradient spikes $f'(x_k) = -\beta_k / 2$ with $\beta_k = (\epsilon^q + \omega_k)/q!$,
steps the global model minimizers, $\sigma_k = \sigma_0$, $\rho_k = 1$, and no
accuracy-improving iteration. The weight is small enough for (13.1.54) to hold at the Step-1
displacements, unlike the weight (12.2.85), and for the measures of the model at its minimizer
to vanish at radius $\epsilon$ (Example 12.1.3). This is
`Optimization.exists_isARqpEDARun_slowGrad`. -/
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
  exact ⟨f, hb, AssumptionD0qL.of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpIDA-SC row in the lower-bound
mode of the radii control for $q = p \ge 3$, with the "otherwise" order $\epsilon^{-q(p+1)/p}$,
here $\epsilon^{-(p+1)}$. Let $p \ge 3$. There are $f_{\mathrm{low}}$, $L \ge 1$ and
$\epsilon_0 > 0$ such that for every $\epsilon \in (0, \epsilon_0]$ and all ARqpIDA parameters
with $q = p$, weight $\sigma_0 = p$, initial radii $\delta_{0,j} = \epsilon$ and initial
accuracies $0 < h_{0,i} \le \kappa_s \epsilon^{p-i+1}$ for $i \in [1 : p]$, there are
$f : \mathbb{R}^1 \to \mathbb{R}$ with $f \ge f_{\mathrm{low}}$ and f.D0pL with all constants
$L$, and an ARqpIDA-SC run on $X = \mathbb{R}^1$ with $\kappa_{\nabla,i} = 0$,
$\epsilon_j = \epsilon$ and $x_0 = 0$, whose jets are the exact Taylor jets, such that:

* the run satisfies the radii control in the lower-bound mode with $\bar L = L$;
* the first iterate that is $(\epsilon, \delta)$-approximately optimal for some radii
  $\delta \in (0, 1]^q$ is $x_{k_\epsilon}$ with $k_\epsilon = \lceil \epsilon^{-(p+1)} \rceil$;
* the numbers of function and of derivative evaluations before $k_\epsilon$ are at least
  $\epsilon^{-(p+1)} + 1$.

**Reading.** The slow runs of Chapter 12 are not runs of the regularization steps of Chapter 13.
Here the weight is $\sigma_0 = p$, the initial radii are $\epsilon$, and the Step-2 radii are
$\epsilon / p$.

The run follows the slow example of Theorem 12.2.15 with $q = p$: pure $p$-th order spikes
$f^{(p)}(x_k) = -(\epsilon + \omega_k)$, which fail the criterion at every radius, steps the
global model minimizers $t^*_k = \epsilon + \omega_k$, $\sigma_k = \sigma_0$ and $\rho_k = 1$.
At the Step-2 radii $\delta_{s_k} = \epsilon / p$ the model measures at the minimizer vanish
(`Optimization.taylorMeasure_topMonomialRegModel_eq_zero`). After $k_\epsilon$ the run continues
as any ARqpIDA iteration from the state at $k_\epsilon$ (`Optimization.exists_arqpDA_steps`).
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
  exact ⟨f, hb, AssumptionD0qL.of_lipschitzDerivsAnchored hf hL, H⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpIDA-SC row in the lower-bound
mode of the radii control, with the "otherwise" order $\epsilon^{-q(p+1)/p}$, on a closed
nonconvex feasible set in $\mathbb{R}^2$. Let $1 \le q \le p$. There are $f_{\mathrm{low}}$,
$L \ge 1$ and $\epsilon_0 > 0$ such that for every $\epsilon \in (0, \epsilon_0]$ and all
ARqpIDA parameters with orders $p$ and $q$, weight $\sigma_0 = (3/(p+2))^p$, initial radii
$\delta_{0,j} = \epsilon$ and initial accuracies $h_{0,i} \le \kappa_s \epsilon^{p-i+1}$ for
$i \in [1 : p]$, there are $\rho \in (\epsilon, 2\epsilon]$, the closed set $$X = \{v \in
\mathbb{R}^2 : v_2 = 0\} \cup \{v \in \mathbb{R}^2 : v_2 \ge \rho\},$$ a line and a parallel
half-plane at distance $\rho$, a function $f : \mathbb{R}^2 \to \mathbb{R}$ with
$f \ge f_{\mathrm{low}}$ and f.D0pL with all constants $L$, and an ARqpIDA-SC run on $X$ with
$\kappa_{\nabla,i} = 0$, $\epsilon_j = \epsilon$ and $x_0 = 0$, whose jets are the exact Taylor
jets, such that:

* the run satisfies the radii control in the lower-bound mode for every $\bar L \ge 1$ (all
  radii are $\epsilon$);
* the first iterate that is $(\epsilon, \delta)$-approximately optimal on $X$ for some radii
  $\delta \in (0, 1]^q$ is $x_{k_\epsilon}$ with $k_\epsilon = \lceil \epsilon^{-q(p+1)/p}
  \rceil$;
* the numbers of function and of derivative evaluations before $k_\epsilon$ are at least
  $\epsilon^{-q(p+1)/p} + 1$.

**Reading.** The criterion `Optimization.arqpIDATest` asks for approximate optimality for some
radii, and on the line alone the gradient spikes $\beta_k \approx \epsilon^q / q!$ meet it at
radius $1$. The second coordinate and the half-plane make every radius $\delta \ge \rho$ fail,
while the radii $\delta < \rho$, including the radii $\epsilon$ of the algorithm, only see the
line. The weight is $(3/(p+2))^p$ and all radii are $\epsilon$.

The run follows the slow example of Theorem 12.2.17 ($r = p$) on the line $v_2 = 0$, with
$f(v) = G(v_1) + H(v_2)$, gradient spikes $G'(x_k) = -\beta_k$, $\beta_k = (\epsilon^q +
\epsilon^q (k_\epsilon - k) / k_\epsilon) / q!$, steps the minimizers of the model on the line,
$\sigma_k = \sigma_0$, $\rho_k = 1$, and $H'(0) = -1$, so that the half-plane lowers the Taylor
models by at least $\rho > \epsilon$. The steps are admissible Step-2 steps, since
(13.1.55)–(13.1.57) are local conditions, but they are not global minimizers of the model on
$X$, which lie in the half-plane. Radii $\delta < \rho$ only see the line, where the measure of
order $q$ is $\beta_k \delta$. With $\rho^m = \epsilon^m (1 + 1/k_\epsilon)$,
$m = \max(q - 1, 1)$, this measure exceeds $\epsilon \delta^q / q!$ for every $\delta < \rho$
exactly when $k < k_\epsilon$, and radii $\delta \ge \rho$ reach the half-plane. So the
criterion fails at every radius before $k_\epsilon$, while the Step-1 and Step-2 radii
$\epsilon < \rho$ only see the line, where the model measures at the steps vanish (Example
12.1.3). After $k_\epsilon$ one more step reaches a point where all derivatives of $G$ vanish,
and the run continues with accuracy-improving iterations there. For $q = 1$ this is the
"otherwise" entry with a nonconvex $X$, whose order $\epsilon^{-(p+1)/p}$ coincides with that of
the convex entry. The cases $q = 2 < p$ (with $X \neq \mathbb{R}^n$) and $3 \le q < p$ are not
reached by the source's reduction to unconstrained problems: on $\mathbb{R}^n$ the order is not
attained for $q = 2 < p$ (`CartisGouldToint.Chapter14.theorem_14_2_4_arqpida_le_two`), and for
$3 \le q < p$ the case $X = \mathbb{R}^n$ is open (see the module doc comment). The coordinates
$v_1, v_2$ are `v 0` and `v 1`. This is `Optimization.exists_isARqpIDARun_slit`. -/
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
  exact ⟨ρ, X, f, hρ, hρ2, hX, hXc, hb, AssumptionD0qL.of_lipschitzDerivsAnchored hf hL, H⟩

end Sharp

section TRqPrintedFalse

open scoped ContDiff
open Optimization

set_option hygiene false in
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-!
### Failure of the alternative TRq-SC exponent $\pi_j = j + 1$ for $q = 2$

For $q = 2$ the OCR reading $\pi_j = j + 1$ fails per iteration with uniform constants.
The original PDF has $\pi_j = q + 1$. The example is in
`Numlib.Optimization.Complexity.SlowExample.TRqSaddle`.
-/

/-- The objective $f_a(x) = x_1^2/2 - a x_2^2/2$ on $\mathbb{R}^2$ of the counterexample to
the alternative exponent $\pi_j = j + 1$. It is `Optimization.saddleQuad`, with $x_1$ and $x_2$
the coordinates `v 0` and `v 1`. -/
noncomputable abbrev trqSadF (a : ℝ) : ℝ² → ℝ := saddleQuad a

/-- The box $X = [-1, 1]^2$ of the counterexample to the alternative exponent $\pi_j = j + 1$.
It is `Optimization.saddleBox`. -/
abbrev trqSadX : Set ℝ² := saddleBox

/-- The trust-region parameters of the counterexample to the alternative exponent
$\pi_j = j + 1$ are $\Delta_0 = \Delta_{\max} = 1$, $\eta_1 = 1/4$, $\eta_2 = 3/4$,
$\gamma_1 = 1/4$, $\gamma_2 = 1/2$, $\gamma_3 = 2$ and $\varsigma = 1/2$. They are
`Optimization.saddleTRqParams`. -/
noncomputable abbrev trqSadP : Optimization.TRqParams := saddleTRqParams

/-- For every $a \in [0, 1]$ and every anchor $x_0$, the objective $f_a$ satisfies f.D1qLaB.X with
$q = 2$ on the box $X = [-1, 1]^2$, with $X_0$ the open ball of radius $2$ about $0$ and the
constants $L_j = B_j = 4$, which depend neither on $a$ nor on the anchor. -/
theorem trqSadF_assumption {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (x₀ : ℝ²) :
    AssumptionD1qLaBX (trqSadF a) trqSadX (ball 0 2) x₀ 1 2 (fun _ => 4) (fun _ => 4) :=
  AssumptionD1qLaBX.of_lipschitzOn isOpen_ball (convex_ball 0 2) saddleBox_subset_ball
    (fun y _ => (contDiffAt_saddleQuad a 2 y).contDiffWithinAt)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ hj => iteratedFDerivLipschitzOn_saddleQuad ha0 ha1 hj)
    (fun _ hj _ hx => norm_iteratedFDeriv_saddleQuad_le_four ha0 ha1 hj hx)

/-- Counterexample to the alternative exponents $\pi_j = j + 1$ for $q = 2$ in the TRq-SC
decrease relation (14.2.11) of [cartis2022evaluation]. Consider the TRq parameters
`CartisGouldToint.Chapter14.trqSadP`, the threshold $\vartheta = 1$ and the box $X = [-1, 1]^2$.
For every $\kappa > 0$ there are $a \in (0, 1]$, tolerances $\epsilon \in (0, 1]^2$ and a TRq-SC
run on $X$ for $f_a(x) = x_1^2/2 - a x_2^2/2$ with $x_0 \in X$, where $f_a$ satisfies f.D1qLaB.X
on the ball of radius $2$ with the constants $4$ (independent of $a$), and an iteration $k$ such
that the termination test fails at the iterations $0, \dots, k$, $k$ is successful
($\rho_k \ge \eta_1$), and $$f_a(x_k) - f_a(x_{k+1}) < \kappa \min(1, \epsilon_1^2,
\epsilon_2^3).$$ So (14.2.11) with $\pi_j = j + 1$ fails for every $\kappa_{\mathrm{decr}}$ that
depends only on the algorithm parameters, $\vartheta$ and the f.D1qLaB.X constants, the
dependence of the explicit $\kappa_{\mathrm{decr}}$ of Lemma 12.2.4 and (12.2.14).

The objective varies with $\kappa$ within a family with uniform constants; a single fixed $f$ is
not treated here. With $r = 2^{-N}$, $\epsilon_1 = r^2$ and $\epsilon_2 = a = r$: $N$
unsuccessful first-order iterations at $(r^2, 0)$ shrink the radius from $1$ to $r^2$, a
successful step reaches $0$, where the gradient vanishes and the second-order test fails, and
the second-order step $r^2 e_2$ decreases $f_a$ by $r^5/2$, against $\kappa \min(\epsilon_1^2,
\epsilon_2^3) = \kappa r^4$. The radius is shared across the orders and is driven down by the
first-order failures. The decrease proved in Lemma 12.2.4 is $\kappa \epsilon_{\min}^{q+1}$
(`CartisGouldToint.Chapter14.lemma_14_2_2_trq`). The minimum is `Optimization.finMin 1`, which
also contains $1$. The run is `Optimization.exists_isTRqRun_saddleQuad_decrease_lt`. -/
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

/-- For $q = 2$ the TRq-SC decrease relation (14.2.11) of [cartis2022evaluation] lacks a uniform
$\kappa_{\mathrm{decr}}$ with the alternative exponents $\pi_j = j + 1$. There is no
$\kappa > 0$ such that, for every $a \in (0, 1]$, every $\epsilon \in (0, 1]^2$, every TRq-SC
run with the parameters `CartisGouldToint.Chapter14.trqSadP`, $\vartheta = 1$ and
$X = [-1, 1]^2$ on $f_a(x) = x_1^2/2 - a x_2^2/2$ for which $f_a$ satisfies f.D1qLaB.X on the
ball of radius $2$ with the constants $4$ and anchor $x_0$, and every successful iteration $k$
such that the termination test fails at the iterations $0, \dots, k$, $$f_a(x_k) - f_a(x_{k+1})
\ge \kappa \min(1, \epsilon_1^2, \epsilon_2^3).$$

This follows from `CartisGouldToint.Chapter14.lemma_14_2_2_trq_printed_false`. -/
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
