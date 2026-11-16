/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.AnchoredLipschitzDerivs
import Numlib.Optimization.Complexity.Existence
import Numlib.Optimization.Complexity.SlowExample.HighOrder
import Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity
import Numlib.Optimization.ModelBased.HighOrder.TRqComplexity
import Numlib.Optimization.ModelBased.HighOrder.ARqpDetailedStep
import Numlib.Optimization.ModelBased.HighOrder.Orders
import NumlibSurface.CartisGouldToint.Chapter02.Section01
import NumlibSurface.CartisGouldToint.Chapter12.Section01

/-!
# Cartis, Gould and Toint, Section 12.2: Finding approximate minimizers of arbitrary order

This module formalizes Section 12.2 of [cartis2022evaluation]: the trust-region method TRq (Section
12.2.1) and the adaptive-regularization method ARqp (Section 12.2.2) for
$(\varepsilon, \delta)$-approximate $q$-th order minimizers (12.1.25), their evaluation complexity,
and the sharpness of the complexity bounds. At an iterate $x_k$, both methods compare the decreases
$\Delta T_{f,j}(x_k, d) = T_{f,j}(x_k, 0) - T_{f,j}(x_k, d)$ of the Taylor models of the orders
$j \in [1:q]$ with the tolerances $\varepsilon_j$. The Step-1 test stops when an approximate
maximizer $d_{k,j}$ of $\Delta T_{f,j}(x_k, \cdot)$ on the ball of radius $\delta_{k,j}$ gives
$\Delta T_{f,j}(x_k, d_{k,j}) \le \varsigma \varepsilon_j \delta_{k,j}^j/j!$ for every $j$.
Otherwise TRq takes a step in a trust region of radius $\Delta_k$ that decreases the Taylor model of
the first order that fails the test, and ARqp takes a step that approximately minimizes the
regularized model
$$m_k(s) = T_{f,p}(x_k, s) + \frac{\sigma_k}{(p+1)!} \|s\|^{p+1}, \qquad p \ge q.$$
TRq needs a number of evaluations of order $\varepsilon_{\min}^{-(q+1)}$ (Theorem 12.2.5). ARqp
needs a number of order $\max_j \varepsilon_j^{-\pi_j}$, with $\pi_j = (p+1)/(p-j+1)$ for $q \le 2$
and $\pi_j = j(p+1)/p$ for $q > 2$ (Theorem 12.2.14). Examples in one variable show that these
orders are attained (Theorems 12.2.6, 12.2.15 and 12.2.17, Corollary 12.2.16).

The algorithms are backbone run predicates with exact Taylor data: Algorithm 12.2.1 is
`Optimization.IsTRqRun`, Algorithm 12.2.2 is `Optimization.IsARqpRun`, and Algorithm 12.2.3 is an
instance of the transition system `Optimization.DetailedStepTrans`. The analyses are those of
`Numlib.Optimization.ModelBased.HighOrder.TRqComplexity` (Lemmas 12.2.3–12.2.4, Theorem 12.2.5),
`Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity` (Lemmas 12.2.9–12.2.13, Theorem 12.2.14)
and `Numlib.Optimization.ModelBased.HighOrder.ARqpDetailedStep` (termination of Algorithm 12.2.3).
The slow examples come from `Numlib.Optimization.Complexity.SlowExample.HighOrder`.

## Main definitions

* Assumptions f.D1qL, f.D1pL and f.D1rL, `CartisGouldToint.Chapter12.AssumptionD1pL`: $f$ is $C^p$,
  and its derivatives of the orders $j \in [1:p]$ are Lipschitz continuous with constants
  $L_{f,j} \ge 1$.
* Algorithm 12.2.1, `CartisGouldToint.Chapter12.algorithm_12_2_1`: a run of TRq, with the
  termination test `CartisGouldToint.Chapter12.trqStop`.
* Algorithm 12.2.1 with a feasible set, `CartisGouldToint.Chapter12.algorithm_12_2_1_feasible`: a
  run of TRq-SC (Section 14.2).
* Algorithm 12.2.2, `CartisGouldToint.Chapter12.algorithm_12_2_2`: a run of ARqp, with the
  termination test `Optimization.arqpStop`.
* Algorithm 12.2.2 with a feasible set, `CartisGouldToint.Chapter12.algorithm_12_2_2_feasible`: a
  run of ARqp-SC (Section 14.2).
* Algorithm 12.2.3, `CartisGouldToint.Chapter12.algorithm_12_2_3`: an output of the detailed Step 2
  of ARqp.
* Lemma 12.2.13, `CartisGouldToint.Chapter12.arqpPi` and `CartisGouldToint.Chapter12.arqpKappaDm`:
  the exponents $\pi_j$ and the constant $\kappa_{\Delta m}$.
* Theorem 12.2.14, `CartisGouldToint.Chapter12.kappaSARqp` and
  `CartisGouldToint.Chapter12.kappaAARqp`: the constants $\kappa^s$ and $\kappa^a$ of the complexity
  bounds.
* Theorem 12.2.15, `CartisGouldToint.Chapter12.IsARqpGlobalStepRun`: an ARqp run with all radii $1$
  whose steps are global minimizers of the model.
* Equation (12.2.85), `CartisGouldToint.Chapter12.arqpSigmaSharp`: the regularization weight of
  Theorem 12.2.17.

## Main results

* Algorithm 12.2.1, `CartisGouldToint.Chapter12.algorithm_12_2_1_exists`: in finite dimension, a TRq
  run exists from every starting point.
* Lemma 12.2.1, `CartisGouldToint.Chapter12.lemma_12_2_1`: before termination of TRq, the scaled
  gaps satisfy $\min_{i \le k} \hat\phi_i \ge \varsigma \varepsilon_{\min}$, and the step decreases
  the model by at least $\hat\phi_k \delta_k^{j_k}/j_k!$.
* Lemma 12.2.2, `CartisGouldToint.Chapter12.lemma_12_2_2`: a small trust-region radius gives a very
  successful iteration.
* Lemma 12.2.3, `CartisGouldToint.Chapter12.lemma_12_2_3`: $\Delta_k \ge \min(\gamma_1 \vartheta,
  \kappa_\Delta \min_{i \le k} \hat\phi_i)$ before termination.
* Lemma 12.2.4, `CartisGouldToint.Chapter12.lemma_12_2_4`: each TRq step decreases the model by at
  least $(\varsigma \kappa_\Delta)^{q+1} \varepsilon_{\min}^{q+1}/q!$.
* Theorem 12.2.5, `CartisGouldToint.Chapter12.theorem_12_2_5`: TRq finds an
  $(\varepsilon, \delta)$-approximate $q$-th order minimizer, with explicit bounds of the order
  $\varepsilon_{\min}^{-(q+1)}$ on the numbers of evaluations.
* Proofs of Theorems 12.2.6, 12.2.15 and 12.2.17, `CartisGouldToint.Chapter12.assumptionD1pL_real`:
  a criterion for f.D1rL in one variable.
* Theorem 12.2.6, `CartisGouldToint.Chapter12.theorem_12_2_6`: TRq can need
  $\lceil \varepsilon^{-(q+1)} \rceil$ iterations.
* Algorithm 12.2.2, `CartisGouldToint.Chapter12.algorithm_12_2_2_exists`: in finite dimension, an
  ARqp run exists from every starting point.
* Example 12.2.1, `CartisGouldToint.Chapter12.example_12_2_1`: for the model of Example 12.1.3 with
  $p = 5$, the radius $\delta_{s_k,3} = 1$ is not admissible.
* Example 12.2.2, `CartisGouldToint.Chapter12.example_12_2_2`: the model $s^2(s - \frac12)^2$ has
  the global minimizers $0$ and $\frac12$, and its third-order measure at $0$ vanishes exactly for
  the radii $\delta \le \frac14$.
* Lemma 12.2.7, `CartisGouldToint.Chapter12.lemma_12_2_7`: smoothness of the model and the bound
  (12.2.38) on its derivatives.
* Lemma 12.2.8, `CartisGouldToint.Chapter12.lemma_12_2_8`: a large Taylor decrease of the model
  gives a large decrease of the model.
* Lemma 12.2.9, `CartisGouldToint.Chapter12.lemma_12_2_9`: an admissible Step-2 step exists, with
  the radii bounds (12.2.44)–(12.2.45).
* Lemma 12.2.9, `CartisGouldToint.Chapter12.lemma_12_2_9_algorithm`: every execution of Algorithm
  12.2.3 terminates and returns an admissible step with the radii bounds (12.2.44)–(12.2.45).
* Lemmas 12.2.9–12.2.10, `CartisGouldToint.Chapter12.algorithm_12_2_2_exists_of_D1pL`: ARqp runs
  with the radii property (12.2.50) exist.
* Lemma 12.2.10, `CartisGouldToint.Chapter12.isEpsDeltaApproxMinimizer_of_isMinOn_zero`: if $0$
  globally minimizes the model at $y$, then $y$ is an approximate minimizer.
* Lemma 12.2.10, `CartisGouldToint.Chapter12.lemma_12_2_10_le_two`: for $q \le 2$, ARqp does not
  terminate in Step 2.
* Lemma 12.2.10, `CartisGouldToint.Chapter12.lemma_12_2_10`: termination in Step 2 needs $q \ge 3$
  and gives an approximate minimizer.
* Lemma 12.2.11, `CartisGouldToint.Chapter12.lemma_12_2_11`: the inequality (12.2.52) after a
  successful short step.
* Lemma 12.2.12, `CartisGouldToint.Chapter12.lemma_12_2_12`: lower bounds on the step length
  (12.2.57).
* Lemma 12.2.13, `CartisGouldToint.Chapter12.lemma_12_2_13`: the decreases (12.2.61)–(12.2.62) at
  successful iterations.
* Theorem 12.2.14 (1), `CartisGouldToint.Chapter12.theorem_12_2_14_i`: the complexity of ARqp for
  $q \in \{1, 2\}$.
* Theorem 12.2.14 (2), `CartisGouldToint.Chapter12.theorem_12_2_14_ii`: the complexity of ARqp for
  $q > 2$.
* Theorem 12.2.15, `CartisGouldToint.Chapter12.theorem_12_2_15`: ARqp with global model minimizers
  as steps can need $\lceil \varepsilon^{-(p+1)/(p-q+1)} \rceil$ iterations.
* Theorem 12.2.15, `CartisGouldToint.Chapter12.theorem_12_2_15_counterexample`: for $p = q = 3$, the
  hypothesis "the choice $\delta_{s_k,j} = 1$ is possible" fails for the example of the proof.
* Corollary 12.2.16, `CartisGouldToint.Chapter12.IsARqpGlobalStepRun.toAlgorithm`: for $q \le 2$, a
  run with global model minimizers as steps is an ARqp run.
* Corollary 12.2.16, `CartisGouldToint.Chapter12.corollary_12_2_16`: for $q \in \{1, 2\}$, ARqp can
  need $\lceil \varepsilon^{-(p+1)/(p-q+1)} \rceil$ iterations.
* Theorem 12.2.17, `CartisGouldToint.Chapter12.theorem_12_2_17`: ARqp can need
  $\lceil \varepsilon^{-q(p+1)/p} \rceil$ iterations.

## Conventions

* $\varepsilon_{\min} = \min(1, \min_{j \in [1:q]} \varepsilon_j)$ is `Optimization.finMin 1 ε q`,
  and $L_f = \max(1, \max_{j \in [1:p]} L_{f,j})$ is `Optimization.finMax 1 L p` ((12.2.6),
  (12.2.7), (12.2.25)). For $\varepsilon \in (0, 1]^q$ and $L_{f,j} \ge 1$ these are
  $\min_j \varepsilon_j$ and $\max_j L_{f,j}$. Likewise $\min_j \varepsilon_j^{\pi_j}$ is
  `Optimization.finMin 1 (fun j => ε j ^ arqpPi p q j) q`.
* The tolerances $\varepsilon_j$, the radii $\delta_j$ and the constants $L_{f,j}$ are functions
  `ℕ → ℝ` of the order $j$. Only the entries for $j \in [1:q]$ (or $[1:p]$) matter.
* An iteration $k$ is *reached* if the termination test fails at every $i < k$, and it is *before
  termination* if the test fails at every $i \le k$. The termination index is the first index at
  which the test holds (`Optimization.IsFirstHit`). An iteration is successful if
  $\rho_k \ge \eta_1$.
* The number of evaluations of $f$ up to the termination index $k$ is
  `Optimization.funEvalCount k = k + 1`. The number of evaluations of the derivatives is
  `Optimization.derivEvalCount`: the initial evaluation and one for each successful iteration before
  $k$.
* The definitions are stated on a real normed space (TRq) or a real inner product space (ARqp) $E$.
  The complexity theorems are stated on $\mathbb{R}^n$ (`EuclideanSpace ℝ (Fin n)`), and the
  sharpness examples, as in the source, on $\mathbb{R}$.

## Implementation notes

* The analyses of the backbone are stated once on a feasible set $X$, under the anchored smoothness
  assumption `LipschitzDerivsAnchored`: the derivatives are Lipschitz continuous with respect to
  anchors in a set that contains the sublevel set $\{y \in X \mid f(y) \le f(x_0)\}$. The results of
  this module are their instances with $X = C = A = E$. The forms of f.D1pL on an open convex set,
  or anchored at a set, that Section 14.2 uses with feasible sets are `LipschitzDerivsAnchored`
  itself.
* The constants `CartisGouldToint.Chapter12.arqpKappaDm`, `CartisGouldToint.Chapter12.arqpPi`,
  `CartisGouldToint.Chapter12.kappaSARqp` and `CartisGouldToint.Chapter12.kappaAARqp` are the radii
  mode $u = (q \le 2)$ of `Optimization.arqpKappaDmOf`, `Optimization.arqpPiOf`,
  `Optimization.kappaSARqpOf` and `Optimization.kappaAARqpOf`. The other constants are those of the
  backbone: `Optimization.trqKappaDelta`, `Optimization.kappaSTRq`, `Optimization.kappaATRq`,
  `Optimization.kappaBTRq`, `Optimization.kappaCTRq`, `Optimization.arqpKappaDelta`,
  `Optimization.arqpTau`, `Optimization.arqpKappaHat` and `Optimization.kappaCARqp`.
* The conditions of Step 0 of the algorithms on $\varepsilon$, $\vartheta$ and $\delta_0$ are
  hypotheses of the results, not parts of the run predicates.
* The existence of an admissible Step-2 step is proved twice: directly from a global minimizer of
  the model in `CartisGouldToint.Chapter12.lemma_12_2_9`, and through the termination of Algorithm
  12.2.3 in `CartisGouldToint.Chapter12.lemma_12_2_9_algorithm`.

## Deviations from the source

* **Algorithm 12.2.2, Step 1** (typo). The printed test continues when $\Delta T_{f,j}(x_k, d_{k,j})
  \ge \varsigma \varepsilon_j \delta_{k,j}^j/j!$. With $\ge$, the sharpness examples of the source
  never stop. The library continues on $>$, as in the test (12.2.2) of TRq. See
  `CartisGouldToint.Chapter12.algorithm_12_2_2`.
* **Algorithm 12.2.2, Step 2** (reading). Termination in Step 2 is allowed only when $0$ is a global
  minimizer of the model, as Algorithm 12.2.3 guarantees. See
  `CartisGouldToint.Chapter12.algorithm_12_2_2`.
* **(12.2.28)** (typo). The long-step branch is printed $\|s_k\| > 1$. The library uses
  $\|s_k\| \ge 1$, as Algorithm 12.2.3 does. See `CartisGouldToint.Chapter12.algorithm_12_2_2`.
* **Theorem 12.2.5** (typo). The printed conclusion $\phi^{\delta_\varepsilon}_{f,q}$ is
  $\phi^{\delta_\varepsilon}_{f,j}$. See `CartisGouldToint.Chapter12.theorem_12_2_5`.
* **Theorem 12.2.6** (correction). The slow data of Appendix B are wrong in four points: they
  decrease $f$ by $\frac12 \varepsilon^{q+1} c_k$ while the Taylor decrease is
  $\varepsilon^{q+1} c_k$, so (B.12.8) fails; $x_k = (k-1)\varepsilon$ must be $k\varepsilon$;
  $\varepsilon^{q+1} k_\varepsilon \le 1$ is false, and only $\varepsilon^{q+1} k_\varepsilon \le 2$
  holds; and the residuals at the orders $1 \le j < q$ are $2\, q!/(q-j)!\, s_k^{q-j+1}$. The
  library uses corrected data. See `CartisGouldToint.Chapter12.theorem_12_2_6` and
  `Optimization.exists_slowTRq_interpolant`.
* **Lemma 12.2.11** (correction). A failed Step-1 test gives only $\phi^\delta_{f,j}(x_{k+1}) >
  \varsigma \varepsilon_j \delta^j/j!$, so the printed factor $1 - \theta$ is $\varsigma - \theta$.
  The lemma also needs (12.2.29) at the iteration $k$, that is, a short step. See
  `CartisGouldToint.Chapter12.lemma_12_2_11`.
* **Lemma 12.2.12** for $q > 2$ (correction). The argument "the first case implies the second" needs
  $\kappa_{\delta,\min} \le \tau_q/2$, which fails for $\theta$ close to $\varsigma$. The constant
  $\kappa_{\delta,\min}$ is replaced by $\hat\kappa = \min(\kappa_{\delta,\min}, \tau_q/2)$, also in
  Lemma 12.2.13 and Theorem 12.2.14 (2). See `CartisGouldToint.Chapter12.lemma_12_2_12`.
* **Lemma 12.2.13** (correction). The lemma needs f.D1pL (printed: f.D1qL), and it holds at
  successful iterations that are followed by an iteration without termination (printed: at every
  iteration before termination). See `CartisGouldToint.Chapter12.lemma_12_2_13`.
* **(12.2.56)** (typo). The printed $(p-j+1)!$ and $\|s_k\|^{p-j+1}$ are $(p-\ell+1)!$ and
  $\|s_k\|^{p-\ell+1}$. See `CartisGouldToint.Chapter12.lemma_12_2_13`.
* **Theorem 12.2.14** (correction). The hypothesis $\theta < \varsigma$, which Lemma 12.2.11 needs,
  is explicit, and the constants have $\varsigma - \theta$ in place of $1 - \theta$ and, in (2),
  $\hat\kappa$ in place of $\kappa_{\delta,\min}$. See
  `CartisGouldToint.Chapter12.theorem_12_2_14_i` and
  `CartisGouldToint.Chapter12.theorem_12_2_14_ii`.
* **Theorem 12.2.14** (reading). The hypothesis $\sigma_{\min} > 0$ of Step 0 is explicit. In (1),
  the radii equal to $1$ ("the algorithm ensures $\delta_{k+1,j} = 1$") are a hypothesis on
  $\delta_0$ and on every returned step. In (2), the radii property (12.2.50) is a hypothesis on the
  run. See `CartisGouldToint.Chapter12.theorem_12_2_14_i` and
  `CartisGouldToint.Chapter12.theorem_12_2_14_ii`.
* **Theorem 12.2.15** for $q \ge 3$ (correction). The hypothesis "the choice $\delta_{s_k,j} = 1$ is
  possible" fails for the example of the proof, for instance for $p = q = 3$. The theorem is stated
  for runs whose steps are global model minimizers, which are ARqp runs for $q \le 2$. See
  `CartisGouldToint.Chapter12.theorem_12_2_15`,
  `CartisGouldToint.Chapter12.theorem_12_2_15_counterexample` and
  `CartisGouldToint.Chapter12.corollary_12_2_16`.
* **Theorem 12.2.15** (generalization). The source takes $\varepsilon \le \frac12$. The library
  proves the statement for $\varepsilon \in (0, 1]$. See
  `CartisGouldToint.Chapter12.theorem_12_2_15`.
* **Example 12.2.2** (typo). The source prints $s^2(s - \frac12)^2 = \frac12 s^2(1 - 2s) + s^4$,
  which has the unique minimizer $0$. The correct expansion is $\frac14 s^2(1 - 4s) + s^4$, the
  measure is $\phi^1_{m,3}(0) = \frac34$, and the radius threshold is $\frac14$. See
  `CartisGouldToint.Chapter12.example_12_2_2`.
* **Theorem 12.2.17** (reading). "$\varepsilon$ sufficiently small" is $\varepsilon \le \frac12$.
  See `CartisGouldToint.Chapter12.theorem_12_2_17`.
* **(12.2.78)** (typo). The residual of order $q$ is $\varepsilon/k_\varepsilon$, not $0$. It still
  satisfies (A.32). See `CartisGouldToint.Chapter12.theorem_12_2_17`.

## Not formalized

* The $O(\cdot)$ restatements of the complexity bounds and Table 12.2.1.
-/

open Set Metric Filter Optimization Topology
open scoped Nat

namespace CartisGouldToint.Chapter12

section Assumption

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Assumptions f.D1qL, f.D1pL and f.D1rL** of [cartis2022evaluation] (Sections 12.2.1.2, 12.2.2.1
and 12.2.2.4; the same condition for the orders $q$, $p$ and $r$). Let $E$ be a real normed
space, $f : E \to \mathbb{R}$, $p \in \mathbb{N}$, and let $L_{f,j}$ be constants. The function
$f$ satisfies **f.D1pL** if $f$ is $p$ times continuously differentiable and, for every
$j \in [1:p]$,
$$\|\nabla^j f(x) - \nabla^j f(y)\| \le L_{f,j} \|x - y\| \quad \text{for all } x, y \in E,
  \qquad L_{f,j} \ge 1.$$

The condition is stated as the anchored smoothness assumption `LipschitzDerivsAnchored` of the
orders $[1:p]$ on the whole space ($C = A = E$), together with $L_{f,j} \ge 1$. The form above
is given by `CartisGouldToint.Chapter12.AssumptionD1pL.contDiff`,
`CartisGouldToint.Chapter12.AssumptionD1pL.lipschitz` and
`CartisGouldToint.Chapter12.AssumptionD1pL.of_iteratedFDerivLipschitzOn`. The constant $L_{f,j}$
is `L j`. -/
abbrev AssumptionD1pL (f : E → ℝ) (p : ℕ) (L : ℕ → ℝ) : Prop :=
  LipschitzDerivsAnchored f univ univ 1 p L ∧ ∀ j ∈ Finset.Icc 1 p, 1 ≤ L j

variable {f : E → ℝ} {p : ℕ} {L : ℕ → ℝ}

namespace AssumptionD1pL

/-- Under f.D1pL, $f$ is $C^p$. -/
theorem contDiff (h : AssumptionD1pL f p L) : ContDiff ℝ p f :=
  h.1.contDiff

/-- The constants of f.D1pL satisfy $L_{f,j} \ge 1$ for $j \in [1:p]$. -/
theorem one_le (h : AssumptionD1pL f p L) : ∀ j ∈ Finset.Icc 1 p, 1 ≤ L j :=
  h.2

/-- Under f.D1pL, the $j$-th derivative of $f$ is Lipschitz continuous on $E$ with the constant
$L_{f,j}$, for $j \in [1:p]$. -/
theorem lipschitz (h : AssumptionD1pL f p L) : ∀ j ∈ Finset.Icc 1 p,
    IteratedFDerivLipschitzOn f j (L j) univ :=
  fun _ hj => h.1.lipschitzOn hj

/-- A $C^p$ function whose derivatives of the orders $j \in [1:p]$ are Lipschitz continuous on $E$
with constants $L_{f,j} \ge 1$ satisfies f.D1pL. -/
theorem of_iteratedFDerivLipschitzOn (hf : ContDiff ℝ p f) (h1 : ∀ j ∈ Finset.Icc 1 p, 1 ≤ L j)
    (hL : ∀ j ∈ Finset.Icc 1 p, IteratedFDerivLipschitzOn f j (L j) univ) :
    AssumptionD1pL f p L :=
  ⟨.of_contDiff hf hL univ, h1⟩

/-- If $q \le p$, then f.D1pL implies f.D1qL with the same constants. -/
theorem mono (h : AssumptionD1pL f p L) {q : ℕ} (hq : q ≤ p) : AssumptionD1pL f q L :=
  ⟨h.1.mono le_rfl hq, fun j hj => h.one_le j (Finset.Icc_subset_Icc_right hq hj)⟩

/-- Under f.D1pL, every derivative of an order $j \in [1:p]$ is Lipschitz continuous on $E$ with the
constant $L_f = \max(1, \max_{i \in [1:p]} L_{f,i})$. -/
theorem lipschitz_finMax (h : AssumptionD1pL f p L) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) :
    IteratedFDerivLipschitzOn f j (finMax 1 L p) univ :=
  IteratedFDerivHolderOn.mono_const (h.lipschitz j hj) (le_finMax hj)

/-- **(12.2.24)** of [cartis2022evaluation], with Theorem A.8.5. Under f.D1pL,
$\|\nabla^j f(x)\| \le L_{f,j-1}$ for all $x \in E$ and $j \in [2:p]$. -/
theorem norm_iteratedFDeriv_le (h : AssumptionD1pL f p L) {j : ℕ} (hj : j ∈ Finset.Icc 2 p)
    (x : E) : ‖iteratedFDeriv ℝ j f x‖ ≤ L (j - 1) := by
  obtain ⟨hj2, hjp⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  rw [Nat.add_sub_cancel]
  exact h.1.norm_iteratedFDeriv_le hi (zero_le_one.trans (h.one_le i hi)) (mem_univ x)

/-- Under f.D1pL, $\|\nabla^j f(x)\| \le L_f$ for all $x \in E$ and $j \in [2:p]$, where
$L_f = \max(1, \max_{i \in [1:p]} L_{f,i})$. -/
theorem norm_iteratedFDeriv_le_finMax (h : AssumptionD1pL f p L) {j : ℕ}
    (hj : j ∈ Finset.Icc 2 p) (x : E) : ‖iteratedFDeriv ℝ j f x‖ ≤ finMax 1 L p := by
  refine (h.norm_iteratedFDeriv_le hj x).trans (le_finMax ?_)
  obtain ⟨hj2, hjp⟩ := Finset.mem_Icc.1 hj
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

/-- f.D1pL gives the anchored assumption `LipschitzDerivsAnchored` of the orders $[1:p]$ on the
whole space, for every set of anchors $A$. -/
theorem toLipschitzDerivsAnchored (h : AssumptionD1pL f p L) (A : Set E) :
    LipschitzDerivsAnchored f univ A 1 p L :=
  h.1.mono_left (subset_univ A)

/-- For $p \ge 1$, f.D1pL gives the anchored assumption `LipschitzDerivsAnchored` of the order $p$
only, on the whole space and for every set of anchors $A$. This is the form of the hypotheses of
the ARqp analysis. -/
theorem toLipschitzDerivsAnchored_top (h : AssumptionD1pL f p L) (hp : 1 ≤ p) (A : Set E) :
    LipschitzDerivsAnchored f univ A p p L :=
  (h.toLipschitzDerivsAnchored A).mono hp le_rfl

/-- For $p \ge 1$, the constant of the top order satisfies $L_{f,p} \ge 1$. -/
theorem one_le_top (h : AssumptionD1pL f p L) (hp : 1 ≤ p) : 1 ≤ L p :=
  h.one_le p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)

end AssumptionD1pL

end Assumption

/-! ### The TRq algorithm (Section 12.2.1) -/

section TRq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Algorithm 12.2.1** of [cartis2022evaluation] (TRq). Let $E$ be a real normed space and
$f : E \to \mathbb{R}$. A **run of TRq** with the constants $P$ ($\Delta_0$, $\Delta_{\max}$,
$\eta_1$, $\eta_2$, $\gamma_1$, $\gamma_2$, $\gamma_3$, $\varsigma$), the order $q$, the
tolerances $\varepsilon_j$ and the threshold $\vartheta$ consists of iterates $x_k$, steps
$s_k$, trust-region radii $\Delta_k$, orders $j_k$ and Step-1 displacements $d_{k,j}$, with the
optimality radius $\delta_k = \min(\Delta_k, \vartheta)$, such that:
* Step 1: at every iteration $k$ reached, $d_{k,j}$ is a $\varsigma$-approximate optimality
  displacement of radius $\delta_k$ for $\Delta T_{f,j}(x_k, \cdot)$, $j \in [1:q]$ (12.2.1);
  the run stops at the first $k$ with $\Delta T_{f,j}(x_k, d_{k,j}) \le \varsigma \varepsilon_j
  \delta_k^j/j!$ for all $j \in [1:q]$;
* Step 2: otherwise $j_k$ is the least order that fails this test (12.2.2), and the step
  satisfies $\|s_k\| \le \Delta_k$ and $\Delta T_{f,j_k}(x_k, s_k) \ge \Delta T_{f,j_k}(x_k,
  d_{k,j_k})$ (12.2.3);
* Steps 3–4: the iterate and the radius are updated as in a trust-region method with the ratio
  $\rho_k = (f(x_k) - f(x_k + s_k))/\Delta T_{f,j_k}(x_k, s_k)$ (12.2.4), and
  $\Delta_{k+1} \le \Delta_{\max}$ (12.2.5).

The run is `Optimization.IsTRqRun` with the exact Taylor data `ftaylorSeries ℝ f (x k)` and no
constraints. The trust-region update is that of `Optimization.IsTRRun`. Step 0 of the source
asks $\varepsilon \in (0, 1]^q$ and $\vartheta \in [\varepsilon_{\min}, 1]$; these conditions
are hypotheses of the results below. -/
def algorithm_12_2_1 (f : E → ℝ) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ) (ϑ : ℝ) (x s : ℕ → E)
    (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E) : Prop :=
  IsTRqRun f (fun k => ftaylorSeries ℝ f (x k)) (fun _ => univ) P q ε ϑ x s Δ jk d

/-- The termination test of TRq (Step 1) at the iteration $k$: $\Delta T_{f,j}(x_k, d_{k,j}) \le
\varsigma \varepsilon_j \delta_k^j/j!$ for all $j \in [1:q]$, where
$\delta_k = \min(\Delta_k, \vartheta)$. -/
abbrev trqStop (f : E → ℝ) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ) (ϑ : ℝ) (x : ℕ → E)
    (Δ : ℕ → ℝ) (d : ℕ → ℕ → E) (k : ℕ) : Prop :=
  trqTest (fun k => ftaylorSeries ℝ f (x k)) P q ε ϑ Δ d k

/-- The ratio (12.2.4) of TRq: $\rho_k = (f(x_k) - f(x_k + s_k))/\Delta T_{f,j_k}(x_k, s_k)$. -/
noncomputable abbrev trqRho (f : E → ℝ) (x s : ℕ → E) (jk : ℕ → ℕ) (k : ℕ) : ℝ :=
  trqRatio f (fun k => ftaylorSeries ℝ f (x k)) x s jk k

/-- The scaled approximate criticality gap (12.2.8) of TRq: $\hat\phi_k = j_k!\, \Delta
T_{f,j_k}(x_k, d_{k,j_k})/\delta_k^{j_k}$, with $\delta_k = \min(\Delta_k, \vartheta)$. -/
noncomputable abbrev trqGapSeq (f : E → ℝ) (ϑ : ℝ) (x : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ)
    (d : ℕ → ℕ → E) (k : ℕ) : ℝ :=
  trqGap (ftaylorSeries ℝ f (x k)) (jk k) (min (Δ k) ϑ) (d k (jk k))

/-- **Algorithm 12.2.1** of [cartis2022evaluation], well-posedness. Let $E$ be a finite-dimensional
real normed space. For every $f : E \to \mathbb{R}$, all constants $P$, every order $q$, all
tolerances $\varepsilon_j$, every threshold $\vartheta \ge 0$ and every starting point
$x_0 \in E$, there is a TRq run that starts at $x_0$.

The proof specializes `Optimization.exists_isTRqRun`. -/
theorem algorithm_12_2_1_exists [FiniteDimensional ℝ E] (f : E → ℝ) (P : TRqParams) (q : ℕ)
    (ε : ℕ → ℝ) {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (x₀ : E) :
    ∃ (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E), x 0 = x₀ ∧
      algorithm_12_2_1 f P q ε ϑ x s Δ jk d :=
  exists_isTRqRun f (fun y => ftaylorSeries ℝ f y) (fun _ => univ) (fun _ => isClosed_univ)
    (fun _ => mem_univ 0) P q ε hϑ x₀

variable {f : E → ℝ} {P : TRqParams} {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → E}
  {Δ : ℕ → ℝ} {jk : ℕ → ℕ} {d : ℕ → ℕ → E} {L : ℕ → ℝ}

/-- **Algorithm 12.2.1** of [cartis2022evaluation] with a feasible set (TRq-SC, Section 14.2). Let
$X \subseteq E$. A **run of TRq-SC** is a run of Algorithm 12.2.1 whose Step-1 displacements $d$
and steps $s_k$ are feasible, $x_k + d \in X$ and $x_k + s_k \in X$.

It is `Optimization.IsTRqRun` with the feasible displacements $\{d \mid x_k + d \in X\}$. For
$X = E$ it is `CartisGouldToint.Chapter12.algorithm_12_2_1`, by
`CartisGouldToint.Chapter12.algorithm_12_2_1_iff_feasible`. -/
def algorithm_12_2_1_feasible (f : E → ℝ) (X : Set E) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ)
    (ϑ : ℝ) (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E) : Prop :=
  IsTRqRun f (fun k => ftaylorSeries ℝ f (x k)) (fun k => {e | x k + e ∈ X}) P q ε ϑ x s Δ jk d

/-- A sequence of iterates, steps, radii, orders and displacements is a TRq run if and only if it is
a TRq-SC run for the feasible set $X = E$. -/
theorem algorithm_12_2_1_iff_feasible :
    algorithm_12_2_1 f P q ε ϑ x s Δ jk d ↔
      algorithm_12_2_1_feasible f univ P q ε ϑ x s Δ jk d := by
  have : (fun k => {e | x k + e ∈ (univ : Set E)}) = fun _ => univ := by
    funext k; ext; simp
  rw [algorithm_12_2_1_feasible, this]; rfl

/-- **Lemma 12.2.1** of [cartis2022evaluation]. Consider a TRq run with $\vartheta > 0$, let
$\varepsilon_{\min} = \min(1, \min_{j \in [1:q]} \varepsilon_j)$ (12.2.7), and let $\hat\phi_i$
be the scaled gaps (12.2.8). At every iteration $k$ before termination,
$$\min_{i \in [0:k]} \hat\phi_i \ge \varsigma \varepsilon_{\min} \quad \text{(12.2.9)} \qquad
  \text{and} \qquad \Delta T_{f,j_k}(x_k, s_k) \ge \hat\phi_k \frac{\delta_k^{j_k}}{j_k!} \quad
  \text{(12.2.10)}.$$

The minimum over $[0:k]$ is `Optimization.prefixMin`. -/
theorem lemma_12_2_1 (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) (hϑ : 0 < ϑ) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ trqStop f P q ε ϑ x Δ d i) :
    P.ς * finMin 1 ε q ≤ prefixMin (trqGapSeq f ϑ x Δ jk d) k ∧
      trqGapSeq f ϑ x Δ jk d k * min (Δ k) ϑ ^ jk k / (jk k)! ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) :=
  IsTRqRun.trqGap_ge h hϑ (fun _ hj => finMin_le hj) hk

/-- Model fidelity of TRq under f.D1qL, from (A.19) and Corollary A.8.4 of [cartis2022evaluation].
At every iteration $k$ before termination of a TRq run,
$$|f(x_k + s_k) - T_{f,j_k}(x_k, s_k)| \le \frac{L_f}{(j_k+1)!} \|s_k\|^{j_k+1},$$
where $L_f = \max(1, \max_{j \in [1:q]} L_{f,j})$. -/
theorem trq_fidelity (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) (hf : AssumptionD1pL f q L) :
    ∀ k, (∀ i ≤ k, ¬ trqStop f P q ε ϑ x Δ d i) →
      |f (x k + s k) - (f (x k) - (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k))| ≤
        finMax 1 L q / (jk k + 1)! * ‖s k‖ ^ (jk k + 1) :=
  IsTRqRun.abs_sub_le_of_lipschitz h hf.contDiff fun _ hj => hf.lipschitz_finMax hj

/-- **Lemma 12.2.2** of [cartis2022evaluation]. Assume f.D1qL and consider a TRq run. If at an
iteration $k$ before termination
$$\Delta_k \le \min\Big(\vartheta, \frac{(1 - \eta_2) \hat\phi_k}{L_f}\Big) \quad
  \text{(12.2.11)},$$
then $\rho_k \ge \eta_2$, that is, the iteration is very successful, and
$\Delta_{k+1} \ge \Delta_k$.

Here $L_f = \max(1, \max_{j \in [1:q]} L_{f,j})$. -/
theorem lemma_12_2_2 (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) (hf : AssumptionD1pL f q L)
    {k : ℕ} (hk : ∀ i ≤ k, ¬ trqStop f P q ε ϑ x Δ d i)
    (hΔ : Δ k ≤ min ϑ ((1 - P.η₂) * trqGapSeq f ϑ x Δ jk d k / finMax 1 L q)) :
    P.η₂ ≤ trqRho f x s jk k ∧ Δ k ≤ Δ (k + 1) := by
  obtain ⟨-, h1, h2⟩ := IsTRqRun.le_reductionRatio h
    (zero_lt_one.trans_le one_le_finMax) hk (trq_fidelity h hf k hk) hΔ
  exact ⟨h1, h2⟩

/-- **Lemma 12.2.4** of [cartis2022evaluation]. Assume f.D1qL, $\varepsilon \in (0, 1]^q$ and
$\varepsilon_{\min} \le \vartheta \le 1$, and consider a TRq run. At every iteration $k$ before
termination,
$$\Delta T_{f,j_k}(x_k, s_k) \ge \frac{(\varsigma \kappa_\Delta)^{q+1}}{q!}
  \varepsilon_{\min}^{q+1} \quad \text{(12.2.18)},$$
and if the iteration $k$ is successful, then
$$f(x_k) - f(x_{k+1}) \ge \eta_1 \frac{(\varsigma \kappa_\Delta)^{q+1}}{q!}
  \varepsilon_{\min}^{q+1} \quad \text{(12.2.19)}.$$

The constant $\kappa_\Delta$ of (12.2.14) is `Optimization.trqKappaDelta`. It depends on the
derivatives of $f$ at $x_0$. -/
theorem lemma_12_2_4 (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) (hf : AssumptionD1pL f q L)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ trqStop f P q ε ϑ x Δ d i) :
    (P.ς * trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! * finMin 1 ε q ^ (q + 1) ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ trqRho f x s jk k →
        P.η₁ * ((P.ς * trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
          finMin 1 ε q ^ (q + 1)) ≤ f (x k) - f (x (k + 1))) :=
  IsTRqRun.taylorDecrement_ge_of_anchored (X := univ) (algorithm_12_2_1_iff_feasible.1 h)
    (hf.toLipschitzDerivsAnchored univ) subset_rfl (fun _ hy _ => hy) (mem_univ _) hε hϑ hϑ1 hk

/-- **Lemma 12.2.3** of [cartis2022evaluation]. Assume f.D1qL, $0 < \vartheta \le 1$ and
$\varepsilon_j \ge 0$ for $j \in [1:q]$, and consider a TRq run. Then $\kappa_\Delta \in (0, 1)$
(12.2.14), and at every iteration $k$ before termination,
$$\Delta_k \ge \min\Big(\gamma_1 \vartheta, \kappa_\Delta \min_{i \in [0:k]} \hat\phi_i\Big)
  \quad \text{(12.2.13)}.$$
The same bound holds for $\Delta_{k+1}$.

The constant $\kappa_\Delta$ is `Optimization.trqKappaDelta`. It depends on the derivatives of
$f$ at $x_0$. -/
theorem lemma_12_2_3 (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) (hf : AssumptionD1pL f q L)
    (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ trqStop f P q ε ϑ x Δ d i) :
    (0 < trqKappaDelta f P q L ϑ (x 0) ∧ trqKappaDelta f P q L ϑ (x 0) < 1) ∧
      min (P.γ₁ * ϑ) (trqKappaDelta f P q L ϑ (x 0) * prefixMin (trqGapSeq f ϑ x Δ jk d) k) ≤
        Δ k ∧
      min (P.γ₁ * ϑ) (trqKappaDelta f P q L ϑ (x 0) * prefixMin (trqGapSeq f ϑ x Δ jk d) k) ≤
        Δ (k + 1) :=
  IsTRqRun.radius_ge_of_anchored (X := univ) (algorithm_12_2_1_iff_feasible.1 h)
    (hf.toLipschitzDerivsAnchored univ) subset_rfl (fun _ hy _ => hy) (mem_univ _) hϑ hϑ1 hε hk

end TRq

section TRqComplexity

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {flow : ℝ} {P : TRqParams} {q : ℕ}
  {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ} {jk : ℕ → ℕ}
  {d : ℕ → ℕ → EuclideanSpace ℝ (Fin n)} {L : ℕ → ℝ}

/-- **Theorem 12.2.5** of [cartis2022evaluation] (complexity of TRq). Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.Bb with the lower bound $f_{\mathrm{low}}$ and
f.D1qL, and let $\varepsilon \in (0, 1]^q$ and $\varepsilon_{\min} \le \vartheta \le 1$. Every
TRq run terminates at some iteration $k_\varepsilon$. The radius $\delta_\varepsilon =
\min(\Delta_{k_\varepsilon}, \vartheta)$ lies in $(0, 1]$, and
$x_\varepsilon = x_{k_\varepsilon}$ is an $(\varepsilon, \delta_\varepsilon)$-approximate $q$-th
order minimizer, that is, $\phi^{\delta_\varepsilon}_{f,j}(x_\varepsilon) \le \varepsilon_j
\delta_\varepsilon^j/j!$ for all $j \in [1:q]$. The number of evaluations of $f$ is at most
$$\kappa^A \frac{f(x_0) - f_{\mathrm{low}}}{\varepsilon_{\min}^{q+1}} + \kappa^B |\log
  \varepsilon_{\min}| + \kappa^C \quad \text{(12.2.21)},$$
and the number of evaluations of the derivatives is at most $\kappa^S (f(x_0) -
f_{\mathrm{low}})/\varepsilon_{\min}^{q+1} + 1$ (12.2.22). Here $\kappa^S = q!/(\eta_1
(\varsigma \kappa_\Delta)^{q+1})$, $\kappa^A = \kappa^S (1 + \log \gamma_3/|\log \gamma_2|)$,
$\kappa^B = 1/|\log \gamma_2|$ and $\kappa^C = |\log(\varsigma \kappa_\Delta/\Delta_0)|/|\log
\gamma_2| + 1$.

**Typo.** The source prints the conclusion with $\phi^{\delta_\varepsilon}_{f,q}$ for every $j$;
it is $\phi^{\delta_\varepsilon}_{f,j}$.

The constants are `Optimization.kappaATRq`, `Optimization.kappaBTRq`, `Optimization.kappaCTRq`
and `Optimization.kappaSTRq`. The constant $\kappa_\Delta$ of (12.2.14) depends on $x_0$. If all
derivatives of $f$ vanish at $x_0$, the run stops at once. -/
theorem theorem_12_2_5 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionD1pL f q L)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) :
    ∃ kε, IsFirstHit (trqStop f P q ε ϑ x Δ d) kε ∧
      min (Δ kε) ϑ ∈ Ioc 0 1 ∧
      IsEpsDeltaApproxMinimizer f q ε (fun _ => min (Δ kε) ϑ) (x kε) ∧
      (funEvalCount kε : ℝ) ≤
        kappaATRq f P q L ϑ (x 0) * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) +
          kappaBTRq P * |Real.log (finMin 1 ε q)| + kappaCTRq f P q L ϑ (x 0) ∧
      (derivEvalCount (fun k => P.η₁ ≤ trqRho f x s jk k) kε : ℝ) ≤
        kappaSTRq f P q L ϑ (x 0) * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) + 1 := by
  obtain ⟨kε, hk, -, hδ, hcert, hF, hD⟩ := IsTRqRun.complexity (X := univ)
    (fun y _ => hb y) (hf.toLipschitzDerivsAnchored univ) subset_rfl (fun _ hy _ => hy)
    (mem_univ _) hε hϑ hϑ1 (algorithm_12_2_1_iff_feasible.1 h)
  have hU : {e : EuclideanSpace ℝ (Fin n) | x kε + e ∈ (univ : Set _)} = univ := by ext; simp
  rw [hU] at hcert
  exact ⟨kε, hk, hδ, ⟨fun j hj => ⟨hε j hj, hδ⟩, hcert⟩, hF, hD⟩

end TRqComplexity

/-! ### Functions of one variable -/

section OneDim

/-- **f.D1rL for functions of one variable.** Let $G : \mathbb{R} \to \mathbb{R}$ be $C^r$, let its
$r$-th derivative be Lipschitz continuous with the constant $L$, and let $|G^{(j)}(t)| \le B$
for all $t$ and $j \in [0:r]$. Then $G$ satisfies f.D1rL with all constants equal to
$\max(1, L, B)$.

This criterion supports the slow examples of Theorems 12.2.6, 12.2.15 and 12.2.17 of
[cartis2022evaluation]. -/
theorem assumptionD1pL_real {G : ℝ → ℝ} {r : ℕ} {L B : ℝ} (hG : ContDiff ℝ r G)
    (hL : ∀ s t, |iteratedDeriv r G s - iteratedDeriv r G t| ≤ L * |s - t|)
    (hB : ∀ j ≤ r, ∀ t, |iteratedDeriv j G t| ≤ B) :
    AssumptionD1pL G r (fun _ => max 1 (max L B)) := by
  refine .of_iteratedFDerivLipschitzOn hG (fun _ _ => le_max_left _ _) fun j hj => ?_
  obtain ⟨hj1, hjr⟩ := Finset.mem_Icc.1 hj
  rcases hjr.lt_or_eq with hjr | rfl
  · have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (Nat.zero_le r) 0)
    refine IteratedFDerivHolderOn.mono_const (iteratedFDerivLipschitzOn_of_norm_le convex_univ
      (fun y _ => (hG.of_le (by exact_mod_cast hjr)).contDiffAt) (L := B) fun y _ => ?_) ?_
    · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact hB (j + 1) hjr y
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · rw [iteratedFDerivLipschitzOn_iff]
    intro s _ t _
    rw [norm_iteratedFDeriv_sub_real, Real.norm_eq_abs]
    refine (hL s t).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    exact (le_max_left _ _).trans (le_max_right _ _)

end OneDim

/-! ### Sharpness for TRq (Theorem 12.2.6) -/

section TRqSharp

/-- **Theorem 12.2.6** of [cartis2022evaluation] (slow convergence of TRq). Let $q \ge 1$. There are
$f_{\mathrm{low}}$ and $L \ge 1$, which depend only on $q$, with the following property. For
every $\varepsilon \in (0, 1/q!]$ and all TRq constants with $\Delta_0 = \varepsilon$, there is
$f : \mathbb{R} \to \mathbb{R}$ with $f \ge f_{\mathrm{low}}$ that satisfies f.D1qL with all
constants $L_{f,j} = L$, and a TRq run for the tolerances $\varepsilon_j = j!\, \varepsilon$ and
the threshold $\vartheta = 1$, such that:
* $x_k = k\varepsilon$, $s_k = \Delta_k = \delta_k = \varepsilon$ for all $k$, so that
  $x_0 = 0$;
* $\rho_k = 1$ for all $k < k_\varepsilon$, where $k_\varepsilon = \lceil \varepsilon^{-(q+1)}
  \rceil$;
* the run terminates at $k_\varepsilon$, and $\phi^{\varepsilon}_{f,j}(x_{k_\varepsilon}) \le
  \varepsilon_j \varepsilon^j/j! = \varepsilon^{j+1}$ for $j \in [1:q]$;
* the numbers of evaluations of $f$ and of its derivatives are at least
  $\varepsilon^{-(q+1)} + 1$.

So TRq can need $\varepsilon^{-(q+1)}$ iterations. As in the source, the initial radius
$\Delta_0 = \varepsilon$ depends on $\varepsilon$, and the example shows that the order
$\varepsilon^{-(q+1)}$ of Theorem 12.2.5 is attained.

**Correction.** The proof of the source in Appendix B uses slow data that are wrong. They
decrease $f$ by $\frac12 \varepsilon^{q+1} c_k$ while the Taylor decrease is
$\varepsilon^{q+1} c_k$, so (B.12.8) fails; $x_k = (k-1)\varepsilon$ must be $k\varepsilon$;
$\varepsilon^{q+1} k_\varepsilon \le 1$ is false, and only
$\varepsilon^{q+1} k_\varepsilon \le 2$ holds; and the residuals at the orders $1 \le j < q$ are
$2\, q!/(q-j)!\, s_k^{q-j+1}$, where the source omits the factor $q!/(q-j)!$. The proof uses the
corrected data of `Optimization.exists_slowTRq_interpolant`.

The approximate optimality at $x_{k_\varepsilon}$ is `Optimization.IsEpsDeltaApprox` for the
radii $\delta_j = \varepsilon$. -/
theorem theorem_12_2_6 {q : ℕ} (hq : 1 ≤ q) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : TRqParams, P.Δ₀ = ε →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ AssumptionD1pL f q (fun _ => L) ∧
        ∃ (x s : ℕ → ℝ) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ),
          algorithm_12_2_1 f P q (fun j => j ! * ε) 1 x s Δ jk d ∧
          (∀ k, x k = k * ε ∧ s k = ε ∧ Δ k = ε ∧ min (Δ k) 1 = ε) ∧
          (∀ k < ⌈(ε ^ (q + 1))⁻¹⌉₊, trqRho f x s jk k = 1) ∧
          IsFirstHit (trqStop f P q (fun j => j ! * ε) 1 x Δ d) ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          IsEpsDeltaApprox (ftaylorSeries ℝ f (x ⌈(ε ^ (q + 1))⁻¹⌉₊)) univ q
            (fun j => j ! * ε) (fun _ => ε) ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (funEvalCount ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤
            (derivEvalCount (fun k => P.η₁ ≤ trqRho f x s jk k) ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨L, B, hL, hB, hG⟩ := exists_slowTRq_interpolant hq
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hεq P hP => ?_⟩
  have hqf : (0 : ℝ) < q ! := by exact_mod_cast q.factorial_pos
  have hε1 : ε ≤ 1 := hεq.trans (by
    rw [div_le_one hqf]; exact_mod_cast Nat.one_le_iff_ne_zero.2 q.factorial_ne_zero)
  set x : ℕ → ℝ := fun k => k * ε with hx
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε x hε hε1 fun k _ => by simp only [hx]; push_cast; ring
  set kε : ℕ := ⌈(ε ^ (q + 1))⁻¹⌉₊ with hkε
  have hkε1 : 1 ≤ kε := Nat.one_le_iff_ne_zero.2 (by
    rw [hkε]; exact (Nat.ceil_pos.2 (by positivity)).ne')
  have hkεge : (ε ^ (q + 1))⁻¹ ≤ kε := by rw [hkε]; exact Nat.le_ceil _
  clear_value kε
  have hkεpos : (0 : ℝ) < kε := by exact_mod_cast hkε1
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ k, c k = 2 - k / kε := ⟨_, fun _ => rfl⟩
  have hGq : ∀ k ≤ kε, iteratedDeriv q G (x k) = -ε * c k * q ! := fun k hk => by
    rw [hc]; exact (hGd k hk).2
  have hGf' : ∀ k < kε, G (x (k + 1)) = G (x k) - ε ^ (q + 1) * c k := fun k hk => by
    rw [hc]; exact hGf k hk
  have hc1 : ∀ k < kε, 1 < c k := fun k hk => by
    rw [hc]
    have : (k : ℝ) / kε < 1 := (div_lt_one hkεpos).2 (by exact_mod_cast hk)
    linarith
  have hckε : c kε = 1 := by rw [hc, div_self hkεpos.ne']; ring
  have hc0 : ∀ k ≤ kε, 0 ≤ c k := fun k hk => by
    rw [hc]
    have : (k : ℝ) / kε ≤ 1 := (div_le_one hkεpos).2 (by exact_mod_cast hk)
    linarith
  -- Taylor decrements along the iterates
  have hdec_lt : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q, j < q → ∀ e : ℝ,
      (ftaylorSeries ℝ G (x k)).taylorDecrement j e = 0 := fun k hk j hj hjq e =>
    taylorDecrement_real_eq_zero (fun i hi => (hGd k hk).1 i (Finset.mem_Icc.1 hi).1
      (lt_of_le_of_lt (Finset.mem_Icc.1 hi).2 hjq)) e
  have hdec_q : ∀ k ≤ kε, ∀ e : ℝ,
      (ftaylorSeries ℝ G (x k)).taylorDecrement q e = ε * c k * e ^ q := fun k hk e => by
    rw [taylorDecrement_real_spike (m := q) (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
      (fun i hi hiq => (hGd k hk).1 i (Finset.mem_Icc.1 hi).1
        (lt_of_le_of_ne (Finset.mem_Icc.1 hi).2 hiq)), hGq k hk]
    field_simp
  have hδ : min ε 1 = ε := min_eq_left hε1
  -- the measures
  have hφ_lt : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q, j < q →
      taylorMeasure (ftaylorSeries ℝ G (x k)) j ε univ = 0 := fun k hk j hj hjq => by
    have := taylorMeasure_real_monomial (a := 0) (m := 0) le_rfl hε.le
      (D := ftaylorSeries ℝ G (x k))
      (j := j) fun e => by rw [hdec_lt k hk j hj hjq, zero_mul]
    rwa [zero_mul] at this
  have hφ_q : ∀ k ≤ kε, taylorMeasure (ftaylorSeries ℝ G (x k)) q ε univ = ε * c k * ε ^ q :=
    fun k hk => taylorMeasure_real_monomial (mul_nonneg hε.le (hc0 k hk)) hε.le (hdec_q k hk)
  -- the witnesses: a fraction `ς` of the measure, exactly
  have hw : ∀ k j, ∃ e : ℝ, IsApproxMeasureStep ((ftaylorSeries ℝ G (x k)).taylorDecrement j)
      (min ε 1) univ P.ς e ∧ (ftaylorSeries ℝ G (x k)).taylorDecrement j e =
        P.ς * taylorMeasure (ftaylorSeries ℝ G (x k)) j (min ε 1) univ := fun k j =>
    exists_isApproxMeasureStep_eq isClosed_univ (mem_univ 0) (starConvex_univ 0)
      (le_min hε.le zero_le_one)
      ((ftaylorSeries ℝ G (x k)).continuous_taylorDecrement j).continuousOn
      ((ftaylorSeries ℝ G (x k)).taylorDecrement_zero_right j) ⟨P.ς_pos.le, P.ς_le_one⟩
  choose d hd hdeq using hw
  set εv : ℕ → ℝ := fun j => j ! * ε with hεv
  -- the test
  have htest : ∀ k ≤ kε, (trqStop G P q εv 1 x (fun _ => ε) d k ↔ k = kε) := by
    intro k hk
    rw [trqStop, trqTest_iff, measureTestPasses_iff]
    simp only [hδ]
    constructor
    · intro ht
      by_contra hne
      have hlt : k < kε := lt_of_le_of_ne hk hne
      have := ht q (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
      rw [hdeq, hδ, hφ_q k hk] at this
      have h1 := hc1 k hlt
      have : P.ς * (ε * c k * ε ^ q) ≤ P.ς * (q ! * ε) * ε ^ q / q ! := this
      have hς := P.ς_pos
      have e : P.ς * (q ! * ε) * ε ^ q / q ! = P.ς * (ε * 1 * ε ^ q) := by field_simp
      rw [e] at this
      have := le_of_mul_le_mul_left this hς
      have := le_of_mul_le_mul_left (by linarith : ε * ε ^ q * c k ≤ ε * ε ^ q * 1)
        (by positivity : (0 : ℝ) < ε * ε ^ q)
      linarith
    · intro hkk j hj
      rw [hdeq, hδ]
      rcases (Finset.mem_Icc.1 hj).2.lt_or_eq with hjq | rfl
      · rw [hφ_lt k hk j hj hjq, mul_zero]
        have := P.ς_pos
        positivity
      · rw [hφ_q k hk, hkk, hckε]
        apply le_of_eq
        simp only [hεv]
        field_simp
  have hfirst : IsFirstHit (trqStop G P q εv 1 x (fun _ => ε) d) kε :=
    ⟨(htest kε le_rfl).2 rfl, fun i hi => fun h => hi.ne ((htest i hi.le).1 h)⟩
  have hbefore : ∀ k, (∀ i ≤ k, ¬ trqStop G P q εv 1 x (fun _ => ε) d i) → k < kε := by
    intro k hk
    by_contra hge
    exact hk kε (not_lt.1 hge) hfirst.1
  -- the ratio
  have hρ : ∀ k < kε, trqRho G x (fun _ => ε) (fun _ => q) k = 1 := by
    intro k hk
    rw [trqRho, trqRatio_eq, reductionRatio_def, hdec_q k hk.le]
    have hxk : x k + ε = x (k + 1) := by simp only [hx]; push_cast; ring
    rw [hxk, hGf' k hk]
    have := hc1 k hk
    have : 0 < ε * c k * ε ^ q := by positivity
    field_simp
    ring
  have hcert : IsEpsDeltaApprox (ftaylorSeries ℝ G (x kε)) univ q (fun j => j ! * ε)
      (fun _ => ε) := by
    have h1 : MeasureTestPasses (fun j => (ftaylorSeries ℝ G (x kε)).taylorDecrement j) q P.ς
        εv (fun _ => min ε 1) (d kε) := hfirst.1
    have h := MeasureTestPasses.isEpsDeltaApprox (S := univ) P.ς_pos (fun j _ => hd kε j) h1
    rwa [show (fun _ : ℕ => min ε 1) = fun _ => ε from funext fun _ => hδ] at h
  have hderiv : (kε : ℝ) + 1 ≤ (derivEvalCount
      (fun k => P.η₁ ≤ trqRho G x (fun _ => ε) (fun _ => q) k) kε : ℝ) := by
    obtain ⟨m, rfl⟩ : ∃ m, kε = m + 1 := ⟨kε - 1, by omega⟩
    rw [derivEvalCount_add_one]
    have hfail : (failureSet (fun k => P.η₁ ≤ trqRho G x (fun _ => ε) (fun _ => q) k) m).card =
        0 := Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun j hj => by
      rw [mem_failureSet] at hj
      exact hj.2 (by rw [hρ j (by omega)]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le))
    have := card_successSet_add_card_failureSet
      (succ := fun k => P.η₁ ≤ trqRho G x (fun _ => ε) (fun _ => q) k) (k := m)
    rw [hfail, add_zero] at this
    rw [this]
    push_cast
    linarith
  refine ⟨G, neg_le_of_abs_iteratedDeriv_zero_le fun t => hGB 0 (Nat.zero_le q) t,
    assumptionD1pL_real hGc hGL hGB, x, fun _ => ε, fun _ => ε, fun _ => q, d, ?_,
    fun k => ⟨rfl, rfl, rfl, hδ⟩, hρ, hfirst, hcert,
    by rw [funEvalCount_eq]; push_cast; linarith, by linarith⟩
  refine ⟨⟨hP.symm, fun k hk => ?_, fun k hk => ?_⟩, fun k _ j _ => hd k j,
    fun k _ => hP ▸ P.Δ₀_le_Δmax⟩
  · -- Step 2
    have hkε' := hbefore k hk
    refine ⟨Finset.mem_Icc.2 ⟨hq, le_rfl⟩, ?_, fun i hi hiq => ?_, ⟨?_, mem_univ _⟩, ?_⟩
    · simp only [hδ]
      rw [hdeq, hδ, hφ_q k hkε'.le]
      have h1 := hc1 k hkε'
      have hς := P.ς_pos
      have e : P.ς * (q ! * ε) * ε ^ q / q ! = P.ς * (ε * 1 * ε ^ q) := by field_simp
      rw [e]
      gcongr
    · simp only [hδ]
      rw [hdeq, hδ, hφ_lt k hkε'.le i hi hiq, mul_zero]
      have := P.ς_pos
      positivity
    · simp [Real.norm_eq_abs, abs_of_pos hε]
    · rw [hdeq, hδ, hφ_q k hkε'.le, hdec_q k hkε'.le]
      have := hc0 k hkε'.le
      calc P.ς * (ε * c k * ε ^ q) ≤ 1 * (ε * c k * ε ^ q) :=
            mul_le_mul_of_nonneg_right P.ς_le_one (by positivity)
        _ = ε * c k * ε ^ q := one_mul _
  · -- Steps 3–4
    have hkε' := hbefore k hk
    have hρk := hρ k hkε'
    refine ⟨?_, ⟨fun _ => ⟨le_rfl, ?_⟩, fun _ h => ?_, fun h => ?_⟩⟩
    · change x (k + 1) = if P.η₁ ≤ trqRho G x (fun _ => ε) (fun _ => q) k then x k + ε else x k
      rw [hρk, ite_eq_left (P.η₁_le_η₂.trans P.η₂_lt_one.le)]
      simp only [hx]; push_cast; ring
    · exact le_mul_of_one_le_left hε.le P.one_le_γ₃
    · change trqRho G x (fun _ => ε) (fun _ => q) k < P.η₂ at h
      rw [hρk] at h; linarith [P.η₂_lt_one]
    · change trqRho G x (fun _ => ε) (fun _ => q) k < P.η₁ at h
      rw [hρk] at h; linarith [P.η₁_le_η₂, P.η₂_lt_one]

end TRqSharp

/-! ### The ARqp algorithm (Section 12.2.2.1) -/

section ARqp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Algorithm 12.2.2** of [cartis2022evaluation] with a feasible set (ARqp-SC, Section 14.2). Let
$X \subseteq E$. A **run of ARqp-SC** is a run of Algorithm 12.2.2 in which $x_0 \in X$, the
steps satisfy $x_k + s_k \in X$, the Step-1 displacements are taken among the feasible
displacements $\{d \mid x_k + d \in X\}$, the Step-2 displacements among
$\{d \mid x_k + s_k + d \in X\}$, and termination in Step 2 needs $0$ to minimize the model over
the feasible steps.

It is `Optimization.IsARqpRun f X` with the exact model data `Optimization.arqpData`. For
$X = E$ it is `CartisGouldToint.Chapter12.algorithm_12_2_2`. -/
def algorithm_12_2_2_feasible (f : E → ℝ) (X : Set E) (P : ARqpParams) (p q : ℕ)
    (ε δ₀ : ℕ → ℝ) (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) : Prop :=
  IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm

/-- **Algorithm 12.2.2** of [cartis2022evaluation] (ARqp). Let $E$ be a real inner product space and
$f : E \to \mathbb{R}$. A **run of ARqp** with the constants $P$ ($\sigma_0$, $\sigma_{\min}$,
$\eta_1$, $\eta_2$, $\gamma_1$, $\gamma_2$, $\gamma_3$, $\theta$, $\varsigma$), the model degree
$p$, the order $q$, the tolerances $\varepsilon_j$ and the initial radii $\delta_{0,j}$ consists
of iterates $x_k$, steps $s_k$, weights $\sigma_k$, Step-1 radii $\delta_{k,j}$ and
displacements $d_{k,j}$, and Step-2 radii $\delta_{s_k,j}$ and displacements $d^m_{k,j}$, such
that:
* Step 1: at every iteration $k$ reached, $d_{k,j}$ is a $\varsigma$-approximate optimality
  displacement of radius $\delta_{k,j}$ for $\Delta T_{f,j}(x_k, \cdot)$, $j \in [1:q]$
  (12.2.26); the run stops if $\Delta T_{f,j}(x_k, d_{k,j}) \le \varsigma \varepsilon_j
  \delta_{k,j}^j/j!$ for all $j \in [1:q]$;
* Step 2: otherwise the step satisfies $m_k(s_k) \le m_k(0)$ (12.2.27), with the model $m_k(s) =
  T_{f,p}(x_k, s) + \sigma_k \|s\|^{p+1}/(p+1)!$ of (12.2.23); the run stops if
  $m_k(s_k) = m_k(0)$, which is allowed only if $0$ is a global minimizer of $m_k$; the radii
  satisfy $\delta_{s_k,j} \in (0, 1]$; and either $\|s_k\| \ge 1$ (12.2.28), or for every
  $j \in [1:q]$ the displacement $d^m_{k,j}$ is a $\varsigma$-approximate optimality
  displacement of radius $\delta_{s_k,j}$ for $\Delta T_{m_k,j}(s_k, \cdot)$ with $\Delta
  T_{m_k,j}(s_k, d^m_{k,j}) \le \varsigma \theta \varepsilon_j \delta_{s_k,j}^j/j!$ (12.2.29);
* Steps 3–4: the iterate and the weight are updated as in an adaptive-regularization method with
  $\sigma_0$ given and the ratio $\rho_k = (f(x_k) - f(x_k + s_k))/\Delta T_{f,p}(x_k, s_k)$
  (12.2.30); a successful iteration sets $\delta_{k+1} = \delta_{s_k}$, and an unsuccessful one
  keeps $\delta_{k+1} = \delta_k$ and $d_{k+1} = d_k$.

**Typo.** The source continues in Step 1 when $\Delta T_{f,j}(x_k, d_{k,j}) \ge \varsigma
\varepsilon_j \delta_{k,j}^j/j!$ for some $j$; with $\ge$ the sharpness examples of the source
never stop. The test here continues on $>$, as the test (12.2.2) of TRq does. The long-step
branch, printed $\|s_k\| > 1$ in (12.2.28), is $\|s_k\| \ge 1$, as in Algorithm 12.2.3.

**Reading.** Termination in Step 2 is allowed only when $0$ is a global minimizer of $m_k$, as
Algorithm 12.2.3 guarantees.

The run is `Optimization.IsARqpRun` with the exact model data `Optimization.arqpData` and no
constraints, whose Steps 2–4 form the generic run `Optimization.IsARRun`. Step 0 of the source
asks $q \le p$, $\varepsilon \in (0, 1)^q$ and $\delta_0 \in (0, 1]^q$; these conditions are
hypotheses of the results below. -/
def algorithm_12_2_2 (f : E → ℝ) (P : ARqpParams) (p q : ℕ) (ε δ₀ : ℕ → ℝ) (x s : ℕ → E)
    (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) : Prop :=
  algorithm_12_2_2_feasible f univ P p q ε δ₀ x s σ δ δs d dm

/-- **Algorithm 12.2.2** of [cartis2022evaluation], well-posedness, with Lemmas 12.2.9 and 12.2.10.
Let $E$ be a finite-dimensional real inner product space, $f : E \to \mathbb{R}$, $1 \le p$,
$q \le p$, $\varepsilon_j > 0$ and $\delta_{0,j} \in (0, 1]$ for $j \in [1:q]$. For every
$x_0 \in E$ there is an ARqp run that starts at $x_0$, whose Step-2 radii satisfy
$\delta_{s_k,j} = 1$ for $j \in [1:\min(q, 2)]$ at every iteration $k$ reached. -/
theorem algorithm_12_2_2_exists [FiniteDimensional ℝ E] (f : E → ℝ) (P : ARqpParams) {p q : ℕ}
    (hp : 1 ≤ p) (hq : q ≤ p) {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (x₀ : E) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm ∧
      ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs k j = 1 := by
  obtain ⟨x, s, σ, δ, δs, d, dm, h0, h, hrad⟩ := exists_isARqpRun f P hp hq hε hδ₀
    (fun y => ∑ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖) (fun _ => by positivity)
    (fun y i hi => Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f y‖)
      (fun _ _ => norm_nonneg _) hi) x₀
  exact ⟨x, s, σ, δ, δs, d, dm, h0, h, fun k hk => (hrad k hk).1⟩

/-- **Example 12.2.1** of [cartis2022evaluation], with Example 12.1.3. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $x, e \in \mathbb{R}^n$, $\beta, \sigma \in \mathbb{R}$ and
$p \ge 1$. If $f(x) = 0$, $\nabla f(x)[s] = -\beta \langle e, s \rangle$ for all $s$, and
$\nabla^j f(x) = 0$ for $j \in [2:p]$, then the ARqp model (12.2.23) at $x$ is the model of
Example 12.1.3,
$$m(s) = -\beta \langle e, s \rangle + \frac{\sigma}{(p+1)!} \|s\|^{p+1}.$$
Moreover, let $\|e\| = 1$, and let $m$ be this model for $p = 5$, $\sigma = 5!$ and $\beta = 1$,
whose global minimizer is $s^* = e$. For all $\theta, \varepsilon_3$ with
$\theta \varepsilon_3 \le 1$ and every radius $\delta \in (15/19, 1]$,
$$\phi^\delta_{m,3}(s^*) > \theta \varepsilon_3 \frac{\delta^3}{3!}.$$

The condition (12.2.29) at the order $3$ with the radius $\delta$ implies
$\phi^\delta_{m,3}(s_k) \le \theta \varepsilon_3 \delta^3/3!$. So such radii are not admissible
at $s_k = s^*$; in particular $\delta_{s_k,3} = 1$ is not. Along $d = -\delta s^*$ one has
$\Delta T_{m,3}(s^*, d) = -5\delta^2/2 + 10\delta^3/3$. The global minimizer
$s^* = (\beta p!/\sigma)^{1/p} e$ of the model of Example 12.1.3 is given by
`CartisGouldToint.Chapter12.example_12_1_3`. The ARqp model is `Optimization.regularizedModel`,
and the model of Example 12.1.3 is `CartisGouldToint.Chapter12.example1213Model`. -/
theorem example_12_2_1 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {x e : EuclideanSpace ℝ (Fin n)}
    {β σ : ℝ} {p : ℕ} (hp : 1 ≤ p) (hx : f x = 0)
    (h1 : ∀ s, iteratedFDeriv ℝ 1 f x (fun _ => s) = -β * inner ℝ e s)
    (hj : ∀ j ∈ Finset.Icc 2 p, iteratedFDeriv ℝ j f x = 0) :
    regularizedModel (ftaylorSeries ℝ f x) p σ = example1213Model β σ p e ∧
      (‖e‖ = 1 → ∀ θ ε₃ : ℝ, θ * ε₃ ≤ 1 → ∀ δ ∈ Ioc (15 / 19 : ℝ) 1,
        θ * ε₃ * δ ^ 3 / 3 ! < phiMeasure (example1213Model 1 (5 !) 5 e) 3 δ e) := by
  refine ⟨funext fun s => ?_, fun he θ ε₃ hθε δ hδ => ?_⟩
  · rw [regularizedModel_def, example1213Model, FormalMultilinearSeries.taylorSum_eq_add]
    have hsum : ∑ i ∈ Finset.Icc 1 p, ((i ! : ℝ))⁻¹ • ftaylorSeries ℝ f x i (fun _ => s) =
        -β * inner ℝ e s := by
      rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.2 ⟨le_rfl, hp⟩)]
      · simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
        exact h1 s
      · intro i hi hi1
        have : ftaylorSeries ℝ f x i = 0 := hj i (Finset.mem_Icc.2
          ⟨by have := (Finset.mem_Icc.1 hi).1; omega, (Finset.mem_Icc.1 hi).2⟩)
        rw [this]; simp
    have h0 : ftaylorSeries ℝ f x 0 0 = f x := by simp [ftaylorSeries]
    rw [hsum, h0, hx, zero_add]
    ring
  · obtain ⟨hδ0, hδ1⟩ := hδ
    have hδpos : (0 : ℝ) < δ := by linarith
    have hβ : ((5 ! : ℕ) : ℝ) / (5 ! : ℕ) = 1 := div_self (by positivity)
    have hd := example1213_taylorDecrement_unit (σ := (5 ! : ℕ)) (p := 5) he ((-δ) • e)
    rw [hβ] at hd
    have hin : inner ℝ e ((-δ) • e) = -δ := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq, he]; ring
    have hnorm : ‖(-δ) • e‖ ^ 2 = δ ^ 2 := by
      rw [norm_smul, he, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos]; ring
    rw [hin, hnorm] at hd
    have hle := taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (example1213Model 1 (5 !) 5 e) e) 3 (S := univ) (d := (-δ) • e) (δ := δ)
      ⟨mem_closedBall_zero_iff.2 (by
        rw [norm_smul, he, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos, mul_one]), mem_univ _⟩
    rw [hd] at hle
    refine lt_of_lt_of_le ?_ hle
    norm_num [Nat.factorial]
    nlinarith [mul_pos hδpos hδpos,
      mul_le_mul_of_nonneg_right hθε (by positivity : (0 : ℝ) ≤ δ ^ 3)]

/-- The model $m(s) = s^2 (s - \frac12)^2$ on $\mathbb{R}$ of Example 12.2.2. -/
noncomputable def example1222Model (s : ℝ) : ℝ := s ^ 2 * (s - 1 / 2) ^ 2

/-- The model of Example 12.2.2 expands as $s^2 (s - \frac12)^2 = s^4 - s^3 + s^2/4$. -/
theorem example1222Model_eq (s : ℝ) : example1222Model s = s ^ 4 - s ^ 3 + s ^ 2 / 4 := by
  rw [example1222Model]; ring

/-- The third-order Taylor decrement of the model of Example 12.2.2 at $0$ is
$\Delta T_{m,3}(0, d) = d^3 - d^2/4$. -/
theorem example1222Model_taylorDecrement (d : ℝ) :
    (ftaylorSeries ℝ example1222Model 0).taylorDecrement 3 d = d ^ 3 - d ^ 2 / 4 := by
  have hc : ContDiffAt ℝ 4 example1222Model 0 := by
    unfold example1222Model; fun_prop
  set a : ℕ → ℝ := fun i => if i = 2 then d ^ 2 / 4 else if i = 3 then -d ^ 3 else
    if i = 4 then d ^ 4 else 0 with ha
  have hpoly : ∀ t : ℝ, example1222Model (0 + t • d) =
      example1222Model 0 + ∑ i ∈ Finset.Icc 1 4, t ^ i * a i := by
    intro t
    rw [show Finset.Icc 1 4 = {1, 2, 3, 4} by decide]
    simp [ha, example1222Model_eq, smul_eq_mul]
    ring
  rw [ftaylorSeries_taylorDecrement_eq, taylorPolynomial_eq_of_poly hc
    (Eventually.of_forall hpoly) (by norm_num : 3 ≤ 4)]
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]
  simp [ha]
  ring

/-- **Example 12.2.2** of [cartis2022evaluation]. Let $m(s) = s^2 (s - \frac12)^2 = \frac14 s^2 (1 -
4s) + s^4$ on $\mathbb{R}$. Then:
* for every $f : \mathbb{R} \to \mathbb{R}$ and $x \in \mathbb{R}$ with $f(x) = 0$, $f'(x) = 0$,
  $f''(x) = \frac12$ and $f'''(x) = -6$, the ARqp model (12.2.23) at $x$ with $p = 3$ and
  $\sigma = 4!$ is $m$;
* the global minimizers of $m$ are exactly $0$ and $\frac12$;
* $\phi^1_{m,3}(0) = \frac34$;
* $\phi^\delta_{m,3}(0) = 0$ for every $\delta \le \frac14$, and $\phi^\delta_{m,3}(0) > 0$ for
  every $\delta > \frac14$.

So the Step-1 test with radius $1$ at $x_k$ does not stop, although the global model minimizer
$s_k = 0$ makes the algorithm stop in Step 2.

**Typo.** The source prints the expansion $\frac12 s^2 (1 - 2s) + s^4$, which has the unique
minimizer $0$, together with the value $-\frac12$ and the threshold $\frac12$. These do not
match $s^2 (s - \frac12)^2$, whose expansion, measure and threshold are those above.

The model is `CartisGouldToint.Chapter12.example1222Model`, and the measure is
`CartisGouldToint.Chapter12.phiMeasure`. For $\delta < 0$ the ball of radius $\delta$ is empty,
and the measure is $0$. -/
theorem example_12_2_2 :
    (∀ (f : ℝ → ℝ) (x : ℝ), f x = 0 → iteratedDeriv 1 f x = 0 → iteratedDeriv 2 f x = 1 / 2 →
      iteratedDeriv 3 f x = -6 →
        regularizedModel (ftaylorSeries ℝ f x) 3 (4 !) = example1222Model) ∧
    (∀ s, IsMinOn example1222Model univ s ↔ s = 0 ∨ s = 1 / 2) ∧
    phiMeasure example1222Model 3 1 0 = 3 / 4 ∧
    (∀ δ : ℝ, δ ≤ 1 / 4 → phiMeasure example1222Model 3 δ 0 = 0) ∧
    (∀ δ : ℝ, 1 / 4 < δ → 0 < phiMeasure example1222Model 3 δ 0) := by
  have hnonneg : ∀ t, 0 ≤ example1222Model t := fun t => by unfold example1222Model; positivity
  refine ⟨fun f x h0 h1 h2 h3 => funext fun s => ?_, fun s => ⟨fun hs => ?_, fun hs => ?_⟩, ?_,
    fun δ hδ => ?_, fun δ hδ => ?_⟩
  · rw [regularizedModel_def, FormalMultilinearSeries.taylorSum_eq_add,
      show Finset.Icc 1 3 = {1, 2, 3} by decide]
    have h00 : ftaylorSeries ℝ f x 0 0 = f x := by simp [ftaylorSeries]
    rw [h00, h0, Real.norm_eq_abs, (by decide : Even 4).pow_abs, example1222Model_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, ftaylorSeries_real_apply, ftaylorSeries_real_apply,
      ftaylorSeries_real_apply, h1, h2, h3]
    norm_num [Nat.factorial]
    ring
  · have h1 : example1222Model s ≤ example1222Model 0 := hs (mem_univ 0)
    have h2 : example1222Model s = 0 :=
      le_antisymm (h1.trans_eq (by simp [example1222Model])) (hnonneg s)
    rw [example1222Model, mul_eq_zero] at h2
    rcases h2 with h | h
    · exact Or.inl (pow_eq_zero_iff (by norm_num) |>.1 h)
    · right; have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h; linarith
  · refine fun t _ => le_trans (le_of_eq ?_) (hnonneg t)
    rcases hs with rfl | rfl <;> simp [example1222Model]
  · refine le_antisymm (decrementMeasure_le ⟨0, by simp, mem_univ _⟩ fun d hd => ?_) ?_
    · have hd1 : |d| ≤ 1 := by simpa [Real.norm_eq_abs] using hd.1
      rw [example1222Model_taylorDecrement]
      obtain ⟨h1, h2⟩ := abs_le.1 hd1
      nlinarith [sq_nonneg (d + 3 / 8)]
    · have := taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ example1222Model 0) 3
        (S := univ) (d := 1) (δ := 1) ⟨by simp, mem_univ _⟩
      rw [example1222Model_taylorDecrement] at this
      linarith
  · rcases lt_or_ge δ 0 with hneg | hδ0
    · rw [phiMeasure_def, taylorMeasure_eq_sSup, closedBall_eq_empty.2 hneg, empty_inter,
        image_empty, Real.sSup_empty]
    refine le_antisymm (decrementMeasure_le ⟨0, mem_closedBall_self hδ0, mem_univ _⟩
      fun d hd => ?_) (phiMeasure_nonneg _ _ hδ0 _)
    have hdδ : |d| ≤ δ := by simpa [Real.norm_eq_abs] using hd.1
    rw [example1222Model_taylorDecrement]
    have : d ≤ 1 / 4 := (le_abs_self d).trans (hdδ.trans hδ)
    nlinarith [sq_nonneg d]
  · have := taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ example1222Model 0) 3
      (S := univ) (d := δ) (δ := δ)
      ⟨mem_closedBall_zero_iff.2 (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]),
        mem_univ _⟩
    rw [example1222Model_taylorDecrement] at this
    refine lt_of_lt_of_le ?_ this
    nlinarith [mul_pos (by linarith : (0 : ℝ) < δ) (by linarith : (0 : ℝ) < δ)]

/-- **Algorithm 12.2.3** of [cartis2022evaluation] (a detailed Step 2 for ARqp). Let
$m : E \to \mathbb{R}$ be a model with the global minimal value $m^* = \inf_s m(s)$, and let
$q$, $\varsigma$, $\theta$ and the tolerances $\varepsilon_j$ be given. A pair $(s, \delta_s)$
is an **output of Algorithm 12.2.3** if some execution started (Step 2.1) with a parameter
$\mu_0 \in (0, 1]$ and all radii equal to $1$ returns it. An execution repeats the following
steps, where $\phi^{\delta}_{m,j}(s) = \sup_{\|d\| \le \delta} \Delta T_{m,j}(s, d)$:
* Step 2.2: compute a step $s_\mu$ with $\mu (m(0) - m^*) \le m(0) - m(s_\mu)$ (12.2.34);
* Step 2.3: if $\|s_\mu\| \ge 1$, return $(s_\mu, \delta)$; otherwise check the orders
  $j = 1, \dots, q$ in turn;
* Step 2.4: at the order $j$, choose $d$ with $\|d\| \le \delta_j$ and $\varsigma
  \phi^{\delta_j}_{m,j}(s_\mu) \le \Delta T_{m,j}(s_\mu, d)$ (12.2.35). If $\Delta
  T_{m,j}(s_\mu, d) \le \varsigma \theta \varepsilon_j \delta_j^j/j!$, the order $j$ passes, and
  $(s_\mu, \delta)$ is returned after the order $q$. Otherwise, if $j \ge 3$ and $m(s_\mu) -
  m(s_\mu + d) < \varsigma \theta \varepsilon_j \delta_j^j/(2\, j!)$, that is, if (12.2.36)
  fails but (12.2.37) holds, the radius $\delta_j$ is halved and the order $j$ is checked again.
  Otherwise $\mu$ is replaced by $(1 + \mu)/2$, and the execution returns to Step 2.2.

The model $m$ is arbitrary; ARqp uses $m_k$. The definition is
`Optimization.IsDetailedStepOutput` for the instance $J = \{j \mid j \ge 3\}$, without
constraints, of the transition system `Optimization.DetailedStepTrans`, which Algorithm 14.1.2
shares. The value $m^*$ is a Lean infimum, which is $0$ if $m$ is unbounded below. -/
def algorithm_12_2_3 (m : E → ℝ) (q : ℕ) (ς θ : ℝ) (ε : ℕ → ℝ) (s : E) (δs : ℕ → ℝ) : Prop :=
  IsDetailedStepOutput m univ (fun _ => univ)
    (fun j s d => (ftaylorSeries ℝ m s).taylorDecrement j d) q ς θ ε {j | 3 ≤ j} s δs

variable {f : E → ℝ} {p q : ℕ} {L : ℕ → ℝ}

/-- **Lemma 12.2.7** of [cartis2022evaluation]. Assume f.D1pL, let $\sigma \ge 0$ and $x \in E$, and
let $m(s) = T_{f,p}(x, s) + \sigma \|s\|^{p+1}/(p+1)!$. Then $m$ is $C^p$, its $p$-th derivative
is Lipschitz continuous on $E$ with the constant $\sigma$, and
$$\|\nabla^\ell m(s)\| \le 3 L_f + \sigma \quad \text{for all } \|s\| \le 1 \text{ and } \ell
  \in [2:p] \quad \text{(12.2.38)},$$
where $L_f = \max(1, \max_{j \in [1:p]} L_{f,j})$. -/
theorem lemma_12_2_7 (hf : AssumptionD1pL f p L) {σ : ℝ} (hσ : 0 ≤ σ) (x : E) :
    ContDiff ℝ p (regularizedModel (ftaylorSeries ℝ f x) p σ) ∧
      IteratedFDerivLipschitzOn (regularizedModel (ftaylorSeries ℝ f x) p σ) p σ univ ∧
      ∀ s : E, ‖s‖ ≤ 1 → ∀ ℓ ∈ Finset.Icc 2 p,
        ‖iteratedFDeriv ℝ ℓ (regularizedModel (ftaylorSeries ℝ f x) p σ) s‖ ≤
          3 * finMax 1 L p + σ :=
  ⟨contDiff_regularizedModel, iteratedFDerivLipschitzOn_regularizedModel hσ,
    fun _ hs _ hℓ => norm_iteratedFDeriv_regularizedModel_le
      (zero_le_one.trans one_le_finMax)
      (fun _ hi => hf.norm_iteratedFDeriv_le_finMax hi x) hσ hℓ hs⟩

/-- **Lemma 12.2.8** of [cartis2022evaluation]. Assume f.D1pL, let $\sigma \ge 0$ and $x \in E$, and
let $m(s) = T_{f,p}(x, s) + \sigma \|s\|^{p+1}/(p+1)!$. Let $\|s\| \le 1$,
$\alpha \in \mathbb{R}$,
$$0 < \delta \le \min\Big(1, \frac{\alpha}{4 (3 L_f + \sigma)}\Big) \quad \text{(12.2.41)},$$
$\|d\| \le \delta$ and $j \in [1:p]$. If $\Delta T_{m,j}(s, d) \ge \alpha \delta^j/j!$
(12.2.42), then
$$m(s) - m(s + d) \ge \frac12 \alpha \frac{\delta^j}{j!} \quad \text{(12.2.43)}.$$

Here $L_f = \max(1, \max_{j \in [1:p]} L_{f,j})$. -/
theorem lemma_12_2_8 (hf : AssumptionD1pL f p L) {σ : ℝ} (hσ : 0 ≤ σ) (x : E) {s d : E}
    (hs : ‖s‖ ≤ 1) {α δ : ℝ}
    (hδ : δ ∈ Ioc 0 (min 1 (α / (4 * (3 * finMax 1 L p + σ))))) (hd : ‖d‖ ≤ δ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 p)
    (hdec : α * δ ^ j / j ! ≤
      (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s).taylorDecrement j d) :
    1 / 2 * α * δ ^ j / j ! ≤ regularizedModel (ftaylorSeries ℝ f x) p σ s -
      regularizedModel (ftaylorSeries ℝ f x) p σ (s + d) := by
  have hL1 := one_le_finMax (L := L) (p := p)
  have hL := zero_le_one.trans hL1
  have hK : 0 < 3 * finMax 1 L p + σ := by linarith
  have hδα : 4 * (3 * finMax 1 L p + σ) * δ ≤ α := by
    have := hδ.2.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have := sub_regularizedModel_ge_of_taylorDecrement_ge hL
    (fun i hi => hf.norm_iteratedFDeriv_le_finMax hi x) hσ hj hs hδ.1.le
    (hδ.2.trans (min_le_left _ _)) hδα hd hdec
  calc 1 / 2 * α * δ ^ j / j ! = α / 2 * δ ^ j / j ! := by ring
    _ ≤ _ := this

/-- **Lemma 12.2.9** of [cartis2022evaluation] (existence of a step). Let $E$ be a
finite-dimensional real inner product space, assume f.D1pL, and let $1 \le p$, $q \le p$,
$\varepsilon \in (0, 1]^q$ and $\sigma > 0$. At every iterate $x \in E$ there are a step $s$,
radii $\delta_{s,j}$ and displacements $d^m_j$ that satisfy the Step-2 conditions of ARqp for
the model with the weight $\sigma$ ((12.2.27), and either $\|s\| \ge 1$ or (12.2.29)), with
$$\delta_{s,j} = 1 \text{ for } j \in [1:\min(q, 2)] \quad \text{(12.2.44)}, \qquad \delta_{s,j}
  \ge \kappa_\delta(\sigma) \varepsilon_j \text{ for } j \in [3:q] \quad \text{(12.2.45)},$$
where $\kappa_\delta(\sigma) = \varsigma \theta/(8 (3 L_f + \sigma))$.

The step is a global minimizer of the model, which the source notes is always acceptable. The
proof does not use the termination of Algorithm 12.2.3; see
`CartisGouldToint.Chapter12.lemma_12_2_9_algorithm` for that route. The constant $\kappa_\delta$
is `Optimization.arqpKappaDelta`. -/
theorem lemma_12_2_9 [FiniteDimensional ℝ E] (hf : AssumptionD1pL f p L) (P : ARqpParams)
    (hp : 1 ≤ p) (hq : q ≤ p) {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) {σ : ℝ}
    (hσ : 0 < σ) (x : E) :
    ∃ (s : E) (δs : ℕ → ℝ) (dm : ℕ → E),
      ARqpStep univ P q ε (ARqpData.ofTaylor (ftaylorSeries ℝ f x) p σ) x s δs dm ∧
      (∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs j = 1) ∧
      ∀ j ∈ Finset.Icc 3 q, arqpKappaDelta P (finMax 1 L p) σ * ε j ≤ δs j := by
  have hL : 1 ≤ finMax 1 L p := one_le_finMax
  obtain ⟨s, δs, dm, hstep, h12, h3⟩ := exists_arqpStep_ofTaylor P hp hq
    (fun j hj => (hε j hj).1) (zero_le_one.trans hL)
    (fun i hi => hf.norm_iteratedFDeriv_le_finMax hi x) hσ x (D := ftaylorSeries ℝ f x)
  refine ⟨s, δs, dm, hstep, h12, fun j hj => ?_⟩
  have hj' : j ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hj).1; omega,
    (Finset.mem_Icc.1 hj).2⟩
  obtain ⟨hε0, hε1⟩ := hε j hj'
  rw [h3 j hj]
  have hK : 0 < 3 * finMax 1 L p + σ := by positivity
  have := P.ς_pos; have := P.θ_pos; have := P.ς_le_one; have := P.θ_lt_one
  refine le_min ?_ ?_
  · calc arqpKappaDelta P (finMax 1 L p) σ * ε j ≤ 1 * 1 :=
          mul_le_mul (arqpKappaDelta_lt_one P hL hσ.le).le hε1 hε0.le zero_le_one
      _ = 1 := one_mul 1
  · rw [arqpKappaDelta]
    calc P.ς * P.θ / (8 * (3 * finMax 1 L p + σ)) * ε j =
        P.ς * P.θ * ε j / (8 * (3 * finMax 1 L p + σ)) := by ring
      _ ≤ P.ς * P.θ * ε j / (4 * (3 * finMax 1 L p + σ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- **Lemmas 12.2.9 and 12.2.10** of [cartis2022evaluation], runs with the radii property (12.2.50).
Let $E$ be a finite-dimensional real inner product space, assume f.D1pL, and let
$1 \le q \le p$, $\varepsilon \in (0, 1]^q$ and $\delta_0 \in (0, 1]^q$. From every $x_0 \in E$
there is an ARqp run whose Step-2 radii satisfy $\delta_{s_k,j} = 1$ for $j \in [1:\min(q, 2)]$
at every iteration $k$ reached (12.2.44), and $\delta_{s_k,j} \ge \kappa_\delta(\sigma_k)
\varepsilon_j$ for all $j \in [1:q]$ at every iteration $k$ before termination ((12.2.45),
(12.2.50)).

In particular, the hypotheses of Theorem 12.2.14 can be met. The constant $\kappa_\delta$ is
`Optimization.arqpKappaDelta`. -/
theorem algorithm_12_2_2_exists_of_D1pL [FiniteDimensional ℝ E] (hf : AssumptionD1pL f p L)
    (P : ARqpParams) (hq : 1 ≤ q) (hqp : q ≤ p) {ε δ₀ : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (x₀ : E) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm ∧
      (∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs k j = 1) ∧
      ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ δs k j :=
  exists_isARqpRun_of_anchored (A := univ) (fun _ hj y _ => hf.norm_iteratedFDeriv_le_finMax hj y)
    P hq hqp hε hδ₀ x₀ fun y _ => mem_univ y

/-- **Lemma 12.2.9** of [cartis2022evaluation], algorithmic form (from the proof of the lemma). Let
$E$ be a finite-dimensional real inner product space, assume f.D1pL, and let $1 \le q \le p$,
$\varepsilon \in (0, 1]^q$, $\sigma > 0$ and $x \in E$. Consider Algorithm 12.2.3 for the model
$m(s) = T_{f,p}(x, s) + \sigma \|s\|^{p+1}/(p+1)!$ with the constants $\varsigma$ and $\theta$
of ARqp. Then:
* for every $\mu_0 \in (0, 1]$, there is no infinite sequence of transitions from the initial
  state with the parameter $\mu_0$ and all radii $1$;
* every state that is reachable from such an initial state and is not final has a successor;
* every output $(s, \delta_s)$ satisfies the Step-2 conditions of ARqp ((12.2.27)–(12.2.29)) for
  some displacements $d^m_j$, with $\delta_{s,j} = 1$ for $j \le 2$ (12.2.44) and $\delta_{s,j}
  \ge \kappa_\delta(\sigma) \varepsilon_j$ for $j \in [3:q]$ (12.2.45).

So every execution of Algorithm 12.2.3 terminates and returns an admissible step. The
transitions are `Optimization.ARqpDetailedTrans`, and the constant $\kappa_\delta$ is
`Optimization.arqpKappaDelta`. -/
theorem lemma_12_2_9_algorithm [FiniteDimensional ℝ E] (hf : AssumptionD1pL f p L)
    (P : ARqpParams) (hq : 1 ≤ q) (hqp : q ≤ p) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) {σ : ℝ} (hσ : 0 < σ) (x : E) :
    (∀ μ₀ ∈ Ioc (0 : ℝ) 1, ¬ ∃ c : ℕ → DetailedStepState E,
      c 0 = .findStep μ₀ (fun _ => 1) ∧
        ∀ n, ARqpDetailedTrans (ftaylorSeries ℝ f x) p σ q P.ς P.θ ε (c n) (c (n + 1))) ∧
    (∀ μ₀ ∈ Ioc (0 : ℝ) 1, ∀ b : DetailedStepState E,
      Relation.ReflTransGen (ARqpDetailedTrans (ftaylorSeries ℝ f x) p σ q P.ς P.θ ε)
        (.findStep μ₀ fun _ => 1) b → (∀ s δ, b ≠ .done s δ) →
      ∃ b', ARqpDetailedTrans (ftaylorSeries ℝ f x) p σ q P.ς P.θ ε b b') ∧
    ∀ s δs, algorithm_12_2_3 (regularizedModel (ftaylorSeries ℝ f x) p σ) q P.ς P.θ ε s δs →
      (∃ dm, ARqpStep univ P q ε (ARqpData.ofTaylor (ftaylorSeries ℝ f x) p σ) x s δs dm) ∧
      (∀ j ≤ 2, δs j = 1) ∧
      ∀ j ∈ Finset.Icc 3 q, arqpKappaDelta P (finMax 1 L p) σ * ε j ≤ δs j := by
  have hp : 1 ≤ p := hq.trans hqp
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  have hD : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ f x i‖ ≤ finMax 1 L p :=
    fun i hi => hf.norm_iteratedFDeriv_le_finMax hi x
  have hε0 : ∀ j ∈ Finset.Icc 1 q, 0 < ε j := fun j hj => (hε j hj).1
  refine ⟨fun μ₀ hμ₀ => arqpDetailedStep_terminates hσ (zero_le_one.trans hL1) hD hq hqp
    P.ς_pos P.θ_pos hε0 hμ₀, fun μ₀ hμ₀ b h hb =>
      arqpDetailedStep_exists_trans hσ hp P.ς_le_one hμ₀ h hb, fun s δs h => ?_⟩
  obtain ⟨h1, h2⟩ := h.exists_arqpStep P hp hσ x
  refine ⟨h1, h2, fun j hj => ?_⟩
  have hj' : j ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hj).1; omega,
    (Finset.mem_Icc.1 hj).2⟩
  obtain ⟨μ₀, hμ₀, hrun⟩ := h
  have hlow := arqpDetailedStep_radius_ge hσ (zero_le_one.trans hL1) hD hq hqp P.ς_pos P.θ_pos hε0
    hμ₀ hrun j hj'
  refine le_trans ?_ hlow
  obtain ⟨hεj, hεj1⟩ := hε j hj'
  refine le_min ?_ (le_of_eq ?_)
  · calc arqpKappaDelta P (finMax 1 L p) σ * ε j ≤ 1 * 1 :=
          mul_le_mul (arqpKappaDelta_lt_one P hL1 hσ.le).le hεj1 hεj.le zero_le_one
      _ = 1 := one_mul 1
  · rw [arqpKappaDelta]; ring

variable {P : ARqpParams} {ε δ₀ : ℕ → ℝ} {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ}
  {d dm : ℕ → ℕ → E} {X C A : Set E}

/-- **Lemma 12.2.11** of [cartis2022evaluation]. Assume f.D1pL and $1 \le q \le p$, and consider an
ARqp run. Let the iteration $k$ be successful and before termination, with a short step
$\|s_k\| < 1$, and let the Step-1 test fail at $k + 1$. Then for some $j \in [1:q]$
$$(\varsigma - \theta) \varepsilon_j \frac{\delta_{k+1,j}^j}{j!} < (L_{f,p} + \sigma_{\max})
  \sum_{\ell=1}^{j} \frac{\delta_{k+1,j}^\ell}{\ell!} \|s_k\|^{p-\ell+1} \quad
  \text{(12.2.52)},$$
where $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_{f,p}/(1 - \eta_2))$.

**Correction.** The source prints the factor $1 - \theta$ in place of $\varsigma - \theta$,
which is valid only for $\varsigma = 1$: a failed Step-1 test gives only
$\phi^\delta_{f,j}(x_{k+1}) > \varsigma \varepsilon_j \delta^j/j!$. The lemma also needs
(12.2.29) at the iteration $k$, which is the hypothesis $\|s_k\| < 1$.

The constant $\sigma_{\max}$ is `Optimization.arSigmaMax`. -/
theorem lemma_12_2_11 (hf : AssumptionD1pL f p L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hshort : ‖s k‖ < 1) (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, (P.ς - P.θ) * ε j * δ (k + 1) j ^ j / j ! <
      (L p + arSigmaMax P.toARParams (L p)) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hT := hf.toLipschitzDerivsAnchored_top hp univ
  have hσ := IsARqpRun.sigma_le_of_anchored hT subset_rfl
    (fun _ hy _ => hy) h k fun i hi => hk i hi.le
  have hstep := h.step (fun i hi => hk i hi.le) fun h1 => hk k le_rfl (Or.inl h1)
  rw [(h.succ_eq hk hs).2]
  exact ARqpStep.exists_radius_ineq hT (hf.one_le_top hp)
    subset_rfl hq hqp (mem_univ _)
    (P.σmin_nonneg.trans hσ.1) hσ.2 hstep hshort
    (h.next_witness hk hs) (h.next_not_measureTestPasses hk hs hk1)

/-- The common core of Lemmas 12.2.12 and 12.2.13 of [cartis2022evaluation]. Assume f.D1pL,
$1 \le q \le p$, $\theta < \varsigma$ and $\varepsilon \in (0, 1]^q$, and consider an ARqp run,
a successful iteration $k$ before termination after which the Step-1 test fails, and the radii
hypotheses of Lemma 12.2.12. Then some order $j \in [1:q]$ satisfies
$\tau_j \varepsilon_j/2 \le \|s_k\|^{p-j+1}$ if $q \le 2$, and $(\tau_j/2) \hat\kappa^{j-1}
\varepsilon_j^j \le \|s_k\|^p$ if $q > 2$. -/
theorem arqp_step_core (hf : AssumptionD1pL f p L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1))
    (hrad : (q ≤ 2 → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (2 < q → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    ∃ j ∈ Finset.Icc 1 q,
      (q ≤ 2 → arqpTau P L p j * ε j / 2 ≤ ‖s k‖ ^ (p - j + 1)) ∧
      (2 < q → arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1) * ε j ^ j ≤ ‖s k‖ ^ p) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hT := hf.toLipschitzDerivsAnchored_top hp univ
  have hσ := IsARqpRun.sigma_le_of_anchored hT subset_rfl
    (fun _ hy _ => hy) h k fun i hi => hk i hi.le
  have hstep := h.step (fun i hi => hk i hi.le) fun h1 => hk k le_rfl (Or.inl h1)
  rw [(h.succ_eq hk hs).2] at hrad
  obtain ⟨j, hj, h1, h2⟩ := ARqpStep.exists_norm_pow_ge hT
    (hf.one_le_top hp) subset_rfl hq
    hqp hθς hε (mem_univ _)
    (P.σmin_nonneg.trans hσ.1) hσ.2 hstep (h.model_lt hk)
    (h.next_witness hk hs) (h.next_not_measureTestPasses hk hs hk1) (u := q ≤ 2)
    ⟨hrad.1, fun h' => hrad.2 (not_le.1 h')⟩
  exact ⟨j, hj, h1, fun h' => h2 (not_le.2 h')⟩

/-- **Lemma 12.2.12** of [cartis2022evaluation]. Assume f.D1pL, $1 \le q \le p$,
$\theta < \varsigma$ and $\varepsilon \in (0, 1]^q$, and consider an ARqp run. Let the iteration
$k$ be successful and before termination, and let the Step-1 test fail at $k + 1$. Then:
* if $q \le 2$ and $\delta_{k+1,j} = 1$ for $j \in [1:q]$, then some $j \in [1:q]$ has $\|s_k\|
  \ge (\tau_j \varepsilon_j/2)^{1/(p-j+1)}$;
* if $q > 2$, and either $\|s_k\| \ge 1$ or $\delta_{k+1,j} \ge \kappa_{\delta,\min}
  \varepsilon_j$ for all $j \in [1:q]$ (12.2.51), then some $j \in [1:q]$ has
$$\|s_k\| \ge \Big(\frac{\tau_j}{2} \hat\kappa^{j-1}\Big)^{1/p} \varepsilon_j^{j/p} \quad
  \text{(12.2.57)}.$$

Here $\tau_j = (\varsigma - \theta)/(j!\, (L_{f,p} + \sigma_{\max}))$, $\kappa_{\delta,\min} =
\kappa_\delta(\sigma_{\max})$ and $\hat\kappa = \min(\kappa_{\delta,\min}, \tau_q/2)$.

**Correction.** The source uses the constant $\kappa_{\delta,\min}$ in place of $\hat\kappa$.
This relies on "the first case implies the second", which needs
$\kappa_{\delta,\min} \le \tau_q/2$ and fails for $\theta$ close to $\varsigma$. The printed
hypothesis $\delta_{k+1,j} = 1$ for $j \le 2$ is not needed when $q > 2$.

The constants are `Optimization.arqpTau`, `Optimization.arqpKappaDelta` and
`Optimization.arqpKappaHat`. -/
theorem lemma_12_2_12 (hf : AssumptionD1pL f p L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1)) :
    (q ≤ 2 → (∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) →
      ∃ j ∈ Finset.Icc 1 q,
        (arqpTau P L p j * ε j / 2) ^ (1 / ((p - j + 1 : ℕ) : ℝ)) ≤ ‖s k‖) ∧
    (2 < q → (1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j) →
      ∃ j ∈ Finset.Icc 1 q,
        (arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1)) ^ (1 / (p : ℝ)) *
          ε j ^ ((j : ℝ) / p) ≤ ‖s k‖) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hLp : 1 ≤ L p := hf.one_le p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)
  have hκ := (arqpKappaHat_pos P L hθς hLp q).le
  refine ⟨fun hq2 hrad => ?_, fun hq2 hrad => ?_⟩
  · obtain ⟨j, hj, h1, -⟩ := arqp_step_core hf hq hqp hθς hε h hk hs hk1
      ⟨fun _ => hrad, fun h' => absurd h' (by omega)⟩
    obtain ⟨hε0, -⟩ := hε j hj
    have hτ := arqpTau_pos P L hθς (zero_le_one.trans hLp) j
    exact ⟨j, hj, rpow_one_div_le_of_le_pow (by omega) (by positivity) (norm_nonneg _)
      (h1 hq2)⟩
  · obtain ⟨j, hj, -, h2⟩ := arqp_step_core hf hq hqp hθς hε h hk hs hk1
      ⟨fun h' => absurd h' (by omega), fun _ => hrad⟩
    obtain ⟨hε0, -⟩ := hε j hj
    have hτ := arqpTau_pos P L hθς (zero_le_one.trans hLp) j
    refine ⟨j, hj, ?_⟩
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    calc (arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1)) ^ (1 / (p : ℝ)) *
          ε j ^ ((j : ℝ) / p)
        = (arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1) * ε j ^ j) ^
            (1 / (p : ℝ)) := by
          rw [Real.mul_rpow (x := arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1))
            (y := ε j ^ j) (by positivity) (by positivity), ← Real.rpow_natCast (ε j) j,
            ← Real.rpow_mul hε0.le]
          congr 2
          ring
      _ ≤ ‖s k‖ := rpow_one_div_le_of_le_pow (by omega) (by positivity) (norm_nonneg _) (h2 hq2)

/-- **Lemma 12.2.13** of [cartis2022evaluation], the exponents $\pi_j$: $\pi_j = (p+1)/(p-j+1)$ if
$q \in \{1, 2\}$, and $\pi_j = j(p+1)/p$ if $q > 2$.

This is the radii mode $u = (q \le 2)$ of `Optimization.arqpPiOf`. The value for $q = 0$ is that
of $q \le 2$. -/
noncomputable def arqpPi (p q j : ℕ) : ℝ := arqpPiOf (q ≤ 2) p j

/-- **Lemma 12.2.13** of [cartis2022evaluation], the constant $\kappa_{\Delta m}$:
$$\kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!} \Big(\frac{\tau_q}{2}\Big)^{(p+1)/(p-q+1)}
  \text{ if } q \in \{1, 2\}, \qquad \kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!}
  \Big(\frac{\tau_q}{2} \hat\kappa^{q-1}\Big)^{q(p+1)/p} \text{ if } q > 2,$$
with $\tau_q = (\varsigma - \theta)/(q!\, (L_{f,p} + \sigma_{\max}))$ and the corrected constant
$\hat\kappa = \min(\kappa_{\delta,\min}, \tau_q/2)$.

This is the radii mode $u = (q \le 2)$ of `Optimization.arqpKappaDmOf`. -/
noncomputable def arqpKappaDm (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  arqpKappaDmOf (q ≤ 2) P L p q

/-- For $q \le 2$, $\kappa_{\Delta m} = \sigma_{\min}/(p+1)!\, (\tau_q/2)^{(p+1)/(p-q+1)}$. -/
theorem arqpKappaDm_of_le_two {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (hq : q ≤ 2) :
    arqpKappaDm P L p q = P.σmin / ((p + 1)! : ℝ) *
      (arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)) :=
  arqpKappaDmOf_of_pos hq P L p q

/-- For $q > 2$, $\kappa_{\Delta m} = \sigma_{\min}/(p+1)!\, ((\tau_q/2)
\hat\kappa^{q-1})^{q(p+1)/p}$. -/
theorem arqpKappaDm_of_two_lt {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (hq : 2 < q) :
    arqpKappaDm P L p q = P.σmin / ((p + 1)! : ℝ) *
      (arqpTau P L p q / 2 * arqpKappaHat P L p q ^ (q - 1)) ^ ((q : ℝ) * (p + 1) / p) :=
  arqpKappaDmOf_of_neg (by omega) P L p q

/-- For $q \le 2$, $\pi_j = (p+1)/(p-j+1)$. -/
theorem arqpPi_of_le_two {p q j : ℕ} (hq : q ≤ 2) :
    arqpPi p q j = ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ) :=
  arqpPiOf_of_pos hq p j

/-- For $q > 2$, $\pi_j = j(p+1)/p$. -/
theorem arqpPi_of_two_lt {p q j : ℕ} (hq : 2 < q) : arqpPi p q j = (j : ℝ) * (p + 1) / p :=
  arqpPiOf_of_neg (by omega) p j

/-- If $\theta < \varsigma$ and $L_{f,p} \ge 1$, then $\kappa_{\Delta m} \ge 0$. -/
theorem arqpKappaDm_nonneg {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (hθς : P.θ < P.ς)
    (hL : 1 ≤ L p) : 0 ≤ arqpKappaDm P L p q :=
  arqpKappaDmOf_nonneg _ hθς hL

/-- **Lemma 12.2.13** of [cartis2022evaluation]. Assume f.D1pL, $1 \le q \le p$,
$\theta < \varsigma$ and $\varepsilon \in (0, 1]^q$, and consider an ARqp run. Let the iteration
$k$ be successful and before termination, let the Step-1 test fail at $k + 1$, and assume the
radii hypotheses of Lemma 12.2.12: if $q \le 2$, then $\delta_{k+1,j} = 1$ for $j \in [1:q]$; if
$q > 2$, then $\|s_k\| \ge 1$ or $\delta_{k+1,j} \ge \kappa_{\delta,\min} \varepsilon_j$ for all
$j \in [1:q]$. Then
$$\Delta T_{f,p}(x_k, s_k) \ge \kappa_{\Delta m} \min_{j \in [1:q]} \varepsilon_j^{\pi_j} \quad
  \text{(12.2.61)} \qquad \text{and} \qquad f(x_k) - f(x_{k+1}) \ge \eta_1 \kappa_{\Delta m}
  \min_{j \in [1:q]} \varepsilon_j^{\pi_j} \quad \text{(12.2.62)}.$$

**Correction.** The source assumes only f.D1qL and states the bounds at every iteration before
termination. The proof needs f.D1pL and an iteration $k + 1$ at which the Step-1 test fails. In
(12.2.56) of the proof, the printed $(p-j+1)!$ and $\|s_k\|^{p-j+1}$ are typos for $(p-\ell+1)!$
and $\|s_k\|^{p-\ell+1}$.

The constants are `CartisGouldToint.Chapter12.arqpKappaDm` and
`CartisGouldToint.Chapter12.arqpPi`. The minimum is `Optimization.finMin 1 _ q`, that is,
$\min(1, \min_j \varepsilon_j^{\pi_j})$. -/
theorem lemma_12_2_13 (hf : AssumptionD1pL f p L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1))
    (hrad : (q ≤ 2 → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (2 < q → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    arqpKappaDm P L p q * finMin 1 (fun j => ε j ^ arqpPi p q j) q ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      P.η₁ * (arqpKappaDm P L p q * finMin 1 (fun j => ε j ^ arqpPi p q j) q) ≤
        f (x k) - f (x (k + 1)) :=
  have hT := hf.toLipschitzDerivsAnchored_top (hq.trans hqp) univ
  IsARqpRun.decrease hT (hf.one_le_top (hq.trans hqp)) subset_rfl
    (fun _ hy _ => hy) hq hqp hθς hε h hk hs
    hk1 (u := q ≤ 2)
    ⟨hrad.1, fun h' => hrad.2 (not_le.1 h')⟩

/-- **Theorem 12.2.14** of [cartis2022evaluation], the constant
$\kappa^s = 1/(\eta_1 \kappa_{\Delta m})$. For $q \in \{1, 2\}$ it is
$$\kappa^{s,1} = \frac{(p+1)!}{\eta_1 \sigma_{\min}} \Big(\frac{2\, q!\, (L_{f,p} +
  \sigma_{\max})}{\varsigma - \theta}\Big)^{(p+1)/(p-q+1)},$$
and for $q > 2$ it is
$$\kappa^{s,2} = \frac{(p+1)!}{\eta_1 \sigma_{\min}} \Big(\frac{2\, q!\, (L_{f,p} +
  \sigma_{\max})}{(\varsigma - \theta) \hat\kappa^{q-1}}\Big)^{q(p+1)/p},$$
with the corrected constant $\hat\kappa$.

This is the radii mode $u = (q \le 2)$ of `Optimization.kappaSARqpOf`. -/
noncomputable def kappaSARqp (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  kappaSARqpOf (q ≤ 2) P L p q

/-- The constant $\kappa^a = \kappa^s (1 + |\log \gamma_1|/\log \gamma_2)$ of Theorem 12.2.14 of
[cartis2022evaluation]. It is the radii mode $u = (q \le 2)$ of `Optimization.kappaAARqpOf`. -/
noncomputable def kappaAARqp (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  kappaAARqpOf (q ≤ 2) P L p q

/-- If $\sigma_{\min} > 0$, $\theta < \varsigma$ and $L_{f,p} \ge 1$, then $\kappa_{\Delta m} > 0$.
-/
theorem arqpKappaDm_pos {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) (hL : 1 ≤ L p) : 0 < arqpKappaDm P L p q :=
  arqpKappaDmOf_pos _ hσmin hθς hL

/-- If $\sigma_{\min} > 0$, $\theta < \varsigma$ and $L_{f,p} \ge 1$, then $\kappa^s > 0$. -/
theorem kappaSARqp_pos {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) (hL : 1 ≤ L p) : 0 < kappaSARqp P L p q :=
  kappaSARqpOf_pos _ hσmin hθς hL

/-- **Lemma 12.2.10** of [cartis2022evaluation], certification at a model minimizer $0$. Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D1pL, and let $q \le p$, $\varepsilon \in (0, 1]^q$,
$\sigma > 0$ and $y \in \mathbb{R}^n$. If $0$ is a global minimizer of the model $m(s) =
T_{f,p}(y, s) + \sigma \|s\|^{p+1}/(p+1)!$, then $y$ is an $(\varepsilon, \delta)$-approximate
$q$-th order minimizer of $f$ for the radii
$$\delta_j = \min\Big(1, \frac{\varepsilon_j}{4 (3 L_f + \sigma)}\Big),$$
where $L_f = \max(1, \max_{j \in [1:p]} L_{f,j})$.

This is the content of Lemma 12.2.10. -/
theorem isEpsDeltaApproxMinimizer_of_isMinOn_zero {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {y : EuclideanSpace ℝ (Fin n)} {σk : ℝ} (hf : AssumptionD1pL f p L) (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hσ : 0 < σk)
    (hmin : IsMinOn (regularizedModel (ftaylorSeries ℝ f y) p σk) univ 0) :
    IsEpsDeltaApproxMinimizer f q ε (fun j => min 1 (ε j / (4 * (3 * finMax 1 L p + σk)))) y := by
  have hU : {e : EuclideanSpace ℝ (Fin n) | y + e ∈ (univ : Set _)} = univ := by ext; simp
  obtain ⟨h1, h2⟩ := isEpsDeltaApprox_of_isMinOn_zero_of_jet (mem_univ y) hf.contDiff.contDiffAt
    (fun _ hi => hf.norm_iteratedFDeriv_le_finMax hi y) hqp hε hσ (hU ▸ hmin)
  rw [hU] at h2
  exact ⟨fun j hj => ⟨hε j hj, h1 j hj⟩, h2⟩

/-- **Lemma 12.2.10** of [cartis2022evaluation], no termination in Step 2 for $q \le 2$. Let
$f : \mathbb{R}^n \to \mathbb{R}$ and consider an ARqp run with $q \le 2$, $q \le p$,
$\varepsilon \in (0, 1]^q$ and $\delta_0 \in (0, 1]^q$. Let $k$ be the termination index, and
let $f$ be $C^p$ near $x_k$. Then the Step-1 test passes at $k$, that is, the run does not
terminate in Step 2.

If the Step-1 test failed at $k$, then $0$ would minimize the model, so the model measures of
the orders $j \le 2$ would vanish at $0$, which contradicts the failed test. Only the smoothness
of $f$ at $x_k$ is used, as under the anchored assumptions. -/
theorem lemma_12_2_10_le_two {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (hfk : ContDiffAt ℝ p f (x k)) (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm)
    (hk : IsFirstHit (arqpStop f P p q ε x s σ δ d) k)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k) (hq2 : q ≤ 2) : False :=
  h1 (IsARqpRun.arqpStop₁_of_isFirstHit_of_le_two h hfk hqp hε hδ₀ hk hq2)

/-- **Lemma 12.2.10** of [cartis2022evaluation] (termination in Step 2). Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.D1pL, let $q \le p$, $\varepsilon \in (0, 1]^q$ and
$\delta_0 \in (0, 1]^q$, and consider an ARqp run. Let $k$ be the termination index, and let the
Step-1 test fail at $k$, so that the run terminates in Step 2. Then $q \ge 3$, and $x_k$ is an
$(\varepsilon, \delta)$-approximate $q$-th order minimizer of $f$ for the radii
$$\delta_j = \min\Big(1, \frac{\varepsilon_j}{4 (3 L_f + \sigma_k)}\Big).$$

The algorithm stops in Step 2 only when $0$ globally minimizes $m_k$. The printed proof applies
(12.2.29) to the step $s_k = 0$, which need not be the returned step (Example 12.2.2 allows
$s_k = \frac12$). The statement is proved from the global minimality of $0$, with explicit
radii, by `CartisGouldToint.Chapter12.isEpsDeltaApproxMinimizer_of_isMinOn_zero`. -/
theorem lemma_12_2_10 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin n)}
    (hf : AssumptionD1pL f p L) (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : IsFirstHit (arqpStop f P p q ε x s σ δ d) k)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k) :
    (q ≤ 2 → False) ∧
      IsEpsDeltaApproxMinimizer f q ε (fun j => min 1 (ε j / (4 * (3 * finMax 1 L p + σ k))))
        (x k) := by
  have hσ : 0 < σ k := h.toIsARRun.sigma_pos hk.2 k le_rfl
  have hstep := h.step hk.2 h1
  have h2 : arqpStop₂ (arqpData f p x σ) s k := hk.1.resolve_left h1
  have hU : ∀ y : EuclideanSpace ℝ (Fin n),
      {e : EuclideanSpace ℝ (Fin n) | y + e ∈ (univ : Set _)} = univ := fun y => by ext; simp
  have hmin := hstep.isMinOn_of_eq h2
  rw [hU] at hmin
  exact ⟨lemma_12_2_10_le_two hf.contDiff.contDiffAt hqp hε hδ₀ h hk h1,
    isEpsDeltaApproxMinimizer_of_isMinOn_zero hf hqp hε hσ hmin⟩

section ARqpComplexity

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {flow : ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin n)}

/-- **Theorem 12.2.14 (1)** of [cartis2022evaluation] (complexity of ARqp for $q \in \{1, 2\}$). Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.Bb with the lower bound $f_{\mathrm{low}}$ and
f.D1pL. Let $1 \le q \le 2$, $q \le p$, $\varepsilon \in (0, 1]^q$, $\sigma_{\min} > 0$ and
$\theta < \varsigma$. Consider an ARqp run with $\delta_{0,j} = 1$ whose steps have the radii
$\delta_{s_k,j} = 1$ for $j \in [1:q]$ at every iteration $k$ before termination, as Lemma
12.2.9 allows. Then the run terminates at some iteration $k_\varepsilon$, in Step 1 (Lemma
12.2.10), with $\phi^1_{f,j}(x_{k_\varepsilon}) \le \varepsilon_j/j!$ for $j \in [1:q]$, after
at most
$$\kappa^{a,1} \frac{f(x_0) - f_{\mathrm{low}}}{\min_j \varepsilon_j^{(p+1)/(p-j+1)}} + \kappa^c
  \quad \text{(12.2.63)}$$
evaluations of $f$ and at most $\kappa^{s,1} (f(x_0) - f_{\mathrm{low}})/\min_j
\varepsilon_j^{(p+1)/(p-j+1)} + 2$ evaluations of the derivatives (12.2.64).

**Correction.** The hypothesis $\theta < \varsigma$ is needed by Lemma 12.2.11, and the
constants have $\varsigma - \theta$ in place of the printed $1 - \theta$.

**Reading.** The hypothesis $\sigma_{\min} > 0$ comes from Step 0 of the source;
`Optimization.ARqpParams` asks only $\sigma_{\min} \ge 0$. The radii equal to $1$ ("the
algorithm ensures $\delta_{k+1,j} = 1$") are a hypothesis on $\delta_0$ and on every returned
step.

The constants are `CartisGouldToint.Chapter12.kappaAARqp`, `Optimization.kappaCARqp` and
`CartisGouldToint.Chapter12.kappaSARqp`. -/
theorem theorem_12_2_14_i (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionD1pL f p L)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, δ₀ j = 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm)
    (hδs : ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) →
      ∀ j ∈ Finset.Icc 1 q, δs k j = 1) :
    ∃ kε, IsFirstHit (arqpStop f P p q ε x s σ δ d) kε ∧
      arqpStop₁ P q ε (arqpData f p x σ) δ d kε ∧
      (∀ j ∈ Finset.Icc 1 q, phiMeasure f j 1 (x kε) ≤ ε j / j !) ∧
      (funEvalCount kε : ℝ) ≤ kappaAARqp P L p q * (f (x 0) - flow) /
        finMin 1 (fun j => ε j ^ arqpPi p q j) q + kappaCARqp P L p ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε : ℝ) ≤
        kappaSARqp P L p q * (f (x 0) - flow) / finMin 1 (fun j => ε j ^ arqpPi p q j) q + 2 := by
  have hone := h.delta_eq_one hδ₀ hδs
  have hT := hf.toLipschitzDerivsAnchored_top (hq.trans hqp) univ
  obtain ⟨kε, hk, hF, hD⟩ := IsARqpRun.exists_isFirstHit_of_anchored
    (fun y _ => hb y) hT (hf.one_le_top (hq.trans hqp))
    subset_rfl (fun _ hy _ => hy) hq hqp hσmin hθς hε h (u := q ≤ 2)
    fun k hk _ => ⟨fun _ => hone (k + 1) fun i hi => hk i hi.le,
      fun h' => absurd h' (by omega)⟩
  have hδ₀' : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1 := fun j hj => by
    rw [hδ₀ j hj]; norm_num
  have h1 : arqpStop₁ P q ε (arqpData f p x σ) δ d kε := by
    by_contra h1
    exact (lemma_12_2_10 hf hqp hε hδ₀' h hk h1).1 hq2
  refine ⟨kε, hk, h1, fun j hj => ?_, hF, hD⟩
  have hU : {e : EuclideanSpace ℝ (Fin n) | x kε + e ∈ (univ : Set _)} = univ := by ext; simp
  have hw := h.witness kε hk.2
  rw [hU] at hw
  have := isEpsDeltaApprox_of_measureTestPasses P.ς_pos hw h1 j hj
  rw [hone kε hk.2 j hj, one_pow, mul_one] at this
  exact this

/-- **Theorem 12.2.14 (2)** of [cartis2022evaluation] (complexity of ARqp for $q > 2$). Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.Bb with the lower bound $f_{\mathrm{low}}$ and
f.D1pL. Let $3 \le q \le p$, $\varepsilon \in (0, 1]^q$, $\delta_0 \in (0, 1]^q$,
$\sigma_{\min} > 0$ and $\theta < \varsigma$. Consider an ARqp run with the radii property
(12.2.50): at every iteration $k$ before termination with a short step $\|s_k\| < 1$, the radii
satisfy $\delta_{s_k,j} \ge \kappa_\delta(\sigma_k) \varepsilon_j$ for $j \in [1:q]$, as Lemma
12.2.9 allows. Then the run terminates at some iteration $k_\varepsilon$ where
$x_{k_\varepsilon}$ is an $(\varepsilon, \delta_\varepsilon)$-approximate $q$-th order minimizer
for some $\delta_\varepsilon \in (0, 1]^q$ (by Lemma 12.2.10 for a termination in Step 2), after
at most
$$\kappa^{a,2} \frac{f(x_0) - f_{\mathrm{low}}}{\min_j \varepsilon_j^{j(p+1)/p}} + \kappa^c
  \quad \text{(12.2.65)}$$
evaluations of $f$ and at most $\kappa^{s,2} (f(x_0) - f_{\mathrm{low}})/\min_j
\varepsilon_j^{j(p+1)/p} + 2$ evaluations of the derivatives (12.2.66).

**Correction.** The hypothesis $\theta < \varsigma$ is needed by Lemma 12.2.11. The constants
have $\varsigma - \theta$ in place of $1 - \theta$, and the corrected $\hat\kappa =
\min(\kappa_{\delta,\min}, \tau_q/2)$ of Lemma 12.2.12 in place of $\kappa_{\delta,\min}$.

**Reading.** The hypothesis $\sigma_{\min} > 0$ comes from Step 0 of the source. The radii
property (12.2.50) is a hypothesis on the run, which the runs of
`CartisGouldToint.Chapter12.algorithm_12_2_2_exists_of_D1pL` satisfy.

The constant $\kappa_\delta$ is `Optimization.arqpKappaDelta`, and the other constants are
`CartisGouldToint.Chapter12.kappaAARqp`, `Optimization.kappaCARqp` and
`CartisGouldToint.Chapter12.kappaSARqp`. -/
theorem theorem_12_2_14_ii (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionD1pL f p L)
    (hq : 2 < q) (hqp : q ≤ p) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm)
    (hrad : ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) → ‖s k‖ < 1 →
      ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ δs k j) :
    ∃ kε, IsFirstHit (arqpStop f P p q ε x s σ δ d) kε ∧
      (∃ δε : ℕ → ℝ, IsEpsDeltaApproxMinimizer f q ε δε (x kε)) ∧
      (funEvalCount kε : ℝ) ≤ kappaAARqp P L p q * (f (x 0) - flow) /
        finMin 1 (fun j => ε j ^ arqpPi p q j) q + kappaCARqp P L p ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε : ℝ) ≤
        kappaSARqp P L p q * (f (x 0) - flow) / finMin 1 (fun j => ε j ^ arqpPi p q j) q + 2 := by
  have hq1 : 1 ≤ q := by omega
  have hp : 1 ≤ p := hq1.trans hqp
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  have hT := hf.toLipschitzDerivsAnchored_top hp univ
  obtain ⟨kε, hk, hF, hD⟩ := IsARqpRun.exists_isFirstHit_of_anchored
    (fun y _ => hb y) hT (hf.one_le_top hp)
    subset_rfl (fun _ hy _ => hy) hq1 hqp hσmin hθς hε h (u := q ≤ 2) fun k hk hs => by
    refine ⟨fun h' => absurd h' (by omega), fun _ => ?_⟩
    by_cases hlong : 1 ≤ ‖s k‖
    · exact Or.inl hlong
    refine Or.inr fun j hj => ?_
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (by omega)
    rw [(h.succ_eq hk' hs).2]
    have hσ := IsARqpRun.sigma_le_of_anchored hT subset_rfl
      (fun _ hy _ => hy) h k fun i hi => hk' i hi.le
    have hσ0 : 0 ≤ σ k := P.σmin_nonneg.trans hσ.1
    refine le_trans ?_ (hrad k hk' (not_le.1 hlong) j hj)
    exact mul_le_mul_of_nonneg_right (arqpKappaDelta_anti P hL1 hσ0 hσ.2) (hε j hj).1.le
  refine ⟨kε, hk, ?_, hF, hD⟩
  by_cases h1 : arqpStop₁ P q ε (arqpData f p x σ) δ d kε
  · refine ⟨δ kε, fun j hj => ⟨hε j hj, h.delta_mem hδ₀ kε hk.2 j hj⟩, ?_⟩
    have hU : {e : EuclideanSpace ℝ (Fin n) | x kε + e ∈ (univ : Set _)} = univ := by ext; simp
    have hw := h.witness kε hk.2
    rw [hU] at hw
    exact MeasureTestPasses.isEpsDeltaApprox P.ς_pos hw h1
  · exact ⟨_, (lemma_12_2_10 hf hqp hε hδ₀ h hk h1).2⟩

end ARqpComplexity

end ARqp

/-! ### Sharpness for ARqp (Section 12.2.2.4) -/

section ARqpSharp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The termination test of a global-step ARqp run, with all Step-1 radii equal to $1$: the Step-1
test with radii $1$ passes, or $m_k(s_k) = m_k(0)$. -/
abbrev arqpGlobalStop (f : E → ℝ) (P : ARqpParams) (p q : ℕ) (ε : ℕ → ℝ) (x s : ℕ → E)
    (σ : ℕ → ℝ) (d : ℕ → ℕ → E) (k : ℕ) : Prop :=
  IsARRun.Stop (arqpStop₁ P q ε (arqpData f p x σ) (fun _ _ => 1) d)
    (arqpStop₂ (arqpData f p x σ) s) k

/-- **Theorem 12.2.15** of [cartis2022evaluation], the scenario of the theorem ("the choice
$\delta_{s_k,j} = 1$ is possible and made", with steps that globally minimize the model). A
**global-step ARqp run** is an ARqp run with all radii equal to $1$ ($\delta_0 = 1$ and
$\delta_{s_k} = 1$) whose Step 2 returns a global minimizer $s_k$ of the model $m_k$, without
the requirement (12.2.29). That is: Steps 2–4 form an adaptive-regularization run whose steps
are global model minimizers; at every iteration reached, the Step-1 displacements are
approximate optimality displacements of radius $1$; and unsuccessful iterations keep the Step-1
displacements.

For $q \le 2$ every such run is an ARqp run, by
`CartisGouldToint.Chapter12.IsARqpGlobalStepRun.toAlgorithm`. For $q \ge 3$ the condition
(12.2.29) may fail with radius $1$, by
`CartisGouldToint.Chapter12.theorem_12_2_15_counterexample`. -/
structure IsARqpGlobalStepRun (f : E → ℝ) (P : ARqpParams) (p q : ℕ) (ε : ℕ → ℝ)
    (x s : ℕ → E) (σ : ℕ → ℝ) (d : ℕ → ℕ → E) : Prop where
  /-- Steps 2–4 form an adaptive-regularization run whose steps are global minimizers of the model,
  with the Step-1 test with radii $1$ and the Step-2 termination test $m_k(s_k) = m_k(0)$. -/
  toIsARRun : IsARRun P.toARParams (arqpStop₁ P q ε (arqpData f p x σ) (fun _ _ => 1) d)
    (fun k => IsMinOn (arqpModel f p x σ k) univ (s k)) (arqpStop₂ (arqpData f p x σ) s)
    (arqpRho f p x s σ) x s σ
  /-- Step 1: at every iteration $k$ reached, $d_{k,j}$ is a $\varsigma$-approximate optimality
  displacement of radius $1$ for $\Delta T_{f,j}(x_k, \cdot)$, for $j \in [1:q]$. -/
  witness : ∀ k, (∀ i < k, ¬ arqpGlobalStop f P p q ε x s σ d i) → ∀ j ∈ Finset.Icc 1 q,
    IsApproxMeasureStep ((ftaylorSeries ℝ f (x k)).taylorDecrement j) 1 univ P.ς (d k j)
  /-- Before termination, an unsuccessful iteration keeps the Step-1 displacements. -/
  keep : UntilHit (arqpGlobalStop f P p q ε x s σ d) fun k =>
    ¬ P.η₁ ≤ arqpRho f p x s σ k → d (k + 1) = d k

/-- **Corollary 12.2.16** of [cartis2022evaluation], global-step runs are ARqp runs for $q \le 2$
(from the proof of the corollary, with Theorem 12.1.4). Let $q \le 2$, $q \le p$ and
$\varepsilon_j \ge 0$ for $j \in [1:q]$. Every global-step ARqp run is an ARqp run
(`CartisGouldToint.Chapter12.algorithm_12_2_2`) with $\delta_0 = 1$, all Step-1 and Step-2 radii
equal to $1$, and the Step-2 displacements $d^m_{k,j} = 0$.

A global minimizer of the model satisfies (12.2.29) with radii $1$ at the orders $j \le 2$, with
$d^m_j = 0$. -/
theorem IsARqpGlobalStepRun.toAlgorithm {f : E → ℝ} {P : ARqpParams} {p q : ℕ} {ε : ℕ → ℝ}
    {x s : ℕ → E} {σ : ℕ → ℝ} {d : ℕ → ℕ → E} (h : IsARqpGlobalStepRun f P p q ε x s σ d)
    (hq2 : q ≤ 2) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) :
    algorithm_12_2_2 f P p q ε (fun _ => 1) x s σ (fun _ _ => 1) (fun _ _ => 1) d
      (fun _ _ => 0) := by
  have hU : ∀ y : E, {e : E | y + e ∈ (univ : Set E)} = univ := fun y => by ext; simp
  refine ⟨h.toIsARRun.mono fun k hmin => ?_, mem_univ _, rfl, fun k hk j hj => ?_,
    fun k hk => ⟨fun _ => rfl, fun hρ => ⟨rfl, h.keep k hk hρ⟩⟩⟩
  · refine ⟨mem_univ _, hmin (mem_univ 0), fun heq => ?_, fun _ _ => one_pos, fun _ _ => le_rfl,
      Or.inr fun j hj => ?_⟩
    · rw [hU]
      intro e _
      change regularizedModel _ p (σ k) 0 ≤ regularizedModel _ p (σ k) e
      change regularizedModel _ p (σ k) (s k) = regularizedModel _ p (σ k) 0 at heq
      rw [← heq]
      exact hmin (mem_univ e)
    · rw [hU]
      have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
      have hcd : ContDiffAt ℝ j (arqpModel f p x σ k) (s k) :=
        (contDiff_regularizedModel (D := ftaylorSeries ℝ f (x k))).contDiffAt.of_le
          (by exact_mod_cast hjp)
      have hφ := taylorMeasure_eq_zero_of_isLocalMin hcd (hmin.isLocalMin univ_mem)
        (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2.trans hq2⟩)
        zero_le_one
      refine ⟨⟨⟨by simp, mem_univ _⟩, ?_⟩, ?_⟩
      · change P.ς * taylorMeasure (ftaylorSeries ℝ (arqpModel f p x σ k) (s k)) j 1 univ ≤
          (ftaylorSeries ℝ (arqpModel f p x σ k) (s k)).taylorDecrement j 0
        rw [hφ, mul_zero, FormalMultilinearSeries.taylorDecrement_zero_right]
      · change (ftaylorSeries ℝ (arqpModel f p x σ k) (s k)).taylorDecrement j 0 ≤ _
        rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.ς_pos; have := P.θ_pos; have := hε j hj
        positivity
  · rw [hU]
    exact h.witness k hk j hj

/-- **Theorem 12.2.15** of [cartis2022evaluation] (slow convergence of ARqp, good case). Let
$1 \le q \le p$. There are $f_{\mathrm{low}}$ and $L \ge 1$, which depend only on $p$ and $q$,
with the following property. For every $\varepsilon \in (0, 1]$ and all ARqp constants with
$\sigma_0 = p!/(q-1)!$, there is $f : \mathbb{R} \to \mathbb{R}$ with $f \ge f_{\mathrm{low}}$
that satisfies f.D1pL with all constants $L_{f,j} = L$, and a global-step ARqp run for the
tolerances $\varepsilon_j = \varepsilon$, with steps the global model minimizers (12.2.70), such
that:
* $x_0 = 0$ and $\sigma_k = \sigma_0$ for all $k$;
* $\rho_k = 1$ for all $k < k_\varepsilon$, where $k_\varepsilon = \lceil
  \varepsilon^{-(p+1)/(p-q+1)} \rceil$;
* the run terminates at $k_\varepsilon$, with $\phi^1_{f,j}(x_{k_\varepsilon}) \le
  \varepsilon/j!$ for $j \in [1:q]$;
* $\phi^1_{f,q}(x_k) > \varepsilon/q!$ for all $k < k_\varepsilon$.

So ARqp can need $\varepsilon^{-(p+1)/(p-q+1)}$ iterations and evaluations.

**Correction.** The source assumes that "the choice $\delta_{s_k,j} = 1$ is possible". For
$q \ge 3$ this fails for the example of the proof, for instance for $p = q = 3$
(`CartisGouldToint.Chapter12.theorem_12_2_15_counterexample`). The theorem is therefore stated
for the global-step scenario `CartisGouldToint.Chapter12.IsARqpGlobalStepRun`, whose Step 2 does
not require (12.2.29). This scenario is an ARqp run
(`CartisGouldToint.Chapter12.algorithm_12_2_2`) only for $q \le 2$
(`CartisGouldToint.Chapter12.corollary_12_2_16`).

**Generalization.** The source takes $\varepsilon \le \frac12$; the statement holds for every
$\varepsilon \in (0, 1]$. -/
theorem theorem_12_2_15 {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ P : ARqpParams,
      P.σ₀ = (p ! : ℝ) / (q - 1)! →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          IsARqpGlobalStepRun f P p q (fun _ => ε) x s σ d ∧ x 0 = 0 ∧ (∀ k, σ k = P.σ₀) ∧
          (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, arqpRho f p x s σ k = 1) ∧
          IsFirstHit (arqpGlobalStop f P p q (fun _ => ε) x s σ d)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          (∀ j ∈ Finset.Icc 1 q, phiMeasure f j 1
            (x ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊) ≤ ε / j !) ∧
          ∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊,
            ε / q ! < phiMeasure f q 1 (x k) := by
  obtain ⟨L, B, hL, hB, hG⟩ := exists_slowTaylorOrder_interpolant hq hqp one_pos
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hε1 P hP => ?_⟩
  have hq0 : q ≠ 0 := by omega
  set kε : ℕ := ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ with hkε
  have hkε1 : 1 ≤ kε := Nat.one_le_iff_ne_zero.2 (by
    rw [hkε]; exact (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)).ne')
  have hkεpos : (0 : ℝ) < kε := by exact_mod_cast hkε1
  set a : ℕ → ℝ := fun k => ε + ε * ((kε : ℝ) - k) / kε with ha
  set st : ℕ → ℝ := fun k => (1 * a k) ^ (1 / ((p - q + 1 : ℕ) : ℝ)) with hst
  set x : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, st i with hx
  have hxs : ∀ k, x (k + 1) = x k + st k := fun k => by
    simp only [hx, Finset.sum_range_succ]
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε kε x hε hε1 hkε fun k _ => hxs k
  clear_value kε
  -- the sequence `a_k = ε + ω_k`
  have ha_ge : ∀ k ≤ kε, ε ≤ a k := fun k hk => by
    simp only [ha]
    have : (0 : ℝ) ≤ ε * ((kε : ℝ) - k) / kε := by
      have : (k : ℝ) ≤ kε := by exact_mod_cast hk
      have : 0 ≤ (kε : ℝ) - k := by linarith
      positivity
    linarith
  have ha_gt : ∀ k < kε, ε < a k := fun k hk => by
    simp only [ha]
    have : (0 : ℝ) < ε * ((kε : ℝ) - k) / kε := by
      have : (k : ℝ) < kε := by exact_mod_cast hk
      have : 0 < (kε : ℝ) - k := by linarith
      positivity
    linarith
  have ha_eq : a kε = ε := by simp only [ha]; rw [sub_self, mul_zero, zero_div, add_zero]
  have hst_pos : ∀ k ≤ kε, 0 < st k := fun k hk => by
    simp only [hst]; exact Real.rpow_pos_of_pos (by linarith [ha_ge k hk]) _
  have hqf : (0 : ℝ) < q ! := by exact_mod_cast q.factorial_pos
  have hqm : q ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hq, hqp⟩
  have hspike : ∀ k ≤ kε, ∀ i ∈ Finset.Icc 1 p, i ≠ q → iteratedDeriv i G (x k) = 0 :=
    fun k hk i hi hiq => (hGd k hk).2 i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2 hiq
  have hGq : ∀ k ≤ kε, iteratedDeriv q G (x k) = -a k := fun k hk => (hGd k hk).1
  -- the models and their minimizers
  set σ₀ := P.σ₀
  have hmodel : ∀ k ≤ kε, regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ =
      fun t => G (x k) + negMonomialRegModel p q ((p ! : ℝ) / (q - 1)!) (a k) t := fun k hk =>
    funext fun t => by
      rw [regularizedModel_real_spike hqm (hspike k hk), hGq k hk, negMonomialRegModel_def, hP]
      ring
  have hminim : ∀ k ≤ kε,
      IsMinOn (regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀) univ (st k) ∧
      regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ (st k) <
        regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ 0 := fun k hk => by
    have hak : 0 < a k := by linarith [ha_ge k hk]
    obtain ⟨hmin, hval⟩ := isMinOn_neg_monomial_add_regularization_book hq hqp hak
    rw [hmodel k hk]
    have hstk : st k = (a k) ^ (1 / ((p - q + 1 : ℕ) : ℝ)) := by simp only [hst, one_mul]
    refine ⟨isMinOn_iff.2 fun t _ => ?_, ?_⟩
    · rw [hstk]
      linarith [isMinOn_iff.1 hmin t (mem_univ t)]
    · rw [hstk]
      simp only
      rw [hval]
      have h0 : negMonomialRegModel p q ((p ! : ℝ) / (q - 1)!) (a k) 0 = 0 := by
        simp [negMonomialRegModel_def, hq0]
      rw [h0]
      have : 0 < (((p - q + 1 : ℕ) : ℝ) / ((p + 1) * q !)) * a k ^ ((p + 1 : ℝ) /
          ((p - q + 1 : ℕ) : ℝ)) := by positivity
      linarith
  -- Taylor decrements along the iterates
  have hdec_lt : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q, j < q → ∀ e : ℝ,
      (ftaylorSeries ℝ G (x k)).taylorDecrement j e = 0 := fun k hk j hj hjq e =>
    taylorDecrement_real_eq_zero (fun i hi => hspike k hk i
      (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hi).1, ((Finset.mem_Icc.1 hi).2.trans hjq.le).trans
        hqp⟩) (by have := (Finset.mem_Icc.1 hi).2; omega)) e
  have hdec_q : ∀ k ≤ kε, ∀ e : ℝ,
      (ftaylorSeries ℝ G (x k)).taylorDecrement q e = a k / q ! * e ^ q := fun k hk e => by
    rw [taylorDecrement_real_spike (m := q) (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
      (fun i hi hiq => hspike k hk i (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hi).1,
        (Finset.mem_Icc.1 hi).2.trans hqp⟩) hiq), hGq k hk]
    ring
  have hdec_p : ∀ k ≤ kε, (ftaylorSeries ℝ G (x k)).taylorDecrement p (st k) =
      a k * st k ^ q / q ! := fun k hk => by
    rw [taylorDecrement_real_spike hqm (hspike k hk), hGq k hk]
    ring
  have hφ_lt : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q, j < q →
      taylorMeasure (ftaylorSeries ℝ G (x k)) j 1 univ = 0 := fun k hk j hj hjq => by
    have := taylorMeasure_real_monomial (a := 0) (m := 0) le_rfl zero_le_one
      (D := ftaylorSeries ℝ G (x k)) (j := j) fun e => by rw [hdec_lt k hk j hj hjq, zero_mul]
    rwa [zero_mul] at this
  have hφ_q : ∀ k ≤ kε, taylorMeasure (ftaylorSeries ℝ G (x k)) q 1 univ = a k / q ! :=
    fun k hk => by
      have := taylorMeasure_real_monomial
        (div_nonneg (by linarith [ha_ge k hk]) hqf.le) zero_le_one (hdec_q k hk)
      rwa [one_pow, mul_one] at this
  -- witnesses
  have hw : ∀ k j, ∃ e : ℝ, IsApproxMeasureStep ((ftaylorSeries ℝ G (x k)).taylorDecrement j)
      1 univ P.ς e ∧ (ftaylorSeries ℝ G (x k)).taylorDecrement j e =
        P.ς * taylorMeasure (ftaylorSeries ℝ G (x k)) j 1 univ := fun k j =>
    exists_isApproxMeasureStep_eq isClosed_univ (mem_univ 0) (starConvex_univ 0) zero_le_one
      ((ftaylorSeries ℝ G (x k)).continuous_taylorDecrement j).continuousOn
      ((ftaylorSeries ℝ G (x k)).taylorDecrement_zero_right j) ⟨P.ς_pos.le, P.ς_le_one⟩
  choose d hd hdeq using hw
  set σs : ℕ → ℝ := fun _ => σ₀ with hσs
  -- the tests
  have hstop₁ : ∀ k ≤ kε, (arqpStop₁ P q (fun _ => ε) (arqpData G p x σs) (fun _ _ => 1) d k ↔
      k = kε) := by
    intro k hk
    simp only [arqpStop₁, measureTestPasses_iff]
    constructor
    · intro ht
      by_contra hne
      have hlt : k < kε := lt_of_le_of_ne hk hne
      have := ht q (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
      change (ftaylorSeries ℝ G (x k)).taylorDecrement q (d k q) ≤ _ at this
      rw [hdeq, hφ_q k hk, one_pow, mul_one] at this
      have h1 := ha_gt k hlt
      have h2 : P.ς * ε / q ! < P.ς * (a k / q !) := by
        rw [mul_div_assoc]
        exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right h1 hqf) P.ς_pos
      linarith
    · intro hkk j hj
      change (ftaylorSeries ℝ G (x k)).taylorDecrement j (d k j) ≤ _
      rw [hdeq]
      rcases (Finset.mem_Icc.1 hj).2.lt_or_eq with hjq | rfl
      · rw [hφ_lt k hk j hj hjq, mul_zero]
        have := P.ς_pos
        positivity
      · rw [hφ_q k hk, hkk, ha_eq, one_pow, mul_one]
        exact le_of_eq (mul_div_assoc _ _ _).symm
  -- the ratio
  have hρ : ∀ k < kε, arqpRho G p x st σs k = 1 := by
    intro k hk
    change reductionRatio G (x k) (st k)
      ((ftaylorSeries ℝ G (x k)).taylorDecrement p (st k)) = 1
    have hpos : 0 < a k * st k ^ q / q ! := by
      have := hst_pos k hk.le
      have : 0 < a k := by linarith [ha_ge k hk.le]
      positivity
    rw [reductionRatio_def, hdec_p k hk.le, ← hxs k, hGf k hk, hxs k, add_sub_cancel_left,
      sub_sub_cancel, div_self hpos.ne']
  have hη1 : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  have hstop₂ : ∀ k ≤ kε, ¬ arqpStop₂ (arqpData G p x σs) st k := fun k hk h2 =>
    (hminim k hk).2.ne h2
  have hfirst : IsFirstHit (arqpGlobalStop G P p q (fun _ => ε) x st σs d) kε :=
    ⟨Or.inl ((hstop₁ kε le_rfl).2 rfl), fun i hi h' => h'.elim
      (fun h1 => hi.ne ((hstop₁ i hi.le).1 h1)) (hstop₂ i hi.le)⟩
  have hbefore : ∀ k, (∀ i ≤ k, ¬ arqpGlobalStop G P p q (fun _ => ε) x st σs d i) → k < kε := by
    intro k hk
    by_contra hge
    exact hk kε (not_lt.1 hge) hfirst.1
  have hbefore' : ∀ k, (∀ i < k, ¬ arqpGlobalStop G P p q (fun _ => ε) x st σs d i) → k ≤ kε := by
    intro k hk
    by_contra hge
    exact hk kε (not_le.1 hge) hfirst.1
  refine ⟨G, neg_le_of_abs_iteratedDeriv_zero_le fun t => hGB 0 (Nat.zero_le p) t,
    assumptionD1pL_real hGc hGL hGB, x, st, σs, d, ⟨⟨rfl, fun k hk _ => (hminim k
      (hbefore' k hk)).1, fun k hk => ?_⟩, fun k _ j _ => hd k j, fun k hk hρ' => ?_⟩,
    by simp [hx], fun _ => rfl, hρ, hfirst, fun j hj => ?_, fun k hk => ?_⟩
  · have hk' := hbefore k hk
    have hρk := hρ k hk'
    refine ⟨?_, ⟨fun _ => ⟨max_le P.σmin_le_σ₀ ?_, le_rfl⟩, fun _ h => ?_, fun h => ?_⟩⟩
    · rw [hρk, ite_eq_left hη1]; exact hxs k
    · exact mul_le_of_le_one_left P.σ₀_pos.le P.γ₁_le_one
    · rw [hρk] at h; linarith [P.η₂_lt_one]
    · rw [hρk] at h; linarith
  · exact absurd (hρ k (hbefore k hk) ▸ hη1) hρ'
  · rcases (Finset.mem_Icc.1 hj).2.lt_or_eq with hjq | rfl
    · rw [phiMeasure_def, hφ_lt kε le_rfl j hj hjq]
      have : (0 : ℝ) < j ! := by positivity
      positivity
    · rw [phiMeasure_def, hφ_q kε le_rfl, ha_eq]
  · rw [phiMeasure_def, hφ_q k hk.le]
    exact div_lt_div_of_pos_right (ha_gt k hk) hqf

/-- **Corollary 12.2.16** of [cartis2022evaluation] (slow convergence of ARqp for $q \in \{1, 2\}$).
Let $q \in \{1, 2\}$ and $q \le p$. There are $f_{\mathrm{low}}$ and $L \ge 1$, which depend
only on $p$ and $q$, with the following property. For every $\varepsilon \in (0, 1]$ and all
ARqp constants with $\sigma_0 = p!/(q-1)!$, there is $f : \mathbb{R} \to \mathbb{R}$ with
$f \ge f_{\mathrm{low}}$ that satisfies f.D1pL with all constants $L_{f,j} = L$, and an ARqp run
(`CartisGouldToint.Chapter12.algorithm_12_2_2`) from $x_0 = 0$ for the tolerances
$\varepsilon_j = \varepsilon$, with $\delta_0 = 1$, all radii $1$ and $d^m = 0$, that terminates
at $k_\varepsilon = \lceil \varepsilon^{-(p+1)/(p-q+1)} \rceil$, with
$\phi^1_{f,j}(x_{k_\varepsilon}) \le \varepsilon/j!$ for $j \in [1:q]$ and
$\phi^1_{f,q}(x_k) > \varepsilon/q!$ for all $k < k_\varepsilon$.

So the bound of Theorem 12.2.14 (1) is sharp in order. The proof combines
`CartisGouldToint.Chapter12.theorem_12_2_15` with
`CartisGouldToint.Chapter12.IsARqpGlobalStepRun.toAlgorithm`. -/
theorem corollary_12_2_16 {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ P : ARqpParams,
      P.σ₀ = (p ! : ℝ) / (q - 1)! →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          algorithm_12_2_2 f P p q (fun _ => ε) (fun _ => 1) x s σ (fun _ _ => 1)
            (fun _ _ => 1) d (fun _ _ => 0) ∧ x 0 = 0 ∧
          IsFirstHit (arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => 1) d)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          (∀ j ∈ Finset.Icc 1 q, phiMeasure f j 1
            (x ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊) ≤ ε / j !) ∧
          ∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊,
            ε / q ! < phiMeasure f q 1 (x k) := by
  obtain ⟨flow, L, hL, H⟩ := theorem_12_2_15 hq hqp
  refine ⟨flow, L, hL, fun ε hε hε1 P hP => ?_⟩
  obtain ⟨f, hb, hf, x, s, σ, d, hrun, hx0, -, -, hfirst, hφ1, hφ2⟩ := H ε hε hε1 P hP
  exact ⟨f, hb, hf, x, s, σ, d, hrun.toAlgorithm hq2 hqp fun _ _ => hε.le, hx0, hfirst, hφ1, hφ2⟩

/-- **Theorem 12.2.15** of [cartis2022evaluation], counterexample for $q \ge 3$. Let
$0 < \varepsilon < \frac12$, $\theta < 1$ and $\varsigma > 0$, and let
$G : \mathbb{R} \to \mathbb{R}$ and $y \in \mathbb{R}$ with $G'(y) = G''(y) = 0$ and
$G'''(y) = -2\varepsilon$. Let
$$m(s) = T_{G,3}(y, s) + \frac{3!/2!}{4!} |s|^4 = G(y) - \frac{2\varepsilon}{3!} s^3 +
  \frac{3}{4!} s^4$$
be the ARqp model with $p = 3$ and $\sigma = 3!/2!$. Then $s_0 = 2\varepsilon$ is a global
minimizer of $m$ (12.2.70), $|s_0| < 1$, $\phi^1_{m,3}(s_0) > \theta \varepsilon/3!$, and no
displacement $d$ is a $\varsigma$-approximate optimality displacement of radius $1$ for
$\Delta T_{m,3}(s_0, \cdot)$ with $\Delta T_{m,3}(s_0, d) \le \varsigma \theta \varepsilon/3!$.

This is the example of the proof of Theorem 12.2.15 for $p = q = 3$ at $k = 0$, where
$f'(x_0) = f''(x_0) = 0$, $f'''(x_0) = -(\varepsilon + \omega_0) = -2\varepsilon$ and
$\sigma_0 = 3!/2!$. Since $|s_0| < 1$, the long-step branch is not available, and (12.2.29)
fails at the order $3$ with the radius $\delta_{s_0,3} = 1$ and the tolerance
$\varepsilon_3 = \varepsilon$. So the hypothesis "$\delta_{s_k,j} = 1$ is possible" of the
theorem fails for its own example, as in Example 12.2.1. The bound on the measure comes from
$\phi^1_{m,3}(s_0) \ge \Delta T_{m,3}(s_0, -1) = 2\varepsilon/3 - \varepsilon^2 \ge
\varepsilon/6$. At $\varepsilon = \frac12$ the step $s_0 = 1$ is long and is accepted by the
long-step branch. -/
theorem theorem_12_2_15_counterexample {ε θ ς : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hθ : θ < 1)
    (hς : 0 < ς) {G : ℝ → ℝ} {y : ℝ} (h1 : iteratedDeriv 1 G y = 0)
    (h2 : iteratedDeriv 2 G y = 0) (h3 : iteratedDeriv 3 G y = -(2 * ε)) :
    IsMinOn (regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !)) univ (2 * ε) ∧
      ‖2 * ε‖ < 1 ∧ θ * ε / 3 ! <
        phiMeasure (regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !)) 3 1 (2 * ε) ∧
      ¬ ∃ dm : ℝ, IsApproxMeasureStep ((ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ G y)
          3 ((3 ! : ℝ) / 2 !)) (2 * ε)).taylorDecrement 3) 1 univ ς dm ∧
        (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !))
          (2 * ε)).taylorDecrement 3 dm ≤ ς * θ * ε * 1 ^ 3 / 3 ! := by
  set a := 2 * ε with ha
  have ha0 : 0 < a := by positivity
  set g : ℝ → ℝ := fun t => -a * t ^ 3 / 6 + t ^ 4 / 8 with hg
  have hmodel : regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !) =
      fun t => G y + g t := by
    funext t
    rw [regularizedModel_real_spike (m := 3) (by decide) (fun i hi hi3 => by
      rcases (show i = 1 ∨ i = 2 by have := Finset.mem_Icc.1 hi; omega) with rfl | rfl
      · exact h1
      · exact h2), h3]
    simp only [hg, (by decide : Even 4).pow_abs]
    norm_num [Nat.factorial]
    ring
  have hmodel' : regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !) =
      fun t => G y + negMonomialRegModel 3 3 ((3 ! : ℝ) / (3 - 1)!) a t := by
    rw [hmodel]
    funext t
    simp only [hg, negMonomialRegModel_def, (by decide : Even 4).pow_abs]
    norm_num [Nat.factorial]
    ring
  -- the decrement along `-1`
  have hc : ContDiffAt ℝ 4 g a := by rw [hg]; fun_prop
  have hdec : (ftaylorSeries ℝ g a).taylorDecrement 3 (-1) = a / 3 - a ^ 2 / 4 := by
    set c : ℕ → ℝ := fun i => if i = 2 then a ^ 2 / 4 else if i = 3 then -a / 3 else
      if i = 4 then 1 / 8 else 0 with hcdef
    have hpoly : ∀ t : ℝ, g (a + t • (-1)) = g a + ∑ i ∈ Finset.Icc 1 4, t ^ i * c i := by
      intro t
      rw [show Finset.Icc 1 4 = {1, 2, 3, 4} by decide]
      simp [hcdef, hg, smul_eq_mul]
      ring
    rw [ftaylorSeries_taylorDecrement_eq, taylorPolynomial_eq_of_poly hc
      (Eventually.of_forall hpoly) (by norm_num : 3 ≤ 4),
      show Finset.Icc 1 3 = {1, 2, 3} by decide]
    simp [hcdef]
    ring
  have hφ : θ * ε / 3 ! <
      phiMeasure (regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !)) 3 1 a := by
    rw [phiMeasure_def, hmodel, taylorMeasure_real_const_add]
    refine lt_of_lt_of_le ?_ (taylorDecrement_le_taylorMeasure _ 3 (S := univ) (d := -1)
      (δ := 1) ⟨by simp, mem_univ _⟩)
    rw [hdec, ha]
    norm_num [Nat.factorial]
    nlinarith
  refine ⟨?_, by rw [Real.norm_eq_abs, abs_of_pos ha0]; linarith, hφ, ?_⟩
  · rw [hmodel']
    obtain ⟨hmin, -⟩ := isMinOn_neg_monomial_add_regularization_book (p := 3) (q := 3)
      (by norm_num) le_rfl ha0
    have e : a ^ (1 / ((3 - 3 + 1 : ℕ) : ℝ)) = a := by norm_num
    rw [e] at hmin
    refine isMinOn_iff.2 fun t _ => ?_
    linarith [isMinOn_iff.1 hmin t (mem_univ t)]
  · rintro ⟨dm, hdm, hle⟩
    have h := hdm.2.trans hle
    change ς * phiMeasure _ 3 1 a ≤ _ at h
    have : ς * (θ * ε / 3 !) < ς * phiMeasure (regularizedModel (ftaylorSeries ℝ G y) 3
        ((3 ! : ℝ) / 2 !)) 3 1 a := mul_lt_mul_of_pos_left hφ hς
    have e : ς * θ * ε * 1 ^ 3 / 3 ! = ς * (θ * ε / 3 !) := by ring
    linarith

/-- **Equation (12.2.85)** of [cartis2022evaluation], the regularization weight of Theorem 12.2.17:
$\sigma = (3/(p-1))^p\, p!/q!$ if $p > 2$, and $\sigma = p!$ otherwise. -/
noncomputable def arqpSigmaSharp (p q : ℕ) : ℝ :=
  if 2 < p then (3 / ((p : ℝ) - 1)) ^ p * p ! / q ! else p !

/-- The weight (12.2.85) is positive. -/
theorem arqpSigmaSharp_pos (p q : ℕ) : 0 < arqpSigmaSharp p q := by
  unfold arqpSigmaSharp
  split_ifs with hp
  · have : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) < p := by exact_mod_cast hp
      linarith
    positivity
  · positivity

/-- The admissible radius of Theorem 12.2.17. Let $p > 2$, $q \le p$, $\varepsilon \in (0, 1]$ and
$\beta \ge \varepsilon^q/q!$, and let $\sigma$ be the weight (12.2.85). Then $(p - 1)
\varepsilon \le 3 (\beta p!/\sigma)^{1/p}$, so that Example 12.1.3 (iv) gives
$\phi^\varepsilon_{m,j}(s^*) = 0$. -/
theorem arqpSigmaSharp_radius {p q : ℕ} (hp : 2 < p) (hqp : q ≤ p) {ε β : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hβ : ε ^ q / q ! ≤ β) :
    ((p : ℝ) - 1) * ε ≤ 3 * (β * p ! / arqpSigmaSharp p q) ^ (1 / (p : ℝ)) := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  have hp0 : p ≠ 0 := by omega
  have hqf : (0 : ℝ) < q ! := by positivity
  have hpf : (0 : ℝ) < p ! := by positivity
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have e : β * p ! / arqpSigmaSharp p q = (β * q !) * (((p : ℝ) - 1) / 3) ^ p := by
    rw [arqpSigmaSharp, ite_eq_left hp, div_pow, div_pow]
    field_simp
  rw [e, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (((p : ℝ) - 1) / 3),
    ← Real.rpow_mul (by positivity), mul_one_div_cancel (by exact_mod_cast hp0), Real.rpow_one]
  have h1 : ε ≤ (β * q !) ^ (1 / (p : ℝ)) := by
    have h2 : ε ^ q ≤ β * q ! := by rwa [div_le_iff₀ hqf] at hβ
    calc ε = (ε ^ p) ^ (1 / (p : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, mul_one_div_cancel
            (by exact_mod_cast hp0), Real.rpow_one]
      _ ≤ (ε ^ q) ^ (1 / (p : ℝ)) :=
          Real.rpow_le_rpow (by positivity) (pow_le_pow_of_le_one hε.le hε1 hqp) (by positivity)
      _ ≤ (β * q !) ^ (1 / (p : ℝ)) := Real.rpow_le_rpow (by positivity) h2 (by positivity)
  have : ((p : ℝ) - 1) * ε ≤ ((p : ℝ) - 1) * (β * q !) ^ (1 / (p : ℝ)) :=
    mul_le_mul_of_nonneg_left h1 hp1.le
  linarith

/-- **Theorem 12.2.17** of [cartis2022evaluation] (slow convergence of ARqp, general case). Let
$1 \le q \le p \le r$. There are $f_{\mathrm{low}}$ and $L \ge 1$, which depend only on $p$, $q$
and $r$, with the following property. For every $\varepsilon \in (0, \frac12]$ and all ARqp
constants with $\sigma_0$ the weight (12.2.85), there is $f : \mathbb{R} \to \mathbb{R}$ with
$f \ge f_{\mathrm{low}}$ that satisfies f.D1rL with all constants $L_{f,j} = L$, and an ARqp run
(`CartisGouldToint.Chapter12.algorithm_12_2_2`) for the tolerances
$\varepsilon_j = \varepsilon$, with $\delta_0 = \varepsilon$, all Step-1 and Step-2 radii equal
to $\varepsilon$ (12.2.89) and $d^m = 0$, such that:
* $x_0 = 0$ and $\sigma_k = \sigma_0$ for all $k$;
* $\kappa_\delta(\sigma_k) \varepsilon \le \varepsilon$ for all $k$, so that the radii property
  (12.2.50) of Theorem 12.2.14 (2) holds;
* $\rho_k = 1$ for all $k < k_\varepsilon$, where $k_\varepsilon = \lceil
  \varepsilon^{-q(p+1)/p} \rceil$;
* the run terminates at $k_\varepsilon$, and $x_{k_\varepsilon}$ is an
  $(\varepsilon, \varepsilon)$-approximate $q$-th order minimizer:
  $\phi^{\varepsilon}_{f,j}(x_{k_\varepsilon}) \le \varepsilon^{j+1}/j!$ for $j \in [1:q]$.

So ARqp can need $\varepsilon^{-q(p+1)/p}$ iterations and evaluations, even on functions with
more Lipschitz continuous derivatives than it uses.

**Reading.** The source asks "$\varepsilon$ sufficiently small"; here $\varepsilon \le \frac12$.

**Typo.** In (12.2.78) the residual of the order $q$ is $\varepsilon/k_\varepsilon$, not $0$. It
still satisfies (A.32).

In the construction, the steps are the global model minimizers (12.2.88). The approximate
optimality at $x_{k_\varepsilon}$ is `Optimization.IsEpsDeltaApprox` for the radii
$\delta_j = \varepsilon$, and $\kappa_\delta$ is `Optimization.arqpKappaDelta`. -/
theorem theorem_12_2_17 {p q r : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) (hpr : p ≤ r) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ P : ARqpParams,
      P.σ₀ = arqpSigmaSharp p q →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ AssumptionD1pL f r (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          algorithm_12_2_2 f P p q (fun _ => ε) (fun _ => ε) x s σ (fun _ _ => ε)
            (fun _ _ => ε) d (fun _ _ => 0) ∧
          x 0 = 0 ∧ (∀ k, σ k = P.σ₀) ∧
          (∀ k, arqpKappaDelta P (finMax 1 (fun _ => L) p) (σ k) * ε ≤ ε) ∧
          (∀ k < ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊, arqpRho f p x s σ k = 1) ∧
          IsFirstHit (arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          IsEpsDeltaApprox (ftaylorSeries ℝ f (x ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊)) univ q
            (fun _ => ε) (fun _ => ε) := by
  have hp : 1 ≤ p := hq.trans hqp
  set σv := arqpSigmaSharp p q with hσv
  have hσv : 0 < σv := arqpSigmaSharp_pos p q
  obtain ⟨L, B, hL, hB, hG⟩ := exists_slowARqpSmooth_interpolant hq hqp hpr hσv
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hε2 P hP => ?_⟩
  have hε1 : ε ≤ 1 := hε2.trans (by norm_num)
  set kε : ℕ := ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ with hkε
  have hkε1 : 1 ≤ kε := Nat.one_le_iff_ne_zero.2 (by
    rw [hkε]; exact (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)).ne')
  have hkεpos : (0 : ℝ) < kε := by exact_mod_cast hkε1
  have hqf : (0 : ℝ) < q ! := by positivity
  set ω : ℕ → ℝ := fun k => ε ^ ((q : ℝ) * r / p) * ((kε : ℝ) - k) / kε with hω
  set β : ℕ → ℝ := fun k => (ε ^ q + ω k) / q ! with hβ
  set st : ℕ → ℝ := fun k => (p ! * β k / σv) ^ (1 / (p : ℝ)) with hst
  set x : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, st i with hx
  have hxs : ∀ k, x (k + 1) = x k + st k := fun k => by
    simp only [hx, Finset.sum_range_succ]
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε kε x hε hε1 hkε fun k _ => hxs k
  clear_value kε
  -- `ω_k` and `β_k`
  have hω0 : ∀ k ≤ kε, 0 ≤ ω k := fun k hk => by
    have : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have : 0 ≤ (kε : ℝ) - k := by linarith
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hε.le _) this) hkεpos.le
  have hωpos : ∀ k < kε, 0 < ω k := fun k hk => by
    have : (k : ℝ) < kε := by exact_mod_cast hk
    have : 0 < (kε : ℝ) - k := by linarith
    exact div_pos (mul_pos (Real.rpow_pos_of_pos hε _) this) hkεpos
  have hωkε : ω kε = 0 := by simp only [hω]; rw [sub_self, mul_zero, zero_div]
  have hωle : ∀ k ≤ kε, ω k ≤ ε ^ q := fun k hk => by
    have h1 : ((kε : ℝ) - k) / kε ≤ 1 := by
      rw [div_le_one hkεpos]; have := (Nat.cast_nonneg (α := ℝ) k); linarith
    have h2 : ε ^ ((q : ℝ) * r / p) ≤ ε ^ q := by
      rw [← Real.rpow_natCast ε q]
      refine Real.rpow_le_rpow_of_exponent_ge hε hε1 ?_
      have : (p : ℝ) ≤ r := by exact_mod_cast hpr
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
      rw [le_div_iff₀ hp0]
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith
    calc ω k = ε ^ ((q : ℝ) * r / p) * (((kε : ℝ) - k) / kε) := by simp only [hω]; ring
      _ ≤ ε ^ q * 1 := mul_le_mul h2 h1 (div_nonneg (by
          have : (k : ℝ) ≤ kε := by exact_mod_cast hk
          linarith) hkεpos.le) (by positivity)
      _ = ε ^ q := mul_one _
  have hβ_ge : ∀ k ≤ kε, ε ^ q / q ! ≤ β k := fun k hk => by
    simp only [hβ]; gcongr; linarith [hω0 k hk]
  have hβ_pos : ∀ k ≤ kε, 0 < β k := fun k hk => lt_of_lt_of_le (by positivity) (hβ_ge k hk)
  have hst_pos : ∀ k ≤ kε, 0 < st k := fun k hk => by
    have := hβ_pos k hk; simp only [hst]; positivity
  -- the derivatives at the iterates
  have hspike : ∀ k ≤ kε, ∀ j ≤ r, ∀ i ∈ Finset.Icc 1 j, i ≠ 1 →
      iteratedDeriv i G (x k) = 0 := fun k hk j hj i hi hi1 =>
    (hGd k hk).2 i (by have := (Finset.mem_Icc.1 hi).1; omega)
      ((Finset.mem_Icc.1 hi).2.trans hj)
  have hG1 : ∀ k ≤ kε, iteratedDeriv 1 G (x k) = -β k := fun k hk => by
    rw [iteratedDeriv_one]; exact (hGd k hk).1
  have hdec : ∀ k ≤ kε, ∀ j, 1 ≤ j → j ≤ r → ∀ e : ℝ,
      (ftaylorSeries ℝ G (x k)).taylorDecrement j e = β k * e ^ 1 := fun k hk j hj1 hjr e => by
    rw [taylorDecrement_real_spike (m := 1) (Finset.mem_Icc.2 ⟨le_rfl, hj1⟩)
      (hspike k hk j hjr), hG1 k hk]
    simp
  -- the models
  set σ₀ := P.σ₀
  have hmodel : ∀ k ≤ kε, regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ =
      fun t => G (x k) + (-β k * t + σv * |t| ^ (p + 1) / (p + 1)!) := fun k hk =>
    funext fun t => by
      rw [regularizedModel_real_spike (Finset.mem_Icc.2 ⟨le_rfl, hp⟩)
        (fun i hi hi1 => hspike k hk p hpr i hi hi1), hG1 k hk, hP]
      ring
  have hstk : ∀ k, st k = (β k * p ! / σv) ^ (1 / (p : ℝ)) := fun k => by
    simp only [hst]; ring_nf
  have hminim : ∀ k ≤ kε,
      IsMinOn (regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀) univ (st k) ∧
      regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ (st k) <
        regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ 0 := fun k hk => by
    obtain ⟨hmin, hneg⟩ := isMinOn_linearRegModel hp (hβ_pos k hk) hσv
    rw [hmodel k hk, hstk k]
    refine ⟨isMinOn_iff.2 fun t _ => ?_, ?_⟩
    · linarith [isMinOn_iff.1 hmin t (mem_univ t)]
    · simp only [mul_zero, abs_zero, zero_pow (Nat.succ_ne_zero p), zero_div, add_zero]
      linarith
  -- the model measures vanish at the steps with radius `ε`
  have hφm : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q, taylorMeasure (ftaylorSeries ℝ
      (regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀) (st k)) j ε univ = 0 := by
    intro k hk j hj
    rw [hmodel k hk, taylorMeasure_real_const_add, hstk k]
    refine taylorMeasure_linearRegModel_eq_zero ⟨(Finset.mem_Icc.1 hj).1,
      (Finset.mem_Icc.1 hj).2.trans hqp⟩ (hβ_pos k hk) hσv ?_
    by_cases hp2 : 2 < p
    · exact Or.inr (arqpSigmaSharp_radius hp2 hqp hε hε1 (hβ_ge k hk))
    · exact Or.inl (by have := (Finset.mem_Icc.1 hj).2; omega)
  -- Step-1 measures
  have hφ : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q,
      taylorMeasure (ftaylorSeries ℝ G (x k)) j ε univ = β k * ε := fun k hk j hj => by
    have := taylorMeasure_real_monomial (hβ_pos k hk).le hε.le
      (hdec k hk j (Finset.mem_Icc.1 hj).1 (((Finset.mem_Icc.1 hj).2.trans hqp).trans hpr))
    rwa [pow_one] at this
  -- witnesses
  have hw : ∀ k j, ∃ e : ℝ, IsApproxMeasureStep ((ftaylorSeries ℝ G (x k)).taylorDecrement j)
      ε univ P.ς e ∧ (ftaylorSeries ℝ G (x k)).taylorDecrement j e =
        P.ς * taylorMeasure (ftaylorSeries ℝ G (x k)) j ε univ := fun k j =>
    exists_isApproxMeasureStep_eq isClosed_univ (mem_univ 0) (starConvex_univ 0) hε.le
      ((ftaylorSeries ℝ G (x k)).continuous_taylorDecrement j).continuousOn
      ((ftaylorSeries ℝ G (x k)).taylorDecrement_zero_right j) ⟨P.ς_pos.le, P.ς_le_one⟩
  choose d hd hdeq using hw
  set σs : ℕ → ℝ := fun _ => σ₀ with hσs
  have hU : ∀ y : ℝ, {e : ℝ | y + e ∈ (univ : Set ℝ)} = univ := fun y => by ext; simp
  -- the test
  have hstop₁ : ∀ k ≤ kε,
      (arqpStop₁ P q (fun _ => ε) (arqpData G p x σs) (fun _ _ => ε) d k ↔ k = kε) := by
    intro k hk
    simp only [arqpStop₁, measureTestPasses_iff]
    have hς := P.ς_pos
    constructor
    · intro ht
      by_contra hne
      have hlt : k < kε := lt_of_le_of_ne hk hne
      have := ht q (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
      change (ftaylorSeries ℝ G (x k)).taylorDecrement q (d k q) ≤ _ at this
      rw [hdeq, hφ k hk q (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)] at this
      have h1 : ε ^ q / q ! < β k := by
        simp only [hβ]; gcongr; linarith [hωpos k hlt]
      have h2 : P.ς * ε * ε ^ q / q ! < P.ς * (β k * ε) := by
        have := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h1 hε) hς
        calc P.ς * ε * ε ^ q / q ! = P.ς * (ε ^ q / q ! * ε) := by ring
          _ < _ := this
      linarith
    · intro hkk j hj
      change (ftaylorSeries ℝ G (x k)).taylorDecrement j (d k j) ≤ _
      rw [hdeq, hφ k hk j hj]
      have hjq := (Finset.mem_Icc.1 hj).2
      have hj1 := (Finset.mem_Icc.1 hj).1
      have hβj : β k ≤ ε ^ j / j ! := by
        rcases hjq.lt_or_eq with hlt | rfl
        · -- `β_k ≤ 2 ε^q/q! ≤ ε^j/j!`
          have h1 : β k ≤ 2 * ε ^ q / q ! := by
            simp only [hβ]; gcongr; linarith [hωle k hk]
          have h2 : 2 * ε ^ q ≤ ε ^ j := by
            have : ε ^ q = ε ^ j * ε ^ (q - j) := by rw [← pow_add]; congr 1; omega
            rw [this]
            have h3 : ε ^ (q - j) ≤ ε := pow_le_of_le_one hε.le hε1 (by omega)
            have := pow_pos hε j
            nlinarith
          have h3 : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hlt.le
          calc β k ≤ 2 * ε ^ q / q ! := h1
            _ ≤ ε ^ j / q ! := by gcongr
            _ ≤ ε ^ j / j ! := by gcongr
        · rw [hkk]; simp only [hβ, hωkε, add_zero]; exact le_rfl
      calc P.ς * (β k * ε) ≤ P.ς * (ε ^ j / j ! * ε) := by gcongr
        _ = P.ς * ε * ε ^ j / j ! := by ring
  -- the ratio
  have hρ : ∀ k < kε, arqpRho G p x st σs k = 1 := by
    intro k hk
    change reductionRatio G (x k) (st k)
      ((ftaylorSeries ℝ G (x k)).taylorDecrement p (st k)) = 1
    have hpos : 0 < β k * st k := mul_pos (hβ_pos k hk.le) (hst_pos k hk.le)
    rw [reductionRatio_def, hdec k hk.le p hp hpr, pow_one, ← hxs k, hGf k hk, hxs k,
      add_sub_cancel_left, sub_sub_cancel, div_self hpos.ne']
  have hη1 : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  have hstop₂ : ∀ k ≤ kε, ¬ arqpStop₂ (arqpData G p x σs) st k := fun k hk h2 =>
    (hminim k hk).2.ne h2
  have hfirst : IsFirstHit (arqpStop G P p q (fun _ => ε) x st σs (fun _ _ => ε) d) kε :=
    ⟨Or.inl ((hstop₁ kε le_rfl).2 rfl), fun i hi h' => h'.elim
      (fun h1 => hi.ne ((hstop₁ i hi.le).1 h1)) (hstop₂ i hi.le)⟩
  have hbefore : ∀ k, (∀ i ≤ k, ¬ arqpStop G P p q (fun _ => ε) x st σs (fun _ _ => ε) d i) →
      k < kε := by
    intro k hk
    by_contra hge
    exact hk kε (not_lt.1 hge) hfirst.1
  have hbefore' : ∀ k, (∀ i < k, ¬ arqpStop G P p q (fun _ => ε) x st σs (fun _ _ => ε) d i) →
      k ≤ kε := by
    intro k hk
    by_contra hge
    exact hk kε (not_le.1 hge) hfirst.1
  have hLf : 1 ≤ finMax 1 (fun _ => max 1 (max L B)) p := le_finMax_left
  refine ⟨G, neg_le_of_abs_iteratedDeriv_zero_le fun t => hGB 0 (Nat.zero_le r) t,
    assumptionD1pL_real hGc hGL hGB, x, st, σs, d, ⟨⟨rfl, fun k hk _ => ?_, fun k hk => ?_⟩,
      mem_univ _, rfl, fun k hk j hj => ?_, fun k hk => ⟨fun _ => rfl, fun hρ' => ?_⟩⟩,
    by simp [hx], fun _ => rfl, fun k => ?_, hρ, hfirst, ?_⟩
  · -- Step 2
    have hk' := hbefore' k hk
    obtain ⟨hmin, hlt⟩ := hminim k hk'
    refine ⟨mem_univ _, hmin (mem_univ 0), fun heq => ?_, fun _ _ => hε, fun _ _ => hε1,
      Or.inr fun j hj => ?_⟩
    · rw [hU]
      intro e _
      change regularizedModel _ p σ₀ 0 ≤ regularizedModel _ p σ₀ e
      change regularizedModel _ p σ₀ (st k) = regularizedModel _ p σ₀ 0 at heq
      rw [← heq]
      exact hmin (mem_univ e)
    · rw [hU]
      refine ⟨⟨⟨by simp [hε.le], mem_univ _⟩, ?_⟩, ?_⟩
      · change P.ς * taylorMeasure (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ G (x k))
          p σ₀) (st k)) j ε univ ≤ (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ G (x k))
          p σ₀) (st k)).taylorDecrement j 0
        rw [hφm k hk' j hj, mul_zero, FormalMultilinearSeries.taylorDecrement_zero_right]
      · change (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀)
          (st k)).taylorDecrement j 0 ≤ _
        rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.ς_pos; have := P.θ_pos
        positivity
  · -- Steps 3–4
    have hk' := hbefore k hk
    have hρk := hρ k hk'
    refine ⟨?_, ⟨fun _ => ⟨max_le P.σmin_le_σ₀ ?_, le_rfl⟩, fun _ h => ?_, fun h => ?_⟩⟩
    · change x (k + 1) = if P.η₁ ≤ arqpRho G p x st σs k then x k + st k else x k
      rw [hρk, ite_eq_left hη1]; exact hxs k
    · exact mul_le_of_le_one_left P.σ₀_pos.le P.γ₁_le_one
    · change arqpRho G p x st σs k < P.η₂ at h
      rw [hρk] at h; linarith [P.η₂_lt_one]
    · change arqpRho G p x st σs k < P.η₁ at h
      rw [hρk] at h; linarith
  · rw [hU]; exact hd k j
  · exact absurd (hη1.trans_eq (hρ k (hbefore k hk)).symm) hρ'
  · calc arqpKappaDelta P (finMax 1 (fun _ => max 1 (max L B)) p) (σs k) * ε ≤ 1 * ε :=
          mul_le_mul_of_nonneg_right (arqpKappaDelta_lt_one P hLf P.σ₀_pos.le).le hε.le
      _ = ε := one_mul ε
  · exact MeasureTestPasses.isEpsDeltaApprox P.ς_pos (fun j _ => hd kε j)
      (hfirst.1.resolve_right (hstop₂ kε le_rfl))

end ARqpSharp

end CartisGouldToint.Chapter12
