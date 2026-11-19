/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDAExistence
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqIDA
import NumlibSurface.CartisGouldToint.Chapter02.Section01

/-!
# Cartis, Gould and Toint, Section 13.1: Inexact algorithms using implicit dynamic accuracy

This module formalizes Section 13.1 of [cartis2022evaluation], with the corresponding proofs of
Appendix B. The section studies the trust-region method TRqIDA (Algorithm 13.1.1) and the
adaptive-regularization method ARqpIDA (Algorithm 13.1.2) for an objective $f$ on $\mathbb{R}^n$.
Both methods use exact function values and inexact derivatives $\bar\nabla^i f(x_k)$ that satisfy
$$\|\bar\nabla^i f(x_k) - \nabla^i f(x_k)\| \le \kappa_{\nabla,i} h_{k,i} \qquad (13.1.2)$$
with constants $\kappa_{\nabla,i} \ge 0$ that the method does not know and requested accuracies
$h_{k,i}$ that the method controls (implicit dynamic accuracy). An iteration whose step is too short
for the current accuracies only reduces the accuracies; it is called accuracy-improving. Theorem
13.1.8 bounds the evaluations of TRqIDA by $O(\epsilon_{\min}^{-(q+1)})$ and Theorem 13.1.19 bounds
those of ARqpIDA by $O(\max_j \epsilon_j^{-\pi_j})$, the orders of TRq and ARqp in Chapter 12.
Neither method has a termination rule: the bounds count the evaluations before the first iterate
that is truly approximately optimal.

The inexact derivatives define the inexact Taylor decrements $\overline{\Delta T}_{f,j}(x_k, d) =
\sum_{i=1}^j \bar\nabla^i f(x_k)[d]^i / i!$ and the inexact measures $\bar\phi^\delta_{f,j}(x_k) =
\sup_{\|d\| \le \delta} \overline{\Delta T}_{f,j}(x_k, d)$ (13.1.5). A point $x$ is an
$(\epsilon, \delta)$-approximate $q$-th order minimizer if $\phi^{\delta_j}_{f,j}(x) \le \epsilon_j
\delta_j^j / j!$ for $j \in [1, q]$ (12.1.25), with the exact measures. The iterations split into
the successful iterations $\mathcal{S}$, the unsuccessful iterations $\mathcal{U}$ and the
accuracy-improving iterations $\mathcal{A}$, and $\mathcal{T} = \mathcal{S} \cup \mathcal{U}$ is the
set of trial iterations. The proofs specialize
`Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqIDA` and
`Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDA`.

## Main definitions

* Algorithm 13.1.1, `CartisGouldToint.Chapter13.algorithm_13_1_1`: a run of TRqIDA.
* Assumption f.D0qL, `CartisGouldToint.Chapter13.AssumptionD0qL`: $f$ is $C^q$ and its derivatives
  of orders $0, \dots, q$ are Lipschitz with constants $L_{f,j} \ge 1$.
* Equation (13.1.25), `CartisGouldToint.Chapter13.phiHat`: the scaled criticality $\hat\phi_{f,k} =
  j_k! \, \overline{\Delta T}_{f,j_k}(x_k, d_k) / \delta_k^{j_k}$.
* Algorithm 13.1.2, `CartisGouldToint.Chapter13.algorithm_13_1_2`: a run of ARqpIDA.
* Assumption f.D0pL, `CartisGouldToint.Chapter13.AssumptionD0pL`: Assumption f.D0qL with the order
  $p$.

## Main results

* Lemma 13.1.1, `CartisGouldToint.Chapter13.lemma_13_1_1`: the number of trial iterations of TRqIDA
  is bounded by the number of successful iterations and a logarithmic term.
* Lemma 13.1.2, `CartisGouldToint.Chapter13.lemma_13_1_2`: at a trial iteration of TRqIDA,
  $\hat\phi_{f,k} \ge \frac12 \varsigma \epsilon_{\min}$, and the predicted decrease is at least
  $\hat\phi_{f,k} \delta_k^{j_k} / j_k!$.
* Lemma 13.1.3, `CartisGouldToint.Chapter13.lemma_13_1_3`: a trial iteration with a small radius is
  very successful.
* Lemma 13.1.4, `CartisGouldToint.Chapter13.lemma_13_1_4`: the radii stay bounded below, and
  $\delta_k \ge \varsigma \kappa_\delta \epsilon_{\min}$.
* Lemma 13.1.5, `CartisGouldToint.Chapter13.lemma_13_1_5`: the predicted decrease and the decrease
  of $f$ at the trial and successful iterations are at least of order $\epsilon_{\min}^{q+1}$.
* Lemma 13.1.6, `CartisGouldToint.Chapter13.lemma_13_1_6`: small accuracies make an iteration that
  enters Step 2 a trial iteration.
* Lemma 13.1.7, `CartisGouldToint.Chapter13.lemma_13_1_7`: small accuracies make an iteration that
  passes the Step-1 tests approximately optimal.
* Theorem 13.1.8, `CartisGouldToint.Chapter13.theorem_13_1_8`: TRqIDA reaches an approximate
  minimizer after $O(\epsilon_{\min}^{-(q+1)})$ function values and derivative estimates.
* Lemma 13.1.9, `CartisGouldToint.Chapter13.lemma_13_1_9`: the number of trial iterations of ARqpIDA
  is bounded by the number of successful iterations and a logarithmic term.
* Lemma 13.1.10, `CartisGouldToint.Chapter13.lemma_13_1_10`: a displacement with a large inexact
  decrement in a small ball also decreases the regularized model.
* Lemma 13.1.11, `CartisGouldToint.Chapter13.lemma_13_1_11`: the halving loop of Step 1 keeps the
  radii above $\min(\varsigma \epsilon_j / (16 \max(\bar L, \sigma_k)), \delta^{(0)}_{k,j})$.
* Lemma 13.1.12, `CartisGouldToint.Chapter13.lemma_13_1_12`: the model decrease of Step 2, the lower
  bound (13.1.71) on the radii, and small accuracies give a trial iteration.
* Lemma 13.1.13, `CartisGouldToint.Chapter13.lemma_13_1_13`: at a trial iteration the predicted
  decrease is positive and at least $\sigma_k \|s_k\|^{p+1} / (p+1)!$.
* Lemma 13.1.14, `CartisGouldToint.Chapter13.lemma_13_1_14`: the regularization parameters stay
  below $\sigma_{\max}$.
* Lemma 13.1.15, `CartisGouldToint.Chapter13.lemma_13_1_15`: small accuracies make an iteration that
  passes the Step-1 tests approximately optimal.
* Lemma 13.1.16, `CartisGouldToint.Chapter13.lemma_13_1_16`: the radius inequality (13.1.79) after a
  successful short step to a point that is not approximately optimal.
* Lemma 13.1.17, `CartisGouldToint.Chapter13.lemma_13_1_17`: the step length after such an iteration
  is bounded below by powers of $\epsilon_j$.
* Lemma 13.1.18, `CartisGouldToint.Chapter13.lemma_13_1_18`: the predicted decrease and the decrease
  of $f$ at such an iteration are at least of order $\min_j \epsilon_j^{\pi_j}$.
* Theorem 13.1.19, `CartisGouldToint.Chapter13.theorem_13_1_19_i`,
  `CartisGouldToint.Chapter13.theorem_13_1_19_ii`: ARqpIDA reaches an approximate minimizer after
  $O(\max_j \epsilon_j^{-\pi_j})$ function values and derivative estimates, for $q \le 2$ and for
  $q > 2$. The common argument is `CartisGouldToint.Chapter13.arqpIDA_complexity`.
* Existence of runs, `CartisGouldToint.Chapter13.exists_algorithm_13_1_1`,
  `CartisGouldToint.Chapter13.exists_algorithm_13_1_2`: for every oracle that satisfies (13.1.2),
  runs of TRqIDA, and runs of ARqpIDA with the radii control, exist.

## Conventions

* Points live in $\mathbb{R}^n$, which is `EuclideanSpace ℝ (Fin n)`. Tolerances, radii and
  accuracies are sequences indexed by the orders: $\epsilon_j$ is `ε j` for $j \in [1, q]$, and
  $\epsilon_{\min}$ is `Optimization.epsMin q ε`.
* The inexact derivatives at iteration $k$ form a jet `D k : FormalMultilinearSeries ℝ ℝⁿ ℝ`. The
  decrement $\overline{\Delta T}_{f,j}(x_k, d)$ is `(D k).taylorDecrement j d`, the measure
  $\bar\phi^\delta_{f,j}(x_k)$ is `Optimization.taylorMeasure (D k) j δ univ`, and the error model
  (13.1.2) is `Optimization.JetApprox (ftaylorSeries ℝ f (x k)) (D k) r (fun i => κg i * h k i)`.
* $L_f = \max_{j \le q} L_{f,j}$ is `Optimization.lipMax L q`, and $\kappa_{\nabla,\max} = \max_{i
  \in [1, q]} \kappa_{\nabla,i}$ is `Optimization.ordMax q κg`.
* An iteration $k$ is accuracy-improving ($k \in \mathcal{A}$) when the proposition `acc k` holds,
  and a trial iteration otherwise. The function values computed before iteration $k$ (the initial
  value and one per trial iteration) are counted by `Optimization.derivEvalCount (fun i => ¬ acc i)
  k`, and the derivative estimates (the initial estimate and one per successful or
  accuracy-improving iteration) by `Optimization.derivEvalCount` of $\mathcal{S} \cup \mathcal{A}$.

## Implementation notes

* The algorithms and their analysis are those of the library, stated there on a real inner product
  space, on a feasible set $X$ and under the anchored smoothness hypothesis
  `LipschitzDerivsAnchored`. This module takes $X = \mathbb{R}^n$ under Assumption f.D0qL.
* One iteration (Steps 1, 2, 4 and 5) of TRqIDA is the predicate `Optimization.TRqDAStep`, and one
  iteration of ARqpIDA is `Optimization.ARqpDAStep`, given the value of the ratio. The
  explicit-dynamic-accuracy methods of Section 13.3 reuse them, so Lemmas 13.1.1, 13.1.2, 13.1.9,
  13.1.11 and 13.1.13 are stated for the step predicates on any feasible set. The runs
  `CartisGouldToint.Chapter13.algorithm_13_1_1` and `CartisGouldToint.Chapter13.algorithm_13_1_2`
  are `Optimization.IsTRqIDARun` and `Optimization.IsARqpIDARun` with $X = \mathbb{R}^n$; they add
  the ratios (13.1.16) and (13.1.58) with exact values and the error model (13.1.2).
* Assumption f.D0qL is `LipschitzDerivsAnchored f univ univ 0 q L` together with $L_{f,j} \ge 1$;
  `CartisGouldToint.Chapter13.assumptionD0qL_iff` gives the form of the source. Its form on an open
  convex set $C$, used for the feasible sets of Section 14.2, is
  `LipschitzDerivsAnchored f C C 0 q L` with $L_{f,j} \ge 1$.
* After an unsuccessful iteration the derivative estimates are reused:
  $\bar\nabla^i f(x_{k+1}) = \bar\nabla^i f(x_k)$.
* Step 1 records displacements $d_{k,j}$ for all orders $j \in [1, q]$; the source computes them
  only up to the first order that fails the test. Admissible displacements always exist. The halving
  loop of Step 1 of ARqpIDA is recorded by its effect on the radii,
  $\delta^{(1)}_{k,j} \le \delta^{(0)}_{k,j}$, together with witnesses of the last halving and of
  the failure of (13.1.53) at the inherited radius.
* The approximate-optimality tests are `CartisGouldToint.Chapter13.trTest` for TRqIDA, with the
  radius $\delta_k = \min(\Delta_k, \vartheta)$ at all orders, and
  `CartisGouldToint.Chapter13.arTest` for ARqpIDA, with some radii in $(0, 1]^q$. The methods cannot
  evaluate these tests.
* Constants that the source defines through a chain of earlier constants are parameters with the
  properties that the proofs use. For example, $\kappa_\Delta$ of (13.1.31) enters only through $0 <
  \kappa_\Delta \le \min(1, \gamma_1 (1 - \eta_2) / (L_f + 4 (q+1)! \kappa_s
  \kappa_{\nabla,\max}))$, which is `Optimization.IsTRKappaDelta`; the value of the source is
  `CartisGouldToint.Chapter13.trKappaDelta`.
* The finiteness of the halving loop of Step 1 (the existence half of Lemma 13.1.11) is
  `Optimization.exists_arqpDA_halving`, and the well-definedness of Step 2 (the first part of Lemma
  13.1.12) is part of the existence of runs, `Optimization.exists_arqpDA_steps`.
* The library's analysis of ARqpIDA takes the mode of the radii control as a parameter:
  `Optimization.ARqpDARadiiControl u` asks for unit radii if `u` holds and for the lower bounds at
  every order otherwise, with the exponents `Optimization.arPiOf u`. The lower-bound mode also
  covers $q \le 2$ when unit radii are not available (Section 14.2). `Optimization.RadiiControl` is
  the mode `u = (q ≤ 2)`.

## Deviations from the source

* **Algorithm 13.1.1, Step 0** (typo). The source prints $0 < \gamma_1 < 1 < \gamma_2 < \gamma_3$;
  the update (13.1.17) and the proof of Lemma 13.1.1 need
  $0 < \gamma_1 \le \gamma_2 < 1 \le \gamma_3$. See `Optimization.TRqIDAParams`.
* **Algorithm 13.1.1, Step 4** (reading). After an unsuccessful iteration with
  $\Delta_{k+1} \ge \vartheta$ the source returns to Step 2 with $d_{k+1} = d_k$; the run predicate
  performs Step 1 at every iteration, and every run of the source is a run of the predicate. See
  `CartisGouldToint.Chapter13.algorithm_13_1_1`.
* **Lemmas 13.1.1 and 13.1.9** (correction). The source assumes the bound at $\Delta_k$ (at
  $\sigma_k$); the proofs need it at $\Delta_{k+1}$ (at $\sigma_{k+1}$), and the printed statements
  are false for $k = 0$. See `CartisGouldToint.Chapter13.lemma_13_1_1`,
  `CartisGouldToint.Chapter13.lemma_13_1_9`.
* **Lemma 13.1.4** (generalization). The lemma holds for every admissible $\kappa_\Delta$; the value
  (13.1.31) is admissible when its denominator is positive. See
  `CartisGouldToint.Chapter13.lemma_13_1_4`.
* **Lemma 13.1.5** (generalization). The decrease bounds hold for every trial iteration and every
  admissible $\kappa_\Delta$. See `CartisGouldToint.Chapter13.lemma_13_1_5`.
* **Lemma 13.1.6** (reading). The source bounds the branch from Step 2 to Step 5. The Lean
  conclusion assumes Step 1 advanced to Step 2, since Step 1 can also branch directly to Step 5.
  The inexact derivative bound $\bar L_f$ is defined in (13.1.24). See
  `CartisGouldToint.Chapter13.lemma_13_1_6`.
* **Lemmas 13.1.7 and 13.1.15 and Theorems 13.1.8 and 13.1.19** (zero-error case). With
  $\kappa_{\nabla,\max}=0$ the Step 1 accuracy condition holds for every requested accuracy.
  The Lean statements multiply through by $\kappa_{\nabla,\max}$ and the complexity constants use
  only the Step 2 restriction in this case. See `Optimization.trKappaAcc` and
  `Optimization.arKappaAcc`.
* **Theorem 13.1.8** (correction). The bound (13.1.39) omits the initial derivative estimate and the
  last accuracy-improving iteration; the constant is $\kappa^F + 2$. See
  `CartisGouldToint.Chapter13.theorem_13_1_8`.
* **Theorem 13.1.8** (typo). The conclusion $\phi^\delta_{f,q}$ reads $\phi^\delta_{f,j}$. See
  `CartisGouldToint.Chapter13.theorem_13_1_8`.
* **Algorithm 13.1.2, Step 0** (reading). The list of constants omits $\varsigma \in (0, 1]$, which
  Step 1 uses. See `Optimization.ARqpIDAParams`.
* **Algorithm 13.1.2, Step 2** (correction). The source checks (13.1.46) only for $i \in [1, q]$ and
  for short steps; Lemmas 13.1.14 and 13.1.16 need $i \in [1, p]$, and the constant $\sigma_{\max}$
  of Lemma 13.1.14 needs $\max(\kappa_s, \kappa_h)$ in place of $\kappa_s$. See
  `Optimization.ARqpDAStep`, `CartisGouldToint.Chapter13.lemma_13_1_14`.
* **Lemmas 13.1.10 and 13.1.11** (proof typos). The regularization term in the model decrement
  has a minus sign, and the proof of (13.1.66) needs only the strict witness inequality in
  (13.1.67). See `CartisGouldToint.Chapter13.lemma_13_1_10` and
  `CartisGouldToint.Chapter13.lemma_13_1_11`.
* **Lemma 13.1.12** (correction and generalization). The conclusion $k \in \mathcal{T}$ also
  requires Step 1 to advance to Step 2. The lemma holds for every bound $\bar\sigma \ge \sigma_i$,
  $i \le k$, including the source's $\sigma_{k,\max}$. See
  `CartisGouldToint.Chapter13.lemma_13_1_12`.
* **Radii control (13.1.69)–(13.1.70)** (generalization). The results assume the weaker condition
  `Optimization.RadiiControl`: after a trial iteration with $\|s_k\| < 1$, $\delta_{s_k,j} = 1$ for
  all $j \in [1, q]$ if $q \le 2$, and $\delta_{s_k,j} \ge \varsigma \theta \epsilon_j / (24
  \max(\bar L_f, \sigma_k))$ for all $j \in [1, q]$ if $q > 2$. The condition of the source implies
  it (`Optimization.RadiiControl.of_unit_le_two`); for $q > 2$ the proofs do not use $\delta = 1$ at
  the orders $j \le 2$.
* **Lemma 13.1.15** (reading). The source writes $\delta_k$ for the radii $\delta^{(1)}_k$ at the
  end of Step 1. See `CartisGouldToint.Chapter13.lemma_13_1_15`.
* **Lemma 13.1.17** (correction). For $q > 2$ the constant $\kappa_{\delta,\min}^{j-1}$ is replaced
  by $\hat\kappa^{j-1}$ with $\hat\kappa = \min(\kappa_{\delta,\min}, (1 - \theta) / (2 q! A))$; the
  argument of the source needs $\kappa_{\delta,\min}$ below this bound. See
  `CartisGouldToint.Chapter13.lemma_13_1_17`.
* **Lemma 13.1.18** (correction). The source states (13.1.82) for every trial iteration before
  approximate optimality; the proof covers the successful iterations whose successor is not
  approximately optimal, and the constant uses $\hat\kappa$. See
  `CartisGouldToint.Chapter13.lemma_13_1_18`.
* **Theorem 13.1.19** (correction). The proof certifies approximate optimality only for some radii
  in $(0, 1]^q$, not for the radius one; the first index is defined with some radii, and the radius
  one follows for $q \le 2$. The constant $\kappa^C$ misses a factor
  $1 + |\log \gamma_1| / \log \gamma_2$ on a term $1$, and the derivative count needs
  $\kappa^F + 3$. See `CartisGouldToint.Chapter13.theorem_13_1_19_i`,
  `CartisGouldToint.Chapter13.theorem_13_1_19_ii`.
* **Theorem 13.1.19** (reading). For $\kappa_h = 0$, which (13.1.51) allows, $\kappa^F$ is read with
  $\log 0 = 0$. See `CartisGouldToint.Chapter13.theorem_13_1_19_i`.
-/

open Set Metric Finset Optimization
open scoped Nat

namespace CartisGouldToint.Chapter13

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-!
### Minima and maxima over the orders

The extrema over the orders are those of the library:

* $\epsilon_{\min} = \min_{j \in [1, q]} \epsilon_j$ is `Optimization.epsMin`;
* $\max_{i \in [1, r]} \kappa_i$ is `Optimization.ordMax`;
* $L_f = \max_{j \in [0, q]} L_{f,j}$ is `Optimization.lipMax`.
-/

/-! ### Assumptions f.D0qL and f.D0pL -/

/-- **Assumption f.D0qL** of [cartis2022evaluation], (13.1.23). Let
$f : \mathbb{R}^n \to \mathbb{R}$, $q \in \mathbb{N}$ and constants $L_{f,j}$. The function $f$
satisfies **Assumption f.D0qL** if $f$ is $q$ times continuously differentiable, and for every
$j \in [0, q]$ the $j$-th derivative is Lipschitz continuous with constant $L_{f,j} \ge 1$:
$$\|\nabla^j f(x) - \nabla^j f(y)\| \le L_{f,j} \|x - y\| \quad \text{for all } x, y \in
  \mathbb{R}^n.$$
The order $j = 0$ is the function itself.

The definition is `LipschitzDerivsAnchored f univ univ 0 q L` (the anchored smoothness
hypothesis of orders $[0, q]$ on the whole space) together with $L_{f,j} \ge 1$. The form of the
source is `CartisGouldToint.Chapter13.assumptionD0qL_iff` and
`CartisGouldToint.Chapter13.AssumptionD0qL.of_iteratedFDerivLipschitzOn`. -/
abbrev AssumptionD0qL (f : ℝⁿ → ℝ) (q : ℕ) (L : ℕ → ℝ) : Prop :=
  LipschitzDerivsAnchored f univ univ 0 q L ∧ ∀ j ≤ q, 1 ≤ L j

/-- **Assumption f.D0pL** of [cartis2022evaluation], Section 13.1.4. The function $f$ satisfies
**Assumption f.D0pL** if it satisfies Assumption f.D0qL with the order $p$ in place of $q$: $f$
is $C^p$ and its derivatives of orders $j \in [0, p]$ are Lipschitz continuous with constants
$L_{f,j} \ge 1$. -/
abbrev AssumptionD0pL (f : ℝⁿ → ℝ) (p : ℕ) (L : ℕ → ℝ) : Prop :=
  AssumptionD0qL f p L

section Assumption

variable {f : ℝⁿ → ℝ} {q : ℕ} {L : ℕ → ℝ}

/-- Under Assumption f.D0qL, $f$ satisfies the smoothness hypothesis
`LipschitzDerivsAnchored f univ univ 0 q L` of the library: on the whole space, the derivatives
of orders $0, \dots, q$ are Lipschitz with the constants $L_{f,j}$. -/
theorem AssumptionD0qL.lipschitzDerivsAnchored (hf : AssumptionD0qL f q L) :
    LipschitzDerivsAnchored f univ univ 0 q L :=
  hf.1

/-- Under Assumption f.D0qL, the constants satisfy $L_{f,j} \ge 1$ for every $j \le q$. -/
theorem AssumptionD0qL.normalized (hf : AssumptionD0qL f q L) : ∀ j ≤ q, 1 ≤ L j :=
  hf.2

/-- Under Assumption f.D0qL, $L_{f,j} \ge 1$ for every $j \le q$. -/
theorem AssumptionD0qL.one_le (hf : AssumptionD0qL f q L) {j : ℕ} (hj : j ≤ q) : 1 ≤ L j :=
  hf.2 j hj

/-- Under Assumption f.D0qL, $f$ is $q$ times continuously differentiable. -/
theorem AssumptionD0qL.contDiff (hf : AssumptionD0qL f q L) : ContDiff ℝ q f :=
  hf.1.contDiff

/-- Under Assumption f.D0qL, for $j \le q$ the derivative $\nabla^j f$ is Lipschitz continuous on
$\mathbb{R}^n$ with constant $L_{f,j}$. -/
theorem AssumptionD0qL.lipschitz (hf : AssumptionD0qL f q L) {j : ℕ} (hj : j ≤ q) :
    IteratedFDerivLipschitzOn f j (L j) univ :=
  hf.1.lipschitzOn_of_le hj

/-- Assumption f.D0qL in the form of the source: it holds if and only if $f$ is $C^q$ and, for every
$j \in [0, q]$, $L_{f,j} \ge 1$ and $\nabla^j f$ is Lipschitz continuous on $\mathbb{R}^n$ with
constant $L_{f,j}$. -/
theorem assumptionD0qL_iff : AssumptionD0qL f q L ↔
    ContDiff ℝ q f ∧ ∀ j ≤ q, 1 ≤ L j ∧ IteratedFDerivLipschitzOn f j (L j) univ :=
  ⟨fun hf => ⟨hf.contDiff, fun _ hj => ⟨hf.one_le hj, hf.lipschitz hj⟩⟩, fun ⟨hf, hL⟩ =>
    ⟨.of_contDiff hf (fun j hj => (hL j (Finset.mem_Icc.1 hj).2).2) univ,
      fun j hj => (hL j hj).1⟩⟩

/-- If $f$ is $C^q$ and, for every $j \in [0, q]$, $L_{f,j} \ge 1$ and $\nabla^j f$ is Lipschitz
continuous on $\mathbb{R}^n$ with constant $L_{f,j}$, then $f$ satisfies Assumption f.D0qL. -/
theorem AssumptionD0qL.of_iteratedFDerivLipschitzOn (hf : ContDiff ℝ q f)
    (hL : ∀ j ≤ q, 1 ≤ L j ∧ IteratedFDerivLipschitzOn f j (L j) univ) : AssumptionD0qL f q L :=
  assumptionD0qL_iff.2 ⟨hf, hL⟩

/-- Assumption f.D0qL with a single constant. Let $L \ge 1$, and let $f$ satisfy the smoothness
hypothesis of the library on the whole space with the constant $L$ at every order
$j \in [0, q]$. Then $f$ satisfies Assumption f.D0qL with $L_{f,j} = L$ for all $j$.

The hypothesis is `LipschitzDerivsAnchored f univ univ 0 q (fun _ => L)`. -/
theorem AssumptionD0qL.of_lipschitzDerivsAnchored {L : ℝ}
    (hf : LipschitzDerivsAnchored f univ univ 0 q (fun _ => L)) (hL : 1 ≤ L) :
    AssumptionD0qL f q (fun _ => L) :=
  ⟨hf, fun _ _ => hL⟩

/-- Under Assumption f.D0qL, $L_f = \max_{j \in [0, q]} L_{f,j} \ge 1$. -/
theorem AssumptionD0qL.one_le_lipMax (hf : AssumptionD0qL f q L) : 1 ≤ lipMax L q :=
  (hf.one_le (Nat.zero_le q)).trans (le_lipMax (Nat.zero_le q))

/-- Under Assumption f.D0qL, $f$ is $C^j$ near every point for every $j \le q$. -/
theorem AssumptionD0qL.contDiffAt (hf : AssumptionD0qL f q L) {j : ℕ} (hj : j ≤ q) (y : ℝⁿ) :
    ContDiffAt ℝ j f y :=
  hf.1.contDiffAt_of_le hj (mem_univ y)

/-- Taylor's theorem (A.19) under Assumption f.D0qL. For $j \le q$ and $x, s \in \mathbb{R}^n$,
$$|f(x + s) - T_{f,j}(x, s)| \le \frac{L_{f,j}}{(j+1)!} \|s\|^{j+1}.$$
The Taylor polynomial is written as $T_{f,j}(x, s) = f(x) - \Delta T_{f,j}(x, s)$. -/
theorem AssumptionD0qL.abs_sub_le (hf : AssumptionD0qL f q L) {j : ℕ} (hj : j ≤ q) (x s : ℝⁿ) :
    |f (x + s) - (f x - (ftaylorSeries ℝ f x).taylorDecrement j s)| ≤
      L j / ((j + 1)! : ℝ) * ‖s‖ ^ (j + 1) :=
  hf.lipschitzDerivsAnchored.abs_sub_taylorDecrement_le_of_le hj (mem_univ x) (mem_univ _)

/-- **Equation (13.1.24)** of [cartis2022evaluation]. Under Assumption f.D0qL,
$\|\nabla^i f(x)\| \le L_f$ for every $i \in [1, q]$ and every $x$. -/
theorem AssumptionD0qL.norm_iteratedFDeriv_le (hf : AssumptionD0qL f q L) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 q) (x : ℝⁿ) : ‖iteratedFDeriv ℝ i f x‖ ≤ lipMax L q :=
  hf.lipschitzDerivsAnchored.norm_iteratedFDeriv_le_lipMax hf.normalized hi (mem_univ x)

/-- **Equations (13.1.24) and (13.1.63)** of [cartis2022evaluation]. Assume f.D0qL. Let
$\bar\nabla^i f(x)$ be inexact derivatives with $\|\bar\nabla^i f(x) - \nabla^i f(x)\| \le
\kappa_{\nabla,i} h_i$, where $\kappa_{\nabla,i} \ge 0$ and $0 \le h_i \le \kappa_h$ for
$i \in [1, q]$. Then
$$\|\bar\nabla^i f(x)\| \le L_f + \kappa_{\nabla,\max} \kappa_h \quad \text{for } i \in [1,
  q].$$
-/
theorem AssumptionD0qL.norm_le_of_jetApprox (hf : AssumptionD0qL f q L)
    {D : FormalMultilinearSeries ℝ ℝⁿ ℝ} {κg hh : ℕ → ℝ} {κh : ℝ} {x : ℝⁿ}
    (hD : JetApprox (ftaylorSeries ℝ f x) D q (fun i => κg i * hh i))
    (hκ : ∀ i ∈ Finset.Icc 1 q, 0 ≤ κg i) (hh0 : ∀ i ∈ Finset.Icc 1 q, 0 ≤ hh i)
    (hhκ : ∀ i ∈ Finset.Icc 1 q, hh i ≤ κh) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) :
    ‖D i‖ ≤ lipMax L q + ordMax q κg * κh :=
  hf.lipschitzDerivsAnchored.norm_le_of_jetApprox hf.normalized (mem_univ x) hD hκ hh0 hhκ hi

end Assumption



/-! ### TRqIDA -/

section TRqIDA

variable {X : Set ℝⁿ} {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {ρ : ℕ → ℝ} {L : ℕ → ℝ}
  {k : ℕ}

/-- **Equation (13.1.25)** of [cartis2022evaluation]. For inexact derivatives $D$, an order $j$, a
radius $\delta$ and a displacement $d$, the **scaled criticality** is
$$\hat\phi = \frac{j! \, \overline{\Delta T}_{j}(d)}{\delta^j}.$$
At iteration $k$ of TRqIDA, with $j = j_k$, $\delta = \delta_k$ and $d = d_k$, this is
$\hat\phi_{f,k}$.

The definition is `Optimization.trqGap`. The value at iteration $k$ is `Optimization.trPhiHat`. -/
noncomputable abbrev phiHat (D : FormalMultilinearSeries ℝ ℝⁿ ℝ) (j : ℕ) (δ : ℝ) (d : ℝⁿ) : ℝ :=
  trqGap D j δ d

/-- The test of approximate optimality of TRqIDA at iteration $k$: $x_k$ is an
$(\epsilon, \delta_k)$-approximate $q$-th order minimizer (12.1.25) of [cartis2022evaluation]
with the radius $\delta_k = \min(\Delta_k, \vartheta)$ at all orders, that is,
$\phi^{\delta_k}_{f,j}(x_k) \le \epsilon_j \delta_k^j / j!$ for $j \in [1, q]$.

The method cannot evaluate this test, because it uses the exact derivatives. -/
def trTest (f : ℝⁿ → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (k : ℕ) :
    Prop :=
  IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (fun _ => trqDARadius P Δ k)

/-- The approximate-optimality test `Optimization.trqIDATest` of the library on the feasible set
$\mathbb{R}^n$ is `CartisGouldToint.Chapter13.trTest`. -/
theorem trqIDATest_univ {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x : ℕ → ℝⁿ}
    {Δ : ℕ → ℝ} : trqIDATest f univ P ε x Δ = trTest f P ε x Δ := by
  funext k; simp only [trqIDATest, trTest, Set.setOf_add_mem_univ]

/-- **Algorithm 13.1.1** of [cartis2022evaluation] (TRqIDA), as a run predicate. The data are an
objective $f$, the oracle constants $\kappa_{\nabla,i} \ge 0$ (unknown to the method), the
constants of Step 0, tolerances $\epsilon \in (0, 1]^q$ with $\epsilon_{\min} \le \vartheta$,
and a starting point $x_0$. A run consists of sequences of iterates $x_k$, radii $\Delta_k$,
requested accuracies $h_{k,i}$, inexact derivatives $\bar\nabla^i f(x_k)$ that satisfy (13.1.2),
Step-1 displacements $d_{k,j}$, orders $j_k$, steps $s_k$ and flags that mark the
accuracy-improving iterations. Every iteration satisfies Steps 1, 2, 4 and 5 with the ratio
(13.1.16)
$$\rho_k = \frac{f(x_k) - f(x_k + s_k)}{\overline{\Delta T}_{f,j_k}(x_k, s_k)}.$$
The method has no termination rule; its approximate-optimality test is
`CartisGouldToint.Chapter13.trTest`.

**Reading.** After an unsuccessful iteration with $\Delta_{k+1} \ge \vartheta$, Step 4 of the
source returns to Step 2 with $d_{k+1} = d_k$. The run predicate performs Step 1 at every
iteration. Every run of the source is a run of the predicate, because then
$\delta_{k+1} = \delta_k$ and the derivative estimates are unchanged, so the same displacements
are admissible. The analysis therefore covers the algorithm of the source.

The predicate is `Optimization.IsTRqIDARun` with the feasible set $X = \mathbb{R}^n$. One
iteration is `Optimization.TRqDAStep`, the constants are `Optimization.TRqIDAParams`, and the
ratio is `Optimization.trqRatio`. -/
abbrev algorithm_13_1_1 (f : ℝⁿ → ℝ) (κg : ℕ → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ)
    (x₀ : ℝⁿ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) : Prop :=
  IsTRqIDARun f univ κg P ε x₀ x Δ h D dd jk s acc

/-- **Lemma 13.1.1** of [cartis2022evaluation]. Consider sequences that satisfy the iteration rules
of TRqIDA at every iteration $i \le k$, with $\Delta_0$ the initial radius of Step 0. Let
$\mathcal{T}_k$ be the trial iterations and $\mathcal{S}_k$ the successful iterations
($\rho_i \ge \eta_1$) among $0, \dots, k$. If $0 < \Delta_{\min} \le \Delta_{k+1}$, then
$$|\mathcal{T}_k| \le |\mathcal{S}_k| \left(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\right) +
  \frac{|\log(\Delta_{\min} / \Delta_0)|}{|\log \gamma_2|}. \qquad (13.1.22)$$

**Correction.** The source assumes $\Delta_{\min} \le \Delta_k$ and
$\Delta_{\min} \le \Delta_0$. The proof needs the radius after iteration $k$, so the hypothesis
is at $\Delta_{k+1}$; with the bound at $\Delta_k$ the statement is false for $k = 0$. The bound
$\Delta_{\min} \le \Delta_0$ is not needed.

The iteration rules are `Optimization.TRqDAStep` on any feasible set $X$, with any values
$\rho_i$ of the ratio, so the lemma also serves TRqEDA. The proof specializes
`Optimization.trqDA_card_trial_le`. -/
theorem lemma_13_1_1 (hstep : ∀ i ≤ k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i)
    (hΔ0 : Δ 0 = P.Δ₀) {Δmin : ℝ} (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ (k + 1)) :
    ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card *
          (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (Δmin / P.Δ₀)| / |Real.log P.γ₂| :=
  trqDA_card_trial_le hstep hΔ0 hmin hΔmin

/-- **Lemma 13.1.2** of [cartis2022evaluation]. At a trial iteration $k \in \mathcal{T}$ of TRqIDA
(or TRqEDA) with $\Delta_k > 0$, the scaled criticality (13.1.25) satisfies $\hat\phi_{f,k} \ge
\frac12 \varsigma \epsilon_{\min}$, which gives (13.1.26), $\min_{i \in \mathcal{T}_k}
\hat\phi_{f,i} \ge \frac12 \varsigma \epsilon_{\min}$, and
$$\overline{\Delta T}_{f,j_k}(x_k, s_k) \ge \frac{\hat\phi_{f,k} \, \delta_k^{j_k}}{j_k!}.
  \qquad (13.1.27)$$

The hypothesis is one iteration `Optimization.TRqDAStep` on any feasible set, with any value of
the ratio.

**Generalization.** Gives the pointwise form underlying the printed minimum and extends to trial
steps of TRqEDA on any feasible set.
-/
theorem lemma_13_1_2 (hs : TRqDAStep X P ε x Δ h D dd jk s acc ρ k) (hk : ¬ acc k)
    (hΔ : 0 < Δ k) :
    P.ς * epsMin P.q ε / 2 ≤ phiHat (D k) (jk k) (trqDARadius P Δ k) (dd k (jk k)) ∧
      phiHat (D k) (jk k) (trqDARadius P Δ k) (dd k (jk k)) * trqDARadius P Δ k ^ jk k / (jk k)! ≤
        (D k).taylorDecrement (jk k) (s k) :=
  TRqDAStep.trqGap_ge hs hk hΔ

/-- **Lemma 13.1.3** of [cartis2022evaluation]. Assume f.D0qL. Let $k \in \mathcal{T}$ be a trial
iteration of a TRqIDA run with
$$\Delta_k \le \min\left(\vartheta, \frac{1 - \eta_2}{L_f + 4 (q+1)! \kappa_s
  \kappa_{\nabla,\max}} \hat\phi_{f,k}\right). \qquad (13.1.28)$$
Then the iteration is very successful, $\rho_k \ge \eta_2$, and $\Delta_{k+1} \ge \Delta_k$. -/
theorem lemma_13_1_3 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) (hk : ¬ acc k)
    (hΔ : Δ k ≤ min P.ϑ ((1 - P.η₂) /
      (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg) * trPhiHat P Δ D dd jk k)) :
    P.η₂ ≤ trqRatio f D x s jk k ∧ Δ k ≤ Δ (k + 1) :=
  IsTRqIDARun.ratio_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hk hΔ

/-- The constant $\kappa_\Delta$ of (13.1.31) in [cartis2022evaluation]:
$$\kappa_\Delta = \min\left(1, \frac{\gamma_1 (1 - \eta_2)}{L_f + 4 (q+1)! \kappa_s
  \kappa_{\nabla,\max}}\right) \min\left(\vartheta, \frac{\Delta_0 \min_j \delta_0^j}{2 q
  (\max_i \|\nabla^i f(x_0)\| + \kappa_{\nabla,\max} \kappa_h)}\right)$$
with $\delta_0 = \min(\Delta_0, \vartheta)$.

The analysis uses only $0 < \kappa_\Delta \le \min(1, \gamma_1 (1 - \eta_2) / (L_f + 4 (q+1)!
\kappa_s \kappa_{\nabla,\max}))$ (`CartisGouldToint.Chapter13.trKappaDelta_spec`), and the
results are stated for every such $\kappa_\Delta$. A division by zero gives the value $0$.

**Reading.** Reproduces the displayed factors when the denominator is positive and totalizes
division by zero otherwise.
-/
noncomputable def trKappaDelta (f : ℝⁿ → ℝ) (P : TRqIDAParams) (L κg : ℕ → ℝ) (x₀ : ℝⁿ) : ℝ :=
  min 1 (P.γ₁ * (1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)) *
    min P.ϑ (P.Δ₀ * epsMin P.q (fun j => min P.Δ₀ P.ϑ ^ j) /
      (2 * P.q * (ordMax P.q (fun i => ‖iteratedFDeriv ℝ i f x₀‖) + ordMax P.q κg * P.κh)))

/-- Assume f.D0qL and $\kappa_{\nabla,i} \ge 0$ for $i \in [1, q]$, and let $\max_i \|\nabla^i
f(x_0)\| + \kappa_{\nabla,\max} \kappa_h > 0$. Then the constant $\kappa_\Delta$ of (13.1.31)
satisfies $0 < \kappa_\Delta \le 1$ and $\kappa_\Delta \le \gamma_1 (1 - \eta_2) / (L_f + 4
(q+1)! \kappa_s \kappa_{\nabla,\max})$, the properties that Lemma 13.1.4 uses. If the
denominator is zero, the printed formula divides by zero. -/
theorem trKappaDelta_spec {f : ℝⁿ → ℝ} {P : TRqIDAParams} {L κg : ℕ → ℝ} {x₀ : ℝⁿ}
    (hf : AssumptionD0qL f P.q L) (hκg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i)
    (hM : 0 < ordMax P.q (fun i => ‖iteratedFDeriv ℝ i f x₀‖) + ordMax P.q κg * P.κh) :
    0 < trKappaDelta f P L κg x₀ ∧ trKappaDelta f P L κg x₀ ≤ 1 ∧
      trKappaDelta f P L κg x₀ ≤
        P.γ₁ * ((1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)) := by
  have hLf := hf.one_le_lipMax
  have hκm := ordMax_nonneg hκg
  have hC : 0 < lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg := by
    have := P.κs_pos; positivity
  have hδ₀ : 0 < min P.Δ₀ P.ϑ := lt_min P.Δ₀_pos P.ϑ_pos
  have hmin : 0 < epsMin P.q (fun j => min P.Δ₀ P.ϑ ^ j) :=
    Optimization.epsMin_pos P.one_le_q fun j _ => pow_pos hδ₀ j
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.one_le_q
  have hA0 : 0 < min 1 (P.γ₁ * (1 - P.η₂) /
      (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)) :=
    lt_min one_pos (div_pos (mul_pos P.γ₁_pos P.one_sub_η₂_pos) hC)
  have hB0 : 0 < min P.ϑ (P.Δ₀ * epsMin P.q (fun j => min P.Δ₀ P.ϑ ^ j) /
      (2 * P.q * (ordMax P.q (fun i => ‖iteratedFDeriv ℝ i f x₀‖) + ordMax P.q κg * P.κh))) :=
    lt_min P.ϑ_pos (by have := P.Δ₀_pos; positivity)
  have hB1 : min P.ϑ (P.Δ₀ * epsMin P.q (fun j => min P.Δ₀ P.ϑ ^ j) /
      (2 * P.q * (ordMax P.q (fun i => ‖iteratedFDeriv ℝ i f x₀‖) + ordMax P.q κg * P.κh))) ≤ 1 :=
    (min_le_left _ _).trans P.ϑ_le_one
  refine ⟨mul_pos hA0 hB0, ?_, ?_⟩
  · exact (mul_le_of_le_one_left hB0.le (min_le_left _ _)).trans hB1
  · rw [← mul_div_assoc]
    exact (mul_le_of_le_one_right hA0.le hB1).trans (min_le_right _ _)

/-- **Lemma 13.1.4** of [cartis2022evaluation]. Assume f.D0qL, and let $\kappa_\Delta$ satisfy
$0 < \kappa_\Delta \le 1$ and
$$\kappa_\Delta \le \frac{\gamma_1 (1 - \eta_2)}{L_f + 4 (q+1)! \kappa_s
  \kappa_{\nabla,\max}},$$
for example the value (13.1.31). Then every TRqIDA run satisfies, for every $k$,
$$\Delta_k \ge \min\left(\gamma_1 \vartheta, \kappa_\Delta \min_{i \in \mathcal{T}_k}
  \hat\phi_{f,i}\right) \text{ if } \mathcal{T}_k \neq \emptyset, \qquad \Delta_k \ge \gamma_1
  \vartheta \text{ if } \mathcal{T}_k = \emptyset, \qquad (13.1.30)$$
and $\delta_k \ge \varsigma \kappa_\delta \epsilon_{\min}$ (13.1.32) with
$\kappa_\delta = \kappa_\Delta / 2$ (13.1.33).

**Generalization.** The source proves the lemma for the value (13.1.31) of $\kappa_\Delta$. The
lemma holds for every admissible $\kappa_\Delta$, and the value (13.1.31) is admissible when its
denominator is positive (`CartisGouldToint.Chapter13.trKappaDelta_spec`).

Here $\mathcal{T}_k$ is the set of trial iterations among $0, \dots, k$. The proof specializes
the radius bound `Optimization.trqDA_delta_ge`, which holds for every lower bound of
$\{\hat\phi_{f,i} : i \in \mathcal{T}_{k-1}\}$ and so covers both printed cases. -/
theorem lemma_13_1_4 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ} (hκΔ0 : 0 < κΔ)
    (hκΔ1 : κΔ ≤ 1)
    (hκΔ : κΔ ≤ P.γ₁ * ((1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)))
    (k : ℕ) :
    (∀ hne : (successSet (fun i => ¬ acc i) k).Nonempty, min (P.γ₁ * P.ϑ)
        (κΔ * (successSet (fun i => ¬ acc i) k).inf' hne (trPhiHat P Δ D dd jk)) ≤ Δ k) ∧
      (successSet (fun i => ¬ acc i) k = ∅ → P.γ₁ * P.ϑ ≤ Δ k) ∧
      P.ς * (κΔ / 2) * epsMin P.q ε ≤ trqDARadius P Δ k :=
  IsTRqIDARun.delta_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ0 hκΔ1 hκΔ k

/-- **Lemma 13.1.5** of [cartis2022evaluation]. Assume f.D0qL, let $\kappa_\Delta$ be admissible (as
in Lemma 13.1.4) and $\kappa_\delta = \kappa_\Delta / 2$. Every trial iteration
$k \in \mathcal{T}$ of a TRqIDA run satisfies
$$\overline{\Delta T}_{f,j_k}(x_k, s_k) \ge \frac{(\varsigma \kappa_\delta)^{q+1}}{q!}
  \epsilon_{\min}^{q+1}, \qquad (13.1.34)$$
and if moreover $k \in \mathcal{S}$, then
$$f(x_k) - f(x_{k+1}) \ge \eta_1 \frac{(\varsigma \kappa_\delta)^{q+1}}{2 \, q!}
  \epsilon_{\min}^{q+1}. \qquad (13.1.35)$$

**Generalization.** The source states the bounds before reaching approximate optimality and
uses the particular constant from (13.1.33). The trial-iteration conditions suffice for the
bounds with every admissible $\kappa_\Delta$.

The admissibility of $\kappa_\Delta$ is `Optimization.IsTRKappaDelta`. -/
theorem lemma_13_1_5 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) (hk : ¬ acc k) :
    (P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) ≤
        (D k).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ trqRatio f D x s jk k →
        P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
          f (x k) - f (x (k + 1))) :=
  IsTRqIDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ hk

/-- **Lemma 13.1.6** of [cartis2022evaluation]. Assume f.D0qL, let $\kappa_\Delta$ be admissible and
$\kappa_\delta = \kappa_\Delta / 2$, and let $\bar L_f = L_f + \kappa_{\nabla,\max} \kappa_h$ as
in (13.1.24). If Step 1 of TRqIDA branches to Step 2 at iteration $k$ (the test (13.1.14) holds
at some order) and
$$h_{k,i} \le \kappa_s \left(\frac{\varsigma^{q+1} \kappa_\delta^q}{4 q! \bar L_f}\right)^q
  \epsilon_{\min}^{q(q+1)} \quad \text{for all } i \in [1, q], \qquad (13.1.36)$$
then Step 2 does not branch to Step 5, that is, $k \in \mathcal{T}$.

**Reading.** The hypothesis that a Step 1 witness passes (13.1.14) ensures that Step 2 is
performed. Otherwise Step 1 can branch directly to Step 5. Equation (13.1.24) defines
$\bar L_f$ as $L_f + \kappa_{\nabla,\max} \kappa_h$. -/
theorem lemma_13_1_6 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hb : ∃ j ∈ Finset.Icc 1 P.q, trqDAFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤ P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q /
      (4 * P.q ! * (lipMax L P.q + ordMax P.q κg * P.κh))) ^ P.q *
        epsMin P.q ε ^ (P.q * (P.q + 1))) :
    ¬ acc k :=
  IsTRqIDARun.not_acc_of_le hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ hb hh

/-- **Lemma 13.1.7** of [cartis2022evaluation]. Assume f.D0qL, let $\kappa_\Delta$ be admissible and
$\kappa_\delta = \kappa_\Delta / 2$. If Step 1 of TRqIDA branches to Step 5 at iteration $k$
(the test (13.1.14) fails at every order) and
$$\kappa_{\nabla,\max} h_{k,i} \le \frac{\varsigma^{q+1} \kappa_\delta^q}{4 q!}
  \epsilon_{\min}^{q+1} \quad \text{for } i \in [1, q], \qquad (13.1.37)$$
then $\phi^{\delta_k}_{f,j}(x_k) \le \epsilon_j \delta_k^j / j!$ for all $j \in [1, q]$, that
is, $x_k$ passes the test `CartisGouldToint.Chapter13.trTest`.

The condition (13.1.37) is written without a division, so that $\kappa_{\nabla,\max} = 0$ is
allowed.

**Reading.** Writes the threshold as a product so the case of exact oracle constants is included.
-/
theorem lemma_13_1_7 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, ¬ trqDAFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, ordMax P.q κg * h k i ≤
      P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    trTest f P ε x Δ k := by
  have := IsTRqIDARun.trqIDATest_of_pass hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ hpass hh
  rwa [trqIDATest_univ] at this

/-- **Theorem 13.1.8** of [cartis2022evaluation]. Assume f.D0qL and f.Bb with the lower bound
$f_{\rm low}$. Let $\kappa_\Delta$ be admissible (as in Lemma 13.1.4, for example the value
(13.1.31)) and $\kappa_\delta = \kappa_\Delta / 2$. Then every TRqIDA run has a first iteration
$k_\epsilon$ at which $x_\epsilon = x_{k_\epsilon}$ is an
$(\epsilon, \delta_\epsilon)$-approximate $q$-th order minimizer with $\delta_\epsilon =
\min(\Delta_{k_\epsilon}, \vartheta) \in (0, 1]$. Before $k_\epsilon$ the method computes at
most
$$\kappa^A \frac{f(x_0) - f_{\rm low}}{\epsilon_{\min}^{q+1}} + \kappa^B |\log
  \epsilon_{\min}| + \kappa^C \qquad (13.1.38)$$
function values and at most
$$\kappa^A \frac{f(x_0) - f_{\rm low}}{\epsilon_{\min}^{q+1}} + \kappa^E |\log
  \epsilon_{\min}| + \kappa^F + 2 \qquad (13.1.39)$$
derivative estimates, where $\kappa^S = 2 q! / (\eta_1 (\varsigma \kappa_\delta)^{q+1})$,
$\kappa^A = \kappa^S (1 + \log \gamma_3 / |\log \gamma_2|)$, $\kappa^B = 1 / |\log \gamma_2|$,
$\kappa^C = |\log(\varsigma \kappa_\delta / \Delta_0)| / |\log \gamma_2| + 1$,
$\kappa^E = q (q+1) / |\log \gamma_h|$ and $\kappa^F = |\log(\kappa_{\rm acc} / \kappa_h)| /
|\log \gamma_h|$.

**Correction.** The source prints $\kappa^F$ in place of $\kappa^F + 2$ in (13.1.39). Its count
omits the initial derivative estimate and the estimate after the last accuracy-improving
iteration.

**Typo.** The conclusion of the source reads $\phi^\delta_{f,q}$; the intended measure is
$\phi^\delta_{f,j}$ for each $j \in [1, q]$.

The function values are counted as the initial value and one per trial iteration, and the
derivative estimates as the initial estimate and one per successful or accuracy-improving
iteration. The constant $\kappa^S$ is `Optimization.trKappaS`, and $\kappa_{\rm acc}$ is
`Optimization.trKappaAcc` with $\bar L_f = L_f + \kappa_{\nabla,\max} \kappa_h$. For
$\kappa_{\nabla,\max}=0$ it uses just the Step 2 restriction (13.1.36), since (13.1.37) then
holds in its multiplicative form for every requested accuracy. -/
theorem theorem_13_1_8 (hf : AssumptionD0qL f P.q L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) :
    ∃ kε, IsFirstHit (trTest f P ε x Δ) kε ∧ 0 < trqDARadius P Δ kε ∧ trqDARadius P Δ kε ≤ 1 ∧
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
  have := IsTRqIDARun.complexity hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) (fun y _ => hb y) hrun hκΔ
  rwa [trqIDATest_univ] at this

end TRqIDA

/-- Runs of Algorithm 13.1.1 exist. Let the constants of Step 0, tolerances $\epsilon \in (0, 1]^q$
with $\epsilon_{\min} \le \vartheta$, oracle constants $\kappa_{\nabla,i} \ge 0$ and a starting
point $x_0$ be given, and let $O$ be a deterministic oracle that satisfies (13.1.2) at every
point for all positive accuracies. Then there is a TRqIDA run whose derivative estimates are
$O(x_k, h_k)$.

No smoothness of $f$ is assumed. Examples of oracles are the exact derivatives
(`CartisGouldToint.Chapter13.exists_algorithm_13_1_1_exact`) and a finite
derivative-approximation scheme
(`CartisGouldToint.Chapter13.exists_algorithm_13_1_1_of_scheme`). The proof specializes
`Optimization.exists_trqDA_run`. -/
theorem exists_algorithm_13_1_1 {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hϑ : epsMin P.q ε ≤ P.ϑ)
    (hκg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i) (x₀ : ℝⁿ)
    (O : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.q, 0 < h' i) →
      JetApprox (ftaylorSeries ℝ f y) (O y h') P.q (fun i => κg i * h' i)) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc ∧ ∀ k, D k = O (x k) (h k) := by
  obtain ⟨x, Δ, h, dd, jk, s, acc, hx, hΔ, hh, hstep⟩ := exists_trqDA_run f P ε O x₀
  exact ⟨x, Δ, h, _, dd, jk, s, acc, ⟨hε, hϑ, hκg, hx, mem_univ _, hΔ, hh,
    fun k => hO _ _ fun i hi =>
      ((trqDA_invariants (k := k) (fun i _ => hstep i) hΔ hh).2 i hi).1, hstep⟩, fun _ => rfl⟩

/-- TRqIDA runs with exact derivatives exist: under the hypotheses of
`CartisGouldToint.Chapter13.exists_algorithm_13_1_1`, there is a TRqIDA run whose derivative
estimates are the exact derivatives of $f$ at the iterates. The exact derivatives satisfy
(13.1.2) for every accuracy. -/
theorem exists_algorithm_13_1_1_exact {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams}
    {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hϑ : epsMin P.q ε ≤ P.ϑ)
    (hκg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i) (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc ∧
        ∀ k, D k = ftaylorSeries ℝ f (x k) :=
  exists_algorithm_13_1_1 hε hϑ hκg x₀ (fun y _ => ftaylorSeries ℝ f y) fun _ _ hh =>
    (jetApprox_self _ _).mono_err fun i hi => mul_nonneg (hκg i hi) (hh i hi).le


/-! ### ARqpIDA -/

section ARqpIDA

variable {X : Set ℝⁿ} {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ}
  {acc : ℕ → Prop} {ρ : ℕ → ℝ} {L : ℕ → ℝ} {k : ℕ}

/-- **Lemma 13.1.9** of [cartis2022evaluation]. Consider sequences that satisfy the iteration rules
of ARqpIDA at every iteration $i \le k$, with the initial values $\sigma_0$, $\delta_0$ and
$h_0$ of Step 0. If $\sigma_{k+1} \le \sigma_{\max}$, then
$$|\mathcal{T}_k| \le |\mathcal{S}_k| \left(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\right) +
  \frac{\log(\sigma_{\max} / \sigma_0)}{\log \gamma_2}. \qquad (13.1.62)$$

**Correction.** The source assumes $\sigma_k \le \sigma_{\max}$. The proof needs the parameter
after iteration $k$, so the hypothesis is at $\sigma_{k+1}$; with the bound at $\sigma_k$ the
statement is false for $k = 0$.

The iteration rules are `Optimization.ARqpDAStep` on any feasible set, with any values $\rho_i$
of the ratio, so the lemma also serves ARqpEDA. -/
theorem lemma_13_1_9 (hstep : ∀ i ≤ k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀) (hh0 : h 0 = P.h₀) {σmax : ℝ}
    (hσmax : σ (k + 1) ≤ σmax) :
    ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ :=
  arqpDA_card_trial_le hstep hσ0 hδ0 hh0 hσmax

/-- **Lemma 13.1.11** of [cartis2022evaluation]. Suppose that Step 1 of ARqpIDA (or ARqpEDA) is
performed at iteration $k$, with $\|\bar\nabla^i f(x_k)\| \le \bar L$ for $i \in [1, p]$ and
some $\bar L > 0$ (for ARqpIDA, (13.1.63) gives $\bar L$), $\sigma_k \ge 0$, and
$\delta^{(0)}_{k,j} \le 1$ for $j \in [1, q]$. Then for every $j \in [1, q]$
$$\delta^{(0)}_{k,j} \ge \delta^{(1)}_{k,j} \ge \min\left(\frac{\varsigma \epsilon_j}{16
  \max(\bar L, \sigma_k)}, \delta^{(0)}_{k,j}\right). \qquad (13.1.66)$$

The printed lemma also states that the halving loop of Step 1 stops. This existence half is a
property of the algorithm, `Optimization.exists_arqpDA_halving`. The same estimate shows that
the loop stops once the radius is below $\varsigma \epsilon_j / (8 \max(\bar L, \sigma_k))$. The
hypothesis is Step 1 on any feasible set, `Optimization.ARqpStep1`.

**Proof typo.** Equation (13.1.67) identifies the witness decrement with the maximum decrement.
Equation (13.1.52) only bounds the witness below by a fraction of that maximum. The strict
inequality in (13.1.67) follows directly from failure of (13.1.53).

**Generalization.** States the radius bound in the generalized feasible-set setting; halving
existence is separate and the proof only uses the witness inequality in (13.1.67).
-/
theorem lemma_13_1_11 (hs : ARqpStep1 X P ε x σ δ δ₁ D dd k) {Lb : ℝ}
    (hLb : 0 < Lb) (hD : ∀ i ∈ Finset.Icc 1 P.p, ‖D k i‖ ≤ Lb) (hσ : 0 ≤ σ k)
    (hδ1 : ∀ j ∈ Finset.Icc 1 P.q, δ k j ≤ 1) {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    δ₁ k j ≤ δ k j ∧ min (P.ς * ε j / (16 * max Lb (σ k))) (δ k j) ≤ δ₁ k j :=
  ARqpStep1.radius_bounds hs hLb hD hσ hδ1 hj

/-- **Lemma 13.1.13** of [cartis2022evaluation]. At a trial iteration $k \in \mathcal{T}$ of ARqpIDA
(or ARqpEDA) with $\epsilon_j > 0$ for $j \in [1, q]$ and $\sigma_k \ge 0$,
$$\overline{\Delta T}_{f,p}(x_k, s_k) \ge \frac{\sigma_k}{(p+1)!} \|s_k\|^{p+1} \qquad
  (13.1.76)$$
and $\overline{\Delta T}_{f,p}(x_k, s_k) > 0$, so that the ratio (13.1.58) is well defined.

**Reading.** The displayed lower bound and positive ratio denominator hold for the shared trial-step
predicate, including ARqpEDA.
-/
theorem lemma_13_1_13 (hs : ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ k) (hk : ¬ acc k)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, 0 < ε j) (hσ : 0 ≤ σ k) :
    σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) ≤ (D k).taylorDecrement P.p (s k) ∧
      0 < (D k).taylorDecrement P.p (s k) :=
  ARqpDAStep.taylorDecrement_ge hs hk hε hσ

/-- **Lemma 13.1.10** of [cartis2022evaluation]. Assume f.D0pL. Let $\bar\nabla^i f(x)$ be inexact
derivatives at $x$ that satisfy (13.1.2) with $\kappa_{\nabla,i} \ge 0$ and
$0 \le h_i \le \kappa_h$ for $i \in [1, p]$, and let
$\bar L_f = L_f + \kappa_{\nabla,\max} \kappa_h$ (13.1.63). Let $\sigma \ge 0$, let
$$0 < \delta \le \min\left(1, \frac{\alpha}{4 \max(\bar L_f, \sigma)}\right), \qquad (13.1.64)$$
and let $\|d\| \le \delta$ with $\overline{\Delta T}_{f,j}(x, d) \ge \alpha \delta^j / j!$ for
some $j \in [1, p]$. Then the regularized model $\bar m(v) = \overline{T}_{f,p}(x, v) + \sigma
\|v\|^{p+1} / (p+1)!$ satisfies
$$\bar m(0) - \bar m(d) \ge \frac{\alpha}{2} \frac{\delta^j}{j!}. \qquad (13.1.65)$$

**Generalization.** The source restricts $j$ to $[1,q]$, and the estimate holds through degree
$p$. The radius hypothesis (13.1.64) already implies $\alpha > 0$.

**Proof typo.** The first equality in the printed proof has plus signs before the higher-order
Taylor sum and the regularizer. The decrement of `Optimization.regularizedModel` subtracts both
terms from $\overline{\Delta T}_{f,j}(x,d)$. -/
theorem lemma_13_1_10 {f : ℝⁿ → ℝ} {p : ℕ} {L κg hh : ℕ → ℝ} {κh : ℝ} {x : ℝⁿ}
    {D : FormalMultilinearSeries ℝ ℝⁿ ℝ} (hf : AssumptionD0pL f p L)
    (hD : JetApprox (ftaylorSeries ℝ f x) D p (fun i => κg i * hh i))
    (hκg : ∀ i ∈ Finset.Icc 1 p, 0 ≤ κg i) (hh0 : ∀ i ∈ Finset.Icc 1 p, 0 ≤ hh i)
    (hhκ : ∀ i ∈ Finset.Icc 1 p, hh i ≤ κh) {σ α δ : ℝ} (hσ : 0 ≤ σ)
    (hδ : δ ∈ Set.Ioc 0 (min 1 (α / (4 * max (lipMax L p + ordMax p κg * κh) σ))))
    {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {d : ℝⁿ} (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ D.taylorDecrement j d) :
    α / 2 * δ ^ j / j ! ≤ regularizedModel D p σ 0 - regularizedModel D p σ d := by
  set Lb := lipMax L p + ordMax p κg * κh
  have hLb : 0 < Lb := by
    have := hf.one_le_lipMax
    have := ordMax_nonneg hκg
    have h1p : 1 ∈ Finset.Icc 1 p :=
      Finset.mem_Icc.2 ⟨le_rfl, (Finset.mem_Icc.1 hj).1.trans (Finset.mem_Icc.1 hj).2⟩
    have : 0 ≤ κh := (hh0 1 h1p).trans (hhκ 1 h1p)
    positivity
  have hM : 0 < max Lb σ := lt_max_of_lt_left hLb
  obtain ⟨hδ0, hδ1⟩ := hδ
  refine regularizedModel_decrease_ge_of_taylorDecrement_ge (Finset.mem_Icc.1 hj).2 hσ
    (L := Lb) (fun ℓ hℓ => hf.norm_le_of_jetApprox hD hκg hh0 hhκ
      (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hℓ).1; omega, (Finset.mem_Icc.1 hℓ).2⟩))
    hδ0.le (hδ1.trans (min_le_left _ _)) ?_ hd hdec
  have := hδ1.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at this
  linarith

/-- The test of approximate optimality of ARqpIDA, used in Theorem 13.1.19 of
[cartis2022evaluation]: $x_k$ is an $(\epsilon, \delta)$-approximate $q$-th order minimizer
(12.1.25) for some radii $\delta \in (0, 1]^q$.

The method cannot evaluate this test, because it uses the exact derivatives. -/
def arTest (f : ℝⁿ → ℝ) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (k : ℕ) : Prop :=
  ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 P.q, δ' j ∈ Set.Ioc 0 1) ∧
    IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε δ'

/-- The approximate-optimality test `Optimization.arqpIDATest` of the library on the feasible set
$\mathbb{R}^n$ is `CartisGouldToint.Chapter13.arTest`. -/
theorem arqpIDATest_univ {f : ℝⁿ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x : ℕ → ℝⁿ} :
    arqpIDATest f univ P ε x = arTest f P ε x := by
  funext k; simp only [arqpIDATest, arTest, Set.setOf_add_mem_univ]

/-- **Algorithm 13.1.2** of [cartis2022evaluation] (ARqpIDA), as a run predicate. The data are an
objective $f$, the oracle constants $\kappa_{\nabla,i} \ge 0$ (unknown to the method), the
constants of Step 0, tolerances $\epsilon \in (0, 1]^q$ with $\epsilon_j \le \delta_{0,j}$, and
a starting point $x_0$. A run consists of sequences of iterates $x_k$, regularization parameters
$\sigma_k$, radii $\delta^{(0)}_k$, $\delta^{(1)}_k$ and $\delta_{s_k}$, requested accuracies
$h_{k,i}$, inexact derivatives that satisfy (13.1.2) up to the order $p$, Step-1 displacements
$d_{k,j}$, orders $j_k$, steps $s_k$ and flags that mark the accuracy-improving iterations.
Every iteration satisfies Steps 1, 2, 4 and 5 with the ratio (13.1.58)
$$\rho_k = \frac{f(x_k) - f(x_k + s_k)}{\overline{\Delta T}_{f,p}(x_k, s_k)}.$$
The method has no termination rule; its approximate-optimality test is
`CartisGouldToint.Chapter13.arTest`.

**Reading.** Step 0 of the source omits $\varsigma \in (0, 1]$ from its list of constants, but
Step 1 uses it. The constants `Optimization.ARqpIDAParams` include it.

**Correction.** Step 2 of the source checks the accuracy condition (13.1.46) only for
$i \in [1, q]$ and for short steps. The condition (13.1.46), Step 5 and the proofs of Lemmas
13.1.14 and 13.1.16 concern $i \in [1, p]$, which the iteration rules use. The test is skipped
for long steps $\|s_k\| \ge 1$, and Lemma 13.1.14 is corrected accordingly.

The predicate is `Optimization.IsARqpIDARun` with the feasible set $X = \mathbb{R}^n$, and one
iteration is `Optimization.ARqpDAStep`. The radii $\delta^{(0)}_k$, $\delta^{(1)}_k$ and
$\delta_{s_k}$ are `δ k`, `δ₁ k` and `δs k`. -/
abbrev algorithm_13_1_2 (f : ℝⁿ → ℝ) (κg : ℕ → ℝ) (P : ARqpIDAParams) (ε : ℕ → ℝ)
    (x₀ : ℝⁿ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) : Prop :=
  IsARqpIDARun f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc

/-- **Lemma 13.1.12** of [cartis2022evaluation]. Consider an ARqpIDA run under Assumption f.D0pL,
and let $\bar L_f = L_f + \kappa_{\nabla,\max} \kappa_h$. Assume the radii control
(13.1.69)–(13.1.70) at the iterations $i < k$, and let $\bar\sigma$ be a bound with
$\sigma_i \le \bar\sigma$ for $i \le k$. Write $\kappa^{(1)}_\delta(\bar\sigma) = \varsigma
\theta / (24 \max(\bar L_f, \bar\sigma))$. Then:

* if Step 2 is performed at $k$, then $\Delta \bar m_k(s_k) \ge \frac14 \varsigma \epsilon_{j_k}
  (\delta^{(1)}_{k,j_k})^{j_k} / j_k! > 0$ (13.1.74), and hence $s_k \neq 0$;
* $\delta^{(0)}_{k,j} \ge \delta^{(1)}_{k,j} \ge \kappa^{(1)}_\delta(\bar\sigma) \epsilon_j$ for
  $j \in [1, q]$ (13.1.71);
* if Step 2 is performed at $k$ and $h_{k,i} \le \kappa_s (\varsigma
  \kappa^{(1)}_\delta(\bar\sigma)^q / (12 q! \max(\bar L_f, \bar\sigma)))^p
  \epsilon_{\min}^{p(q+1)}$ for $i \in [1, p]$ (13.1.73), then iteration $k$ is not
  accuracy-improving.

**Correction.** The printed conclusion $k \in \mathcal{T}$ under (13.1.73) also requires Step 2
to be performed. For a constant objective with exact estimates, Step 1 satisfies (13.1.53) at
every order and branches to Step 5 even when the requested accuracies are arbitrarily small.

**Generalization.** The lemma holds for every bound $\bar\sigma$, including the source's
$\sigma_{k,\max}$.

Only the radii control at the iterations before $k$ enters the radius bound at $k$. The printed
lemma also states that Step 2 is well defined; this is part of the existence of runs,
`CartisGouldToint.Chapter13.exists_algorithm_13_1_2`. Here
$\Delta \bar m_k(v) = \bar m_k(0) - \bar m_k(v)$ is `Optimization.arModelDec`, and
$\kappa^{(1)}_\delta$ is `Optimization.arKappaDelta1`. -/
theorem lemma_13_1_12 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i < k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {σbar : ℝ} (hσ : ∀ i ≤ k, σ i ≤ σbar) :
    ((∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd k j) →
        0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ∧
        P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ≤ arModelDec P D σ k (s k) ∧
        s k ≠ 0) ∧
      (∀ j ∈ Finset.Icc 1 P.q,
        arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar * ε j ≤ δ₁ k j ∧
          δ₁ k j ≤ δ k j) ∧
      ((∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd k j) →
        (∀ i ∈ Finset.Icc 1 P.p, h k i ≤
          P.κs * (P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar ^ P.q /
            (12 * P.q ! * max (lipMax L P.p + ordMax P.p κg * P.κh) σbar)) ^ P.p *
            epsMin P.q ε ^ (P.p * (P.q + 1))) → ¬ acc k) :=
  IsARqpIDARun.not_acc_of_le hf.lipschitzDerivsAnchored hf.normalized
    (fun _ _ _ => Set.mem_univ _) hrun hrc hσ

/-- **Lemma 13.1.14** of [cartis2022evaluation]. Under Assumption f.D0pL, every ARqpIDA run
satisfies $\sigma_k \le \sigma_{\max}$ for all $k$ (13.1.77), where
$$\sigma_{\max} = \max\left(\sigma_0, \gamma_3 \frac{2 L_{f,p} + 4 (p+1)! \kappa_s'
  \kappa_{\nabla,\max}}{1 - \eta_2}\right), \qquad \kappa_s' = \max(\kappa_s, \kappa_h).$$

**Correction.** The source has $\kappa_s$ in place of $\kappa_s'$. Its proof applies (13.1.47)
also to long steps $\|s_k\| \ge 1$, where the accuracy test (13.1.46) is not performed and only
$h_{k,i} \le \kappa_h$ is known.

The constant $\sigma_{\max}$ is `Optimization.arqpIDASigmaMax`. -/
theorem lemma_13_1_14 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (k : ℕ) :
    σ k ≤ arqpIDASigmaMax P (L P.p) (ordMax P.p κg) :=
  IsARqpIDARun.sigma_le hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun k

/-- **Lemma 13.1.15** of [cartis2022evaluation]. Assume f.D0pL and the radii control at every
iteration before $k$, and let $\sigma_{\max}$ be the bound of Lemma 13.1.14. Suppose that Step 1
of ARqpIDA branches to Step 5 at iteration $k$ (the test (13.1.53) holds at every order) and
$$\kappa_{\nabla,\max} h_{k,i} \le \frac{\varsigma \kappa^{(1)}_\delta(\sigma_{\max})^q}{4 q!}
  \epsilon_{\min}^{q+1} \quad \text{for } i \in [1, p]. \qquad (13.1.78)$$
Then $\delta^{(1)}_k \in (0, 1]^q$ and $x_k$ is an $(\epsilon, \delta^{(1)}_k)$-approximate
$q$-th order minimizer; in particular $x_k$ passes the test `CartisGouldToint.Chapter13.arTest`.

**Reading.** The source writes $\delta_k$ for the radii; they are the radii $\delta^{(1)}_k$ at
the end of Step 1.

Here $\kappa^{(1)}_\delta(\sigma) = \varsigma \theta / (24 \max(\bar L_f, \sigma))$ with
$\bar L_f = L_f + \kappa_{\nabla,\max} \kappa_h$. -/
theorem lemma_13_1_15 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i < k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, ordMax P.p κg * h k i ≤
      P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) ^ P.q / (4 * P.q !) *
        epsMin P.q ε ^ (P.q + 1)) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (δ₁ k) ∧ arTest f P ε x k := by
  have := IsARqpIDARun.arqpIDATest_of_pass hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hrc hpass hh
  rwa [Set.setOf_add_mem_univ, arqpIDATest_univ] at this

/-- **Lemma 13.1.16** of [cartis2022evaluation]. Assume f.D0pL. Let iteration $k$ of an ARqpIDA run
be successful with $\|s_k\| < 1$, and let $x_{k+1}$ not be an
$(\epsilon, \delta_{k+1})$-approximate $q$-th order minimizer for the radii
$\delta_{k+1} = \delta^{(0)}_{k+1}$, which equal $\delta_{s_k}$. Then for some $j \in [1, q]$
$$(1 - \theta) \epsilon_j \frac{\delta_{k+1,j}^j}{j!} \le (L_{f,p} + \sigma_{\max} + 3
  \kappa_{\nabla,\max} \kappa_s) \sum_{\ell=1}^j \frac{\delta_{k+1,j}^\ell}{\ell!}
  \|s_k\|^{p-\ell+1}, \qquad (13.1.79)$$
with $\sigma_{\max}$ of Lemma 13.1.14. -/
theorem lemma_13_1_16 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hs1 : ‖s k‖ < 1)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, (1 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arqpIDASigmaMax P (L P.p) (ordMax P.p κg) + 3 * ordMax P.p κg * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) :=
  IsARqpIDARun.measure_ineq hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hk hρ hs1 (by rwa [Set.setOf_add_mem_univ])

/-- **Lemma 13.1.17** of [cartis2022evaluation]. Assume f.D0pL and the radii control at iteration
$k$. Let iteration $k$ of an ARqpIDA run be successful, and let $x_{k+1}$ not be an
$(\epsilon, \delta_{k+1})$-approximate $q$-th order minimizer. Write $A = L_{f,p} +
\sigma_{\max} + 3 \kappa_{\nabla,\max} \kappa_s$, $\kappa_{\delta,\min} = \varsigma \theta / (24
\max(\bar L_f, \sigma_{\max}))$ (13.1.81) and $\hat\kappa = \min(\kappa_{\delta,\min}, (1 -
\theta) / (2 q! A))$. Then for some $j \in [1, q]$ (13.1.80):

* if $q \le 2$, then $\|s_k\| \ge \left(\frac{1 - \theta}{2 j! A}\right)^{1/(p-j+1)}
  \epsilon_j^{1/(p-j+1)}$;
* if $q > 2$, then $\|s_k\| \ge \left(\frac{(1 - \theta) \hat\kappa^{j-1}}{2 j! A}\right)^{1/p}
  \epsilon_j^{j/p}$.

**Correction.** For $q > 2$ the source has $\kappa_{\delta,\min}$ in place of $\hat\kappa$. Its
argument, that of Lemma 12.2.12, needs $\kappa_{\delta,\min} \le (1 - \theta) / (2 j! A)$: the
source derives the second case from the first, and this needs $\kappa_{\delta,\min}$ below that
bound.

The constants are `Optimization.arConstA` and `Optimization.arKappaHat`. -/
theorem lemma_13_1_17 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (δ (k + 1))) :
    (P.q ≤ 2 → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) *
        ε j ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) ≤ ‖s k‖) ∧
    (2 < P.q → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
          (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) /
          (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / (P.p : ℝ)) *
        ε j ^ ((j : ℝ) / P.p) ≤ ‖s k‖) := by
  have h := IsARqpIDARun.norm_step_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hrc hk hρ
    (by rwa [Set.setOf_add_mem_univ])
  exact ⟨h.1, fun hq => h.2 (not_le.2 hq)⟩

/-- **Lemma 13.1.18** of [cartis2022evaluation]. Assume f.D0pL and the radii control at iteration
$k$. Let iteration $k$ of an ARqpIDA run be successful, and let $x_{k+1}$ not be approximately
optimal for any radii in $(0, 1]^q$. Then
$$\overline{\Delta T}_{f,p}(x_k, s_k) \ge \kappa_{\Delta m} \min_{j \in [1, q]}
  \epsilon_j^{\pi_j} \qquad (13.1.82)$$
and
$$f(x_k) - f(x_{k+1}) \ge \tfrac12 \eta_1 \kappa_{\Delta m} \min_{j \in [1, q]}
  \epsilon_j^{\pi_j}, \qquad (13.1.83)$$
where $\pi_j = (p+1)/(p-j+1)$ if $q \le 2$ and $\pi_j = j (p+1)/p$ if $q > 2$, and
$$\kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!} \left(\frac{1 - \theta}{2 q!
  A}\right)^{(p+1)/(p-q+1)} \text{ if } q \le 2, \qquad \kappa_{\Delta m} =
  \frac{\sigma_{\min}}{(p+1)!} \left(\frac{(1 - \theta) \hat\kappa^{q-1}}{2 q!
  A}\right)^{q(p+1)/p} \text{ if } q > 2,$$
with $A$ and $\hat\kappa$ as in Lemma 13.1.17.

**Correction.** The source states (13.1.82) for every trial iteration before approximate
optimality. Its proof, through Lemma 13.1.17, covers only the successful iterations $k$ for
which $x_{k+1}$ is not approximately optimal; this is the case that the complexity argument
uses. For $q > 2$ the constant has $\hat\kappa$ in place of $\kappa_{\delta,\min}$, as in Lemma
13.1.17.

The exponents are `Optimization.arPi`, and the constant $\kappa_{\Delta m}$ is
$\sigma_{\min}/(p+1)!$ times `Optimization.arStepConst`. -/
theorem lemma_13_1_18 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arTest f P ε x (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) *
        epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
          (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ f (x k) - f (x (k + 1)) :=
  IsARqpIDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hrc hk hρ (by rwa [arqpIDATest_univ])

/-- The counting argument of **Theorem 13.1.19** of [cartis2022evaluation], for any decrease
constant. Assume f.D0pL, f.Bb with the lower bound $f_{\rm low}$, and the radii control at every
iteration of an ARqpIDA run. Suppose that every successful iteration $k$ whose successor
$x_{k+1}$ is not approximately optimal decreases $f$ by at least $c > 0$. Then there is a first
iterate $x_{k_\epsilon}$ that is approximately optimal for some radii in $(0, 1]^q$, and before
it the method computes at most
$$\left(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\right) \frac{f(x_0) - f_{\rm low}}{c} +
  \frac{\log(\sigma_{\max} / \sigma_0)}{\log \gamma_2} + 2 + \frac{|\log \gamma_1|}{\log
  \gamma_2}$$
function values and at most
$$\frac{f(x_0) - f_{\rm low}}{c} + \frac{p (q+1)}{|\log \gamma_h|} |\log \epsilon_{\min}| +
  \frac{|\log(\kappa_{\rm acc} / \kappa_h)|}{|\log \gamma_h|} + 3$$
derivative estimates.

The constant $\kappa_{\rm acc}$ is `Optimization.arKappaAcc` with
$\kappa = \kappa^{(1)}_\delta(\sigma_{\max})$.

**Correction.** Generalizes to arbitrary uniform successful-step decrease with the corrected
first-hit test and counts.
-/
theorem arqpIDA_complexity (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {c : ℝ} (hc : 0 < c)
    (hdec : ∀ k, ¬ acc k → P.η₁ ≤ arqpIDARatio f P D x s k → ¬ arTest f P ε x (k + 1) →
      c ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (arTest f P ε x) kε ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) / c) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) / c + P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have := IsARqpIDARun.complexity hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) (fun y _ => hb y) hrun hrc hc
    fun k hk hρ hnot => hdec k hk hρ (by rwa [arqpIDATest_univ] at hnot)
  rwa [arqpIDATest_univ] at this

/-- **Theorem 13.1.19** of [cartis2022evaluation], case $q \le 2$. Assume f.D0pL, f.Bb with the
lower bound $f_{\rm low}$, the radii control (13.1.69)–(13.1.70) at every iteration, and
$q \le 2$. Then every ARqpIDA run has a first iterate $x_{k_\epsilon}$ that is an
$(\epsilon, \delta_\epsilon)$-approximate $q$-th order minimizer for some radii
$\delta_\epsilon \in (0, 1]^q$. This iterate satisfies $\phi^1_{f,j}(x_{k_\epsilon}) \le
\epsilon_j / j!$ for $j \in [1, q]$. Before $k_\epsilon$ the method computes at most
$$\kappa^A \frac{f(x_0) - f_{\rm low}}{\min_j \epsilon_j^{(p+1)/(p-j+1)}} + \kappa^C \qquad
  (13.1.84)$$
function values and at most
$$\kappa^S \frac{f(x_0) - f_{\rm low}}{\min_j \epsilon_j^{(p+1)/(p-j+1)}} + \kappa^E |\log
  \epsilon_{\min}| + \kappa^F + 3 \qquad (13.1.85)$$
derivative estimates. Here $\kappa_{\Delta m} = \sigma_{\min} / (p+1)! \cdot ((1 - \theta)/(2 q!
A))^{(p+1)/(p-q+1)}$ with $A = L_{f,p} + \sigma_{\max} + 3 \kappa_{\nabla,\max} \kappa_s$,
$\kappa^S = 2 / (\eta_1 \kappa_{\Delta m})$, $\kappa^A = \kappa^S (1 + |\log \gamma_1| / \log
\gamma_2)$, $\kappa^C = \log(\sigma_{\max} / \sigma_0) / \log \gamma_2 + 2 + |\log \gamma_1| /
\log \gamma_2$, $\kappa^E = p (q+1) / |\log \gamma_h|$ and $\kappa^F = |\log(\kappa_{\rm acc} /
\kappa_h)| / |\log \gamma_h|$.

**Correction.** The source defines $k_\epsilon$ by approximate optimality with the radius one.
The proof certifies only the radii of the algorithm at the end of Step 1, which can be smaller
than one: it conflates $\delta^{(0)}_k$ and $\delta^{(1)}_k$. Here $k_\epsilon$ is the first
index with some radii in $(0, 1]^q$, and the radius one follows for $q \le 2$
(`Optimization.isEpsDeltaApprox_one_of_le_two`). The constant $\kappa^C$ of the source misses
the factor $1 + |\log \gamma_1| / \log \gamma_2$ on the term $1$ from
$|\mathcal{S}_k| \le |\mathcal{S}_{k-1}| + 1$. The derivative count includes the initial
estimate, this term $1$, and the last accuracy-improving iteration, so the constant is
$\kappa^F + 3$.

**Reading.** For $\kappa_h = 0$, which (13.1.51) allows, no iteration before $k_\epsilon$ is
accuracy-improving, and $\kappa^F$ is read with $\log 0 = 0$.

The proof applies `CartisGouldToint.Chapter13.arqpIDA_complexity` with the decrease of Lemma
13.1.18. -/
theorem theorem_13_1_19_i (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hq2 : P.q ≤ 2) :
    ∃ kε, IsFirstHit (arTest f P ε x) kε ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (fun _ => 1) ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)))) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) +
        (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
          |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)))) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) +
        P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  set κΔm := P.σmin / ((P.p + 1)! : ℝ) *
    ((1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
      (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)) with hκΔm
  set m := epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2, ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2, ↓reduceIte]; exact hκΔm.symm
  have hA := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hκpos : 0 < κΔm := by
    have := P.σmin_pos; have := P.θ_lt_one
    have : 0 < (1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg)) := by
      apply div_pos (by linarith) (by positivity)
    positivity
  have hmpos : 0 < m := Optimization.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := arqpIDA_complexity hf hb hrun hrc hc fun k hk hρ hnot => by
    have := (lemma_13_1_18 hf hrun (hrc k) hk hρ hnot).2
    rwa [hm', hκ'] at this
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = 2 / (P.η₁ * κΔm) * (f x₀ - flow) / m := by
    have := P.η₁_pos; field_simp
  obtain ⟨δ', hδ', hap⟩ := hk.test
  exact ⟨kε, hk, isEpsDeltaApprox_one_of_le_two hq2 hδ' hap,
    h1.trans (le_of_eq (by rw [hdiv]; ring)),
    h2.trans (le_of_eq (by rw [hdiv]))⟩

/-- **Theorem 13.1.19** of [cartis2022evaluation], case $q > 2$. Under the hypotheses of
`CartisGouldToint.Chapter13.theorem_13_1_19_i` with $q > 2$ in place of $q \le 2$, every ARqpIDA
run has a first iterate $x_{k_\epsilon}$ that is approximately optimal for some radii in
$(0, 1]^q$, and the bounds (13.1.86)–(13.1.87) hold: they are the bounds of the case $q \le 2$
with the exponents $\pi_j = j (p+1)/p$ in place of $(p+1)/(p-j+1)$ and with
$$\kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!} \left(\frac{(1 - \theta) \hat\kappa^{q-1}}{2
  q! A}\right)^{q(p+1)/p},$$
where $\hat\kappa$ is the constant of Lemma 13.1.17.

**Correction.** The constant $\kappa^{s,2}$ of the source prints the exponent $(p+1)/(p-j+1)$
and $\kappa_{\delta,\min}^{j-1}$; the proof gives the exponents of Lemma 13.1.18 and
$\hat\kappa$. The corrections of `CartisGouldToint.Chapter13.theorem_13_1_19_i` to the first
index, to $\kappa^C$ and to the derivative count also apply. -/
theorem theorem_13_1_19_ii (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hq2 : 2 < P.q) :
    ∃ kε, IsFirstHit (arTest f P ε x) kε ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
              (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
                (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
              (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
        (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
          |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
              (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
                (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
              (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
        P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hq2' : ¬ P.q ≤ 2 := not_le.2 hq2
  set κΔm := P.σmin / ((P.p + 1)! : ℝ) *
    ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
      (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
      (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p)
    with hκΔm
  set m := epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2', ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2', ↓reduceIte]; exact hκΔm.symm
  have hLb := hrun.one_le_Lbar hf.normalized
  have hA := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hκpos : 0 < κΔm := by
    have := P.σmin_pos; have := P.θ_lt_one
    have h0 : 0 < arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) :=
      lt_min (arKappaDelta1_pos (by linarith)) (div_pos (by linarith) (by positivity))
    have : 0 < (1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
        (2 * P.q ! * arConstA P L (ordMax P.p κg)) :=
      div_pos (mul_pos (by linarith) (pow_pos h0 _)) (by positivity)
    positivity
  have hmpos : 0 < m := Optimization.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := arqpIDA_complexity hf hb hrun hrc hc fun k hk hρ hnot => by
    have := (lemma_13_1_18 hf hrun (hrc k) hk hρ hnot).2
    rwa [hm', hκ'] at this
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = 2 / (P.η₁ * κΔm) * (f x₀ - flow) / m := by
    have := P.η₁_pos; field_simp
  exact ⟨kε, hk, h1.trans (le_of_eq (by rw [hdiv]; ring)),
    h2.trans (le_of_eq (by rw [hdiv]))⟩

end ARqpIDA

section ARExistence

variable {P : ARqpIDAParams} {ε : ℕ → ℝ} (O : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ)

/-- Runs of **Algorithm 13.1.2** exist; this is the existence part of Lemmas 13.1.11 and 13.1.12 of
[cartis2022evaluation]. Assume f.D0pL. Let the constants of Step 0 with positive initial
accuracies $h_{0,i} > 0$, tolerances $\epsilon \in (0, 1]^q$ with $\epsilon_j \le \delta_{0,j}$,
oracle constants $\kappa_{\nabla,i} \ge 0$ and a starting point $x_0$ be given, and let $O$ be a
deterministic oracle that satisfies (13.1.2) at every point for all accuracies
$h \in (0, \kappa_h]^p$. Then there is an ARqpIDA run whose derivative estimates are
$O(x_k, h_k)$ and which satisfies the radii control (13.1.69)–(13.1.70) at every iteration.

In the construction, Step 2 uses a global minimizer of the model (Lemma 12.2.9). The proof
specializes `Optimization.exists_arqpDA_steps`.

**Reading.** Packages halving and step existence for a uniform oracle with positive initial requests
and weaker radii control.
-/
theorem exists_algorithm_13_1_2 {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {L : ℕ → ℝ}
    (hf : AssumptionD0pL f P.p L) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j) (hκg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i)
    (hh₀ : ∀ i ∈ Finset.Icc 1 P.p, 0 < P.h₀ i) (x₀ : ℝⁿ)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      JetApprox (ftaylorSeries ℝ f y) (O y h') P.p (fun i => κg i * h' i)) :
    ∃ (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc ∧
        (∀ k, D k = O (x k) (h k)) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k := by
  obtain ⟨x, σ, δ, δ₁, δs, h, dd, jk, s, acc, hx0, hσ0, hδ0, hh0, hhm, hstep, hrc⟩ :=
    exists_arqpDA_steps O hf.lipschitzDerivsAnchored hf.normalized hε hκg x₀ P.σmin_le_σ₀
        (fun j hj => P.δ₀_mem j hj)
      (fun i hi => ⟨hh₀ i hi, P.h₀_le i hi⟩) hO
  exact ⟨x, σ, δ, δ₁, δs, h, fun i => O (x i) (h i), dd, jk, s, acc,
    ⟨hε, hεδ, hκg, hx0, mem_univ _, hσ0, hδ0, hh0, fun k => hO _ _ (hhm k), hstep⟩,
    fun _ => rfl, hrc⟩

/-- ARqpIDA runs with exact derivatives and the radii control exist: under the hypotheses of
`CartisGouldToint.Chapter13.exists_algorithm_13_1_2`, there is an ARqpIDA run whose derivative
estimates are the exact derivatives of $f$ at the iterates and which satisfies the radii control
at every iteration.

**Reading.** Exact derivatives instantiate the relational run with the revised rules and weaker
radii condition.
-/
theorem exists_algorithm_13_1_2_exact {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {L : ℕ → ℝ}
    (hf : AssumptionD0pL f P.p L) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j) (hκg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i)
    (hh₀ : ∀ i ∈ Finset.Icc 1 P.p, 0 < P.h₀ i) (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc ∧
        (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k :=
  exists_algorithm_13_1_2 (fun y _ => ftaylorSeries ℝ f y) hf hε hεδ hκg hh₀ x₀ fun _ _ hh =>
    (jetApprox_self _ _).mono_err fun i hi => mul_nonneg (hκg i hi) (hh i hi).1.le

end ARExistence

end CartisGouldToint.Chapter13
