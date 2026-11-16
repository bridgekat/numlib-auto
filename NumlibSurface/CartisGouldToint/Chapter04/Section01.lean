/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Optimization.Complexity.SlowExample.ARp
import Numlib.Optimization.ModelBased.ARpRun
import NumlibSurface.CartisGouldToint.Chapter03.Section03

/-!
# Cartis, Gould and Toint, Section 4.1: The ARp algorithm and its complexity

This module formalizes §4.1 of [cartis2022evaluation]: the adaptive-regularization algorithm ARp,
which minimizes a smooth function $f : \mathbb{R}^n \to \mathbb{R}$ with Taylor models of order $p$,
and its evaluation complexity. At the iterate $x_k$ the model (4.1.2) is
$$m_k(s) = T_{f,p}(x_k, s) + \frac{\sigma_k}{(p+1)!} \|s\|^{p+1},$$
where $T_{f,p}(x_k, s)$ is the Taylor polynomial of degree $p$ of $f$ at $x_k$ and $\sigma_k > 0$ is
the regularization weight. The step $s_k$ approximately minimizes $m_k$, and the ratio $\rho_k$ of
(4.1.15), the achieved decrease of $f$ over the decrease of $T_{f,p}$, decides whether $x_k + s_k$
is accepted. ARp seeks an approximate minimizer of order $q = 1$, $2$ or $3$, according to how many
of the tolerances $\varepsilon_1, \varepsilon_2, \varepsilon_3$ are finite.

Under the assumptions f.Bb and f.DpL, ARp needs $O(\varepsilon^{-(p+1)/(p-q+1)})$ evaluations of $f$
and its derivatives to find such a point (Theorem 4.1.5), and this order is sharp (Theorem 4.1.6).
The proofs specialize the backbone run predicate `Optimization.IsARpRun` and the slow examples of
`Numlib.Optimization.Complexity.SlowExample.ARp`.

## Main definitions

* (4.1.3)–(4.1.4), `CartisGouldToint.Chapter04.IsApproxThirdOrderMinimizer`: an approximate
  second-order minimizer at which $|\nabla^3 f(x)[d]^3| \le \varepsilon_3$ for every unit direction
  $d$ of curvature at most $\varepsilon_2$ in absolute value.
* Algorithm 4.1.1, Step 0, `CartisGouldToint.Chapter04.ARpParams`: the constants of ARp.
* Algorithm 4.1.1, Step 1, `CartisGouldToint.Chapter04.arpStopTest`: the termination test
  (4.1.5)–(4.1.9).
* (4.1.14), `CartisGouldToint.Chapter04.arpCurvSet`: the sets $\mathcal{M}_k$ of directions of small
  model curvature along a run.
* Algorithm 4.1.1, `CartisGouldToint.Chapter04.algorithm_4_1_1`: ARp as a predicate on sequences of
  iterates, steps and weights.
* Assumption f.DpL, (4.1.17), `CartisGouldToint.Chapter04.AssumptionDpL`: $f$ is $C^p$ and
  $\nabla^p f$ is Lipschitz continuous with a constant $L_{f,p} \ge 1$.
* (4.1.19), `CartisGouldToint.Chapter04.sigmaMaxARp`: the bound $\sigma_{\max}$ on the
  regularization weights.
* (4.1.23), `CartisGouldToint.Chapter04.kappaS2ARp`: the constant $\kappa_{s2}$.
* (4.1.32), (4.1.34), (4.1.36), `CartisGouldToint.Chapter04.kappaARp₁`,
  `CartisGouldToint.Chapter04.kappaARp₂`, `CartisGouldToint.Chapter04.kappaARp₃`: the constants
  $\kappa_1, \kappa_2, \kappa_3$ of the decrease bounds.
* (4.1.45), (4.1.46), `CartisGouldToint.Chapter04.kappaSARp`,
  `CartisGouldToint.Chapter04.kappaCARp`: the constants $\kappa^S$ and $\kappa^C$ of the complexity
  bound.

## Main results

* Algorithm 4.1.1, `CartisGouldToint.Chapter04.exists_algorithm_4_1_1`: for
  $\varepsilon_3 = +\infty$, a run exists from every starting point.
* Algorithm 4.1.1, `CartisGouldToint.Chapter04.not_exists_algorithm_4_1_1_third_order`: for
  $\varepsilon_3 < \infty$, a run need not exist.
* Lemma 4.1.1, `CartisGouldToint.Chapter04.lemma_4_1_1`: a step that does not increase the model
  decreases the Taylor polynomial by at least $\sigma \|s\|^{p+1}/(p+1)!$.
* Lemma 4.1.2, `CartisGouldToint.Chapter04.lemma_4_1_2`: the weights satisfy
  $\sigma_k \le \sigma_{\max}$.
* Lemma 4.1.3, (4.1.20), `CartisGouldToint.Chapter04.lemma_4_1_3_i`: on a successful iteration,
  $\|s_k\|^p$ is bounded below by a multiple of $\|\nabla f(x_{k+1})\|$.
* Lemma 4.1.3, (4.1.21), `CartisGouldToint.Chapter04.lemma_4_1_3_ii`: $\|s_k\|^{p-1}$ is bounded
  below by a multiple of the negative curvature at $x_{k+1}$.
* Lemma 4.1.3, (4.1.22), `CartisGouldToint.Chapter04.lemma_4_1_3_iii`: $\|s_k\|^{p-2}$ is bounded
  below by a multiple of $|\nabla^3 f(x_{k+1})[d]^3|$ for $d \in \mathcal{M}_{k+1}$.
* Lemma 4.1.3, (4.1.23), `CartisGouldToint.Chapter04.lemma_4_1_3_iv`: the curvature of $f$ at
  $x_{k+1}$ along $d \in \mathcal{M}_{k+1}$ is at most $\|s_k\|^{p-1}/\kappa_{s2}$.
* Lemma 4.1.4, (4.1.31) and (4.1.37), `CartisGouldToint.Chapter04.lemma_4_1_4_i`: on a successful
  iteration, $f$ decreases by at least $\kappa_1 \|\nabla f(x_{k+1})\|^{(p+1)/p}$.
* Lemma 4.1.4, (4.1.33), `CartisGouldToint.Chapter04.lemma_4_1_4_ii`: the decrease is at least
  $\kappa_2$ times a power of the negative curvature at $x_{k+1}$.
* Lemma 4.1.4, (4.1.35), `CartisGouldToint.Chapter04.lemma_4_1_4_iii`: the decrease is at least
  $\kappa_3 |\nabla^3 f(x_{k+1})[d]^3|^{(p+1)/(p-2)}$ for $d \in \mathcal{M}_{k+1}$.
* Theorem 4.1.5, `CartisGouldToint.Chapter04.theorem_4_1_5_i`,
  `CartisGouldToint.Chapter04.theorem_4_1_5_ii`, `CartisGouldToint.Chapter04.theorem_4_1_5_iii`: the
  evaluation complexity of ARp for the orders $q = 1, 2, 3$.
* Theorem 4.1.6, `CartisGouldToint.Chapter04.theorem_4_1_6_i`,
  `CartisGouldToint.Chapter04.theorem_4_1_6_ii`, `CartisGouldToint.Chapter04.theorem_4_1_6_iii`: the
  bounds of Theorem 4.1.5 are attained on functions of one variable.

## Proof outline

On a successful iteration, Lemma 4.1.4 bounds the decrease of $f$ from below by a power of the
criticality measure at the next iterate. Before termination one of the measures exceeds its
tolerance, so each successful iteration decreases $f$ by a fixed amount, and f.Bb bounds the number
of successful iterations. Lemma 4.1.2 bounds the weights, and this bounds the number of unsuccessful
iterations in terms of the successful ones.

## Conventions

* The tolerances $\varepsilon_2, \varepsilon_3 \in (0, +\infty]$ are `Option ℝ`, with `none` for
  $+\infty$. A finite $\varepsilon_3$ requires a finite $\varepsilon_2$. The order $q$ sought is
  `CartisGouldToint.Chapter04.arpOrder ε₂ ε₃`.
* A run consists of sequences `x s : ℕ → EuclideanSpace ℝ (Fin n)` and `σ : ℕ → ℝ`. Iteration $k$ is
  successful if $\rho_k \ge \eta_1$, that is, `P.η₁ ≤ Optimization.taylorRatio f p x s k`.
* The examples of Theorem 4.1.6 live on $\mathbb{R}^1$ = `EuclideanSpace ℝ (Fin 1)`. They are ridge
  functions $x \mapsto G(\langle e_0, x\rangle)$, which are `Optimization.ridge G
  CartisGouldToint.Chapter02.e₀`.

## Implementation notes

* The model (4.1.2) is `Optimization.regularizedModel (ftaylorSeries ℝ f x_k) p σ_k`, and the ratio
  (4.1.15) is `Optimization.taylorRatio`. ARp is the backbone run predicate `Optimization.IsARpRun`,
  an instance of the generic adaptive-regularization run `Optimization.IsARRun`.
* The sets $\mathcal{M}_k$ of Step 0 and (4.1.14) depend on the run; they are the function
  `CartisGouldToint.Chapter04.arpCurvSet` of the sequences.
* The tensor norm of f.DpL is the operator norm of multilinear maps.
* The examples of Theorem 4.1.6 use the one-dimensional data of Theorem 12.2.15
  (`Optimization.exists_slowTaylorOrder_interpolant`). Their iterations are exact global
  minimizations of the model with $\sigma_k = \sigma_0$ and $\rho_k = 1$, and the run mechanism is
  `Optimization.arp_ridge_run`.

## Deviations from the source

* **Step 1, (4.1.8)–(4.1.9)** (correction). The source also requires $\mathcal{M}_k \neq \emptyset$,
  and with it a run can get stuck. The condition is read as "for all $d \in \mathcal{M}_k$", as in
  the proof of Theorem 4.1.5, and so is (4.1.13). See `CartisGouldToint.Chapter04.arpStopTest` and
  `CartisGouldToint.Chapter04.algorithm_4_1_1`.
* **Algorithm 4.1.1 with $\varepsilon_3 < \infty$** (correction). The source takes for granted that
  a step satisfying Step 2 exists; it need not, and Theorem 4.1.5 in the third-order case is a
  statement about runs. See `CartisGouldToint.Chapter04.not_exists_algorithm_4_1_1_third_order`.
* **Theorem 4.1.5** (reading). The source states one theorem with one constant $\kappa^S$ that mixes
  the three orders. It is split by the order of criticality, each part with the constants of the
  active orders only. See `CartisGouldToint.Chapter04.theorem_4_1_5_i`.
* **Theorem 4.1.5** (generalization). The hypothesis $(\varepsilon_1, \varepsilon_2, \varepsilon_3)
  \in (0, 1]^3$ is weakened to positive tolerances. See
  `CartisGouldToint.Chapter04.theorem_4_1_5_i`.
* **Theorem 4.1.6, third-order case** (correction). The proof that the source defers to §12.2.2.4
  has the wrong sign of $\lambda_{\min}$. The case is proved for
  $\sigma_0 \le (p-2)! \min(\theta_2, \theta_3)$. See
  `CartisGouldToint.Chapter04.theorem_4_1_6_iii`.

## Not formalized

* §4.1.3 ("A TRp algorithm?"). It contains no numbered statement and defines no algorithm.
-/

open Set Finset Optimization
open Optimization hiding ARParams ARpParams
open scoped Nat RealInnerProductSpace

namespace CartisGouldToint.Chapter04

variable {n : ℕ}

/-! ### The algorithm -/

/-- **Algorithm 4.1.1** of [cartis2022evaluation], Step 0: the constants of ARp. They are an initial
regularization weight $\sigma_0 > 0$, a lower bound $\sigma_{\min} \in (0, \sigma_0]$ on the
weights, acceptance thresholds $0 < \eta_1 \le \eta_2 < 1$, update factors
$0 < \gamma_1 < 1 < \gamma_2 < \gamma_3$, and step-termination constants
$\theta_1, \theta_2, \theta_3 \in (0, 1]$.

The structure extends `Optimization.ARpParams`, which allows $\sigma_{\min} = 0$ and
$\gamma_2 = \gamma_3$, by the two conditions $\sigma_{\min} > 0$ and $\gamma_2 < \gamma_3$. -/
structure ARpParams extends Optimization.ARpParams where
  /-- The lower bound $\sigma_{\min}$ on the weights is positive. -/
  σmin_pos : 0 < σmin
  /-- The update factors satisfy $\gamma_2 < \gamma_3$. -/
  γ₂_lt_γ₃ : γ₂ < γ₃

/-- The constants of ARp, viewed as the constants (2.4.2) of the algorithm AR1 of Chapter 2. -/
def ARpParams.toAR1Params (P : ARpParams) : Chapter02.ARParams where
  toARParams := P.toARParams
  σmin_pos := P.σmin_pos
  γ₂_lt_γ₃ := P.γ₂_lt_γ₃

/-- **Assumption f.DpL** of [cartis2022evaluation], (4.1.17). Let $f : \mathbb{R}^n \to \mathbb{R}$,
$p \in \mathbb{N}$ and $L \in \mathbb{R}$. The function $f$ satisfies f.DpL with constant
$L_{f,p} = L$ if $f$ is $p$ times continuously differentiable on $\mathbb{R}^n$, $L \ge 1$, and
$$\|\nabla^p f(x) - \nabla^p f(y)\| \le L \|x - y\| \quad \text{for all } x, y \in
  \mathbb{R}^n.$$

The tensor norm is the operator norm of multilinear maps. The definition is the anchored
smoothness assumption `LipschitzDerivsAnchored f univ univ p p (fun _ => L)` on the whole space,
together with $1 \le L$. The form (4.1.17) is
`CartisGouldToint.Chapter04.AssumptionDpL.lipschitz` and
`CartisGouldToint.Chapter04.AssumptionDpL.of_lipschitz`. For $p = 1$ the assumption is f.gL, and
for $p = 2$ it is f.HL (`CartisGouldToint.Chapter04.assumptionDpL_one_iff`,
`CartisGouldToint.Chapter04.assumptionDpL_two_iff`). -/
abbrev AssumptionDpL (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (L : ℝ) : Prop :=
  LipschitzDerivsAnchored f univ univ p p (fun _ => L) ∧ 1 ≤ L

namespace AssumptionDpL

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {L : ℝ}

/-- Under f.DpL, $f$ is $p$ times continuously differentiable. -/
theorem contDiff (h : AssumptionDpL f p L) : ContDiff ℝ p f :=
  h.1.contDiff

/-- The constant of f.DpL satisfies $L_{f,p} \ge 1$. -/
theorem one_le (h : AssumptionDpL f p L) : 1 ≤ L :=
  h.2

/-- The constant of f.DpL is nonnegative. -/
theorem nonneg (h : AssumptionDpL f p L) : 0 ≤ L :=
  zero_le_one.trans h.one_le

/-- Under f.DpL, the $p$-th derivative of $f$ is $L$-Lipschitz on $\mathbb{R}^n$ in the sense of the
backbone predicate `IteratedFDerivLipschitzOn`. -/
theorem iteratedFDerivLipschitzOn (h : AssumptionDpL f p L) :
    IteratedFDerivLipschitzOn f p L univ :=
  (lipschitzDerivsAnchored_univ_top_iff.1 h.1).2

/-- Under f.DpL, $\|\nabla^p f(x) - \nabla^p f(y)\| \le L \|x - y\|$ for all
$x, y \in \mathbb{R}^n$. This is (4.1.17). -/
theorem lipschitz (h : AssumptionDpL f p L) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖ :=
  iteratedFDerivLipschitzOn_iff.1 h.iteratedFDerivLipschitzOn x (mem_univ _) y (mem_univ _)

/-- A $C^p$ function whose $p$-th derivative is $L$-Lipschitz on $\mathbb{R}^n$
(`IteratedFDerivLipschitzOn`), with $L \ge 1$, satisfies f.DpL with constant $L$. -/
theorem of_iteratedFDerivLipschitzOn (hf : ContDiff ℝ p f) (hL1 : 1 ≤ L)
    (hL : IteratedFDerivLipschitzOn f p L univ) : AssumptionDpL f p L :=
  ⟨lipschitzDerivsAnchored_univ_top_iff.2 ⟨hf, hL⟩, hL1⟩

/-- f.DpL in the form (4.1.17): if $f$ is $C^p$, $L \ge 1$ and $\|\nabla^p f(x) - \nabla^p f(y)\|
\le L \|x - y\|$ for all $x, y$, then $f$ satisfies f.DpL with constant $L$. -/
theorem of_lipschitz (hf : ContDiff ℝ p f) (hL1 : 1 ≤ L)
    (hL : ∀ x y, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖) :
    AssumptionDpL f p L :=
  of_iteratedFDerivLipschitzOn hf hL1 (iteratedFDerivLipschitzOn_iff.2 fun x _ y _ => hL x y)

/-- If $f$ satisfies f.DpL with constant $L$ and $L \le L'$, then $f$ satisfies f.DpL with constant
$L'$. -/
theorem mono (h : AssumptionDpL f p L) {L' : ℝ} (hL : L ≤ L') : AssumptionDpL f p L' :=
  ⟨h.1.mono_const fun _ _ => hL, h.2.trans hL⟩

end AssumptionDpL

/-- For $p = 2$, f.DpL with constant $L$ is equivalent to f.HL with constant $L$
(`CartisGouldToint.Chapter03.AssumptionHL`). -/
theorem assumptionDpL_two_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} :
    AssumptionDpL f 2 L ↔ Chapter03.AssumptionHL f L :=
  Iff.rfl

/-- For $p = 1$, f.DpL with constant $L$ is equivalent to f.gL with constant $L$
(`CartisGouldToint.Chapter02.AssumptionGL`). -/
theorem assumptionDpL_one_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} :
    AssumptionDpL f 1 L ↔ Chapter02.AssumptionGL f L :=
  Iff.rfl

/-- The set $\mathcal{Z}_\varepsilon$ of (4.1.4) of [cartis2022evaluation]: the unit directions
along which the curvature of $f$ at $x$ is at most $\varepsilon_2$ in absolute value,
$$\mathcal{Z}_\varepsilon = \{d \in \mathbb{R}^n : \|d\| = 1,\ |\nabla^2 f(x)[d]^2| \le
  \varepsilon_2\}.$$
At $x = x_0$ it is also the set $\mathcal{M}_0$ of Step 0 of Algorithm 4.1.1. -/
noncomputable def smallCurvatureSet (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (ε₂ : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  smallCurvatureDirections (iteratedFDeriv ℝ 2 f x) ε₂

/-- A vector $d$ is in $\mathcal{Z}_\varepsilon$ if and only if $\|d\| = 1$ and
$|\nabla^2 f(x)[d]^2| \le \varepsilon_2$. -/
theorem mem_smallCurvatureSet {f : EuclideanSpace ℝ (Fin n) → ℝ} {x d : EuclideanSpace ℝ (Fin n)}
    {ε₂ : ℝ} :
    d ∈ smallCurvatureSet f x ε₂ ↔ ‖d‖ = 1 ∧ |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ ε₂ :=
  Iff.rfl

/-- **(4.1.3)–(4.1.4)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$ and
$\varepsilon_1, \varepsilon_2, \varepsilon_3 \in \mathbb{R}$. A point $x$ is an
**$\varepsilon$-approximate third-order minimizer** of $f$ if it is an
$(\varepsilon_1, \varepsilon_2)$-approximate second-order minimizer (3.2.6), that is,
$\|\nabla f(x)\| \le \varepsilon_1$ and $\lambda_{\min}[\nabla^2 f(x)] \ge -\varepsilon_2$, and
$$|\nabla^3 f(x)[d]^3| \le \varepsilon_3 \quad \text{for every } d \in
  \mathcal{Z}_\varepsilon,$$
where $\mathcal{Z}_\varepsilon$ is the set (4.1.4) of unit vectors $d$ with
$|\nabla^2 f(x)[d]^2| \le \varepsilon_2$.

The last condition is vacuous when $\mathcal{Z}_\varepsilon = \emptyset$. For $n \ge 1$ and
$\varepsilon_2 \ge 0$ the second-order condition then gives
$\lambda_{\min}[\nabla^2 f(x)] > \varepsilon_2$. The set $\mathcal{Z}_\varepsilon$ is
`CartisGouldToint.Chapter04.smallCurvatureSet`, and the second-order condition is
`CartisGouldToint.Chapter03.IsApproxSecondOrderMinimizer`. -/
def IsApproxThirdOrderMinimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (ε₁ ε₂ ε₃ : ℝ) : Prop :=
  Chapter03.IsApproxSecondOrderMinimizer f x ε₁ ε₂ ∧
    ∀ d ∈ smallCurvatureSet f x ε₂, |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ ε₃

/-- The certificate of the third-order test of ARp (Theorem 4.1.5 of [cartis2022evaluation]): $x$ is
an $(\varepsilon_1, \varepsilon_2)$-approximate second-order minimizer of $f$, and
$|\nabla^3 f(x)[d]^3| \le \varepsilon_3$ for every $d$ in a given set $M$ of directions. The
algorithm uses for $M$ the set $\mathcal{M}_\varepsilon$ of directions of small model curvature
at termination, in place of $\mathcal{Z}_\varepsilon$. -/
def IsApproxThirdOrderMinimizerOn (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (ε₁ ε₂ ε₃ : ℝ) (M : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Chapter03.IsApproxSecondOrderMinimizer f x ε₁ ε₂ ∧
    ∀ d ∈ M, |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ ε₃

/-- A point is an $\varepsilon$-approximate third-order minimizer if and only if it satisfies
`CartisGouldToint.Chapter04.IsApproxThirdOrderMinimizerOn` with $M = \mathcal{Z}_\varepsilon$. -/
theorem isApproxThirdOrderMinimizer_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {ε₁ ε₂ ε₃ : ℝ} :
    IsApproxThirdOrderMinimizer f x ε₁ ε₂ ε₃ ↔
      IsApproxThirdOrderMinimizerOn f x ε₁ ε₂ ε₃ (smallCurvatureSet f x ε₂) :=
  Iff.rfl

/-- **Algorithm 4.1.1** of [cartis2022evaluation], Step 1: the termination test (4.1.5)–(4.1.9). Let
$f : \mathbb{R}^n \to \mathbb{R}$, $\varepsilon_1 \in \mathbb{R}$ and $\varepsilon_2,
\varepsilon_3 \in \mathbb{R} \cup \{+\infty\}$, and let $M \subseteq \mathbb{R}^n$ be the
current set $\mathcal{M}_k$ of directions of small model curvature. The test holds at $x$ if
$\|\nabla f(x)\| \le \varepsilon_1$ (4.1.5) and, when $\varepsilon_2 < \infty$, either
$\lambda_{\min}[\nabla^2 f(x)] > \varepsilon_2$ (4.1.6), or $\lambda_{\min}[\nabla^2 f(x)] \ge
-\varepsilon_2$ (4.1.7) and, when also $\varepsilon_3 < \infty$,
$$|\nabla^3 f(x)[d]^3| \le \varepsilon_3 \ \text{(4.1.8)} \quad \text{and} \quad |\nabla^2
  f(x)[d]^2| \le \varepsilon_2 \ \text{(4.1.9)} \qquad \text{for all } d \in M.$$

**Correction.** In the branch (4.1.8)–(4.1.9) the source also requires
$\mathcal{M}_k \neq \emptyset$. With this requirement a run can get stuck at a point that
satisfies (4.1.5) and (4.1.7) with $\mathcal{M}_k = \emptyset$. The proof of Theorem 4.1.5 uses
the reading "for all $d \in \mathcal{M}_k$", which is vacuous when $\mathcal{M}_k = \emptyset$,
and this reading is the one formalized.

The tolerances $\varepsilon_2$ and $\varepsilon_3$ are `Option ℝ`, with `none` for $+\infty$.
The number $\lambda_{\min}[\nabla^2 f(x)]$ is `CartisGouldToint.Chapter01.hessianMinEig f x`. -/
def arpStopTest (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε₁ : ℝ) (ε₂ ε₃ : Option ℝ)
    (M : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖gradient f x‖ ≤ ε₁ ∧ ∀ e₂ ∈ ε₂, e₂ < Chapter01.hessianMinEig f x ∨
    (-e₂ ≤ Chapter01.hessianMinEig f x ∧ ∀ e₃ ∈ ε₃, ∀ d ∈ M,
      |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ e₃ ∧ |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ e₂)

section StopTest

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {ε₁ : ℝ} {M : Set (EuclideanSpace ℝ (Fin n))}
  {x : EuclideanSpace ℝ (Fin n)}

/-- With $\varepsilon_2 = +\infty$ the termination test of ARp is
$\|\nabla f(x)\| \le \varepsilon_1$. -/
@[simp]
theorem arpStopTest_none {ε₃ : Option ℝ} :
    arpStopTest f ε₁ none ε₃ M x ↔ ‖gradient f x‖ ≤ ε₁ := by
  simp [arpStopTest]

/-- With $\varepsilon_3 = +\infty$, and $\varepsilon_2 \ge 0$ if $\varepsilon_2$ is finite, the
termination test of ARp is the second-order test (3.2.9) of Chapter 3
(`CartisGouldToint.Chapter03.stopTest`): $\|\nabla f(x)\| \le \varepsilon_1$ and, if
$\varepsilon_2 < \infty$, $\lambda_{\min}[\nabla^2 f(x)] \ge -\varepsilon_2$. -/
theorem arpStopTest_none_right {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 ≤ e) :
    arpStopTest f ε₁ ε₂ none M x ↔ Chapter03.stopTest f ε₁ ε₂ x := by
  rcases ε₂ with _ | e₂
  · simp
  · have he := hε₂ e₂ rfl
    simp only [arpStopTest, Option.mem_def, Option.some.injEq, forall_eq', reduceCtorEq,
      IsEmpty.forall_iff, implies_true, and_true, Chapter03.stopTest_def]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, by linarith⟩
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Or.inr h2⟩

/-- With finite tolerances $\varepsilon_2$ and $\varepsilon_3$, the termination test fails if and
only if $\|\nabla f(x)\| > \varepsilon_1$, or $\lambda_{\min}[\nabla^2 f(x)] \le \varepsilon_2$
and either $\lambda_{\min}[\nabla^2 f(x)] < -\varepsilon_2$ or some $d \in M$ violates (4.1.8)
or (4.1.9). -/
theorem not_arpStopTest_some_some {e₂ e₃ : ℝ} :
    ¬ arpStopTest f ε₁ (some e₂) (some e₃) M x ↔
      ε₁ < ‖gradient f x‖ ∨ (Chapter01.hessianMinEig f x ≤ e₂ ∧
        (Chapter01.hessianMinEig f x < -e₂ ∨ ∃ d ∈ M,
          e₃ < |iteratedFDeriv ℝ 3 f x (fun _ => d)| ∨
            e₂ < |iteratedFDeriv ℝ 2 f x (fun _ => d)|)) := by
  have hs : arpStopTest f ε₁ (some e₂) (some e₃) M x ↔ ‖gradient f x‖ ≤ ε₁ ∧
      (e₂ < Chapter01.hessianMinEig f x ∨ (-e₂ ≤ Chapter01.hessianMinEig f x ∧ ∀ d ∈ M,
        |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ e₃ ∧
          |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ e₂)) := by
    unfold arpStopTest
    refine and_congr Iff.rfl ⟨fun h => ?_, fun h e he => ?_⟩
    · rcases h e₂ rfl with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2 e₃ rfl⟩
    · cases he
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun e he => by cases he; exact h2⟩
  rw [hs]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    refine h ⟨h1, ?_⟩
    rcases le_or_gt (Chapter01.hessianMinEig f x) e₂ with hl | hl
    · obtain ⟨h4, h5⟩ := h2 hl
      exact Or.inr ⟨h4, fun d hd => h5 d hd⟩
    · exact Or.inl hl
  · rintro (h | ⟨hl, h | ⟨d, hd, h⟩⟩) ⟨h1, h2⟩
    · linarith
    · rcases h2 with h2 | ⟨h2, -⟩ <;> linarith
    · rcases h2 with h2 | ⟨-, h2⟩
      · linarith
      · obtain ⟨h3, h4⟩ := h2 d hd
        rcases h with h | h <;> linarith

/-- The certificate of the third-order test (Theorem 4.1.5 of [cartis2022evaluation] and the
discussion after Algorithm 4.1.1). Let $\varepsilon_2 \ge 0$ and $\varepsilon_3$ be finite, and
let $M$ be a set of unit vectors. If the test holds at $x$ with the set $M$, then $x$ is an
$(\varepsilon_1, \varepsilon_2)$-approximate second-order minimizer, and either
$\lambda_{\min}[\nabla^2 f(x)] > \varepsilon_2$ (an approximate strict local minimizer, with
$\mathcal{Z}_\varepsilon = \emptyset$), or $M \subseteq \mathcal{Z}_\varepsilon$ and
$|\nabla^3 f(x)[d]^3| \le \varepsilon_3$ for all $d \in M$. -/
theorem arpStopTest_some_some_certificate {e₂ e₃ : ℝ} (he₂ : 0 ≤ e₂)
    (hM : ∀ d ∈ M, ‖d‖ = 1) (h : arpStopTest f ε₁ (some e₂) (some e₃) M x) :
    Chapter03.IsApproxSecondOrderMinimizer f x ε₁ e₂ ∧
      (e₂ < Chapter01.hessianMinEig f x ∨
        (M ⊆ smallCurvatureSet f x e₂ ∧ IsApproxThirdOrderMinimizerOn f x ε₁ e₂ e₃ M)) := by
  obtain ⟨h1, h2⟩ := h
  rcases h2 e₂ rfl with h2 | ⟨h2, h3⟩
  · exact ⟨⟨h1, by linarith⟩, Or.inl h2⟩
  · exact ⟨⟨h1, h2⟩, Or.inr ⟨fun d hd => ⟨hM d hd, (h3 e₃ rfl d hd).2⟩, ⟨h1, h2⟩,
      fun d hd => (h3 e₃ rfl d hd).1⟩⟩

end StopTest

/-- The order $q$ of criticality that ARp seeks: $q = 1$ if $\varepsilon_2 = +\infty$ (whatever
$\varepsilon_3$ is), $q = 2$ if $\varepsilon_2 < \infty = \varepsilon_3$, and $q = 3$ if both
tolerances are finite. -/
def arpOrder : Option ℝ → Option ℝ → ℕ
  | none, _ => 1
  | some _, none => 2
  | some _, some _ => 3

/-- The order sought is $q = 1$ when $\varepsilon_2 = +\infty$. -/
@[simp] theorem arpOrder_none (ε₃ : Option ℝ) : arpOrder none ε₃ = 1 := rfl
/-- The order sought is $q = 2$ when $\varepsilon_2 < \infty$ and $\varepsilon_3 = +\infty$. -/
@[simp] theorem arpOrder_some_none (e₂ : ℝ) : arpOrder (some e₂) none = 2 := rfl
/-- The order sought is $q = 3$ when both tolerances are finite. -/
@[simp] theorem arpOrder_some_some (e₂ e₃ : ℝ) : arpOrder (some e₂) (some e₃) = 3 := rfl

/-- The sets $\mathcal{M}_k$ of directions of small model curvature along an ARp run of
[cartis2022evaluation]. The set $\mathcal{M}_0$ is $\mathcal{Z}_\varepsilon$ at $x_0$ (Step 0),
and (4.1.14) gives
$$\mathcal{M}_{k+1} = \{d : \|d\| = 1,\ |\nabla^2 m_k(s_k)[d]^2| \le \theta_2 \|s_k\|^{p-1}\},$$
with $m_k$ the model (4.1.2) at $x_k$ with weight $\sigma_k$. If $\varepsilon_2 = +\infty$, then
$\mathcal{M}_0 = \emptyset$. The sets are used only when $\varepsilon_3 < \infty$. -/
noncomputable def arpCurvSet (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpParams)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) :
    ℕ → Set (EuclideanSpace ℝ (Fin n))
  | 0 => ε₂.elim ∅ (smallCurvatureSet f (x 0))
  | k + 1 => smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1))

/-- The set $\mathcal{M}_{k+1}$ is the set (4.1.14) of unit vectors $d$ with $|\nabla^2
m_k(s_k)[d]^2| \le \theta_2 \|s_k\|^{p-1}$. -/
theorem arpCurvSet_succ (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpParams)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) (k : ℕ) :
    arpCurvSet f p P ε₂ x s σ (k + 1) = smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1)) := rfl

/-- Every element of a set $\mathcal{M}_k$ is a unit vector. -/
theorem norm_eq_one_of_mem_arpCurvSet {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpParams}
    {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ} {k : ℕ}
    {d : EuclideanSpace ℝ (Fin n)} (hd : d ∈ arpCurvSet f p P ε₂ x s σ k) : ‖d‖ = 1 := by
  cases k with
  | zero =>
    rcases ε₂ with _ | e₂
    · exact absurd hd (by simp [arpCurvSet])
    · exact hd.1
  | succ k => exact hd.1

/-- The termination test of iteration $k$ of an ARp run: the test (4.1.5)–(4.1.9) of Step 1 at
$x_k$, with the set $\mathcal{M}_k$. -/
abbrev arpTest (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpParams) (ε₁ : ℝ)
    (ε₂ ε₃ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) (k : ℕ) : Prop :=
  arpStopTest f ε₁ ε₂ ε₃ (arpCurvSet f p P ε₂ x s σ k) (x k)

/-- **Algorithm 4.1.1** of [cartis2022evaluation] (ARp), as a predicate on sequences of iterates
$x_k$, steps $s_k$ and regularization weights $\sigma_k$. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$p \ge 1$, $\varepsilon_1 > 0$ and $\varepsilon_2, \varepsilon_3 \in (0, +\infty]$, with
$\varepsilon_3 = +\infty$ if $\varepsilon_2 = +\infty$. Let $q \in \{1, 2, 3\}$ be the order of
criticality sought, and require $q \le p$. Let $m_k$ be the model (4.1.2) at $x_k$ with weight
$\sigma_k$. The sequences form a run if $\sigma_0$ is the initial weight of the constants and,
at every iteration $k$ before the first iteration at which the test (4.1.5)–(4.1.9) holds, the
following conditions hold.

* The step satisfies $m_k(s_k) < m_k(0)$ (4.1.10) and
  $\|\nabla m_k(s_k)\| \le \theta_1 \|s_k\|^p$ (4.1.11).
* If $q \ge 2$, then $\lambda_{\min}[\nabla^2 m_k(s_k)] \ge -\theta_2 \|s_k\|^{p-1}$ (4.1.12).
* If $q = 3$, then $|\nabla^3 m_k(s_k)[d]^3| \le \theta_3 \|s_k\|^{p-2}$ for all
  $d \in \mathcal{M}_{k+1}$ (4.1.13).
* With the ratio $\rho_k$ of (4.1.15), $x_{k+1} = x_k + s_k$ if $\rho_k \ge \eta_1$, and
  $x_{k+1} = x_k$ otherwise.
* The weight follows (4.1.16): $\sigma_{k+1} \in [\max(\sigma_{\min}, \gamma_1 \sigma_k),
  \sigma_k]$ if $\rho_k \ge \eta_2$, $\sigma_{k+1} \in [\sigma_k, \gamma_2 \sigma_k]$ if
  $\eta_1 \le \rho_k < \eta_2$, and $\sigma_{k+1} \in [\gamma_2 \sigma_k, \gamma_3 \sigma_k]$ if
  $\rho_k < \eta_1$.

Iteration $k$ is successful if $\rho_k \ge \eta_1$.

**Correction.** The source also requires $\mathcal{M}_k \neq \emptyset$ in the third-order
branch of Step 1; this requirement is dropped, as explained at
`CartisGouldToint.Chapter04.arpStopTest`. Likewise (4.1.13) is required for all
$d \in \mathcal{M}_{k+1}$, and it is vacuous when $\mathcal{M}_{k+1} = \emptyset$.

The order $q$ is `CartisGouldToint.Chapter04.arpOrder ε₂ ε₃`, the test is
`CartisGouldToint.Chapter04.arpTest`, and the run is the backbone predicate
`Optimization.IsARpRun` with these data. The ratio $\rho_k$ is
`Optimization.taylorRatio f p x s k`. With $\varepsilon_3 < \infty$ a run need not exist
(`CartisGouldToint.Chapter04.not_exists_algorithm_4_1_1_third_order`). -/
structure algorithm_4_1_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpParams) (ε₁ : ℝ)
    (ε₂ ε₃ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- The order $p$ of the models is at least $1$. -/
  one_le_p : 1 ≤ p
  /-- The order $p$ of the models is at least the order $q$ of criticality sought. -/
  order_le : arpOrder ε₂ ε₃ ≤ p
  /-- The first-order tolerance satisfies $\varepsilon_1 > 0$. -/
  ε₁_pos : 0 < ε₁
  /-- If it is finite, the second-order tolerance satisfies $\varepsilon_2 > 0$. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- If it is finite, the third-order tolerance satisfies $\varepsilon_3 > 0$. -/
  ε₃_pos : ∀ e ∈ ε₃, 0 < e
  /-- If $\varepsilon_2 = +\infty$, then $\varepsilon_3 = +\infty$. -/
  ε₃_eq_none : ε₂ = none → ε₃ = none
  /-- Steps 1–4: the sequences form an ARp run (`Optimization.IsARpRun`) of order $q$ with the
  termination test `CartisGouldToint.Chapter04.arpTest`. -/
  run : IsARpRun f p P.toARpParams (arpOrder ε₂ ε₃) (arpTest f p P ε₁ ε₂ ε₃ x s σ) x s σ

section Order

/-- If $\varepsilon_2 < \infty$, then the order sought is $q \ge 2$. -/
theorem two_le_arpOrder {ε₂ ε₃ : Option ℝ} (h : ε₂ ≠ none) : 2 ≤ arpOrder ε₂ ε₃ := by
  rcases ε₂ with _ | e₂
  · exact absurd rfl h
  · rcases ε₃ with _ | e₃ <;> simp

/-- If $\varepsilon_2 < \infty$ and $\varepsilon_3 < \infty$, then the order sought is $q \ge 3$. -/
theorem three_le_arpOrder {ε₂ ε₃ : Option ℝ} (h₂ : ε₂ ≠ none) (h₃ : ε₃ ≠ none) :
    3 ≤ arpOrder ε₂ ε₃ := by
  rcases ε₂ with _ | e₂
  · exact absurd rfl h₂
  · rcases ε₃ with _ | e₃
    · exact absurd rfl h₃
    · simp

/-- The order sought is $q \le 3$. -/
theorem arpOrder_le_three (ε₂ ε₃ : Option ℝ) : arpOrder ε₂ ε₃ ≤ 3 := by
  rcases ε₂ with _ | e₂ <;> rcases ε₃ with _ | e₃ <;> simp

/-- If $\varepsilon_3 = +\infty$, then the order sought is $q \le 2$. -/
theorem arpOrder_none_right_le_two (ε₂ : Option ℝ) : arpOrder ε₂ none ≤ 2 := by
  rcases ε₂ with _ | e₂ <;> simp

end Order

namespace algorithm_4_1_1

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpParams} {ε₁ : ℝ}
  {ε₂ ε₃ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- Along an ARp run, the step $s_k$ satisfies the conditions (4.1.10)–(4.1.13) of Step 2 at every
iteration $k$ such that the termination test fails at the iterations $0, \dots, k$. -/
theorem step (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) :
    IsARpStep f p P.toARpParams (arpOrder ε₂ ε₃) (x k) (σ k) (s k) :=
  h.run.step_spec hk

/-- Along an ARp run, $\sigma_k > 0$ for every $k$ such that the termination test fails at all
iterations before $k$. -/
theorem sigma_pos (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) : 0 < σ k :=
  h.run.sigma_pos hk

/-- Along an ARp run, a finite second-order tolerance requires $p \ge 2$. -/
theorem two_le_p (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) (h₂ : ε₂ ≠ none) : 2 ≤ p :=
  (two_le_arpOrder h₂).trans h.order_le

/-- Along an ARp run, a finite third-order tolerance gives the order $q = 3$, and it requires a
finite $\varepsilon_2$. -/
theorem three_le_order (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) (h₃ : ε₃ ≠ none) :
    3 ≤ arpOrder ε₂ ε₃ :=
  three_le_arpOrder (fun h₂ => h₃ (h.ε₃_eq_none h₂)) h₃

/-- Along an ARp run, a finite third-order tolerance requires $p \ge 3$. -/
theorem three_le_p (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) (h₃ : ε₃ ≠ none) : 3 ≤ p :=
  (h.three_le_order h₃).trans h.order_le

/-- (4.1.18) along an ARp run: at every iteration $k$ such that the termination test fails at the
iterations $0, \dots, k$,
$$T_{f,p}(x_k, 0) - T_{f,p}(x_k, s_k) > \frac{\sigma_k}{(p+1)!} \|s_k\|^{p+1}.$$
-/
theorem lt_taylorDecrement (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) :
    σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) <
      (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
  lt_taylorDecrement_of_regularizedModel_lt (h.step hk).decrease

/-- Along an ARp run, the decrease $T_{f,p}(x_k, 0) - T_{f,p}(x_k, s_k)$ of the Taylor polynomial is
positive at every iteration $k$ such that the termination test fails at the iterations
$0, \dots, k$. -/
theorem taylorDecrement_pos (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) :
    0 < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) := by
  have := h.sigma_pos fun j hj => hk j hj.le
  exact lt_of_le_of_lt (by positivity) (h.lt_taylorDecrement hk)

end algorithm_4_1_1

/-! ### Existence of runs -/

section Existence

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ}

/-- **Algorithm 4.1.1** of [cartis2022evaluation], existence of runs for $\varepsilon_3 = +\infty$.
Let $f : \mathbb{R}^n \to \mathbb{R}$ be $p$ times continuously differentiable with $p \ge 1$,
let the constants of ARp be given, and let $\varepsilon_1 > 0$ and
$\varepsilon_2 \in (0, +\infty]$, with $p \ge 2$ if $\varepsilon_2 < \infty$. Then for every
$x_0 \in \mathbb{R}^n$ there is a run of ARp with $\varepsilon_3 = +\infty$ that starts at
$x_0$.

The source takes for granted that the algorithm is well defined. In the proof, a global
minimizer of the model (4.1.2) satisfies Step 2 whenever the termination test fails. For
$\varepsilon_3 < \infty$ a run need not exist
(`CartisGouldToint.Chapter04.not_exists_algorithm_4_1_1_third_order`). -/
theorem exists_algorithm_4_1_1 (hf : ContDiff ℝ p f) (P : ARpParams) (hp : 1 ≤ p) {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e) (hord : arpOrder ε₂ none ≤ p)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_4_1_1 f p P ε₁ ε₂ none x s σ := by
  have hq := arpOrder_none_right_le_two ε₂
  have hcrit : ∀ y, ¬ Chapter03.stopTest f ε₁ ε₂ y → fderiv ℝ f y ≠ 0 ∨
      (2 ≤ arpOrder ε₂ none ∧ minCurvature (iteratedFDeriv ℝ 2 f y) < 0) := by
    intro y hy
    by_cases hg : fderiv ℝ f y = 0
    · right
      have hg' : ‖gradient f y‖ = 0 := by rw [norm_gradient_eq, hg, norm_zero]
      rcases ε₂ with _ | e₂
      · exact absurd (by rw [Chapter03.stopTest_none, hg']; exact hε₁.le) hy
      · refine ⟨by simp, ?_⟩
        rw [Chapter03.not_stopTest_some, hg'] at hy
        have := hε₂ e₂ rfl
        rcases hy with hy | hy
        · linarith
        · change Chapter01.hessianMinEig f y < 0
          linarith
    · exact Or.inl hg
  obtain ⟨x, s, σ, hx0, hrun⟩ := exists_isARpRun (q := arpOrder ε₂ none) P.toARpParams hf hp hq
    (fun h2 => h2.trans hord) (test := Chapter03.stopTest f ε₁ ε₂) hcrit x₀
  refine ⟨x, s, σ, hx0, ⟨hp, hord, hε₁, hε₂, fun _ h => absurd h (by simp), fun _ => rfl, ?_⟩⟩
  have htest : arpTest f p P ε₁ ε₂ none x s σ = fun k => Chapter03.stopTest f ε₁ ε₂ (x k) :=
    funext fun k => propext (arpStopTest_none_right fun e he => (hε₂ e he).le)
  rw [htest]
  exact hrun

end Existence

/-! ### Lemmas 4.1.1–4.1.4 -/

/-- **Lemma 4.1.1** of [cartis2022evaluation], (4.1.18). Let $f : \mathbb{R}^n \to \mathbb{R}$,
$p \in \mathbb{N}$, $x, s \in \mathbb{R}^n$ and $\sigma \in \mathbb{R}$, and let $m(s) =
T_{f,p}(x, s) + \frac{\sigma}{(p+1)!} \|s\|^{p+1}$ be the model (4.1.2). If $m(s) \le m(0)$,
then
$$T_{f,p}(x, 0) - T_{f,p}(x, s) \ge \frac{\sigma}{(p+1)!} \|s\|^{p+1}.$$

The statement needs no assumption on $f$, because $T_{f,p}$ is built from `ftaylorSeries ℝ f x`.
Along an ARp run the inequality holds strictly at every iteration before termination
(`CartisGouldToint.Chapter04.algorithm_4_1_1.lt_taylorDecrement`). -/
theorem lemma_4_1_1 {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {x s : EuclideanSpace ℝ (Fin n)}
    {σ : ℝ} (h : regularizedModel (ftaylorSeries ℝ f x) p σ s ≤
      regularizedModel (ftaylorSeries ℝ f x) p σ 0) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ (ftaylorSeries ℝ f x).taylorDecrement p s :=
  taylorDecrement_ge_of_regularizedModel_le h

/-- The bound $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_{f,p}/(1 - \eta_2))$ of (4.1.19) of
[cartis2022evaluation] on the regularization weights (`Optimization.arSigmaMax`). -/
noncomputable abbrev sigmaMaxARp (P : ARpParams) (L : ℝ) : ℝ := arSigmaMax P.toARParams L

/-- The constant
$$\kappa_1 = \frac{\eta_1 \sigma_{\min}}{(p+1)!} \left(\frac{p!}{L_{f,p} + \sigma_{\max} +
  \theta_1 p!}\right)^{(p+1)/p}$$
of (4.1.32) of [cartis2022evaluation]. -/
noncomputable def kappaARp₁ (P : ARpParams) (p : ℕ) (L : ℝ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    ((p ! : ℝ) / (L + sigmaMaxARp P L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p)

/-- The constant
$$\kappa_2 = \frac{\eta_1 \sigma_{\min}}{(p+1)!} \left(\frac{(p-1)!}{L_{f,p} + \sigma_{\max} +
  \theta_2 (p-1)!}\right)^{(p+1)/(p-1)}$$
of (4.1.34) of [cartis2022evaluation]. -/
noncomputable def kappaARp₂ (P : ARpParams) (p : ℕ) (L : ℝ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    (((p - 1)! : ℝ) / (L + sigmaMaxARp P L + P.θ₂ * (p - 1)!)) ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))

/-- The constant
$$\kappa_3 = \frac{\eta_1 \sigma_{\min}}{(p+1)!} \left(\frac{(p-2)!}{L_{f,p} + \sigma_{\max} +
  \theta_3 (p-2)!}\right)^{(p+1)/(p-2)}$$
of (4.1.36) of [cartis2022evaluation]. -/
noncomputable def kappaARp₃ (P : ARpParams) (p : ℕ) (L : ℝ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    (((p - 2)! : ℝ) / (L + sigmaMaxARp P L + P.θ₃ * (p - 2)!)) ^ (((p : ℝ) + 1) / ((p : ℝ) - 2))

/-- The constant $\kappa_{s2} = (p-1)!/(L_{f,p} + \sigma_{\max} + \theta_2 (p-1)!)$ of (4.1.23) of
[cartis2022evaluation]. -/
noncomputable def kappaS2ARp (P : ARpParams) (p : ℕ) (L : ℝ) : ℝ :=
  ((p - 1)! : ℝ) / (L + sigmaMaxARp P L + P.θ₂ * (p - 1)!)

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpParams} {ε₁ L flow : ℝ}
  {ε₂ ε₃ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 4.1.2** of [cartis2022evaluation], (4.1.19). Let $f : \mathbb{R}^n \to \mathbb{R}$
satisfy f.DpL with constant $L_{f,p}$, and let $(x_k, s_k, \sigma_k)$ be a run of ARp. Then
$$\sigma_k \le \sigma_{\max} = \max\left(\sigma_0, \frac{\gamma_3 L_{f,p}}{1 - \eta_2}\right)$$
for every $k$ such that the termination test fails at all iterations before $k$, that is, for
every iteration up to and including termination. -/
theorem lemma_4_1_2 (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    {k : ℕ} (hk : ∀ j < k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) : σ k ≤ sigmaMaxARp P L :=
  (h.run.sigma_le hf.contDiff hf.iteratedFDerivLipschitzOn hk).2

/-- **Lemma 4.1.3** of [cartis2022evaluation], (4.1.20). Let $f : \mathbb{R}^n \to \mathbb{R}$
satisfy f.DpL with constant $L_{f,p}$, and let $(x_k, s_k, \sigma_k)$ be a run of ARp. If the
termination test fails at the iterations $0, \dots, k$ and iteration $k$ is successful, then
$$\|s_k\|^p \ge \frac{p!}{L_{f,p} + \sigma_{\max} + \theta_1 p!} \|\nabla f(x_{k+1})\|.$$
-/
theorem lemma_4_1_3_i (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    (p ! : ℝ) / (L + sigmaMaxARp P L + P.θ₁ * p !) * ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ ^ p := by
  rw [norm_gradient_eq]
  exact (h.run.step_lower_bounds hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p
    h.order_le hk hs).2.1

/-- **Lemma 4.1.3** of [cartis2022evaluation], (4.1.21). Let $f : \mathbb{R}^n \to \mathbb{R}$
satisfy f.DpL with constant $L_{f,p}$, and let $(x_k, s_k, \sigma_k)$ be a run of ARp with
$\varepsilon_2 < \infty$. If the termination test fails at the iterations $0, \dots, k$ and
iteration $k$ is successful, then
$$\|s_k\|^{p-1} \ge \frac{(p-1)!}{L_{f,p} + \sigma_{\max} + \theta_2 (p-1)!} \max\left(0,
  -\lambda_{\min}[\nabla^2 f(x_{k+1})]\right).$$
-/
theorem lemma_4_1_3_ii (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    (h₂ : ε₂ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    ((p - 1)! : ℝ) / (L + sigmaMaxARp P L + P.θ₂ * (p - 1)!) *
      max 0 (-Chapter01.hessianMinEig f (x (k + 1))) ≤ ‖s k‖ ^ (p - 1) :=
  (h.run.step_lower_bounds hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p
    h.order_le hk hs).2.2.1 (two_le_arpOrder h₂)

/-- **Lemma 4.1.3** of [cartis2022evaluation], (4.1.22). Let $f : \mathbb{R}^n \to \mathbb{R}$
satisfy f.DpL with constant $L_{f,p}$, and let $(x_k, s_k, \sigma_k)$ be a run of ARp with
$\varepsilon_3 < \infty$. If the termination test fails at the iterations $0, \dots, k$ and
iteration $k$ is successful, then for every $d$ in the set $\mathcal{M}_{k+1}$ of (4.1.14),
$$\|s_k\|^{p-2} \ge \frac{(p-2)!}{L_{f,p} + \sigma_{\max} + \theta_3 (p-2)!} |\nabla^3
  f(x_{k+1})[d]^3|.$$
-/
theorem lemma_4_1_3_iii (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    (h₃ : ε₃ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    ∀ d ∈ arpCurvSet f p P ε₂ x s σ (k + 1),
      ((p - 2)! : ℝ) / (L + sigmaMaxARp P L + P.θ₃ * (p - 2)!) *
        |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| ≤ ‖s k‖ ^ (p - 2) :=
  (h.run.step_lower_bounds hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p
    h.order_le hk hs).2.2.2.1 (h.three_le_order h₃)

/-- **Lemma 4.1.3** of [cartis2022evaluation], (4.1.23). Let $f : \mathbb{R}^n \to \mathbb{R}$
satisfy f.DpL with constant $L_{f,p}$, and let $(x_k, s_k, \sigma_k)$ be a run of ARp with
$\varepsilon_2 < \infty$. If the termination test fails at the iterations $0, \dots, k$ and
iteration $k$ is successful, then for every $d$ in the set $\mathcal{M}_{k+1}$ of (4.1.14),
$$|\nabla^2 f(x_{k+1})[d]^2| \le \frac{1}{\kappa_{s2}} \|s_k\|^{p-1}, \qquad \kappa_{s2} =
  \frac{(p-1)!}{L_{f,p} + \sigma_{\max} + \theta_2 (p-1)!}.$$
-/
theorem lemma_4_1_3_iv (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    (h₂ : ε₂ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    ∀ d ∈ arpCurvSet f p P ε₂ x s σ (k + 1),
      |iteratedFDeriv ℝ 2 f (x (k + 1)) (fun _ => d)| ≤ 1 / kappaS2ARp P p L * ‖s k‖ ^ (p - 1) := by
  intro d hd
  rw [kappaS2ARp, one_div_div]
  exact (h.run.step_lower_bounds hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p
    h.order_le hk hs).2.2.2.2 (two_le_arpOrder h₂) d hd

/-- **Lemma 4.1.4** of [cartis2022evaluation], (4.1.31) and (4.1.37). Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.DpL with constant $L_{f,p}$, and let
$(x_k, s_k, \sigma_k)$ be a run of ARp. If the termination test fails at the iterations
$0, \dots, k$ and iteration $k$ is successful, then
$$f(x_k) - f(x_{k+1}) \ge \frac{\eta_1 \sigma_{\min}}{(p+1)!} \|s_k\|^{p+1} \quad \text{and}
  \quad f(x_k) - f(x_{k+1}) \ge \kappa_1 \|\nabla f(x_{k+1})\|^{(p+1)/p},$$
with $\kappa_1$ of (4.1.32). -/
theorem lemma_4_1_4_i (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ f (x k) - f (x (k + 1)) ∧
      kappaARp₁ P p L * ‖gradient f (x (k + 1))‖ ^ (((p : ℝ) + 1) / p) ≤
        f (x k) - f (x (k + 1)) := by
  obtain ⟨h1, h2, -⟩ := h.run.decrease_ge hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg
    h.one_le_p h.order_le hk hs
  rw [norm_gradient_eq]
  exact ⟨h1, h2⟩

/-- **Lemma 4.1.4** of [cartis2022evaluation], (4.1.33). Let $f : \mathbb{R}^n \to \mathbb{R}$
satisfy f.DpL with constant $L_{f,p}$, and let $(x_k, s_k, \sigma_k)$ be a run of ARp with
$\varepsilon_2 < \infty$. If the termination test fails at the iterations $0, \dots, k$ and
iteration $k$ is successful, then
$$f(x_k) - f(x_{k+1}) \ge \kappa_2 \max\left(0, -\lambda_{\min}[\nabla^2
  f(x_{k+1})]\right)^{(p+1)/(p-1)},$$
with $\kappa_2$ of (4.1.34). -/
theorem lemma_4_1_4_ii (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    (h₂ : ε₂ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    kappaARp₂ P p L * (max 0 (-Chapter01.hessianMinEig f (x (k + 1)))) ^
      (((p : ℝ) + 1) / ((p : ℝ) - 1)) ≤ f (x k) - f (x (k + 1)) :=
  (h.run.decrease_ge hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p h.order_le hk
    hs).2.2.1 (two_le_arpOrder h₂)

/-- **Lemma 4.1.4** of [cartis2022evaluation], (4.1.35). Let $f : \mathbb{R}^n \to \mathbb{R}$
satisfy f.DpL with constant $L_{f,p}$, and let $(x_k, s_k, \sigma_k)$ be a run of ARp with
$\varepsilon_3 < \infty$. If the termination test fails at the iterations $0, \dots, k$ and
iteration $k$ is successful, then for every $d \in \mathcal{M}_{k+1}$,
$$f(x_k) - f(x_{k+1}) \ge \kappa_3 |\nabla^3 f(x_{k+1})[d]^3|^{(p+1)/(p-2)},$$
with $\kappa_3$ of (4.1.36). -/
theorem lemma_4_1_4_iii (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    (h₃ : ε₃ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    ∀ d ∈ arpCurvSet f p P ε₂ x s σ (k + 1),
      kappaARp₃ P p L * |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| ^
        (((p : ℝ) + 1) / ((p : ℝ) - 2)) ≤ f (x k) - f (x (k + 1)) :=
  (h.run.decrease_ge hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p h.order_le hk
    hs).2.2.2 (h.three_le_order h₃)

end Lemmas

/-! ### Theorem 4.1.5 -/

/-- The constant $\kappa^S_{\mathrm{ARp}}$ of (4.1.45) of [cartis2022evaluation] for the order of
criticality $q$:
$$\kappa^S = \frac{(p+1)!}{\eta_1 \sigma_{\min}} \max_{j \in \{1, 2, 3\},\ j \le \max(q, 1)}
  \left(\frac{L_{f,p} + \sigma_{\max} + \theta_j (p-j+1)!}{(p-j+1)!}\right)^{(p+1)/(p-j+1)}.$$
Only the terms of the active orders $j \le q$ enter the maximum; the term $j = 1$ is always
present. -/
noncomputable def kappaSARp (P : ARpParams) (p : ℕ) (L : ℝ) (q : ℕ) : ℝ :=
  ((p + 1)! : ℝ) / (P.η₁ * P.σmin) *
    max (((L + sigmaMaxARp P L + P.θ₁ * p !) / (p ! : ℝ)) ^ (((p : ℝ) + 1) / p))
      (max (if 2 ≤ q then ((L + sigmaMaxARp P L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ)) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)) else 0)
        (if 3 ≤ q then ((L + sigmaMaxARp P L + P.θ₃ * (p - 2)!) / ((p - 2)! : ℝ)) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 2)) else 0))

/-- The constant $\kappa^C_{\mathrm{ARp}} = (|\log \gamma_1| + \log(\sigma_{\max}/\sigma_0))/\log
\gamma_2 + 2$ of (4.1.46) of [cartis2022evaluation]. -/
noncomputable def kappaCARp (P : ARpParams) (L : ℝ) : ℝ :=
  (|Real.log P.γ₁| + Real.log (sigmaMaxARp P L / P.σ₀)) / Real.log P.γ₂ + 2

section Constants

variable {P : ARpParams} {p : ℕ} {L : ℝ}

private theorem constant_pos (hL : 0 ≤ L) (θ : ℝ) (hθ : 0 < θ) (m : ℕ) :
    0 < L + sigmaMaxARp P L + θ * m ! := by
  have := arSigmaMax_pos P.toARParams L
  positivity

private theorem one_le_mul_of_le {u v a b M e : ℝ} (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hb : 0 < b) (hM : (b / a) ^ e ≤ M) : 1 ≤ u / v * M * (v / u * (a / b) ^ e) := by
  have h1 : u / v * M * (v / u * (a / b) ^ e) = M * (a / b) ^ e := by
    field_simp
  have h2 : (b / a) ^ e * (a / b) ^ e = 1 := by
    have : b / a * (a / b) = 1 := by field_simp
    rw [← Real.mul_rpow (by positivity) (by positivity), this, Real.one_rpow]
  rw [h1, ← h2]
  exact mul_le_mul_of_nonneg_right hM (by positivity)

/-- If $L_{f,p} \ge 0$, then $\kappa^S > 0$. -/
theorem kappaSARp_pos (hL : 0 ≤ L) (q : ℕ) : 0 < kappaSARp P p L q := by
  have := P.η₁_pos; have := P.σmin_pos
  have h1 : 0 < ((L + sigmaMaxARp P L + P.θ₁ * p !) / (p ! : ℝ)) ^ (((p : ℝ) + 1) / p) := by
    have := constant_pos (P := P) hL _ P.θ₁_pos p
    positivity
  unfold kappaSARp
  exact mul_pos (by positivity) (h1.trans_le (le_max_left _ _))

/-- If $L_{f,p} \ge 0$, then $\kappa^S \kappa_1 \ge 1$ for every order $q$. -/
theorem one_le_kappaSARp_mul_kappaARp₁ (hL : 0 ≤ L) (q : ℕ) :
    1 ≤ kappaSARp P p L q * kappaARp₁ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  exact one_le_mul_of_le (by positivity) (by positivity) (by positivity)
    (constant_pos hL _ P.θ₁_pos p) (le_max_left _ _)

/-- If $L_{f,p} \ge 0$ and $q \ge 2$, then $\kappa^S \kappa_2 \ge 1$. -/
theorem one_le_kappaSARp_mul_kappaARp₂ (hL : 0 ≤ L) {q : ℕ} (hq : 2 ≤ q) :
    1 ≤ kappaSARp P p L q * kappaARp₂ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  refine one_le_mul_of_le (by positivity) (by positivity) (by positivity)
    (constant_pos hL _ P.θ₂_pos (p - 1)) ?_
  refine le_trans (le_of_eq ?_) ((le_max_left _ _).trans (le_max_right _ _))
  simp [hq]

/-- If $L_{f,p} \ge 0$ and $q \ge 3$, then $\kappa^S \kappa_3 \ge 1$. -/
theorem one_le_kappaSARp_mul_kappaARp₃ (hL : 0 ≤ L) {q : ℕ} (hq : 3 ≤ q) :
    1 ≤ kappaSARp P p L q * kappaARp₃ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  refine one_le_mul_of_le (by positivity) (by positivity) (by positivity)
    (constant_pos hL _ P.θ₃_pos (p - 2)) ?_
  refine le_trans (le_of_eq ?_) ((le_max_right _ _).trans (le_max_right _ _))
  simp [hq]

/-- $\kappa_2 = \frac{\eta_1 \sigma_{\min}}{(p+1)!} \kappa_{s2}^{(p+1)/(p-1)}$, the remark after
(4.1.44). -/
theorem kappaARp₂_eq : kappaARp₂ P p L = P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    kappaS2ARp P p L ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) := rfl

/-- $\kappa^C \ge 2$, because $\sigma_{\max} \ge \sigma_0$. -/
theorem two_le_kappaCARp (L : ℝ) : 2 ≤ kappaCARp P L := by
  have h1 : 1 ≤ sigmaMaxARp P L / P.σ₀ := by
    rw [le_div_iff₀ P.σ₀_pos, one_mul]; exact σ₀_le_arSigmaMax _ _
  have := Real.log_nonneg h1
  have := P.toARParams.log_γ₂_pos
  unfold kappaCARp
  have : 0 ≤ (|Real.log P.γ₁| + Real.log (sigmaMaxARp P L / P.σ₀)) / Real.log P.γ₂ := by
    positivity
  linarith

end Constants

private theorem div_le_mul_of_one_le {t E κS κ : ℝ} (hκS : 0 < κS) (h1 : 1 ≤ κS * κ)
    (ht : t ≤ E) (hE : 0 ≤ E) : t / κS ≤ κ * E := by
  rw [div_le_iff₀ hκS]
  nlinarith

section Complexity

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpParams} {ε₁ L flow : ℝ}
  {ε₂ ε₃ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- The common last step of the proof of Theorem 4.1.5 of [cartis2022evaluation]. Let $f$ satisfy
f.Bb with lower bound $f_{\text{low}}$ and f.DpL, let $(x_k, s_k, \sigma_k)$ be a run of ARp,
and let $\delta > 0$. Suppose that $f(x_k) - f(x_{k+1}) \ge \delta$ for every successful
iteration $k$ such that the termination test fails at the iterations $0, \dots, k + 1$. Then the
run terminates at an iteration $k_\varepsilon$, after
$$k_\varepsilon + 1 \le \left(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\right) \frac{f(x_0) -
  f_{\text{low}}}{\delta} + \kappa^C$$
evaluations of $f$ and at most $(f(x_0) - f_{\text{low}})/\delta + 2$ evaluations of the
derivatives. -/
theorem algorithm_4_1_1.exists_isFirstHit_of_decrease (hb : Chapter02.AssumptionBb f flow)
    (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) {δ : ℝ} (hδ : 0 < δ)
    (hdec : ∀ k, (∀ j ≤ k + 1, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) →
      P.η₁ ≤ taylorRatio f p x s k → δ ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (arpTest f p P ε₁ ε₂ ε₃ x s σ) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f (x 0) - flow) / δ) +
        kappaCARp P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        (f (x 0) - flow) / δ + 2 := by
  obtain ⟨kε, hk, hF, hD⟩ := h.run.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := sigmaMaxARp P L) (V := fun k => f (x k)) (Vlow := flow)
    (fun k hk => lemma_4_1_2 hf h (IsARRun.forall_lt_not_stop_iff.1 hk)) hδ
    (fun k hk => (h.run.toIsARRun.accept k hk).le (w := f) rfl
      (h.taylorDecrement_pos (IsARRun.forall_le_not_stop_iff.1 hk)))
    (fun k _ => hb (x k))
    (fun k hk hs => hdec k (IsARRun.forall_le_not_stop_iff.1 hk) hs)
  exact ⟨kε, IsARRun.isFirstHit_stop_iff.1 hk, hF, hD⟩

/-- **Theorem 4.1.5** of [cartis2022evaluation], first-order case
($\varepsilon_2 = \varepsilon_3 = +\infty$). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.Bb
with lower bound $f_{\text{low}}$ and f.DpL with constant $L_{f,p}$, and let
$(x_k, s_k, \sigma_k)$ be a run of ARp with tolerances $\varepsilon_1$ and
$\varepsilon_2 = \varepsilon_3 = +\infty$. Then there is a first iteration $k_\varepsilon$ with
$\|\nabla f(x_{k_\varepsilon})\| \le \varepsilon_1$, at which the run terminates. The number of
evaluations of $f$ satisfies
$$k_\varepsilon + 1 \le \kappa^A \frac{f(x_0) - f_{\text{low}}}{\varepsilon_1^{(p+1)/p}} +
  \kappa^C,$$
and the number of evaluations of the derivatives of orders $1$ to $p$ is at most $\kappa^S
(f(x_0) - f_{\text{low}})/\varepsilon_1^{(p+1)/p} + 2$ (4.1.38). Here
$$\kappa^S = \frac{(p+1)!}{\eta_1 \sigma_{\min}} \left(\frac{L_{f,p} + \sigma_{\max} + \theta_1
  p!}{p!}\right)^{(p+1)/p},$$
$\kappa^A = \kappa^S (1 + |\log \gamma_1|/\log \gamma_2)$, and $\kappa^C$ is the constant
(4.1.46).

**Reading.** The source states one theorem for the three orders, with one constant $\kappa^S$
that mixes them. The theorem is split here by the order of criticality, and each part uses only
the constants of the active orders.

**Generalization.** The source assumes $(\varepsilon_1, \varepsilon_2, \varepsilon_3) \in (0,
1]^3$. The bound $\varepsilon_1 \le 1$ is not needed and is dropped.

The constants are `CartisGouldToint.Chapter04.kappaSARp P p L 1` and
`CartisGouldToint.Chapter04.kappaCARp P L`. The count of evaluations of $f$ is
`Optimization.funEvalCount`, which equals $k_\varepsilon + 1$. The count of evaluations of the
derivatives is `Optimization.derivEvalCount` of the successful iterations. The hypotheses
$\varepsilon_1 > 0$ and $p \ge 1$ are part of the run predicate. -/
theorem theorem_4_1_5_i (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionDpL f p L)
    (h : algorithm_4_1_1 f p P ε₁ none none x s σ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaSARp P p L 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        (f (x 0) - flow) / ε₁ ^ (((p : ℝ) + 1) / p) + kappaCARp P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        kappaSARp P p L 1 * (f (x 0) - flow) / ε₁ ^ (((p : ℝ) + 1) / p) + 2 := by
  have hκ := kappaSARp_pos (P := P) (p := p) hf.nonneg 1
  have hε := h.ε₁_pos
  set e := ((p : ℝ) + 1) / p
  have hE : 0 < ε₁ ^ e := Real.rpow_pos_of_pos hε _
  set δ := ε₁ ^ e / kappaSARp P p L 1
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ = kappaSARp P p L 1 * (f (x 0) - flow) / ε₁ ^ e := by
    simp only [δ]; field_simp
  obtain ⟨kε, hk, hF, hD⟩ := h.exists_isFirstHit_of_decrease hb hf hδ fun k hk hs => by
    have hg : ε₁ < ‖gradient f (x (k + 1))‖ := by
      have := hk (k + 1) le_rfl
      simpa using this
    have h1 := (lemma_4_1_4_i hf h (fun j hj => hk j (hj.trans k.le_succ)) hs).2
    have hκ₁ : 0 ≤ kappaARp₁ P p L := by
      have := P.η₁_pos; have := P.σmin_pos
      have := constant_pos (P := P) hf.nonneg _ P.θ₁_pos p
      unfold kappaARp₁; positivity
    refine le_trans ?_ h1
    refine (div_le_mul_of_one_le hκ (one_le_kappaSARp_mul_kappaARp₁ hf.nonneg 1) le_rfl
      hE.le).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le hg.le (by positivity)) hκ₁
  rw [hNδ] at hF hD
  have htest : arpTest f p P ε₁ none none x s σ = fun k => ‖gradient f (x k)‖ ≤ ε₁ :=
    funext fun k => propext arpStopTest_none
  refine ⟨kε, htest ▸ hk, ?_, hD⟩
  calc (funEvalCount kε : ℝ) ≤ _ := hF
    _ = _ := by ring

private theorem kappaARp₁_nonneg (hL : 0 ≤ L) : 0 ≤ kappaARp₁ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  have := constant_pos (P := P) hL _ P.θ₁_pos p
  unfold kappaARp₁; positivity

private theorem kappaARp₂_nonneg (hL : 0 ≤ L) : 0 ≤ kappaARp₂ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  have := constant_pos (P := P) hL _ P.θ₂_pos (p - 1)
  unfold kappaARp₂; positivity

private theorem kappaARp₃_nonneg (hL : 0 ≤ L) : 0 ≤ kappaARp₃ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  have := constant_pos (P := P) hL _ P.θ₃_pos (p - 2)
  unfold kappaARp₃; positivity

/-- One case of the decrease estimate (4.1.44): if $t \le \varepsilon^e$, $\varepsilon \le v$,
$\kappa^S \kappa \ge 1$ and $D \ge \kappa v^e$, then $D \ge t/\kappa^S$. -/
private theorem div_le_of_decrease {t ε v e κS κ D : ℝ} (hκS : 0 < κS) (h1 : 1 ≤ κS * κ)
    (hκ : 0 ≤ κ) (ht : t ≤ ε ^ e) (hε : 0 ≤ ε) (hv : ε ≤ v) (he : 0 ≤ e) (hD : κ * v ^ e ≤ D) :
    t / κS ≤ D :=
  (div_le_mul_of_one_le hκS h1 ht (by positivity)).trans
    ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε hv he) hκ).trans hD)

/-- **Theorem 4.1.5** of [cartis2022evaluation], second-order case
($\varepsilon_2 < \infty = \varepsilon_3$). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.Bb
with lower bound $f_{\text{low}}$ and f.DpL with constant $L_{f,p}$, and let
$(x_k, s_k, \sigma_k)$ be a run of ARp with tolerances $\varepsilon_1$, a finite $\varepsilon_2$
and $\varepsilon_3 = +\infty$. Then there is a first iteration $k_\varepsilon$ at which
$x_{k_\varepsilon}$ is an $(\varepsilon_1, \varepsilon_2)$-approximate second-order minimizer,
that is, (4.1.5) and (4.1.7) hold, and the run terminates there. With
$$\varepsilon_{\min} = \min\left(\varepsilon_1^{(p+1)/p}, \varepsilon_2^{(p+1)/(p-1)}\right),$$
the number of evaluations of $f$ satisfies $k_\varepsilon + 1 \le \kappa^A (f(x_0) -
f_{\text{low}})/\varepsilon_{\min} + \kappa^C$, and the number of evaluations of the derivatives
is at most $\kappa^S (f(x_0) - f_{\text{low}})/\varepsilon_{\min} + 2$ (4.1.38). Here $\kappa^S$
is the constant (4.1.45) with the terms of the orders $1$ and $2$, $\kappa^A = \kappa^S (1 +
|\log \gamma_1|/\log \gamma_2)$, and $\kappa^C$ is the constant (4.1.46).

**Reading.** As in `CartisGouldToint.Chapter04.theorem_4_1_5_i`, the theorem of the source is
split by the order of criticality, and this part uses only the constants of the orders $1$ and
$2$.

**Generalization.** The bounds $\varepsilon_1, \varepsilon_2 \le 1$ of the source are not needed
and are dropped.

The constant $\kappa^S$ is `CartisGouldToint.Chapter04.kappaSARp P p L 2`. The hypotheses
$\varepsilon_1, \varepsilon_2 > 0$ and $p \ge 2$ follow from the run predicate. -/
theorem theorem_4_1_5_ii (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionDpL f p L)
    {e₂ : ℝ} (h : algorithm_4_1_1 f p P ε₁ (some e₂) none x s σ) :
    ∃ kε, IsFirstHit (fun k => Chapter03.IsApproxSecondOrderMinimizer f (x k) ε₁ e₂) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaSARp P p L 2 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        (f (x 0) - flow) / min (ε₁ ^ (((p : ℝ) + 1) / p)) (e₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) +
          kappaCARp P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        kappaSARp P p L 2 * (f (x 0) - flow) /
          min (ε₁ ^ (((p : ℝ) + 1) / p)) (e₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) + 2 := by
  have hκ := kappaSARp_pos (P := P) (p := p) hf.nonneg 2
  have hε := h.ε₁_pos
  have he₂ := h.ε₂_pos e₂ rfl
  have hp2 := h.two_le_p (by simp)
  set a := ((p : ℝ) + 1) / p
  set b := ((p : ℝ) + 1) / ((p : ℝ) - 1)
  have hb0 : 0 ≤ b := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    exact div_nonneg (by linarith) (by linarith)
  set T := min (ε₁ ^ a) (e₂ ^ b)
  have hT : 0 < T := lt_min (Real.rpow_pos_of_pos hε _) (Real.rpow_pos_of_pos he₂ _)
  set δ := T / kappaSARp P p L 2
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ = kappaSARp P p L 2 * (f (x 0) - flow) / T := by
    simp only [δ]; field_simp
  have htest : arpTest f p P ε₁ (some e₂) none x s σ =
      fun k => Chapter03.IsApproxSecondOrderMinimizer f (x k) ε₁ e₂ := by
    funext k
    rw [arpTest, arpStopTest_none_right (by simpa using he₂.le), Chapter03.stopTest_some]
  obtain ⟨kε, hk, hF, hD⟩ := h.exists_isFirstHit_of_decrease hb hf hδ fun k hk hs => by
    have hk' : ∀ j ≤ k, ¬ arpTest f p P ε₁ (some e₂) none x s σ j :=
      fun j hj => hk j (hj.trans k.le_succ)
    have hfail := hk (k + 1) le_rfl
    rw [htest] at hfail
    have hfail' : ε₁ < ‖gradient f (x (k + 1))‖ ∨
        Chapter01.hessianMinEig f (x (k + 1)) < -e₂ := by
      rw [← Chapter03.not_stopTest_some, Chapter03.stopTest_some]; exact hfail
    rcases hfail' with hg | hl
    · exact div_le_of_decrease hκ (one_le_kappaSARp_mul_kappaARp₁ hf.nonneg 2)
        (kappaARp₁_nonneg hf.nonneg) (min_le_left _ _) hε.le hg.le (by positivity)
        (lemma_4_1_4_i hf h hk' hs).2
    · exact div_le_of_decrease hκ (one_le_kappaSARp_mul_kappaARp₂ hf.nonneg le_rfl)
        (kappaARp₂_nonneg hf.nonneg) (min_le_right _ _) he₂.le
        ((by linarith : e₂ ≤ -Chapter01.hessianMinEig f (x (k + 1))).trans (le_max_right _ _))
        hb0 (lemma_4_1_4_ii hf h (by simp) hk' hs)
  rw [hNδ] at hF hD
  refine ⟨kε, htest ▸ hk, ?_, hD⟩
  calc (funEvalCount kε : ℝ) ≤ _ := hF
    _ = _ := by ring

/-- **Theorem 4.1.5** of [cartis2022evaluation], third-order case
($\varepsilon_2, \varepsilon_3 < \infty$). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.Bb
with lower bound $f_{\text{low}}$ and f.DpL with constant $L_{f,p}$, and let
$(x_k, s_k, \sigma_k)$ be a run of ARp with tolerances $\varepsilon_1$ and finite
$\varepsilon_2, \varepsilon_3$. Then the run terminates at a first iteration $k_\varepsilon$ at
which the test (4.1.5)–(4.1.9) holds. With
$$\varepsilon_{\min} = \min\left(\varepsilon_1^{(p+1)/p}, \varepsilon_2^{(p+1)/(p-1)},
  \varepsilon_3^{(p+1)/(p-2)}\right),$$
the number of evaluations of $f$ satisfies $k_\varepsilon + 1 \le \kappa^A (f(x_0) -
f_{\text{low}})/\varepsilon_{\min} + \kappa^C$, and the number of evaluations of the derivatives
is at most $\kappa^S (f(x_0) - f_{\text{low}})/\varepsilon_{\min} + 2$ (4.1.38), with $\kappa^S$
the constant (4.1.45), $\kappa^A = \kappa^S (1 + |\log \gamma_1|/\log \gamma_2)$ and $\kappa^C$
the constant (4.1.46). At $x_\varepsilon = x_{k_\varepsilon}$, with $\mathcal{M}_\varepsilon =
\mathcal{M}_{k_\varepsilon}$, the point $x_\varepsilon$ is an
$(\varepsilon_1, \varepsilon_2)$-approximate second-order minimizer, and either
$\lambda_{\min}[\nabla^2 f(x_\varepsilon)] > \varepsilon_2$ (an approximate strict local
minimizer, with $\mathcal{Z}_\varepsilon = \emptyset$), or $\mathcal{M}_\varepsilon \subseteq
\mathcal{Z}_\varepsilon$ and $|\nabla^3 f(x_\varepsilon)[d]^3| \le \varepsilon_3$ for all
$d \in \mathcal{M}_\varepsilon$.

**Reading.** As in `CartisGouldToint.Chapter04.theorem_4_1_5_i`, the theorem of the source is
split by the order of criticality.

**Generalization.** The bounds $\varepsilon_1, \varepsilon_2, \varepsilon_3 \le 1$ of the source
are not needed and are dropped.

The conclusion is the one of the source. It is weaker than (4.1.3)–(4.1.4), because the
third-order condition is only known on $\mathcal{M}_\varepsilon$; compare §6.2.1 of the source.
Runs need not exist in this case
(`CartisGouldToint.Chapter04.not_exists_algorithm_4_1_1_third_order`), so the theorem is a
statement about the runs that exist. The constant $\kappa^S$ is
`CartisGouldToint.Chapter04.kappaSARp P p L 3`. -/
theorem theorem_4_1_5_iii (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionDpL f p L)
    {e₂ e₃ : ℝ} (h : algorithm_4_1_1 f p P ε₁ (some e₂) (some e₃) x s σ) :
    ∃ kε, IsFirstHit (arpTest f p P ε₁ (some e₂) (some e₃) x s σ) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaSARp P p L 3 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        (f (x 0) - flow) / min (ε₁ ^ (((p : ℝ) + 1) / p))
          (min (e₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) (e₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)))) +
          kappaCARp P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        kappaSARp P p L 3 * (f (x 0) - flow) / min (ε₁ ^ (((p : ℝ) + 1) / p))
          (min (e₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) (e₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)))) +
          2 ∧
      Chapter03.IsApproxSecondOrderMinimizer f (x kε) ε₁ e₂ ∧
      (e₂ < Chapter01.hessianMinEig f (x kε) ∨
        (arpCurvSet f p P (some e₂) x s σ kε ⊆ smallCurvatureSet f (x kε) e₂ ∧
          ∀ d ∈ arpCurvSet f p P (some e₂) x s σ kε,
            |iteratedFDeriv ℝ 3 f (x kε) (fun _ => d)| ≤ e₃)) := by
  have hκ := kappaSARp_pos (P := P) (p := p) hf.nonneg 3
  have hε := h.ε₁_pos
  have he₂ := h.ε₂_pos e₂ rfl
  have he₃ := h.ε₃_pos e₃ rfl
  have hp3 := h.three_le_p (by simp)
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  set a := ((p : ℝ) + 1) / p
  set b := ((p : ℝ) + 1) / ((p : ℝ) - 1)
  set c := ((p : ℝ) + 1) / ((p : ℝ) - 2)
  have hb0 : 0 ≤ b := div_nonneg (by linarith) (by linarith)
  have hc0 : 0 ≤ c := div_nonneg (by linarith) (by linarith)
  set T := min (ε₁ ^ a) (min (e₂ ^ b) (e₃ ^ c))
  have hT : 0 < T := lt_min (Real.rpow_pos_of_pos hε _)
    (lt_min (Real.rpow_pos_of_pos he₂ _) (Real.rpow_pos_of_pos he₃ _))
  set δ := T / kappaSARp P p L 3
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ = kappaSARp P p L 3 * (f (x 0) - flow) / T := by
    simp only [δ]; field_simp
  have hs2 : 0 < kappaS2ARp P p L := by
    have := constant_pos (P := P) hf.nonneg _ P.θ₂_pos (p - 1)
    unfold kappaS2ARp; positivity
  obtain ⟨kε, hk, hF, hD⟩ := h.exists_isFirstHit_of_decrease hb hf hδ fun k hk hs => by
    have hk' : ∀ j ≤ k, ¬ arpTest f p P ε₁ (some e₂) (some e₃) x s σ j :=
      fun j hj => hk j (hj.trans k.le_succ)
    have hfail := not_arpStopTest_some_some.1 (hk (k + 1) le_rfl)
    rcases hfail with hg | ⟨-, hl | ⟨d, hd, h3 | h2⟩⟩
    · exact div_le_of_decrease hκ (one_le_kappaSARp_mul_kappaARp₁ hf.nonneg 3)
        (kappaARp₁_nonneg hf.nonneg) (min_le_left _ _) hε.le hg.le (by positivity)
        (lemma_4_1_4_i hf h hk' hs).2
    · exact div_le_of_decrease hκ (one_le_kappaSARp_mul_kappaARp₂ hf.nonneg (by norm_num))
        (kappaARp₂_nonneg hf.nonneg) ((min_le_right _ _).trans (min_le_left _ _)) he₂.le
        ((by linarith : e₂ ≤ -Chapter01.hessianMinEig f (x (k + 1))).trans (le_max_right _ _))
        hb0 (lemma_4_1_4_ii hf h (by simp) hk' hs)
    · exact div_le_of_decrease hκ (one_le_kappaSARp_mul_kappaARp₃ hf.nonneg le_rfl)
        (kappaARp₃_nonneg hf.nonneg) ((min_le_right _ _).trans (min_le_right _ _)) he₃.le
        h3.le hc0 (lemma_4_1_4_iii hf h (by simp) hk' hs d hd)
    · -- (4.1.43): a direction of `𝓜_{k+1}` with large curvature forces a long step
      have hiv := lemma_4_1_3_iv hf h (by simp) hk' hs d hd
      have hstep : kappaS2ARp P p L * e₂ ≤ ‖s k‖ ^ (p - 1) := by
        have := h2.le.trans hiv
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs2] at this
        linarith
      have h37 := (lemma_4_1_4_i hf h hk' hs).1
      have hcm : b = ((p + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
        simp only [b]; rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hpow : (kappaS2ARp P p L * e₂) ^ b ≤ ‖s k‖ ^ (p + 1) := by
        rw [hcm]
        exact Real.rpow_div_le_pow_of_le_pow (by positivity) (norm_nonneg _) (by omega) hstep
      have hD : kappaARp₂ P p L * e₂ ^ b ≤ f (x k) - f (x (k + 1)) := by
        rw [kappaARp₂_eq, mul_assoc, ← Real.mul_rpow hs2.le he₂.le]
        have := P.η₁_pos; have := P.σmin_pos
        exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans h37
      exact (div_le_mul_of_one_le hκ (one_le_kappaSARp_mul_kappaARp₂ hf.nonneg (by norm_num))
        ((min_le_right _ _).trans (min_le_left _ _)) (by positivity)).trans hD
  rw [hNδ] at hF hD
  have hcert := arpStopTest_some_some_certificate he₂.le
    (fun d hd => norm_eq_one_of_mem_arpCurvSet hd) hk.test
  refine ⟨kε, hk, ?_, hD, hcert.1, ?_⟩
  · calc (funEvalCount kε : ℝ) ≤ _ := hF
      _ = _ := by ring
  · rcases hcert.2 with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, h2.2⟩

end Complexity


section WellPosedness

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)

/-! ### Third-order runs need not exist -/

section Counterexample

variable (a b : ℝ)

/-- The quartic $G(t) = a t^2/2 + b t^3/3 + t^4$ of the counterexample to the existence of ARp runs
with $\varepsilon_3 < \infty$
(`CartisGouldToint.Chapter04.not_exists_algorithm_4_1_1_third_order`). -/
noncomputable def arpQuartic (t : ℝ) : ℝ := a * t ^ 2 / 2 + b * t ^ 3 / 3 + t ^ 4

private theorem hasDerivAt_arpQuartic (t : ℝ) :
    HasDerivAt (arpQuartic a b) (a * t + b * t ^ 2 + 4 * t ^ 3) t := by
  have h1 := ((hasDerivAt_pow 2 t).const_mul a).div_const 2
  have h2 := ((hasDerivAt_pow 3 t).const_mul b).div_const 3
  have h3 := hasDerivAt_pow 4 t
  convert (h1.add h2).add h3 using 1
  · funext s; simp only [arpQuartic, Pi.add_apply]
  · norm_num; ring

private theorem deriv_arpQuartic :
    deriv (arpQuartic a b) = fun t => a * t + b * t ^ 2 + 4 * t ^ 3 :=
  funext fun t => (hasDerivAt_arpQuartic a b t).deriv

private theorem deriv2_arpQuartic :
    deriv (fun t : ℝ => a * t + b * t ^ 2 + 4 * t ^ 3) = fun t => a + 2 * b * t + 12 * t ^ 2 := by
  funext t
  have h1 := (hasDerivAt_id t).const_mul a
  have h2 := (hasDerivAt_pow 2 t).const_mul b
  have h3 := (hasDerivAt_pow 3 t).const_mul 4
  have h : HasDerivAt (fun t : ℝ => a * t + b * t ^ 2 + 4 * t ^ 3)
      (a + 2 * b * t + 12 * t ^ 2) t := by
    convert (h1.add h2).add h3 using 1
    · funext s; simp only [Pi.add_apply, id]
    · norm_num; ring
  exact h.deriv

private theorem deriv3_arpQuartic :
    deriv (fun t : ℝ => a + 2 * b * t + 12 * t ^ 2) = fun t => 2 * b + 24 * t := by
  funext t
  have h1 := ((hasDerivAt_id t).const_mul (2 * b)).const_add a
  have h3 := (hasDerivAt_pow 2 t).const_mul 12
  have h : HasDerivAt (fun t : ℝ => a + 2 * b * t + 12 * t ^ 2) (2 * b + 24 * t) t := by
    convert h1.add h3 using 1
    · funext s; simp only [Pi.add_apply, id]
    · norm_num; ring
  exact h.deriv

/-- The first derivative of the quartic is $G'(t) = a t + b t^2 + 4 t^3$. -/
theorem iteratedDeriv_one_arpQuartic :
    iteratedDeriv 1 (arpQuartic a b) = fun t => a * t + b * t ^ 2 + 4 * t ^ 3 := by
  rw [iteratedDeriv_one, deriv_arpQuartic]

/-- The second derivative of the quartic is $G''(t) = a + 2 b t + 12 t^2$. -/
theorem iteratedDeriv_two_arpQuartic :
    iteratedDeriv 2 (arpQuartic a b) = fun t => a + 2 * b * t + 12 * t ^ 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one_arpQuartic, deriv2_arpQuartic]

/-- The third derivative of the quartic is $G'''(t) = 2 b + 24 t$. -/
theorem iteratedDeriv_three_arpQuartic :
    iteratedDeriv 3 (arpQuartic a b) = fun t => 2 * b + 24 * t := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_arpQuartic, deriv3_arpQuartic]

/-- The quartic is smooth of the highest order (`ContDiff ℝ ⊤`). -/
theorem contDiff_arpQuartic : ContDiff ℝ ⊤ (arpQuartic a b) := by
  unfold arpQuartic
  fun_prop

end Counterexample

/-- **Algorithm 4.1.1** of [cartis2022evaluation] with $\varepsilon_3 < \infty$ is not always well
defined. Let the constants of ARp be given, let $\varepsilon_1 \in \mathbb{R}$, and let
$\varepsilon_2, \varepsilon_3 > 0$ with $4 \varepsilon_3^2 \le 3 \varepsilon_2 \sigma_0$. Let
$$f(x) = \frac{\varepsilon_2}{2} x^2 + \frac{\varepsilon_3}{3} x^3 + x^4$$
on $\mathbb{R}^1$. Then $f$ satisfies f.Bb with $f_{\text{low}} = -\varepsilon_3^4$ and f.DpL
with $p = 3$ and $L_{f,3} = 24$, but no run of ARp with $p = 3$ and tolerances
$\varepsilon_1, \varepsilon_2, \varepsilon_3$ starts at $x_0 = 0$.

**Correction.** The source takes for granted that a step satisfying Step 2 exists whenever the
termination test fails. Here the test fails at $0$: $\nabla f(0) = 0$,
$\lambda_{\min}[\nabla^2 f(0)] = \varepsilon_2$, $\mathcal{M}_0 = \{\pm 1\}$ and $|\nabla^3
f(0)[1]^3| = 2 \varepsilon_3 > \varepsilon_3$. But the model satisfies $m_0(s) - m_0(0) = s^2
(\varepsilon_2/2 + \varepsilon_3 s/3 + \sigma_0 s^2/24) \ge 0$, so no step satisfies (4.1.10).
Theorem 4.1.5 in the third-order case is therefore a statement about the runs that exist.

The function is the ridge function `Optimization.ridge (CartisGouldToint.Chapter04.arpQuartic ε₂
ε₃) CartisGouldToint.Chapter02.e₀`, that is, $x \mapsto G(\langle e_0, x\rangle)$. For
$\varepsilon_1 \le 0$ the last claim holds trivially, because a run requires
$\varepsilon_1 > 0$. -/
theorem not_exists_algorithm_4_1_1_third_order (P : ARpParams) {ε₁ e₂ e₃ : ℝ} (he₂ : 0 < e₂)
    (he₃ : 0 < e₃) (hσ : 4 * e₃ ^ 2 ≤ 3 * e₂ * P.σ₀) :
    Chapter02.AssumptionBb (ridge (arpQuartic e₂ e₃) e₀) (-e₃ ^ 4) ∧
      AssumptionDpL (ridge (arpQuartic e₂ e₃) e₀) 3 24 ∧
      ¬ ∃ x s σ, x 0 = 0 ∧
        algorithm_4_1_1 (ridge (arpQuartic e₂ e₃) e₀) 3 P ε₁ (some e₂) (some e₃) x s σ := by
  have hG : ContDiff ℝ ⊤ (arpQuartic e₂ e₃) := contDiff_arpQuartic e₂ e₃
  have hG3 : ContDiff ℝ 3 (arpQuartic e₂ e₃) := hG.of_le le_top
  refine ⟨fun y => ?_, ?_, ?_⟩
  · simp only [ridge_apply, arpQuartic]
    set t := ⟪e₀, y⟫
    nlinarith [sq_nonneg (t ^ 2 + e₃ * t / 6), sq_nonneg (e₃ ^ 2 - 0), sq_nonneg t,
      sq_nonneg (e₃ * t), sq_nonneg (t + e₃), mul_pos he₂ he₂, sq_nonneg (e₂ * t),
      sq_nonneg (t ^ 2 - e₃ ^ 2), sq_nonneg (e₃ * t + 2 * e₃ ^ 2)]
  · refine .of_iteratedFDerivLipschitzOn (contDiff_ridge hG3) (by norm_num) ?_
    refine iteratedFDerivLipschitzOn_ridge hG3 le_rfl norm_e₀.le (by norm_num) fun s t => ?_
    rw [iteratedDeriv_three_arpQuartic]
    simp only
    rw [show 2 * e₃ + 24 * s - (2 * e₃ + 24 * t) = 24 * (s - t) by ring, abs_mul]
    norm_num
  · rintro ⟨x, s, σ, hx0, h⟩
    have hd2 : ∀ d : EuclideanSpace ℝ (Fin 1),
        iteratedFDeriv ℝ 2 (ridge (arpQuartic e₂ e₃) e₀) (x 0) (fun _ => d) =
          e₂ * ⟪e₀, d⟫ ^ 2 := fun d => by
      rw [iteratedFDeriv_ridge_apply_diag hG (by exact_mod_cast le_top), hx0, inner_zero_right,
        iteratedDeriv_two_arpQuartic]
      ring
    have hd3 : ∀ d : EuclideanSpace ℝ (Fin 1),
        iteratedFDeriv ℝ 3 (ridge (arpQuartic e₂ e₃) e₀) (x 0) (fun _ => d) =
          2 * e₃ * ⟪e₀, d⟫ ^ 3 := fun d => by
      rw [iteratedFDeriv_ridge_apply_diag hG (by exact_mod_cast le_top), hx0, inner_zero_right,
        iteratedDeriv_three_arpQuartic]
      ring
    have he₀ : ⟪e₀, e₀⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_e₀]; norm_num
    -- the test fails at `x₀ = 0`
    have htest : ¬ arpTest (ridge (arpQuartic e₂ e₃) e₀) 3 P ε₁ (some e₂) (some e₃) x s σ 0 := by
      rw [arpTest, not_arpStopTest_some_some]
      have hlam : Chapter01.hessianMinEig (ridge (arpQuartic e₂ e₃) e₀) (x 0) = e₂ := by
        rw [Chapter03.hessianMinEig_ridge (hG.of_le le_top), hx0, inner_zero_right,
          iteratedDeriv_two_arpQuartic]
        ring
      refine Or.inr ⟨hlam.le, Or.inr ⟨e₀, ⟨norm_e₀, ?_⟩, Or.inl ?_⟩⟩
      · rw [hd2, he₀]; simp [abs_of_pos he₂]
      · rw [hd3, he₀, one_pow, mul_one, abs_of_pos (by linarith)]
        linarith
    have hstep := (h.step (k := 0) fun j hj => by
      rw [Nat.le_zero.1 hj]; exact htest).decrease
    rw [h.run.toIsARRun.sigma_zero] at hstep
    -- the model does not decrease
    set t := ⟪e₀, s 0⟫
    have hT : taylorPolynomial (ridge (arpQuartic e₂ e₃) e₀) 3 (x 0) (s 0) =
        arpQuartic e₂ e₃ 0 + e₂ * t ^ 2 / 2 + e₃ * t ^ 3 / 3 := by
      rw [Optimization.taylorPolynomial_ridge hG3, hx0, inner_zero_right]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero,
        iteratedDeriv_one_arpQuartic, iteratedDeriv_two_arpQuartic, iteratedDeriv_three_arpQuartic]
      norm_num [Nat.factorial]
      ring
    have hm : regularizedModel (ftaylorSeries ℝ (ridge (arpQuartic e₂ e₃) e₀) (x 0)) 3 P.σ₀ (s 0) -
        regularizedModel (ftaylorSeries ℝ (ridge (arpQuartic e₂ e₃) e₀) (x 0)) 3 P.σ₀ 0 =
          t ^ 2 * (e₂ / 2 + e₃ * t / 3 + P.σ₀ * t ^ 2 / 24) := by
      rw [regularizedModel_ftaylorSeries_zero_right, regularizedModel_def,
        ← taylorPolynomial_eq_taylorSum, hT, Chapter03.norm_eq_abs_inner_e₀, hx0]
      simp only [ridge_apply, inner_zero_right]
      rw [show 3 + 1 = 2 * 2 by rfl, pow_mul, sq_abs]
      norm_num [Nat.factorial]
      ring
    have hσ₀ := P.σ₀_pos
    have hq : 0 ≤ e₂ / 2 + e₃ * t / 3 + P.σ₀ * t ^ 2 / 24 := by
      nlinarith [sq_nonneg (P.σ₀ * t + 4 * e₃)]
    have := mul_nonneg (sq_nonneg t) hq
    linarith


end WellPosedness

/-! ### Theorem 4.1.6: sharpness of the complexity bounds -/

section Sharpness

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)
open Chapter03 (norm_eq_abs_inner_e₀ inner_e₀_sq)

/-- For a unit vector $d \in \mathbb{R}^1$, $|\langle e_0, d\rangle| = 1$. -/
theorem abs_inner_e₀_eq_one {d : EuclideanSpace ℝ (Fin 1)} (hd : ‖d‖ = 1) : |⟪e₀, d⟫| = 1 := by
  rw [← norm_eq_abs_inner_e₀, hd]

/-! ### The one-dimensional data -/

/-- The termination index $\lceil \varepsilon^{-(p+1)/(p-q+1)} \rceil$ of the one-dimensional ARp
examples for the order $q$, $1 \le q \le p$. -/
noncomputable def arpSlowK (p q : ℕ) (ε : ℝ) : ℕ :=
  ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊

/-- For $\varepsilon > 0$, the termination index $\lceil \varepsilon^{-(p+1)/(p-q+1)} \rceil$ is
positive. -/
theorem arpSlowK_pos {p q : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 < arpSlowK p q ε :=
  Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)

/-- For $q = 1$ and $p \ge 1$, the termination index is $\lceil \varepsilon^{-(p+1)/p} \rceil$. -/
theorem arpSlowK_one {p : ℕ} (hp : 1 ≤ p) (ε : ℝ) :
    arpSlowK p 1 ε = ⌈ε ^ (-(((p : ℝ) + 1) / p))⌉₊ := by
  rw [arpSlowK, Nat.sub_add_cancel hp]

/-- For $q = 2$ and $p \ge 2$, the termination index is $\lceil \varepsilon^{-(p+1)/(p-1)} \rceil$.
-/
theorem arpSlowK_two {p : ℕ} (hp : 2 ≤ p) (ε : ℝ) :
    arpSlowK p 2 ε = ⌈ε ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊ := by
  rw [arpSlowK, show p - 2 + 1 = p - 1 by omega, Nat.cast_sub (by omega), Nat.cast_one]

/-- For $q = 3$ and $p \ge 3$, the termination index is $\lceil \varepsilon^{-(p+1)/(p-2)} \rceil$.
-/
theorem arpSlowK_three {p : ℕ} (hp : 3 ≤ p) (ε : ℝ) :
    arpSlowK p 3 ε = ⌈ε ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 2)))⌉₊ := by
  rw [arpSlowK, show p - 3 + 1 = p - 2 by omega, Nat.cast_sub (by omega)]
  norm_num

/-- The one-dimensional data of the ARp examples: the data of Theorem 12.2.15 of
[cartis2022evaluation] with the scale $c = p!/((q-1)! \sigma_0)$
(`Optimization.exists_slowTaylorOrder_interpolant`). Let the constants of ARp be given and let
$1 \le q \le p$. There are $L \ge 1$ and $B \ge 0$ such that for every $\varepsilon \in (0, 1]$
the following holds, with $K = \lceil \varepsilon^{-(p+1)/(p-q+1)} \rceil$ and
$\alpha_k = \varepsilon + \varepsilon (K - k)/K$. There are a $C^p$ function
$G : \mathbb{R} \to \mathbb{R}$ and points $x_0 = 0, x_1, \dots, x_K$ such that the ridge
function $f(x) = G(\langle e_0, x\rangle)$ on $\mathbb{R}^1$ satisfies f.Bb with
$f_{\text{low}} = -B$ and f.DpL with constant $L$; at each $x_k$, $k \le K$, the derivatives of
$G$ of orders $1$ to $p$ vanish except $G^{(q)}(x_k) = -\alpha_k$; for $k < K$,
$x_{k+1} - x_k = t^*$ is the global minimizer of the one-dimensional model with weight
$\sigma_0$, where $t^* = (\alpha_k/\lambda)^{1/(p-q+1)}$ and $\lambda = \sigma_0 (q-1)!/p!$
(`Optimization.monomialMinimizer`); and $G(x_{k+1}) = G(x_k) - \alpha_k (x_{k+1} - x_k)^q/q!$,
which is the value $T_{f,p}(x_k, s_k)$ of the Taylor polynomial. -/
theorem exists_arp_slow_data (P : ARpParams) {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (G : ℝ → ℝ) (xr : ℕ → ℝ), ContDiff ℝ p G ∧
        Chapter02.AssumptionBb (ridge G e₀) (-B) ∧ AssumptionDpL (ridge G e₀) p L ∧ xr 0 = 0 ∧
        (∀ k ≤ arpSlowK p q ε,
          IsSpikeJetOf p G q (xr k) (Chapter03.ar2SlowAlpha ε (arpSlowK p q ε) k)) ∧
        (∀ k < arpSlowK p q ε, xr (k + 1) = xr k +
          monomialMinimizer p q P.σ₀ (Chapter03.ar2SlowAlpha ε (arpSlowK p q ε) k)) ∧
        ∀ k < arpSlowK p q ε, G (xr (k + 1)) = G (xr k) -
          Chapter03.ar2SlowAlpha ε (arpSlowK p q ε) k * (xr (k + 1) - xr k) ^ q / q ! := by
  have hσ₀ := P.σ₀_pos
  set c : ℝ := (p ! : ℝ) / (P.σ₀ * (q - 1)!)
  have hc : 0 < c := by positivity
  have hcα : ∀ α : ℝ, c * α = α / (P.σ₀ * (q - 1)! / p !) := fun α => by
    simp only [c]; field_simp
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowTaylorOrder_interpolant hq hqp hc
  refine ⟨max L 1, B, le_max_right _ _, hB, fun ε hε hε1 => ?_⟩
  set K := arpSlowK p q ε
  set xr : ℕ → ℝ := fun k => ∑ j ∈ range k,
    (c * (ε + ε * ((K : ℝ) - j) / K)) ^ (1 / ((p - q + 1 : ℕ) : ℝ))
  obtain ⟨G, hG, hGL, hGB, hGk, hGv⟩ := H ε K xr hε hε1 rfl
    (fun k _ => by simp only [xr, sum_range_succ])
  have hb : Chapter02.AssumptionBb (ridge G e₀) (-B) := fun y => by
    have := hGB 0 (by omega) ⟪e₀, y⟫
    rw [iteratedDeriv_zero] at this
    rw [ridge_apply]; linarith [neg_abs_le (G ⟪e₀, y⟫)]
  have hDpL : AssumptionDpL (ridge G e₀) p (max L 1) :=
    .of_iteratedFDerivLipschitzOn (contDiff_ridge hG) (le_max_right _ _)
      (iteratedFDerivLipschitzOn_ridge hG le_rfl norm_e₀.le (by positivity) fun s t =>
        (hGL s t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
  refine ⟨G, xr, hG, hb, hDpL, by simp [xr], fun k hk => hGk k hk, fun k _ => ?_,
    fun k hk => hGv k hk⟩
  simp only [xr, sum_range_succ, Chapter03.ar2SlowAlpha, monomialMinimizer, hcα]

/-! ### Ridge functions at the iterates -/

section RidgeAt

variable {p : ℕ} {G : ℝ → ℝ}

/-- For a $C^1$ function $G$ and the ridge function $f(x) = G(\langle e_0, x\rangle)$ on
$\mathbb{R}^1$, $\|\nabla f(a e_0)\| = |G'(a)|$. -/
theorem norm_gradient_ridge_e₀ (hG : ContDiff ℝ 1 G) (a : ℝ) :
    ‖gradient (ridge G e₀) (a • e₀)‖ = |iteratedDeriv 1 G a| := by
  rw [gradient_ridge (hG.differentiable one_ne_zero), inner_e₀_smul, norm_smul, norm_e₀, mul_one,
    Real.norm_eq_abs, iteratedDeriv_one]

/-- For a $C^2$ function $G$ and the ridge function $f(x) = G(\langle e_0, x\rangle)$ on
$\mathbb{R}^1$, $\lambda_{\min}[\nabla^2 f(a e_0)] = G''(a)$. -/
theorem hessianMinEig_ridge_e₀ (hG : ContDiff ℝ 2 G) (a : ℝ) :
    Chapter01.hessianMinEig (ridge G e₀) (a • e₀) = iteratedDeriv 2 G a := by
  rw [Chapter03.hessianMinEig_ridge hG, inner_e₀_smul]

/-- For a $C^p$ function $G$, the ridge function $f(x) = G(\langle e_0, x\rangle)$ on $\mathbb{R}^1$
and $j \le p$, $\nabla^j f(a e_0)[d]^j = G^{(j)}(a) \langle e_0, d\rangle^j$ for every
$d \in \mathbb{R}^1$. -/
theorem iteratedFDeriv_ridge_e₀ (hG : ContDiff ℝ p G) {j : ℕ} (hj : j ≤ p) (a : ℝ)
    (d : EuclideanSpace ℝ (Fin 1)) :
    iteratedFDeriv ℝ j (ridge G e₀) (a • e₀) (fun _ => d) = iteratedDeriv j G a * ⟪e₀, d⟫ ^ j := by
  rw [iteratedFDeriv_ridge_apply_diag hG (by exact_mod_cast hj), inner_e₀_smul]

/-- For a $C^p$ function $G$, the ridge function $f(x) = G(\langle e_0, x\rangle)$ on $\mathbb{R}^1$
and $j \le p$, $|\nabla^j f(a e_0)[d]^j| = |G^{(j)}(a)|$ for every unit vector $d$. -/
theorem abs_iteratedFDeriv_ridge_e₀ (hG : ContDiff ℝ p G) {j : ℕ} (hj : j ≤ p) (a : ℝ)
    {d : EuclideanSpace ℝ (Fin 1)} (hd : ‖d‖ = 1) :
    |iteratedFDeriv ℝ j (ridge G e₀) (a • e₀) (fun _ => d)| = |iteratedDeriv j G a| := by
  rw [iteratedFDeriv_ridge_e₀ hG hj, abs_mul, abs_pow, abs_inner_e₀_eq_one hd, one_pow, mul_one]

end RidgeAt

/-! ### The three cases of Theorem 4.1.6 -/

/-- **Theorem 4.1.6** of [cartis2022evaluation], first-order case: the bound of Theorem 4.1.5 for
$\varepsilon_2 = \varepsilon_3 = +\infty$ is sharp. Let $p \ge 1$ and let the constants of ARp
be given. There are $f_{\text{low}} \in \mathbb{R}$ and $L_{f,p} \ge 1$ such that for every
$\varepsilon_1 \in (0, 1]$ there are a function $f : \mathbb{R}^1 \to \mathbb{R}$ that satisfies
f.Bb and f.DpL and a run of ARp with $\varepsilon_2 = \varepsilon_3 = +\infty$ from $x_0 = 0$
with the following properties, where $K = \lceil \varepsilon_1^{-(p+1)/p} \rceil$:
$\sigma_k = \sigma_0$ for all $k$; for every $k < K$ the step $s_k$ is a global minimizer of the
model $m_k$ and $\rho_k = 1$; and $K$ is the first iteration with
$\|\nabla f(x_k)\| \le \varepsilon_1$.

Every iteration before termination is very successful, so the run makes $K + 1$ evaluations of
$f$ and of its derivatives. The source defers the proof to §12.2.2.4. The proof here uses the
one-dimensional data of Theorem 12.2.15 (`CartisGouldToint.Chapter04.exists_arp_slow_data`). -/
theorem theorem_4_1_6_i (P : ARpParams) {p : ℕ} (hp : 1 ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧ AssumptionDpL f p L ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_4_1_1 f p P ε₁ none none x s σ ∧ (∀ k, σ k = P.σ₀) ∧
          (∀ k < ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊,
            IsMinOn (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) univ (s k) ∧
              taylorRatio f p x s k = 1) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊ := by
  obtain ⟨L, B, hL, -, H⟩ := exists_arp_slow_data P le_rfl hp
  refine ⟨-B, L, hL, fun ε hε hε1 => ?_⟩
  obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H ε hε hε1
  have hK := arpSlowK_pos (p := p) (q := 1) hε
  set K := arpSlowK p 1 ε
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast hp)
  have htest : ∀ k ≤ K, (arpTest (ridge G e₀) p P ε none none (fun k => xr k • e₀)
      (fun k => (xr (k + 1) - xr k) • e₀) (fun _ => P.σ₀) k ↔ K ≤ k) := fun k hk => by
    rw [arpTest, arpStopTest_none, norm_gradient_ridge_e₀ hG1, (hd k hk).1, abs_neg,
      abs_of_pos (Chapter03.ar2SlowAlpha_pos hε hK hk)]
    exact Chapter03.ar2SlowAlpha_le_iff hε hK hk
  obtain ⟨hrun, hhit, hmin⟩ := arp_ridge_run P.toARpParams norm_e₀ norm_eq_abs_inner_e₀ (r := 1)
    le_rfl hp (by omega) (by omega) hG
    (fun k hk => Chapter03.ar2SlowAlpha_pos hε hK hk.le) (fun k hk => hd k hk.le) hx hv htest
  have htest' : arpTest (ridge G e₀) p P ε none none (fun k => xr k • e₀)
      (fun k => (xr (k + 1) - xr k) • e₀) (fun _ => P.σ₀) =
      fun k => ‖gradient (ridge G e₀) (xr k • e₀)‖ ≤ ε :=
    funext fun k => propext arpStopTest_none
  refine ⟨ridge G e₀, hb, hDpL, _, _, _, by rw [hx0, zero_smul],
    ⟨hp, by simpa using hp, hε, by simp, by simp, fun _ => rfl, hrun⟩, fun _ => rfl, ?_, ?_⟩
  · rw [← arpSlowK_one hp]; exact hmin
  · rw [← arpSlowK_one hp, ← htest']; exact hhit

/-- ARp runs on one-dimensional spike data. Let $1 \le q \le p$, let the tolerances satisfy the
conditions of Algorithm 4.1.1, and in the third-order case let $q \le 3 \le p$ and
$\sigma_0 \le (p-2)! \theta_3$. Let $G : \mathbb{R} \to \mathbb{R}$ be $C^p$, and let
$x_0 = 0, x_1, \dots, x_K \in \mathbb{R}$ and $\alpha_k > 0$ be such that for $k < K$ the
derivatives of $G$ of orders $1$ to $p$ at $x_k$ vanish except $G^{(q)}(x_k) = -\alpha_k$,
$x_{k+1} - x_k$ is the global minimizer of the one-dimensional model with weight $\sigma_0$, and
$G(x_{k+1}) = G(x_k) - \alpha_k (x_{k+1} - x_k)^q/q!$. Suppose that the termination test for the
iterates $x_k e_0$, the steps $(x_{k+1} - x_k) e_0$ and the weights $\sigma_0$ holds at
$k \le K$ exactly when $k = K$. Then there is an ARp run for the ridge function
$f(x) = G(\langle e_0, x\rangle)$ from $0$ with iterates $x_k e_0$ and $\sigma_k = \sigma_0$
that terminates exactly at iteration $K$. -/
theorem exists_algorithm_4_1_1_ridge (P : ARpParams) {p q : ℕ} {ε₁ : ℝ} {ε₂ ε₃ : Option ℝ}
    (hp : 1 ≤ p) (hord : arpOrder ε₂ ε₃ ≤ p) (hε₁ : 0 < ε₁) (hε₂ : ∀ e ∈ ε₂, 0 < e)
    (hε₃ : ∀ e ∈ ε₃, 0 < e) (h32 : ε₂ = none → ε₃ = none) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hthird : 3 ≤ arpOrder ε₂ ε₃ → q ≤ 3 ∧ 3 ≤ p ∧ P.σ₀ ≤ (p - 2)! * P.θ₃) {G : ℝ → ℝ}
    (hG : ContDiff ℝ p G) {xr α : ℕ → ℝ} {K : ℕ} (hα : ∀ k < K, 0 < α k)
    (hd : ∀ k < K, IsSpikeJetOf p G q (xr k) (α k))
    (hx : ∀ k < K, xr (k + 1) = xr k + monomialMinimizer p q P.σ₀ (α k))
    (hval : ∀ k < K, G (xr (k + 1)) = G (xr k) - α k * (xr (k + 1) - xr k) ^ q / q !)
    (hx0 : xr 0 = 0)
    (htest : ∀ k ≤ K, (arpTest (ridge G e₀) p P ε₁ ε₂ ε₃ (fun k => xr k • e₀)
      (fun k => (xr (k + 1) - xr k) • e₀) (fun _ => P.σ₀) k ↔ K ≤ k)) :
    ∃ x s σ, x 0 = 0 ∧ algorithm_4_1_1 (ridge G e₀) p P ε₁ ε₂ ε₃ x s σ ∧ (∀ k, σ k = P.σ₀) ∧
      IsFirstHit (arpTest (ridge G e₀) p P ε₁ ε₂ ε₃ x s σ) K ∧ ∀ k, x k = xr k • e₀ := by
  obtain ⟨hrun, hhit, -⟩ := arp_ridge_run P.toARpParams norm_e₀ norm_eq_abs_inner_e₀ hq hqp
    (fun h2 => h2.trans hord) hthird hG hα hd hx hval htest
  exact ⟨_, _, _, by simp only [hx0, zero_smul], ⟨hp, hord, hε₁, hε₂, hε₃, h32, hrun⟩,
    fun _ => rfl, hhit, fun _ => rfl⟩

/-- If a predicate on $\mathbb{N}$ holds at $k \le K$ exactly when $k = K$, then $K$ is the first
index at which it holds. -/
theorem isFirstHit_of_forall_le_iff {test : ℕ → Prop} {K : ℕ} (h : ∀ k ≤ K, (test k ↔ K ≤ k)) :
    IsFirstHit test K :=
  ⟨(h K le_rfl).2 le_rfl, fun j hj ht => absurd ((h j hj.le).1 ht) (not_le.2 hj)⟩

/-- **Theorem 4.1.6** of [cartis2022evaluation], second-order case: the bound of Theorem 4.1.5 for
$\varepsilon_2 < \infty = \varepsilon_3$ is sharp. Let $p \ge 2$ and let the constants of ARp be
given. There are $f_{\text{low}} \in \mathbb{R}$ and $L_{f,p} \ge 1$ such that for all
$\varepsilon_1, \varepsilon_2 \in (0, 1]$ there are a function $f : \mathbb{R}^1 \to \mathbb{R}$
that satisfies f.Bb and f.DpL and a run of ARp with tolerances $\varepsilon_1$, $\varepsilon_2$
and $\varepsilon_3 = +\infty$ from $x_0 = 0$, with $\sigma_k = \sigma_0$ for all $k$, whose
first $(\varepsilon_1, \varepsilon_2)$-approximate second-order minimizer, and thus its
termination iterate, is $x_K$ with
$$K = \max\left(\lceil \varepsilon_1^{-(p+1)/p} \rceil, \lceil \varepsilon_2^{-(p+1)/(p-1)}
  \rceil\right).$$

If the first term is the larger, the proof uses the example of the first-order case, which has
zero curvature. Otherwise it uses an example with zero gradients and
$\lambda_{\min}[\nabla^2 f(x_k)] = -\alpha_k$, $\alpha_k = \varepsilon_2 + \varepsilon_2 (K -
k)/K$. -/
theorem theorem_4_1_6_ii (P : ARpParams) {p : ℕ} (hp : 2 ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε₁ e₂ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < e₂ → e₂ ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧ AssumptionDpL f p L ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_4_1_1 f p P ε₁ (some e₂) none x s σ ∧
          (∀ k, σ k = P.σ₀) ∧
          IsFirstHit (fun k => Chapter03.IsApproxSecondOrderMinimizer f (x k) ε₁ e₂)
            (max ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊ ⌈e₂ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊) := by
  obtain ⟨L₁, B₁, hL₁, -, H₁⟩ := exists_arp_slow_data P le_rfl (by omega : 1 ≤ p)
  obtain ⟨L₂, B₂, -, -, H₂⟩ := exists_arp_slow_data P (q := 2) (by norm_num) hp
  refine ⟨-max B₁ B₂, max L₁ L₂, hL₁.trans (le_max_left _ _),
    fun ε₁ e₂ hε₁ hε₁1 he₂ he₂1 => ?_⟩
  have hord : arpOrder (some e₂) none ≤ p := by simpa using hp
  have hG2 : ∀ {G : ℝ → ℝ}, ContDiff ℝ p G → ContDiff ℝ 2 G := fun hG =>
    hG.of_le (by exact_mod_cast hp)
  have hsecond : ∀ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin 1))
      (σ : ℕ → ℝ), arpTest f p P ε₁ (some e₂) none x s σ =
        fun k => Chapter03.IsApproxSecondOrderMinimizer f (x k) ε₁ e₂ := fun f x s σ => by
    funext k
    rw [arpTest, arpStopTest_none_right (by simpa using he₂.le), Chapter03.stopTest_some]
  rcases le_total ⌈e₂ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊ ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊
    with hle | hle
  · -- the first-order example
    rw [max_eq_left hle, ← arpSlowK_one (by omega)]
    obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H₁ ε₁ hε₁ hε₁1
    have hK := arpSlowK_pos (p := p) (q := 1) hε₁
    obtain ⟨x, s, σ, hx0', halg, hσ, hhit, -⟩ :=
      exists_algorithm_4_1_1_ridge P (by omega) hord hε₁
      (by simpa using he₂) (by simp) (by simp) le_rfl (by omega) (by simp) hG
      (fun k hk => Chapter03.ar2SlowAlpha_pos hε₁ hK hk.le) (fun k hk => hd k hk.le) hx hv hx0
      fun k hk => by
        rw [hsecond]
        dsimp only
        rw [Chapter03.isApproxSecondOrderMinimizer_def, norm_gradient_ridge_e₀
          (hG.of_le (by exact_mod_cast (by omega : 1 ≤ p))), hessianMinEig_ridge_e₀ (hG2 hG),
          (hd k hk).1, (hd k hk).2 2 (by norm_num) hp (by norm_num), abs_neg,
          abs_of_pos (Chapter03.ar2SlowAlpha_pos hε₁ hK hk),
          ← Chapter03.ar2SlowAlpha_le_iff hε₁ hK hk]
        exact ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩
    refine ⟨ridge G e₀, fun y => (hb y).trans' (by linarith [le_max_left B₁ B₂]),
      hDpL.mono (le_max_left _ _), x, s, σ, hx0', halg, hσ, ?_⟩
    rw [← hsecond (ridge G e₀) x s σ]; exact hhit
  · -- the negative-curvature example
    rw [max_eq_right hle, ← arpSlowK_two hp]
    obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H₂ e₂ he₂ he₂1
    have hK := arpSlowK_pos (p := p) (q := 2) he₂
    obtain ⟨x, s, σ, hx0', halg, hσ, hhit, -⟩ :=
      exists_algorithm_4_1_1_ridge P (by omega) hord hε₁
      (by simpa using he₂) (by simp) (by simp) (by norm_num) hp (by simp) hG
      (fun k hk => Chapter03.ar2SlowAlpha_pos he₂ hK hk.le) (fun k hk => hd k hk.le) hx hv hx0
      fun k hk => by
        rw [hsecond]
        dsimp only
        rw [Chapter03.isApproxSecondOrderMinimizer_def, norm_gradient_ridge_e₀
          (hG.of_le (by exact_mod_cast (by omega : 1 ≤ p))), hessianMinEig_ridge_e₀ (hG2 hG),
          (hd k hk).1, (hd k hk).2 1 le_rfl (by omega) (by norm_num), abs_zero, neg_le_neg_iff,
          ← Chapter03.ar2SlowAlpha_le_iff he₂ hK hk]
        exact ⟨fun h => h.2, fun h => ⟨hε₁.le, h⟩⟩
    refine ⟨ridge G e₀, fun y => (hb y).trans' (by linarith [le_max_right B₁ B₂]),
      hDpL.mono (le_max_right _ _), x, s, σ, hx0', halg, hσ, ?_⟩
    rw [← hsecond (ridge G e₀) x s σ]; exact hhit

/-- With finite tolerances, the termination test holds at $x$ when
$\|\nabla f(x)\| \le \varepsilon_1$, $\lambda_{\min}[\nabla^2 f(x)] \ge -\varepsilon_2$, and
every $d \in M$ satisfies (4.1.8) and (4.1.9). -/
theorem arpStopTest_some_some_of {f : EuclideanSpace ℝ (Fin n) → ℝ} {ε₁ e₂ e₃ : ℝ}
    {M : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hg : ‖gradient f x‖ ≤ ε₁) (hl : -e₂ ≤ Chapter01.hessianMinEig f x)
    (hM : ∀ d ∈ M, |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ e₃ ∧
      |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ e₂) :
    arpStopTest f ε₁ (some e₂) (some e₃) M x :=
  ⟨hg, fun e he => by
    cases he
    exact Or.inr ⟨hl, fun e' he' d hd => by cases he'; exact hM d hd⟩⟩

/-- **Theorem 4.1.6** of [cartis2022evaluation], third-order case: the bound of Theorem 4.1.5 for
finite $\varepsilon_2, \varepsilon_3$ is sharp, under a restriction on the constants. Let
$p \ge 3$ and let the constants of ARp satisfy $\sigma_0 \le (p-2)! \min(\theta_2, \theta_3)$.
There are $f_{\text{low}} \in \mathbb{R}$ and $L_{f,p} \ge 1$ such that for all $\varepsilon_1,
\varepsilon_2, \varepsilon_3 \in (0, 1]$ there are a function $f : \mathbb{R}^1 \to \mathbb{R}$
that satisfies f.Bb and f.DpL and a run of ARp with these tolerances from $x_0 = 0$, with
$\sigma_k = \sigma_0$ for all $k$, that terminates exactly at iteration
$$K = \max\left(\lceil \varepsilon_1^{-(p+1)/p} \rceil, \lceil \varepsilon_2^{-(p+1)/(p-1)}
  \rceil, \lceil \varepsilon_3^{-(p+1)/(p-2)} \rceil\right).$$
Moreover $x_K$ is also the first iterate that is an $\varepsilon$-approximate third-order
minimizer in the sense of (4.1.3)–(4.1.4). The bound is thus sharp for the true criterion as
well as for the test of the algorithm.

**Correction.** The source states this case for all constants and defers the proof to §12.2.2.4.
In that proof the sign of $\lambda_{\min}$ is wrong: the source has $\lambda_{\min} =
f_k^{(2)} = \varepsilon + \omega_k$, but $\lambda_{\min} = -(\varepsilon + \omega_k)$, where
$\omega_k \ge 0$ is the perturbation of the example (in the data used here,
$\omega_k = \varepsilon (K - k)/K$). Here the case is proved under the restriction
$\sigma_0 \le (p-2)! \min(\theta_2, \theta_3)$. The bound $\sigma_0 \le (p-2)! \theta_3$ makes
the global model minimizers satisfy (4.1.13), and the bound $\sigma_0 \le (p-2)! \theta_2$ keeps
$\pm e_0$ in the sets $\mathcal{M}_{k+1}$ of the third-order example, so that its test fails
before the last iteration. For other constants the claim is unproved. If
$\pm e_0 \notin \mathcal{M}_{k+1}$, then $\mathcal{M}_{k+1} = \emptyset$. With the vacuous
reading of Step 1 the test then holds as soon as $\|\nabla f\| \le \varepsilon_1$ and
$\lambda_{\min} \ge -\varepsilon_2$, and with the requirement $\mathcal{M}_k \neq \emptyset$ of
the source the run cannot terminate at all.

The restriction is sufficient but not necessary. The exact conditions are weaker and depend on
the example; for the third-order example they are $\sigma_0 (p-2)/p! \le \theta_2$ and
$\sigma_0 (1/(p-2)! - 2/p!) \le \theta_3$. The third-order approximate minimizer is
`CartisGouldToint.Chapter04.IsApproxThirdOrderMinimizer`. -/
theorem theorem_4_1_6_iii (P : ARpParams) {p : ℕ} (hp : 3 ≤ p)
    (hσ : P.σ₀ ≤ (p - 2)! * min P.θ₂ P.θ₃) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε₁ e₂ e₃ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < e₂ → e₂ ≤ 1 → 0 < e₃ → e₃ ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧ AssumptionDpL f p L ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_4_1_1 f p P ε₁ (some e₂) (some e₃) x s σ ∧
          (∀ k, σ k = P.σ₀) ∧
          IsFirstHit (arpTest f p P ε₁ (some e₂) (some e₃) x s σ)
            (max (max ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊
              ⌈e₂ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊)
              ⌈e₃ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 2)))⌉₊) ∧
          IsFirstHit (fun k => IsApproxThirdOrderMinimizer f (x k) ε₁ e₂ e₃)
            (max (max ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊
              ⌈e₂ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊)
              ⌈e₃ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 2)))⌉₊) := by
  obtain ⟨L₁, B₁, hL₁, -, H₁⟩ := exists_arp_slow_data P le_rfl (by omega : 1 ≤ p)
  obtain ⟨L₂, B₂, -, -, H₂⟩ := exists_arp_slow_data P (p := p) (q := 2) (by norm_num) (by omega)
  obtain ⟨L₃, B₃, -, -, H₃⟩ := exists_arp_slow_data P (q := 3) (by norm_num) hp
  refine ⟨-max B₁ (max B₂ B₃), max L₁ (max L₂ L₃), hL₁.trans (le_max_left _ _),
    fun ε₁ e₂ e₃ hε₁ hε₁1 he₂ he₂1 he₃ he₃1 => ?_⟩
  have hord : arpOrder (some e₂) (some e₃) ≤ p := by simpa using hp
  have hσ₀ := P.σ₀_pos
  have hthird : 3 ≤ arpOrder (some e₂) (some e₃) → ∀ q, q ≤ 3 →
      q ≤ 3 ∧ 3 ≤ p ∧ P.σ₀ ≤ (p - 2)! * P.θ₃ := fun _ q hq =>
    ⟨hq, hp, hσ.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))⟩
  have hG' : ∀ {G : ℝ → ℝ}, ContDiff ℝ p G → ContDiff ℝ 1 G ∧ ContDiff ℝ 2 G := fun hG =>
    ⟨hG.of_le (by exact_mod_cast (by omega : 1 ≤ p)), hG.of_le (by exact_mod_cast (by omega))⟩
  have hunit : ∀ {x s : ℕ → EuclideanSpace ℝ (Fin 1)} {σ : ℕ → ℝ} {k : ℕ} {d}
      {f : EuclideanSpace ℝ (Fin 1) → ℝ}, d ∈ arpCurvSet f p P (some e₂) x s σ k → ‖d‖ = 1 :=
    fun hd => norm_eq_one_of_mem_arpCurvSet hd
  set A := ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊
  set B := ⌈e₂ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊
  set C := ⌈e₃ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 2)))⌉₊
  rcases (by omega : (B ≤ A ∧ C ≤ A) ∨ (A ≤ B ∧ C ≤ B) ∨ (A ≤ C ∧ B ≤ C)) with hm | hm | hm
  · -- the first-order example
    rw [show max (max A B) C = A by omega,
      show A = arpSlowK p 1 ε₁ from (arpSlowK_one (by omega) _).symm]
    obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H₁ ε₁ hε₁ hε₁1
    have hK := arpSlowK_pos (p := p) (q := 1) hε₁
    obtain ⟨x, s, σ, hx0', halg, hσ', hhit, hxk⟩ :=
      exists_algorithm_4_1_1_ridge P (by omega) hord hε₁
      (by simpa using he₂) (by simpa using he₃) (by simp) le_rfl (by omega)
      (fun h => hthird h 1 (by norm_num)) hG
      (fun k hk => Chapter03.ar2SlowAlpha_pos hε₁ hK hk.le) (fun k hk => hd k hk.le) hx hv hx0
      fun k hk => by
        have hα := Chapter03.ar2SlowAlpha_pos hε₁ hK hk
        have hg : ‖gradient (ridge G e₀) (xr k • e₀)‖ =
            Chapter03.ar2SlowAlpha ε₁ (arpSlowK p 1 ε₁) k := by
          rw [norm_gradient_ridge_e₀ (hG' hG).1, (hd k hk).1, abs_neg, abs_of_pos hα]
        rcases hk.lt_or_eq with hlt | rfl
        · refine iff_of_false (not_arpStopTest_some_some.2 (Or.inl ?_)) (not_le.2 hlt)
          rw [hg]
          exact not_le.1 fun h => (not_le.2 hlt) ((Chapter03.ar2SlowAlpha_le_iff hε₁ hK hk).1 h)
        · refine iff_of_true (arpStopTest_some_some_of ?_ ?_ fun d hd' => ?_) le_rfl
          · rw [hg]; exact (Chapter03.ar2SlowAlpha_le_iff hε₁ hK hk).2 le_rfl
          · rw [hessianMinEig_ridge_e₀ (hG' hG).2, (hd _ hk).2 2 (by norm_num) (by omega)
              (by norm_num)]
            linarith
          · rw [abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ (hunit hd'),
              abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ (hunit hd'),
              (hd _ hk).2 3 (by norm_num) hp (by norm_num),
              (hd _ hk).2 2 (by norm_num) (by omega) (by norm_num), abs_zero]
            exact ⟨he₃.le, he₂.le⟩
    have hcrit : IsFirstHit (fun k => IsApproxThirdOrderMinimizer (ridge G e₀) (x k) ε₁ e₂ e₃)
        (arpSlowK p 1 ε₁) := by
      simp only [hxk]
      refine isFirstHit_of_forall_le_iff fun k hk => ?_
      have hα := Chapter03.ar2SlowAlpha_pos hε₁ hK hk
      rw [IsApproxThirdOrderMinimizer, Chapter03.isApproxSecondOrderMinimizer_def,
        norm_gradient_ridge_e₀ (hG' hG).1, (hd k hk).1, abs_neg, abs_of_pos hα,
        hessianMinEig_ridge_e₀ (hG' hG).2, (hd k hk).2 2 (by norm_num) (by omega) (by norm_num),
        ← Chapter03.ar2SlowAlpha_le_iff hε₁ hK hk]
      refine ⟨fun h => h.1.1, fun h => ⟨⟨h, by linarith⟩, fun d hd' => ?_⟩⟩
      rw [abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ hd'.1,
        (hd k hk).2 3 (by norm_num) hp (by norm_num), abs_zero]
      exact he₃.le
    exact ⟨ridge G e₀, fun y => (hb y).trans' (by linarith [le_max_left B₁ (max B₂ B₃)]),
      hDpL.mono (le_max_left _ _), x, s, σ, hx0', halg, hσ', hhit, hcrit⟩
  · -- the negative-curvature example
    rw [show max (max A B) C = B by omega,
      show B = arpSlowK p 2 e₂ from (arpSlowK_two (by omega) _).symm]
    obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H₂ e₂ he₂ he₂1
    have hK := arpSlowK_pos (p := p) (q := 2) he₂
    obtain ⟨x, s, σ, hx0', halg, hσ', hhit, hxk⟩ :=
      exists_algorithm_4_1_1_ridge P (by omega) hord hε₁
      (by simpa using he₂) (by simpa using he₃) (by simp) (by norm_num) (by omega)
      (fun h => hthird h 2 (by norm_num)) hG
      (fun k hk => Chapter03.ar2SlowAlpha_pos he₂ hK hk.le) (fun k hk => hd k hk.le) hx hv hx0
      fun k hk => by
        have hα := Chapter03.ar2SlowAlpha_pos he₂ hK hk
        have hl : Chapter01.hessianMinEig (ridge G e₀) (xr k • e₀) =
            -Chapter03.ar2SlowAlpha e₂ (arpSlowK p 2 e₂) k := by
          rw [hessianMinEig_ridge_e₀ (hG' hG).2, (hd k hk).1]
        rcases hk.lt_or_eq with hlt | rfl
        · refine iff_of_false (not_arpStopTest_some_some.2 (Or.inr ⟨by linarith, Or.inl ?_⟩))
            (not_le.2 hlt)
          rw [hl, neg_lt_neg_iff]
          exact not_le.1 fun h => (not_le.2 hlt) ((Chapter03.ar2SlowAlpha_le_iff he₂ hK hk).1 h)
        · have hαle := (Chapter03.ar2SlowAlpha_le_iff he₂ hK hk).2 le_rfl
          refine iff_of_true (arpStopTest_some_some_of ?_ ?_ fun d hd' => ?_) le_rfl
          · rw [norm_gradient_ridge_e₀ (hG' hG).1, (hd _ hk).2 1 le_rfl (by omega) (by norm_num),
              abs_zero]
            exact hε₁.le
          · rw [hl, neg_le_neg_iff]; exact hαle
          · rw [abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ (hunit hd'),
              abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ (hunit hd'),
              (hd _ hk).2 3 (by norm_num) hp (by norm_num), (hd _ hk).1, abs_zero, abs_neg,
              abs_of_pos hα]
            exact ⟨he₃.le, hαle⟩
    have hcrit : IsFirstHit (fun k => IsApproxThirdOrderMinimizer (ridge G e₀) (x k) ε₁ e₂ e₃)
        (arpSlowK p 2 e₂) := by
      simp only [hxk]
      refine isFirstHit_of_forall_le_iff fun k hk => ?_
      have hα := Chapter03.ar2SlowAlpha_pos he₂ hK hk
      rw [IsApproxThirdOrderMinimizer, Chapter03.isApproxSecondOrderMinimizer_def,
        norm_gradient_ridge_e₀ (hG' hG).1, (hd k hk).2 1 le_rfl (by omega) (by norm_num),
        abs_zero, hessianMinEig_ridge_e₀ (hG' hG).2, (hd k hk).1, neg_le_neg_iff,
        ← Chapter03.ar2SlowAlpha_le_iff he₂ hK hk]
      refine ⟨fun h => h.1.2, fun h => ⟨⟨hε₁.le, h⟩, fun d hd' => ?_⟩⟩
      rw [abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ hd'.1,
        (hd k hk).2 3 (by norm_num) hp (by norm_num), abs_zero]
      exact he₃.le
    exact ⟨ridge G e₀, fun y => (hb y).trans' (by
        linarith [le_max_left B₂ B₃, le_max_right B₁ (max B₂ B₃)]),
      hDpL.mono ((le_max_left _ _).trans (le_max_right _ _)), x, s, σ, hx0', halg, hσ', hhit,
      hcrit⟩
  · -- the third-order example
    rw [show max (max A B) C = C by omega,
      show C = arpSlowK p 3 e₃ from (arpSlowK_three hp _).symm]
    obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H₃ e₃ he₃ he₃1
    have hK := arpSlowK_pos (p := p) (q := 3) he₃
    set K := arpSlowK p 3 e₃
    set α := Chapter03.ar2SlowAlpha e₃ K
    -- `e₀` is a direction of small model curvature at every iteration before `K`
    have hmem : ∀ k < K, e₀ ∈ arpCurvSet (ridge G e₀) p P (some e₂) (fun k => xr k • e₀)
        (fun k => (xr (k + 1) - xr k) • e₀) (fun _ => P.σ₀) k := by
      intro k hk
      cases k with
      | zero =>
        change e₀ ∈ smallCurvatureSet (ridge G e₀) (xr 0 • e₀) e₂
        rw [mem_smallCurvatureSet, abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ norm_e₀,
          (hd 0 hk.le).2 2 (by norm_num) (by omega) (by norm_num), abs_zero]
        exact ⟨norm_e₀, he₂.le⟩
      | succ j =>
        rw [arpCurvSet_succ, mem_smallCurvatureDirections]
        have hj : j < K := by omega
        have hdj : IsSpikeJetOf p G 3 ⟪e₀, xr j • e₀⟫ (α j) := by
          rw [inner_e₀_smul]; exact hd j hj.le
        have hαj : 0 < α j := Chapter03.ar2SlowAlpha_pos he₃ hK hj.le
        have ht : ⟪e₀, (xr (j + 1) - xr j) • e₀⟫ = monomialMinimizer p 3 P.σ₀ (α j) := by
          rw [inner_e₀_smul, hx j hj]; ring
        have htpos := monomialMinimizer_pos (p := p) (q := 3) hσ₀ hαj
        have hn : ‖(xr (j + 1) - xr j) • e₀‖ = monomialMinimizer p 3 P.σ₀ (α j) := by
          rw [norm_eq_abs_inner_e₀, ht, abs_of_pos htpos]
        refine ⟨norm_e₀, ?_⟩
        rw [iteratedFDeriv_regularizedModel_ridge_spike norm_eq_abs_inner_e₀ hG (by norm_num) hp hdj
          _ (by norm_num)
          (by omega), ht, hn, real_inner_self_eq_norm_sq, norm_e₀]
        obtain ⟨h0, h1⟩ := iteratedDeriv_two_negMonomialRegModel_mem hp hσ₀ hαj
        rw [one_pow, one_pow, mul_one, abs_of_nonneg h0]
        refine h1.trans ?_
        have hf1 : (0 : ℝ) < (p - 1)! := by positivity
        have hf : ((p - 2)! : ℝ) ≤ (p - 1)! := by
          exact_mod_cast Nat.factorial_le (by omega)
        have hσ2 : P.σ₀ ≤ (p - 1)! * P.θ₂ :=
          hσ.trans ((mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans
            (mul_le_mul_of_nonneg_right hf P.θ₂_pos.le))
        rw [div_le_iff₀ hf1]
        have : 0 ≤ monomialMinimizer p 3 P.σ₀ (α j) ^ (p - 1) := by positivity
        nlinarith
    obtain ⟨x, s, σ, hx0', halg, hσ', hhit, hxk⟩ :=
      exists_algorithm_4_1_1_ridge P (by omega) hord hε₁
      (by simpa using he₂) (by simpa using he₃) (by simp) (by norm_num) hp
      (fun h => hthird h 3 le_rfl) hG
      (fun k hk => Chapter03.ar2SlowAlpha_pos he₃ hK hk.le) (fun k hk => hd k hk.le) hx hv hx0
      fun k hk => by
        have hαk := Chapter03.ar2SlowAlpha_pos he₃ hK hk
        have hg : ‖gradient (ridge G e₀) (xr k • e₀)‖ = 0 := by
          rw [norm_gradient_ridge_e₀ (hG' hG).1, (hd k hk).2 1 le_rfl (by omega) (by norm_num),
            abs_zero]
        have hl : Chapter01.hessianMinEig (ridge G e₀) (xr k • e₀) = 0 := by
          rw [hessianMinEig_ridge_e₀ (hG' hG).2, (hd k hk).2 2 (by norm_num) (by omega)
            (by norm_num)]
        rcases hk.lt_or_eq with hlt | rfl
        · refine iff_of_false (not_arpStopTest_some_some.2 (Or.inr ⟨by rw [hl]; exact he₂.le,
            Or.inr ⟨e₀, hmem k hlt, Or.inl ?_⟩⟩)) (not_le.2 hlt)
          rw [abs_iteratedFDeriv_ridge_e₀ hG hp _ norm_e₀, (hd k hk).1, abs_neg, abs_of_pos hαk]
          exact not_le.1 fun h => (not_le.2 hlt) ((Chapter03.ar2SlowAlpha_le_iff he₃ hK hk).1 h)
        · refine iff_of_true (arpStopTest_some_some_of (by rw [hg]; exact hε₁.le)
            (by rw [hl]; linarith) fun d hd' => ?_) le_rfl
          rw [abs_iteratedFDeriv_ridge_e₀ hG hp _ (hunit hd'),
            abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ (hunit hd'), (hd _ hk).1,
            (hd _ hk).2 2 (by norm_num) (by omega) (by norm_num), abs_zero, abs_neg,
            abs_of_pos hαk]
          exact ⟨(Chapter03.ar2SlowAlpha_le_iff he₃ hK hk).2 le_rfl, he₂.le⟩
    have hcrit : IsFirstHit (fun k => IsApproxThirdOrderMinimizer (ridge G e₀) (x k) ε₁ e₂ e₃)
        K := by
      simp only [hxk]
      refine isFirstHit_of_forall_le_iff fun k hk => ?_
      have hαk := Chapter03.ar2SlowAlpha_pos he₃ hK hk
      have h3 : ∀ d : EuclideanSpace ℝ (Fin 1), ‖d‖ = 1 →
          |iteratedFDeriv ℝ 3 (ridge G e₀) (xr k • e₀) (fun _ => d)| = α k := fun d hd' => by
        rw [abs_iteratedFDeriv_ridge_e₀ hG hp _ hd', (hd k hk).1, abs_neg, abs_of_pos hαk]
      rw [IsApproxThirdOrderMinimizer, Chapter03.isApproxSecondOrderMinimizer_def,
        norm_gradient_ridge_e₀ (hG' hG).1, (hd k hk).2 1 le_rfl (by omega) (by norm_num),
        abs_zero, hessianMinEig_ridge_e₀ (hG' hG).2,
        (hd k hk).2 2 (by norm_num) (by omega) (by norm_num),
        ← Chapter03.ar2SlowAlpha_le_iff he₃ hK hk]
      refine ⟨fun h => ?_, fun h => ⟨⟨hε₁.le, by linarith⟩, fun d hd' => (h3 d hd'.1).le.trans h⟩⟩
      have he₀ : e₀ ∈ smallCurvatureSet (ridge G e₀) (xr k • e₀) e₂ := by
        rw [mem_smallCurvatureSet, abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ norm_e₀,
          (hd k hk).2 2 (by norm_num) (by omega) (by norm_num), abs_zero]
        exact ⟨norm_e₀, he₂.le⟩
      exact (h3 e₀ norm_e₀).symm.le.trans (h.2 e₀ he₀)
    exact ⟨ridge G e₀, fun y => (hb y).trans' (by
        linarith [le_max_right B₂ B₃, le_max_right B₁ (max B₂ B₃)]),
      hDpL.mono ((le_max_right _ _).trans (le_max_right _ _)), x, s, σ, hx0', halg, hσ', hhit,
      hcrit⟩


end Sharpness

end CartisGouldToint.Chapter04
