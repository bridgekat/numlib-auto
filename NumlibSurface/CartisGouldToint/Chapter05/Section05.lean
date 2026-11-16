/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter03.Section03
import Numlib.Optimization.ModelBased.PowRegularizedModel

/-!
# Cartis, Gould and Toint, Section 5.5: Universal regularization methods

This module formalizes Section 5.5 of [cartis2022evaluation]: the universal adaptive-regularization
algorithm ARp-H (Algorithm 5.5.1) for objectives $f : \mathbb{R}^n \to \mathbb{R}$ whose $p$-th
derivative is Hölder continuous with constant $H$ and an exponent $\beta = \beta_p \in [0, 1]$ that
the algorithm does not know (assumption f.DpH). The model of iteration $k$ is
$$m_k(s) = T_{f,p}(x_k, s) + \frac{\sigma_k}{r!} \|s\|^r \quad \text{(5.5.1)}$$
for a real power $r > p$, with the generalized factorial $r!$ of (5.5.2). A step is accepted only if
the ratio $\rho_k$ is at least $\eta_1$ and the step-length tests $\sigma_k \|s_k\|^{r-1} \ge
\alpha_1 \|\nabla f(x_k + s_k)\|$ (5.5.10) and $\sigma_k \|s_k\|^{r-2} \ge -\alpha_2
\lambda_{\min}[\nabla^2 f(x_k + s_k)]$ (5.5.11) hold. Lemmas 5.5.1–5.5.6 bound the step, the
regularization weight and the decrease, and Theorem 5.5.7 shows that, for $r \ge p + \beta$, ARp-H
finds an $(\epsilon_1, \epsilon_2)$-approximate minimizer after
$O(\max[\epsilon_1^{-(p+\beta)/(p+\beta-1)}, \epsilon_2^{-(p+\beta)/(p+\beta-2)}])$ evaluations, up
to logarithmic terms.

The model is `Optimization.powRegularizedModel` with the generalized factorial
`Optimization.realFactorial`, and a run is an instance of the generic adaptive-regularization run
`Optimization.IsARRun`.

## Main definitions

* Assumption f.DpH, `CartisGouldToint.Chapter05.AssumptionDpH`: $f$ is $p$ times continuously
  differentiable and $\nabla^p f$ is Hölder continuous, (5.5.3).
* Algorithm 5.5.1, `CartisGouldToint.Chapter05.ARpHParams`: the constants of Step 0.
* Algorithm 5.5.1, `CartisGouldToint.Chapter05.arpHStep`,
  `CartisGouldToint.Chapter05.arpHLengthTest`, `CartisGouldToint.Chapter05.arpHRatio`,
  `CartisGouldToint.Chapter05.arpHStop`: the step conditions (5.5.4)–(5.5.6), the step-length tests
  (5.5.10)–(5.5.11), the modified ratio and the termination test.
* Algorithm 5.5.1, `CartisGouldToint.Chapter05.algorithm_5_5_1`: a run of ARp-H.
* Equations (5.5.19), (5.5.27)–(5.5.30), (5.5.41), (5.5.42) and (5.5.45),
  `CartisGouldToint.Chapter05.kappaBeta`, `CartisGouldToint.Chapter05.kappaBetaJ`,
  `CartisGouldToint.Chapter05.sigmaBar`, `CartisGouldToint.Chapter05.epsMax`,
  `CartisGouldToint.Chapter05.sigmaH`, `CartisGouldToint.Chapter05.kappaH`: the constants of the
  analysis.

## Main results

* Algorithm 5.5.1, `CartisGouldToint.Chapter05.exists_algorithm_5_5_1`: ARp-H runs exist from every
  starting point.
* Lemma 5.5.1, `CartisGouldToint.Chapter05.lemma_5_5_1`: the Taylor decrease of a step exceeds
  $\sigma_k \|s_k\|^r / r!$.
* Lemma 5.5.2, `CartisGouldToint.Chapter05.lemma_5_5_2`: bounds on the gradient and the curvature of
  $f$ at the trial point in terms of $\|s_k\|$.
* Lemma 5.5.3, `CartisGouldToint.Chapter05.lemma_5_5_3`: a large weight relative to $\|s_k\|$ makes
  the iteration very successful.
* Lemma 5.5.4, `CartisGouldToint.Chapter05.lemma_5_5_4`: a weight above $\bar\sigma$ makes the
  iteration very successful.
* Lemma 5.5.5, `CartisGouldToint.Chapter05.lemma_5_5_5`: an upper bound on the weights.
* Lemma 5.5.6, `CartisGouldToint.Chapter05.lemma_5_5_6`: the decrease of $f$ on successful
  iterations.
* Theorem 5.5.7, `CartisGouldToint.Chapter05.theorem_5_5_7`: the evaluation complexity of ARp-H.

## Conventions

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`.
* The tolerance $\epsilon_2$ is an `Option ℝ`: `none` stands for $\epsilon_2 = \infty$, when only
  first-order points are sought.
* $\lambda_{\min}[\nabla^2 f(x)]$ is `CartisGouldToint.Chapter01.hessianMinEig f x`, and the least
  curvature of a model Hessian is `minCurvature`.
* The generalized factorial $(p + \beta - j)!$ of a Hölder exponent is `holderFactorial (p - j) β`,
  and $(r - j)!$ is `Optimization.realFactorial (r - j)`.

## Implementation notes

* Termination is tested at $x_0$ (the test of Step 1 is "$k = 0$ and the test holds at $x_0$") and
  at every trial point $x_k + s_k$ (a test after the step). The test is
  `CartisGouldToint.Chapter03.stopTest f ε₁ ε₂`, which subsumes the strict local minimizer branch
  (5.5.8).
* Steps 3–4 are `Optimization.ARAcceptance` with $\sigma_{\min} = 0$ and the **modified ratio**
  $\tilde\rho_k$, which is $\rho_k$ if the step-length tests (5.5.10)–(5.5.11) hold and $0$
  otherwise. Since $\eta_1 > 0$, iteration $k$ is successful ($\tilde\rho_k \ge \eta_1$) if and only
  if $\rho_k \ge \eta_1$ and (5.5.10)–(5.5.11) hold. This encodes Steps 3–4 with the corrected third
  case of Step 4.
* The condition $p + \beta_p > 1$ is not a hypothesis; it follows from f.DpH, which requires
  $\beta_1 > 0$ when $p = 1$ (`CartisGouldToint.Chapter05.AssumptionDpH.one_lt_add`).

## Deviations from the source

* **Algorithm 5.5.1, Step 4** (typo). The third case reads "$\rho_k < \eta_1$ and (5.5.10) or
  (5.5.11) fails"; it must be the complement of the first two cases, "$\rho_k < \eta_1$, or (5.5.10)
  fails, or (5.5.11) fails". See `CartisGouldToint.Chapter05.algorithm_5_5_1`.
* **Lemma 5.5.2** (typo). The display writes $\nabla_s m_k(x_k + s_k)$ for the model gradient
  $\nabla_s m_k(s_k)$. See `CartisGouldToint.Chapter05.lemma_5_5_2`.
* **Lemma 5.5.4** (typo). In the proof of case (b), the conclusion is $\sigma_k < \kappa_{\beta,2}
  \epsilon_2^{(p+\beta-r)/(p+\beta-2)}$, printed with $\epsilon_1$. See
  `CartisGouldToint.Chapter05.lemma_5_5_4`.
* **Theorem 5.5.7** (correction). The function and its derivatives are evaluated at $x_0$ and at
  every trial point, that is, $k_\epsilon + 2$ times when the run terminates at the trial point of
  iteration $k_\epsilon$, while Lemma 2.4.1 bounds $k_\epsilon + 1$. The constant $\kappa^C$ needs
  an additional $+ 2$. See `CartisGouldToint.Chapter05.theorem_5_5_7`.
-/

open Set Finset Optimization
open Optimization hiding ARParams
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter05

open Chapter03

variable {n : ℕ}

/-! ### Assumption f.DpH and the algorithm -/

/-- **Assumption f.DpH** of [cartis2022evaluation], Section 5.5.1. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $p \in \mathbb{N}$ and $H, \beta \in \mathbb{R}$. The
assumption holds if $f$ is $p$ times continuously differentiable, $H = H_{f,p} \ge 0$,
$\beta = \beta_p \in [0, 1]$ with $\beta > 0$ if $p = 1$, and for all $x, y \in \mathbb{R}^n$
$$\|\nabla^p f(x) - \nabla^p f(y)\| \le H \|x - y\|^\beta \quad \text{(5.5.3)}.$$

The norm of the derivative tensor is the operator norm, and the Hölder condition is
`IteratedFDerivHolderOn f p H β univ`. -/
structure AssumptionDpH (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (H β : ℝ) : Prop where
  /-- The function $f$ is $p$ times continuously differentiable. -/
  contDiff : ContDiff ℝ p f
  /-- The Hölder constant satisfies $H \ge 0$. -/
  H_nonneg : 0 ≤ H
  /-- The Hölder exponent satisfies $\beta \ge 0$. -/
  β_nonneg : 0 ≤ β
  /-- The Hölder exponent satisfies $\beta \le 1$. -/
  β_le_one : β ≤ 1
  /-- The Hölder exponent satisfies $\beta > 0$ when $p = 1$. -/
  β_pos_of_eq_one : p = 1 → 0 < β
  /-- The $p$-th derivative satisfies the Hölder condition (5.5.3) on $\mathbb{R}^n$. -/
  holder : IteratedFDerivHolderOn f p H β univ

/-- Assumption f.DpH holds if and only if $f$ is $p$ times continuously differentiable, $H \ge 0$,
$\beta \in [0, 1]$, $\beta > 0$ if $p = 1$, and $\nabla^p f$ is Hölder continuous on
$\mathbb{R}^n$ with constant $H$ and exponent $\beta$. -/
theorem assumptionDpH_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {H β : ℝ} :
    AssumptionDpH f p H β ↔ ContDiff ℝ p f ∧ 0 ≤ H ∧ β ∈ Set.Icc 0 1 ∧ (p = 1 → 0 < β) ∧
      IteratedFDerivHolderOn f p H β univ :=
  ⟨fun h => ⟨h.contDiff, h.H_nonneg, ⟨h.β_nonneg, h.β_le_one⟩, h.β_pos_of_eq_one, h.holder⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3.1, h3.2, h4, h5⟩⟩

/-- **Algorithm 5.5.1** of [cartis2022evaluation], the constants of Step 0. Let $r \in \mathbb{R}$
be the regularization power. A set of **ARp-H constants** consists of the constants of adaptive
regularization with $\sigma_{\min} = 0$ ($\sigma_0 > 0$, $0 < \eta_1 \le \eta_2 < 1$,
$0 < \gamma_1 < 1 < \gamma_2 \le \gamma_3$), the step accuracies
$\theta_1, \theta_2 \in (0, 1]$, and the step-length constants
$$\alpha_1 \in \left(0, \tfrac{1}{3} \min(1, (r-1)!)\right], \qquad \alpha_2 \in \left(0,
  \tfrac{1}{3} \min(1, (r-2)!)\right].$$

The constants of adaptive regularization are `Optimization.ARParams`. -/
structure ARpHParams (r : ℝ) extends Optimization.ARParams where
  /-- The lower bound on the regularization weight is $\sigma_{\min} = 0$. -/
  σmin_eq_zero : σmin = 0
  /-- The first-order step accuracy $\theta_1$ of (5.5.5). -/
  θ₁ : ℝ
  /-- The second-order step accuracy $\theta_2$ of (5.5.6). -/
  θ₂ : ℝ
  /-- The first-order step-length constant $\alpha_1$ of (5.5.10). -/
  α₁ : ℝ
  /-- The second-order step-length constant $\alpha_2$ of (5.5.11). -/
  α₂ : ℝ
  /-- The step accuracy $\theta_1$ is positive. -/
  θ₁_pos : 0 < θ₁
  /-- The step accuracy $\theta_1$ is at most $1$. -/
  θ₁_le_one : θ₁ ≤ 1
  /-- The step accuracy $\theta_2$ is positive. -/
  θ₂_pos : 0 < θ₂
  /-- The step accuracy $\theta_2$ is at most $1$. -/
  θ₂_le_one : θ₂ ≤ 1
  /-- The step-length constant $\alpha_1$ is positive. -/
  α₁_pos : 0 < α₁
  /-- The step-length constant satisfies $\alpha_1 \le \min(1, (r-1)!) / 3$. -/
  α₁_le : α₁ ≤ min 1 (realFactorial (r - 1)) / 3
  /-- The step-length constant $\alpha_2$ is positive. -/
  α₂_pos : 0 < α₂
  /-- The step-length constant satisfies $\alpha_2 \le \min(1, (r-2)!) / 3$. -/
  α₂_le : α₂ ≤ min 1 (realFactorial (r - 2)) / 3

variable {r : ℝ}

/-- **Equation (5.5.1)** of [cartis2022evaluation]. The model of ARp-H at the iterate $y$ with
weight $\sigma$ is $m(s) = T_{f,p}(y, s) + \sigma \|s\|^r / r!$. -/
noncomputable abbrev arpHModel (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (r : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (σ : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  powRegularizedModel (ftaylorSeries ℝ f y) p σ r

/-- **Algorithm 5.5.1** of [cartis2022evaluation], Step 1. A step $s$ at $y$ with weight $\sigma$
satisfies Step 1 if it decreases the model, $m(s) < m(0)$ (5.5.4), satisfies
$\|\nabla m(s)\| \le \theta_1 \|s\|^{r-1}$ (5.5.5), and, if $\epsilon_2 < \infty$, satisfies
$\lambda_{\min}[\nabla^2 m(s)] \ge -\theta_2 \|s\|^{r-2}$ (5.5.6). -/
def arpHStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpHParams r) (ε₂ : Option ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  arpHModel f p r y σ s < arpHModel f p r y σ 0 ∧
    ‖fderiv ℝ (arpHModel f p r y σ) s‖ ≤ P.θ₁ * ‖s‖ ^ (r - 1) ∧
    (ε₂.isSome →
      -(P.θ₂ * ‖s‖ ^ (r - 2)) ≤ minCurvature (iteratedFDeriv ℝ 2 (arpHModel f p r y σ) s))

/-- **Algorithm 5.5.1** of [cartis2022evaluation], the step-length tests of Step 3. A step $s$ at
$y$ with weight $\sigma$ passes the tests if $\sigma \|s\|^{r-1} \ge \alpha_1 \|\nabla f(y +
s)\|$ (5.5.10) and, if $\epsilon_2 < \infty$, $\sigma \|s\|^{r-2} \ge -\alpha_2
\lambda_{\min}[\nabla^2 f(y + s)]$ (5.5.11). -/
def arpHLengthTest (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : ARpHParams r) (ε₂ : Option ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  P.α₁ * ‖gradient f (y + s)‖ ≤ σ * ‖s‖ ^ (r - 1) ∧
    (ε₂.isSome → -(P.α₂ * Chapter01.hessianMinEig f (y + s)) ≤ σ * ‖s‖ ^ (r - 2))

open Classical in
/-- The modified ratio of one iteration: the ratio (5.5.9) if the step-length tests
(5.5.10)–(5.5.11) hold, and $0$ otherwise. -/
noncomputable def arpHRatioAt (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpHParams r)
    (ε₂ : Option ℝ) (y : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if arpHLengthTest f P ε₂ y σ s then
    reductionRatio f y s ((ftaylorSeries ℝ f y).taylorDecrement p s)
  else 0

/-- The modified ratios $\tilde\rho_k$ of a run: the modified ratio of iteration $k$ at $x_k$ with
weight $\sigma_k$ and step $s_k$. -/
noncomputable abbrev arpHRatio (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpHParams r)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) (k : ℕ) : ℝ :=
  arpHRatioAt f p P ε₂ (x k) (σ k) (s k)

/-- **Algorithm 5.5.1** of [cartis2022evaluation], the termination test. ARp-H terminates at
iteration $k$ if $k = 0$ and the test (5.5.7)–(5.5.8) holds at $x_0$, or if the test holds at
the trial point $x_k + s_k$. -/
abbrev arpHStop (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε₁ : ℝ) (ε₂ : Option ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) : ℕ → Prop :=
  IsARRun.Stop (fun k => k = 0 ∧ stopTest f ε₁ ε₂ (x k)) (fun k => stopTest f ε₁ ε₂ (x k + s k))

/-- **Algorithm 5.5.1** of [cartis2022evaluation] (ARp-H). Let $f : \mathbb{R}^n \to \mathbb{R}$,
$p \in \mathbb{N}$, ARp-H constants $P$ for the power $r$, and tolerances
$\epsilon_1 \in \mathbb{R}$ and $\epsilon_2 \in \mathbb{R} \cup \{\infty\}$. Sequences of
iterates $x_k$, steps $s_k$ and weights $\sigma_k$ form a **run of ARp-H** if $p \ge 1$
($p \ge 2$ if $\epsilon_2 < \infty$), $r > p$, $\epsilon_1 \in (0, 1]$, $\epsilon_2 \in (0, 1]$
if it is finite, and they form an adaptive-regularization run with the termination test at $x_0$
and at every trial point, the Step 1 conditions (5.5.4)–(5.5.6), and Steps 3–4 with the modified
ratio.

**Typo.** The third case of Step 4 reads "$\rho_k < \eta_1$ and (5.5.10) or (5.5.11) fails". It
must be the complement of the first two cases: "$\rho_k < \eta_1$, or (5.5.10) fails, or
(5.5.11) fails". The modified ratio encodes this.

The run is `Optimization.IsARRun` with the Step 1 conditions
`CartisGouldToint.Chapter05.arpHStep` and the ratio `CartisGouldToint.Chapter05.arpHRatio`. -/
structure algorithm_5_5_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpHParams r)
    (ε₁ : ℝ) (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- The degree satisfies $p \ge 1$. -/
  one_le_p : 1 ≤ p
  /-- The degree satisfies $p \ge 2$ when second-order points are sought. -/
  two_le_p : ε₂.isSome → 2 ≤ p
  /-- The regularization power satisfies $r > p$. -/
  p_lt_r : (p : ℝ) < r
  /-- The tolerance $\epsilon_1$ is positive. -/
  ε₁_pos : 0 < ε₁
  /-- The tolerance $\epsilon_1$ is at most $1$. -/
  ε₁_le_one : ε₁ ≤ 1
  /-- The tolerance $\epsilon_2$ is positive if it is finite. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- The tolerance $\epsilon_2$ is at most $1$ if it is finite. -/
  ε₂_le_one : ∀ e ∈ ε₂, e ≤ 1
  /-- The sequences follow Steps 1–4 of the algorithm. -/
  run : IsARRun P.toARParams (fun k => k = 0 ∧ stopTest f ε₁ ε₂ (x k))
    (fun k => arpHStep f p P ε₂ (x k) (σ k) (s k)) (fun k => stopTest f ε₁ ε₂ (x k + s k))
    (arpHRatio f p P ε₂ x s σ) x s σ

section Basic

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₂ : Option ℝ}
  {y : EuclideanSpace ℝ (Fin n)} {σ : ℝ} {s : EuclideanSpace ℝ (Fin n)}

/-- An iteration is successful for the modified ratio, $\tilde\rho_k \ge \eta_1$, if and only if
$\rho_k \ge \eta_1$ and the step-length tests hold. -/
theorem le_arpHRatioAt_iff :
    P.η₁ ≤ arpHRatioAt f p P ε₂ y σ s ↔
      P.η₁ ≤ reductionRatio f y s ((ftaylorSeries ℝ f y).taylorDecrement p s) ∧
        arpHLengthTest f P ε₂ y σ s := by
  unfold arpHRatioAt
  split_ifs with h
  · exact ⟨fun h1 => ⟨h1, h⟩, fun h1 => h1.1⟩
  · exact ⟨fun h1 => absurd h1 (not_le.2 P.η₁_pos), fun h1 => absurd h1.2 h⟩

/-- If the step-length tests hold, then the modified ratio is the ratio (5.5.9). -/
theorem arpHRatioAt_of_lengthTest (h : arpHLengthTest f P ε₂ y σ s) :
    arpHRatioAt f p P ε₂ y σ s = reductionRatio f y s ((ftaylorSeries ℝ f y).taylorDecrement p s) :=
  by unfold arpHRatioAt; simp only [h, ↓reduceIte]

/-- If $f$ is $p$ times continuously differentiable at $y$, then the derivatives of the model at the
zero step are those of $f$: $\nabla^j m(0) = \nabla^j f(y)$ for $j \le p$ with $j < r$. -/
theorem iteratedFDeriv_arpHModel_zero (hf : ContDiffAt ℝ p f y) {j : ℕ} (hj : j ≤ p)
    (hjr : (j : ℝ) < r) :
    iteratedFDeriv ℝ j (arpHModel f p r y σ) 0 = iteratedFDeriv ℝ j f y := by
  rw [arpHModel, iteratedFDeriv_powRegularizedModel ((contDiff_normRpow_of_lt hjr).contDiffAt),
    ← taylorPolynomial_eq_taylorSum, iteratedFDeriv_taylorPolynomial_zero hf hj,
    iteratedFDeriv_normRpow_zero hjr, smul_zero, add_zero]

end Basic

/-! ### Existence of runs -/

section Existence

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ}

/-- Let $f$ be $p$ times continuously differentiable, $p \ge 1$, $r > p$, $\epsilon_1 > 0$,
$\epsilon_2 > 0$ if finite, and $p \ge 2$ if $\epsilon_2 < \infty$. At a point $y$ where the
termination test fails, and for every $\sigma > 0$, some step satisfies Step 1; a global
minimizer of the model is such a step. -/
theorem exists_arpHStep (hf : ContDiff ℝ p f) (P : ARpHParams r) (hp : 1 ≤ p)
    (hpr : (p : ℝ) < r) {ε₁ : ℝ} (hε₁ : 0 < ε₁) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e)
    (hp2 : ε₂.isSome → 2 ≤ p) {y : EuclideanSpace ℝ (Fin n)} {σ : ℝ} (hσ : 0 < σ)
    (hnot : ¬ stopTest f ε₁ ε₂ y) : ∃ s, arpHStep f p P ε₂ y σ s := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨s, -, hd, hc, hlt⟩ := exists_isMinOn_powRegularizedModel
    (D := ftaylorSeries ℝ f y) (p := p) hσ hpr (by linarith)
  refine ⟨s, hlt fun hmin0 => hnot ?_, ?_, fun hs => ?_⟩
  · have hloc : IsLocalMin (arpHModel f p r y σ) 0 := hmin0.isLocalMin Filter.univ_mem
    have hg : gradient f y = 0 := by
      have h1 := iteratedFDeriv_arpHModel_zero (y := y) (σ := σ) hf.contDiffAt hp
        (by push_cast; linarith : ((1 : ℕ) : ℝ) < r)
      have h2 := congrArg norm h1
      rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one, hloc.fderiv_eq_zero, norm_zero]
        at h2
      rw [← norm_eq_zero, norm_gradient_eq, ← h2]
    refine ⟨by rw [hg, norm_zero]; exact hε₁.le, fun e he => ?_⟩
    have hp2' := hp2 (by rw [Option.mem_def.1 he]; rfl)
    have hp2r : (2 : ℝ) < r := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2'
      linarith
    have h0 := hloc.minCurvature_iteratedFDeriv_two_nonneg
      (contDiff_two_powRegularizedModel hp2r.le).contDiffAt
    rw [iteratedFDeriv_arpHModel_zero (y := y) hf.contDiffAt hp2' (by push_cast; linarith)] at h0
    have := hε₂ e he
    change -e ≤ minCurvature _
    linarith
  · rw [hd, norm_zero]
    have := P.θ₁_pos
    positivity
  · have hp2' := hp2 hs
    have h2r : (2 : ℝ) ≤ r := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2'
      linarith
    have := hc h2r
    have := P.θ₂_pos
    have : 0 ≤ P.θ₂ * ‖s‖ ^ (r - 2) := by positivity
    linarith

/-- Consider an adaptive-regularization run whose test is a predicate of the iterates. If the test
fails at $x_0$ and at the trial points $x_j + s_j$ for all $j < k$, then it fails at all
iterates $x_j$ with $j \le k$. -/
theorem not_stopTest_iterate {E : Type*} [Add E] {P : Optimization.ARParams} {test : E → Prop}
    {step : ℕ → Prop} {ρ : ℕ → ℝ} {x s : ℕ → E} {σ : ℕ → ℝ}
    (h : IsARRun P (fun k => test (x k)) step (fun _ => False) ρ x s σ) (h0 : ¬ test (x 0))
    {k : ℕ} (hk : ∀ j < k, ¬ test (x j + s j)) : ∀ j ≤ k, ¬ test (x j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases j with _ | j
    · exact h0
    · have hle : ∀ i ≤ j, ¬ IsARRun.Stop (fun k => test (x k)) (fun _ => False) i :=
        IsARRun.forall_le_not_stop_iff.2 fun i hi => ih i (by omega) (by omega)
      rcases (h.accept j hle).eq_add_or_eq_self with he | he
      · rw [he]; exact hk j (by omega)
      · rw [he]; exact ih j (by omega) (by omega)

/-- **Algorithm 5.5.1** of [cartis2022evaluation], existence of runs. Let $f$ be $p$ times
continuously differentiable, $p \ge 1$, $r > p$, $\epsilon_1 \in (0, 1]$,
$\epsilon_2 \in (0, 1]$ if finite, and $p \ge 2$ if $\epsilon_2 < \infty$. Then for all ARp-H
constants and every $x_0 \in \mathbb{R}^n$ there is a run of ARp-H that starts at $x_0$.

Global minimizers of the model satisfy Step 1 (`CartisGouldToint.Chapter05.exists_arpHStep`). -/
theorem exists_algorithm_5_5_1 (hf : ContDiff ℝ p f) (P : ARpHParams r) (hp : 1 ≤ p)
    (hpr : (p : ℝ) < r) {ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) {ε₂ : Option ℝ}
    (hε₂ : ∀ e ∈ ε₂, 0 < e) (hε₂1 : ∀ e ∈ ε₂, e ≤ 1) (hp2 : ε₂.isSome → 2 ≤ p)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_5_5_1 f p P ε₁ ε₂ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := fun _ => True)
    (test := stopTest f ε₁ ε₂) (stepOK := arpHStep f p P ε₂) (arpHRatioAt f p P ε₂)
    (fun y σ _ _ hσ hnot => (exists_arpHStep hf P hp hpr hε₁ hε₂ hp2 hσ hnot).imp
      fun _ hs => ⟨hs, trivial⟩) trivial
  refine ⟨x, s, σ, hx0, hp, hp2, hpr, hε₁, hε₁1, hε₂, hε₂1, ⟨hrun.sigma_zero, ?_, ?_⟩⟩
  · intro k hk h1
    have h0 : ¬ stopTest f ε₁ ε₂ (x 0) := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact fun h => h1 ⟨rfl, h⟩
      · exact fun h => hk 0 hpos (Or.inl ⟨rfl, h⟩)
    have hnt := not_stopTest_iterate hrun h0 (k := k) fun j hj h => hk j hj (Or.inr h)
    exact hrun.step k (fun j hj => by simpa [IsARRun.Stop] using hnt j hj.le)
      (by simpa using hnt k le_rfl)
  · intro k hk
    have h0 : ¬ stopTest f ε₁ ε₂ (x 0) := fun h => hk 0 (Nat.zero_le _) (Or.inl ⟨rfl, h⟩)
    have hnt := not_stopTest_iterate hrun h0 (k := k) fun j hj h => hk j hj.le (Or.inr h)
    exact hrun.accept k fun j hj => by simpa [IsARRun.Stop] using hnt j hj

end Existence

/-! ### Basic properties of runs -/

section RunBasic

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

namespace algorithm_5_5_1

variable (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
include h

/-- Along a run of ARp-H, $r > 1$. -/
theorem one_lt_r : 1 < r := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast h.one_le_p
  linarith [h.p_lt_r]

/-- Along a run of ARp-H with $\epsilon_2 < \infty$, $r > 2$. -/
theorem two_lt_r (hs : ε₂.isSome) : 2 < r := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast h.two_le_p hs
  linarith [h.p_lt_r]

/-- Along a run of ARp-H, the weights are positive up to termination: if the run does not terminate
at any $j < k$, then $\sigma_k > 0$. -/
theorem sigma_pos {k : ℕ} (hk : ∀ j < k, ¬ arpHStop f ε₁ ε₂ x s j) : 0 < σ k :=
  h.run.sigma_pos hk k le_rfl

/-- Along a run of ARp-H, if the run does not terminate at any $j \le k$, then the step $s_k$
satisfies Step 1. -/
theorem step {k : ℕ} (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) :
    arpHStep f p P ε₂ (x k) (σ k) (s k) :=
  h.run.step_of_forall_le hk

end algorithm_5_5_1

/-- Along a run of ARp-H, if the run does not terminate at any $j \le k$, then the trial point
$x_k + s_k$ fails the termination test. -/
theorem not_stopTest_trial {k : ℕ} (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) :
    ¬ stopTest f ε₁ ε₂ (x k + s k) :=
  fun ht => hk k le_rfl (Or.inr ht)

end RunBasic

/-! ### Lemmas 5.5.1 and 5.5.2 -/

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 5.5.1** of [cartis2022evaluation], sufficient decrease (5.5.12). Along a run of ARp-H,
if the run does not terminate at any iteration $j \le k$, then
$$T_{f,p}(x_k, 0) - T_{f,p}(x_k, s_k) > \frac{\sigma_k}{r!} \|s_k\|^r.$$
-/
theorem lemma_5_5_1 (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) :
    σ k / realFactorial r * ‖s k‖ ^ r < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
  lt_taylorDecrement_of_powRegularizedModel_lt (by linarith [h.one_lt_r]) (h.step hk).1

/-- Along a run of ARp-H, if the run does not terminate at any iteration $j \le k$, then
$s_k \ne 0$. -/
theorem algorithm_5_5_1.step_ne_zero (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) : s k ≠ 0 := by
  intro h0
  have := (h.step hk).1
  rw [h0] at this
  exact lt_irrefl _ this

/-- **Lemma 5.5.2** of [cartis2022evaluation], lower bound on the step. Let $f$ satisfy f.DpH with
constants $H$ and $\beta$. Along a run of ARp-H, if the run does not terminate at any iteration
$j \le k$, then
$$\|\nabla f(x_k + s_k)\| \le \frac{H}{(p+\beta-1)!} \|s_k\|^{p+\beta-1} +
  \frac{\sigma_k}{(r-1)!} \|s_k\|^{r-1} + \theta_1 \|s_k\|^{r-1} \quad \text{(5.5.13)},$$
and, if $\epsilon_2 < \infty$,
$$-\lambda_{\min}[\nabla^2 f(x_k + s_k)] \le \frac{H}{(p+\beta-2)!} \|s_k\|^{p+\beta-2} +
  \frac{\sigma_k}{(r-2)!} \|s_k\|^{r-2} + \theta_2 \|s_k\|^{r-2} \quad \text{(5.5.14)}.$$

**Typo.** The display of the source writes $\nabla_s m_k(x_k + s_k)$ for the model gradient
$\nabla_s m_k(s_k)$.

The factorial $(p+\beta-j)!$ is `holderFactorial (p - j) β`, and $(r-j)!$ is
`Optimization.realFactorial (r - j)`. -/
theorem lemma_5_5_2 (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) :
    ‖gradient f (x k + s k)‖ ≤ H / holderFactorial (p - 1) β * ‖s k‖ ^ ((p : ℝ) + β - 1) +
        σ k / realFactorial (r - 1) * ‖s k‖ ^ (r - 1) + P.θ₁ * ‖s k‖ ^ (r - 1) ∧
      (ε₂.isSome → -Chapter01.hessianMinEig f (x k + s k) ≤
        H / holderFactorial (p - 2) β * ‖s k‖ ^ ((p : ℝ) + β - 2) +
          σ k / realFactorial (r - 2) * ‖s k‖ ^ (r - 2) + P.θ₂ * ‖s k‖ ^ (r - 2)) := by
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hstep := h.step hk
  have hcd : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin n))), ContDiffAt ℝ p f y :=
    fun y _ => hf.contDiff.contDiffAt
  refine ⟨?_, fun hs => ?_⟩
  · have hb := norm_fderiv_le_of_powRegularizedModel convex_univ hcd h.one_le_p hf.β_nonneg
      hf.holder (mem_univ (x k)) (mem_univ (x k + s k)) hσ.le h.one_lt_r
    have he : ((p - 1 : ℕ) : ℝ) + β = (p : ℝ) + β - 1 := by
      rw [Nat.cast_sub h.one_le_p]; push_cast; ring
    rw [he] at hb
    rw [norm_gradient_eq]
    linarith [hstep.2.1]
  · have hp2 := h.two_le_p hs
    have hb := minCurvature_ge_of_powRegularizedModel convex_univ hcd hp2 hf.β_nonneg
      hf.holder (mem_univ (x k)) (mem_univ (x k + s k)) hσ.le (h.two_lt_r hs).le
    have he : ((p - 2 : ℕ) : ℝ) + β = (p : ℝ) + β - 2 := by
      rw [Nat.cast_sub hp2]; push_cast; ring
    rw [he] at hb
    have := hstep.2.2 hs
    simp only [Chapter01.hessianMinEig_def]
    linarith

end Lemmas

/-! ### The constants -/

section Constants

variable (P : ARpHParams r) (p : ℕ) (H β : ℝ)

/-- **Equation (5.5.19)** of [cartis2022evaluation]. The constant is $\kappa_\beta = r! \, H /
((p+\beta-1)! (1 - \eta_2))$. -/
noncomputable def kappaBeta : ℝ :=
  realFactorial r * H / (holderFactorial (p - 1) β * (1 - P.η₂))

/-- **Equations (5.5.28) and (5.5.30)** of [cartis2022evaluation]. For $j \in \mathbb{R}$, the
constant is
$$\kappa_{\beta,j} = \left(\frac{(r-j)!}{3}\right)^{(p+\beta-r)/(p+\beta-j)}
  \kappa_\beta^{(r-j)/(p+\beta-j)},$$
used with $j = 1$ in (5.5.28) and $j = 2$ in (5.5.30). -/
noncomputable def kappaBetaJ (j : ℝ) : ℝ :=
  (realFactorial (r - j) / 3) ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - j)) *
    kappaBeta P p H β ^ ((r - j) / ((p : ℝ) + β - j))

/-- **Equations (5.5.27) and (5.5.29)** of [cartis2022evaluation], the threshold $\bar\sigma$ above
which iterations are very successful. For $\epsilon_2 = \infty$ it is $\max[\theta_1 (r-1)!,
\kappa_{\beta,1} \epsilon_1^{(p+\beta-r)/(p+\beta-1)}]$, the right-hand side of (5.5.27). For
$\epsilon_2 < \infty$ it is the right-hand side of (5.5.29),
$$\max\left[\theta_1 (r-1)!, \theta_2 (r-2)!, \kappa_{\beta,1}
  \epsilon_1^{(p+\beta-r)/(p+\beta-1)}, \kappa_{\beta,2}
  \epsilon_2^{(p+\beta-r)/(p+\beta-2)}\right].$$
-/
noncomputable def sigmaBar (ε₁ : ℝ) : Option ℝ → ℝ
  | none => max (P.θ₁ * realFactorial (r - 1))
      (kappaBetaJ P p H β 1 * ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1)))
  | some e => max (max (P.θ₁ * realFactorial (r - 1)) (P.θ₂ * realFactorial (r - 2)))
      (max (kappaBetaJ P p H β 1 * ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1)))
        (kappaBetaJ P p H β 2 * e ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 2))))

/-- **Equations (5.5.42) and (5.5.55)** of [cartis2022evaluation], the constant $\sigma_H$. For
$\epsilon_2 < \infty$ it is $\max[\sigma_0, \gamma_3 \theta_1 (r-1)!, \gamma_3 \theta_2 (r-2)!,
\gamma_3 \kappa_{\beta,1}, \gamma_3 \kappa_{\beta,2}]$. For $\epsilon_2 = \infty$ it is the
constant $\sigma_{H,1} = \max[\sigma_0, \gamma_3 \theta_1 (r-1)!, \gamma_3 \kappa_{\beta,1}]$ of
Lemma 5.5.6 (i). -/
noncomputable def sigmaH : Option ℝ → ℝ
  | none => max P.σ₀ (max (P.γ₃ * (P.θ₁ * realFactorial (r - 1))) (P.γ₃ * kappaBetaJ P p H β 1))
  | some _ => max P.σ₀ (max (max (P.γ₃ * (P.θ₁ * realFactorial (r - 1)))
      (P.γ₃ * (P.θ₂ * realFactorial (r - 2))))
      (max (P.γ₃ * kappaBetaJ P p H β 1) (P.γ₃ * kappaBetaJ P p H β 2)))

/-- **Equation (5.5.41)** of [cartis2022evaluation], the tolerance factor. It is
$\epsilon_1^{(p+\beta-r)/(p+\beta-1)}$ for $\epsilon_2 = \infty$, and
$\max[\epsilon_1^{(p+\beta-r)/(p+\beta-1)}, \epsilon_2^{(p+\beta-r)/(p+\beta-2)}]$ for
$\epsilon_2 < \infty$. -/
noncomputable def epsMax (r ε₁ : ℝ) : Option ℝ → ℝ
  | none => ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1))
  | some e => max (ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1)))
      (e ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 2)))

/-- The order $\delta_\epsilon$ of the guaranteed decrease in Lemma 5.5.6 and Theorem 5.5.7 of
[cartis2022evaluation]. It is $\epsilon_1^{(p+\beta)/(p+\beta-1)}$ for $\epsilon_2 = \infty$,
and $\min[\epsilon_1^{(p+\beta)/(p+\beta-1)}, \epsilon_2^{(p+\beta)/(p+\beta-2)}]$ for
$\epsilon_2 < \infty$. -/
noncomputable def deltaEps (ε₁ : ℝ) : Option ℝ → ℝ
  | none => ε₁ ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1))
  | some e => min (ε₁ ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1)))
      (e ^ (((p : ℝ) + β) / ((p : ℝ) + β - 2)))

/-- **Equation (5.5.45)** of [cartis2022evaluation] and Lemma 5.5.6 (i), the decrease constant. For
$\epsilon_2 = \infty$ it is $\kappa_{H,1} = \frac{\eta_1}{r!} (\alpha_1^r /
\sigma_{H,1})^{1/(r-1)}$. For $\epsilon_2 < \infty$ it is
$$\kappa_{H,2} = \frac{\eta_1}{r!} \min\left[\left(\frac{\alpha_1^r}{\sigma_H}\right)^{1/(r-1)},
  \left(\frac{\alpha_2^r}{\sigma_H^2}\right)^{1/(r-2)}\right].$$
-/
noncomputable def kappaH : Option ℝ → ℝ
  | none => P.η₁ / realFactorial r * (P.α₁ ^ r / sigmaH P p H β none) ^ (1 / (r - 1))
  | some e => P.η₁ / realFactorial r * min ((P.α₁ ^ r / sigmaH P p H β (some e)) ^ (1 / (r - 1)))
      ((P.α₂ ^ r / sigmaH P p H β (some e) ^ 2) ^ (1 / (r - 2)))

variable {P p H β}

/-- If $H \ge 0$ and $\beta \ge 0$, then $\kappa_\beta \ge 0$. -/
theorem kappaBeta_nonneg (hH : 0 ≤ H) (hβ : 0 ≤ β) : 0 ≤ kappaBeta P p H β := by
  have := realFactorial_pos r
  have := holderFactorial_pos (p - 1) (by linarith : (-1 : ℝ) < β)
  have := P.one_sub_η₂_pos
  unfold kappaBeta; positivity

/-- If $H \ge 0$ and $\beta \ge 0$, then $\kappa_{\beta,j} \ge 0$ for every $j$. -/
theorem kappaBetaJ_nonneg (hH : 0 ≤ H) (hβ : 0 ≤ β) (j : ℝ) : 0 ≤ kappaBetaJ P p H β j := by
  have := realFactorial_pos (r - j)
  have := kappaBeta_nonneg (P := P) (p := p) hH hβ
  unfold kappaBetaJ; positivity

/-- If $H \ge 0$, $\beta \ge 0$ and $r \ge 1$, then $H / (p+\beta-1)! \le \kappa_\beta / (r-1)!$, as
in (5.5.24). -/
theorem div_holderFactorial_le_kappaBeta (hH : 0 ≤ H) (hβ : 0 ≤ β) (hr : 1 ≤ r) :
    H / holderFactorial (p - 1) β ≤ kappaBeta P p H β / realFactorial (r - 1) := by
  have hD := holderFactorial_pos (p - 1) (by linarith : (-1 : ℝ) < β)
  have hF := realFactorial_pos (r - 1)
  have hη := P.one_sub_η₂_pos
  have hη1 : 1 - P.η₂ ≤ 1 := by linarith [P.η₂_pos]
  have hFr := realFactorial_sub_one_le hr
  unfold kappaBeta
  rw [div_div, div_le_div_iff₀ hD (by positivity)]
  have h1 : (1 - P.η₂) * realFactorial (r - 1) ≤ realFactorial r := by
    nlinarith
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hH hD.le)
  nlinarith

/-- If $H \ge 0$, $\beta \ge 0$, $p \ge 2$ and $p + \beta \le r$, then
$H / (p+\beta-2)! \le \kappa_\beta / (r-2)!$, as in (5.5.26). -/
theorem div_holderFactorial_le_kappaBeta_two (hH : 0 ≤ H) (hβ : 0 ≤ β) (hp : 2 ≤ p)
    (hr : (p : ℝ) + β ≤ r) :
    H / holderFactorial (p - 2) β ≤ kappaBeta P p H β / realFactorial (r - 2) := by
  have hD := holderFactorial_pos (p - 2) (by linarith : (-1 : ℝ) < β)
  have hF := realFactorial_pos (r - 2)
  have hη := P.one_sub_η₂_pos
  have hη1 : 1 - P.η₂ ≤ 1 := by linarith [P.η₂_pos]
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hD1 : holderFactorial (p - 1) β = holderFactorial (p - 2) β * ((p : ℝ) - 1 + β) := by
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this, holderFactorial_succ, Nat.cast_sub hp]
    push_cast; ring
  have hr2 : realFactorial r = r * (r - 1) * realFactorial (r - 2) :=
    realFactorial_eq_mul_mul_sub_two (by linarith)
  unfold kappaBeta
  have hq1 : 0 < (p : ℝ) - 1 + β := by linarith
  rw [hD1, hr2, div_div, div_le_div_iff₀ hD (by positivity)]
  have h1 : ((p : ℝ) - 1 + β) * (1 - P.η₂) ≤ r * (r - 1) := by
    have : ((p : ℝ) - 1 + β) * (1 - P.η₂) ≤ (p : ℝ) - 1 + β := by
      have : 0 ≤ (p : ℝ) - 1 + β := by linarith
      nlinarith
    nlinarith
  have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ H * holderFactorial (p - 2) β *
    realFactorial (r - 2))
  nlinarith

end Constants

/-- The three-term bound behind (5.5.23)–(5.5.25): let $F > 0$, $T, U \ge 0$,
$G \le c T + \sigma U / F + \theta U$, $\theta F \le \sigma$, $c \le \kappa / F$ and
$\kappa T \le \sigma U$. Then $G \le 3 \sigma U / F$. -/
theorem le_three_mul_of_bound {G c κ F θ σ T U : ℝ} (hG : G ≤ c * T + σ / F * U + θ * U)
    (hF : 0 < F) (hθ : θ * F ≤ σ) (hc : c ≤ κ / F) (hκ : κ * T ≤ σ * U) (hT : 0 ≤ T)
    (hU : 0 ≤ U) : G ≤ 3 * (σ / F * U) := by
  have h1 : θ * U ≤ σ / F * U :=
    mul_le_mul_of_nonneg_right ((le_div_iff₀ hF).2 hθ) hU
  have h2 : c * T ≤ σ / F * U :=
    calc c * T ≤ κ / F * T := mul_le_mul_of_nonneg_right hc hT
      _ = κ * T / F := by ring
      _ ≤ σ * U / F := by gcongr
      _ = σ / F * U := by ring
  linarith

/-- For $t > 0$ and real $q, r, j$, $t^{q-r} t^{r-j} = t^{q-j}$. -/
theorem rpow_mul_rpow_sub {t q j : ℝ} (ht : 0 < t) (r : ℝ) :
    t ^ (q - r) * t ^ (r - j) = t ^ (q - j) := by
  rw [← Real.rpow_add ht]; ring_nf

/-! ### Lemma 5.5.3 -/

section Lemma553

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 5.5.3** of [cartis2022evaluation], successful iterations. Let $f$ satisfy f.DpH with
constants $H$ and $\beta$, and let $r \ge p + \beta$. Along a run of ARp-H, let $k$ be an
iteration such that the run does not terminate at any $j \le k$. If
$$\sigma_k \ge \max[\theta_1 (r-1)!, \kappa_\beta \|s_k\|^{p+\beta-r}] \quad \text{(5.5.18)}$$
and, when $\epsilon_2 < \infty$, also $\sigma_k \ge \theta_2 (r-2)!$ (5.5.20), then
$\rho_k \ge \eta_2$ and the step-length tests (5.5.10)–(5.5.11) hold, so iteration $k$ is very
successful.

The ratio $\rho_k$ is `Optimization.taylorRatio f p x s k`. -/
theorem lemma_5_5_3 (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    (hr : (p : ℝ) + β ≤ r) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j)
    (h1 : P.θ₁ * realFactorial (r - 1) ≤ σ k)
    (h2 : ε₂.isSome → P.θ₂ * realFactorial (r - 2) ≤ σ k)
    (hκ : kappaBeta P p H β * ‖s k‖ ^ ((p : ℝ) + β - r) ≤ σ k) :
    P.η₂ ≤ taylorRatio f p x s k ∧ arpHLengthTest f P ε₂ (x k) (σ k) (s k) := by
  set t := ‖s k‖
  have ht : 0 < t := norm_pos_iff.2 (h.step_ne_zero hk)
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hr1 := h.one_lt_r
  have hH := hf.H_nonneg
  have hβ := hf.β_nonneg
  have hF1 := realFactorial_pos (r - 1)
  have hκ0 := kappaBeta_nonneg (P := P) (p := p) hH hβ
  -- the ratio
  have hdec := lemma_5_5_1 h hk
  have hrat := abs_reductionRatio_sub_one_le_of_holder convex_univ
    (fun y _ => hf.contDiff.contDiffAt) h.one_le_p hβ hf.holder (mem_univ (x k))
    (mem_univ (x k + s k)) (by have := realFactorial_pos r; positivity) hdec.le
  have hη := P.one_sub_η₂_pos
  have hratio : P.η₂ ≤ taylorRatio f p x s k := by
    have hD := holderFactorial_pos (p - 1) (by linarith : (-1 : ℝ) < β)
    have heq : realFactorial r * H / (holderFactorial (p - 1) β * σ k) * t ^ ((p : ℝ) + β - r) =
        (1 - P.η₂) * (kappaBeta P p H β * t ^ ((p : ℝ) + β - r)) / σ k := by
      unfold kappaBeta; field_simp
    have hle : (1 - P.η₂) * (kappaBeta P p H β * t ^ ((p : ℝ) + β - r)) / σ k ≤ 1 - P.η₂ := by
      rw [div_le_iff₀ hσ]; nlinarith
    rw [taylorRatio_def]
    have := neg_abs_le (reductionRatio f (x k) (s k)
      ((ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)) - 1)
    linarith
  -- the step-length tests
  obtain ⟨hg, hl⟩ := lemma_5_5_2 hf h hk
  refine ⟨hratio, ?_, fun hs => ?_⟩
  · have hκT : kappaBeta P p H β * t ^ ((p : ℝ) + β - 1) ≤ σ k * t ^ (r - 1) := by
      rw [← rpow_mul_rpow_sub ht r, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hκ (by positivity)
    have h3 := le_three_mul_of_bound hg hF1 h1
      (div_holderFactorial_le_kappaBeta hH hβ hr1.le) hκT (by positivity) (by positivity)
    have hα := P.α₁_le
    have hα' : P.α₁ * 3 ≤ realFactorial (r - 1) := by
      have := min_le_right 1 (realFactorial (r - 1)); linarith
    have hα0 := P.α₁_pos
    calc P.α₁ * ‖gradient f (x k + s k)‖ ≤ P.α₁ * (3 * (σ k / realFactorial (r - 1) *
          t ^ (r - 1))) := mul_le_mul_of_nonneg_left h3 hα0.le
      _ = (P.α₁ * 3) / realFactorial (r - 1) * (σ k * t ^ (r - 1)) := by ring
      _ ≤ 1 * (σ k * t ^ (r - 1)) := by
          gcongr
          rw [div_le_one hF1]; exact hα'
      _ = σ k * t ^ (r - 1) := one_mul _
  · have hp2 := h.two_le_p hs
    have hF2 := realFactorial_pos (r - 2)
    have hκT : kappaBeta P p H β * t ^ ((p : ℝ) + β - 2) ≤ σ k * t ^ (r - 2) := by
      rw [← rpow_mul_rpow_sub ht r, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hκ (by positivity)
    have h3 := le_three_mul_of_bound (hl hs) hF2 (h2 hs)
      (div_holderFactorial_le_kappaBeta_two hH hβ hp2 hr) hκT (by positivity) (by positivity)
    have hα' : P.α₂ * 3 ≤ realFactorial (r - 2) := by
      have := P.α₂_le; have := min_le_right 1 (realFactorial (r - 2)); linarith
    have hα0 := P.α₂_pos
    calc -(P.α₂ * Chapter01.hessianMinEig f (x k + s k)) =
          P.α₂ * -Chapter01.hessianMinEig f (x k + s k) := by ring
      _ ≤ P.α₂ * (3 * (σ k / realFactorial (r - 2) * t ^ (r - 2))) :=
          mul_le_mul_of_nonneg_left h3 hα0.le
      _ = (P.α₂ * 3) / realFactorial (r - 2) * (σ k * t ^ (r - 2)) := by ring
      _ ≤ 1 * (σ k * t ^ (r - 2)) := by
          gcongr
          rw [div_le_one hF2]; exact hα'
      _ = σ k * t ^ (r - 2) := one_mul _

end Lemma553

/-! ### Lemma 5.5.4 -/

/-- If $f$ satisfies f.DpH with exponent $\beta$ and $p \ge 1$, then $p + \beta > 1$. -/
theorem AssumptionDpH.one_lt_add {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {H β : ℝ}
    (hf : AssumptionDpH f p H β) (hp : 1 ≤ p) : 1 < (p : ℝ) + β := by
  rcases Nat.lt_or_ge p 2 with h2 | h2
  · have hp1 : p = 1 := by omega
    have := hf.β_pos_of_eq_one hp1
    rw [hp1]; push_cast; linarith
  · have : (2 : ℝ) ≤ p := by exact_mod_cast h2
    linarith [hf.β_nonneg]

/-- The real-power step of the proof of Lemma 5.5.4: let $\sigma, t, K, F, \epsilon > 0$ and
$a, d > 0$. If $\sigma t^d < K$ and $\epsilon < 3 K t^a / F$, then $\sigma < (F/3)^{-d/a}
K^{1+d/a} \epsilon^{-d/a}$. -/
theorem lt_of_rpow_bounds {σ t K F ε a d : ℝ} (hσ : 0 < σ) (ht : 0 < t) (hK : 0 < K)
    (hF : 0 < F) (hε : 0 < ε) (ha : 0 < a) (hd : 0 < d) (h1 : σ * t ^ d < K)
    (h2 : ε < 3 * K / F * t ^ a) :
    σ < (F / 3) ^ (-(d / a)) * K ^ (1 + d / a) * ε ^ (-(d / a)) := by
  set c := 3 * K / F
  have hc : 0 < c := by positivity
  have hx : 0 < d / a := div_pos hd ha
  have h2' : ε / c < t ^ a := by rw [div_lt_iff₀ hc]; linarith
  have h3 : (ε / c) ^ (d / a) < t ^ d := by
    have := Real.rpow_lt_rpow (by positivity) h2' hx
    rwa [← Real.rpow_mul ht.le, mul_div_cancel₀ _ ha.ne'] at this
  have h4 : σ * (ε / c) ^ (d / a) < K :=
    (mul_lt_mul_of_pos_left h3 hσ).trans h1
  have hpos : 0 < (ε / c) ^ (d / a) := by positivity
  have h5 : σ < K / (ε / c) ^ (d / a) := by rw [lt_div_iff₀ hpos]; exact h4
  have heq : K / (ε / c) ^ (d / a) = (F / 3) ^ (-(d / a)) * K ^ (1 + d / a) * ε ^ (-(d / a)) := by
    have hc' : c = K * (F / 3)⁻¹ := by simp only [c]; field_simp
    rw [Real.div_rpow hε.le hc.le, hc', Real.mul_rpow hK.le (by positivity),
      Real.inv_rpow (by positivity), Real.rpow_add hK, Real.rpow_one, Real.rpow_neg (by positivity),
      Real.rpow_neg hε.le]
    have : 0 < ε ^ (d / a) := by positivity
    have : 0 < (F / 3) ^ (d / a) := by positivity
    have : 0 < K ^ (d / a) := by positivity
    field_simp
  rwa [heq] at h5

section Lemma554

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 5.5.4** of [cartis2022evaluation], a lower bound on $\sigma_k$ that ensures success. Let
$f$ satisfy f.DpH with constants $H$ and $\beta$, let $r \ge p + \beta$, and let $p + \beta > 2$
if $\epsilon_2 < \infty$. Along a run of ARp-H, let $k$ be an iteration such that the run does
not terminate at any $j \le k$; in particular, the trial point does not pass the termination
test. If $\sigma_k \ge \bar\sigma$, the right-hand side of (5.5.27) for $\epsilon_2 = \infty$ or
of (5.5.29) for $\epsilon_2 < \infty$, then $\sigma_k \ge \kappa_\beta \|s_k\|^{p+\beta-r}$, so
(5.5.18) holds, and iteration $k$ is very successful: $\rho_k \ge \eta_2$ and (5.5.10)–(5.5.11)
hold.

**Typo.** In the proof of case (b), the source prints the conclusion $\sigma_k <
\kappa_{\beta,2} \epsilon_1^{(p+\beta-r)/(p+\beta-2)}$, with $\epsilon_1$ in place of
$\epsilon_2$. The intended conclusion $\sigma_k < \kappa_{\beta,2}
\epsilon_2^{(p+\beta-r)/(p+\beta-2)}$ contradicts (5.5.29).

The threshold $\bar\sigma$ is `CartisGouldToint.Chapter05.sigmaBar`. -/
theorem lemma_5_5_4 (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    (hr : (p : ℝ) + β ≤ r) (hq2 : ε₂.isSome → 2 < (p : ℝ) + β) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) (hσ : sigmaBar P p H β ε₁ ε₂ ≤ σ k) :
    kappaBeta P p H β * ‖s k‖ ^ ((p : ℝ) + β - r) ≤ σ k ∧
      P.η₂ ≤ taylorRatio f p x s k ∧ arpHLengthTest f P ε₂ (x k) (σ k) (s k) := by
  set q := (p : ℝ) + β
  set t := ‖s k‖
  set κ := kappaBeta P p H β
  have ht : 0 < t := norm_pos_iff.2 (h.step_ne_zero hk)
  have hσ0 := h.sigma_pos fun j hj => hk j hj.le
  have hq1 : 1 < q := hf.one_lt_add h.one_le_p
  have hH := hf.H_nonneg
  have hβ := hf.β_nonneg
  have hκ0 : 0 ≤ κ := kappaBeta_nonneg hH hβ
  have hε₁ := h.ε₁_pos
  -- the thresholds
  have h1 : P.θ₁ * realFactorial (r - 1) ≤ σ k := by
    cases ε₂ <;> simp only [sigmaBar, max_le_iff] at hσ <;> tauto
  have h2 : ε₂.isSome → P.θ₂ * realFactorial (r - 2) ≤ σ k := by
    cases ε₂ with
    | none => simp
    | some e => intro; simp only [sigmaBar, max_le_iff] at hσ; tauto
  have hb1 : kappaBetaJ P p H β 1 * ε₁ ^ ((q - r) / (q - 1)) ≤ σ k := by
    cases ε₂ <;> simp only [sigmaBar, max_le_iff] at hσ <;> tauto
  have hb2 : ∀ e ∈ ε₂, kappaBetaJ P p H β 2 * e ^ ((q - r) / (q - 2)) ≤ σ k := by
    cases ε₂ with
    | none => simp
    | some e =>
      intro e' he'
      rw [Option.mem_def, Option.some_inj] at he'
      subst he'
      simp only [sigmaBar, max_le_iff] at hσ; tauto
  have h18 : κ * t ^ (q - r) ≤ σ k := by
    by_contra hlt
    push Not at hlt
    have hκpos : 0 < κ := by
      rcases hκ0.eq_or_lt with h0 | h0
      · rw [← h0, zero_mul] at hlt; linarith
      · exact h0
    rcases hr.eq_or_lt with heq | hqr
    · -- `r = p + β`
      have hz : q - r = 0 := by linarith
      rw [hz, Real.rpow_zero, mul_one] at hlt
      have : kappaBetaJ P p H β 1 = κ := by
        unfold kappaBetaJ
        rw [show (p : ℝ) + β - r = 0 by linarith, zero_div, Real.rpow_zero, one_mul,
          show (r - 1) / ((p : ℝ) + β - 1) = 1 by rw [div_eq_one_iff_eq (by linarith)]; linarith,
          Real.rpow_one]
      rw [hz, zero_div, Real.rpow_zero, mul_one, this] at hb1
      linarith
    · set d := r - q
      have hd : 0 < d := sub_pos.2 hqr
      have hσt : σ k * t ^ d < κ := by
        have h0 : t ^ (q - r) * t ^ d = 1 := by
          rw [rpow_mul_rpow_sub ht r, sub_self, Real.rpow_zero]
        have := mul_lt_mul_of_pos_right hlt (by positivity : 0 < t ^ d)
        rwa [mul_assoc, h0, mul_one] at this
      obtain ⟨hg, hl⟩ := lemma_5_5_2 hf h hk
      have hnot := not_stopTest_trial hk
      -- the case `‖∇f(x_k + s_k)‖ > ε₁`
      have hcase1 : ¬ ε₁ < ‖gradient f (x k + s k)‖ := by
        intro hgt
        have hF1 := realFactorial_pos (r - 1)
        have hA : H / holderFactorial (p - 1) β * t ^ (q - 1) ≤ κ / realFactorial (r - 1) *
            t ^ (q - 1) :=
          mul_le_mul_of_nonneg_right (div_holderFactorial_le_kappaBeta hH hβ h.one_lt_r.le)
            (by positivity)
        have hsplit : t ^ (r - 1) = t ^ d * t ^ (q - 1) := (rpow_mul_rpow_sub ht q).symm
        have hB : σ k / realFactorial (r - 1) * t ^ (r - 1) < κ / realFactorial (r - 1) *
            t ^ (q - 1) := by
          rw [hsplit, div_mul_eq_mul_div, div_mul_eq_mul_div, ← mul_assoc]
          gcongr
        have hθ : P.θ₁ * t ^ (r - 1) ≤ σ k / realFactorial (r - 1) * t ^ (r - 1) :=
          mul_le_mul_of_nonneg_right ((le_div_iff₀ hF1).2 h1) (by positivity)
        have h3 : ε₁ < 3 * κ / realFactorial (r - 1) * t ^ (q - 1) := by
          have : 3 * κ / realFactorial (r - 1) * t ^ (q - 1) =
              3 * (κ / realFactorial (r - 1) * t ^ (q - 1)) := by ring
          linarith
        have key := lt_of_rpow_bounds hσ0 ht hκpos hF1 hε₁ (by linarith) hd hσt h3
        have e1 : -(d / (q - 1)) = (q - r) / (q - 1) := by simp only [d]; ring
        have e2 : 1 + d / (q - 1) = (r - 1) / (q - 1) := by
          have hne : q - 1 ≠ 0 := by linarith
          rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]; simp only [d]; ring
        rw [e1, e2] at key
        have : kappaBetaJ P p H β 1 * ε₁ ^ ((q - r) / (q - 1)) =
            (realFactorial (r - 1) / 3) ^ ((q - r) / (q - 1)) * κ ^ ((r - 1) / (q - 1)) *
              ε₁ ^ ((q - r) / (q - 1)) := by
          unfold kappaBetaJ; rfl
        linarith
      cases ε₂ with
      | none =>
        rw [stopTest_none, not_le] at hnot
        exact hcase1 hnot
      | some e =>
        rcases not_stopTest_some.1 hnot with hgt | hlam
        · exact hcase1 hgt
        · have he := h.ε₂_pos e rfl
          have hq2' : 2 < q := hq2 rfl
          have hp2 := h.two_le_p rfl
          have hF2 := realFactorial_pos (r - 2)
          have hA : H / holderFactorial (p - 2) β * t ^ (q - 2) ≤ κ / realFactorial (r - 2) *
              t ^ (q - 2) :=
            mul_le_mul_of_nonneg_right (div_holderFactorial_le_kappaBeta_two hH hβ hp2 hr)
              (by positivity)
          have hsplit : t ^ (r - 2) = t ^ d * t ^ (q - 2) := (rpow_mul_rpow_sub ht q).symm
          have hB : σ k / realFactorial (r - 2) * t ^ (r - 2) < κ / realFactorial (r - 2) *
              t ^ (q - 2) := by
            rw [hsplit, div_mul_eq_mul_div, div_mul_eq_mul_div, ← mul_assoc]
            gcongr
          have hθ : P.θ₂ * t ^ (r - 2) ≤ σ k / realFactorial (r - 2) * t ^ (r - 2) :=
            mul_le_mul_of_nonneg_right ((le_div_iff₀ hF2).2 (h2 rfl)) (by positivity)
          have hl' := hl rfl
          have h3 : e < 3 * κ / realFactorial (r - 2) * t ^ (q - 2) := by
            have : 3 * κ / realFactorial (r - 2) * t ^ (q - 2) =
                3 * (κ / realFactorial (r - 2) * t ^ (q - 2)) := by ring
            linarith
          have key := lt_of_rpow_bounds hσ0 ht hκpos hF2 he (by linarith) hd hσt h3
          have e1 : -(d / (q - 2)) = (q - r) / (q - 2) := by simp only [d]; ring
          have e2 : 1 + d / (q - 2) = (r - 2) / (q - 2) := by
            have hne : q - 2 ≠ 0 := by linarith
            rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]; simp only [d]; ring
          rw [e1, e2] at key
          have hb := hb2 e rfl
          have : kappaBetaJ P p H β 2 * e ^ ((q - r) / (q - 2)) =
              (realFactorial (r - 2) / 3) ^ ((q - r) / (q - 2)) * κ ^ ((r - 2) / (q - 2)) *
                e ^ ((q - r) / (q - 2)) := by
            unfold kappaBetaJ; rfl
          linarith
  exact ⟨h18, lemma_5_5_3 hf h hr hk h1 h2 h18⟩

end Lemma554

/-! ### Lemma 5.5.5 -/

section Lemma555

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- For $\epsilon \in (0, 1]$ and $r \ge q > j$, $\epsilon^{(q-r)/(q-j)} \ge 1$. -/
theorem one_le_rpow_exponent {ε q j : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hqj : j < q) (hr : q ≤ r) :
    1 ≤ ε ^ ((q - r) / (q - j)) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

/-- Let $f$ satisfy f.DpH, let $r \ge p + \beta$, and let $p + \beta > 2$ if $\epsilon_2 < \infty$.
Along a run of ARp-H, the tolerance factor (5.5.41) is at least $1$, because the tolerances are
at most $1$. -/
theorem one_le_epsMax (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    (hr : (p : ℝ) + β ≤ r) (hq2 : ε₂.isSome → 2 < (p : ℝ) + β) : 1 ≤ epsMax p β r ε₁ ε₂ := by
  have hq1 := hf.one_lt_add h.one_le_p
  cases ε₂ with
  | none => exact one_le_rpow_exponent h.ε₁_pos h.ε₁_le_one hq1 hr
  | some e => exact le_max_of_le_left (one_le_rpow_exponent h.ε₁_pos h.ε₁_le_one hq1 hr)

/-- **Lemma 5.5.5** of [cartis2022evaluation], an upper bound on $\sigma_k$. Let $f$ satisfy f.DpH
with constants $H$ and $\beta$, let $r \ge p + \beta$, and let $p + \beta > 2$ if
$\epsilon_2 < \infty$. Along a run of ARp-H, if the run does not terminate at any iteration
$j < k$, then $\sigma_k \le \max(\sigma_0, \gamma_3 \bar\sigma)$ by (5.5.39)–(5.5.40), and hence
$$\sigma_k \le \sigma_H \max\left[\epsilon_1^{(p+\beta-r)/(p+\beta-1)},
  \epsilon_2^{(p+\beta-r)/(p+\beta-2)}\right] \quad \text{(5.5.41)}.$$
For $\epsilon_2 = \infty$ the second bound reads $\sigma_k \le \sigma_{H,1}
\epsilon_1^{(p+\beta-r)/(p+\beta-1)}$.

The bound covers every iteration up to and including termination. The threshold $\bar\sigma$ is
`CartisGouldToint.Chapter05.sigmaBar`. -/
theorem lemma_5_5_5 (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    (hr : (p : ℝ) + β ≤ r) (hq2 : ε₂.isSome → 2 < (p : ℝ) + β) {k : ℕ}
    (hk : ∀ j < k, ¬ arpHStop f ε₁ ε₂ x s j) :
    σ k ≤ max P.σ₀ (P.γ₃ * sigmaBar P p H β ε₁ ε₂) ∧
      σ k ≤ sigmaH P p H β ε₂ * epsMax p β r ε₁ ε₂ := by
  have hforce : ∀ k, (∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) →
      sigmaBar P p H β ε₁ ε₂ ≤ σ k → P.η₂ ≤ arpHRatio f p P ε₂ x s σ k := by
    intro k hk hσ
    obtain ⟨-, hρ, hlen⟩ := lemma_5_5_4 hf h hr hq2 hk hσ
    rw [arpHRatio, arpHRatioAt_of_lengthTest hlen]
    exact hρ
  have h1 := (h.run.sigma_le_max hforce hk k le_rfl).2.2
  refine ⟨h1, h1.trans ?_⟩
  have hM := one_le_epsMax hf h hr hq2
  have hγ := P.γ₃_pos.le
  have hq1 := hf.one_lt_add h.one_le_p
  have hε₁ := h.ε₁_pos
  have hσ₀ := P.σ₀_pos
  cases ε₂ with
  | none =>
    simp only [sigmaH, sigmaBar, epsMax] at hM ⊢
    set M := ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1))
    set S := max P.σ₀ (max (P.γ₃ * (P.θ₁ * realFactorial (r - 1)))
      (P.γ₃ * kappaBetaJ P p H β 1))
    have hS : 0 ≤ S := hσ₀.le.trans (le_max_left _ _)
    have hSM : S ≤ S * M := le_mul_of_one_le_right hS hM
    refine max_le ((le_max_left _ _).trans hSM) ?_
    rw [mul_max_of_nonneg _ _ hγ]
    refine max_le (le_trans ?_ hSM) ?_
    · exact le_max_of_le_right (le_max_left _ _)
    · rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (by positivity)
  | some e =>
    have he := h.ε₂_pos e rfl
    simp only [sigmaH, sigmaBar, epsMax] at hM ⊢
    set E₁ := ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1))
    set E₂ := e ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 2))
    set S := max P.σ₀ (max (max (P.γ₃ * (P.θ₁ * realFactorial (r - 1)))
      (P.γ₃ * (P.θ₂ * realFactorial (r - 2))))
      (max (P.γ₃ * kappaBetaJ P p H β 1) (P.γ₃ * kappaBetaJ P p H β 2)))
    have hS : 0 ≤ S := hσ₀.le.trans (le_max_left _ _)
    have hSM : S ≤ S * max E₁ E₂ := le_mul_of_one_le_right hS hM
    refine max_le ((le_max_left _ _).trans hSM) ?_
    rw [mul_max_of_nonneg _ _ hγ, mul_max_of_nonneg _ _ hγ, mul_max_of_nonneg _ _ hγ]
    refine max_le (max_le (le_trans ?_ hSM) (le_trans ?_ hSM)) (max_le ?_ ?_)
    · exact le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
    · exact le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
    · rw [← mul_assoc]
      exact mul_le_mul (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
        (le_max_left _ _) (by positivity) hS
    · rw [← mul_assoc]
      exact mul_le_mul (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
        (le_max_right _ _) (by positivity) hS

end Lemma555

/-! ### Lemma 5.5.6 -/

/-- The real-power chain of the proof of Lemma 5.5.6: let $\sigma, \alpha, g, m, S, M > 0$,
$t, \delta \ge 0$ and $m \le r$. If $\alpha g \le \sigma t^m$, $\sigma \le S M$ and
$\delta^m M^{r-m} \le g^r$, then $(\alpha^r / S^{r-m})^{1/m} \delta \le \sigma t^r$. -/
theorem rpow_mul_le_mul_rpow {σ t α g m r S M δ : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) (hα : 0 < α)
    (hg : 0 < g) (hm : 0 < m) (hmr : m ≤ r) (hS : 0 < S) (hM : 0 < M) (hσS : σ ≤ S * M)
    (hδ : 0 ≤ δ) (hlen : α * g ≤ σ * t ^ m) (hδM : δ ^ m * M ^ (r - m) ≤ g ^ r) :
    (α ^ r / S ^ (r - m)) ^ (1 / m) * δ ≤ σ * t ^ r := by
  have hr : 0 < r := hm.trans_le hmr
  have hrm : 0 ≤ r - m := sub_nonneg.2 hmr
  have him : 0 ≤ 1 / m := by positivity
  -- `(α^r g^r/σ^{r-m})^{1/m} ≤ σ t^r`
  have h1 : (α ^ r * g ^ r / σ ^ (r - m)) ^ (1 / m) ≤ σ * t ^ r := by
    have hY : 0 ≤ σ * t ^ r := by positivity
    have hX : α ^ r * g ^ r / σ ^ (r - m) ≤ (σ * t ^ r) ^ m := by
      have heq : (σ * t ^ r) ^ m * σ ^ (r - m) = (σ * t ^ m) ^ r := by
        rw [Real.mul_rpow hσ.le (by positivity), Real.mul_rpow hσ.le (by positivity),
          ← Real.rpow_mul ht, ← Real.rpow_mul ht, mul_comm r m,
          show σ ^ r = σ ^ m * σ ^ (r - m) by rw [← Real.rpow_add hσ]; ring_nf]
        ring
      rw [div_le_iff₀ (by positivity), heq, ← Real.mul_rpow hα.le hg.le]
      exact Real.rpow_le_rpow (by positivity) hlen hr.le
    calc (α ^ r * g ^ r / σ ^ (r - m)) ^ (1 / m) ≤ ((σ * t ^ r) ^ m) ^ (1 / m) :=
          Real.rpow_le_rpow (by positivity) hX him
      _ = σ * t ^ r := by rw [one_div, Real.rpow_rpow_inv hY hm.ne']
  -- replace `σ` by `S M`
  have h2 : (α ^ r * g ^ r / (S * M) ^ (r - m)) ^ (1 / m) ≤
      (α ^ r * g ^ r / σ ^ (r - m)) ^ (1 / m) := by
    refine Real.rpow_le_rpow (by positivity) ?_ him
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (Real.rpow_le_rpow hσ.le hσS hrm)
  have h3 : (α ^ r * g ^ r / (S * M) ^ (r - m)) ^ (1 / m) =
      (α ^ r / S ^ (r - m)) ^ (1 / m) * (g ^ r / M ^ (r - m)) ^ (1 / m) := by
    have : α ^ r * g ^ r / (S * M) ^ (r - m) = (α ^ r / S ^ (r - m)) * (g ^ r / M ^ (r - m)) := by
      rw [Real.mul_rpow hS.le hM.le]; field_simp
    rw [this, Real.mul_rpow (by positivity) (by positivity)]
  have h4 : δ ≤ (g ^ r / M ^ (r - m)) ^ (1 / m) := by
    have : δ ^ m ≤ g ^ r / M ^ (r - m) := by rw [le_div_iff₀ (by positivity)]; exact hδM
    calc δ = (δ ^ m) ^ (1 / m) := by rw [one_div, Real.rpow_rpow_inv hδ hm.ne']
      _ ≤ _ := Real.rpow_le_rpow (by positivity) this him
  calc (α ^ r / S ^ (r - m)) ^ (1 / m) * δ ≤
        (α ^ r / S ^ (r - m)) ^ (1 / m) * (g ^ r / M ^ (r - m)) ^ (1 / m) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := h3.symm
    _ ≤ _ := h2
    _ ≤ _ := h1

/-- The tolerance algebra of (5.5.48)–(5.5.51) for $\epsilon_2 = \infty$: for $\epsilon > 0$ and
$q > 1$, $(\epsilon^{q/(q-1)})^{r-1} (\epsilon^{(q-r)/(q-1)})^{r-(r-1)} = \epsilon^r$. -/
theorem rpow_tolerance_eq {ε q r : ℝ} (hε : 0 < ε) (hq : 1 < q) :
    (ε ^ (q / (q - 1))) ^ (r - 1) * (ε ^ ((q - r) / (q - 1))) ^ (r - (r - 1)) = ε ^ r := by
  rw [← Real.rpow_mul hε.le, ← Real.rpow_mul hε.le, ← Real.rpow_add hε]
  congr 1
  have : q - 1 ≠ 0 := by linarith
  field_simp; ring

/-- The tolerance algebra of (5.5.48)–(5.5.51) for $\epsilon_2 < \infty$: let
$\epsilon_1, \epsilon_2 > 0$ and $r \ge q > 2$, and put $\delta = \min[\epsilon_1^{q/(q-1)},
\epsilon_2^{q/(q-2)}]$ and $M = \max[\epsilon_1^{(q-r)/(q-1)}, \epsilon_2^{(q-r)/(q-2)}]$. Then
$\delta^{r-1} M \le \epsilon_1^r$ and $\delta^{r-2} M^2 \le \epsilon_2^r$. -/
theorem rpow_tolerance_le {ε₁ ε₂ q r : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hq : 2 < q)
    (hr : q ≤ r) :
    (min (ε₁ ^ (q / (q - 1))) (ε₂ ^ (q / (q - 2)))) ^ (r - 1) *
        (max (ε₁ ^ ((q - r) / (q - 1))) (ε₂ ^ ((q - r) / (q - 2)))) ^ (r - (r - 1)) ≤
        ε₁ ^ r ∧
      (min (ε₁ ^ (q / (q - 1))) (ε₂ ^ (q / (q - 2)))) ^ (r - 2) *
        (max (ε₁ ^ ((q - r) / (q - 1))) (ε₂ ^ ((q - r) / (q - 2)))) ^ (r - (r - 2)) ≤
        ε₂ ^ r := by
  set X₁ := Real.log ε₁ / (q - 1)
  set X₂ := Real.log ε₂ / (q - 2)
  have ha₁ : q - 1 ≠ 0 := by linarith
  have ha₂ : q - 2 ≠ 0 := by linarith
  have hL₁ : Real.log ε₁ = X₁ * (q - 1) := by simp only [X₁]; field_simp
  have hL₂ : Real.log ε₂ = X₂ * (q - 2) := by simp only [X₂]; field_simp
  have e1 : ε₁ ^ (q / (q - 1)) = Real.exp (q * X₁) := by
    rw [Real.rpow_def_of_pos hε₁, hL₁]; congr 1; field_simp
  have e2 : ε₂ ^ (q / (q - 2)) = Real.exp (q * X₂) := by
    rw [Real.rpow_def_of_pos hε₂, hL₂]; congr 1; field_simp
  have e3 : ε₁ ^ ((q - r) / (q - 1)) = Real.exp ((q - r) * X₁) := by
    rw [Real.rpow_def_of_pos hε₁, hL₁]; congr 1; field_simp
  have e4 : ε₂ ^ ((q - r) / (q - 2)) = Real.exp ((q - r) * X₂) := by
    rw [Real.rpow_def_of_pos hε₂, hL₂]; congr 1; field_simp
  have e5 : ε₁ ^ r = Real.exp (X₁ * (q - 1) * r) := by rw [Real.rpow_def_of_pos hε₁, hL₁]
  have e6 : ε₂ ^ r = Real.exp (X₂ * (q - 2) * r) := by rw [Real.rpow_def_of_pos hε₂, hL₂]
  rw [e1, e2, e3, e4, e5, e6]
  have hq0 : 0 ≤ q := by linarith
  have hqr : q - r ≤ 0 := by linarith
  have hr0 : 0 ≤ r := by linarith
  rcases le_total X₁ X₂ with h12 | h21
  · rw [min_eq_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h12 hq0)),
      max_eq_left (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left h12 hqr))]
    simp only [← Real.exp_mul, ← Real.exp_add]
    refine ⟨le_of_eq (by congr 1; ring), Real.exp_le_exp.2 ?_⟩
    have : X₁ * ((q - 2) * r) ≤ X₂ * ((q - 2) * r) :=
      mul_le_mul_of_nonneg_right h12 (by nlinarith)
    nlinarith
  · rw [min_eq_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h21 hq0)),
      max_eq_right (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left h21 hqr))]
    simp only [← Real.exp_mul, ← Real.exp_add]
    refine ⟨Real.exp_le_exp.2 ?_, le_of_eq (by congr 1; ring)⟩
    have : X₂ * ((q - 1) * r) ≤ X₁ * ((q - 1) * r) :=
      mul_le_mul_of_nonneg_right h21 (by nlinarith)
    nlinarith

section Lemma556

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 5.5.6** of [cartis2022evaluation], decrease on successful iterations. Let $f$ satisfy
f.DpH with constants $H$ and $\beta$, let $r \ge p + \beta$, and let $p + \beta > 2$ if
$\epsilon_2 < \infty$. Along a run of ARp-H, let $k$ be a successful iteration
($\tilde\rho_k \ge \eta_1$) such that the run does not terminate at any $j \le k$. Then:
* (i) if $\epsilon_2 = \infty$, then $f(x_k) - f(x_{k+1}) \ge \kappa_{H,1}
  \epsilon_1^{(p+\beta)/(p+\beta-1)}$;
* (ii) if $\epsilon_2 < \infty$, then $f(x_k) - f(x_{k+1}) \ge \kappa_{H,2}
  \min[\epsilon_1^{(p+\beta)/(p+\beta-1)}, \epsilon_2^{(p+\beta)/(p+\beta-2)}]$ (5.5.44).

The constants $\kappa_{H,1}$ and $\kappa_{H,2}$ are `CartisGouldToint.Chapter05.kappaH` of
(5.5.45). The condition $p + \beta > 1$ follows from f.DpH. -/
theorem lemma_5_5_6 (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    (hr : (p : ℝ) + β ≤ r) (hq2 : ε₂.isSome → 2 < (p : ℝ) + β) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) (hs : P.η₁ ≤ arpHRatio f p P ε₂ x s σ k) :
    kappaH P p H β ε₂ * deltaEps p β ε₁ ε₂ ≤ f (x k) - f (x (k + 1)) := by
  set q := (p : ℝ) + β
  set t := ‖s k‖
  obtain ⟨hρ, hlen⟩ := le_arpHRatioAt_iff.1 hs
  have hx1 : x (k + 1) = x k + s k := h.run.eq_add_of_succ hk hs
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hr1 := h.one_lt_r
  have hq1 : 1 < q := hf.one_lt_add h.one_le_p
  have hε₁ := h.ε₁_pos
  have hrf := realFactorial_pos r
  have ht : 0 ≤ t := norm_nonneg _
  have hdec := lemma_5_5_1 h hk
  have hΔ : 0 < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
    lt_of_le_of_lt (by positivity) hdec
  have hfd := sub_le_of_le_reductionRatio hΔ hρ
  rw [← hx1] at hfd
  have hD : P.η₁ / realFactorial r * (σ k * t ^ r) ≤ f (x k) - f (x (k + 1)) := by
    have := mul_le_mul_of_nonneg_left hdec.le P.η₁_pos.le
    calc P.η₁ / realFactorial r * (σ k * t ^ r) = P.η₁ * (σ k / realFactorial r * t ^ r) := by
          ring
      _ ≤ _ := this
      _ ≤ _ := hfd
  have hσmax := (lemma_5_5_5 hf h hr hq2 fun j hj => hk j hj.le).2
  have hM := one_le_epsMax hf h hr hq2
  have hSpos : 0 < sigmaH P p H β ε₂ := by
    cases ε₂ <;> exact P.σ₀_pos.trans_le (le_max_left _ _)
  have hnot := not_stopTest_trial hk
  have hη : 0 ≤ P.η₁ / realFactorial r := by have := P.η₁_pos; positivity
  have hpow : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → a ^ r ≤ b ^ r := fun ha hab =>
    Real.rpow_le_rpow ha hab (by linarith)
  refine le_trans ?_ hD
  cases ε₂ with
  | none =>
    rw [stopTest_none, not_le] at hnot
    simp only [kappaH, deltaEps, epsMax, sigmaH] at hσmax hM hSpos ⊢
    have key := rpow_mul_le_mul_rpow hσ ht P.α₁_pos (hε₁.trans hnot) (by linarith)
      (by linarith) hSpos (by linarith) hσmax (by positivity) hlen.1
      ((rpow_tolerance_eq hε₁ hq1).le.trans (hpow hε₁.le hnot.le))
    rw [show r - (r - 1) = 1 by ring, Real.rpow_one] at key
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left key hη
  | some e =>
    have he := h.ε₂_pos e rfl
    have hq2' : 2 < q := hq2 rfl
    have tol := rpow_tolerance_le hε₁ he hq2' hr
    simp only [kappaH, deltaEps, epsMax] at hσmax hM ⊢
    rcases not_stopTest_some.1 hnot with hg | hl
    · have key := rpow_mul_le_mul_rpow hσ ht P.α₁_pos (hε₁.trans hg) (by linarith)
        (by linarith) hSpos (by linarith) hσmax (by positivity) hlen.1
        (tol.1.trans (hpow hε₁.le hg.le))
      rw [show r - (r - 1) = 1 by ring, Real.rpow_one] at key
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (le_trans ?_ key) hη
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    · have hg2 : e < -Chapter01.hessianMinEig f (x k + s k) := by linarith
      have hlen2 : P.α₂ * -Chapter01.hessianMinEig f (x k + s k) ≤ σ k * t ^ (r - 2) := by
        have := hlen.2 rfl; linarith
      have key := rpow_mul_le_mul_rpow hσ ht P.α₂_pos (he.trans hg2)
        (by linarith [h.two_lt_r rfl]) (by linarith) hSpos (by linarith) hσmax
        (by positivity) hlen2 (tol.2.trans (hpow he.le hg2.le))
      rw [show r - (r - 2) = (2 : ℝ) by ring, Real.rpow_two] at key
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (le_trans ?_ key) hη
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)

end Lemma556

/-! ### Theorem 5.5.7 -/

/-- The logarithmic tolerance terms of (5.5.52), multiplied by $\log \gamma_2$:
$\frac{r-p-\beta}{p+\beta-1} |\log \epsilon_1|$, plus
$\frac{r-p-\beta}{p+\beta-2} |\log \epsilon_2|$ if $\epsilon_2 < \infty$. -/
noncomputable def epsLogTerm (p : ℕ) (β r ε₁ : ℝ) : Option ℝ → ℝ
  | none => (r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε₁|
  | some e => (r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε₁| +
      (r - ((p : ℝ) + β)) / ((p : ℝ) + β - 2) * |Real.log e|

/-- For $\epsilon > 0$ and $r \ge q > j$, $\log \epsilon^{(q-r)/(q-j)} \le \frac{r-q}{q-j} |\log
\epsilon|$. -/
theorem log_rpow_exponent_le {ε q j : ℝ} (hε : 0 < ε) (hqj : j < q) (hr : q ≤ r) :
    Real.log (ε ^ ((q - r) / (q - j))) ≤ (r - q) / (q - j) * |Real.log ε| := by
  rw [Real.log_rpow hε]
  have hc : 0 ≤ (r - q) / (q - j) := div_nonneg (by linarith) (by linarith)
  have : (q - r) / (q - j) * Real.log ε = (r - q) / (q - j) * -Real.log ε := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (neg_le_abs _) hc

section Theorem557

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β flow : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- The decrease constant $\kappa_H$ of (5.5.45) is positive. -/
theorem kappaH_pos :
    0 < kappaH P p H β ε₂ := by
  have := P.η₁_pos; have := realFactorial_pos r; have := P.α₁_pos; have := P.α₂_pos
  cases ε₂ with
  | none =>
    have : 0 < sigmaH P p H β none := P.σ₀_pos.trans_le (le_max_left _ _)
    simp only [kappaH]; positivity
  | some e =>
    have : 0 < sigmaH P p H β (some e) := P.σ₀_pos.trans_le (le_max_left _ _)
    simp only [kappaH]
    refine mul_pos (by positivity) (lt_min (by positivity) (by positivity))

/-- Along a run of ARp-H, the decrease order $\delta_\epsilon$ is positive. -/
theorem deltaEps_pos (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ) : 0 < deltaEps p β ε₁ ε₂ := by
  have := h.ε₁_pos
  cases ε₂ with
  | none => simp only [deltaEps]; positivity
  | some e =>
    have := h.ε₂_pos e rfl
    simp only [deltaEps]; exact lt_min (by positivity) (by positivity)

/-- **Theorem 5.5.7** of [cartis2022evaluation], complexity of ARp-H. Let $f$ be bounded below by
$f_{\mathrm{low}}$ (f.Bb), let $f$ satisfy f.DpH with constants $H$ and $\beta$, let
$r \ge p + \beta$, and let $p + \beta > 2$ if $\epsilon_2 < \infty$. Then every run of ARp-H
terminates at a first iteration $k_\epsilon$, with an output $x_\epsilon$ that passes the
termination test and is either $x_0$, with $k_\epsilon = 0$, or the trial point
$x_{k_\epsilon} + s_{k_\epsilon}$. Moreover, $k_\epsilon + 2$ is at most
$$\kappa^A \frac{f(x_0) - f_{\mathrm{low}}}{\delta_\epsilon} + \kappa^B_1 |\log \epsilon_1| +
  \kappa^B_2 |\log \epsilon_2| + \kappa^C \quad \text{(5.5.52)},$$
where $\delta_\epsilon = \min[\epsilon_1^{(p+\beta)/(p+\beta-1)},
\epsilon_2^{(p+\beta)/(p+\beta-2)}]$, $\kappa^S = 1 / \kappa_H$, $\kappa^A = \kappa^S (1 + |\log
\gamma_1| / \log \gamma_2)$, $\kappa^B_j = (r-p-\beta) / ((p+\beta-j) \log \gamma_2)$ and
$\kappa^C = (|\log \gamma_1| + \log(\sigma_H / \sigma_0)) / \log \gamma_2 + 2$. This bounds the
number of evaluations of the first (and second) derivatives that the termination test needs, at
$x_0$ and at the trial points of iterations $0, \dots, k_\epsilon$, which is at most
$k_\epsilon + 2$. It also bounds the number of evaluations of $f$, at $x_0$ and at the trial
points of iterations $0, \dots, k_\epsilon - 1$, which is at most $k_\epsilon + 1$. Finally, the
number of evaluations of the derivatives of orders up to $p$, at $x_0$ and after each successful
iteration, is at most $\kappa^S (f(x_0) - f_{\mathrm{low}}) / \delta_\epsilon + 1$.

**Correction.** The source counts $k_\epsilon + 1$ evaluations (Lemma 2.4.1), but the function
and its derivatives are evaluated at $x_0$ and at every trial point, that is, $k_\epsilon + 2$
times. The constant $\kappa^C$ of the source lacks the term $+ 2$.

For $\epsilon_2 = \infty$ the terms with $\epsilon_2$ are absent. The logarithmic terms are
`CartisGouldToint.Chapter05.epsLogTerm` divided by $\log \gamma_2$, and the last count is
`Optimization.derivEvalCount` of the successful iterations. -/
theorem theorem_5_5_7 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionDpH f p H β)
    (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ) (hr : (p : ℝ) + β ≤ r)
    (hq2 : ε₂.isSome → 2 < (p : ℝ) + β) :
    ∃ kε, IsFirstHit (arpHStop f ε₁ ε₂ x s) kε ∧
      (∃ xε, (kε = 0 ∧ xε = x 0 ∨ xε = x kε + s kε) ∧ stopTest f ε₁ ε₂ xε) ∧
      (kε : ℝ) + 2 ≤
        1 / kappaH P p H β ε₂ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f (x 0) - flow) /
            deltaEps p β ε₁ ε₂ + epsLogTerm p β r ε₁ ε₂ / Real.log P.γ₂ +
          ((|Real.log P.γ₁| + Real.log (sigmaH P p H β ε₂ / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ arpHRatio f p P ε₂ x s σ k) kε : ℝ) ≤
        1 / kappaH P p H β ε₂ * (f (x 0) - flow) / deltaEps p β ε₁ ε₂ + 1 := by
  set κ := kappaH P p H β ε₂
  set δε := deltaEps p β ε₁ ε₂
  set S := sigmaH P p H β ε₂
  set M := epsMax p β r ε₁ ε₂
  have hκ : 0 < κ := kappaH_pos
  have hδε : 0 < δε := deltaEps_pos h
  have hδ : 0 < κ * δε := mul_pos hκ hδε
  have hM := one_le_epsMax hf h hr hq2
  have hS : 0 < S := by cases ε₂ <;> exact P.σ₀_pos.trans_le (le_max_left _ _)
  have hσ₀ := P.σ₀_pos
  have hlog := P.log_γ₂_pos
  have hdec : ∀ k, (∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) →
      P.η₁ ≤ arpHRatio f p P ε₂ x s σ k → κ * δε ≤ f (x k) - f (x (k + 1)) :=
    fun k hk hs => lemma_5_5_6 hf h hr hq2 hk hs
  obtain ⟨kε, hK, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease_of_le (σmax := S * M)
    (V := fun k => f (x k)) (Vlow := flow)
    (fun k hk => (lemma_5_5_5 hf h hr hq2 hk).2) hδ
    (fun k hk => by
      by_cases hs : P.η₁ ≤ arpHRatio f p P ε₂ x s σ k
      · have := hdec k hk hs; linarith
      · rw [h.run.eq_of_not_succ hk (not_le.1 hs)])
    (fun k _ => hb _) hdec
  refine ⟨kε, hK, ?_, ?_, ?_⟩
  · rcases hK.test with ⟨h0, ht⟩ | ht
    · exact ⟨x 0, Or.inl ⟨h0, rfl⟩, by rwa [h0] at ht⟩
    · exact ⟨x kε + s kε, Or.inr rfl, ht⟩
  · have hX : (f (x 0) - flow) / (κ * δε) = 1 / κ * (f (x 0) - flow) / δε := by
      field_simp
    have hlogM : Real.log M ≤ epsLogTerm p β r ε₁ ε₂ := by
      have hq1 := hf.one_lt_add h.one_le_p
      cases ε₂ with
      | none => exact log_rpow_exponent_le h.ε₁_pos hq1 hr
      | some e =>
        have he := h.ε₂_pos e rfl
        have h1 := log_rpow_exponent_le (r := r) h.ε₁_pos hq1 hr
        have h2 := log_rpow_exponent_le (r := r) he (hq2 rfl) hr
        have hc1 : 0 ≤ (r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε₁| :=
          mul_nonneg (div_nonneg (by linarith) (by linarith)) (abs_nonneg _)
        have hc2 : 0 ≤ (r - ((p : ℝ) + β)) / ((p : ℝ) + β - 2) * |Real.log e| :=
          mul_nonneg (div_nonneg (by linarith) (by linarith [hq2 rfl])) (abs_nonneg _)
        simp only [M, epsMax, epsLogTerm] at h1 h2 ⊢
        rcases max_choice (ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1)))
          (e ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 2))) with hm | hm <;> rw [hm] <;> linarith
    have hlogS : Real.log (S * M / P.σ₀) = Real.log (S / P.σ₀) + Real.log M := by
      rw [mul_div_right_comm, Real.log_mul (by positivity) (by positivity)]
    have hγ : 0 ≤ |Real.log P.γ₁| / Real.log P.γ₂ := by positivity
    rw [funEvalCount, hX, hlogS] at hF
    push_cast at hF
    have : (Real.log (S / P.σ₀) + Real.log M) / Real.log P.γ₂ ≤
        epsLogTerm p β r ε₁ ε₂ / Real.log P.γ₂ + Real.log (S / P.σ₀) / Real.log P.γ₂ := by
      rw [← add_div, add_comm (epsLogTerm _ _ _ _ _)]
      exact div_le_div_of_nonneg_right (by linarith) hlog.le
    have e1 : 1 / κ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f (x 0) - flow) / δε =
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (1 / κ * (f (x 0) - flow) / δε) := by ring
    rw [e1, add_div (|Real.log P.γ₁|)]
    linarith
  · have hX : (f (x 0) - flow) / (κ * δε) = 1 / κ * (f (x 0) - flow) / δε := by
      field_simp
    rwa [hX] at hD

end Theorem557

end CartisGouldToint.Chapter05
