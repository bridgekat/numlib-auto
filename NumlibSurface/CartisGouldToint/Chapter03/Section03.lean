/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.SlowExample.ARp
import NumlibSurface.CartisGouldToint.Chapter02.Section04
import NumlibSurface.CartisGouldToint.Chapter03.Section02

/-!
# Cartis, Gould and Toint, Section 3.3: Adaptive regularization using second derivatives

This module formalizes §3.3 of [cartis2022evaluation]: the second-order adaptive-regularization
algorithm AR2 for the minimization of a function $f : \mathbb{R}^n \to \mathbb{R}$. At iteration $k$
the method computes an approximate minimizer $s_k$ of the cubic model (3.3.1)
$$m_k(s) = T_{f,2}(x_k, s) + \frac{\sigma_k}{6} \|s\|^3$$
that satisfies the accuracy conditions (3.3.5)–(3.3.6). It accepts the trial point when the ratio
(3.3.7) of achieved to predicted decrease is at least $\eta_1$, and it updates $\sigma_k$ by
(3.3.8). The method stops at the first iterate that passes the test (3.3.4), the test (3.2.9) of
TR2.

Under f.Bb and f.HL, AR2 stops after $O(\epsilon_1^{-3/2})$ evaluations when $\epsilon_2 = \infty$
(Theorem 3.3.5), and after $O(\max(\epsilon_1^{-3/2}, \epsilon_2^{-3}))$ evaluations otherwise
(Theorem 3.3.9). Both orders are attained by one-dimensional examples (Theorems 3.3.6 and 3.3.10).
The module also treats the modified AR2 algorithm of §3.3.2, which uses the condition (3.3.23) in
place of (3.3.5). AR2 is an instance of the generic adaptive-regularization run of
`Numlib.Optimization.ModelBased.ARRun`, and the examples come from
`Numlib.Optimization.Complexity.SlowExample.ARp`.

## Main definitions

* (3.3.1), `CartisGouldToint.Chapter03.ar2Model`: the cubic model $m(s) = T_{f,2}(x, s) +
  \frac{\sigma}{6} \|s\|^3$.
* (3.3.3), `CartisGouldToint.Chapter03.AR2Params`: the constants of AR1 and the step-accuracy
  parameters $\theta_1, \theta_2 > 0$.
* (3.3.5)–(3.3.6), `CartisGouldToint.Chapter03.ar2Step`: the Step-2 conditions on the step.
* Algorithm 3.3.1, `CartisGouldToint.Chapter03.algorithm_3_3_1`: AR2 as a predicate on the sequences
  of a run.
* (3.3.14), `CartisGouldToint.Chapter03.sigmaMaxAR2`: the bound $\sigma_{\max} = \max(\sigma_0,
  \gamma_3 L_{f,2}/(1 - \eta_2))$.
* Lemma 3.3.4, `CartisGouldToint.Chapter03.kappaSAR2`: the constant $\kappa^S_{\mathrm{AR2}}$.
* Theorem 3.3.5, `CartisGouldToint.Chapter03.kappaCAR2`: the constant $\kappa^C_{\mathrm{AR2}}$,
  which is also $\kappa^F_{\mathrm{AR2}}$ of Theorem 3.3.9.
* (3.3.23), `CartisGouldToint.Chapter03.IsModifiedAR2Run`: the modified AR2 algorithm.
* Theorem 3.3.9, `CartisGouldToint.Chapter03.kappaTAR2`: the constant $\kappa^T_{\mathrm{AR2}}$.

## Main results

* `CartisGouldToint.Chapter03.exists_algorithm_3_3_1`: an AR2 run exists for every $C^2$ function
  and every starting point.
* Lemma 3.3.1, `CartisGouldToint.Chapter03.lemma_3_3_1`: the Taylor decrease exceeds
  $\frac{\sigma_k}{6} \|s_k\|^3$.
* Lemma 3.3.2, `CartisGouldToint.Chapter03.lemma_3_3_2`: under f.HL, $\sigma_k \le \sigma_{\max}$.
* Lemma 3.3.3, `CartisGouldToint.Chapter03.lemma_3_3_3`: at a successful iteration, $\|s_k\|^2 \ge 2
  \|\nabla f(x_{k+1})\| / (L_{f,2} + \theta_1 + \sigma_{\max})$.
* Lemma 3.3.4, `CartisGouldToint.Chapter03.lemma_3_3_4`: with $\epsilon_2 = \infty$, there are at
  most $\kappa^S_{\mathrm{AR2}} (f(x_0) - f_{\mathrm{low}})/\epsilon_1^{3/2} + 1$ successful
  iterations.
* Theorem 3.3.5, `CartisGouldToint.Chapter03.theorem_3_3_5`: with $\epsilon_2 = \infty$, AR2 stops
  after $O(\epsilon_1^{-3/2})$ evaluations.
* Theorem 3.3.6, `CartisGouldToint.Chapter03.theorem_3_3_6`: on a one-dimensional example, AR2 stops
  exactly at iteration $\lceil \epsilon_1^{-3/2} \rceil$.
* `CartisGouldToint.Chapter03.exists_isModifiedAR2Run`: a run of the modified AR2 algorithm exists.
* Lemma 3.3.7, `CartisGouldToint.Chapter03.lemma_3_3_7`: for the modified algorithm, $\|s_k\|^2 \ge
  2 \|\nabla f(x_{k+1})\| / (L_{f,2} + \theta_1 \sigma_{\max})$ at a successful iteration.
* Lemma 3.3.8, `CartisGouldToint.Chapter03.lemma_3_3_8`: at a successful iteration with negative
  curvature at $x_{k+1}$, $\|s_k\| \ge |\lambda_{\min}[\nabla^2 f(x_{k+1})]| / (L_{f,2} + \theta_2 +
  \sigma_{\max})$.
* Theorem 3.3.9, `CartisGouldToint.Chapter03.theorem_3_3_9`: with $\epsilon_2 < \infty$, AR2 stops
  after $O(\max(\epsilon_1^{-3/2}, \epsilon_2^{-3}))$ evaluations.
* Theorem 3.3.10, `CartisGouldToint.Chapter03.theorem_3_3_10`: on a one-dimensional example, AR2
  stops exactly at iteration $\max(\lceil \epsilon_1^{-3/2} \rceil, \lceil \epsilon_2^{-3} \rceil)$.

## Conventions

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. The Taylor model $T_{f,2}(x, \cdot)$ is
  `taylorPolynomial f 2 x`, and the Taylor decrease $T_{f,2}(x, 0) - T_{f,2}(x, s)$ is
  `FormalMultilinearSeries.taylorDecrement`.
* The tolerance $\epsilon_2$ is an `Option ℝ`, and `none` stands for $\epsilon_2 = +\infty$.
* "Before termination at iteration $k$" means that the test (3.3.4) fails at every $j \le k$.

## Implementation notes

* The model is `Optimization.regularizedModel (ftaylorSeries ℝ f x) 2 σ`, and the ratio (3.3.7) is
  `Optimization.taylorRatio f 2 x s`.
* An AR2 run is `Optimization.IsARRun`. Steps 3–4 are `Optimization.ARAcceptance`, and the update
  (3.3.8) is `Optimization.ARUpdate`.
* The sharpness examples are ridge functions $x \mapsto G(\langle e_0, x \rangle)$ on $\mathbb{R}^1$
  built from the one-dimensional data of Theorem 12.2.15
  (`Optimization.exists_slowTaylorOrder_interpolant`). Their iterations are exact global model
  minimizations with $\sigma_k = \sigma_0$ and $\rho_k = 1$.

## Deviations from the source

* **Equation (3.3.1)** (generalization). The model formula accepts any real
  regularization weight, while an active run uses positive weights.
* **Hessian of the model after (3.3.2)** (typo). The displayed Hessian has a spurious factor $2$.
  Nothing depends on it; the curvature bounds use
  `Optimization.minCurvature_ge_of_regularizedModel`.
* **Step 1 of Algorithm 3.3.1** (reading). The source also stops at strict local minimizers. These
  satisfy (3.3.4), so the termination test is (3.3.4) alone (`CartisGouldToint.Chapter03.stopTest`).
* **Proof of Lemma 3.3.4** (typo). Passing from the preceding prefix to the current
  one uses $|\mathcal S_k|\le|\mathcal S_{k-1}|+1$. The source displays the
  opposite order of the two prefix cardinalities.
* **Theorems 3.3.6 and 3.3.10** (reading). The source defers the proofs to §12.2.2.4. They are
  proved here from the data of Theorem 12.2.15 with the run's initial weight in
  place of that example's fixed weight. The first hit is the ceiling of the
  indicated power, or the maximum of the two ceilings. See
  `CartisGouldToint.Chapter03.theorem_3_3_6` and `CartisGouldToint.Chapter03.theorem_3_3_10`.
* **Theorem 3.3.9, (3.3.30)** (correction). The printed bound on the derivative evaluations ends
  with $+ 1$, which is false; the bound holds with $+ 2$. See
  `CartisGouldToint.Chapter03.theorem_3_3_9`.
* **Lemma 3.3.8 and Theorem 3.3.9** (generalization). The finite second tolerance
  need only be positive. See `CartisGouldToint.Chapter03.lemma_3_3_8` and
  `CartisGouldToint.Chapter03.theorem_3_3_9`.
-/

open Set Finset Optimization Subproblem
open Optimization hiding ARParams
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter03

variable {n : ℕ}

/-- **Equation (3.3.3)** of [cartis2022evaluation]. The constants of Algorithm 3.3.1 consist of the
constants (2.4.2) of AR1 and two step-accuracy parameters $\theta_1 > 0$ and $\theta_2 > 0$. -/
structure AR2Params extends toAR1Params : Chapter02.ARParams where
  /-- The first-order step accuracy $\theta_1$ of (3.3.5). -/
  θ₁ : ℝ
  /-- The second-order step accuracy $\theta_2$ of (3.3.6). -/
  θ₂ : ℝ
  /-- The first-order step accuracy satisfies $\theta_1 > 0$. -/
  θ₁_pos : 0 < θ₁
  /-- The second-order step accuracy satisfies $\theta_2 > 0$. -/
  θ₂_pos : 0 < θ₂

/-- The constants of AR2, without $\theta_1$ and $\theta_2$, as backbone `Optimization.ARParams`. -/
abbrev AR2Params.ar (P : AR2Params) : Optimization.ARParams := P.toAR1Params.toARParams

/-- **Equation (3.3.1)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$x \in \mathbb{R}^n$ and $\sigma \in \mathbb{R}$. The **cubic model** of AR2 at $x$ is
$$m(s) = T_{f,2}(x, s) + \frac{\sigma}{6} \|s\|^3,$$
where $T_{f,2}(x, \cdot)$ is the second-order Taylor polynomial of $f$ at $x$. It is
`Optimization.regularizedModel` of `ftaylorSeries ℝ f x` with $p = 2$.

**Reading.** Defines the cubic model for arbitrary real weights, beyond the positive weights of a
run.
-/
noncomputable def ar2Model (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (σ : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  regularizedModel (ftaylorSeries ℝ f x) 2 σ

/-- The AR2 model is $m(s) = T_{f,2}(x, s) + \frac{\sigma}{6} \|s\|^3$, with $T_{f,2}(x, \cdot)$
given by `taylorPolynomial f 2 x`.

**Reading.** Unfolds the model for all real weights and total derivative data.
-/
theorem ar2Model_apply (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) :
    ar2Model f x σ s = taylorPolynomial f 2 x s + σ / 6 * ‖s‖ ^ 3 := by
  rw [ar2Model, regularizedModel_def, ← taylorPolynomial_eq_taylorSum]
  norm_num [Nat.factorial]

section AR2Model

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- The derivative of the AR2 model (3.3.2). If $f$ is twice continuously differentiable at $x$,
then $\nabla m(s) = \nabla f(x) + \nabla^2 f(x) s + \frac{\sigma}{2} \|s\| s$.

**Reading.** The displayed gradient is packaged as a Fréchet derivative and allows arbitrary real
weights.
-/
theorem hasFDerivAt_ar2Model (hf : ContDiffAt ℝ 2 f x) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (ar2Model f x σ)
      (innerSL ℝ (gradient f x + hessianOperator f x s + (σ / 2 * ‖s‖) • s)) s := by
  have heq : ar2Model f x σ =
      fun s => f x + regModel (gradient f x) (hessianOperator f x) (σ / 2) 3 s := by
    funext s
    exact regularizedModel_two_eq_regModel hf σ s
  rw [heq]
  refine ((hasFDerivAt_regModel (g := gradient f x) (hessianOperator_isSymmetric hf) (σ / 2)
    (by norm_num : (1 : ℝ) < 3) s).const_add (f x)).congr_fderiv ?_
  norm_num

/-- If $f$ is twice continuously differentiable at $x$, then $\|\nabla m(s)\| = \|\nabla f(x) +
\nabla^2 f(x) s + \frac{\sigma}{2} \|s\| s\|$.

**Reading.** The derivative norm formula also allows arbitrary real weights.
-/
theorem norm_fderiv_ar2Model (hf : ContDiffAt ℝ 2 f x) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (ar2Model f x σ) s‖ =
      ‖gradient f x + hessianOperator f x s + (σ / 2 * ‖s‖) • s‖ := by
  rw [(hasFDerivAt_ar2Model hf σ s).fderiv, innerSL_apply_norm]

/-- If $f$ is twice continuously differentiable at $x$, the second-order Taylor decrease is
$T_{f,2}(x, 0) - T_{f,2}(x, s) = -\langle \nabla f(x), s \rangle - \frac12 \langle s, \nabla^2
f(x) s \rangle$. -/
theorem taylorDecrement_two_eq (hf : ContDiffAt ℝ 2 f x) (s : EuclideanSpace ℝ (Fin n)) :
    (ftaylorSeries ℝ f x).taylorDecrement 2 s =
      -⟪gradient f x, s⟫ - 1 / 2 * ⟪s, hessianOperator f x s⟫ := by
  rw [ftaylorSeries_taylorDecrement_eq, taylorPolynomial_two_eq_quadModel hf, quadModel_def]
  ring

/-- For every order $p$, $f(x) - (T_{f,p}(x, 0) - T_{f,p}(x, s)) = T_{f,p}(x, s)$. -/
theorem sub_taylorDecrement_eq (p : ℕ) (s : EuclideanSpace ℝ (Fin n)) :
    f x - (ftaylorSeries ℝ f x).taylorDecrement p s = taylorPolynomial f p x s := by
  simp only [ftaylorSeries_taylorDecrement_eq]
  ring

/-- If $f$ is twice continuously differentiable at $x$, then $\lambda_{\min}[\nabla^2 f(x)] \|s\|^2
\le \langle s, \nabla^2 f(x) s \rangle$ for every $s$. -/
theorem hessianMinEig_mul_le_inner (hf : ContDiffAt ℝ 2 f x) (s : EuclideanSpace ℝ (Fin n)) :
    Chapter01.hessianMinEig f x * ‖s‖ ^ 2 ≤ ⟪s, hessianOperator f x s⟫ := by
  rw [inner_hessianOperator_apply hf, show (![s, s] : Fin 2 → _) = fun _ => s by
    funext i; fin_cases i <;> rfl]
  exact minCurvature_mul_norm_sq_le (iteratedFDeriv ℝ 2 f x) s

/-- For every $s$, $\langle \nabla f(x) + \nabla^2 f(x) s + \frac{\sigma}{2} \|s\| s, s \rangle =
\langle \nabla f(x), s \rangle + \langle s, \nabla^2 f(x) s \rangle + \frac{\sigma}{2} \|s\|^3$. -/
theorem inner_ar2ModelGrad_self (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient f x + hessianOperator f x s + (σ / 2 * ‖s‖) • s, s⟫ =
      ⟪gradient f x, s⟫ + ⟪s, hessianOperator f x s⟫ + σ / 2 * ‖s‖ ^ 3 := by
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    real_inner_comm s (hessianOperator f x s)]
  ring

end AR2Model

/-- Step 2 of Algorithm 3.3.1 of [cartis2022evaluation]. A step $s$ is an **AR2 step** at $x$ with
weight $\sigma$ if it decreases the model, $m(s) < m(0)$, it satisfies the first-order accuracy
condition (3.3.5)
$$\|\nabla m(s)\| \le \frac{\theta_1}{2} \|s\|^2,$$
and, when $\epsilon_2 < \infty$, it satisfies the second-order accuracy condition (3.3.6),
$\lambda_{\min}[\nabla^2 m(s)] \ge -\theta_2 \|s\|$. -/
def ar2Step (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ar2Model f x σ s < ar2Model f x σ 0 ∧ ‖fderiv ℝ (ar2Model f x σ) s‖ ≤ P.θ₁ / 2 * ‖s‖ ^ 2 ∧
    (ε₂ ≠ none → -(P.θ₂ * ‖s‖) ≤ minCurvature (iteratedFDeriv ℝ 2 (ar2Model f x σ) s))

/-- **Algorithm 3.3.1** of [cartis2022evaluation] (AR2). Let $f : \mathbb{R}^n \to \mathbb{R}$, let
the constants (3.3.3) be given, let $\epsilon_1 \in \mathbb{R}$, and let $\epsilon_2$ be a real
number or $+\infty$. Sequences of iterates $x_k$, trial steps $s_k$ and regularization weights
$\sigma_k$ form an **AR2 run** if $\epsilon_1 \in (0, 1]$, $\epsilon_2 > 0$ when it is finite,
$\sigma_0$ is the initial weight of the constants, and the following holds at every iteration
$k$ at which the test (3.3.4) has failed for all $j \le k$.

* Step 2: $s_k$ is an AR2 step at $x_k$ with weight $\sigma_k$, that is, it satisfies
  (3.3.5)–(3.3.6).
* Step 3: $x_{k+1} = x_k + s_k$ if $\rho_k \ge \eta_1$, and $x_{k+1} = x_k$ otherwise, where
  $\rho_k$ is the ratio (3.3.7) of $f(x_k) - f(x_k + s_k)$ to
  $T_{f,2}(x_k, 0) - T_{f,2}(x_k, s_k)$.
* Step 4: the update (3.3.8), which has the form (2.4.4).

The run stops at the first $k$ at which $x_k$ passes the test (3.3.4). The structure is the
generic run `Optimization.IsARRun` with the termination test
`CartisGouldToint.Chapter03.stopTest`, the step condition `CartisGouldToint.Chapter03.ar2Step`,
no termination test after the step, and the ratio `Optimization.taylorRatio f 2`.

**Reading.** Combines the strict and ordinary stop branches without recording which branch fired.
-/
structure algorithm_3_3_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (ε₁ : ℝ)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- The first-order tolerance satisfies $\epsilon_1 > 0$. -/
  ε₁_pos : 0 < ε₁
  /-- The first-order tolerance satisfies $\epsilon_1 \le 1$. -/
  ε₁_le_one : ε₁ ≤ 1
  /-- The second-order tolerance satisfies $\epsilon_2 > 0$ when it is finite. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- Steps 1–4 hold in the form of the generic adaptive-regularization run `Optimization.IsARRun`.
  -/
  run : IsARRun P.ar (fun k => stopTest f ε₁ ε₂ (x k)) (fun k => ar2Step f P ε₂ (x k) (σ k) (s k))
    (fun _ => False) (taylorRatio f 2 x s) x s σ

section Existence

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- A global minimizer $s$ of the AR2 model with $m(s) < m(0)$ is an AR2 step, for every
$\epsilon_2$. -/
theorem ar2Step_of_isMinOn {x : EuclideanSpace ℝ (Fin n)} (P : AR2Params) (ε₂ : Option ℝ)
    {σ : ℝ} {s : EuclideanSpace ℝ (Fin n)} (hmin : IsMinOn (ar2Model f x σ) univ s)
    (hdec : ar2Model f x σ s < ar2Model f x σ 0) :
    ar2Step f P ε₂ x σ s := by
  have hloc : IsLocalMin (ar2Model f x σ) s := hmin.isLocalMin Filter.univ_mem
  refine ⟨hdec, by rw [hloc.fderiv_eq_zero, norm_zero]; have := P.θ₁_pos; positivity,
    fun _ => ?_⟩
  have h0 := hloc.minCurvature_iteratedFDeriv_two_nonneg
    ((contDiff_regularizedModel (D := ftaylorSeries ℝ f x) (p := 2) (σ := σ)).contDiffAt)
  have := P.θ₂_pos
  have : 0 ≤ P.θ₂ * ‖s‖ := by positivity
  linarith

/-- Let $f$ be twice continuously differentiable, $\epsilon_1 > 0$, $\epsilon_2$ either $+\infty$ or
positive, and $\sigma > 0$. If $y$ fails the test (3.3.4), then the AR2 model at $y$ has a
global minimizer $s$ with $m(s) < m(0)$. -/
theorem exists_isMinOn_ar2Model_lt (hf : ContDiff ℝ 2 f) {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e) {y : EuclideanSpace ℝ (Fin n)}
    {σ : ℝ} (hσ : 0 < σ) (hnot : ¬ stopTest f ε₁ ε₂ y) :
    ∃ s, IsMinOn (ar2Model f y σ) univ s ∧ ar2Model f y σ s < ar2Model f y σ 0 := by
  obtain ⟨s, hmin, -, -, hlt⟩ := exists_isMinOn_regularizedModel
    (D := ftaylorSeries ℝ f y) (p := 2) hσ (by norm_num)
  have hdec : ar2Model f y σ s < ar2Model f y σ 0 := by
    by_cases hg : gradient f y = 0
    · -- the second-order part of the test fails
      have hlam : minCurvature (iteratedFDeriv ℝ 2 (ar2Model f y σ) 0) < 0 := by
        rw [ar2Model, iteratedFDeriv_two_regularizedModel_ftaylorSeries_zero
          hf.contDiffAt le_rfl]
        by_contra hnn
        refine hnot ⟨by rw [hg, norm_zero]; exact hε₁.le, fun e he => ?_⟩
        have := hε₂ e he
        change -e ≤ minCurvature _
        linarith [not_lt.1 hnn]
      exact regularizedModel_lt_of_isMinOn_of_minCurvature_neg le_rfl hmin hlam
    · refine regularizedModel_lt_of_isMinOn_of_fderiv_ne_zero hmin ?_
      rw [fderiv_regularizedModel_ftaylorSeries_zero hf.contDiffAt (by norm_num)]
      intro h0
      exact hg (by rw [← norm_eq_zero, norm_gradient_eq, h0, norm_zero])
  exact ⟨s, hmin, hdec⟩

/-- Existence of runs of Algorithm 3.3.1 of [cartis2022evaluation]. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable, let the constants
(3.3.3) be given, let $\epsilon_1 \in (0, 1]$, let $\epsilon_2$ be $+\infty$ or a positive real
number, and let $x_0 \in \mathbb{R}^n$. Then there is an AR2 run that starts at $x_0$.

The proof takes as step a global minimizer of the model (3.3.1), which exists because
$\sigma_k > 0$, and which is an AR2 step whenever the termination test fails. -/
theorem exists_algorithm_3_3_1 (hf : ContDiff ℝ 2 f) (P : AR2Params) {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hε₁1 : ε₁ ≤ 1) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_3_3_1 f P ε₁ ε₂ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.ar (Inv := fun _ => True)
    (test := stopTest f ε₁ ε₂) (stepOK := fun y σ s => ar2Step f P ε₂ y σ s)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement 2 t))
    (fun y σ _ _ hσ hnot => by
      obtain ⟨s, hmin, hdec⟩ := exists_isMinOn_ar2Model_lt hf hε₁ hε₂ hσ hnot
      exact ⟨s, ar2Step_of_isMinOn P ε₂ hmin hdec, trivial⟩) trivial
  exact ⟨x, s, σ, hx0, hε₁, hε₁1, hε₂, hrun⟩

end Existence

/-! ### Lemmas 3.3.1–3.3.4 and Theorem 3.3.5 -/

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ L₂ flow : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

namespace algorithm_3_3_1

/-- In an AR2 run, if the termination test fails at every iteration $j < k$, then $\sigma_k > 0$. -/
theorem sigma_pos (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) : 0 < σ k :=
  h.run.sigma_pos (IsARRun.forall_lt_not_stop_iff.2 hk) k le_rfl

/-- In an AR2 run, if the termination test fails at every iteration $j < k$, then
$\sigma_k \ge \sigma_{\min}$. -/
theorem sigmaMin_le (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) : P.σmin ≤ σ k :=
  h.run.sigmaMin_le (IsARRun.forall_lt_not_stop_iff.2 hk) k le_rfl

/-- In an AR2 run, at every iteration $k$ before termination, $s_k$ is an AR2 step at $x_k$ with
weight $\sigma_k$. -/
theorem step (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) : ar2Step f P ε₂ (x k) (σ k) (s k) :=
  h.run.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)

end algorithm_3_3_1

/-- **Lemma 3.3.1** of [cartis2022evaluation]. In an AR2 run, at every iteration $k$ before
termination, (3.3.13) holds:
$$T_{f,2}(x_k, 0) - T_{f,2}(x_k, s_k) > \frac{\sigma_k}{6} \|s_k\|^3.$$
-/
theorem lemma_3_3_1 (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) :
    σ k / 6 * ‖s k‖ ^ 3 < (ftaylorSeries ℝ f (x k)).taylorDecrement 2 (s k) := by
  have := lt_taylorDecrement_of_regularizedModel_lt (h.step hk).1
  norm_num [Nat.factorial] at this
  exact this

/-- The bound (3.3.14) of [cartis2022evaluation] on the regularization weights,
$$\sigma_{\max} = \max\left( \sigma_0, \frac{\gamma_3 L}{1 - \eta_2} \right),$$
which is `Optimization.arSigmaMax`. -/
noncomputable abbrev sigmaMaxAR2 (P : AR2Params) (L : ℝ) : ℝ := arSigmaMax P.ar L

/-- **Lemma 3.3.2** of [cartis2022evaluation]. Assume f.HL with constant $L_{f,2}$ and consider an
AR2 run. Let $k$ be an iteration at which the test (3.3.4) has failed for all $j < k$. Then
(3.3.14) holds:
$$\sigma_k \le \sigma_{\max} = \max\left( \sigma_0, \frac{\gamma_3 L_{f,2}}{1 - \eta_2}
  \right).$$
So the bound holds at every iteration up to and including the termination index. -/
theorem lemma_3_3_2 (hf : AssumptionHL f L₂) (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) : σ k ≤ sigmaMaxAR2 P L₂ :=
  (h.run.sigma_le convex_univ (fun y _ => hf.contDiffAt y) hf.iteratedFDerivLipschitzOn
    (mem_univ _) (fun _ _ hst => ⟨mem_univ _, hst.1⟩) k
    (IsARRun.forall_lt_not_stop_iff.2 hk)).2.2

/-- **Lemma 3.3.3** of [cartis2022evaluation]. Assume f.HL with constant $L_{f,2}$ and consider an
AR2 run. Let $k$ be an iteration before termination that is successful, $\rho_k \ge \eta_1$.
Then (3.3.15) holds:
$$\|s_k\|^2 \ge \frac{2}{L_{f,2} + \theta_1 + \sigma_{\max}} \|\nabla f(x_{k+1})\|.$$
-/
theorem lemma_3_3_3 (hf : AssumptionHL f L₂) (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ taylorRatio f 2 x s k) :
    2 / (L₂ + P.θ₁ + sigmaMaxAR2 P L₂) * ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ ^ 2 := by
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hσmax := lemma_3_3_2 hf h fun j hj => hk j hj.le
  have hstep := h.step hk
  have hb := norm_fderiv_le_of_regularizedModel convex_univ (fun y _ => hf.contDiffAt y)
    (le_refl _ |>.trans (by norm_num : (1 : ℕ) ≤ 2)) hf.iteratedFDerivLipschitzOn (mem_univ (x k))
    (mem_univ (x k + s k)) hσ.le
  rw [h.run.eq_add_of_succ (IsARRun.forall_le_not_stop_iff.2 hk) hs, norm_gradient_eq]
  change ‖fderiv ℝ f (x k + s k)‖ ≤ (L₂ + σ k) / (Nat.factorial 2 : ℝ) * ‖s k‖ ^ 2 +
    ‖fderiv ℝ (ar2Model f (x k) (σ k)) (s k)‖ at hb
  have hC : 0 < L₂ + P.θ₁ + sigmaMaxAR2 P L₂ := by
    have := hf.pos; have := P.θ₁_pos; have := arSigmaMax_pos P.ar L₂; linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  have h2 := hstep.2.1
  norm_num [Nat.factorial] at hb
  have : σ k * ‖s k‖ ^ 2 ≤ sigmaMaxAR2 P L₂ * ‖s k‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hσmax (sq_nonneg _)
  nlinarith

/-- The constant $\kappa^S_{\mathrm{AR2}}$ of Lemma 3.3.4 of [cartis2022evaluation],
$$\kappa^S_{\mathrm{AR2}} = \frac{6 (L + \theta_1 + \sigma_{\max})^{3/2}}{2^{3/2} \eta_1
  \sigma_{\min}}.$$
-/
noncomputable def kappaSAR2 (P : AR2Params) (L : ℝ) : ℝ :=
  6 * (L + P.θ₁ + sigmaMaxAR2 P L) ^ (3 / 2 : ℝ) / (2 ^ (3 / 2 : ℝ) * P.η₁ * P.σmin)

/-- If $L \ge 0$, then $\kappa^S_{\mathrm{AR2}} > 0$. -/
theorem kappaSAR2_pos {P : AR2Params} {L : ℝ} (hL : 0 ≤ L) : 0 < kappaSAR2 P L := by
  have := P.θ₁_pos; have := arSigmaMax_pos P.ar L; have := P.η₁_pos; have := P.σmin_pos
  unfold kappaSAR2
  have : 0 < L + P.θ₁ + sigmaMaxAR2 P L := by linarith
  positivity

/-- The decrease at a successful AR2 iteration, from the argument of Lemma 3.3.4. Assume f.HL, and
let $k$ be a successful iteration before termination with $\|\nabla f(x_{k+1})\| \ge \zeta$ for
some $\zeta > 0$. Then $f(x_k) - f(x_{k+1}) \ge \zeta^{3/2} / \kappa^S_{\mathrm{AR2}}$.

**Reading.** The descent lower bound uses an arbitrary positive lower bound on the next gradient
norm.
-/
theorem ar2_decrease_of_le (hf : AssumptionHL f L₂) (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ taylorRatio f 2 x s k)
    {ζ : ℝ} (hζ : 0 < ζ) (hg : ζ ≤ ‖gradient f (x (k + 1))‖) :
    ζ ^ (3 / 2 : ℝ) / kappaSAR2 P L₂ ≤ f (x k) - f (x (k + 1)) := by
  set C := L₂ + P.θ₁ + sigmaMaxAR2 P L₂
  have hσmin := h.sigmaMin_le fun j hj => hk j hj.le
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hC : 0 < C := by
    have := hf.pos; have := P.θ₁_pos; have := arSigmaMax_pos P.ar L₂; simp only [C]; linarith
  have hη := P.η₁_pos
  have hsmin := P.σmin_pos
  obtain ⟨-, hdec⟩ :=
    h.run.sub_ge_of_succ_taylor (IsARRun.forall_le_not_stop_iff.2 hk) (h.step hk).1 hs
  norm_num [Nat.factorial] at hdec
  have h3 := lemma_3_3_3 hf h hk hs
  have hs2 : 2 * ζ / C ≤ ‖s k‖ ^ 2 :=
    le_trans (by rw [div_mul_eq_mul_div]; gcongr) h3
  have hs3 : (2 * ζ / C) ^ (3 / 2 : ℝ) ≤ ‖s k‖ ^ 3 := by
    have : (‖s k‖ ^ 2) ^ (3 / 2 : ℝ) = ‖s k‖ ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; norm_num
    rw [← this]
    exact Real.rpow_le_rpow (by positivity) hs2 (by norm_num)
  have hsplit : (2 * ζ / C) ^ (3 / 2 : ℝ) =
      2 ^ (3 / 2 : ℝ) * ζ ^ (3 / 2 : ℝ) / C ^ (3 / 2 : ℝ) := by
    rw [Real.div_rpow (by positivity) hC.le, Real.mul_rpow (by norm_num) hζ.le]
  have key : ζ ^ (3 / 2 : ℝ) / kappaSAR2 P L₂ =
      P.η₁ * (P.σmin / 6 * (2 * ζ / C) ^ (3 / 2 : ℝ)) := by
    rw [hsplit, kappaSAR2, show L₂ + P.θ₁ + sigmaMaxAR2 P L₂ = C from rfl]
    have : 0 < C ^ (3 / 2 : ℝ) := by positivity
    have : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
    field_simp
  rw [key]
  calc P.η₁ * (P.σmin / 6 * (2 * ζ / C) ^ (3 / 2 : ℝ)) ≤ P.η₁ * (σ k / 6 * ‖s k‖ ^ 3) := by
        gcongr
    _ ≤ _ := by linarith

/-- Assume f.HL, and let $k$ be a successful AR2 iteration before termination with
$\|\nabla f(x_{k+1})\| \ge \epsilon_1$. Then $f(x_k) - f(x_{k+1}) \ge \epsilon_1^{3/2} /
\kappa^S_{\mathrm{AR2}}$. -/
theorem ar2_decrease_first (hf : AssumptionHL f L₂) (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ taylorRatio f 2 x s k)
    (hg : ε₁ ≤ ‖gradient f (x (k + 1))‖) :
    ε₁ ^ (3 / 2 : ℝ) / kappaSAR2 P L₂ ≤ f (x k) - f (x (k + 1)) :=
  ar2_decrease_of_le hf h hk hs h.ε₁_pos hg

/-- With $\epsilon_2 = +\infty$, a point $y$ that fails the test (3.3.4) has
$\|\nabla f(y)\| \ge \epsilon_1$. -/
theorem le_norm_gradient_of_not_stopTest {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {y : EuclideanSpace ℝ (Fin n)} (h : ¬ stopTest f ε₁ none y) : ε₁ ≤ ‖gradient f y‖ := by
  rw [stopTest_none, not_le] at h
  exact h.le

/-- **Lemma 3.3.4** of [cartis2022evaluation]. Assume f.Bb with lower bound $f_{\mathrm{low}}$ and
f.HL with constant $L_{f,2}$, and consider an AR2 run with $\epsilon_2 = +\infty$. Let $k$ be an
iteration with $\|\nabla f(x_j)\| > \epsilon_1$ for all $j \le k$. Then the number of successful
iterations up to $k$ satisfies (3.3.19):
$$|\mathcal{S}_k| \le \kappa^S_{\mathrm{AR2}} \frac{f(x_0) -
  f_{\mathrm{low}}}{\epsilon_1^{3/2}} + 1.$$

The set $\mathcal{S}_k = \{j \le k : \rho_j \ge \eta_1\}$ is `Optimization.successSet`.

**Typo.** In the source proof the cardinalities of the two prefixes are reversed
in the inequality used to pass to the bound on $|\mathcal S_k|$. -/
theorem lemma_3_3_4 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L₂)
    (h : algorithm_3_3_1 f P ε₁ none x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) :
    ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) k).card : ℝ) ≤
      kappaSAR2 P L₂ * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) + 1 := by
  have hκ := kappaSAR2_pos (P := P) hf.nonneg
  have hε := h.ε₁_pos
  set δ := ε₁ ^ (3 / 2 : ℝ) / kappaSAR2 P L₂
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ = kappaSAR2 P L₂ * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) := by
    simp only [δ]; field_simp
  rw [← hNδ]
  cases k with
  | zero =>
    have : (successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) 0).card ≤ 1 := card_successSet_le
    have : ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) 0).card : ℝ) ≤ 1 := by
      exact_mod_cast this
    have : 0 ≤ (f (x 0) - flow) / δ := div_nonneg (sub_nonneg.2 (hb _)) hδ.le
    linarith
  | succ m =>
    have hm : ∀ j ≤ m, ¬ stopTest f ε₁ none (x j) := fun j hj => hk j (hj.trans m.le_succ)
    have hcard := card_successSet_le_div_of_decrease (φ := fun j => f (x j)) (k := m) hδ
      (fun j hj hs => by
        rw [h.run.eq_of_not_succ
          (IsARRun.forall_le_not_stop_iff.2 fun i hi => hm i (hi.trans hj))
          (not_le.1 hs)])
      (fun j hj hs => ar2_decrease_first hf h (fun i hi => hm i (hi.trans hj)) hs
        (le_norm_gradient_of_not_stopTest (hk (j + 1) (Nat.succ_le_succ hj))))
      (hb _)
    have : ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) (m + 1)).card : ℝ) ≤
        (successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) m).card + 1 := by
      exact_mod_cast card_successSet_add_one_le
    linarith

/-- The constant $\kappa^C_{\mathrm{AR2}}$ of Theorem 3.3.5 of [cartis2022evaluation], which is also
$\kappa^F_{\mathrm{AR2}}$ of Theorem 3.3.9:
$$\kappa^C_{\mathrm{AR2}} = \frac{|\log \gamma_1| + \log \max\left( 1, \frac{\gamma_3
  L}{\sigma_0 (1 - \eta_2)} \right)}{\log \gamma_2} + 2.$$
-/
noncomputable def kappaCAR2 (P : AR2Params) (L : ℝ) : ℝ :=
  (|Real.log P.γ₁| + Real.log (max 1 (P.γ₃ * L / (P.σ₀ * (1 - P.η₂))))) / Real.log P.γ₂ + 2

/-- The bound $\sigma_{\max}$ satisfies $\sigma_{\max}/\sigma_0 = \max(1, \gamma_3 L/(\sigma_0 (1 -
\eta_2)))$. -/
theorem sigmaMaxAR2_div_eq (P : AR2Params) (L : ℝ) :
    sigmaMaxAR2 P L / P.σ₀ = max 1 (P.γ₃ * L / (P.σ₀ * (1 - P.η₂))) := by
  have := P.σ₀_pos
  rw [sigmaMaxAR2, arSigmaMax_def, ← max_div_div_right this.le]
  congr 1
  · exact div_self this.ne'
  · field_simp

/-- **Theorem 3.3.5** of [cartis2022evaluation] (first-order complexity of AR2). Assume f.Bb with
lower bound $f_{\mathrm{low}}$ and f.HL with constant $L_{f,2}$, and consider an AR2 run with
$\epsilon_1 \in (0, 1]$ and $\epsilon_2 = +\infty$. Then the run terminates: there is a first
iteration $k_\epsilon$ with $\|\nabla f(x_{k_\epsilon})\| \le \epsilon_1$. Up to termination the
method uses at most (3.3.21)
$$\kappa^A \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon_1^{3/2}} + \kappa^C$$
evaluations of $f$ and at most (3.3.22)
$$\kappa^S \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon_1^{3/2}} + 2$$
evaluations of $\nabla f$ and $\nabla^2 f$, where $\kappa^S = \kappa^S_{\mathrm{AR2}}$,
$\kappa^A = \kappa^S (1 + |\log \gamma_1| / \log \gamma_2)$ and
$\kappa^C = \kappa^C_{\mathrm{AR2}}$.

The evaluation counts are `Optimization.funEvalCount` and `Optimization.derivEvalCount`. -/
theorem theorem_3_3_5 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L₂)
    (h : algorithm_3_3_1 f P ε₁ none x s σ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaSAR2 P L₂ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f (x 0) - flow) /
          ε₁ ^ (3 / 2 : ℝ) + kappaCAR2 P L₂ ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f 2 x s k) kε : ℝ) ≤
        kappaSAR2 P L₂ * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) + 2 := by
  have hκ := kappaSAR2_pos (P := P) hf.nonneg
  have hε := h.ε₁_pos
  set δ := ε₁ ^ (3 / 2 : ℝ) / kappaSAR2 P L₂
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ = kappaSAR2 P L₂ * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) := by
    simp only [δ]; field_simp
  obtain ⟨kε, hk, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease (σmax := sigmaMaxAR2 P L₂)
    (V := fun k => f (x k)) (Vlow := flow)
    (fun k hk => lemma_3_3_2 hf h (IsARRun.forall_lt_not_stop_iff.1 hk)) hδ
    (fun k hk => (h.run.accept k hk).le (w := f) rfl
      ((lt_of_le_of_lt (by
          have := h.sigma_pos (fun j hj => (IsARRun.forall_le_not_stop_iff.1 hk) j hj.le)
          positivity) (lemma_3_3_1 h (IsARRun.forall_le_not_stop_iff.1 hk)))))
    (fun k _ => hb (x k))
    (fun k hk hs => ar2_decrease_first hf h
      (fun j hj => (IsARRun.forall_le_not_stop_iff.1 hk) j
        (hj.trans k.le_succ)) hs
      (le_norm_gradient_of_not_stopTest
        ((IsARRun.forall_le_not_stop_iff.1 hk) (k + 1) le_rfl)))
  rw [hNδ] at hF hD
  refine ⟨kε, ?_, ?_, hD⟩
  · have := IsARRun.isFirstHit_stop_iff.1 hk
    simpa only [stopTest_none] using this
  · rw [kappaCAR2, ← sigmaMaxAR2_div_eq]
    calc (funEvalCount kε : ℝ) ≤ _ := hF
      _ = _ := by ring

end Lemmas

/-! ### The modified AR2 algorithm and Lemma 3.3.7 -/

/-- Step 2 of the **modified AR2 algorithm** of §3.3.2 of [cartis2022evaluation]. It is the AR2 step
condition with (3.3.5) replaced by (3.3.23):
$$\|\nabla_s T_{f,2}(x, s)\| \le \frac{\theta_1}{2} \sigma \|s\|^2.$$
-/
def ar2ModStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ar2Model f x σ s < ar2Model f x σ 0 ∧
    ‖fderiv ℝ (taylorPolynomial f 2 x) s‖ ≤ P.θ₁ / 2 * σ * ‖s‖ ^ 2 ∧
    (ε₂ ≠ none → -(P.θ₂ * ‖s‖) ≤ minCurvature (iteratedFDeriv ℝ 2 (ar2Model f x σ) s))

/-- The **modified AR2 algorithm** of [cartis2022evaluation] (§3.3.2, notes after Theorem 3.3.6). It
is Algorithm 3.3.1 with the accuracy condition (3.3.5) replaced by (3.3.23), for $\theta_1 > 1$.
Sequences $x_k$, $s_k$ and $\sigma_k$ form a run of the modified algorithm if $\theta_1 > 1$,
$\epsilon_1 \in (0, 1]$, $\epsilon_2 > 0$ when it is finite, and Steps 1–4 of AR2 hold with the
modified Step 2 `CartisGouldToint.Chapter03.ar2ModStep`.

**Reading.** Instantiates the described variant as a total run with the same merged stopping test.
-/
structure IsModifiedAR2Run (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (ε₁ : ℝ)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- The first-order step accuracy satisfies $\theta_1 > 1$. -/
  one_lt_θ₁ : 1 < P.θ₁
  /-- The first-order tolerance satisfies $\epsilon_1 > 0$. -/
  ε₁_pos : 0 < ε₁
  /-- The first-order tolerance satisfies $\epsilon_1 \le 1$. -/
  ε₁_le_one : ε₁ ≤ 1
  /-- The second-order tolerance satisfies $\epsilon_2 > 0$ when it is finite. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- Steps 1–4 hold, with the modified Step 2, in the form of the generic run
  `Optimization.IsARRun`. -/
  run : IsARRun P.ar (fun k => stopTest f ε₁ ε₂ (x k))
    (fun k => ar2ModStep f P ε₂ (x k) (σ k) (s k)) (fun _ => False) (taylorRatio f 2 x s) x s σ

section Modified

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ L₂ : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- If $\theta_1 \ge 1$ and $\sigma \ge 0$, a global minimizer $s$ of the AR2 model with
$m(s) < m(0)$ satisfies the modified Step 2 (3.3.23). At such a stationary point, $\nabla_s
T_{f,2}(x, s) = -\frac{\sigma}{2} \|s\| s$.

**Reading.** The global-minimizer sufficient condition allows theta equal to one as well as strictly
larger.
-/
theorem ar2ModStep_of_isMinOn {x : EuclideanSpace ℝ (Fin n)} (P : AR2Params) (hθ : 1 ≤ P.θ₁)
    (ε₂ : Option ℝ) {σ : ℝ} (hσ : 0 ≤ σ) {s : EuclideanSpace ℝ (Fin n)}
    (hmin : IsMinOn (ar2Model f x σ) univ s) (hdec : ar2Model f x σ s < ar2Model f x σ 0) :
    ar2ModStep f P ε₂ x σ s := by
  obtain ⟨-, -, h3⟩ := ar2Step_of_isMinOn (f := f) P ε₂ hmin hdec
  have hloc : IsLocalMin (ar2Model f x σ) s := hmin.isLocalMin Filter.univ_mem
  have h0 := hloc.fderiv_eq_zero
  rw [ar2Model, fderiv_regularizedModel (by norm_num)] at h0
  have hT : fderiv ℝ (taylorPolynomial f 2 x) s =
      -((σ / ((2 : ℕ).factorial : ℝ) * ‖s‖ ^ (2 - 1)) • innerSL ℝ s) := by
    rw [taylorPolynomial_eq_taylorSum]; exact eq_neg_of_add_eq_zero_left h0
  refine ⟨hdec, ?_, h3⟩
  rw [hT, norm_neg, norm_smul, innerSL_apply_norm, Real.norm_of_nonneg (by positivity)]
  norm_num [Nat.factorial]
  have : 0 ≤ σ * ‖s‖ ^ 2 := by positivity
  nlinarith

/-- Existence of runs of the modified AR2 algorithm of §3.3.2 of [cartis2022evaluation]. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable, let the constants
(3.3.3) satisfy $\theta_1 > 1$, let $\epsilon_1 \in (0, 1]$, let $\epsilon_2$ be $+\infty$ or a
positive real number, and let $x_0 \in \mathbb{R}^n$. Then there is a run of the modified AR2
algorithm that starts at $x_0$.

The proof takes as step a global minimizer of the model, which satisfies (3.3.23). -/
theorem exists_isModifiedAR2Run (hf : ContDiff ℝ 2 f) (P : AR2Params) (hθ : 1 < P.θ₁) {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ IsModifiedAR2Run f P ε₁ ε₂ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.ar (Inv := fun _ => True)
    (test := stopTest f ε₁ ε₂) (stepOK := fun y σ s => ar2ModStep f P ε₂ y σ s)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement 2 t))
    (fun y σ _ _ hσ hnot => by
      obtain ⟨s, hmin, hdec⟩ := exists_isMinOn_ar2Model_lt hf hε₁ hε₂ hσ hnot
      exact ⟨s, ar2ModStep_of_isMinOn P hθ.le ε₂ hσ.le hmin hdec, trivial⟩) trivial
  exact ⟨x, s, σ, hx0, hθ, hε₁, hε₁1, hε₂, hrun⟩

/-- Lemma 3.3.2 of [cartis2022evaluation] for the modified AR2 algorithm. Under f.HL with constant
$L_{f,2}$, if the test (3.3.4) has failed at every $j < k$, then $\sigma_k \le \sigma_{\max}$. -/
theorem IsModifiedAR2Run.sigma_le (hf : AssumptionHL f L₂)
    (h : IsModifiedAR2Run f P ε₁ ε₂ x s σ) {k : ℕ} (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) :
    σ k ≤ sigmaMaxAR2 P L₂ :=
  (h.run.sigma_le convex_univ (fun y _ => hf.contDiffAt y) hf.iteratedFDerivLipschitzOn
    (mem_univ _) (fun _ _ hst => ⟨mem_univ _, hst.1⟩) k
    (IsARRun.forall_lt_not_stop_iff.2 hk)).2.2

/-- **Lemma 3.3.7** of [cartis2022evaluation]. Assume f.HL with constant $L_{f,2}$ and consider a
run of the modified AR2 algorithm. Let $k$ be an iteration before termination that is
successful, $\rho_k \ge \eta_1$. Then (3.3.24) holds:
$$\|s_k\|^2 \ge \frac{2}{L_{f,2} + \theta_1 \sigma_{\max}} \|\nabla f(x_{k+1})\|.$$
-/
theorem lemma_3_3_7 (hf : AssumptionHL f L₂) (h : IsModifiedAR2Run f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ taylorRatio f 2 x s k) :
    2 / (L₂ + P.θ₁ * sigmaMaxAR2 P L₂) * ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ ^ 2 := by
  have hσmax := h.sigma_le hf fun j hj => hk j hj.le
  have hstep := h.run.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)
  have hb := norm_fderiv_le_of_taylorPolynomial convex_univ (fun y _ => hf.contDiffAt y)
    (by norm_num : 1 ≤ 2) hf.iteratedFDerivLipschitzOn (mem_univ (x k)) (mem_univ (x k + s k))
  rw [h.run.eq_add_of_succ (IsARRun.forall_le_not_stop_iff.2 hk) hs, norm_gradient_eq]
  have hθ := P.θ₁_pos
  have hC : 0 < L₂ + P.θ₁ * sigmaMaxAR2 P L₂ := by
    have := hf.pos; have := arSigmaMax_pos P.ar L₂; positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  have h2 := hstep.2.1
  norm_num [Nat.factorial] at hb
  have : P.θ₁ / 2 * σ k * ‖s k‖ ^ 2 ≤ P.θ₁ / 2 * sigmaMaxAR2 P L₂ * ‖s k‖ ^ 2 := by gcongr
  nlinarith

end Modified

/-! ### Second-order complexity: Lemma 3.3.8 and Theorem 3.3.9 -/

section SecondOrder

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ e L₂ flow : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 3.3.8** of [cartis2022evaluation]. Assume f.HL with constant $L_{f,2}$, and consider an
AR2 run with $\epsilon_2 < \infty$. Let $k$ be an iteration before termination that is
successful, $\rho_k \ge \eta_1$, and assume $\lambda_{\min}[\nabla^2 f(x_{k+1})] < 0$. Then
(3.3.25) holds:
$$\|s_k\| \ge \frac{|\lambda_{\min}[\nabla^2 f(x_{k+1})]|}{L_{f,2} + \theta_2 +
  \sigma_{\max}}.$$

**Generalization.** The argument applies to every finite positive $\epsilon_2$.
-/
theorem lemma_3_3_8 (hf : AssumptionHL f L₂) (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ)
    (hε₂ : ε₂ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j))
    (hs : P.η₁ ≤ taylorRatio f 2 x s k)
    (hneg : Chapter01.hessianMinEig f (x (k + 1)) < 0) :
    |Chapter01.hessianMinEig f (x (k + 1))| / (L₂ + P.θ₂ + sigmaMaxAR2 P L₂) ≤ ‖s k‖ := by
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hσmax := lemma_3_3_2 hf h fun j hj => hk j hj.le
  have hcurv := (h.step hk).2.2 hε₂
  have hb := minCurvature_ge_of_regularizedModel convex_univ (fun y _ => hf.contDiffAt y)
    le_rfl hf.iteratedFDerivLipschitzOn (mem_univ (x k)) (mem_univ (x k + s k)) hσ.le
  have hC : 0 < L₂ + P.θ₂ + sigmaMaxAR2 P L₂ := by
    have := hf.pos; have := P.θ₂_pos; have := arSigmaMax_pos P.ar L₂; linarith
  rw [Chapter01.hessianMinEig_def,
    h.run.eq_add_of_succ (IsARRun.forall_le_not_stop_iff.2 hk) hs] at hneg ⊢
  rw [abs_of_neg hneg, div_le_iff₀ hC]
  norm_num [Nat.factorial] at hb
  change -(P.θ₂ * ‖s k‖) ≤ minCurvature (iteratedFDeriv ℝ 2
    (regularizedModel (ftaylorSeries ℝ f (x k)) 2 (σ k)) (s k)) at hcurv
  have : σ k * ‖s k‖ ≤ sigmaMaxAR2 P L₂ * ‖s k‖ :=
    mul_le_mul_of_nonneg_right hσmax (norm_nonneg _)
  nlinarith

/-- The constant $\kappa^T_{\mathrm{AR2}}$ of Theorem 3.3.9 of [cartis2022evaluation],
$$\kappa^T_{\mathrm{AR2}} = \frac{6 (L + \max(1, \theta_1, \theta_2) + \sigma_{\max})^3}{\eta_1
  \sigma_{\min}}.$$
-/
noncomputable def kappaTAR2 (P : AR2Params) (L : ℝ) : ℝ :=
  6 * (L + max 1 (max P.θ₁ P.θ₂) + sigmaMaxAR2 P L) ^ 3 / (P.η₁ * P.σmin)

/-- The decrease at a successful AR2 iteration with a finite $\epsilon_2 = e$. Assume f.HL, and let
$k$ be a successful iteration such that the test (3.3.4) fails at every $j \le k + 1$. Then
$f(x_k) - f(x_{k+1}) \ge \min(\epsilon_1^{3/2}, e^3) / \kappa^T_{\mathrm{AR2}}$. -/
theorem ar2_decrease_second (hf : AssumptionHL f L₂)
    (h : algorithm_3_3_1 f P ε₁ (some e) x s σ) {k : ℕ}
    (hk : ∀ j ≤ k + 1, ¬ stopTest f ε₁ (some e) (x j)) (hs : P.η₁ ≤ taylorRatio f 2 x s k) :
    min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) / kappaTAR2 P L₂ ≤ f (x k) - f (x (k + 1)) := by
  have hk' : ∀ j ≤ k, ¬ stopTest f ε₁ (some e) (x j) := fun j hj => hk j (hj.trans k.le_succ)
  set C := L₂ + max 1 (max P.θ₁ P.θ₂) + sigmaMaxAR2 P L₂
  have hσ := h.sigma_pos fun j hj => hk' j hj.le
  have hσmin := h.sigmaMin_le fun j hj => hk' j hj.le
  have hε := h.ε₁_pos
  have he : 0 < e := h.ε₂_pos e rfl
  have hL := hf.pos
  have hsm := arSigmaMax_pos P.ar L₂
  have hθ1 : P.θ₁ ≤ max 1 (max P.θ₁ P.θ₂) := (le_max_left _ _).trans (le_max_right _ _)
  have hθ2 : P.θ₂ ≤ max 1 (max P.θ₁ P.θ₂) := (le_max_right _ _).trans (le_max_right _ _)
  have h1 : 1 ≤ max 1 (max P.θ₁ P.θ₂) := le_max_left _ _
  have hC1 : 1 ≤ C := by simp only [C]; linarith
  have hC : 0 < C := by linarith
  -- the step is long
  have hstep : min (√ε₁) e / C ≤ ‖s k‖ := by
    rcases not_stopTest_some.1 (hk (k + 1) le_rfl) with hg | hlam
    · have h3 := lemma_3_3_3 hf h hk' hs
      have hC' : L₂ + P.θ₁ + sigmaMaxAR2 P L₂ ≤ C := by simp only [C]; linarith
      have hsm' : 0 < sigmaMaxAR2 P L₂ := hsm
      have hθ₁ := P.θ₁_pos
      have hD : 0 < L₂ + P.θ₁ + sigmaMaxAR2 P L₂ := by linarith
      have : ε₁ / C ^ 2 ≤ ‖s k‖ ^ 2 := by
        refine le_trans ?_ h3
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hD]
        have hCC : C ≤ C ^ 2 := by nlinarith
        have h4 : ε₁ * (L₂ + P.θ₁ + sigmaMaxAR2 P L₂) ≤ ε₁ * C ^ 2 :=
          mul_le_mul_of_nonneg_left (hC'.trans hCC) hε.le
        have h5 : ε₁ * C ^ 2 ≤ ‖gradient f (x (k + 1))‖ * C ^ 2 :=
          mul_le_mul_of_nonneg_right hg.le (by positivity)
        nlinarith [sq_nonneg C, norm_nonneg (gradient f (x (k + 1)))]
      have hsq : (√ε₁ / C) ^ 2 ≤ ‖s k‖ ^ 2 := by
        rw [div_pow, Real.sq_sqrt hε.le]; exact this
      exact (div_le_div_of_nonneg_right (min_le_left _ _) hC.le).trans
        ((pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq)
    · have hneg : Chapter01.hessianMinEig f (x (k + 1)) < 0 := hlam.trans (neg_neg_of_pos he)
      have h8 := lemma_3_3_8 hf h (Option.some_ne_none e) hk' hs hneg
      refine le_trans ?_ h8
      rw [abs_of_neg hneg]
      exact div_le_div₀ (by linarith) ((min_le_right _ _).trans (by linarith))
        (by linarith [P.θ₂_pos]) (by simp only [C]; linarith)
  -- the decrease
  obtain ⟨-, hdec⟩ := h.run.sub_ge_of_succ_taylor (IsARRun.forall_le_not_stop_iff.2 hk')
    (h.step hk').1 hs
  norm_num [Nat.factorial] at hdec
  have hmin3 : min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) = min (√ε₁) e ^ 3 := by
    have : ε₁ ^ (3 / 2 : ℝ) = √ε₁ ^ 3 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
    rw [this]
    rcases le_total (√ε₁) e with h' | h'
    · rw [min_eq_left h', min_eq_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) h' 3)]
    · rw [min_eq_right h', min_eq_right (pow_le_pow_left₀ he.le h' 3)]
  have hm0 : 0 ≤ min (√ε₁) e := le_min (Real.sqrt_nonneg _) he.le
  have hη := P.η₁_pos
  have hsmin := P.σmin_pos
  have key : min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) / kappaTAR2 P L₂ =
      P.η₁ * (P.σmin / 6 * (min (√ε₁) e / C) ^ 3) := by
    rw [hmin3, kappaTAR2, show L₂ + max 1 (max P.θ₁ P.θ₂) + sigmaMaxAR2 P L₂ = C from rfl]
    field_simp
  rw [key]
  calc P.η₁ * (P.σmin / 6 * (min (√ε₁) e / C) ^ 3) ≤ P.η₁ * (σ k / 6 * ‖s k‖ ^ 3) := by
        gcongr
    _ ≤ _ := hdec

/-- If $L \ge 0$, then $\kappa^T_{\mathrm{AR2}} > 0$. -/
theorem kappaTAR2_pos {P : AR2Params} {L : ℝ} (hL : 0 ≤ L) : 0 < kappaTAR2 P L := by
  have := arSigmaMax_pos P.ar L; have := P.η₁_pos; have := P.σmin_pos
  have : 1 ≤ max 1 (max P.θ₁ P.θ₂) := le_max_left _ _
  have : 0 < L + max 1 (max P.θ₁ P.θ₂) + sigmaMaxAR2 P L := by
    have : 0 < sigmaMaxAR2 P L := arSigmaMax_pos P.ar L
    linarith
  unfold kappaTAR2
  positivity

/-- **Theorem 3.3.9** of [cartis2022evaluation] (second-order complexity of AR2). Assume f.Bb with
lower bound $f_{\mathrm{low}}$ and f.HL with constant $L_{f,2}$, and consider an AR2 run with
$\epsilon_1 \in (0, 1]$ and a finite tolerance $\epsilon_2 > 0$. Then the run terminates: there
is a first iteration $k_\epsilon$ at which $x_{k_\epsilon}$ is an
$(\epsilon_1, \epsilon_2)$-approximate second-order minimizer (3.3.4). Up to termination the
method uses at most (3.3.29)
$$\kappa^D \frac{f(x_0) - f_{\mathrm{low}}}{\min(\epsilon_1^{3/2}, \epsilon_2^3)} + \kappa^F$$
evaluations of $f$ and at most (3.3.30)
$$\kappa^T \frac{f(x_0) - f_{\mathrm{low}}}{\min(\epsilon_1^{3/2}, \epsilon_2^3)} + 2$$
evaluations of $\nabla f$ and $\nabla^2 f$, where $\kappa^T = \kappa^T_{\mathrm{AR2}}$,
$\kappa^D = \kappa^T (1 + |\log \gamma_1| / \log \gamma_2)$ and
$\kappa^F = \kappa^C_{\mathrm{AR2}}$.

**Correction.** The explicit bound in (3.3.30) needs $+2$. The descent estimate counts
successful steps followed by a nonterminal iterate. The initial evaluation and the
last successful step add two to that count, as in (3.3.22).
For example, take $f(x)=M x^2/2$, $x_0=2/M$, $\epsilon_1=\epsilon_2=1$, and
$L_{f,2}=1$. With fixed AR2 parameters and sufficiently large $M$, the exact cubic
step has ratio $1$ and reduces the gradient from $2$ to below $1$. The two gradient
and Hessian evaluations exceed the printed bound $1+2\kappa^T_{\mathrm{AR2}}/M$.

**Generalization.** The source assumes $\epsilon_2 \le 1$. The bound holds for every
$\epsilon_2 > 0$. -/
theorem theorem_3_3_9 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L₂)
    (h : algorithm_3_3_1 f P ε₁ (some e) x s σ) :
    ∃ kε, IsFirstHit (fun k => stopTest f ε₁ (some e) (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaTAR2 P L₂ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f (x 0) - flow) /
          min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) + kappaCAR2 P L₂ ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f 2 x s k) kε : ℝ) ≤
        kappaTAR2 P L₂ * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) + 2 := by
  have hκ := kappaTAR2_pos (P := P) hf.nonneg
  have hε := h.ε₁_pos
  have he : 0 < e := h.ε₂_pos e rfl
  have hM : 0 < min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) := lt_min (by positivity) (by positivity)
  set δ := min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) / kappaTAR2 P L₂
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ =
      kappaTAR2 P L₂ * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) := by
    simp only [δ]; field_simp
  obtain ⟨kε, hk, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease (σmax := sigmaMaxAR2 P L₂)
    (V := fun k => f (x k)) (Vlow := flow)
    (fun k hk => lemma_3_3_2 hf h (IsARRun.forall_lt_not_stop_iff.1 hk)) hδ
    (fun k hk => (h.run.accept k hk).le (w := f) rfl
      ((lt_of_le_of_lt (by
          have := h.sigma_pos (fun j hj => (IsARRun.forall_le_not_stop_iff.1 hk) j hj.le)
          positivity) (lemma_3_3_1 h (IsARRun.forall_le_not_stop_iff.1 hk)))))
    (fun k _ => hb (x k))
    (fun k hk hs => ar2_decrease_second hf h (IsARRun.forall_le_not_stop_iff.1 hk) hs)
  rw [hNδ] at hF hD
  refine ⟨kε, IsARRun.isFirstHit_stop_iff.1 hk, ?_, hD⟩
  rw [kappaCAR2, ← sigmaMaxAR2_div_eq]
  calc (funEvalCount kε : ℝ) ≤ _ := hF
    _ = _ := by ring

end SecondOrder

/-! ### Sharpness: Theorems 3.3.6 and 3.3.10 -/

section Sharpness

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)

/-- Let $G : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable. The AR2 model of the
ridge function $f(x) = G(\langle e_0, x \rangle)$ on $\mathbb{R}^1$ is
$$m(s) = G(a) + G'(a) t + \tfrac12 G''(a) t^2 + \frac{\sigma}{6} |t|^3, \qquad a = \langle e_0,
  x \rangle, \ t = \langle e_0, s \rangle.$$
-/
theorem ar2Model_ridge {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (x s : EuclideanSpace ℝ (Fin 1))
    (σ : ℝ) :
    ar2Model (ridge G e₀) x σ s = G ⟪e₀, x⟫ + deriv G ⟪e₀, x⟫ * ⟪e₀, s⟫ +
      iteratedDeriv 2 G ⟪e₀, x⟫ * ⟪e₀, s⟫ ^ 2 / 2 + σ / 6 * |⟪e₀, s⟫| ^ 3 := by
  rw [ar2Model_apply, taylorPolynomial_two_ridge hG, norm_eq_abs_inner_e₀]

section Spike

variable {G : ℝ → ℝ} {q : ℕ} {x : EuclideanSpace ℝ (Fin 1)} {α : ℝ}

/-- Let $G$ be twice continuously differentiable with a spike jet of order $q \in \{1, 2\}$ and
height $\alpha$ at $a = \langle e_0, x \rangle$: $G^{(q)}(a) = -\alpha$ and the other
derivatives of order $1$ and $2$ vanish there. Then the AR2 model of the ridge function is
$m(s) = G(a) - \alpha t^q/q! + \frac{\sigma}{6} |t|^3$ with $t = \langle e_0, s \rangle$, that
is, $G(a)$ plus `Optimization.negMonomialRegModel 2 q σ α t`. -/
theorem ar2Model_ridge_spike (hG : ContDiff ℝ 2 G) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hd : IsSpikeJetOf 2 G q ⟪e₀, x⟫ α) (σ : ℝ) (s : EuclideanSpace ℝ (Fin 1)) :
    ar2Model (ridge G e₀) x σ s = G ⟪e₀, x⟫ + negMonomialRegModel 2 q σ α ⟪e₀, s⟫ := by
  rw [ar2Model_apply, taylorPolynomial_ridge_spike hG hq hq2 hd, norm_eq_abs_inner_e₀,
    negMonomialRegModel_def]
  norm_num [Nat.factorial]
  ring

end Spike

/-- AR2 runs on one-dimensional spike data, the mechanism of Theorems 3.3.6 and 3.3.10 of
[cartis2022evaluation]. Let the AR2 constants be given, let $\epsilon_1 \in (0, 1]$, let
$\epsilon_2$ be $+\infty$ or positive, let $q \in \{1, 2\}$, and let
$G : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable. Let $K \in \mathbb{N}$ and
points $\xi_0, \dots, \xi_K \in \mathbb{R}$ and heights $\alpha_k > 0$ ($k < K$) satisfy, for
all $k < K$:

* $G$ has a spike jet of order $q$ and height $\alpha_k$ at $\xi_k$:
  $G^{(q)}(\xi_k) = -\alpha_k$, and the other derivatives of order $1$ and $2$ vanish;
* $\xi_{k+1} = \xi_k + (\alpha_k/\lambda)^{1/(3 - q)}$ with $\lambda = \sigma_0 (q - 1)!/2$, so
  that $t_k = \xi_{k+1} - \xi_k$ is the global minimizer of
  $-\alpha_k t^q/q! + \sigma_0 |t|^3/6$;
* $G(\xi_{k+1}) = G(\xi_k) - \alpha_k t_k^q / q!$.

Assume also that, for $k \le K$, the point $\xi_k e_0$ passes the test (3.3.4) for the ridge
function $f(x) = G(\langle e_0, x \rangle)$ if and only if $k = K$. Then there is an AR2 run on
$f$ with $x_k = \xi_k e_0$ for all $k$ and $\sigma_k = \sigma_0$ for all $k$, whose steps $s_k$
for $k < K$ are global minimizers of the models and have $\rho_k = 1$, and which terminates
exactly at iteration $K$.

The spike jet is `Optimization.IsSpikeJetOf 2 G q`.

**Reading.** Realizes global minimizers and unit ratios for AR2 with arbitrary initial weight in
place of the fixed sample weight.
-/
theorem exists_ar2_ridge_run (P : AR2Params) {ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1)
    {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e) {q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G) {xr α : ℕ → ℝ} {K : ℕ} (hα : ∀ k < K, 0 < α k)
    (hd : ∀ k < K, IsSpikeJetOf 2 G q (xr k) (α k))
    (hx : ∀ k < K, xr (k + 1) = xr k + (α k / (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial)) ^
      (1 / ((2 - q + 1 : ℕ) : ℝ)))
    (hval : ∀ k < K, G (xr (k + 1)) = G (xr k) - α k * (xr (k + 1) - xr k) ^ q / q.factorial)
    (htest : ∀ k ≤ K, (stopTest (ridge G e₀) ε₁ ε₂ (xr k • e₀) ↔ K ≤ k)) :
    ∃ x s : ℕ → EuclideanSpace ℝ (Fin 1), ∃ σ : ℕ → ℝ, x 0 = xr 0 • e₀ ∧
      algorithm_3_3_1 (ridge G e₀) P ε₁ ε₂ x s σ ∧ (∀ k, σ k = P.σ₀) ∧
      (∀ k < K, IsMinOn (ar2Model (ridge G e₀) (x k) (σ k)) univ (s k) ∧
        taylorRatio (ridge G e₀) 2 x s k = 1) ∧
      IsFirstHit (fun k => stopTest (ridge G e₀) ε₁ ε₂ (x k)) K ∧ ∀ k, x k = xr k • e₀ := by
  set f := ridge G e₀
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • e₀
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => (xr (k + 1) - xr k) • e₀
  have hσ₀ := P.σ₀_pos
  have hxs : ∀ k, x k + s k = x (k + 1) := fun k => by simp only [x, s, ← add_smul]; ring_nf
  have hdx : ∀ k < K, IsSpikeJetOf 2 G q ⟪e₀, x k⟫ (α k) := fun k hk => by
    rw [inner_e₀_smul]; exact hd k hk
  -- the step is the global minimizer
  have ht : ∀ k < K, ⟪e₀, s k⟫ = (α k / (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial)) ^
      (1 / ((2 - q + 1 : ℕ) : ℝ)) := fun k hk => by
    simp only [s]; rw [inner_e₀_smul, hx k hk]; ring
  have hmin : ∀ k < K, IsMinOn (ar2Model f (x k) P.σ₀) univ (s k) := fun k hk => by
    obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization (p := 2) hq hq2 hσ₀ (hα k hk)
    intro y _
    simp only [mem_ofPred_eq]
    rw [ar2Model_ridge_spike hG hq hq2 (hdx k hk), ar2Model_ridge_spike hG hq hq2 (hdx k hk),
      ht k hk]
    exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  -- the model decreases
  have htpos : ∀ k < K, 0 < ⟪e₀, s k⟫ := fun k hk => by
    rw [ht k hk]
    have := hα k hk
    apply Real.rpow_pos_of_pos
    positivity
  have hdec : ∀ k < K, ar2Model f (x k) P.σ₀ (s k) < ar2Model f (x k) P.σ₀ 0 := fun k hk => by
    obtain ⟨-, hv, -⟩ := isMinOn_neg_monomial_add_regularization (p := 2) hq hq2 hσ₀ (hα k hk)
    rw [ar2Model_ridge_spike hG hq hq2 (hdx k hk), ar2Model_ridge_spike hG hq hq2 (hdx k hk),
      ht k hk, hv, inner_zero_right, negMonomialRegModel_def, zero_pow (by omega), abs_zero,
      zero_pow (by norm_num)]
    have h1 : (0 : ℝ) < ((2 - q + 1 : ℕ) : ℝ) / ((2 + 1) * q.factorial) := by positivity
    have h2 : 0 < (α k / (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial)) ^
        (1 / ((2 - q + 1 : ℕ) : ℝ)) := by rw [← ht k hk]; exact htpos k hk
    have := hα k hk
    have : 0 < ((2 - q + 1 : ℕ) : ℝ) / ((2 + 1) * q.factorial) * α k *
        ((α k / (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial)) ^
          (1 / ((2 - q + 1 : ℕ) : ℝ))) ^ q := by positivity
    simp only [neg_mul, mul_zero, zero_div, add_zero]
    linarith
  -- the ratio
  have hratio : ∀ k < K, taylorRatio f 2 x s k = 1 := fun k hk => by
    have hts : ⟪e₀, s k⟫ = xr (k + 1) - xr k := by simp only [s]; rw [inner_e₀_smul]
    have hT := taylorDecrement_ridge_spike hG hq hq2 (hdx k hk) (s k)
    have hpos : 0 < α k * (xr (k + 1) - xr k) ^ q / q.factorial := by
      have := hα k hk; have := htpos k hk; rw [hts] at this; positivity
    rw [taylorRatio_def, hT, hts, reductionRatio_def, hxs]
    simp only [f, x, ridge_apply, inner_e₀_smul]
    rw [hval k hk, sub_sub_cancel, div_self hpos.ne']
  have hhit : IsFirstHit (fun k => stopTest f ε₁ ε₂ (x k)) K :=
    ⟨(htest K le_rfl).2 le_rfl, fun j hj h => absurd ((htest j hj.le).1 h) (not_le.2 hj)⟩
  have hbefore : ∀ k, (∀ j ≤ k, ¬ IsARRun.Stop (fun k => stopTest f ε₁ ε₂ (x k))
      (fun _ => False) j) → k < K := fun k hk =>
    not_le.1 fun hle => (IsARRun.forall_le_not_stop_iff.1 hk) K hle hhit.test
  refine ⟨x, s, fun _ => P.σ₀, rfl, ⟨hε₁, hε₁1, hε₂, ⟨rfl, fun k hk h1 => ?_, fun k hk => ?_⟩⟩,
    fun _ => rfl, fun k hk => ⟨hmin k hk, hratio k hk⟩, hhit, fun _ => rfl⟩
  · have hk' : k < K := by
      by_contra hle
      rcases (not_lt.1 hle).eq_or_lt with heq | hlt
      · exact h1 (heq ▸ hhit.test)
      · exact hk K hlt (Or.inl hhit.test)
    exact ar2Step_of_isMinOn P ε₂ (hmin k hk') (hdec k hk')
  · have hk' := hbefore k hk
    change ARAcceptance P.ar (taylorRatio f 2 x s k) (x k) (s k) (x (k + 1)) P.σ₀ P.σ₀
    rw [← hxs, hratio k hk']
    exact arAcceptance_of_one_le P.ar le_rfl _ _ P.ar.σmin_le_σ₀ hσ₀.le

/-- The termination index $k_\epsilon = \lceil \epsilon^{-3/(3 - q)} \rceil$ of the one-dimensional
AR2 examples: $\lceil \epsilon^{-3/2} \rceil$ for $q = 1$, and $\lceil \epsilon^{-3} \rceil$ for
$q = 2$. -/
noncomputable def ar2SlowK (q : ℕ) (ε : ℝ) : ℕ :=
  ⌈ε ^ (-((2 + 1 : ℝ) / ((2 - q + 1 : ℕ) : ℝ)))⌉₊

/-- The heights $\alpha_k = \epsilon + \epsilon (k_\epsilon - k)/k_\epsilon$ of the spike
derivatives of the AR2 examples. Lean's division gives $\alpha_k = \epsilon$ when
$k_\epsilon = 0$. -/
noncomputable def ar2SlowAlpha (ε : ℝ) (K k : ℕ) : ℝ := ε + ε * ((K : ℝ) - k) / K

/-- For $q = 1$, the termination index is $\lceil \epsilon^{-3/2} \rceil$. -/
theorem ar2SlowK_one (ε : ℝ) : ar2SlowK 1 ε = ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ := by
  rw [ar2SlowK]; norm_num

/-- For $q = 2$, the termination index is $\lceil \epsilon^{-3} \rceil$. -/
theorem ar2SlowK_two (ε : ℝ) : ar2SlowK 2 ε = ⌈ε ^ (-(3 : ℝ))⌉₊ := by
  rw [ar2SlowK]; norm_num

/-- For $\epsilon > 0$, the termination index is positive. -/
theorem ar2SlowK_pos {q : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 < ar2SlowK q ε :=
  Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)

/-- Let $\epsilon > 0$, $k_\epsilon > 0$ and $k \le k_\epsilon$. Then $\alpha_k \le \epsilon$ if and
only if $k \ge k_\epsilon$. Hence $\alpha_k > \epsilon$ for $k < k_\epsilon$ and
$\alpha_{k_\epsilon} = \epsilon$. -/
theorem ar2SlowAlpha_le_iff {ε : ℝ} (hε : 0 < ε) {K k : ℕ} (hK : 0 < K) (hk : k ≤ K) :
    ar2SlowAlpha ε K k ≤ ε ↔ K ≤ k := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
  rw [ar2SlowAlpha, add_le_iff_nonpos_right, div_nonpos_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_le.2 hK')
    · have : (K : ℝ) - k ≤ 0 := by nlinarith
      exact_mod_cast (show (K : ℝ) ≤ k by linarith)
  · intro h
    have : (K : ℝ) ≤ k := by exact_mod_cast h
    right; exact ⟨by nlinarith, hK'.le⟩

/-- Let $\epsilon > 0$, $k_\epsilon > 0$ and $k \le k_\epsilon$. Then $\alpha_k > 0$. -/
theorem ar2SlowAlpha_pos {ε : ℝ} (hε : 0 < ε) {K k : ℕ} (hK : 0 < K) (hk : k ≤ K) :
    0 < ar2SlowAlpha ε K k := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
  have : 0 ≤ ε * ((K : ℝ) - k) / K := div_nonneg (mul_nonneg hε.le (by linarith)) hK'.le
  rw [ar2SlowAlpha]; linarith

/-- The one-dimensional AR2 examples: the data of Theorem 12.2.15 of [cartis2022evaluation] with
$p = 2$ (§12.2.2.4). Let the AR2 constants be given and let $q \in \{1, 2\}$. There are
$L_1 \ge 1$, $L_2 \ge 1$ and $B \ge 0$ with the following property. For every
$\epsilon \in (0, 1]$ there are a twice continuously differentiable
$G : \mathbb{R} \to \mathbb{R}$ and points $\xi_0 = 0, \xi_1, \dots$ such that the ridge
function $f(x) = G(\langle e_0, x \rangle)$ on $\mathbb{R}^1$ satisfies f.Bb with
$f_{\mathrm{low}} = -B$, f.gL with $L_1$, f.HL with $L_2$ and $|f| \le B$, and, with
$k_\epsilon = \lceil \epsilon^{-3/(3 - q)} \rceil$ and the heights $\alpha_k = \epsilon +
\epsilon (k_\epsilon - k)/k_\epsilon$:

* for $k \le k_\epsilon$, $G$ has a spike jet of order $q$ and height $\alpha_k$ at $\xi_k$;
* for $k < k_\epsilon$, $\xi_{k+1} = \xi_k + (\alpha_k/\lambda)^{1/(3 - q)}$ with
  $\lambda = \sigma_0 (q - 1)!/2$, so the points are spaced by the global minimizers of the AR2
  models with $\sigma = \sigma_0$;
* for $k < k_\epsilon$, $G(\xi_{k+1}) = G(\xi_k) - \alpha_k (\xi_{k+1} - \xi_k)^q / q!$, which
  is $T_{f,2}(x_k, s_k)$.

The construction is `Optimization.exists_slowTaylorOrder_interpolant`, in which the constants
depend only on $\sigma_0$.

**Reading.** Uses the prescribed jets and value recursion with any positive initial weight and
accepts tolerances up to one.
-/
theorem exists_ar2_slow_data (P : AR2Params) {q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) :
    ∃ L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (G : ℝ → ℝ) (xr : ℕ → ℝ), ContDiff ℝ 2 G ∧
        Chapter02.AssumptionBb (ridge G e₀) (-B) ∧ Chapter02.AssumptionGL (ridge G e₀) L₁ ∧
        AssumptionHL (ridge G e₀) L₂ ∧ (∀ y, |ridge G e₀ y| ≤ B) ∧ xr 0 = 0 ∧
        (∀ k ≤ ar2SlowK q ε, IsSpikeJetOf 2 G q (xr k) (ar2SlowAlpha ε (ar2SlowK q ε) k)) ∧
        (∀ k < ar2SlowK q ε, xr (k + 1) = xr k + (ar2SlowAlpha ε (ar2SlowK q ε) k /
          (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial)) ^ (1 / ((2 - q + 1 : ℕ) : ℝ))) ∧
        ∀ k < ar2SlowK q ε, G (xr (k + 1)) = G (xr k) -
          ar2SlowAlpha ε (ar2SlowK q ε) k * (xr (k + 1) - xr k) ^ q / q.factorial := by
  have hσ₀ := P.σ₀_pos
  set c : ℝ := ((2 : ℕ).factorial : ℝ) / (P.σ₀ * (q - 1).factorial)
  have hc : 0 < c := by positivity
  have hcα : ∀ α : ℝ, c * α = α / (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial) := fun α => by
    simp only [c]; field_simp
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowTaylorOrder_interpolant (p := 2) hq hq2 hc
  refine ⟨max B 1, max L 1, B, le_max_right _ _, le_max_right _ _, hB, fun ε hε hε1 => ?_⟩
  set K := ar2SlowK q ε
  set xr : ℕ → ℝ := fun k => ∑ j ∈ range k,
    (c * (ε + ε * ((K : ℝ) - j) / K)) ^ (1 / ((2 - q + 1 : ℕ) : ℝ))
  obtain ⟨G, hG, hGL, hGB, hGk, hGv⟩ := H ε K xr hε hε1 rfl
    (fun k _ => by simp only [xr, sum_range_succ])
  have hG2 : ContDiff ℝ 2 G := by exact_mod_cast hG
  obtain ⟨hb, hgl, -, hhl, -⟩ := ridge_assumptions_two hG2 hGL hGB
  refine ⟨G, xr, hG2, hb, hgl, hhl, fun y => ?_, by simp [xr], fun k hk => hGk k hk,
    fun k _ => ?_, fun k hk => hGv k hk⟩
  · have := hGB 0 (by norm_num) ⟪e₀, y⟫
    rwa [iteratedDeriv_zero] at this
  · simp only [xr, sum_range_succ, ar2SlowAlpha, hcα]

/-- **Theorem 3.3.6** of [cartis2022evaluation] (slow first-order convergence of AR2). For all AR2
constants there are $f_{\mathrm{low}}$, $L_{f,1} \ge 1$, $L_{f,2} \ge 1$ and $B$ with the
following property. For every $\epsilon_1 \in (0, 1]$ there are a function
$f : \mathbb{R}^1 \to \mathbb{R}$ that satisfies f.Bb with $f_{\mathrm{low}}$, f.gL with
$L_{f,1}$, f.HL with $L_{f,2}$ and $|f| \le B$, and an AR2 run with $\epsilon_2 = +\infty$ from
$x_0 = 0$, such that:

* $\sigma_k = \sigma_0$ for all $k$;
* for $k < k_\epsilon = \lceil \epsilon_1^{-3/2} \rceil$, the step $s_k$ is a global minimizer
  of the cubic model and $\rho_k = 1$, so every iteration is very successful;
* the first iteration with $\|\nabla f(x_k)\| \le \epsilon_1$ is $k_\epsilon$.

So the run uses $k_\epsilon + 1$ evaluations of $f$, $\nabla f$ and $\nabla^2 f$.

**Reading.** The source defers the proof to §12.2.2.4. The theorem is proved here from the data
of Theorem 12.2.15 with $q = 1$ (`CartisGouldToint.Chapter03.exists_ar2_slow_data`). -/
theorem theorem_3_3_6 (P : AR2Params) :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_3_3_1 f P ε none x s σ ∧ (∀ k, σ k = P.σ₀) ∧
          (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, IsMinOn (ar2Model f (x k) (σ k)) univ (s k) ∧
            taylorRatio f 2 x s k = 1) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ := by
  obtain ⟨L₁, L₂, B, hL₁, hL₂, -, H⟩ := exists_ar2_slow_data P le_rfl (by norm_num : 1 ≤ 2)
  refine ⟨-B, L₁, L₂, B, hL₁, hL₂, fun ε hε hε1 => ?_⟩
  obtain ⟨G, xr, hG, hb, hgl, hhl, hB, hx0, hd, hx, hv⟩ := H ε hε hε1
  have hK := ar2SlowK_pos (q := 1) hε
  set K := ar2SlowK 1 ε
  have htest : ∀ k ≤ K, (stopTest (ridge G e₀) ε none (xr k • e₀) ↔ K ≤ k) := fun k hk => by
    rw [stopTest_none, gradient_ridge (hG.differentiable (by norm_num)), inner_e₀_smul,
      ← iteratedDeriv_one, (hd k hk).1, norm_smul, norm_e₀, mul_one, norm_neg, Real.norm_of_nonneg
      (ar2SlowAlpha_pos hε hK hk).le]
    exact ar2SlowAlpha_le_iff hε hK hk
  obtain ⟨x, s, σ, hx0', hrun, hσ, hmin, hhit, -⟩ := exists_ar2_ridge_run P hε hε1
    (ε₂ := none) (fun _ h => absurd h (by simp)) le_rfl (by norm_num) hG
    (fun k hk => ar2SlowAlpha_pos hε hK hk.le) (fun k hk => hd k hk.le) hx hv htest
  refine ⟨ridge G e₀, hb, hgl, hhl, hB, x, s, σ, by rw [hx0', hx0, zero_smul], hrun, hσ, ?_, ?_⟩
  · rw [← ar2SlowK_one]; exact hmin
  · rw [← ar2SlowK_one]; simpa only [stopTest_none] using hhit

/-- **Theorem 3.3.10** of [cartis2022evaluation] (slow second-order convergence of AR2). For all AR2
constants there are $f_{\mathrm{low}}$ and $L_{f,2} \ge 1$ with the following property. For all
$\epsilon_1, \epsilon_2 \in (0, 1]$ there are a function $f : \mathbb{R}^1 \to \mathbb{R}$ that
satisfies f.Bb with $f_{\mathrm{low}}$ and f.HL with $L_{f,2}$, and an AR2 run with these
tolerances from $x_0 = 0$ with $\sigma_k = \sigma_0$ for all $k$, whose first iteration that
passes the test (3.3.4) is
$$\max\left( \lceil \epsilon_1^{-3/2} \rceil, \lceil \epsilon_2^{-3} \rceil \right).$$

**Reading.** The source defers the proof to §12.2.2.4. The theorem is proved here from the data
of Theorem 12.2.15. If $\lceil \epsilon_1^{-3/2} \rceil \ge \lceil \epsilon_2^{-3} \rceil$, the
example is that of Theorem 3.3.6, which has zero curvature. Otherwise it is a negative-curvature
example with zero gradients. -/
theorem theorem_3_3_10 (P : AR2Params) :
    ∃ flow L₂ : ℝ, 1 ≤ L₂ ∧ ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < ε₂ → ε₂ ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧ AssumptionHL f L₂ ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_3_3_1 f P ε₁ (some ε₂) x s σ ∧ (∀ k, σ k = P.σ₀) ∧
          IsFirstHit (fun k => stopTest f ε₁ (some ε₂) (x k))
            (max ⌈ε₁ ^ (-(3 / 2 : ℝ))⌉₊ ⌈ε₂ ^ (-(3 : ℝ))⌉₊) := by
  obtain ⟨L₁, L₂, B, -, hL₂, -, H⟩ := exists_ar2_slow_data P le_rfl (by norm_num : 1 ≤ 2)
  obtain ⟨L₁', L₂', B', -, -, -, H'⟩ := exists_ar2_slow_data P (q := 2) (by norm_num) le_rfl
  refine ⟨-max B B', max L₂ L₂', hL₂.trans (le_max_left _ _),
    fun ε₁ ε₂ hε₁ hε₁1 hε₂ hε₂1 => ?_⟩
  rcases le_total ⌈ε₂ ^ (-(3 : ℝ))⌉₊ ⌈ε₁ ^ (-(3 / 2 : ℝ))⌉₊ with hle | hle
  · -- the first-order example
    rw [max_eq_left hle]
    obtain ⟨G, xr, hG, hb, -, hhl, -, hx0, hd, hx, hv⟩ := H ε₁ hε₁ hε₁1
    have hK := ar2SlowK_pos (q := 1) hε₁
    set K := ar2SlowK 1 ε₁
    have htest : ∀ k ≤ K, (stopTest (ridge G e₀) ε₁ (some ε₂) (xr k • e₀) ↔ K ≤ k) :=
      fun k hk => by
        rw [stopTest_some, isApproxSecondOrderMinimizer_def, hessianMinEig_ridge hG, inner_e₀_smul,
          ((hd k hk).2 2 (by norm_num) le_rfl (by norm_num)),
          gradient_ridge (hG.differentiable (by norm_num)), inner_e₀_smul, ← iteratedDeriv_one,
          (hd k hk).1, norm_smul, norm_e₀, mul_one, norm_neg,
          Real.norm_of_nonneg (ar2SlowAlpha_pos hε₁ hK hk).le, ← ar2SlowAlpha_le_iff hε₁ hK hk]
        exact ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩
    obtain ⟨x, s, σ, hx0', hrun, hσ, -, hhit, -⟩ := exists_ar2_ridge_run P hε₁ hε₁1
      (ε₂ := some ε₂) (by simpa using hε₂) le_rfl (by norm_num) hG
      (fun k hk => ar2SlowAlpha_pos hε₁ hK hk.le) (fun k hk => hd k hk.le) hx hv htest
    refine ⟨ridge G e₀, fun y => (hb y).trans' (by linarith [le_max_left B B']),
      hhl.mono (le_max_left _ _), x, s, σ, by rw [hx0', hx0, zero_smul], hrun, hσ, ?_⟩
    rw [← ar2SlowK_one]; exact hhit
  · -- the negative-curvature example
    rw [max_eq_right hle]
    obtain ⟨G, xr, hG, hb, -, hhl, -, hx0, hd, hx, hv⟩ := H' ε₂ hε₂ hε₂1
    have hK := ar2SlowK_pos (q := 2) hε₂
    set K := ar2SlowK 2 ε₂
    have htest : ∀ k ≤ K, (stopTest (ridge G e₀) ε₁ (some ε₂) (xr k • e₀) ↔ K ≤ k) :=
      fun k hk => by
        have hg1 := (hd k hk).2 1 le_rfl (by norm_num) (by norm_num)
        rw [iteratedDeriv_one] at hg1
        rw [stopTest_some, isApproxSecondOrderMinimizer_def, hessianMinEig_ridge hG, inner_e₀_smul,
          (hd k hk).1, gradient_ridge (hG.differentiable (by norm_num)), inner_e₀_smul, hg1,
          zero_smul, norm_zero, neg_le_neg_iff, ← ar2SlowAlpha_le_iff hε₂ hK hk]
        exact ⟨fun h => h.2, fun h => ⟨hε₁.le, h⟩⟩
    obtain ⟨x, s, σ, hx0', hrun, hσ, -, hhit, -⟩ := exists_ar2_ridge_run P hε₁ hε₁1
      (ε₂ := some ε₂) (by simpa using hε₂) (by norm_num) le_rfl hG
      (fun k hk => ar2SlowAlpha_pos hε₂ hK hk.le) (fun k hk => hd k hk.le) hx hv htest
    refine ⟨ridge G e₀, fun y => (hb y).trans' (by linarith [le_max_right B B']),
      hhl.mono (le_max_right _ _), x, s, σ, by rw [hx0', hx0, zero_smul], hrun, hσ, ?_⟩
    rw [← ar2SlowK_two]; exact hhit

end Sharpness

end CartisGouldToint.Chapter03
