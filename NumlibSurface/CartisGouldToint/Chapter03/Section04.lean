/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Analysis.SpecialFunctions.SqrtBound
import Numlib.Optimization.ModelBased.TaylorModel
import Numlib.Optimization.Subproblem.Regularization
import NumlibSurface.CartisGouldToint.Chapter03.Section02

/-!
# Cartis, Gould and Toint, Section 3.4: More algorithms with $O(\epsilon^{-3/2})$ complexity

This module formalizes Section 3.4 of [cartis2022evaluation] on $\mathbb{R}^n$. The section presents
two methods that use second derivatives. The first is the trust-region variant TRε (Algorithm
3.4.1), whose model (3.4.1) adds the fixed quadratic regularization $\tfrac12 \epsilon_* \|s\|^2$ to
the quadratic Taylor model $T_{f,2}(x, s)$. The second is the inexact regularized Newton framework
iRN (Algorithm 3.4.2), whose step $s_k$ solves $(\nabla^2 f(x_k) + \lambda_k I) s = -\nabla f(x_k)$
approximately, with a multiplier $\lambda_k$ between $\sigma^L_k \|s_k\|$ and $\sigma^U_k \|s_k\|$,
and is accepted by the ratio (3.4.35) with the predicted decrease $\|s_k\|^3$. Both methods reach
$\|\nabla f(x)\| \le \epsilon_1$ within $O(\epsilon_1^{-3/2})$ evaluations. With the second-order
test $\lambda_{\min}[\nabla^2 f(x)] \ge -\epsilon_2$, TRε needs $O(\max(\epsilon_1^{-2} \epsilon_2,
\epsilon_2^{-3}))$ evaluations, up to a logarithmic term, and iRN needs
$O(\max(\epsilon_1^{-3/2}, \epsilon_2^{-3}))$. The module proves the lemmas and the complexity
theorems of the section, and it builds the runs on the one-dimensional data (3.5.12) that Corollary
3.5.5 uses.

TRε is an instance of the generic trust-region run `Optimization.IsTRRun` of
`Numlib.Optimization.ModelBased.TRRun`. The proofs use the Taylor bounds of
`Numlib.Optimization.ModelBased.TaylorModel`, the subproblem theory of
`Numlib.Optimization.Subproblem.Regularization`, and the counting lemmas of
`Numlib.Optimization.Complexity.Basic`.

## Main definitions

* Algorithm 3.4.1, Step 0, `CartisGouldToint.Chapter03.TREpsParams`: the constants of TRε.
* Equation (3.4.1), `CartisGouldToint.Chapter03.treModel`: the model $m(s) = T_{f,2}(x, s) +
  \tfrac12 \epsilon_* \|s\|^2$.
* Algorithm 3.4.1, `CartisGouldToint.Chapter03.algorithm_3_4_1`: the runs of TRε, with Step 2
  `CartisGouldToint.Chapter03.treStep`; runs exist by
  `CartisGouldToint.Chapter03.exists_algorithm_3_4_1`.
* Equations (3.4.15) and (3.4.20)–(3.4.22), `CartisGouldToint.Chapter03.kappaDeltaF`,
  `CartisGouldToint.Chapter03.kappaSTREps`, `CartisGouldToint.Chapter03.kappaATREps`,
  `CartisGouldToint.Chapter03.kappaCTREps`: the constants of the TRε bounds.
* Algorithm 3.4.2, Step 0, `CartisGouldToint.Chapter03.IRNParams`: the constants of iRN.
* Algorithm 3.4.2, `CartisGouldToint.Chapter03.algorithm_3_4_2`: the runs of iRN, with Step 2
  `CartisGouldToint.Chapter03.irnStep`, the ratio (3.4.35) `CartisGouldToint.Chapter03.irnRatio`,
  the test `CartisGouldToint.Chapter03.irnTest` and Step 5 `CartisGouldToint.Chapter03.irnUpdate`;
  runs exist by `CartisGouldToint.Chapter03.exists_algorithm_3_4_2`.
* Equations (3.4.38) and (3.4.42), `CartisGouldToint.Chapter03.sigmaUMax`,
  `CartisGouldToint.Chapter03.irnUnsuccBound`: the bound $\sigma^U_{\max}$ on $\sigma^U_k$ and the
  bound $M$ on a block of unsuccessful iterations.
* Theorems 3.4.11 and 3.4.12, `CartisGouldToint.Chapter03.kappaSIRN`,
  `CartisGouldToint.Chapter03.kappaAIRN`, `CartisGouldToint.Chapter03.kappaBIRN`,
  `CartisGouldToint.Chapter03.kappaTIRN`, `CartisGouldToint.Chapter03.kappaCIRN`,
  `CartisGouldToint.Chapter03.kappaDIRN`: the constants of the iRN bounds.

## Main results

* Lemma 3.4.1, `CartisGouldToint.Chapter03.lemma_3_4_1`: the predicted decrease of TRε exceeds
  $\tfrac12 \epsilon_* \|s_k\|^2$.
* Lemma 3.4.2, `CartisGouldToint.Chapter03.lemma_3_4_2` and
  `CartisGouldToint.Chapter03.lemma_3_4_2_delta`: a small radius forces a very successful iteration,
  and the radii stay above $(1 - \eta_2) \gamma_1 \epsilon_* / L_{f,2}$.
* Lemma 3.4.3, `CartisGouldToint.Chapter03.lemma_3_4_3`: a lower bound on an interior successful
  step.
* Lemma 3.4.4, `CartisGouldToint.Chapter03.lemma_3_4_4`: the decrease of $f$ on a successful
  iteration.
* Theorem 3.4.5, `CartisGouldToint.Chapter03.theorem_3_4_5`: TRε with
  $\epsilon_* = \sqrt{\epsilon_1}$ reaches $\|\nabla f\| \le \epsilon_1$ within
  $O(\epsilon_1^{-3/2})$ evaluations.
* Theorem 3.4.6, `CartisGouldToint.Chapter03.theorem_3_4_6`: TRε with $\epsilon_* = \epsilon_2$
  reaches second-order criticality within $O(\max(\epsilon_1^{-2} \epsilon_2, \epsilon_2^{-3}))$
  evaluations.
* Lemma 3.4.7, `CartisGouldToint.Chapter03.lemma_3_4_7`: a large multiplier forces a successful iRN
  iteration.
* Lemma 3.4.8, `CartisGouldToint.Chapter03.lemma_3_4_8`: $\sigma^U_k \le \sigma^U_{\max}$.
* Lemma 3.4.9, `CartisGouldToint.Chapter03.lemma_3_4_9` and
  `CartisGouldToint.Chapter03.lemma_3_4_9_curv`: lower bounds on the iRN step by the next gradient
  and by the negative curvature.
* Lemma 3.4.10, `CartisGouldToint.Chapter03.lemma_3_4_10` and
  `CartisGouldToint.Chapter03.lemma_3_4_10_last`: a block of unsuccessful iRN iterations has at most
  $M$ elements, or $M + 1$ at the end of the run.
* Theorem 3.4.11, `CartisGouldToint.Chapter03.theorem_3_4_11`: iRN reaches
  $\|\nabla f\| \le \epsilon_1$ within $O(\epsilon_1^{-3/2})$ evaluations.
* Theorem 3.4.12, `CartisGouldToint.Chapter03.theorem_3_4_12`: iRN reaches second-order criticality
  within $O(\max(\epsilon_1^{-3/2}, \epsilon_2^{-3}))$ evaluations.
* Equation (3.5.12), `CartisGouldToint.Chapter03.tre_slow_data`,
  `CartisGouldToint.Chapter03.tre_ridge_run`, `CartisGouldToint.Chapter03.tre_slow_example`,
  `CartisGouldToint.Chapter03.irn_slow_data`, `CartisGouldToint.Chapter03.irn_ridge_run`,
  `CartisGouldToint.Chapter03.irn_slow_example`: the TRε and iRN runs on one-dimensional data that
  need exactly $\lceil \epsilon^{-3/2} \rceil$ iterations, used in Corollary 3.5.5.

## Proof outline

For TRε, Lemma 3.4.2 bounds the radii from below, so the number of unsuccessful iterations is
bounded by the number of successful ones and a logarithmic term, and Lemma 3.4.4 bounds the number
of successful iterations through the decrease of $f$. For iRN, Lemma 3.4.10 bounds each block of
unsuccessful iterations by $M$, and on each successful iteration the decrease
$f(x_k) - f(x_{k+1}) \ge \eta \|s_k\|^3$, with the lower bounds of Lemma 3.4.9 on $\|s_k\|$, bounds
the number of successful iterations. In the second-order Theorems 3.4.6 and 3.4.12, a successful
iteration without the required decrease is followed by a successful iteration with it. Then
`Optimization.card_successSet_le_two_mul_add_one` gives $|\mathcal{S}_k| \le 2 |\mathcal{G}_k| + 1$,
where $\mathcal{S}_k$ is the set of successful iterations up to $k$ and $\mathcal{G}_k$ the set of
those with the required decrease.

## Conventions

* The tolerance $\epsilon_2 = +\infty$ is `none : Option ℝ`.
* A finite tolerance $\epsilon_2 = e$ is `some e`.
* The regularization weight $\epsilon_*$ of TRε is the parameter `εs`.
* An iteration $k$ is before termination if the termination test fails at all $j \le k$, and it is
  up to and including termination if the test fails at all $j < k$.
* The matrix $Q_k$ with orthonormal columns of (3.4.32) is represented by its range, a subspace
  $V_k$. The number $\lambda_{\min}[Q_k^T A Q_k]$ is `minCurvatureOn A (V k)`, and $Q_k = I$ is
  $V_k = \top$.
* The evaluation counts are `Optimization.funEvalCount`, which is $k_\epsilon + 1$, and
  `Optimization.derivEvalCount` of the successful iterations, which is one more than the number of
  successful iterations before $k_\epsilon$.

## Implementation notes

* Step 1 of Algorithm 3.4.1 couples the weight to the tolerances: $\epsilon_* = \sqrt{\epsilon_1}$
  if $\epsilon_2 = +\infty$, and $\epsilon_* = \epsilon_2$ otherwise. The run predicate takes
  $\epsilon_*$ as a parameter, and the complexity theorems impose the coupling. The condition
  $\Delta_0 > \epsilon_*$ of Step 0 is part of the run predicate.
* iRN has its own run predicate. When $\epsilon_2 < \infty$ the termination test depends on $Q_k$,
  which Step 2 computes, so the run predicate requires Step 2 also at the iteration where the run
  terminates.
* The ratio (3.4.35) of iRN is not scale invariant. The iRN example of Corollary 3.5.5 therefore
  rescales the data (3.5.12) to $c G(x/c)$ with $c = \min(1, (2\eta)^{-1/2})$; see
  `CartisGouldToint.Chapter03.irn_slow_data` and the deviations of
  `NumlibSurface.CartisGouldToint.Chapter03.Section05`.

## Deviations from the source

* **Lemma 3.4.1** (generalization). The source states (3.4.7) with $\ge$; the inequality is strict.
  See `CartisGouldToint.Chapter03.lemma_3_4_1`.
* **Lemma 3.4.3** (typo). In the proof, the quadratic inequality and its root are misprinted;
  (3.4.10) is proved directly. See `CartisGouldToint.Chapter03.lemma_3_4_3`.
* **Lemma 3.4.4** (typo). In the proof, the case labels (3.4.13) and (3.4.14) are swapped. See
  `CartisGouldToint.Chapter03.lemma_3_4_4`.
* **Theorem 3.4.6** (correction). The proof does not give the printed bounds; they hold with a
  factor $2$ on the leading terms and $+2$ in place of $+1$ for the derivative evaluations. See
  `CartisGouldToint.Chapter03.theorem_3_4_6`.
* **Lemma 3.4.10** (reading). The bound (3.4.42) is stated for a block of unsuccessful iterations
  that is followed by an iteration before termination; a final block can have one more element. See
  `CartisGouldToint.Chapter03.lemma_3_4_10_last`.
* **Theorem 3.4.11** (correction). The count misses the successful iterations; the constants are
  $\kappa^A = \kappa^S (M + 1)$ and $\kappa^B = M + 2$. See
  `CartisGouldToint.Chapter03.theorem_3_4_11`.
* **Theorem 3.4.12** (correction). The proof's claim that the gradient stays small is unjustified;
  the bounds hold with a factor $2$ on the leading terms and $\kappa^D = 2M + 3$. See
  `CartisGouldToint.Chapter03.theorem_3_4_12`.
-/

open Set Finset Optimization Subproblem
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter03

variable {n : ℕ}

/-! ### The TRε algorithm -/

/-- **Algorithm 3.4.1** of [cartis2022evaluation], Step 0. The constants of TRε consist of the
constants of TR1 in (2.3.3), that is, an initial radius $\Delta_0 > 0$, thresholds
$0 < \eta_1 \le \eta_2 < 1$ and radius factors $0 < \gamma_1 \le \gamma_2 < 1 < \gamma_3$,
together with a tolerance $\theta_1 > 0$ for the step condition (3.4.5).

The condition $\Delta_0 > \epsilon_*$ of Step 0 is part of the run predicate
`CartisGouldToint.Chapter03.algorithm_3_4_1`, because $\epsilon_*$ is a parameter of the run and
not a constant of this structure. -/
structure TREpsParams extends Chapter02.TR1Params where
  /-- The tolerance $\theta_1$ of the step condition (3.4.5). -/
  θ₁ : ℝ
  /-- The tolerance is positive: $\theta_1 > 0$. -/
  θ₁_pos : 0 < θ₁

/-- The regularized quadratic model (3.4.1) of TRε at $x$ with weight $\epsilon_*$:
$$m(s) = T_{f,2}(x, s) + \tfrac12 \epsilon_* \|s\|^2,$$
where $T_{f,2}(x, s) = f(x) + \langle \nabla f(x), s \rangle + \tfrac12 \langle s, \nabla^2 f(x)
s \rangle$ is `CartisGouldToint.Chapter03.tr2Model`. -/
noncomputable def treModel (f : EuclideanSpace ℝ (Fin n) → ℝ) (εs : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  tr2Model f x s + εs / 2 * ‖s‖ ^ 2

section TREpsModel

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {εs : ℝ} {x s : EuclideanSpace ℝ (Fin n)}

/-- The model (3.4.1) is $m(s) = T_{f,2}(x, s) + \tfrac12 \epsilon_* \|s\|^2$ by definition. -/
theorem treModel_def : treModel f εs x s = tr2Model f x s + εs / 2 * ‖s‖ ^ 2 := rfl

/-- The quadratic Taylor model at the zero step is $T_{f,2}(x, 0) = f(x)$. -/
theorem tr2Model_zero_eq : tr2Model f x 0 = f x := by
  rw [tr2Model_eq, quadModel_zero, add_zero]

/-- The model (3.4.1) at the zero step is $m(0) = f(x)$. -/
theorem treModel_zero : treModel f εs x 0 = f x := by
  rw [treModel_def, tr2Model_zero_eq, norm_zero]; ring

/-- If $f$ is $C^2$ at $x$, then the model (3.4.1) is $m(s) = T_{f,2}(x, s) + \tfrac12 \epsilon_*
\|s\|^2$, where $T_{f,2}(x, \cdot)$ is the second-order Taylor polynomial
`taylorPolynomial f 2 x`. -/
theorem treModel_eq_taylorPolynomial (hf : ContDiffAt ℝ 2 f x) :
    treModel f εs x s = taylorPolynomial f 2 x s + εs / 2 * ‖s‖ ^ 2 := by
  rw [treModel_def, tr2Model_eq_taylorPolynomial hf]

/-- If $f$ is $C^2$ at $x$, then the model (3.4.1) is differentiable at every step $s$, with
gradient $\nabla m(s) = \nabla f(x) + \nabla^2 f(x) s + \epsilon_* s$. -/
theorem hasFDerivAt_treModel (hf : ContDiffAt ℝ 2 f x) (s : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (treModel f εs x)
      (innerSL ℝ (gradient f x + hessianOperator f x s + εs • s)) s := by
  have hq := hasFDerivAt_quadModel (g := gradient f x) (hessianOperator_isSymmetric hf) s
  have hn := ((hasFDerivAt_id s).norm_sq).const_mul (εs / 2)
  have : treModel f εs x = fun s => f x + quadModel (gradient f x) (hessianOperator f x) s +
      εs / 2 * ‖s‖ ^ 2 := funext fun s => by rw [treModel_def, tr2Model_eq]
  rw [this]
  refine ((hq.const_add (f x)).add hn).congr_fderiv ?_
  ext v
  simp
  ring

/-- If $f$ is $C^2$ at $x$, then the derivative of the model (3.4.1) at $s$ has norm $\|\nabla
f(x) + \nabla^2 f(x) s + \epsilon_* s\|$. -/
theorem norm_fderiv_treModel (hf : ContDiffAt ℝ 2 f x) :
    ‖fderiv ℝ (treModel f εs x) s‖ = ‖gradient f x + hessianOperator f x s + εs • s‖ := by
  rw [(hasFDerivAt_treModel hf s).fderiv, innerSL_apply_norm]

/-- Under Assumption f.HL with constant $L$, for all $x$ and $s$,
$$\|\nabla f(x + s)\| \le \tfrac{L}{2} \|s\|^2 + \|\nabla f(x) + \nabla^2 f(x) s\|.$$
This is (A.20) with $j = 1$ and $p = 2$: the gradient of the quadratic Taylor model is
$\nabla f(x) + \nabla^2 f(x) s$. -/
theorem norm_gradient_add_le {L : ℝ} (hL : AssumptionHL f L) :
    ‖gradient f (x + s)‖ ≤ L / 2 * ‖s‖ ^ 2 + ‖gradient f x + hessianOperator f x s‖ :=
  norm_gradient_add_le_of_lipschitz convex_univ (fun y _ => hL.contDiffAt y)
    hL.iteratedFDerivLipschitzOn (mem_univ x) (mem_univ (x + s))

end TREpsModel

/-- Step 2 of Algorithm 3.4.1 at an iterate $x$ with radius $\Delta$. A step $s$ is admissible if
$\|s\| \le \Delta$, the model (3.4.1) decreases, $m(s) < m(0)$, the gradient condition (3.4.5)
$\|\nabla m(s)\| \le \tfrac12 \theta_1 \|s\|^2$ holds when the step is interior
($\|s\| < \Delta$), and the step is on the boundary, $\|s\| = \Delta$, when
$\epsilon_2 < \infty$ and $\lambda_{\min}[\nabla^2 f(x)] < -\epsilon_2$.

The norm $\|\nabla m(s)\|$ is the norm of `fderiv ℝ (treModel f εs x) s`, and
$\lambda_{\min}[\nabla^2 f(x)]$ is `CartisGouldToint.Chapter01.hessianMinEig f x`. -/
def treStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : TREpsParams) (εs : ℝ) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖s‖ ≤ Δ ∧ treModel f εs x s < treModel f εs x 0 ∧
    (‖s‖ < Δ → ‖fderiv ℝ (treModel f εs x) s‖ ≤ P.θ₁ / 2 * ‖s‖ ^ 2) ∧
    ∀ e ∈ ε₂, Chapter01.hessianMinEig f x < -e → ‖s‖ = Δ

/-- **Algorithm 3.4.1** of [cartis2022evaluation] (TRε). Let $f : \mathbb{R}^n \to \mathbb{R}$, let
$\epsilon_1 \in (0, 1]$, let $\epsilon_2 \in (0, 1]$ or $\epsilon_2 = +\infty$, and let
$\epsilon_* \in (0, 1]$ with $\epsilon_* < \Delta_0$. Sequences of iterates $x_k$, steps $s_k$
and radii $\Delta_k$ form a **TRε run** if the initial radius is $\Delta_0$ and the following
holds at every iteration $k$ before termination. The step $s_k$ satisfies Step 2
(`CartisGouldToint.Chapter03.treStep`). With the ratio (3.4.6)
$$\rho_k = \frac{f(x_k) - f(x_k + s_k)}{T_{f,2}(x_k, 0) - T_{f,2}(x_k, s_k)},$$
the iteration is successful if $\rho_k \ge \eta_1$; then $x_{k+1} = x_k + s_k$, and otherwise
$x_{k+1} = x_k$. The radius satisfies $\Delta_{k+1} \in [\Delta_k, \gamma_3 \Delta_k]$ if
$\rho_k \ge \eta_2$, $\Delta_{k+1} \in [\gamma_2 \Delta_k, \Delta_k]$ if
$\eta_1 \le \rho_k < \eta_2$, and $\Delta_{k+1} \in [\gamma_1 \Delta_k, \gamma_2 \Delta_k]$ if
$\rho_k < \eta_1$. The run terminates at the first iteration $k$ with
$\|\nabla f(x_k)\| \le \epsilon_1$ and, if $\epsilon_2 < \infty$, $\lambda_{\min}[\nabla^2
f(x_k)] \ge -\epsilon_2$ (the test (3.4.3)–(3.4.4)).

The definition is the generic run `Optimization.IsTRRun` with the test
`CartisGouldToint.Chapter03.stopTest f ε₁ ε₂`, the step condition
`CartisGouldToint.Chapter03.treStep` and the ratio `CartisGouldToint.Chapter03.tr2Ratio`. Step 1
of the source sets $\epsilon_* = \sqrt{\epsilon_1}$ if $\epsilon_2 = +\infty$ and
$\epsilon_* = \epsilon_2$ otherwise. The run predicate takes $\epsilon_*$ as the parameter `εs`,
and the complexity theorems impose the coupling. The value `none` of `ε₂` stands for
$\epsilon_2 = +\infty$. -/
structure algorithm_3_4_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : TREpsParams) (ε₁ : ℝ)
    (ε₂ : Option ℝ) (εs : ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (Δ : ℕ → ℝ) : Prop where
  /-- The first-order tolerance is positive: $\epsilon_1 > 0$. -/
  ε₁_pos : 0 < ε₁
  /-- The first-order tolerance is at most one: $\epsilon_1 \le 1$. -/
  ε₁_le_one : ε₁ ≤ 1
  /-- If $\epsilon_2$ is finite, then $0 < \epsilon_2 \le 1$. -/
  ε₂_mem : ∀ e ∈ ε₂, 0 < e ∧ e ≤ 1
  /-- The regularization weight is positive: $\epsilon_* > 0$. -/
  εs_pos : 0 < εs
  /-- The regularization weight is at most one: $\epsilon_* \le 1$. -/
  εs_le_one : εs ≤ 1
  /-- The initial radius exceeds the weight: $\Delta_0 > \epsilon_*$. -/
  εs_lt_Δ₀ : εs < P.Δ₀
  /-- Steps 1–4: the iterates, steps and radii form a trust-region run with the TRε test, step
  condition and ratio. -/
  run : IsTRRun P.toTRParams (fun k => stopTest f ε₁ ε₂ (x k))
    (fun k => treStep f P εs ε₂ (x k) (Δ k) (s k)) (fun k => tr2Ratio f (x k) (s k)) x s Δ

/-! ### Existence of TRε runs -/

section TREpsExistence

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {εs : ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- The model (3.4.1) is the quadratic model with Hessian $\nabla^2 f(x) + \epsilon_* I$:
$$m(s) = f(x) + \langle \nabla f(x), s \rangle + \tfrac12 \langle s, (\nabla^2 f(x) + \epsilon_*
  I) s \rangle.$$
-/
theorem treModel_eq_quadModel (s : EuclideanSpace ℝ (Fin n)) :
    treModel f εs x s = f x + quadModel (gradient f x)
      (hessianOperator f x + εs • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      s := by
  rw [treModel_def, tr2Model_eq, quadModel_def, quadModel_def]
  simp only [add_apply, smul_apply,
    one_apply_eq_self, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- For all steps $s$ and $v$, the model (3.4.1) satisfies $m(s + v) + m(s - v) - 2 m(s) = \langle
v, \nabla^2 f(x) v \rangle + \epsilon_* \|v\|^2$. -/
theorem treModel_add_add_sub (s v : EuclideanSpace ℝ (Fin n)) :
    treModel f εs x (s + v) + treModel f εs x (s - v) - 2 * treModel f εs x s =
      ⟪v, hessianOperator f x v⟫ + εs * ‖v‖ ^ 2 := by
  simp only [treModel_def, tr2Model_eq, quadModel_def, map_add, map_sub, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right, norm_add_sq_real, norm_sub_sq_real]
  ring

/-- Let $f$ be $C^2$ at $x$, let $\epsilon_1 \ge 0$, $\epsilon_* > 0$ and $\Delta > 0$, and let
$\epsilon_* \le \epsilon_2$ if $\epsilon_2$ is finite. If the termination test (3.4.3)–(3.4.4)
fails at $x$, then some step $s$ satisfies Step 2 of Algorithm 3.4.1 at $x$ with radius
$\Delta$. A global minimizer of the model (3.4.1) in the trust region is such a step. -/
theorem exists_treStep (hf : ContDiffAt ℝ 2 f x) (P : TREpsParams) {ε₁ : ℝ} {ε₂ : Option ℝ}
    {Δ : ℝ} (hε₁ : 0 ≤ ε₁) (hεs : 0 < εs) (hε₂ : ∀ e ∈ ε₂, εs ≤ e) (hΔ : 0 < Δ)
    (hnot : ¬ stopTest f ε₁ ε₂ x) : ∃ s, treStep f P εs ε₂ x Δ s := by
  set H' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    hessianOperator f x + εs • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  set g := gradient f x
  have hm : treModel f εs x = fun s => f x + quadModel g H' s :=
    funext fun s => treModel_eq_quadModel s
  obtain ⟨s, hsΔ, hmin, hC, -⟩ := exists_isMinOn_quadModel_ball g H' hΔ.le
  have hneg : ∀ e ∈ ε₂, Chapter01.hessianMinEig f x < -e → ∃ u, ‖u‖ = 1 ∧
      ⟪u, hessianOperator f x u⟫ + εs < 0 ∧ ⟪u, g⟫ ≤ 0 := by
    intro e he hlam
    obtain ⟨u, hu, hHu, hgu⟩ := exists_eigenvector_hessianMinEig hf
      (hlam.trans_le (by linarith [hεs.le.trans (hε₂ e he)]))
    refine ⟨u, hu, ?_, hgu⟩
    rw [hHu, inner_smul_right, real_inner_self_eq_norm_sq, hu]
    linarith [hε₂ e he]
  have hq : ∀ u, ‖u‖ = 1 → quadModel g H' (Δ • u) =
      Δ * ⟪u, g⟫ + Δ ^ 2 / 2 * (⟪u, hessianOperator f x u⟫ + εs) := fun u hu => by
    rw [quadModel_smul, real_inner_comm]
    simp only [H', add_apply, smul_apply,
      one_apply_eq_self, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hu]
    ring
  refine ⟨s, hsΔ, ?_, fun hint => ?_, fun e he hlam => ?_⟩
  · rw [hm]
    simp only [quadModel_zero, add_zero, add_lt_iff_neg_left]
    rcases not_and_or.1 hnot with hg | hl
    · have hg : 0 < ‖g‖ := lt_of_le_of_lt hε₁ (not_le.1 hg)
      obtain ⟨t, ht⟩ := exists_isCauchyStep g H' hΔ.le
      have := neg_quadModel_cauchy_ge ht
      have hpos : 0 < ‖g‖ / 2 * min (‖g‖ / (1 + ‖H'‖)) Δ := by
        have : 0 < min (‖g‖ / (1 + ‖H'‖)) Δ := lt_min (by positivity) hΔ
        positivity
      linarith [hC t ht]
    · push Not at hl
      obtain ⟨e, he, hlam⟩ := hl
      obtain ⟨u, hu, hc, hgu⟩ := hneg e he hlam
      have h1 := hmin (show Δ • u ∈ Metric.closedBall 0 Δ by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu, Real.norm_of_nonneg hΔ.le,
          mul_one])
      simp only [mem_ofPred_eq] at h1
      rw [hq u hu] at h1
      have : Δ * ⟪u, g⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hΔ.le hgu
      have : Δ ^ 2 / 2 * (⟪u, hessianOperator f x u⟫ + εs) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) hc
      linarith
  · have hball : s ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Δ := by
      rwa [Metric.mem_ball, dist_zero_right]
    have hloc : IsLocalMin (treModel f εs x) s := by
      rw [hm]
      have hl : IsLocalMin (quadModel g H') s := hmin.isLocalMin
        (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hball) Metric.ball_subset_closedBall)
      exact isLocalMin_const.add hl
    rw [hloc.fderiv_eq_zero, norm_zero]
    exact mul_nonneg (by linarith [P.θ₁_pos]) (sq_nonneg _)
  · by_contra hne
    have hlt : ‖s‖ < Δ := lt_of_le_of_ne hsΔ hne
    obtain ⟨u, hu, hc, -⟩ := hneg e he hlam
    set t := Δ - ‖s‖
    have ht : 0 < t := sub_pos.2 hlt
    have hmem : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ t → s + v ∈ Metric.closedBall 0 Δ ∧
        s - v ∈ Metric.closedBall 0 Δ := fun v hv => by
      simp only [Metric.mem_closedBall, dist_zero_right]
      constructor
      · linarith [norm_add_le s v]
      · linarith [norm_sub_le s v]
    have hv : ‖t • u‖ ≤ t := by rw [norm_smul, hu, Real.norm_of_nonneg ht.le, mul_one]
    obtain ⟨h1, h2⟩ := hmem _ hv
    have e1 := hmin h1
    have e2 := hmin h2
    simp only [mem_ofPred_eq] at e1 e2
    have hid := treModel_add_add_sub (f := f) (εs := εs) (x := x) s (t • u)
    rw [hm] at hid
    simp only at hid
    have : ⟪t • u, hessianOperator f x (t • u)⟫ + εs * ‖t • u‖ ^ 2 =
        t ^ 2 * (⟪u, hessianOperator f x u⟫ + εs) := by
      rw [map_smul, inner_smul_left, inner_smul_right, norm_smul, hu, Real.norm_of_nonneg ht.le]
      simp only [conj_trivial]
      ring
    have hneg' : t ^ 2 * (⟪u, hessianOperator f x u⟫ + εs) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hc
    linarith

/-- **Algorithm 3.4.1** of [cartis2022evaluation], existence of runs. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be $C^2$, let $\epsilon_1 \in (0, 1]$, let
$\epsilon_2 \in (0, 1]$ or $\epsilon_2 = +\infty$, and let $\epsilon_* \in (0, 1]$ with
$\epsilon_* < \Delta_0$ and, if $\epsilon_2$ is finite, $\epsilon_* \le \epsilon_2$. Then for
every starting point $x_0$ there is a TRε run from $x_0$.

The condition $\epsilon_* \le \epsilon_2$ contains the coupling $\epsilon_* = \epsilon_2$ of
Step 1. The steps of the run are global minimizers of the model in the trust region, as in
`CartisGouldToint.Chapter03.exists_treStep`. -/
theorem exists_algorithm_3_4_1 (hf : ContDiff ℝ 2 f) (P : TREpsParams) {ε₁ : ℝ}
    {ε₂ : Option ℝ} (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε₂ : ∀ e ∈ ε₂, 0 < e ∧ e ≤ 1)
    (hεs : 0 < εs) (hεs1 : εs ≤ 1) (hΔ₀ : εs < P.Δ₀) (hεs₂ : ∀ e ∈ ε₂, εs ≤ e)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s Δ, x 0 = x₀ ∧ algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ := by
  obtain ⟨x, s, Δ, hx0, hrun, -⟩ := exists_isTRRun P.toTRParams (Inv := fun _ => True)
    (test := fun y => stopTest f ε₁ ε₂ y) (stepOK := fun _ y Δ s => treStep f P εs ε₂ y Δ s)
    (fun _ y _ s => tr2Ratio f y s) (fun _ y Δ _ hΔ hnot => by
      obtain ⟨s, hs⟩ := exists_treStep hf.contDiffAt P hε₁.le hεs hεs₂ hΔ hnot
      exact ⟨s, hs, trivial⟩) trivial
  exact ⟨x, s, Δ, hx0, hε₁, hε₁1, hε₂, hεs, hεs1, hΔ₀, hrun⟩

end TREpsExistence

/-! ### Lemmas 3.4.1–3.4.4 -/

section TREpsLemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : TREpsParams} {ε₁ : ℝ} {ε₂ : Option ℝ}
  {εs : ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ} {L : ℝ}

/-- **Lemma 3.4.1** of [cartis2022evaluation]. At every iteration $k$ before termination of a TRε
run,
$$T_{f,2}(x_k, 0) - T_{f,2}(x_k, s_k) > \tfrac12 \epsilon_* \|s_k\|^2.$$

**Generalization.** The source states (3.4.7) with $\ge$. The inequality is strict. -/
theorem lemma_3_4_1 (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) :
    εs / 2 * ‖s k‖ ^ 2 < tr2Model f (x k) 0 - tr2Model f (x k) (s k) := by
  obtain ⟨-, hm, -, -⟩ := h.run.step k hk
  rw [treModel_def, treModel_def, norm_zero] at hm
  linarith

namespace algorithm_3_4_1

/-- Before termination of a TRε run, the predicted decrease is positive:
$T_{f,2}(x_k, 0) - T_{f,2}(x_k, s_k) > 0$. -/
theorem pred_pos (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) :
    0 < -quadModel (gradient f (x k)) (hessianOperator f (x k)) (s k) := by
  rw [← tr2Model_zero_sub]
  exact lt_of_le_of_lt (by have := h.εs_pos; positivity) (lemma_3_4_1 h hk)

/-- If iteration $k$ of a TRε run is before termination and successful ($\rho_k \ge \eta_1$), then
$x_{k+1} = x_k + s_k$ and $f(x_k) - f(x_{k+1}) \ge \eta_1 (T_{f,2}(x_k, 0) - T_{f,2}(x_k,
s_k))$. -/
theorem sub_ge (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ tr2Ratio f (x k) (s k)) :
    x (k + 1) = x k + s k ∧
      P.η₁ * (tr2Model f (x k) 0 - tr2Model f (x k) (s k)) ≤ f (x k) - f (x (k + 1)) := by
  rw [tr2Model_zero_sub]
  exact h.run.sub_ge_of_succ (f := f)
    (pred := fun k => -quadModel (gradient f (x k)) (hessianOperator f (x k)) (s k)) hk
    (tr2Ratio_eq _ _ _) (h.pred_pos hk) hs

/-- Before termination of a TRε run, the objective does not increase: $f(x_{k+1}) \le f(x_k)$. -/
theorem le (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) : f (x (k + 1)) ≤ f (x k) :=
  (h.run.accept k hk).le (tr2Ratio_eq _ _ _) (h.pred_pos hk)

end algorithm_3_4_1

/-- **Lemma 3.4.2** of [cartis2022evaluation], first part. Let $f$ satisfy Assumption f.HL with
constant $L_{f,2}$, and consider a TRε run. If iteration $k$ is before termination and
$$\Delta_k < \frac{3 (1 - \eta_2) \epsilon_*}{L_{f,2}}, \qquad (3.4.8)$$
then $\rho_k \ge \eta_2$, so that iteration $k$ is successful ($\rho_k \ge \eta_1$), and
$\Delta_{k+1} \ge \Delta_k$. -/
theorem lemma_3_4_2 (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hΔk : Δ k < 3 * (1 - P.η₂) * εs / L) :
    P.η₂ ≤ tr2Ratio f (x k) (s k) ∧ P.η₁ ≤ tr2Ratio f (x k) (s k) ∧ Δ k ≤ Δ (k + 1) := by
  obtain ⟨hsΔ, -, -, -⟩ := h.run.step k hk
  have hεs := h.εs_pos
  have hL := hf.pos
  set pred := -quadModel (gradient f (x k)) (hessianOperator f (x k)) (s k)
  have hpred : εs / 2 * ‖s k‖ ^ 2 < pred := by
    have := lemma_3_4_1 h hk; rwa [tr2Model_zero_sub] at this
  have hpos : 0 < pred := h.pred_pos hk
  have habs : |f (x k + s k) - (f (x k) - pred)| ≤ L / 6 * ‖s k‖ ^ 3 := by
    have h1 := abs_sub_taylorPolynomial_le_of_lipschitz convex_univ (fun y _ => hf.contDiffAt y)
      hf.iteratedFDerivLipschitzOn (mem_univ (x k)) (mem_univ (x k + s k))
    have h2 : f (x k) - pred = taylorPolynomial f 2 (x k) (s k) := by
      rw [← tr2Model_eq_taylorPolynomial (hf.contDiffAt _), tr2Model_eq]; ring
    rw [h2]
    norm_num [Nat.factorial] at h1
    linarith
  set c := L * Δ k / (3 * εs)
  have hc : c < 1 - P.η₂ := by
    rw [lt_div_iff₀ hL] at hΔk
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hcp : L / 6 * ‖s k‖ ^ 3 ≤ c * pred := by
    have hΔ0 : 0 ≤ Δ k := (norm_nonneg _).trans hsΔ
    have : L / 6 * ‖s k‖ ^ 3 ≤ c * (εs / 2 * ‖s k‖ ^ 2) := by
      have e : c * (εs / 2 * ‖s k‖ ^ 2) = L / 6 * (Δ k * ‖s k‖ ^ 2) := by
        simp only [c]; field_simp; ring
      rw [e]
      have : ‖s k‖ ^ 3 ≤ Δ k * ‖s k‖ ^ 2 := by
        rw [pow_succ']; exact mul_le_mul_of_nonneg_right hsΔ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hc0 : 0 ≤ c := by positivity
    nlinarith
  have hρ := le_reductionRatio_of_abs_sub_le hpos (habs.trans hcp)
  have h2 : P.η₂ ≤ tr2Ratio f (x k) (s k) := by rw [tr2Ratio_eq]; linarith
  exact ⟨h2, P.η₁_le_η₂.trans h2, (h.run.update hk).le_of_very_successful h2⟩

/-- If $L \ge 1$ and $0 < \epsilon_* < \Delta_0$, then the lower bound (3.4.9) is at most
$\min(\Delta_0, 3 \gamma_1 (1 - \eta_2) \epsilon_* / L)$. -/
private theorem tre_min_ge (hL : 1 ≤ L) (hεs : 0 < εs) (hΔ₀ : εs < P.Δ₀) :
    (1 - P.η₂) * P.γ₁ * εs / L ≤ min P.Δ₀ (P.γ₁ * (3 * (1 - P.η₂) * εs / L)) := by
  have h1η : 0 < 1 - P.η₂ := sub_pos.2 P.η₂_lt_one
  have hγ := P.γ₁_pos
  have hL0 : 0 < L := by linarith
  refine le_min ?_ ?_
  · have : (1 - P.η₂) * P.γ₁ / L ≤ 1 := by
      rw [div_le_one hL0]
      nlinarith [P.γ₁_le_one, P.η₁_pos, P.η₁_le_η₂]
    calc (1 - P.η₂) * P.γ₁ * εs / L = (1 - P.η₂) * P.γ₁ / L * εs := by ring
      _ ≤ 1 * εs := mul_le_mul_of_nonneg_right this hεs.le
      _ ≤ P.Δ₀ := by linarith
  · rw [mul_div_assoc', div_le_div_iff_of_pos_right hL0]
    nlinarith [mul_pos h1η hγ]

/-- **Lemma 3.4.2** of [cartis2022evaluation], second part. Let $f$ satisfy Assumption f.HL with
constant $L_{f,2}$. Every iteration $k$ of a TRε run up to and including termination satisfies
$$\Delta_k \ge \frac{(1 - \eta_2) \gamma_1 \epsilon_*}{L_{f,2}}. \qquad (3.4.9)$$
-/
theorem lemma_3_4_2_delta (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ)
    {k : ℕ} (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) :
    (1 - P.η₂) * P.γ₁ * εs / L ≤ Δ k :=
  (tre_min_ge hf.one_le h.εs_pos h.εs_lt_Δ₀).trans (h.run.delta_ge
    (θ := fun _ => 3 * (1 - P.η₂) * εs / L) hk (fun _ _ => le_rfl)
    (fun _ hj hΔ => (lemma_3_4_2 hf h (fun i hi => hk i (hi.trans_lt hj)) hΔ).1) k le_rfl)

/-- Under Assumption f.HL with constant $L_{f,2}$, if iteration $k$ of a TRε run is before
termination, then the next radius also satisfies (3.4.9): $\Delta_{k+1} \ge (1 - \eta_2)
\gamma_1 \epsilon_* / L_{f,2}$. -/
theorem lemma_3_4_2_delta_succ (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) :
    (1 - P.η₂) * P.γ₁ * εs / L ≤ Δ (k + 1) := by
  have hk' : ∀ j < k + 1, ¬ stopTest f ε₁ ε₂ (x j) := fun j hj => hk j (Nat.lt_succ_iff.1 hj)
  exact (tre_min_ge hf.one_le h.εs_pos h.εs_lt_Δ₀).trans (h.run.delta_succ_ge
    (θ := fun _ => 3 * (1 - P.η₂) * εs / L) hk' (fun _ _ => le_rfl)
    (fun j hj hΔ => (lemma_3_4_2 hf h (fun i hi => hk' i (hi.trans_lt hj)) hΔ).1) k
    k.lt_succ_self)

/-- **Lemma 3.4.3** of [cartis2022evaluation]. Let $f$ satisfy Assumption f.HL with constant
$L_{f,2}$. If iteration $k$ of a TRε run is before termination, is successful, and has an
interior step, $\|s_k\| < \Delta_k$, then
$$\|s_k\| \ge \frac{1}{\sqrt{1 + 2 (L_{f,2} + \theta_1)}} \min\left(\epsilon_*, \frac{\|\nabla
  f(x_{k+1})\|}{\epsilon_*}\right). \qquad (3.4.10)$$

**Typo.** In the proof, before (3.4.12), the quadratic inequality is misprinted as
$\tfrac12 L + \theta_1 \|s\|^2$, and its root is divided by $L_{f,2}$ instead of
$L_{f,2} + \theta_1$. Here (3.4.10) is proved directly from the quadratic inequality $\tfrac12
(L_{f,2} + \theta_1) \|s_k\|^2 + \epsilon_* \|s_k\| \ge \|\nabla f(x_{k+1})\|$.

The last step is `le_of_le_quadratic`. -/
theorem lemma_3_4_3 (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ tr2Ratio f (x k) (s k))
    (hint : ‖s k‖ < Δ k) :
    1 / √(1 + 2 * (L + P.θ₁)) * min εs (‖gradient f (x (k + 1))‖ / εs) ≤ ‖s k‖ := by
  obtain ⟨-, -, hgrad, -⟩ := h.run.step k hk
  have hxk := (h.sub_ge hk hs).1
  have hfx := hf.contDiffAt (x k)
  have h1 := norm_gradient_add_le hf (x := x k) (s := s k)
  have h2 := hgrad hint
  rw [norm_fderiv_treModel hfx] at h2
  have h3 : ‖gradient f (x k) + hessianOperator f (x k) (s k)‖ ≤
      ‖gradient f (x k) + hessianOperator f (x k) (s k) + εs • s k‖ + εs * ‖s k‖ := by
    have := norm_sub_le (gradient f (x k) + hessianOperator f (x k) (s k) + εs • s k) (εs • s k)
    rw [add_sub_cancel_right, norm_smul, Real.norm_of_nonneg h.εs_pos.le] at this
    exact this
  rw [hxk]
  have := le_of_le_quadratic (a := (L + P.θ₁) / 2) (by linarith [hf.nonneg, P.θ₁_pos])
    h.εs_pos (norm_nonneg (s k)) (norm_nonneg (gradient f (x k + s k))) (by linarith)
  rwa [show 1 + 4 * ((L + P.θ₁) / 2) = 1 + 2 * (L + P.θ₁) by ring] at this

/-- The constant (3.4.15)
$$\kappa_{\Delta f} = \tfrac12 \eta_1 \min\left(\frac{\gamma_1^2 (1 - \eta_2)^2}{L^2},
  \frac{1}{1 + 2 (L + \theta_1)}\right).$$
-/
noncomputable def kappaDeltaF (P : TREpsParams) (L : ℝ) : ℝ :=
  P.η₁ / 2 * min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁)))

/-- If $L > 0$, then the constant (3.4.15) is positive: $\kappa_{\Delta f} > 0$. -/
theorem kappaDeltaF_pos (P : TREpsParams) {L : ℝ} (hL : 0 < L) : 0 < kappaDeltaF P L := by
  have := P.η₁_pos; have := P.γ₁_pos; have := sub_pos.2 P.η₂_lt_one; have := P.θ₁_pos
  unfold kappaDeltaF
  have : 0 < min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) :=
    lt_min (by positivity) (by positivity)
  positivity

private theorem mul_min_sq {εs G : ℝ} (hεs : 0 < εs) (hG : 0 ≤ G) :
    εs * min εs (G / εs) ^ 2 = min (εs ^ 3) (G ^ 2 / εs) := by
  have h0 : 0 ≤ G / εs := div_nonneg hG hεs.le
  rcases le_total εs (G / εs) with hle | hle
  · rw [min_eq_left hle, min_eq_left]
    · ring
    · rw [le_div_iff₀ hεs]
      have := pow_le_pow_left₀ hεs.le hle 2
      rw [div_pow, le_div_iff₀ (by positivity)] at this
      nlinarith
  · rw [min_eq_right hle, min_eq_right]
    · field_simp
    · rw [div_le_iff₀ hεs]
      have := pow_le_pow_left₀ h0 hle 2
      rw [div_pow, div_le_iff₀ (by positivity)] at this
      nlinarith

/-- **Lemma 3.4.4** of [cartis2022evaluation]. Let $f$ satisfy Assumption f.HL with constant
$L_{f,2}$, and let iteration $k$ of a TRε run be before termination and successful. If the step
is interior, $\|s_k\| < \Delta_k$, then
$$f(x_k) - f(x_{k+1}) \ge \kappa_{\Delta f} \min\left(\epsilon_*^3, \frac{\|\nabla
  f(x_{k+1})\|^2}{\epsilon_*}\right), \qquad (3.4.13)$$
and if the step is on the boundary, $\|s_k\| = \Delta_k$, then $f(x_k) - f(x_{k+1}) \ge
\kappa_{\Delta f} \epsilon_*^3$ (3.4.14).

**Typo.** In the proof of the source, the case labels (3.4.13) and (3.4.14) are swapped.

The constant $\kappa_{\Delta f}$ is `CartisGouldToint.Chapter03.kappaDeltaF P L`. -/
theorem lemma_3_4_4 (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ tr2Ratio f (x k) (s k)) :
    (‖s k‖ < Δ k → kappaDeltaF P L * min (εs ^ 3) (‖gradient f (x (k + 1))‖ ^ 2 / εs) ≤
      f (x k) - f (x (k + 1))) ∧
    (‖s k‖ = Δ k → kappaDeltaF P L * εs ^ 3 ≤ f (x k) - f (x (k + 1))) := by
  have hεs := h.εs_pos
  have hL := hf.pos
  have hdec := (h.sub_ge hk hs).2
  have hpred := lemma_3_4_1 h hk
  have hη := P.η₁_pos
  have hmin1 : min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) ≤
      P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2 := min_le_left _ _
  have hmin2 : min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) ≤
      1 / (1 + 2 * (L + P.θ₁)) := min_le_right _ _
  have hθ : 0 < 1 + 2 * (L + P.θ₁) := by linarith [P.θ₁_pos]
  constructor
  · intro hint
    set G := ‖gradient f (x (k + 1))‖
    set M := min εs (G / εs)
    have h3 := lemma_3_4_3 hf h hk hs hint
    have hM0 : 0 ≤ M := le_min hεs.le (div_nonneg (norm_nonneg _) hεs.le)
    have hsq : M ^ 2 / (1 + 2 * (L + P.θ₁)) ≤ ‖s k‖ ^ 2 := by
      have h4 := pow_le_pow_left₀ (by positivity) h3 2
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt hθ.le] at h4
      calc M ^ 2 / (1 + 2 * (L + P.θ₁)) = 1 / (1 + 2 * (L + P.θ₁)) * M ^ 2 := by ring
        _ ≤ _ := h4
    rw [← mul_min_sq hεs (norm_nonneg _)]
    unfold kappaDeltaF
    have : P.η₁ / 2 * min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) *
        (εs * M ^ 2) ≤ P.η₁ * (εs / 2 * (M ^ 2 / (1 + 2 * (L + P.θ₁)))) := by
      have hM2 : 0 ≤ εs * M ^ 2 := by positivity
      calc P.η₁ / 2 * min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) *
            (εs * M ^ 2) ≤ P.η₁ / 2 * (1 / (1 + 2 * (L + P.θ₁))) * (εs * M ^ 2) := by gcongr
        _ = P.η₁ * (εs / 2 * (M ^ 2 / (1 + 2 * (L + P.θ₁)))) := by ring
    have h5 : P.η₁ * (εs / 2 * (M ^ 2 / (1 + 2 * (L + P.θ₁)))) ≤
        P.η₁ * (εs / 2 * ‖s k‖ ^ 2) := by gcongr
    nlinarith
  · intro hbd
    have hΔ := lemma_3_4_2_delta hf h (k := k) fun j hj => hk j hj.le
    rw [← hbd] at hΔ
    have hc0 : 0 ≤ (1 - P.η₂) * P.γ₁ * εs / L := by
      have := sub_pos.2 P.η₂_lt_one; have := P.γ₁_pos; positivity
    have h4 := pow_le_pow_left₀ hc0 hΔ 2
    unfold kappaDeltaF
    have e : P.η₁ / 2 * (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) * εs ^ 3 =
        P.η₁ * (εs / 2 * ((1 - P.η₂) * P.γ₁ * εs / L) ^ 2) := by
      field_simp
    calc P.η₁ / 2 * min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) *
          εs ^ 3 ≤ P.η₁ / 2 * (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) * εs ^ 3 := by gcongr
      _ = P.η₁ * (εs / 2 * ((1 - P.η₂) * P.γ₁ * εs / L) ^ 2) := e
      _ ≤ P.η₁ * (εs / 2 * ‖s k‖ ^ 2) := by gcongr
      _ ≤ _ := by nlinarith

end TREpsLemmas

/-! ### Theorems 3.4.5 and 3.4.6 -/

/-- The constant (3.4.20) $\kappa^S_{\mathrm{TR}\epsilon} = \kappa_{\Delta f}^{-1}$. -/
noncomputable def kappaSTREps (P : TREpsParams) (L : ℝ) : ℝ := (kappaDeltaF P L)⁻¹

/-- The constant (3.4.21) $\kappa^A_{\mathrm{TR}\epsilon} = \kappa^S_{\mathrm{TR}\epsilon} (1 + \log
\gamma_3 / |\log \gamma_2|)$. -/
noncomputable def kappaATREps (P : TREpsParams) (L : ℝ) : ℝ :=
  kappaSTREps P L * (1 + Real.log P.γ₃ / |Real.log P.γ₂|)

/-- The constant (3.4.22)
$$\kappa^C_{\mathrm{TR}\epsilon} = \frac{\log \gamma_3 + |\log((1 - \eta_2) \gamma_1 / (\Delta_0
  L))|}{|\log \gamma_2|} + 2.$$
-/
noncomputable def kappaCTREps (P : TREpsParams) (L : ℝ) : ℝ :=
  (Real.log P.γ₃ + |Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))|) / |Real.log P.γ₂| + 2

section TREpsTheorems

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : TREpsParams} {ε₁ : ℝ} {ε₂ : Option ℝ}
  {εs : ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ} {L flow : ℝ}

/-- Under Assumption f.HL, if every iteration $k$ before termination of a TRε run has at most $N$
successful iterations in $[0, k]$, then the run terminates at some $k_\epsilon$ after at most
$(1 + \log \gamma_3 / |\log \gamma_2|) N + (|\log c| + |\log \epsilon_*|) / |\log \gamma_2| + 1$
evaluations of $f$ and at most $N + 1$ evaluations of the derivatives, where
$c = (1 - \eta_2) \gamma_1 / (\Delta_0 L)$. -/
private theorem tre_count (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ)
    {N : ℝ} (hN : 0 ≤ N)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) →
      ((successSet (fun j => P.η₁ ≤ tr2Ratio f (x j) (s j)) k).card : ℝ) ≤ N) :
    ∃ kε, IsFirstHit (fun k => stopTest f ε₁ ε₂ (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * N +
        (|Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))| + |Real.log εs|) / |Real.log P.γ₂| + 1 ∧
      (derivEvalCount (fun k => P.η₁ ≤ tr2Ratio f (x k) (s k)) kε : ℝ) ≤ N + 1 := by
  have hεs := h.εs_pos
  have hL := hf.pos
  have hc : 0 < (1 - P.η₂) * P.γ₁ / (P.Δ₀ * L) := by
    have := sub_pos.2 P.η₂_lt_one; have := P.γ₁_pos; have := P.Δ₀_pos; positivity
  have hlog2 : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  have hA : 0 ≤ 1 + Real.log P.γ₃ / |Real.log P.γ₂| := by
    have := Real.log_nonneg P.one_le_γ₃; positivity
  set B := (|Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))| + |Real.log εs|) / |Real.log P.γ₂|
  have hB : 0 ≤ B := by positivity
  refine exists_isFirstHit_evalCount_le_of_counting hA hN (by positivity) (fun k hk => ?_) hsucc
  have hΔ := lemma_3_4_2_delta_succ hf h hk
  have hmin : 0 < (1 - P.η₂) * P.γ₁ * εs / L := by
    have := sub_pos.2 P.η₂_lt_one; have := P.γ₁_pos; positivity
  have hcount := h.run.succ_count hk hmin hΔ
  have e : (1 - P.η₂) * P.γ₁ * εs / L / P.Δ₀ = (1 - P.η₂) * P.γ₁ / (P.Δ₀ * L) * εs := by
    have := P.Δ₀_pos; field_simp
  have hlog : |Real.log ((1 - P.η₂) * P.γ₁ * εs / L / P.Δ₀)| ≤
      |Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))| + |Real.log εs| := by
    rw [e, Real.log_mul hc.ne' hεs.ne']
    exact abs_add_le _ _
  have : |Real.log ((1 - P.η₂) * P.γ₁ * εs / L / P.Δ₀)| / |Real.log P.γ₂| ≤ B :=
    div_le_div_of_nonneg_right hlog hlog2.le
  linarith

/-- **Theorem 3.4.5** of [cartis2022evaluation]. Let $f$ satisfy Assumption f.Bb with lower bound
$f_{\mathrm{low}}$ and Assumption f.HL with constant $L_{f,2}$. Every TRε run with
$\epsilon_* = \sqrt{\epsilon_1}$ and $\epsilon_2 = +\infty$ terminates at a first iteration
$k_\epsilon$ with $\|\nabla f(x_{k_\epsilon})\| \le \epsilon_1$. It needs at most
$$\kappa^A \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon_1^{3/2}} + \kappa^B |\log \epsilon_1| +
  \kappa^C$$
evaluations of $f$ and at most
$$\kappa^S \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon_1^{3/2}} + 2$$
evaluations of $\nabla f$ and $\nabla^2 f$, where $\kappa^S = \kappa_{\Delta f}^{-1}$ (3.4.20),
$\kappa^A = \kappa^S (1 + \log \gamma_3 / |\log \gamma_2|)$ (3.4.21),
$\kappa^B = 1 / (2 |\log \gamma_2|)$ and $\kappa^C$ is (3.4.22).

The run predicate gives $\epsilon_1 \in (0, 1]$. The number of evaluations of $f$ is
`Optimization.funEvalCount`, and the number of evaluations of the derivatives is
`Optimization.derivEvalCount` of the successful iterations. -/
theorem theorem_3_4_5 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L)
    (h : algorithm_3_4_1 f P ε₁ none (√ε₁) x s Δ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaATREps P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) +
        1 / (2 * |Real.log P.γ₂|) * |Real.log ε₁| + kappaCTREps P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ tr2Ratio f (x k) (s k)) kε : ℝ) ≤
        kappaSTREps P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) + 2 := by
  have hε := h.ε₁_pos
  set r := √ε₁ with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hε
  have hr2 : r ^ 2 = ε₁ := Real.sq_sqrt hε.le
  have hr3 : ε₁ ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  have hκ := kappaDeltaF_pos P hf.pos
  set X := (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ)
  have hX : 0 ≤ X := div_nonneg (sub_nonneg.2 (hb _)) (by positivity)
  set N := kappaSTREps P L * X
  have hN : 0 ≤ N := mul_nonneg (inv_nonneg.2 hκ.le) hX
  have hsucc : ∀ k, (∀ j ≤ k + 1, ¬ stopTest f ε₁ none (x j)) →
      ((successSet (fun j => P.η₁ ≤ tr2Ratio f (x j) (s j)) k).card : ℝ) ≤ N := by
    intro k hk
    have hc : 0 < kappaDeltaF P L * r ^ 3 := by positivity
    have := card_successSet_le_div_of_decrease (φ := fun j => f (x j)) hc
      (fun j hj hs => by
        rw [h.run.eq_of_not_succ (fun i hi => hk i (hi.trans (hj.trans k.le_succ)))
          (not_le.1 hs)])
      (fun j hj hs => by
        have hj' : ∀ i ≤ j, ¬ stopTest f ε₁ none (x i) := fun i hi =>
          hk i (hi.trans (hj.trans k.le_succ))
        have hG : ε₁ < ‖gradient f (x (j + 1))‖ := by
          have := hk (j + 1) (Nat.succ_le_succ hj)
          rwa [stopTest_none, not_le] at this
        have hmin : r ^ 3 ≤ min (r ^ 3) (‖gradient f (x (j + 1))‖ ^ 2 / r) := by
          refine le_min le_rfl ?_
          rw [le_div_iff₀ hr0]
          have : (r ^ 2) ^ 2 ≤ ‖gradient f (x (j + 1))‖ ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by rw [hr2]; exact hG.le) 2
          nlinarith
        obtain ⟨h1, h2⟩ := lemma_3_4_4 hf h hj' hs
        obtain ⟨hsΔ, -⟩ := h.run.step j hj'
        rcases lt_or_eq_of_le hsΔ with hlt | heq
        · exact (mul_le_mul_of_nonneg_left hmin hκ.le).trans (h1 hlt)
        · exact h2 heq)
      (hb (x (k + 1)))
    refine this.trans_eq ?_
    simp only [N, X, kappaSTREps, hr3]
    field_simp
  obtain ⟨kε, hk, hF, hD⟩ := tre_count hf h (by linarith)
    (card_successSet_le_add_one_of_forall hN hsucc)
  simp only [stopTest_none] at hk
  have hNe : N = kappaSTREps P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) := by
    simp only [N, X]; ring
  refine ⟨kε, hk, ?_, by linarith⟩
  have hlogr : |Real.log r| = |Real.log ε₁| / 2 := by
    rw [hr, Real.log_sqrt hε.le, abs_div, abs_two]
  have hlog2 : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  rw [hlogr] at hF
  have e1 : (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (N + 1) +
      (|Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))| + |Real.log ε₁| / 2) / |Real.log P.γ₂| + 1 =
      kappaATREps P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) +
        1 / (2 * |Real.log P.γ₂|) * |Real.log ε₁| + kappaCTREps P L := by
    simp only [N, X, kappaATREps, kappaCTREps]
    field_simp
    ring
  linarith

/-- Between a successful iteration $j$ of a TRε run and the next successful iteration $j'$, the
iterate stays equal to $x_{j+1}$. -/
private theorem tre_x_eq (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {j j' : ℕ}
    (hstop : ∀ i < j', ¬ stopTest f ε₁ ε₂ (x i))
    (hnone : ∀ i, j < i → i < j' → ¬ P.η₁ ≤ tr2Ratio f (x i) (s i)) :
    ∀ m, j + 1 ≤ m → m ≤ j' → x m = x (j + 1) := by
  intro m hm hmj
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [h.run.eq_of_not_succ (fun i hi => hstop i (by omega)) (not_le.1 (hnone m (by omega)
      (by omega))), ih (by omega)]

/-- **Theorem 3.4.6** of [cartis2022evaluation]. Let $f$ satisfy Assumption f.Bb with lower bound
$f_{\mathrm{low}}$ and Assumption f.HL with constant $L_{f,2}$. Every TRε run with
$\epsilon_1, \epsilon_2 \in (0, 1]$ and $\epsilon_* = \epsilon_2$ terminates at a first
iteration $k_\epsilon$ with $\|\nabla f(x_{k_\epsilon})\| \le \epsilon_1$ and
$\lambda_{\min}[\nabla^2 f(x_{k_\epsilon})] \ge -\epsilon_2$. It needs at most
$$2 \kappa^A \frac{f(x_0) - f_{\mathrm{low}}}{\min(\epsilon_1^2 \epsilon_2^{-1},
  \epsilon_2^3)} + \kappa^D |\log \epsilon_2| + \kappa^C$$
evaluations of $f$ and at most
$$2 \kappa^S \frac{f(x_0) - f_{\mathrm{low}}}{\min(\epsilon_1^2 \epsilon_2^{-1},
  \epsilon_2^3)} + 2$$
evaluations of $\nabla f$ and $\nabla^2 f$, where $\kappa^S$, $\kappa^A$ and $\kappa^C$ are as
in Theorem 3.4.5 and $\kappa^D = 1 / |\log \gamma_2|$.

**Correction.** The source prints the bounds without the factor $2$ on the leading terms, and
with $+1$ in place of $+2$ for the derivative evaluations. Its proof claims, before (3.4.26),
that $x_{j+1}$ is on the trust-region boundary when $\lambda_{\min}[\nabla^2 f(x_{j+1})] <
-\epsilon_2$. This is wrong: the boundary step is taken at the next successful iteration from
$x_{j+1}$. So a successful iteration without the required decrease is followed by a successful
iteration with decrease at least $\kappa_{\Delta f} \epsilon_2^3$, and this gives the factor
$2$.

The tolerance $\epsilon_2$ is `some e`. The counting step is
`Optimization.card_successSet_le_two_mul_add_one`. -/
theorem theorem_3_4_6 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L) {e : ℝ}
    (h : algorithm_3_4_1 f P ε₁ (some e) e x s Δ) :
    ∃ kε, IsFirstHit (fun k => stopTest f ε₁ (some e) (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        2 * kappaATREps P L * (f (x 0) - flow) / min (ε₁ ^ 2 / e) (e ^ 3) +
          1 / |Real.log P.γ₂| * |Real.log e| + kappaCTREps P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ tr2Ratio f (x k) (s k)) kε : ℝ) ≤
        2 * kappaSTREps P L * (f (x 0) - flow) / min (ε₁ ^ 2 / e) (e ^ 3) + 2 := by
  have hε := h.ε₁_pos
  have he := h.εs_pos
  have hκ := kappaDeltaF_pos P hf.pos
  set m := min (ε₁ ^ 2 / e) (e ^ 3)
  have hm : 0 < m := lt_min (by positivity) (by positivity)
  set X := (f (x 0) - flow) / m
  have hX : 0 ≤ X := div_nonneg (sub_nonneg.2 (hb _)) hm.le
  set N := kappaSTREps P L * X
  have hN : 0 ≤ N := mul_nonneg (inv_nonneg.2 hκ.le) hX
  set succ := fun j => P.η₁ ≤ tr2Ratio f (x j) (s j)
  have hsucc : ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ (some e) (x j)) →
      ((successSet succ k).card : ℝ) ≤ 2 * N + 1 := by
    intro k hk
    set good := fun j => succ j ∧ (‖s j‖ = Δ j ∨ ε₁ < ‖gradient f (x (j + 1))‖)
    have hcard := card_successSet_le_two_mul_add_one (succ := succ) (good := good) (K := k)
      (fun j _ hg => hg.1) (fun j j' hjj' hj'k hsj hgj hsj' hnone => by
        refine ⟨hsj', Or.inl ?_⟩
        have hstop : ∀ i < j', ¬ stopTest f ε₁ (some e) (x i) := fun i hi => hk i (by omega)
        have hx := tre_x_eq h hstop hnone j' (by omega) le_rfl
        have hg : ‖gradient f (x (j + 1))‖ ≤ ε₁ := by
          by_contra hlt
          exact hgj ⟨hsj, Or.inr (not_le.1 hlt)⟩
        have hnot := hk j' hj'k
        rw [not_stopTest_some, hx] at hnot
        have hlam := hnot.resolve_left (not_lt.2 hg)
        rw [← hx] at hlam
        exact (h.run.step j' fun i hi => hk i (hi.trans hj'k)).2.2.2 e rfl hlam) k le_rfl
    have hc : 0 < kappaDeltaF P L * m := by positivity
    have hG := card_le_div_of_decrease (φ := fun j => f (x j)) (T := successSet good k) hc
      successSet_subset_range (fun j hj => h.le fun i hi => hk i (hi.trans hj))
      (fun j hj => by
        rw [mem_successSet] at hj
        obtain ⟨hjk, hsj, hgj⟩ := hj
        have hj' : ∀ i ≤ j, ¬ stopTest f ε₁ (some e) (x i) := fun i hi => hk i (hi.trans hjk)
        obtain ⟨h1, h2⟩ := lemma_3_4_4 hf h hj' hsj
        obtain ⟨hsΔ, -⟩ := h.run.step j hj'
        have hme : m ≤ e ^ 3 := min_le_right _ _
        rcases lt_or_eq_of_le hsΔ with hlt | heq
        · rcases hgj with heq | hgr
          · exact absurd heq hlt.ne
          · refine (mul_le_mul_of_nonneg_left (le_min hme ?_) hκ.le).trans (h1 hlt)
            refine (min_le_left _ _).trans ?_
            exact div_le_div_of_nonneg_right
              (pow_le_pow_left₀ hε.le hgr.le 2) he.le
        · exact (mul_le_mul_of_nonneg_left hme hκ.le).trans (h2 heq))
      (hb (x (k + 1)))
    have : ((successSet succ k).card : ℝ) ≤ 2 * (successSet good k).card + 1 := by
      exact_mod_cast hcard
    have hGN : ((successSet good k).card : ℝ) ≤ N := by
      refine hG.trans_eq ?_
      simp only [N, X, kappaSTREps]
      field_simp
    linarith
  obtain ⟨kε, hk, hF, hD⟩ := tre_count hf h (by linarith) hsucc
  have hNe : N = kappaSTREps P L * (f (x 0) - flow) / m := by simp only [N, X]; ring
  refine ⟨kε, hk, ?_, hD.trans_eq (by rw [hNe]; ring)⟩
  have e1 : (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (2 * N + 1) +
      (|Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))| + |Real.log e|) / |Real.log P.γ₂| + 1 =
      2 * kappaATREps P L * (f (x 0) - flow) / m + 1 / |Real.log P.γ₂| * |Real.log e| +
        kappaCTREps P L := by
    have hlog2 : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
    simp only [N, X, kappaATREps, kappaCTREps]
    field_simp
    ring
  linarith

end TREpsTheorems

/-! ### The iRN framework -/


/-- **Algorithm 3.4.2** of [cartis2022evaluation], Step 0. The constants of iRN consist of
regularization bounds $0 < \sigma_{\min} \le \sigma_{\max}$, an acceptance threshold
$0 < \eta < 1$, increase factors $1 < \gamma_1 \le \gamma_2$, the constants
$\kappa_1, \kappa_2, \kappa_3, \kappa_4 > 0$ of the step conditions (3.4.29)–(3.4.32), and an
initial upper bound $\sigma^U_0 \in [\sigma_{\min}, \sigma_{\max}]$. -/
structure IRNParams where
  /-- The lower regularization bound $\sigma_{\min}$. -/
  σmin : ℝ
  /-- The upper regularization bound $\sigma_{\max}$. -/
  σmax : ℝ
  /-- The acceptance threshold $\eta$. -/
  η : ℝ
  /-- The lower increase factor $\gamma_1$. -/
  γ₁ : ℝ
  /-- The upper increase factor $\gamma_2$. -/
  γ₂ : ℝ
  /-- The constant $\kappa_1$ of the first inequality of (3.4.29). -/
  κ₁ : ℝ
  /-- The constant $\kappa_2$ of the second inequality of (3.4.29). -/
  κ₂ : ℝ
  /-- The constant $\kappa_3$ of (3.4.30). -/
  κ₃ : ℝ
  /-- The constant $\kappa_4$ of (3.4.32). -/
  κ₄ : ℝ
  /-- The initial upper regularization bound $\sigma^U_0$. -/
  σU₀ : ℝ
  /-- The lower bound is positive: $\sigma_{\min} > 0$. -/
  σmin_pos : 0 < σmin
  /-- The bounds are ordered: $\sigma_{\min} \le \sigma_{\max}$. -/
  σmin_le_σmax : σmin ≤ σmax
  /-- The threshold is positive: $\eta > 0$. -/
  η_pos : 0 < η
  /-- The threshold is less than one: $\eta < 1$. -/
  η_lt_one : η < 1
  /-- The lower increase factor exceeds one: $\gamma_1 > 1$. -/
  one_lt_γ₁ : 1 < γ₁
  /-- The increase factors are ordered: $\gamma_1 \le \gamma_2$. -/
  γ₁_le_γ₂ : γ₁ ≤ γ₂
  /-- The constant $\kappa_1$ is positive. -/
  κ₁_pos : 0 < κ₁
  /-- The constant $\kappa_2$ is positive. -/
  κ₂_pos : 0 < κ₂
  /-- The constant $\kappa_3$ is positive. -/
  κ₃_pos : 0 < κ₃
  /-- The constant $\kappa_4$ is positive. -/
  κ₄_pos : 0 < κ₄
  /-- The initial upper bound is at least the lower bound: $\sigma_{\min} \le \sigma^U_0$. -/
  σmin_le_σU₀ : σmin ≤ σU₀
  /-- The initial upper bound is at most the upper bound: $\sigma^U_0 \le \sigma_{\max}$. -/
  σU₀_le_σmax : σU₀ ≤ σmax

/-- The gradient (3.4.31) of the iRN model (3.4.27) at the step $s$ with multiplier $\lambda$:
$g(s) = \nabla f(x) + (\nabla^2 f(x) + \lambda I) s$. -/
noncomputable def irnGrad (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (lam : ℝ) (s : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  gradient f x + hessianOperator f x s + lam • s

/-- Step 2 of Algorithm 3.4.2 at the iterate $x$, with bounds $\sigma^L, \sigma^U$, multiplier
$\lambda$ and a subspace $V$, the range of a matrix $Q$ with orthonormal columns. Let $g(s) =
\nabla f(x) + (\nabla^2 f(x) + \lambda I) s$. A step $s$ is admissible if
$$\sigma^L \|s\| \le \lambda \le \sigma^U \|s\|, \qquad (3.4.28)$$
the slope condition (3.4.29)
$$\langle s, g(s) \rangle \le \min\left(\kappa_1 \|s\|^2, \tfrac12 \langle s, (\nabla^2 f(x) +
  \lambda I) s \rangle + \tfrac12 \kappa_2 \|s\|^3\right)$$
holds, the gradient bound (3.4.30) $\|g(s)\| \le \lambda \|s\| + \kappa_3 \|s\|^2$ holds, and,
if $\epsilon_2 < \infty$, the curvature condition (3.4.32) $\lambda_{\min}[Q^T (\nabla^2 f(x) +
\lambda I) Q] \ge -\kappa_4 \|s\|$ holds.

The gradient $g(s)$ is `CartisGouldToint.Chapter03.irnGrad f x lam s`. The number
$\lambda_{\min}[Q^T (\nabla^2 f(x) + \lambda I) Q]$ is `minCurvatureOn` of the bilinear form
`iteratedFDeriv ℝ 2 f x + lam • innerForm` on `V`. -/
def irnStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : IRNParams) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (σL σU lam : ℝ) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  σL * ‖s‖ ≤ lam ∧ lam ≤ σU * ‖s‖ ∧
    ⟪s, irnGrad f x lam s⟫ ≤ min (P.κ₁ * ‖s‖ ^ 2)
      (1 / 2 * ⟪s, hessianOperator f x s + lam • s⟫ + 1 / 2 * P.κ₂ * ‖s‖ ^ 3) ∧
    ‖irnGrad f x lam s‖ ≤ lam * ‖s‖ + P.κ₃ * ‖s‖ ^ 2 ∧
    (ε₂ ≠ none → -(P.κ₄ * ‖s‖) ≤ minCurvatureOn (iteratedFDeriv ℝ 2 f x + lam • innerForm) V)

/-- The ratio (3.4.35) of iRN: $\rho = (f(x) - f(x + s)) / \|s\|^3$. For $s = 0$ the ratio is $0$,
by the Lean convention for division by zero. -/
noncomputable def irnRatio (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : EuclideanSpace ℝ (Fin n)) :
    ℝ :=
  reductionRatio f x s (‖s‖ ^ 3)

/-- The termination test of iRN at $x$ with a subspace $V$, the range of a matrix $Q$ with
orthonormal columns: $\|\nabla f(x)\| \le \epsilon_1$ and, if $\epsilon_2 < \infty$,
$\lambda_{\min}[Q^T \nabla^2 f(x) Q] \ge -\epsilon_2$ (3.4.34).

The strict-local-minimizer test of Step 3 implies this test. -/
def irnTest (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε₁ : ℝ) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop :=
  ‖gradient f x‖ ≤ ε₁ ∧ ∀ e ∈ ε₂, -e ≤ minCurvatureOn (iteratedFDeriv ℝ 2 f x) V

/-- With $Q = I$, that is, with $V$ the whole space, the iRN test is the TR2 and AR2 test (3.2.9),
`CartisGouldToint.Chapter03.stopTest`. -/
@[simp]
theorem irnTest_top {f : EuclideanSpace ℝ (Fin n) → ℝ} {ε₁ : ℝ} {ε₂ : Option ℝ}
    {x : EuclideanSpace ℝ (Fin n)} : irnTest f ε₁ ε₂ x ⊤ ↔ stopTest f ε₁ ε₂ x := by
  rw [irnTest, stopTest_def, minCurvatureOn_top]
  rfl

/-- Step 5 of Algorithm 3.4.2: the update of the bounds $\sigma^L, \sigma^U$ to
$\sigma^{L\prime}, \sigma^{U\prime}$ for the ratio $\rho$, the multiplier $\lambda$ and the step
$s$. If $\rho \ge \eta$, then $\sigma^{L\prime} = 0$ and $\sigma^{U\prime} = \sigma^U$. If
$\rho < \eta$ and $\lambda < \sigma_{\min} \|s\|$, then $\sigma_{\min} \le \sigma^{L\prime} \le
\sigma^{U\prime} \le \sigma_{\max}$. If $\rho < \eta$ and $\lambda \ge \sigma_{\min} \|s\|$,
then $\sigma^{L\prime} = \gamma_1 \lambda / \|s\|$ and
$\sigma^{U\prime} = \gamma_2 \lambda / \|s\|$. -/
def irnUpdate (P : IRNParams) (ρ lam : ℝ) (s : EuclideanSpace ℝ (Fin n)) (σU σL' σU' : ℝ) :
    Prop :=
  (P.η ≤ ρ → σL' = 0 ∧ σU' = σU) ∧
    (ρ < P.η → lam < P.σmin * ‖s‖ →
      P.σmin ≤ σL' ∧ σL' ≤ P.σmax ∧ σL' ≤ σU' ∧ σU' ≤ P.σmax) ∧
    (ρ < P.η → P.σmin * ‖s‖ ≤ lam → σL' = P.γ₁ * (lam / ‖s‖) ∧ σU' = P.γ₂ * (lam / ‖s‖))

/-- **Algorithm 3.4.2** of [cartis2022evaluation] (iRN). Let $f : \mathbb{R}^n \to \mathbb{R}$, let
$\epsilon_1 \in (0, 1]$, and let $\epsilon_2 > 0$ or $\epsilon_2 = +\infty$. Sequences of
iterates $x_k$, steps $s_k$, multipliers $\lambda_k$, bounds $\sigma^L_k, \sigma^U_k$ and
subspaces $V_k$ form an **iRN run** if $\sigma^L_0 = 0$, the initial upper bound is the constant
$\sigma^U_0$, and the following holds.

* Step 2 (`CartisGouldToint.Chapter03.irnStep`) holds at every iteration $k$ such that the
  termination test fails at all $j < k$ and, if $\epsilon_2 = +\infty$,
  $\|\nabla f(x_k)\| > \epsilon_1$.
* At every iteration $k$ before termination, Step 4 sets $x_{k+1} = x_k + s_k$ if the ratio
  (3.4.35) satisfies $\rho_k \ge \eta$, and $x_{k+1} = x_k$ otherwise.
* At every iteration $k$ before termination, Step 5 (`CartisGouldToint.Chapter03.irnUpdate`)
  gives $\sigma^L_{k+1}$ and $\sigma^U_{k+1}$.

The run terminates at the first iteration $k$ at which the test of Steps 1 and 3
(`CartisGouldToint.Chapter03.irnTest`) holds for $x_k$ and $V_k$.

The subspace $V_k$ is the range of the matrix $Q_k$ with orthonormal columns of (3.4.32), and
$V_k = \top$ is $Q_k = I$. The first-order test of Step 1 is active only if
$\epsilon_2 = +\infty$. When $\epsilon_2 < \infty$, the test depends on $Q_k$, which Step 2
computes, so Step 2 is required also at the iteration where the run terminates. The tolerance
$\epsilon_2 = +\infty$ is `none`. -/
structure algorithm_3_4_2 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : IRNParams) (ε₁ : ℝ)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (lam σL σU : ℕ → ℝ)
    (V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop where
  /-- The first-order tolerance is positive: $\epsilon_1 > 0$. -/
  ε₁_pos : 0 < ε₁
  /-- The first-order tolerance is at most one: $\epsilon_1 \le 1$. -/
  ε₁_le_one : ε₁ ≤ 1
  /-- If $\epsilon_2$ is finite, then $\epsilon_2 > 0$. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- The initial lower bound is $\sigma^L_0 = 0$. -/
  sigmaL_zero : σL 0 = 0
  /-- The initial upper bound is the constant $\sigma^U_0$. -/
  sigmaU_zero : σU 0 = P.σU₀
  /-- Step 2 holds at every iteration $k$ at which the test failed at all $j < k$, unless
  $\epsilon_2 = +\infty$ and $\|\nabla f(x_k)\| \le \epsilon_1$. -/
  step : ∀ k, (∀ j < k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) →
    (ε₂ = none → ¬ ‖gradient f (x k)‖ ≤ ε₁) →
    irnStep f P ε₂ (x k) (σL k) (σU k) (lam k) (V k) (s k)
  /-- Step 4: before termination, the iterate moves to $x_k + s_k$ if $\rho_k \ge \eta$ and stays at
  $x_k$ otherwise. -/
  accept : UntilHit (fun k => irnTest f ε₁ ε₂ (x k) (V k)) fun k =>
    x (k + 1) = if P.η ≤ irnRatio f (x k) (s k) then x k + s k else x k
  /-- Step 5: before termination, the bounds are updated by `CartisGouldToint.Chapter03.irnUpdate`.
  -/
  update : UntilHit (fun k => irnTest f ε₁ ε₂ (x k) (V k)) fun k =>
    irnUpdate P (irnRatio f (x k) (s k)) (lam k) (s k) (σU k) (σL (k + 1)) (σU (k + 1))

namespace algorithm_3_4_2

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : IRNParams} {ε₁ : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {lam σL σU : ℕ → ℝ}
  {V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))}

/-- Step 2 holds at every iteration of an iRN run before termination. -/
theorem step_of_le (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) :
    irnStep f P ε₂ (x k) (σL k) (σU k) (lam k) (V k) (s k) :=
  h.step k (fun j hj => hk j hj.le) fun he hg => hk k le_rfl ⟨hg, by simp [he]⟩

/-- Before termination of an iRN run the step is nonzero, because a zero step would satisfy the
termination test. -/
theorem s_ne_zero (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) : s k ≠ 0 := by
  intro hs0
  obtain ⟨h1, h2, -, h4, h5⟩ := h.step_of_le hk
  rw [hs0, norm_zero, mul_zero] at h1 h2
  have hl : lam k = 0 := le_antisymm h2 h1
  have hg : ‖gradient f (x k)‖ ≤ 0 := by simpa [irnGrad, hs0, hl] using h4
  refine hk k le_rfl ⟨hg.trans h.ε₁_pos.le, fun e he => ?_⟩
  have := h5 (by rintro rfl; simp at he)
  rw [hs0, hl, norm_zero, mul_zero, neg_zero, zero_smul, add_zero] at this
  linarith [h.ε₂_pos e he]

/-- Along an iRN run, $\sigma^L_k \ge 0$ at every iteration $k$ up to and including termination. -/
theorem sigmaL_nonneg (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) :
    ∀ k, (∀ j < k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) → 0 ≤ σL k := by
  intro k
  induction k with
  | zero => intro _; rw [h.sigmaL_zero]
  | succ k ih =>
    intro hk
    have hk' : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j) := fun j hj => hk j (Nat.lt_succ_of_le hj)
    obtain ⟨u1, u2, u3⟩ := h.update k hk'
    by_cases hs : P.η ≤ irnRatio f (x k) (s k)
    · rw [(u1 hs).1]
    · have hs := not_le.1 hs
      by_cases hl : lam k < P.σmin * ‖s k‖
      · exact P.σmin_pos.le.trans (u2 hs hl).1
      · rw [(u3 hs (not_lt.1 hl)).1]
        have : 0 ≤ lam k := (mul_nonneg P.σmin_pos.le (norm_nonneg _)).trans (not_lt.1 hl)
        have := P.one_lt_γ₁
        positivity

/-- A successful iteration ($\rho_k \ge \eta$) of an iRN run before termination moves to the trial
point: $x_{k+1} = x_k + s_k$. -/
theorem eq_add (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) (hs : P.η ≤ irnRatio f (x k) (s k)) :
    x (k + 1) = x k + s k := by
  rw [h.accept k hk, ite_eq_left hs]

/-- An unsuccessful iteration ($\rho_k < \eta$) of an iRN run before termination keeps the iterate:
$x_{k+1} = x_k$. -/
theorem eq_self (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) (hs : irnRatio f (x k) (s k) < P.η) :
    x (k + 1) = x k := by
  rw [h.accept k hk, ite_eq_right (not_le.2 hs)]

/-- On a successful iteration $k$ of an iRN run before termination,
$f(x_k) - f(x_{k+1}) \ge \eta \|s_k\|^3$. -/
theorem sub_ge (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) (hs : P.η ≤ irnRatio f (x k) (s k)) :
    P.η * ‖s k‖ ^ 3 ≤ f (x k) - f (x (k + 1)) := by
  rw [h.eq_add hk hs]
  exact sub_le_of_le_reductionRatio (by have := h.s_ne_zero hk; positivity) hs

/-- Before termination of an iRN run, the objective does not increase: $f(x_{k+1}) \le f(x_k)$. -/
theorem le (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) : f (x (k + 1)) ≤ f (x k) := by
  by_cases hs : P.η ≤ irnRatio f (x k) (s k)
  · have := h.sub_ge hk hs
    have : 0 ≤ P.η * ‖s k‖ ^ 3 := mul_nonneg P.η_pos.le (by positivity)
    linarith
  · rw [h.eq_self hk (not_le.1 hs)]

end algorithm_3_4_2

/-! ### Lemmas 3.4.7–3.4.10 -/

section IRNLemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : IRNParams} {ε₁ : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {lam σL σU : ℕ → ℝ}
  {V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))} {L : ℝ}

/-- The one-step form of Lemma 3.4.7. Let $f$ satisfy Assumption f.HL with constant $L_{f,2}$. Let
$s \ne 0$ and $\lambda$ satisfy the second inequality of (3.4.29) at $y$,
$$\langle s, g(s) \rangle \le \tfrac12 \langle s, (\nabla^2 f(y) + \lambda I) s \rangle +
  \tfrac12 \kappa_2 \|s\|^3, \qquad g(s) = \nabla f(y) + (\nabla^2 f(y) + \lambda I) s,$$
and let $\lambda \ge (2 \eta + \kappa_2 + L_{f,2}) \|s\|$ (3.4.37). Then the ratio (3.4.35)
satisfies $\rho \ge \eta$. -/
theorem lemma_3_4_7_step (hf : AssumptionHL f L) {y d : EuclideanSpace ℝ (Fin n)} {l : ℝ}
    (hd : d ≠ 0)
    (h29 : ⟪d, irnGrad f y l d⟫ ≤ 1 / 2 * ⟪d, hessianOperator f y d + l • d⟫ +
      1 / 2 * P.κ₂ * ‖d‖ ^ 3)
    (hl : (2 * P.η + P.κ₂ + L) * ‖d‖ ≤ l) : P.η ≤ irnRatio f y d := by
  have ht : 0 < ‖d‖ := norm_pos_iff.2 hd
  have habs := abs_sub_taylorPolynomial_le_of_lipschitz convex_univ (fun z _ => hf.contDiffAt z)
    hf.iteratedFDerivLipschitzOn (mem_univ y) (mem_univ (y + d))
  rw [taylorPolynomial_two_eq_quadModel (hf.contDiffAt y), quadModel_def,
    show ((Nat.factorial (2 + 1 : ℕ) : ℕ) : ℝ) = 6 by norm_num [Nat.factorial],
    show (2 + 1 : ℕ) = 3 from rfl] at habs
  have hlow := le_abs_self (f (y + d) - (f y + (⟪gradient f y, d⟫ +
    1 / 2 * ⟪d, hessianOperator f y d⟫)))
  rw [irnGrad, inner_add_right, inner_add_right, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm] at h29
  rw [irnRatio, le_reductionRatio_iff (by positivity)]
  have hL := hf.nonneg
  have : (2 * P.η + P.κ₂ + L) * ‖d‖ * ‖d‖ ^ 2 ≤ l * ‖d‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hl (sq_nonneg _)
  nlinarith [pow_pos ht 3]

/-- **Lemma 3.4.7** of [cartis2022evaluation]. Let $f$ satisfy Assumption f.HL with constant
$L_{f,2}$. If iteration $k$ of an iRN run is before termination and
$$\lambda_k \ge (2 \eta + \kappa_2 + L_{f,2}) \|s_k\|, \qquad (3.4.37)$$
then $\rho_k \ge \eta$, so that the iteration is successful.

The proof uses the Taylor bound (A.19), $|f(x + s) - T_{f,2}(x, s)| \le \tfrac16 L_{f,2}
\|s\|^3$; the bound $\tfrac12 L_{f,2} \|s\|^3$ of the source is weaker. The proof specializes
`CartisGouldToint.Chapter03.lemma_3_4_7_step`. -/
theorem lemma_3_4_7 (hf : AssumptionHL f L) (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j))
    (hl : (2 * P.η + P.κ₂ + L) * ‖s k‖ ≤ lam k) : P.η ≤ irnRatio f (x k) (s k) :=
  lemma_3_4_7_step hf (h.s_ne_zero hk) ((h.step_of_le hk).2.2.1.trans (min_le_right _ _)) hl

/-- The bound (3.4.38) $\sigma^U_{\max} = \max(\sigma_{\max}, \gamma_2 (2 \eta + \kappa_2 +
L_{f,2}))$. -/
noncomputable def sigmaUMax (P : IRNParams) (L : ℝ) : ℝ :=
  max P.σmax (P.γ₂ * (2 * P.η + P.κ₂ + L))

/-- The lower regularization bound is at most the bound (3.4.38):
$\sigma_{\min} \le \sigma^U_{\max}$. -/
theorem σmin_le_sigmaUMax (P : IRNParams) (L : ℝ) : P.σmin ≤ sigmaUMax P L :=
  P.σmin_le_σmax.trans (le_max_left _ _)

/-- The bound (3.4.38) is positive: $\sigma^U_{\max} > 0$. -/
theorem sigmaUMax_pos (P : IRNParams) (L : ℝ) : 0 < sigmaUMax P L :=
  P.σmin_pos.trans_le (σmin_le_sigmaUMax P L)

/-- **Lemma 3.4.8** of [cartis2022evaluation]. Let $f$ satisfy Assumption f.HL with constant
$L_{f,2}$. Every iteration $k$ of an iRN run up to and including termination satisfies
$\sigma^U_k \le \sigma^U_{\max}$ (3.4.38). -/
theorem lemma_3_4_8 (hf : AssumptionHL f L) (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) :
    ∀ k, (∀ j < k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) → σU k ≤ sigmaUMax P L := by
  intro k
  induction k with
  | zero => intro _; rw [h.sigmaU_zero]; exact P.σU₀_le_σmax.trans (le_max_left _ _)
  | succ k ih =>
    intro hk
    have hk' : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j) := fun j hj => hk j (Nat.lt_succ_of_le hj)
    obtain ⟨u1, u2, u3⟩ := h.update k hk'
    by_cases hs : P.η ≤ irnRatio f (x k) (s k)
    · rw [(u1 hs).2]; exact ih fun j hj => hk' j hj.le
    · have hs := not_le.1 hs
      by_cases hl : lam k < P.σmin * ‖s k‖
      · exact (u2 hs hl).2.2.2.trans (le_max_left _ _)
      · rw [(u3 hs (not_lt.1 hl)).2]
        have hpos : 0 < ‖s k‖ := norm_pos_iff.2 (h.s_ne_zero hk')
        have hlt : lam k < (2 * P.η + P.κ₂ + L) * ‖s k‖ := by
          by_contra hge
          exact absurd (lemma_3_4_7 hf h hk' (not_lt.1 hge)) (not_le.2 hs)
        refine le_trans ?_ (le_max_right _ _)
        have hγ : 0 < P.γ₂ := by linarith [P.one_lt_γ₁, P.γ₁_le_γ₂]
        refine mul_le_mul_of_nonneg_left ?_ hγ.le
        rw [div_le_iff₀ hpos]; exact hlt.le

/-- **Lemma 3.4.9** of [cartis2022evaluation], first part. Let $f$ satisfy Assumption f.HL with
constant $L_{f,2}$. If iteration $k$ of an iRN run is before termination and successful, then
$$\|s_k\|^2 \ge \frac{2}{L_{f,2} + 4 \sigma^U_{\max} + 2 \kappa_3} \|\nabla f(x_{k+1})\|. \qquad
  (3.4.39)$$
-/
theorem lemma_3_4_9 (hf : AssumptionHL f L) (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) (hs : P.η ≤ irnRatio f (x k) (s k)) :
    2 / (L + 4 * sigmaUMax P L + 2 * P.κ₃) * ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ ^ 2 := by
  obtain ⟨h1, h2, -, h4, -⟩ := h.step_of_le hk
  have hσ := lemma_3_4_8 hf h k fun j hj => hk j hj.le
  rw [h.eq_add hk hs]
  have hG := norm_gradient_add_le hf (x := x k) (s := s k)
  set t := ‖s k‖
  have hg : ‖gradient f (x k) + hessianOperator f (x k) (s k)‖ ≤
      ‖irnGrad f (x k) (lam k) (s k)‖ + lam k * t := by
    have := norm_sub_le (irnGrad f (x k) (lam k) (s k)) (lam k • s k)
    rw [irnGrad, add_sub_cancel_right, norm_smul] at this
    have hl0 : 0 ≤ lam k :=
      (mul_nonneg (h.sigmaL_nonneg k fun j hj => hk j hj.le) (norm_nonneg _)).trans h1
    rwa [Real.norm_of_nonneg hl0] at this
  have hlt : lam k * t ≤ sigmaUMax P L * t ^ 2 := by
    have := mul_le_mul_of_nonneg_right hσ (norm_nonneg (s k))
    nlinarith [norm_nonneg (s k)]
  have hC : 0 < L + 4 * sigmaUMax P L + 2 * P.κ₃ := by
    linarith [hf.nonneg, sigmaUMax_pos P L, P.κ₃_pos]
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  nlinarith

/-- **Lemma 3.4.9** of [cartis2022evaluation], second part. Let $f$ satisfy Assumption f.HL with
constant $L_{f,2}$, and let $\epsilon_2 < \infty$. If iteration $k$ of an iRN run is before
termination, then
$$\|s_k\| \ge \frac{-\lambda_{\min}[Q_k^T \nabla^2 f(x_k) Q_k]}{\kappa_4 + \sigma^U_{\max}}.
  \qquad (3.4.40)$$

For $\epsilon_2 < \infty$ the curvature condition (3.4.32) is part of Step 2, so it holds at
iteration $k$. -/
theorem lemma_3_4_9_curv (hf : AssumptionHL f L)
    (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) (hε₂ : ε₂ ≠ none) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) :
    -minCurvatureOn (iteratedFDeriv ℝ 2 f (x k)) (V k) / (P.κ₄ + sigmaUMax P L) ≤ ‖s k‖ := by
  obtain ⟨-, h2, -, -, h5⟩ := h.step_of_le hk
  have hσ := lemma_3_4_8 hf h k fun j hj => hk j hj.le
  have hc : 0 < P.κ₄ + sigmaUMax P L := by linarith [P.κ₄_pos, sigmaUMax_pos P L]
  have hlam : lam k ≤ sigmaUMax P L * ‖s k‖ :=
    h2.trans (mul_le_mul_of_nonneg_right hσ (norm_nonneg _))
  have key : -((P.κ₄ + sigmaUMax P L) * ‖s k‖) ≤
      minCurvatureOn (iteratedFDeriv ℝ 2 f (x k)) (V k) := by
    refine le_minCurvatureOn (by have := norm_nonneg (s k); nlinarith) fun d hd => ?_
    have := minCurvatureOn_mul_norm_sq_le (A := iteratedFDeriv ℝ 2 f (x k) + lam k • innerForm) hd
    have h6 := mul_le_mul_of_nonneg_right (h5 hε₂) (sq_nonneg ‖d‖)
    simp only [add_apply, smul_apply, innerForm_apply_diag, smul_eq_mul] at this
    have : lam k * ‖d‖ ^ 2 ≤ sigmaUMax P L * ‖s k‖ * ‖d‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlam (sq_nonneg _)
    nlinarith
  rw [div_le_iff₀ hc]
  linarith

/-- The bound (3.4.42) $M = \log(\sigma^U_{\max} / \sigma_{\min}) / \log \gamma_1 + 1$ on the length
of a block of unsuccessful iRN iterations. -/
noncomputable def irnUnsuccBound (P : IRNParams) (L : ℝ) : ℝ :=
  Real.log (sigmaUMax P L / P.σmin) / Real.log P.γ₁ + 1

/-- The bound (3.4.42) is at least one: $M \ge 1$. -/
theorem one_le_irnUnsuccBound (P : IRNParams) (L : ℝ) : 1 ≤ irnUnsuccBound P L := by
  have := Real.log_nonneg ((one_le_div P.σmin_pos).2 (σmin_le_sigmaUMax P L))
  have := Real.log_pos P.one_lt_γ₁
  unfold irnUnsuccBound
  have : 0 ≤ Real.log (sigmaUMax P L / P.σmin) / Real.log P.γ₁ := by positivity
  linarith

/-- Along a block of $m \ge 1$ unsuccessful iterations $i, \dots, i + m - 1$ of an iRN run before
termination, $\sigma^L_{i+m} \ge \gamma_1^{m-1} \sigma_{\min}$. -/
private theorem irn_sigmaL_ge (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {i : ℕ} :
    ∀ m, 1 ≤ m → (∀ j < i + m, ¬ irnTest f ε₁ ε₂ (x j) (V j)) →
      (∀ l, i ≤ l → l < i + m → irnRatio f (x l) (s l) < P.η) →
      P.γ₁ ^ (m - 1) * P.σmin ≤ σL (i + m) := by
  have hγ := P.one_lt_γ₁
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro hstop hfail
    have hi : ∀ j ≤ i, ¬ irnTest f ε₁ ε₂ (x j) (V j) := fun j hj => hstop j (by omega)
    obtain ⟨-, u2, u3⟩ := h.update i hi
    have hs := hfail i le_rfl (by omega)
    rw [Nat.sub_self, pow_zero, one_mul]
    by_cases hl : lam i < P.σmin * ‖s i‖
    · exact (u2 hs hl).1
    · rw [(u3 hs (not_lt.1 hl)).1]
      have hpos : 0 < ‖s i‖ := norm_pos_iff.2 (h.s_ne_zero hi)
      have : P.σmin ≤ lam i / ‖s i‖ := by rw [le_div_iff₀ hpos]; exact not_lt.1 hl
      nlinarith [P.σmin_pos]
  | succ m hm ih =>
    intro hstop hfail
    have hprev := ih (fun j hj => hstop j (by omega)) fun l hl hl' => hfail l hl (by omega)
    have hl : ∀ j ≤ i + m, ¬ irnTest f ε₁ ε₂ (x j) (V j) := fun j hj => hstop j (by omega)
    obtain ⟨-, u2, u3⟩ := h.update (i + m) hl
    have hs := hfail (i + m) (by omega) (by omega)
    obtain ⟨h1, -⟩ := h.step_of_le hl
    have hpos : 0 < ‖s (i + m)‖ := norm_pos_iff.2 (h.s_ne_zero hl)
    have hpow : 1 ≤ P.γ₁ ^ (m - 1) := one_le_pow₀ hγ.le
    have hL : σL (i + m) ≤ lam (i + m) / ‖s (i + m)‖ := by rw [le_div_iff₀ hpos]; exact h1
    have hge : P.σmin * ‖s (i + m)‖ ≤ lam (i + m) := by
      have := mul_le_mul_of_nonneg_right (hprev.trans hL) hpos.le
      rw [div_mul_cancel₀ _ hpos.ne'] at this
      have h3 : P.σmin * ‖s (i + m)‖ ≤ P.γ₁ ^ (m - 1) * P.σmin * ‖s (i + m)‖ := by
        have := mul_le_mul_of_nonneg_right hpow (mul_nonneg P.σmin_pos.le hpos.le)
        linarith
      linarith
    rw [show i + (m + 1) = i + m + 1 by ring, (u3 hs hge).1,
      show m + 1 - 1 = m - 1 + 1 by omega, pow_succ]
    nlinarith [P.σmin_pos]

/-- **Lemma 3.4.10** of [cartis2022evaluation]. Let $f$ satisfy Assumption f.HL with constant
$L_{f,2}$. Let the iterations $i, \dots, i + m - 1$ of an iRN run be unsuccessful, and let the
termination test fail at all iterations $j \le i + m$. Then
$$m \le \frac{\log(\sigma^U_{\max} / \sigma_{\min})}{\log \gamma_1} + 1. \qquad (3.4.42)$$
This applies, for example, to the iterations strictly between two consecutive successful
iterations, and to the iterations before the first successful iteration.

**Reading.** The bound is stated for a block of unsuccessful iterations that is followed by an
iteration $i + m$ before termination. A final block before termination can have one more
element; see `CartisGouldToint.Chapter03.lemma_3_4_10_last`. -/
theorem lemma_3_4_10 (hf : AssumptionHL f L) (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V)
    {i m : ℕ} (hstop : ∀ j ≤ i + m, ¬ irnTest f ε₁ ε₂ (x j) (V j))
    (hfail : ∀ l, i ≤ l → l < i + m → irnRatio f (x l) (s l) < P.η) :
    (m : ℝ) ≤ irnUnsuccBound P L := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [CharP.cast_eq_zero]; linarith [one_le_irnUnsuccBound P L]
  have hσL := irn_sigmaL_ge h m hm (fun j hj => hstop j hj.le) hfail
  obtain ⟨h1, h2, -⟩ := h.step_of_le hstop
  have hpos : 0 < ‖s (i + m)‖ := norm_pos_iff.2 (h.s_ne_zero hstop)
  have hU := lemma_3_4_8 hf h (i + m) fun j hj => hstop j hj.le
  have hLU : σL (i + m) ≤ σU (i + m) := by
    have := h1.trans h2
    exact le_of_mul_le_mul_right this hpos
  have hγ := P.one_lt_γ₁
  have key : P.γ₁ ^ (m - 1) ≤ sigmaUMax P L / P.σmin := by
    rw [le_div_iff₀ P.σmin_pos]; linarith
  have hlog := Real.log_le_log (by positivity) key
  rw [Real.log_pow] at hlog
  have hl1 := Real.log_pos hγ
  unfold irnUnsuccBound
  rw [← sub_le_iff_le_add, le_div_iff₀ hl1]
  have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm]; simp
  rw [this] at hlog
  linarith

/-- **Lemma 3.4.10** of [cartis2022evaluation], final block. Let $f$ satisfy Assumption f.HL with
constant $L_{f,2}$. If the iterations $i, \dots, i + m - 1$ of an iRN run are unsuccessful and
the termination test fails at all iterations $j < i + m$, then
$$m \le \frac{\log(\sigma^U_{\max} / \sigma_{\min})}{\log \gamma_1} + 2.$$

Here the run may terminate at iteration $i + m$. The bound is one more than (3.4.42). -/
theorem lemma_3_4_10_last (hf : AssumptionHL f L)
    (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {i m : ℕ}
    (hstop : ∀ j < i + m, ¬ irnTest f ε₁ ε₂ (x j) (V j))
    (hfail : ∀ l, i ≤ l → l < i + m → irnRatio f (x l) (s l) < P.η) :
    (m : ℝ) ≤ irnUnsuccBound P L + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [CharP.cast_eq_zero]; linarith [one_le_irnUnsuccBound P L]
  have hσL := irn_sigmaL_ge h m hm hstop hfail
  -- the last unsuccessful iteration bounds `σᴸ_{i+m} ≤ γ₁ σᵁ_max`
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hl : ∀ j ≤ i + m', ¬ irnTest f ε₁ ε₂ (x j) (V j) := fun j hj => hstop j (by omega)
  obtain ⟨-, u2, u3⟩ := h.update (i + m') hl
  have hs := hfail (i + m') (by omega) (by omega)
  have hU := lemma_3_4_8 hf h (i + m') fun j hj => hl j hj.le
  have hγ := P.one_lt_γ₁
  have hσU := sigmaUMax_pos P L
  have hup : σL (i + (m' + 1)) ≤ P.γ₁ * sigmaUMax P L := by
    rw [show i + (m' + 1) = i + m' + 1 by ring]
    by_cases hlt : lam (i + m') < P.σmin * ‖s (i + m')‖
    · refine (u2 hs hlt).2.1.trans ?_
      have : P.σmax ≤ sigmaUMax P L := le_max_left _ _
      nlinarith
    · rw [(u3 hs (not_lt.1 hlt)).1]
      obtain ⟨-, h2, -⟩ := h.step_of_le hl
      have hpos : 0 < ‖s (i + m')‖ := norm_pos_iff.2 (h.s_ne_zero hl)
      have : lam (i + m') / ‖s (i + m')‖ ≤ sigmaUMax P L := by
        rw [div_le_iff₀ hpos]; nlinarith
      nlinarith
  have key : P.γ₁ ^ m' ≤ P.γ₁ * (sigmaUMax P L / P.σmin) := by
    rw [mul_div_assoc', le_div_iff₀ P.σmin_pos]
    simp only [add_tsub_cancel_right] at hσL
    linarith
  have hlog := Real.log_le_log (by positivity) key
  rw [Real.log_pow, Real.log_mul (by positivity) (by have := P.σmin_pos; positivity)] at hlog
  have hl1 := Real.log_pos hγ
  unfold irnUnsuccBound
  push_cast
  have : (m' : ℝ) ≤ 1 + Real.log (sigmaUMax P L / P.σmin) / Real.log P.γ₁ := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hl1]; linarith
  linarith

end IRNLemmas

/-! ### Theorems 3.4.11 and 3.4.12 -/

/-- Let $t, \epsilon \ge 0$ and $C > 0$. If $t^2 \ge 2 \epsilon / C$, then
$t^3 \ge 2 \sqrt{2} \, \epsilon^{3/2} / C^{3/2}$. -/
theorem rpow_three_halves_div_le {t C ε : ℝ} (ht : 0 ≤ t) (hC : 0 < C) (hε : 0 ≤ ε)
    (h : 2 / C * ε ≤ t ^ 2) : ε ^ (3 / 2 : ℝ) / (C ^ (3 / 2 : ℝ) / (2 * √2)) ≤ t ^ 3 := by
  have h3 : (t ^ 2) ^ (3 / 2 : ℝ) = t ^ 3 := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht]; norm_num
  have h2 : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * √2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hm := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [h3, Real.mul_rpow (by positivity) hε, Real.div_rpow (by norm_num) hC.le, h2] at hm
  have : 0 < C ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hC _
  calc ε ^ (3 / 2 : ℝ) / (C ^ (3 / 2 : ℝ) / (2 * √2)) =
      2 * √2 / C ^ (3 / 2 : ℝ) * ε ^ (3 / 2 : ℝ) := by field_simp
    _ ≤ t ^ 3 := hm

/-- The constant $\kappa^S_{\mathrm{iRN}} = (L_{f,2} + 4 \sigma^U_{\max} + 2 \kappa_3)^{3/2} / (2
\sqrt{2} \, \eta)$ of the proof of Theorem 3.4.11 in Appendix B. -/
noncomputable def kappaSIRN (P : IRNParams) (L : ℝ) : ℝ :=
  (L + 4 * sigmaUMax P L + 2 * P.κ₃) ^ (3 / 2 : ℝ) / (2 * √2) / P.η

/-- The corrected constant $\kappa^A_{\mathrm{iRN}} = \kappa^S_{\mathrm{iRN}} (M + 1)$ of Theorem
3.4.11, where $M$ is the bound (3.4.42). So $\kappa^A_{\mathrm{iRN}} = \kappa^S_{\mathrm{iRN}}
(\log(\sigma^U_{\max} / \sigma_{\min}) / \log \gamma_1 + 2)$. -/
noncomputable def kappaAIRN (P : IRNParams) (L : ℝ) : ℝ :=
  kappaSIRN P L * (irnUnsuccBound P L + 1)

/-- **Theorem 3.4.11** of [cartis2022evaluation], the constant $\kappa^B$. The corrected constant is
$\kappa^B_{\mathrm{iRN}} = M + 2$, where $M = \log(\sigma^U_{\max} / \sigma_{\min}) / \log
\gamma_1 + 1$ is the bound (3.4.42).

**Correction.** The source has $\kappa^B = 2M$, which does not count the successful iterations
themselves; see `CartisGouldToint.Chapter03.theorem_3_4_11`.

With $\epsilon_2 = +\infty$ the run cannot terminate right after an unsuccessful iteration, so
the final block of unsuccessful iterations is empty. -/
noncomputable def kappaBIRN (P : IRNParams) (L : ℝ) : ℝ := irnUnsuccBound P L + 2

/-- **Theorem 3.4.12** of [cartis2022evaluation], the constant $\kappa^D$. The corrected constant is
$\kappa^D_{\mathrm{iRN}} = 2M + 3$, where $M$ is the bound (3.4.42).

**Correction.** The count of the source does not include the successful iterations and the final
block of unsuccessful iterations. When $\epsilon_2 < \infty$ the final block can have $M + 1$
elements (`CartisGouldToint.Chapter03.lemma_3_4_10_last`); see
`CartisGouldToint.Chapter03.theorem_3_4_12`. -/
noncomputable def kappaDIRN (P : IRNParams) (L : ℝ) : ℝ := 2 * irnUnsuccBound P L + 3

/-- The constant
$$\kappa^T_{\mathrm{iRN}} = \eta^{-1} \max\left(\frac{(L_{f,2} + 4 \sigma^U_{\max} + 2
  \kappa_3)^{3/2}}{2 \sqrt{2}}, (\kappa_4 + \sigma^U_{\max})^3\right)$$
of the proof of Theorem 3.4.12 in Appendix B. -/
noncomputable def kappaTIRN (P : IRNParams) (L : ℝ) : ℝ :=
  P.η⁻¹ * max ((L + 4 * sigmaUMax P L + 2 * P.κ₃) ^ (3 / 2 : ℝ) / (2 * √2))
    ((P.κ₄ + sigmaUMax P L) ^ 3)

/-- The corrected constant $\kappa^C_{\mathrm{iRN}} = \kappa^T_{\mathrm{iRN}} (M + 1)$ of Theorem
3.4.12, where $M$ is the bound (3.4.42). So $\kappa^C_{\mathrm{iRN}} = \kappa^T_{\mathrm{iRN}}
(\log(\sigma^U_{\max} / \sigma_{\min}) / \log \gamma_1 + 2)$. -/
noncomputable def kappaCIRN (P : IRNParams) (L : ℝ) : ℝ :=
  kappaTIRN P L * (irnUnsuccBound P L + 1)

section IRNTheorems

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : IRNParams} {ε₁ : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {lam σL σU : ℕ → ℝ}
  {V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))} {L flow : ℝ}

/-- Between a successful iteration $j$ of an iRN run and the next successful iteration $j'$, the
iterate stays equal to $x_{j+1}$. -/
private theorem irn_x_eq (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {j j' : ℕ}
    (hstop : ∀ i < j', ¬ irnTest f ε₁ ε₂ (x i) (V i))
    (hnone : ∀ i, j < i → i < j' → ¬ P.η ≤ irnRatio f (x i) (s i)) :
    ∀ m, j + 1 ≤ m → m ≤ j' → x m = x (j + 1) := by
  intro m hm hmj
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [h.eq_self (fun i hi => hstop i (by omega)) (not_le.1 (hnone m (by omega) (by omega))),
      ih (by omega)]

/-- Under Assumption f.HL, if every iteration $k$ before termination of an iRN run has at most $N$
successful iterations in $[0, k]$, then the run terminates at some $k_\epsilon$ after at most
$(M + 1) N + M + 2$ evaluations of $f$ and at most $N + 1$ evaluations of the derivatives, and
$k_\epsilon \le (M + 1) N + u$ for the length $u$ of the final block of unsuccessful iterations,
where $M$ is the bound (3.4.42). -/
private theorem irn_count (hf : AssumptionHL f L) (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V)
    {N : ℝ} (hN : 0 ≤ N)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) →
      ((successSet (fun j => P.η ≤ irnRatio f (x j) (s j)) k).card : ℝ) ≤ N) :
    ∃ kε, IsFirstHit (fun k => irnTest f ε₁ ε₂ (x k) (V k)) kε ∧
      (funEvalCount kε : ℝ) ≤ (irnUnsuccBound P L + 1) * N + irnUnsuccBound P L + 2 ∧
      (derivEvalCount (fun k => P.η ≤ irnRatio f (x k) (s k)) kε : ℝ) ≤ N + 1 ∧
      ∃ u ≤ kε, (∀ l, kε - u ≤ l → l < kε → irnRatio f (x l) (s l) < P.η) ∧
        (kε : ℝ) ≤ (irnUnsuccBound P L + 1) * N + u := by
  classical
  set succ := fun k => P.η ≤ irnRatio f (x k) (s k)
  set M := irnUnsuccBound P L
  have hM := one_le_irnUnsuccBound P L
  have hD : ∀ k, (derivEvalCount succ (k + 1) : ℝ) =
      derivEvalCount succ k + if succ k then 1 else 0 := by
    intro k
    rw [derivEvalCount_eq_count, derivEvalCount_eq_count, Nat.count_succ]
    split_ifs <;> push_cast <;> ring
  -- the invariant
  have inv : ∀ k, (∀ j < k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) → ∃ u ≤ k,
      (∀ l, k - u ≤ l → l < k → ¬ succ l) ∧
      (k : ℝ) ≤ (M + 1) * ((derivEvalCount succ k : ℝ) - 1) + u := by
    intro k
    induction k with
    | zero => intro _; exact ⟨0, le_rfl, fun l _ hl => absurd hl (Nat.not_lt_zero _), by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, hu, hblock, hbound⟩ := ih fun j hj => hk j (hj.trans k.lt_succ_self)
      by_cases hs : succ k
      · have hu' := lemma_3_4_10 (i := k - u) (m := u) hf h
          (fun j hj => hk j (by omega)) fun l hl hl' => not_le.1 (hblock l hl (by omega))
        refine ⟨0, Nat.zero_le _, fun l hl hl' => by omega, ?_⟩
        rw [hD, ite_eq_left hs]
        push_cast
        nlinarith
      · refine ⟨u + 1, by omega, fun l hl hl' => ?_, ?_⟩
        · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hl') with hl' | rfl
          · exact hblock l (by omega) hl'
          · exact hs
        · rw [hD, ite_eq_right hs]
          push_cast
          linarith
  have hbd : ∀ K, (∀ j < K, ¬ irnTest f ε₁ ε₂ (x j) (V j)) →
      (K : ℝ) ≤ (M + 1) * N + M + 1 ∧ (derivEvalCount succ K : ℝ) ≤ N + 1 := by
    intro K hK
    obtain ⟨u, hu, hblock, hbound⟩ := inv K hK
    have hu' := lemma_3_4_10_last (i := K - u) (m := u) hf h (fun j hj => hK j (by omega))
      fun l hl hl' => not_le.1 (hblock l hl (by omega))
    have hDK : (derivEvalCount succ K : ℝ) ≤ N + 1 := by
      cases K with
      | zero => simp [hN]
      | succ k =>
        rw [derivEvalCount_add_one]
        push_cast
        linarith [hsucc k fun j hj => hK j (Nat.lt_succ_of_le hj)]
    refine ⟨?_, hDK⟩
    have : (M + 1) * ((derivEvalCount succ K : ℝ) - 1) ≤ (M + 1) * N :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hex : ∃ k, irnTest f ε₁ ε₂ (x k) (V k) := by
    by_contra hne
    push Not at hne
    have := (hbd (⌊(M + 1) * N + M + 1⌋₊ + 1) fun j _ => hne j).1
    push_cast at this
    linarith [Nat.lt_floor_add_one ((M + 1) * N + M + 1)]
  obtain ⟨kε, hkε⟩ := exists_isFirstHit hex
  obtain ⟨h1, h2⟩ := hbd kε fun j hj => hkε.not_test_of_lt hj
  obtain ⟨u, hu, hblock, hbound⟩ := inv kε fun j hj => hkε.not_test_of_lt hj
  have : (M + 1) * ((derivEvalCount succ kε : ℝ) - 1) ≤ (M + 1) * N :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  refine ⟨kε, hkε, ?_, h2, u, hu, fun l hl hl' => not_le.1 (hblock l hl hl'), by linarith⟩
  rw [funEvalCount_eq]
  push_cast
  linarith

/-- **Theorem 3.4.11** of [cartis2022evaluation]. Let $f$ satisfy Assumption f.Bb with lower bound
$f_{\mathrm{low}}$ and Assumption f.HL with constant $L_{f,2}$. Every iRN run with
$\epsilon_2 = +\infty$ terminates at a first iteration $k_\epsilon$ with
$\|\nabla f(x_{k_\epsilon})\| \le \epsilon_1$. It needs at most
$$\kappa^A \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon_1^{3/2}} + \kappa^B \qquad (3.4.43)$$
evaluations of $f$ and at most
$$\kappa^S \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon_1^{3/2}} + 2 \qquad (3.4.44)$$
evaluations of $\nabla f$ and $\nabla^2 f$. Here $\kappa^S = (L_{f,2} + 4 \sigma^U_{\max} + 2
\kappa_3)^{3/2} / (2 \sqrt{2} \, \eta)$, $\kappa^A = \kappa^S (M + 1)$ and $\kappa^B = M + 2$,
where $M = \log(\sigma^U_{\max} / \sigma_{\min}) / \log \gamma_1 + 1$ is the bound (3.4.42).

**Correction.** The source has $\kappa^A = \kappa^S M$ and $\kappa^B = 2M$. Its proof in
Appendix B multiplies the bound on the number of successful iterations by $M$. This does not
count the successful iterations themselves.

The proof is in Appendix B of the source. With $\epsilon_2 = +\infty$ the test depends only on
the iterate, so the run cannot terminate right after an unsuccessful iteration. -/
theorem theorem_3_4_11 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L)
    (h : algorithm_3_4_2 f P ε₁ none x s lam σL σU V) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaAIRN P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) +
        kappaBIRN P L ∧
      (derivEvalCount (fun k => P.η ≤ irnRatio f (x k) (s k)) kε : ℝ) ≤
        kappaSIRN P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) + 2 := by
  have hε := h.ε₁_pos
  set C := L + 4 * sigmaUMax P L + 2 * P.κ₃
  have hC : 0 < C := by linarith [hf.nonneg, sigmaUMax_pos P L, P.κ₃_pos]
  have ha : 0 < C ^ (3 / 2 : ℝ) / (2 * √2) := by
    have := Real.rpow_pos_of_pos hC (3 / 2 : ℝ); positivity
  have hη := P.η_pos
  have hε32 : 0 < ε₁ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  set X := (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ)
  have hX : 0 ≤ X := div_nonneg (sub_nonneg.2 (hb _)) hε32.le
  set N := kappaSIRN P L * X
  have hN : 0 ≤ N := mul_nonneg (by unfold kappaSIRN; positivity) hX
  have hsucc : ∀ k, (∀ j ≤ k + 1, ¬ irnTest f ε₁ none (x j) (V j)) →
      ((successSet (fun j => P.η ≤ irnRatio f (x j) (s j)) k).card : ℝ) ≤ N := by
    intro k hk
    have hc : 0 < P.η * (ε₁ ^ (3 / 2 : ℝ) / (C ^ (3 / 2 : ℝ) / (2 * √2))) := by positivity
    have := card_successSet_le_div_of_decrease (φ := fun j => f (x j)) hc
      (fun j hj hs => by
        rw [h.eq_self (fun i hi => hk i (hi.trans (hj.trans k.le_succ))) (not_le.1 hs)])
      (fun j hj hs => by
        have hj' : ∀ i ≤ j, ¬ irnTest f ε₁ none (x i) (V i) := fun i hi =>
          hk i (hi.trans (hj.trans k.le_succ))
        have hG : ε₁ < ‖gradient f (x (j + 1))‖ := by
          by_contra hle
          exact hk (j + 1) (Nat.succ_le_succ hj) ⟨not_lt.1 hle, by simp⟩
        have h9 := lemma_3_4_9 hf h hj' hs
        have ht := rpow_three_halves_div_le (norm_nonneg (s j)) hC hε.le
          ((mul_le_mul_of_nonneg_left hG.le (by positivity)).trans h9)
        exact (mul_le_mul_of_nonneg_left ht hη.le).trans (h.sub_ge hj' hs))
      (hb (x (k + 1)))
    refine this.trans_eq ?_
    simp only [N, X, kappaSIRN]
    field_simp
    rfl
  obtain ⟨kε, hk, -, hD, u, hu, hblock, hbound⟩ := irn_count hf h (by linarith)
    (card_successSet_le_add_one_of_forall hN hsucc)
  have hk' : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε :=
    ⟨hk.test.1, fun j hj hg => hk.not_test_of_lt hj ⟨hg, by simp⟩⟩
  -- with `ε₂ = ∞` the test depends on the iterate only: the last iteration was successful
  have hu0 : u = 0 := by
    by_contra hu0
    have hl : kε - 1 < kε := by omega
    have hx := h.eq_self (k := kε - 1) (fun i hi => hk.not_test_of_lt (by omega))
      (hblock (kε - 1) (by omega) hl)
    rw [show kε - 1 + 1 = kε by omega] at hx
    exact hk'.not_test_of_lt hl (hx ▸ hk'.test)
  rw [hu0, Nat.cast_zero] at hbound
  have hNe : N = kappaSIRN P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) := by
    simp only [N, X]; ring
  refine ⟨kε, hk', ?_, hD.trans_eq (by rw [hNe]; ring)⟩
  rw [funEvalCount_eq]
  push_cast
  have hM := one_le_irnUnsuccBound P L
  calc (kε : ℝ) + 1 ≤ (irnUnsuccBound P L + 1) * (N + 1) + 0 + 1 := by linarith
    _ = kappaAIRN P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) + kappaBIRN P L := by
      simp only [kappaAIRN, kappaBIRN, hNe]; ring

/-- **Theorem 3.4.12** of [cartis2022evaluation]. Let $f$ satisfy Assumption f.Bb with lower bound
$f_{\mathrm{low}}$ and Assumption f.HL with constant $L_{f,2}$. Every iRN run with
$\epsilon_2 < \infty$ terminates at a first iteration $k_\epsilon$ with
$\|\nabla f(x_{k_\epsilon})\| \le \epsilon_1$ and $\lambda_{\min}[Q_{k_\epsilon}^T \nabla^2
f(x_{k_\epsilon}) Q_{k_\epsilon}] \ge -\epsilon_2$. It needs at most
$$2 \kappa^C \frac{f(x_0) - f_{\mathrm{low}}}{\min(\epsilon_1^{3/2}, \epsilon_2^3)} + \kappa^D$$
evaluations of $f$ and at most
$$2 \kappa^T \frac{f(x_0) - f_{\mathrm{low}}}{\min(\epsilon_1^{3/2}, \epsilon_2^3)} + 2$$
evaluations of $\nabla f$ and $\nabla^2 f$. Here $\kappa^T$ is the constant of Appendix B,
$\kappa^C = \kappa^T (M + 1)$ and $\kappa^D = 2M + 3$, where $M$ is the bound (3.4.42).

**Correction.** The proof in Appendix B claims that $\|\nabla f(x_k)\| \le \epsilon_1$ for all
$k \ge k_1$. This is unjustified, because the gradient can grow again. Instead, every successful
iteration without the required decrease is followed by a successful iteration with decrease at
least $\kappa_6 \epsilon_2^3$, for a constant $\kappa_6$ of the proof, and this gives the factor
$2$ on the leading terms. The count of all iterations must also include the successful
iterations and the final block of unsuccessful iterations. That block can have $M + 1$ elements
(`CartisGouldToint.Chapter03.lemma_3_4_10_last`), because the second-order test also depends on
$Q_k$.

The run predicate gives $\epsilon_1 \in (0, 1]$ and $\epsilon_2 > 0$; no bound
$\epsilon_2 \le 1$ is needed. The tolerance $\epsilon_2$ is `some e`. -/
theorem theorem_3_4_12 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L) {e : ℝ}
    (h : algorithm_3_4_2 f P ε₁ (some e) x s lam σL σU V) :
    ∃ kε, IsFirstHit (fun k => irnTest f ε₁ (some e) (x k) (V k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        2 * kappaCIRN P L * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) +
          kappaDIRN P L ∧
      (derivEvalCount (fun k => P.η ≤ irnRatio f (x k) (s k)) kε : ℝ) ≤
        2 * kappaTIRN P L * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) + 2 := by
  have hε := h.ε₁_pos
  have he := h.ε₂_pos e rfl
  set C := L + 4 * sigmaUMax P L + 2 * P.κ₃
  have hC : 0 < C := by linarith [hf.nonneg, sigmaUMax_pos P L, P.κ₃_pos]
  set a := C ^ (3 / 2 : ℝ) / (2 * √2)
  have ha : 0 < a := by have := Real.rpow_pos_of_pos hC (3 / 2 : ℝ); positivity
  set b := (P.κ₄ + sigmaUMax P L) ^ 3
  have hκσ : 0 < P.κ₄ + sigmaUMax P L := by linarith [P.κ₄_pos, sigmaUMax_pos P L]
  have hb' : 0 < b := by positivity
  have hη := P.η_pos
  have hε32 : 0 < ε₁ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  set m := min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3)
  have hm : 0 < m := lt_min hε32 (by positivity)
  set X := (f (x 0) - flow) / m
  have hX : 0 ≤ X := div_nonneg (sub_nonneg.2 (hb _)) hm.le
  set N := kappaTIRN P L * X
  have hκT : kappaTIRN P L = P.η⁻¹ * max a b := rfl
  have hN : 0 ≤ N := mul_nonneg (by rw [hκT]; positivity) hX
  set succ := fun j => P.η ≤ irnRatio f (x j) (s j)
  have hsucc : ∀ k, (∀ j ≤ k, ¬ irnTest f ε₁ (some e) (x j) (V j)) →
      ((successSet succ k).card : ℝ) ≤ 2 * N + 1 := by
    intro k hk
    set good := fun j => succ j ∧
      (minCurvatureOn (iteratedFDeriv ℝ 2 f (x j)) (V j) < -e ∨
        ε₁ < ‖gradient f (x (j + 1))‖)
    have hcard := card_successSet_le_two_mul_add_one (succ := succ) (good := good) (K := k)
      (fun j _ hg => hg.1) (fun j j' hjj' hj'k hsj hgj hsj' hnone => by
        refine ⟨hsj', Or.inl ?_⟩
        have hstop : ∀ i < j', ¬ irnTest f ε₁ (some e) (x i) (V i) := fun i hi => hk i (by omega)
        have hx := irn_x_eq h hstop hnone j' (by omega) le_rfl
        have hg : ‖gradient f (x (j + 1))‖ ≤ ε₁ := by
          by_contra hlt
          exact hgj ⟨hsj, Or.inr (not_le.1 hlt)⟩
        by_contra hge
        exact hk j' hj'k ⟨by rw [hx]; exact hg, fun e' he' => by
          simp only [Option.mem_def, Option.some.injEq] at he'
          subst he'
          exact not_lt.1 hge⟩) k le_rfl
    have hc : 0 < m / (P.η⁻¹ * max a b) := by positivity
    have hG := card_le_div_of_decrease (φ := fun j => f (x j)) (T := successSet good k) hc
      successSet_subset_range (fun j hj => h.le fun i hi => hk i (hi.trans hj))
      (fun j hj => by
        rw [mem_successSet] at hj
        obtain ⟨hjk, hsj, hgj⟩ := hj
        have hj' : ∀ i ≤ j, ¬ irnTest f ε₁ (some e) (x i) (V i) := fun i hi => hk i (hi.trans hjk)
        refine le_trans ?_ (h.sub_ge hj' hsj)
        have hmax : 0 < max a b := lt_max_of_lt_left ha
        rw [div_eq_mul_inv, mul_inv, inv_inv]
        have hT : m / max a b ≤ ‖s j‖ ^ 3 := by
          rcases hgj with hl | hgr
          · have h9 := lemma_3_4_9_curv hf h (by simp) hj'
            have hse : e / (P.κ₄ + sigmaUMax P L) ≤ ‖s j‖ :=
              (div_le_div_of_nonneg_right (by linarith) hκσ.le).trans h9
            have h3 := pow_le_pow_left₀ (by positivity) hse 3
            rw [div_pow] at h3
            calc m / max a b ≤ e ^ 3 / b :=
                  div_le_div₀ (by positivity) (min_le_right _ _) hb' (le_max_right _ _)
              _ ≤ _ := h3
          · have h9 := lemma_3_4_9 hf h hj' hsj
            have ht := rpow_three_halves_div_le (norm_nonneg (s j)) hC hε.le
              ((mul_le_mul_of_nonneg_left hgr.le (by positivity)).trans h9)
            calc m / max a b ≤ ε₁ ^ (3 / 2 : ℝ) / a :=
                  div_le_div₀ hε32.le (min_le_left _ _) ha (le_max_left _ _)
              _ ≤ _ := ht
        calc m * (P.η * (max a b)⁻¹) = P.η * (m / max a b) := by ring
          _ ≤ P.η * ‖s j‖ ^ 3 := mul_le_mul_of_nonneg_left hT hη.le)
      (hb (x (k + 1)))
    have : ((successSet succ k).card : ℝ) ≤ 2 * (successSet good k).card + 1 := by
      exact_mod_cast hcard
    have hGN : ((successSet good k).card : ℝ) ≤ N := by
      refine hG.trans_eq ?_
      simp only [N, X, hκT]
      field_simp
    linarith
  obtain ⟨kε, hk, hF, hD, -⟩ := irn_count hf h (by linarith) hsucc
  have hNe : N = kappaTIRN P L * (f (x 0) - flow) / m := by simp only [N, X]; ring
  refine ⟨kε, hk, hF.trans_eq ?_, hD.trans_eq (by rw [hNe]; ring)⟩
  simp only [kappaCIRN, kappaDIRN, hNe]
  ring

end IRNTheorems

/-! ### Existence of iRN runs -/

section IRNExistence

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {y : EuclideanSpace ℝ (Fin n)}

/-- Let $f$ be $C^2$ at $y$, and let $\sigma > 0$ with $\sigma^L \le \sigma \le \sigma^U$. If $s$ is
a global minimizer of the cubic model $\langle \nabla f(y), s \rangle + \tfrac12 \langle s,
\nabla^2 f(y) s \rangle + \tfrac13 \sigma \|s\|^3$, then $s$ satisfies Step 2 of Algorithm 3.4.2
with the multiplier $\lambda = \sigma \|s\|$ and $Q = I$, and the model gradient vanishes:
$\nabla f(y) + (\nabla^2 f(y) + \lambda I) s = 0$. -/
theorem irnStep_of_isMinOn (hf : ContDiffAt ℝ 2 f y) (P : IRNParams) (ε₂ : Option ℝ)
    {σL σU σ : ℝ} {s : EuclideanSpace ℝ (Fin n)} (hσ : 0 < σ) (hσL : σL ≤ σ) (hσU : σ ≤ σU)
    (hmin : IsMinOn (regModel (gradient f y) (hessianOperator f y) σ 3) univ s) :
    irnStep f P ε₂ y σL σU (σ * ‖s‖) ⊤ s ∧ irnGrad f y (σ * ‖s‖) s = 0 := by
  have hsym := hessianOperator_isSymmetric hf
  obtain ⟨hshift, hpos⟩ := (isMinOn_regModel_iff hsym hσ (by norm_num)).1 hmin
  have h1 : ‖s‖ ^ ((3 : ℝ) - 2) = ‖s‖ := by norm_num
  rw [h1] at hshift hpos
  have h2 : hessianOperator f y s + (σ * ‖s‖) • s = -gradient f y := by
    simpa using hshift
  have hg : irnGrad f y (σ * ‖s‖) s = 0 := by
    rw [irnGrad, add_assoc, h2, add_neg_cancel]
  have hpsd : ∀ d, 0 ≤ ⟪d, hessianOperator f y d⟫ + σ * ‖s‖ * ‖d‖ ^ 2 := fun d => by
    have := hpos.inner_nonneg_right d
    simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.add_apply,
      LinearMap.smul_apply, ContinuousLinearMap.coe_coe, one_apply_eq_self, inner_add_right,
      inner_smul_right, real_inner_self_eq_norm_sq] at this
    exact this
  have hn := norm_nonneg s
  refine ⟨⟨mul_le_mul_of_nonneg_right hσL hn, mul_le_mul_of_nonneg_right hσU hn, ?_, ?_,
    fun _ => ?_⟩, hg⟩
  · rw [hg, inner_zero_right]
    refine le_min (by have := P.κ₁_pos; positivity) ?_
    have := hpsd s
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have := P.κ₂_pos
    have : 0 ≤ 1 / 2 * P.κ₂ * ‖s‖ ^ 3 := by positivity
    nlinarith
  · rw [hg, norm_zero]
    have := P.κ₃_pos
    positivity
  · refine le_minCurvatureOn (by have := P.κ₄_pos; nlinarith) fun d _ => ?_
    simp only [add_apply, smul_apply, innerForm_apply_diag, smul_eq_mul]
    rw [apply_diag_eq_vec, ← inner_hessianOperator_apply hf]
    have := hpsd d
    have : -(P.κ₄ * ‖s‖) * ‖d‖ ^ 2 ≤ 0 := by
      have := P.κ₄_pos; have : 0 ≤ P.κ₄ * ‖s‖ * ‖d‖ ^ 2 := by positivity
      linarith
    linarith

/-- **Algorithm 3.4.2** of [cartis2022evaluation], existence of runs. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be $C^2$, let $\epsilon_1 \in (0, 1]$, and let
$\epsilon_2 > 0$ or $\epsilon_2 = +\infty$. Then for every starting point $x_0$ there is an iRN
run from $x_0$ with $Q_k = I$ for all $k$.

In the construction, $s_k$ is a global minimizer of the cubic model
$T_{f,2}(x_k, s) + \tfrac13 \sigma^U_k \|s\|^3$ and $\lambda_k = \sigma^U_k \|s_k\|$, as in
`CartisGouldToint.Chapter03.irnStep_of_isMinOn`. -/
theorem exists_algorithm_3_4_2 (hf : ContDiff ℝ 2 f) (P : IRNParams) {ε₁ : ℝ} {ε₂ : Option ℝ}
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε₂ : ∀ e ∈ ε₂, 0 < e) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (lam σL σU : ℕ → ℝ), x 0 = x₀ ∧
      algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU (fun _ => ⊤) := by
  classical
  let S : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) := fun y σ =>
    if h : 0 < σ then (exists_isMinOn_regModel (gradient f y) (hessianOperator f y) h
      (by norm_num : (2 : ℝ) < 3)).choose else 0
  have hS : ∀ y σ, 0 < σ →
      IsMinOn (regModel (gradient f y) (hessianOperator f y) σ 3) univ (S y σ) := fun y σ h => by
    simp only [S, h, dite_true]
    exact (exists_isMinOn_regModel (gradient f y) (hessianOperator f y) h
      (by norm_num : (2 : ℝ) < 3)).choose_spec
  -- states `(x_k, σᴸ_k, σᵁ_k)`
  let inv : EuclideanSpace ℝ (Fin n) × ℝ × ℝ → Prop := fun a =>
    0 ≤ a.2.1 ∧ a.2.1 ≤ a.2.2 ∧ 0 < a.2.2
  have hstepOK : ∀ a, inv a → irnStep f P ε₂ a.1 a.2.1 a.2.2 (a.2.2 * ‖S a.1 a.2.2‖) ⊤
      (S a.1 a.2.2) ∧ irnGrad f a.1 (a.2.2 * ‖S a.1 a.2.2‖) (S a.1 a.2.2) = 0 :=
    fun a ha => irnStep_of_isMinOn hf.contDiffAt P ε₂ ha.2.2 ha.2.1 le_rfl (hS _ _ ha.2.2)
  have hne : ∀ a, inv a → ¬ irnTest f ε₁ ε₂ a.1 ⊤ → S a.1 a.2.2 ≠ 0 := by
    intro a ha hnot h0
    obtain ⟨⟨-, -, -, -, h5⟩, hg⟩ := hstepOK a ha
    rw [irnGrad, h0, map_zero, add_zero, smul_zero, add_zero] at hg
    refine hnot ⟨by rw [hg, norm_zero]; exact hε₁.le, fun e he => ?_⟩
    have := h5 (by rintro rfl; simp at he)
    rw [h0, norm_zero, mul_zero, mul_zero, neg_zero, zero_smul, add_zero] at this
    linarith [hε₂ e he]
  let next : EuclideanSpace ℝ (Fin n) × ℝ × ℝ → EuclideanSpace ℝ (Fin n) × ℝ × ℝ := fun a =>
    let s := S a.1 a.2.2
    let l := a.2.2 * ‖s‖
    (if P.η ≤ irnRatio f a.1 s then a.1 + s else a.1,
      if P.η ≤ irnRatio f a.1 s then (0, a.2.2)
      else if l < P.σmin * ‖s‖ then (P.σmin, P.σmax) else (P.γ₁ * (l / ‖s‖), P.γ₂ * (l / ‖s‖)))
  have hnext : ∀ a, inv a → ¬ irnTest f ε₁ ε₂ a.1 ⊤ → inv (next a) ∧
      irnUpdate P (irnRatio f a.1 (S a.1 a.2.2)) (a.2.2 * ‖S a.1 a.2.2‖) (S a.1 a.2.2) a.2.2
        (next a).2.1 (next a).2.2 := by
    intro a ha hnot
    have hpos : 0 < ‖S a.1 a.2.2‖ := norm_pos_iff.2 (hne a ha hnot)
    have hγ := P.one_lt_γ₁
    have hγ2 := P.γ₁_le_γ₂
    by_cases hs : P.η ≤ irnRatio f a.1 (S a.1 a.2.2)
    · simp only [next, hs, ite_true]
      exact ⟨⟨le_rfl, ha.1.trans ha.2.1, ha.2.2⟩, fun _ => ⟨rfl, rfl⟩,
        fun h => absurd h (not_lt.2 hs), fun h => absurd h (not_lt.2 hs)⟩
    · simp only [next, hs, ite_false]
      by_cases hl : a.2.2 * ‖S a.1 a.2.2‖ < P.σmin * ‖S a.1 a.2.2‖
      · simp only [hl, ite_true]
        exact ⟨⟨P.σmin_pos.le, P.σmin_le_σmax, P.σmin_pos.trans_le P.σmin_le_σmax⟩,
          fun h => absurd h hs, fun _ _ => ⟨le_rfl, P.σmin_le_σmax, P.σmin_le_σmax, le_rfl⟩,
          fun _ h => absurd h (not_le.2 hl)⟩
      · simp only [hl, ite_false]
        have hd : a.2.2 * ‖S a.1 a.2.2‖ / ‖S a.1 a.2.2‖ = a.2.2 := by field_simp
        refine ⟨⟨?_, ?_, ?_⟩, fun h => absurd h hs, fun _ h => absurd h hl,
          fun _ _ => ⟨rfl, rfl⟩⟩ <;> rw [hd]
        · exact mul_nonneg (by linarith) ha.2.2.le
        · exact mul_le_mul_of_nonneg_right hγ2 ha.2.2.le
        · exact mul_pos (by linarith) ha.2.2
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant
    (α := EuclideanSpace ℝ (Fin n) × ℝ × ℝ) (init := fun a => a = (x₀, 0, P.σU₀))
    (inv := fun _ a => inv a) (stop := fun _ a => irnTest f ε₁ ε₂ a.1 ⊤)
    (step := fun _ a b => b = next a ∧ inv b ∧ irnUpdate P (irnRatio f a.1 (S a.1 a.2.2))
      (a.2.2 * ‖S a.1 a.2.2‖) (S a.1 a.2.2) a.2.2 b.2.1 b.2.2)
    ⟨_, rfl⟩ (fun a ha => by
      subst ha
      exact ⟨le_rfl, P.σmin_pos.le.trans P.σmin_le_σU₀, P.σmin_pos.trans_le P.σmin_le_σU₀⟩)
    (fun k a ha hnot => ⟨next a, (hnext a ha hnot).1, rfl, hnext a ha hnot⟩)
  have hinv : ∀ k, (∀ j < k, ¬ irnTest f ε₁ ε₂ (r j).1 ⊤) → inv (r k) := by
    intro k hk
    cases k with
    | zero => rw [hr0]; exact ⟨le_rfl, P.σmin_pos.le.trans P.σmin_le_σU₀,
        P.σmin_pos.trans_le P.σmin_le_σU₀⟩
    | succ k => exact (hr k fun j hj => hk j (Nat.lt_succ_of_le hj)).2.2.1
  refine ⟨fun k => (r k).1, fun k => S (r k).1 (r k).2.2,
    fun k => (r k).2.2 * ‖S (r k).1 (r k).2.2‖,
    fun k => (r k).2.1, fun k => (r k).2.2, by simp only [hr0], hε₁, hε₁1, hε₂,
    by simp only [hr0], by simp only [hr0], fun k hk _ => (hstepOK _ (hinv k hk)).1,
    fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨hb, -, -⟩ := (hr k hk).2
    rw [hb]
  · exact (hr k hk).2.2.2

end IRNExistence

/-! ### One-dimensional examples (for Corollary 3.5.5) -/

section Examples

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)

variable {G : ℝ → ℝ}

/-- For a $C^2$ function $G : \mathbb{R} \to \mathbb{R}$, the quadratic Taylor model of the ridge
function $f(x) = G(\langle e_0, x \rangle)$ on $\mathbb{R}^1$ along $e_0$ is $T_{f,2}(y, t
e_0) = G(a) + G'(a) t + \tfrac12 G''(a) t^2$ with $a = \langle e_0, y \rangle$. -/
theorem tr2Model_ridge (hG : ContDiff ℝ 2 G) (y : EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    tr2Model (ridge G e₀) y (t • e₀) =
      G ⟪e₀, y⟫ + deriv G ⟪e₀, y⟫ * t + iteratedDeriv 2 G ⟪e₀, y⟫ * t ^ 2 / 2 := by
  rw [tr2Model_eq_taylorPolynomial (contDiff_ridge hG).contDiffAt, taylorPolynomial_two_ridge hG,
    inner_e₀_smul]

/-- For a $C^2$ function $G : \mathbb{R} \to \mathbb{R}$, the model (3.4.1) of the ridge function
$f(x) = G(\langle e_0, x \rangle)$ along $e_0$ is $m(t e_0) = G(a) + G'(a) t + \tfrac12 G''(a)
t^2 + \tfrac12 \epsilon_* t^2$ with $a = \langle e_0, y \rangle$. -/
theorem treModel_ridge (hG : ContDiff ℝ 2 G) (εs : ℝ) (y : EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    treModel (ridge G e₀) εs y (t • e₀) =
      G ⟪e₀, y⟫ + deriv G ⟪e₀, y⟫ * t + iteratedDeriv 2 G ⟪e₀, y⟫ * t ^ 2 / 2 +
        εs / 2 * t ^ 2 := by
  rw [treModel_def, tr2Model_ridge hG, norm_smul, norm_e₀, mul_one, Real.norm_eq_abs, sq_abs]

/-- For a $C^2$ function $G : \mathbb{R} \to \mathbb{R}$, the ridge function
$f(x) = G(\langle e_0, x \rangle)$ on $\mathbb{R}^1$ has
$\|\nabla f(y)\| = |G'(\langle e_0, y \rangle)|$. -/
theorem norm_gradient_ridge_e₀ (hG : ContDiff ℝ 2 G) (y : EuclideanSpace ℝ (Fin 1)) :
    ‖gradient (ridge G e₀) y‖ = |deriv G ⟪e₀, y⟫| := by
  rw [gradient_ridge (hG.differentiable (by norm_num)), norm_smul, norm_e₀, mul_one,
    Real.norm_eq_abs]

/-- For a $C^2$ function $G : \mathbb{R} \to \mathbb{R}$, the iRN model gradient of the ridge
function $f(x) = G(\langle e_0, x \rangle)$ along $e_0$ is $\nabla f(y) + (\nabla^2 f(y) +
\lambda I)(t e_0) = (G'(a) + (G''(a) + \lambda) t) e_0$ with $a = \langle e_0, y \rangle$. -/
theorem irnGrad_ridge (hG : ContDiff ℝ 2 G) (y : EuclideanSpace ℝ (Fin 1)) (l t : ℝ) :
    irnGrad (ridge G e₀) y l (t • e₀) =
      (deriv G ⟪e₀, y⟫ + (iteratedDeriv 2 G ⟪e₀, y⟫ + l) * t) • e₀ := by
  rw [irnGrad, gradient_ridge (hG.differentiable (by norm_num)), hessianOperator_ridge hG,
    smul_smul, smul_smul, ← add_smul, ← add_smul]
  ring_nf

/-- For a $C^2$ function $G : \mathbb{R} \to \mathbb{R}$, the derivative of the model (3.4.1) of the
ridge function $f(x) = G(\langle e_0, x \rangle)$ at $t e_0$ has norm
$|G'(a) + (G''(a) + \epsilon_*) t|$ with $a = \langle e_0, y \rangle$. -/
theorem norm_fderiv_treModel_ridge (hG : ContDiff ℝ 2 G) (εs : ℝ) (y : EuclideanSpace ℝ (Fin 1))
    (t : ℝ) : ‖fderiv ℝ (treModel (ridge G e₀) εs y) (t • e₀)‖ =
      |deriv G ⟪e₀, y⟫ + (iteratedDeriv 2 G ⟪e₀, y⟫ + εs) * t| := by
  rw [norm_fderiv_treModel (contDiff_ridge hG).contDiffAt]
  have := irnGrad_ridge hG y εs (t • e₀ |> fun _ => t)
  rw [irnGrad] at this
  rw [this, norm_smul, norm_e₀, mul_one, Real.norm_eq_abs]

/-- **Equation (3.5.12)** of [cartis2022evaluation], the one-dimensional data for TRε. There are
$f_{\mathrm{low}}$, $L_1 \ge 1$, $L_2 \ge 1$ and $B$ with the following property. Let
$\epsilon \in (0, 1)$ and $k_\epsilon = \lceil \epsilon^{-3/2} \rceil$. Then there are a $C^2$
function $G : \mathbb{R} \to \mathbb{R}$, abscissae $X_k$ and steps $t_k$ such that:

* the ridge function $f(x) = G(\langle e_0, x \rangle)$ on $\mathbb{R}^1$ satisfies Assumption
  f.Bb with $f_{\mathrm{low}}$, Assumption f.gL with $L_1$ and Assumption f.HL with $L_2$, and
  $|f| \le B$;
* $X_0 = 0$, and for $k \le k_\epsilon$, $|G'(X_k)| \le \epsilon$ holds if and only if
  $k = k_\epsilon$;
* for $k < k_\epsilon$, $X_{k+1} = X_k + t_k$, $0 < t_k \le \sqrt{\epsilon} / 2$,
  $G''(X_k) \ge \sqrt{\epsilon}$,
$$G'(X_k) + (G''(X_k) + \sqrt{\epsilon}) t_k = 0 \quad\text{and}\quad G(X_k) - G(X_{k+1}) \ge
  -\left(G'(X_k) t_k + \tfrac12 G''(X_k) t_k^2\right).$$

The equation says that $t_k$ minimizes the model (3.4.1) with $\epsilon_* = \sqrt{\epsilon}$,
and the last inequality says that the ratio (3.4.6) is at least $1$. In the construction, the
step factors are $\theta_k = 4 f_k^2 / (4 f_k^2 + 1) \in [1/2, 1]$. The direction $e_0$ is
`CartisGouldToint.Chapter02.e₀`, and the ridge function is `Optimization.ridge G e₀`. -/
theorem tre_slow_data :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (G : ℝ → ℝ) (X t : ℕ → ℝ), ContDiff ℝ 2 G ∧
        Chapter02.AssumptionBb (ridge G e₀) flow ∧ Chapter02.AssumptionGL (ridge G e₀) L₁ ∧
        AssumptionHL (ridge G e₀) L₂ ∧ (∀ y, |ridge G e₀ y| ≤ B) ∧ X 0 = 0 ∧
        (∀ k ≤ ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, (|deriv G (X k)| ≤ ε ↔ ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ ≤ k)) ∧
        ∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, X (k + 1) = X k + t k ∧ 0 < t k ∧ t k ≤ √ε / 2 ∧
          √ε ≤ iteratedDeriv 2 G (X k) ∧
          deriv G (X k) + (iteratedDeriv 2 G (X k) + √ε) * t k = 0 ∧
          -(deriv G (X k) * t k + iteratedDeriv 2 G (X k) * t k ^ 2 / 2) ≤
            G (X k) - G (X (k + 1)) := by
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowSecondOrder_run_data (a := 1 / 2) (b := 1)
    (by norm_num) (by norm_num)
  refine ⟨-B, max B 1, max L 1, B, le_max_right _ _, le_max_right _ _, fun ε hε hε1 => ?_⟩
  set r := √ε with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hε
  have hr2 : r ^ 2 = ε := Real.sq_sqrt hε.le
  have hhalf : ε ^ (1 / 2 : ℝ) = r := by rw [hr, Real.sqrt_eq_rpow]
  have h32 : ε ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  set F := secondOrderF ε
  have hF : ∀ k < secondOrderK ε, 1 / 2 < F k ∧ F k ≤ 1 := fun k hk =>
    ⟨secondOrderF_gt_half hε hk, secondOrderF_le_one hε k⟩
  set θ : ℕ → ℝ := fun k => 4 * F k ^ 2 / (4 * F k ^ 2 + 1)
  have hθ : ∀ k < secondOrderK ε, θ k ∈ Icc (1 / 2 : ℝ) 1 := fun k hk => by
    obtain ⟨h1, -⟩ := hF k hk
    have hd : 0 < 4 * F k ^ 2 + 1 := by positivity
    simp only [θ, Set.mem_Icc]
    constructor
    · rw [le_div_iff₀ hd]; nlinarith
    · rw [div_le_one hd]; linarith
  obtain ⟨G, hG, hGL, hGB, hGk⟩ := H ε θ hε hε1 hθ
  obtain ⟨hb, hgl, -, hhl, -⟩ := ridge_assumptions_two hG hGL hGB
  set X := secondOrderX θ ε
  set t : ℕ → ℝ := fun k => θ k * r / (2 * F k)
  have hval : ∀ k ≤ secondOrderK ε, G (X k) = F k ∧ deriv G (X k) = -2 * ε * F k ∧
      iteratedDeriv 2 G (X k) = 4 * r * F k ^ 2 := fun k hk => by
    obtain ⟨h1, h2, h3, -⟩ := hGk k hk
    exact ⟨h1, h2, by rw [h3, secondOrderH_def, hhalf]⟩
  have hdata : ∀ k < secondOrderK ε, X (k + 1) = X k + t k ∧ 0 < t k ∧ t k ≤ r / 2 ∧
      r ≤ iteratedDeriv 2 G (X k) ∧
      deriv G (X k) + (iteratedDeriv 2 G (X k) + r) * t k = 0 ∧
      -(deriv G (X k) * t k + iteratedDeriv 2 G (X k) * t k ^ 2 / 2) ≤
        G (X k) - G (X (k + 1)) := fun k hk => by
    have hFk := hF k hk
    have hθk := hθ k hk
    obtain ⟨hv1, hv2, hv3⟩ := hval k hk.le
    obtain ⟨hw1, -, -⟩ := hval (k + 1) hk
    have hF0 : F k ≠ 0 := by linarith [hFk.1]
    have htk : 0 < t k := by
      have h1 : 0 < θ k := by linarith [hθk.1]
      have h2 : 0 < 2 * F k := by linarith [hFk.1]
      exact div_pos (mul_pos h1 hr0) h2
    have hd : 0 < 4 * F k ^ 2 + 1 := by positivity
    refine ⟨by simp only [X, t]; rw [secondOrderX_succ, hhalf], htk, ?_, ?_, ?_, ?_⟩
    · have e : t k = r * (2 * F k / (4 * F k ^ 2 + 1)) := by
        simp only [t, θ]; field_simp; ring
      have h2 : 2 * F k / (4 * F k ^ 2 + 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ hd]; nlinarith [sq_nonneg (2 * F k - 1)]
      rw [e]
      nlinarith
    · rw [hv3]
      have : 1 ≤ 4 * F k ^ 2 := by nlinarith [hFk.1]
      have := mul_le_mul_of_nonneg_left this hr0.le
      linarith
    · rw [hv2, hv3, ← hr2]
      simp only [t, θ]
      field_simp
      ring
    · have hpred : -(deriv G (X k) * t k + iteratedDeriv 2 G (X k) * t k ^ 2 / 2) =
          r ^ 3 * (θ k - θ k ^ 2 / 2) := by
        rw [hv2, hv3, ← hr2]
        simp only [t]
        field_simp
        ring
      rw [hpred, hv1, hw1, show F (k + 1) = F k - ε ^ (3 / 2 : ℝ) / 2 from secondOrderF_succ ε k,
        h32]
      nlinarith [mul_nonneg (pow_pos hr0 3).le (sq_nonneg (1 - θ k))]
  refine ⟨G, X, t, hG, hb, hgl, hhl, fun y => ?_, secondOrderX_zero _ _,
    fun k hk => (hGk k hk).2.2.2, hdata⟩
  have := hGB 0 (by norm_num) ⟪e₀, y⟫
  rwa [iteratedDeriv_zero] at this

/-- **TRε runs on one-dimensional data**, for Corollary 3.5.5 of [cartis2022evaluation]. Let
$G : \mathbb{R} \to \mathbb{R}$ be $C^2$, let $\epsilon \in (0, 1]$ with
$\sqrt{\epsilon} < \Delta_0$, and let $K \in \mathbb{N}$. Let abscissae $X_k$ with $X_0 = 0$ and
steps $t_k$ satisfy:

* for $k \le K$, $|G'(X_k)| \le \epsilon$ holds if and only if $k = K$;
* for $k < K$, $X_{k+1} = X_k + t_k$, $0 < t_k \le \sqrt{\epsilon} / 2$,
  $G''(X_k) \ge \sqrt{\epsilon}$,
$$G'(X_k) + (G''(X_k) + \sqrt{\epsilon}) t_k = 0 \quad\text{and}\quad G(X_k) - G(X_{k+1}) \ge
  -\left(G'(X_k) t_k + \tfrac12 G''(X_k) t_k^2\right).$$

Then there is a TRε run $(x_k, s_k, \Delta_k)$ on the ridge function
$f(x) = G(\langle e_0, x \rangle)$ with $\epsilon_1 = \epsilon$, $\epsilon_* = \sqrt{\epsilon}$,
$\epsilon_2 = +\infty$ and $x_k = X_k e_0$ for all $k$, and $K$ is the first iteration with
$\|\nabla f(x_k)\| \le \epsilon$.

In the construction the radius is constant, $\Delta_k = \Delta_0$, and the steps $s_k = t_k e_0$
are interior exact minimizers of the model with $\rho_k \ge 1$. -/
theorem tre_ridge_run (P : TREpsParams) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hΔ₀ : √ε < P.Δ₀)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) {X t : ℕ → ℝ} {K : ℕ} (hX0 : X 0 = 0)
    (htest : ∀ k ≤ K, (|deriv G (X k)| ≤ ε ↔ K ≤ k))
    (hdata : ∀ k < K, X (k + 1) = X k + t k ∧ 0 < t k ∧ t k ≤ √ε / 2 ∧
      √ε ≤ iteratedDeriv 2 G (X k) ∧
      deriv G (X k) + (iteratedDeriv 2 G (X k) + √ε) * t k = 0 ∧
      -(deriv G (X k) * t k + iteratedDeriv 2 G (X k) * t k ^ 2 / 2) ≤
        G (X k) - G (X (k + 1))) :
    ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ), x 0 = 0 ∧ (∀ k, x k = X k • e₀) ∧
      algorithm_3_4_1 (ridge G e₀) P ε none (√ε) x s Δ ∧
      IsFirstHit (fun k => ‖gradient (ridge G e₀) (x k)‖ ≤ ε) K := by
  set r := √ε with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hε
  set f := ridge G e₀
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => X k • e₀
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => t k • e₀
  have hxe : ∀ k, ⟪e₀, x k⟫ = X k := fun k => inner_e₀_smul _
  have hhit : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) K := by
    refine ⟨?_, fun j hj => ?_⟩
    · simp only; rw [norm_gradient_ridge_e₀ hG, hxe]; exact (htest K le_rfl).2 le_rfl
    · simp only; rw [norm_gradient_ridge_e₀ hG, hxe, htest j hj.le]; exact not_le.2 hj
  have hbefore : ∀ k, (∀ j ≤ k, ¬ stopTest f ε none (x j)) → k < K := fun k hk =>
    not_le.1 fun hle => hk K hle (stopTest_none.2 hhit.test)
  have hstepx : ∀ k < K, x (k + 1) = x k + s k := fun k hk => by
    simp only [x, s]; rw [(hdata k hk).1, add_smul]
  have hstep : ∀ k < K, treStep f P r none (x k) P.Δ₀ (s k) := fun k hk => by
    obtain ⟨-, htk, hsmall, hHr, hst, -⟩ := hdata k hk
    have hts : ‖s k‖ = t k := by
      simp only [s]; rw [norm_smul, norm_e₀, mul_one, Real.norm_of_nonneg htk.le]
    refine ⟨by rw [hts]; linarith, ?_, fun _ => ?_, fun e he => by simp at he⟩
    · have hfx : f (x k) = G (X k) := by simp only [f, ridge_apply, hxe]
      rw [treModel_zero, treModel_ridge hG, hxe, hfx]
      have hg : deriv G (X k) = -((iteratedDeriv 2 G (X k) + r) * t k) := by linarith
      rw [hg]
      have : 0 < (iteratedDeriv 2 G (X k) + r) * t k ^ 2 := by
        have : 0 < iteratedDeriv 2 G (X k) + r := by linarith
        positivity
      nlinarith
    · rw [norm_fderiv_treModel_ridge hG, hxe, hst, abs_zero]
      have := P.θ₁_pos
      positivity
  have hρ : ∀ k < K, 1 ≤ tr2Ratio f (x k) (s k) := fun k hk => by
    obtain ⟨-, htk, -, hHr, hst, hdec⟩ := hdata k hk
    rw [tr2Ratio, Chapter02.tr1Ratio_def]
    have hpred : Chapter02.tr1Model f (x k) (hessianOperator f (x k)) 0 -
        Chapter02.tr1Model f (x k) (hessianOperator f (x k)) (s k) =
        -(deriv G (X k) * t k + iteratedDeriv 2 G (X k) * t k ^ 2 / 2) := by
      have e1 := tr2Model_ridge hG (x k) 0
      have e2 := tr2Model_ridge hG (x k) (t k)
      rw [zero_smul] at e1
      unfold tr2Model at e1 e2
      rw [e1, e2, hxe]
      ring
    have hpos : 0 < -(deriv G (X k) * t k + iteratedDeriv 2 G (X k) * t k ^ 2 / 2) := by
      have hg : deriv G (X k) = -((iteratedDeriv 2 G (X k) + r) * t k) := by linarith
      rw [hg]
      have : 0 < (iteratedDeriv 2 G (X k) / 2 + r) * t k ^ 2 := by
        have : 0 < iteratedDeriv 2 G (X k) / 2 + r := by linarith
        positivity
      nlinarith
    refine one_le_reductionRatio (by rw [hpred]; exact hpos) ?_
    rw [hpred, ← hstepx k hk]
    simp only [f, ridge_apply, hxe]
    linarith
  refine ⟨x, s, fun _ => P.Δ₀, by simp [x, hX0], fun _ => rfl, ?_, hhit⟩
  refine ⟨hε, hε1, fun e he => by simp at he, hr0, ?_, hΔ₀, rfl,
    fun k hk => hstep k (hbefore k hk), fun k hk => ?_⟩
  · rw [Real.sqrt_le_one]; exact hε1
  · have hk' := hbefore k hk
    dsimp only
    rw [hstepx k hk']
    exact Optimization.trAcceptance_of_one_le P.toTRParams (hρ k hk') _ _ P.Δ₀_pos.le

/-- The TRε example of Corollary 3.5.5 of [cartis2022evaluation], on the data (3.5.12). There are
$f_{\mathrm{low}}$, $L_1 \ge 1$, $L_2 \ge 1$ and $B$ with the following property. For all TRε
constants and every $\epsilon \in (0, 1)$ with $\sqrt{\epsilon} < \Delta_0$, there are a $C^2$
function $G : \mathbb{R} \to \mathbb{R}$, abscissae $X_k$ and steps $t_k > 0$ with
$X_{k+1} = X_k + t_k$, $G''(X_k) \ge \sqrt{\epsilon}$ and
$G'(X_k) + (G''(X_k) + \sqrt{\epsilon}) t_k = 0$ for $k < \lceil \epsilon^{-3/2} \rceil$, such
that $f(x) = G(\langle e_0, x \rangle)$ satisfies Assumptions f.Bb, f.gL and f.HL with these
constants and $|f| \le B$, and the points $x_k = X_k e_0$ form a TRε run from $x_0 = 0$ with
$\epsilon_1 = \epsilon$, $\epsilon_* = \sqrt{\epsilon}$ and $\epsilon_2 = +\infty$ that
terminates exactly at iteration $\lceil \epsilon^{-3/2} \rceil$.

The proof combines `CartisGouldToint.Chapter03.tre_slow_data` and
`CartisGouldToint.Chapter03.tre_ridge_run`. -/
theorem tre_slow_example :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ (P : TREpsParams) (ε : ℝ), 0 < ε → ε < 1 →
      √ε < P.Δ₀ → ∃ (G : ℝ → ℝ) (X t : ℕ → ℝ), ContDiff ℝ 2 G ∧
        Chapter02.AssumptionBb (ridge G e₀) flow ∧ Chapter02.AssumptionGL (ridge G e₀) L₁ ∧
        AssumptionHL (ridge G e₀) L₂ ∧ (∀ y, |ridge G e₀ y| ≤ B) ∧
        (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, X (k + 1) = X k + t k ∧ 0 < t k ∧
          √ε ≤ iteratedDeriv 2 G (X k) ∧
          deriv G (X k) + (iteratedDeriv 2 G (X k) + √ε) * t k = 0) ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ), x 0 = 0 ∧ (∀ k, x k = X k • e₀) ∧
          algorithm_3_4_1 (ridge G e₀) P ε none (√ε) x s Δ ∧
          IsFirstHit (fun k => ‖gradient (ridge G e₀) (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ := by
  obtain ⟨flow, L₁, L₂, B, hL₁, hL₂, H⟩ := tre_slow_data
  refine ⟨flow, L₁, L₂, B, hL₁, hL₂, fun P ε hε hε1 hΔ₀ => ?_⟩
  obtain ⟨G, X, t, hG, hb, hgl, hhl, hB, hX0, htest, hdata⟩ := H ε hε hε1
  exact ⟨G, X, t, hG, hb, hgl, hhl, hB, fun k hk => ⟨(hdata k hk).1, (hdata k hk).2.1,
    (hdata k hk).2.2.2.1, (hdata k hk).2.2.2.2.1⟩,
    tre_ridge_run P hε hε1.le hΔ₀ hG hX0 htest hdata⟩

private theorem irn_alg {c r F θ q σ : ℝ} (hc : c ≠ 0) (hF : F ≠ 0)
    (hq : q * (8 * F ^ 3) = σ * c ^ 2) (hθ : θ + q * θ ^ 2 = 1) :
    -2 * r ^ 2 * F + (c⁻¹ * (4 * r * F ^ 2) + σ * (c * (θ * r / (2 * F)))) *
      (c * (θ * r / (2 * F))) = 0 := by
  have e1 : c⁻¹ * (4 * r * F ^ 2) * (c * (θ * r / (2 * F))) = 2 * r ^ 2 * F * θ := by
    field_simp; ring
  have e2 : σ * (c * (θ * r / (2 * F))) * (c * (θ * r / (2 * F))) =
      2 * r ^ 2 * F * (q * θ ^ 2) := by
    rw [show σ * (c * (θ * r / (2 * F))) * (c * (θ * r / (2 * F))) =
      σ * c ^ 2 * (θ ^ 2 * r ^ 2 / (4 * F ^ 2)) by ring, ← hq]
    field_simp
    ring
  rw [add_mul, e1, e2]
  linear_combination (2 * r ^ 2 * F) * hθ

private theorem irn_ratio_alg {c r F θ η : ℝ} (hc : 0 < c) (hr : 0 < r) (hF : 1 / 2 < F)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hη : 2 * η * c ^ 2 ≤ 1) (hη0 : 0 < η) :
    η * (c * (θ * r / (2 * F))) ^ 3 ≤ c * (r ^ 3 / 2) := by
  have hF0 : 0 < F := by linarith
  have e : (c * (θ * r / (2 * F))) ^ 3 = c * c ^ 2 * (θ ^ 3 * r ^ 3 / (8 * F ^ 3)) := by
    field_simp; ring
  have hF3 : 1 < 8 * F ^ 3 := by
    have := pow_lt_pow_left₀ hF (by norm_num) (by norm_num : (3 : ℕ) ≠ 0); norm_num at this
    linarith
  have hθ3 : θ ^ 3 ≤ 1 := pow_le_one₀ hθ0.le hθ1
  have hr3 := pow_pos hr 3
  have h1 : θ ^ 3 * r ^ 3 / (8 * F ^ 3) ≤ r ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  rw [e]
  have h2 : η * c ^ 2 * (θ ^ 3 * r ^ 3 / (8 * F ^ 3)) ≤ r ^ 3 / 2 := by
    have h0 : 0 ≤ θ ^ 3 * r ^ 3 / (8 * F ^ 3) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ η * c ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]

/-- The scaling factor $c = \min(1, (2 \eta)^{-1/2})$ of the iRN example. It satisfies $0 < c \le 1$
and $2 \eta c^2 \le 1$. -/
noncomputable def irnScale (P : IRNParams) : ℝ := min 1 (1 / √(2 * P.η))

/-- The scaling factor of the iRN example is positive: $c > 0$. -/
theorem irnScale_pos (P : IRNParams) : 0 < irnScale P :=
  lt_min one_pos (by have := P.η_pos; positivity)

/-- The scaling factor of the iRN example is at most one: $c \le 1$. -/
theorem irnScale_le_one (P : IRNParams) : irnScale P ≤ 1 := min_le_left _ _

/-- The scaling factor of the iRN example satisfies $2 \eta c^2 \le 1$. -/
theorem two_mul_η_mul_irnScale_sq_le (P : IRNParams) : 2 * P.η * irnScale P ^ 2 ≤ 1 := by
  have hη := P.η_pos
  have h1 : irnScale P ^ 2 ≤ (1 / √(2 * P.η)) ^ 2 :=
    pow_le_pow_left₀ (irnScale_pos P).le (min_le_right _ _) 2
  rw [div_pow, Real.sq_sqrt (by positivity), one_pow] at h1
  calc 2 * P.η * irnScale P ^ 2 ≤ 2 * P.η * (1 / (2 * P.η)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := by field_simp

/-- If $0 < q \le \sigma$, then $\theta = 2 / (1 + \sqrt{1 + 4q})$ is the positive root of
$\theta + q \theta^2 = 1$, and $1 / (1 + \sigma) \le \theta \le 1$. -/
private theorem quad_root_facts {σ q : ℝ} (hq0 : 0 < q) (hqσ : q ≤ σ) :
    2 / (1 + √(1 + 4 * q)) + q * (2 / (1 + √(1 + 4 * q))) ^ 2 = 1 ∧
      0 < 2 / (1 + √(1 + 4 * q)) ∧ 2 / (1 + √(1 + 4 * q)) ≤ 1 ∧
      1 / (1 + σ) ≤ 2 / (1 + √(1 + 4 * q)) := by
  set u := √(1 + 4 * q)
  have hu2 : u ^ 2 = 1 + 4 * q := Real.sq_sqrt (by linarith)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu1 : 1 ≤ u := by nlinarith
  have hu3 : u ≤ 1 + 2 * q := by nlinarith
  refine ⟨?_, by positivity, ?_, ?_⟩
  · field_simp; nlinarith
  · rw [div_le_one (by linarith)]; linarith
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

/-- **Equation (3.5.12)** of [cartis2022evaluation], rescaled for iRN. For all iRN constants there
are $f_{\mathrm{low}}$, $L_1 \ge 1$, $L_2 \ge 1$ and $B$ with the following property. Let
$\epsilon \in (0, 1)$ and $k_\epsilon = \lceil \epsilon^{-3/2} \rceil$. Then there are a $C^2$
function $G : \mathbb{R} \to \mathbb{R}$, abscissae $X_k$ and steps $t_k$ such that:

* the ridge function $f(x) = G(\langle e_0, x \rangle)$ on $\mathbb{R}^1$ satisfies Assumption
  f.Bb with $f_{\mathrm{low}}$, Assumption f.gL with $L_1$ and Assumption f.HL with $L_2$, and
  $|f| \le B$;
* $X_0 = 0$, and for $k \le k_\epsilon$, $|G'(X_k)| \le \epsilon$ holds if and only if
  $k = k_\epsilon$;
* for $k < k_\epsilon$, $X_{k+1} = X_k + t_k$, $0 < t_k \le G''(X_k)$,
$$G'(X_k) + (G''(X_k) + \sigma^U_0 t_k) t_k = 0 \quad\text{and}\quad \eta t_k^3 \le G(X_k) -
  G(X_{k+1}).$$

The equation says that $t_k$ minimizes the cubic model with $\lambda = \sigma^U_0 t_k$, and the
last inequality says that the ratio (3.4.35) is at least $\eta$. The function is
$G(u) = c G_0(u / c)$, where $G_0$ is the function of (3.5.12) and
$c = \min(1, (2 \eta)^{-1/2})$ is `CartisGouldToint.Chapter03.irnScale P`. The derivatives
$G'(X_k)$ are those of (3.5.12). The ratio (3.4.35) is not scale invariant: it becomes $4 f_k^3
/ (c^2 \theta_k^3) \ge 1 / (2 c^2) \ge \eta$. -/
theorem irn_slow_data (P : IRNParams) :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (G : ℝ → ℝ) (X t : ℕ → ℝ), ContDiff ℝ 2 G ∧
        Chapter02.AssumptionBb (ridge G e₀) flow ∧ Chapter02.AssumptionGL (ridge G e₀) L₁ ∧
        AssumptionHL (ridge G e₀) L₂ ∧ (∀ y, |ridge G e₀ y| ≤ B) ∧ X 0 = 0 ∧
        (∀ k ≤ ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, (|deriv G (X k)| ≤ ε ↔ ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ ≤ k)) ∧
        ∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, X (k + 1) = X k + t k ∧ 0 < t k ∧
          t k ≤ iteratedDeriv 2 G (X k) ∧
          deriv G (X k) + (iteratedDeriv 2 G (X k) + P.σU₀ * t k) * t k = 0 ∧
          P.η * t k ^ 3 ≤ G (X k) - G (X (k + 1)) := by
  set σ := P.σU₀
  have hσ : 0 < σ := P.σmin_pos.trans_le P.σmin_le_σU₀
  set c := irnScale P
  have hc0 : 0 < c := irnScale_pos P
  have hc1 : c ≤ 1 := irnScale_le_one P
  have hcη : 2 * P.η * c ^ 2 ≤ 1 := two_mul_η_mul_irnScale_sq_le P
  have hcinv : 1 ≤ c⁻¹ := one_le_inv₀ hc0 |>.2 hc1
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowSecondOrder_run_data (a := 1 / (1 + σ)) (b := 1)
    (by positivity) (by rw [div_le_one (by linarith)]; linarith)
  refine ⟨-(B / c ^ 2), max (B / c ^ 2) 1, max (L / c ^ 2) 1, B / c ^ 2, le_max_right _ _,
    le_max_right _ _, fun ε hε hε1 => ?_⟩
  set r := √ε with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hε
  have hr2 : r ^ 2 = ε := Real.sq_sqrt hε.le
  have hhalf : ε ^ (1 / 2 : ℝ) = r := by rw [hr, Real.sqrt_eq_rpow]
  have h32 : ε ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  set F := secondOrderF ε
  have hF : ∀ k < secondOrderK ε, 1 / 2 < F k ∧ F k ≤ 1 := fun k hk =>
    ⟨secondOrderF_gt_half hε hk, secondOrderF_le_one hε k⟩
  set q : ℕ → ℝ := fun k => σ * c ^ 2 / (8 * F k ^ 3)
  set θ : ℕ → ℝ := fun k => 2 / (1 + √(1 + 4 * q k))
  -- the step factors solve `θ + q θ² = 1` and lie in `[1/(1+σ), 1]`
  have hθq : ∀ k < secondOrderK ε, 0 < q k ∧ q k ≤ σ ∧ θ k + q k * θ k ^ 2 = 1 ∧ 0 < θ k ∧
      θ k ≤ 1 ∧ 1 / (1 + σ) ≤ θ k := fun k hk => by
    obtain ⟨h1, -⟩ := hF k hk
    have hF3 : 1 / 8 < F k ^ 3 := by
      have := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0); norm_num at this
      linarith
    have hq0 : 0 < q k := by simp only [q]; positivity
    have hqσ : q k ≤ σ := by
      have hc2 : c ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc1
      simp only [q]; rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hc2 hσ.le]
    exact ⟨hq0, hqσ, quad_root_facts hq0 hqσ⟩
  have hθ : ∀ k < secondOrderK ε, θ k ∈ Icc (1 / (1 + σ)) 1 := fun k hk =>
    ⟨(hθq k hk).2.2.2.2.2, (hθq k hk).2.2.2.2.1⟩
  obtain ⟨G₀, hG₀, hGL, hGB, hGk⟩ := H ε θ hε hε1 hθ
  -- the rescaled function `G(u) = c G₀(u/c)`
  set G : ℝ → ℝ := fun u => c * G₀ (c⁻¹ * u)
  obtain ⟨hG, hid, hGL', hGB'⟩ := contDiff_two_rescale_bounds hc0 hc1 hG₀ hGL hGB
  have hc2 : c * c⁻¹ ^ 2 = c⁻¹ := by field_simp
  have hc1' : c * c⁻¹ ^ 1 = 1 := by field_simp
  obtain ⟨hb, hgl, -, hhl, -⟩ := ridge_assumptions_two hG hGL' hGB'
  set X₀ := secondOrderX θ ε
  set X : ℕ → ℝ := fun k => c * X₀ k
  set t : ℕ → ℝ := fun k => c * (θ k * r / (2 * F k))
  have hcX : ∀ k, c⁻¹ * X k = X₀ k := fun k => by simp only [X]; field_simp
  have hd : ∀ k, deriv G (X k) = deriv G₀ (X₀ k) := fun k => by
    have := hid 1 (by norm_num) (X k)
    rw [iteratedDeriv_one, iteratedDeriv_one, hc1', one_mul, hcX] at this
    exact this
  have hval : ∀ k ≤ secondOrderK ε, G (X k) = c * F k ∧ deriv G (X k) = -2 * ε * F k ∧
      iteratedDeriv 2 G (X k) = c⁻¹ * (4 * r * F k ^ 2) := fun k hk => by
    obtain ⟨h1, h2, h3, -⟩ := hGk k hk
    refine ⟨by simp only [G]; rw [hcX, h1], by rw [hd, h2]; rfl, ?_⟩
    rw [hid 2 le_rfl, hc2, hcX, h3, secondOrderH_def, hhalf]
  have hXs : ∀ k < secondOrderK ε, X (k + 1) = X k + t k := fun k hk => by
    simp only [X, X₀, t]; rw [secondOrderX_succ, hhalf]; ring
  have hpos : ∀ k < secondOrderK ε, 0 < t k := fun k hk => by
    have := (hF k hk).1; have := (hθq k hk).2.2.2.1; simp only [t]; positivity
  have hstat : ∀ k < secondOrderK ε,
      deriv G (X k) + (iteratedDeriv 2 G (X k) + σ * t k) * t k = 0 := fun k hk => by
    have hFk := (hF k hk).1
    obtain ⟨-, -, hθe, -, -, -⟩ := hθq k hk
    obtain ⟨-, hv2, hv3⟩ := hval k hk.le
    have hF0 : F k ≠ 0 := by linarith
    have hq : q k * (8 * F k ^ 3) = σ * c ^ 2 := by simp only [q]; field_simp
    rw [hv2, hv3, ← hr2]
    simp only [t]
    linear_combination irn_alg hc0.ne' hF0 hq hθe
  have hsmall : ∀ k < secondOrderK ε, t k ≤ iteratedDeriv 2 G (X k) := fun k hk => by
    have hFk := hF k hk
    obtain ⟨-, -, -, hθ0, hθ1, -⟩ := hθq k hk
    rw [(hval k hk.le).2.2]
    have h1 : θ k * r / (2 * F k) ≤ r := by
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left (show θ k ≤ 2 * F k by linarith [hFk.1]) hr0.le
      linarith
    have h2 : r ≤ 4 * r * F k ^ 2 := by
      have : 1 ≤ 4 * F k ^ 2 := by nlinarith [hFk.1]
      have := mul_le_mul_of_nonneg_left this hr0.le
      linarith
    calc t k = c * (θ k * r / (2 * F k)) := rfl
      _ ≤ 1 * r := mul_le_mul hc1 h1
          (div_nonneg (mul_nonneg hθ0.le hr0.le) (by linarith [hFk.1])) zero_le_one
      _ ≤ 1 * (4 * r * F k ^ 2) := by linarith
      _ ≤ c⁻¹ * (4 * r * F k ^ 2) := mul_le_mul_of_nonneg_right hcinv (by positivity)
  have hratio : ∀ k < secondOrderK ε, P.η * t k ^ 3 ≤ G (X k) - G (X (k + 1)) := fun k hk => by
    have hFk := hF k hk
    obtain ⟨-, -, -, hθ0, hθ1, -⟩ := hθq k hk
    rw [(hval k hk.le).1, (hval (k + 1) hk).1,
      show F (k + 1) = F k - ε ^ (3 / 2 : ℝ) / 2 from secondOrderF_succ ε k, h32]
    have := irn_ratio_alg hc0 hr0 hFk.1 hθ0 hθ1 hcη P.η_pos
    simp only [t]
    linarith
  refine ⟨G, X, t, hG, hb, hgl, hhl, fun y => ?_, by simp [X, X₀],
    fun k hk => by rw [hd]; exact (hGk k hk).2.2.2,
    fun k hk => ⟨hXs k hk, hpos k hk, hsmall k hk, hstat k hk, hratio k hk⟩⟩
  have := hGB' 0 (by norm_num) ⟪e₀, y⟫
  rwa [iteratedDeriv_zero] at this

/-- **iRN runs on one-dimensional data**, for Corollary 3.5.5 of [cartis2022evaluation]. Let
$G : \mathbb{R} \to \mathbb{R}$ be $C^2$, let $\epsilon \in (0, 1]$, and let $K \in \mathbb{N}$.
Let abscissae $X_k$ with $X_0 = 0$ and steps $t_k$ satisfy:

* for $k \le K$, $|G'(X_k)| \le \epsilon$ holds if and only if $k = K$;
* for $k < K$, $X_{k+1} = X_k + t_k$, $0 < t_k \le G''(X_k)$,
$$G'(X_k) + (G''(X_k) + \sigma^U_0 t_k) t_k = 0 \quad\text{and}\quad \eta t_k^3 \le G(X_k) -
  G(X_{k+1}).$$

Then there is an iRN run on the ridge function $f(x) = G(\langle e_0, x \rangle)$ with
$\epsilon_1 = \epsilon$, $\epsilon_2 = +\infty$, $Q_k = I$, $x_k = X_k e_0$ and
$\lambda_k = \sigma^U_0 \|s_k\|$ for all $k$, and $K$ is the first iteration with
$\|\nabla f(x_k)\| \le \epsilon$.

In the construction $\sigma^L_k = 0$, $\sigma^U_k = \sigma^U_0$, the steps $s_k = t_k e_0$ are
exact minimizers of the cubic model, and all iterations are successful. -/
theorem irn_ridge_run (P : IRNParams) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G) {X t : ℕ → ℝ} {K : ℕ} (hX0 : X 0 = 0)
    (htest : ∀ k ≤ K, (|deriv G (X k)| ≤ ε ↔ K ≤ k))
    (hdata : ∀ k < K, X (k + 1) = X k + t k ∧ 0 < t k ∧ t k ≤ iteratedDeriv 2 G (X k) ∧
      deriv G (X k) + (iteratedDeriv 2 G (X k) + P.σU₀ * t k) * t k = 0 ∧
      P.η * t k ^ 3 ≤ G (X k) - G (X (k + 1))) :
    ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (lam σL σU : ℕ → ℝ), x 0 = 0 ∧
      (∀ k, x k = X k • e₀) ∧ (∀ k, lam k = P.σU₀ * ‖s k‖) ∧
      algorithm_3_4_2 (ridge G e₀) P ε none x s lam σL σU (fun _ => ⊤) ∧
      IsFirstHit (fun k => ‖gradient (ridge G e₀) (x k)‖ ≤ ε) K := by
  set σ := P.σU₀
  have hσ : 0 < σ := P.σmin_pos.trans_le P.σmin_le_σU₀
  set f := ridge G e₀
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => X k • e₀
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => t k • e₀
  have hxe : ∀ k, ⟪e₀, x k⟫ = X k := fun k => inner_e₀_smul _
  have hhit : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) K := by
    refine ⟨?_, fun j hj => ?_⟩
    · simp only; rw [norm_gradient_ridge_e₀ hG, hxe]; exact (htest K le_rfl).2 le_rfl
    · simp only; rw [norm_gradient_ridge_e₀ hG, hxe, htest j hj.le]; exact not_le.2 hj
  have hstepx : ∀ k < K, x (k + 1) = x k + s k := fun k hk => by
    simp only [x, s]; rw [(hdata k hk).1, add_smul]
  have htest' : ∀ k, (∀ j ≤ k, ¬ irnTest f ε none (x j) ⊤) → k < K := fun k hk =>
    not_le.1 fun hle => hk K hle ⟨hhit.test, by simp⟩
  have hts : ∀ k < K, ‖s k‖ = t k := fun k hk => by
    simp only [s]; rw [norm_smul, norm_e₀, mul_one, Real.norm_of_nonneg (hdata k hk).2.1.le]
  have hgrad0 : ∀ k < K, irnGrad f (x k) (σ * ‖s k‖) (s k) = 0 := fun k hk => by
    rw [hts k hk, irnGrad_ridge hG, hxe, (hdata k hk).2.2.2.1, zero_smul]
  have hstep : ∀ k < K, irnStep f P none (x k) 0 σ (σ * ‖s k‖) ⊤ (s k) := fun k hk => by
    have hg := hgrad0 k hk
    obtain ⟨-, htk, hH, -, -⟩ := hdata k hk
    refine ⟨by rw [zero_mul]; positivity, le_rfl, ?_, ?_, fun h => absurd rfl h⟩
    · rw [hg, inner_zero_right]
      refine le_min (by have := P.κ₁_pos; positivity) ?_
      have hHs : ⟪s k, hessianOperator f (x k) (s k) + (σ * ‖s k‖) • s k⟫ =
          (iteratedDeriv 2 G (X k) + σ * t k) * t k ^ 2 := by
        simp only [s]
        rw [hessianOperator_ridge hG, hxe, hts k hk, smul_smul, smul_smul, ← add_smul,
          inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, norm_e₀]
        simp only [conj_trivial]
        ring
      rw [hHs, hts k hk]
      have := P.κ₂_pos
      have : 0 ≤ (iteratedDeriv 2 G (X k) + σ * t k) * t k ^ 2 := by
        have : 0 ≤ iteratedDeriv 2 G (X k) := htk.le.trans hH
        positivity
      have : 0 ≤ 1 / 2 * P.κ₂ * t k ^ 3 := by positivity
      linarith
    · rw [hg, norm_zero, hts k hk]
      have := P.κ₃_pos
      positivity
  have hρ : ∀ k < K, P.η ≤ irnRatio f (x k) (s k) := fun k hk => by
    have htk := (hdata k hk).2.1
    have hp : 0 < ‖s k‖ ^ 3 := pow_pos (hts k hk ▸ htk) 3
    change P.η ≤ reductionRatio f (x k) (s k) (‖s k‖ ^ 3)
    rw [le_reductionRatio_iff hp, ← hstepx k hk, hts k hk]
    have hfx : ∀ j, f (x j) = G (X j) := fun j => by simp only [f, ridge_apply, hxe]
    rw [hfx, hfx]
    exact (hdata k hk).2.2.2.2
  refine ⟨x, s, fun k => σ * ‖s k‖, fun _ => 0, fun _ => σ, by simp only [x, hX0, zero_smul],
    fun _ => rfl, fun _ => rfl, ⟨hε, hε1, fun e he => by simp at he, rfl, rfl,
      fun k hk hn => ?_, fun k hk => ?_, fun k hk => ?_⟩, hhit⟩
  · have hk' : k < K := by
      rcases lt_trichotomy k K with h | rfl | h
      · exact h
      · exact absurd hhit.test (hn rfl)
      · exact absurd ⟨hhit.test, by simp⟩ (hk K h)
    exact hstep k hk'
  · have hk' := htest' k hk
    dsimp only
    rw [ite_eq_left (hρ k hk'), hstepx k hk']
  · have hk' := htest' k hk
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd (hρ k hk') (not_le.2 h),
      fun h => absurd (hρ k hk') (not_le.2 h)⟩

/-- The iRN example of Corollary 3.5.5 of [cartis2022evaluation], on the rescaled data (3.5.12). For
all iRN constants there are $f_{\mathrm{low}}$, $L_1 \ge 1$, $L_2 \ge 1$ and $B$ with the
following property. For every $\epsilon \in (0, 1)$ there are a $C^2$ function
$G : \mathbb{R} \to \mathbb{R}$, abscissae $X_k$ and steps $t_k > 0$ with $X_{k+1} = X_k + t_k$,
$t_k \le G''(X_k)$ and $G'(X_k) + (G''(X_k) + \sigma^U_0 t_k) t_k = 0$ for
$k < \lceil \epsilon^{-3/2} \rceil$, such that $f(x) = G(\langle e_0, x \rangle)$ satisfies
Assumptions f.Bb, f.gL and f.HL with these constants and $|f| \le B$, and the points
$x_k = X_k e_0$ form an iRN run from $x_0 = 0$ with $\epsilon_1 = \epsilon$,
$\epsilon_2 = +\infty$, $Q_k = I$ and $\lambda_k = \sigma^U_0 \|s_k\|$ that terminates exactly
at iteration $\lceil \epsilon^{-3/2} \rceil$.

The proof combines `CartisGouldToint.Chapter03.irn_slow_data` and
`CartisGouldToint.Chapter03.irn_ridge_run`. In the run $\sigma^L_k = 0$,
$\sigma^U_k = \sigma^U_0$, and all iterations are successful. -/
theorem irn_slow_example (P : IRNParams) :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (G : ℝ → ℝ) (X t : ℕ → ℝ), ContDiff ℝ 2 G ∧
        Chapter02.AssumptionBb (ridge G e₀) flow ∧ Chapter02.AssumptionGL (ridge G e₀) L₁ ∧
        AssumptionHL (ridge G e₀) L₂ ∧ (∀ y, |ridge G e₀ y| ≤ B) ∧
        (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, X (k + 1) = X k + t k ∧ 0 < t k ∧
          t k ≤ iteratedDeriv 2 G (X k) ∧
          deriv G (X k) + (iteratedDeriv 2 G (X k) + P.σU₀ * t k) * t k = 0) ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (lam σL σU : ℕ → ℝ), x 0 = 0 ∧
          (∀ k, x k = X k • e₀) ∧ (∀ k, lam k = P.σU₀ * ‖s k‖) ∧
          algorithm_3_4_2 (ridge G e₀) P ε none x s lam σL σU (fun _ => ⊤) ∧
          IsFirstHit (fun k => ‖gradient (ridge G e₀) (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ := by
  obtain ⟨flow, L₁, L₂, B, hL₁, hL₂, H⟩ := irn_slow_data P
  refine ⟨flow, L₁, L₂, B, hL₁, hL₂, fun ε hε hε1 => ?_⟩
  obtain ⟨G, X, t, hG, hb, hgl, hhl, hB, hX0, htest, hdata⟩ := H ε hε hε1
  exact ⟨G, X, t, hG, hb, hgl, hhl, hB, fun k hk => ⟨(hdata k hk).1, (hdata k hk).2.1,
    (hdata k hk).2.2.1, (hdata k hk).2.2.2.1⟩, irn_ridge_run P hε hε1.le hG hX0 htest hdata⟩

end Examples

end CartisGouldToint.Chapter03
