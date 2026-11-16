/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter03.Section03
import Numlib.Optimization.Complexity.GapRecurrence

/-!
# Cartis, Gould and Toint, Section 5.4: Phase complexity under strict local convexity

This module formalizes Section 5.4 of [cartis2022evaluation]. The second-order
adaptive-regularization algorithm AR2 (Algorithm 3.3.1), in its first-order version with
$\epsilon_2 = +\infty$, is run with the more stringent model-termination test (5.4.3)
$$\|\nabla m_k(s_k)\| \le \theta_1 \min\left(\|\nabla f(x_k)\|, \tfrac12 \|s_k\|^2\right).$$
Near a local minimizer $x_*$ with $\lambda_* = \lambda_{\min}[\nabla^2 f(x_*)] > 0$, the gradient
norms then converge quadratically, $\|\nabla f(x_{k+1})\| \le \|\nabla f(x_k)\|^2/\zeta_*$. This
gives a local iteration count of order $\log_2 \log_2(\zeta_*/\epsilon_1)$, and a global bound that
adds this count to the bound of Lemma 3.3.4 for the iterations far from $x_*$. The algorithm is
`CartisGouldToint.Chapter03.algorithm_3_3_1` with an additional condition on the steps.

## Main definitions

* Equation (5.4.3), `CartisGouldToint.Chapter05.IsAR2StrictRun`: a run of AR2 with
  $\epsilon_2 = +\infty$ whose steps satisfy the model-termination test (5.4.3).
* Equations (5.4.5)–(5.4.6), `CartisGouldToint.Chapter05.zetaStar` and
  `CartisGouldToint.Chapter05.quadRegion`: the corrected radius $\zeta_*$ of quadratic convergence
  and the neighbourhood $\mathcal{Q}_*^1$ of $x_*$.

## Main results

* Lemma 5.4.1, `CartisGouldToint.Chapter05.lemma_5_4_1`:
  $\lambda_{\min}[\nabla^2 f(x)] \ge \lambda_*/2$ on the ball $\mathcal{Q}_*$ of radius
  $q_* = \lambda_*/(4L)$ around $x_*$.
* Lemma 5.4.2, `CartisGouldToint.Chapter05.lemma_5_4_2`: the quadratic decrease (5.4.4) of the
  gradient near $x_*$, and the invariance of $\mathcal{Q}_*^1$, in which every iteration is very
  successful.
* Lemma 5.4.3, `CartisGouldToint.Chapter05.lemma_5_4_3`: from an iterate in the region (5.4.13), the
  run terminates within $\lceil \log_2 \log_2(\zeta_*/\epsilon_1) \rceil_+$ further iterations, all
  very successful.
* Theorem 5.4.4, `CartisGouldToint.Chapter05.theorem_5_4_4`: the global bounds (5.4.16)–(5.4.17) on
  the number of successful iterations.

## Conventions

* $L = L_{f,2}$ is the Lipschitz constant of the Hessian in assumption f.HL,
  `CartisGouldToint.Chapter03.AssumptionHL f L`, which includes $L \ge 1$. Assumption f.Bb is
  `CartisGouldToint.Chapter02.AssumptionBb f f_low`.
* $\lambda_{\min}[\nabla^2 f(x)]$ is `CartisGouldToint.Chapter01.hessianMinEig f x`, and
  $\lambda_* = \lambda_{\min}[\nabla^2 f(x_*)]$.
* $q_* = \lambda_*/(4L)$ (5.4.1), and $\mathcal{Q}_* = \{x : \|x - x_*\| \le q_*\}$.
* $\sigma_{\max}$ of (3.3.14) is `CartisGouldToint.Chapter03.sigmaMaxAR2 P L`, and
  $\kappa^S_{\rm AR2}$ of Lemma 3.3.4 is `CartisGouldToint.Chapter03.kappaSAR2 P L`.
* $\kappa_s = 2(1 + \theta_1)/\lambda_*$ is `CartisGouldToint.Chapter05.kappaStep P λ_*`, $\zeta_*$
  of (5.4.5) is `CartisGouldToint.Chapter05.zetaStar P L λ_*`, and $\mathcal{Q}_*^1$ of (5.4.6) is
  `CartisGouldToint.Chapter05.quadRegion f P L x_*`.
* $\lceil t \rceil_+$ is the least natural number $n \ge t$. The functions `Nat.ceil` and
  `Real.logb 2` are $\lceil \cdot \rceil_+$ and $\log_2$.

## Implementation notes

* Runs exist for every twice continuously differentiable $f$, because a global minimizer of the
  model satisfies (5.4.3): see `CartisGouldToint.Chapter05.exists_isAR2StrictRun`.
* The statements near $x_*$ use of the local minimizer only $\nabla f(x_*) = 0$ and $\lambda_* > 0$.
  The book's strong-convexity argument for $x_{k+1} \in \mathcal{Q}_*$ is replaced by a first-order
  Taylor bound, `CartisGouldToint.Chapter05.mul_norm_sub_le_norm_gradient`.

## Deviations from the source

* **Lemma 5.4.1** (generalization). The book assumes that $x_*$ is a local minimizer with
  $\lambda_* > 0$. The bound holds for every $x_*$. See `CartisGouldToint.Chapter05.lemma_5_4_1`.
* **Lemma 5.4.2, step bound (5.4.8)** (correction). The printed constant
  $(1 + \theta_1)/(\lambda_* + \sigma_{\min}/2)$ is false. The bound holds with
  $\kappa_s = 2(1 + \theta_1)/\lambda_*$, which changes the radius $\zeta_*$ of (5.4.5). See
  `CartisGouldToint.Chapter05.norm_step_le_of_strict`, `CartisGouldToint.Chapter05.zetaStar` and
  `CartisGouldToint.Chapter05.lemma_5_4_2`.
* **Lemma 5.4.3, count (5.4.14)** (correction). The count $\log_2 \log_2(\zeta/\epsilon)$ is one too
  small in the worst case, has no ceiling and is undefined for $\epsilon \ge \zeta$. The count is
  $\lceil \log_2 \log_2(\zeta_*/\epsilon) \rceil_+$, also in Theorem 5.4.4. See
  `CartisGouldToint.Chapter05.lemma_5_4_3` and `CartisGouldToint.Chapter05.theorem_5_4_4`.
* **Theorem 5.4.4, second part** (reading). The bound (5.4.17) is stated, like Lemma 3.3.4, for
  $|\mathcal{S}_k|$ at every iteration $k$ before termination, and the condition (5.4.18) is
  restricted to the iterations before termination. See `CartisGouldToint.Chapter05.theorem_5_4_4`.
-/

open Set Finset Optimization Subproblem
open Optimization hiding ARParams
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter05

open Chapter03

variable {n : ℕ}

/-! ### The AR2 model in inner-product form -/

section Model

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- The corrected step bound (5.4.8) of Lemma 5.4.2 of [cartis2022evaluation], for one step. Let $f$
be twice continuously differentiable at $x$, let $\sigma \ge 0$, $\theta \ge 0$ and $\mu > 0$,
and suppose that $\lambda_{\min}[\nabla^2 f(x)] \ge \mu$. Let
$m(s) = T_{f,2}(x, s) + \frac{\sigma}{6}\|s\|^3$ be the AR2 model at $x$. If a step $s$
satisfies $\|\nabla m(s)\| \le \theta \|\nabla f(x)\|$, which is part of (5.4.3), then
$$\|s\| \le \frac{1 + \theta}{\mu} \|\nabla f(x)\|.$$
With $\mu = \lambda_*/2$ and $\theta = \theta_1$, the factor is
$\kappa_s = 2(1 + \theta_1)/\lambda_*$. -/
theorem norm_step_le_of_strict (hf : ContDiffAt ℝ 2 f x) {σ μ θ : ℝ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ)
    (hμ : 0 < μ)
    (hH : μ ≤ Chapter01.hessianMinEig f x) {s : EuclideanSpace ℝ (Fin n)}
    (hm : ‖fderiv ℝ (ar2Model f x σ) s‖ ≤ θ * ‖gradient f x‖) :
    ‖s‖ ≤ (1 + θ) / μ * ‖gradient f x‖ := by
  set v := gradient f x + hessianOperator f x s + (σ / 2 * ‖s‖) • s
  rw [Chapter03.norm_fderiv_ar2Model hf] at hm
  have hv := Chapter03.inner_ar2ModelGrad_self (f := f) (x := x) σ s
  have hcurv := Chapter03.hessianMinEig_mul_le_inner hf s
  have h1 : ⟪v, s⟫ ≤ ‖v‖ * ‖s‖ := real_inner_le_norm _ _
  have h2 : -⟪gradient f x, s⟫ ≤ ‖gradient f x‖ * ‖s‖ := by
    have := abs_real_inner_le_norm (gradient f x) s
    linarith [neg_abs_le ⟪gradient f x, s⟫]
  have h3 : 0 ≤ σ / 2 * ‖s‖ ^ 3 := by positivity
  have h4 : μ * ‖s‖ ^ 2 ≤ Chapter01.hessianMinEig f x * ‖s‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hH (sq_nonneg _)
  -- `μ ‖s‖² ≤ (1 + θ) ‖∇f(x)‖ ‖s‖`
  have key : μ * ‖s‖ ^ 2 ≤ (1 + θ) * ‖gradient f x‖ * ‖s‖ := by
    have : ‖v‖ * ‖s‖ ≤ θ * ‖gradient f x‖ * ‖s‖ :=
      mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    nlinarith
  rcases (norm_nonneg s).eq_or_lt with h0 | hpos
  · rw [← h0]; have := norm_nonneg (gradient f x); positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
    nlinarith

/-- The model decrease (5.4.10) in the proof of Lemma 5.4.2 of [cartis2022evaluation]. Let $f$ be
twice continuously differentiable at $x$ with $\lambda_{\min}[\nabla^2 f(x)] \ge \mu$, and let
$m$ be the AR2 model at $x$ with weight $\sigma$. If a step $s$ satisfies
$\|\nabla m(s)\| \le \frac{\theta}{2}\|s\|^2$, which is (3.3.5) and follows from (5.4.3), then
$$T_{f,2}(x, 0) - T_{f,2}(x, s) \ge \frac{\mu}{2}\|s\|^2 + \frac{\sigma - \theta}{2}\|s\|^3.$$
-/
theorem taylorDecrement_ge_of_ar2Model (hf : ContDiffAt ℝ 2 f x) {σ μ θ : ℝ}
    (hH : μ ≤ Chapter01.hessianMinEig f x) {s : EuclideanSpace ℝ (Fin n)}
    (hm : ‖fderiv ℝ (ar2Model f x σ) s‖ ≤ θ / 2 * ‖s‖ ^ 2) :
    μ / 2 * ‖s‖ ^ 2 + (σ - θ) / 2 * ‖s‖ ^ 3 ≤ (ftaylorSeries ℝ f x).taylorDecrement 2 s := by
  set v := gradient f x + hessianOperator f x s + (σ / 2 * ‖s‖) • s
  rw [Chapter03.norm_fderiv_ar2Model hf] at hm
  rw [Chapter03.taylorDecrement_two_eq hf]
  have hv := Chapter03.inner_ar2ModelGrad_self (f := f) (x := x) σ s
  have hcurv := Chapter03.hessianMinEig_mul_le_inner hf s
  have h1 : ⟪v, s⟫ ≤ ‖v‖ * ‖s‖ := real_inner_le_norm _ _
  have h2 : ‖v‖ * ‖s‖ ≤ θ / 2 * ‖s‖ ^ 2 * ‖s‖ := mul_le_mul_of_nonneg_right hm (norm_nonneg _)
  have h4 : μ * ‖s‖ ^ 2 ≤ Chapter01.hessianMinEig f x * ‖s‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hH (sq_nonneg _)
  have h5 : θ / 2 * ‖s‖ ^ 2 * ‖s‖ = θ / 2 * ‖s‖ ^ 3 := by ring
  linarith

end Model

/-! ### Lemma 5.4.1 -/

section Convexity

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}

/-- Under assumption f.HL with constant $L$, for all $x, y \in \mathbb{R}^n$,
$$\lambda_{\min}[\nabla^2 f(y)] \ge \lambda_{\min}[\nabla^2 f(x)] - L\|y - x\|.$$
This is the eigenvalue perturbation bound (A.5) of [cartis2022evaluation] applied to the
Hessian. -/
theorem hessianMinEig_sub_le (hf : AssumptionHL f L) (x y : EuclideanSpace ℝ (Fin n)) :
    Chapter01.hessianMinEig f x - L * ‖y - x‖ ≤ Chapter01.hessianMinEig f y := by
  have h1 := abs_minCurvature_sub_le (A := iteratedFDeriv ℝ 2 f x) (B := iteratedFDeriv ℝ 2 f y)
  have h2 := hf.lipschitz x y
  rw [norm_sub_rev x y] at h2
  have := (le_abs_self _).trans (h1.trans h2)
  simp only [Chapter01.hessianMinEig_def]
  linarith

/-- **Lemma 5.4.1** of [cartis2022evaluation] (region of local strong convexity). Let $f$ satisfy
assumption f.HL with constant $L$, let $x_* \in \mathbb{R}^n$, and let
$\lambda_* = \lambda_{\min}[\nabla^2 f(x_*)]$. If $x$ lies in the region $\mathcal{Q}_*$ of
(5.4.1), that is, $\|x - x_*\| \le q_* = \lambda_*/(4L)$, then
$$\lambda_{\min}[\nabla^2 f(x)] \ge \frac{\lambda_*}{2}.$$

**Generalization.** The book assumes that $x_*$ is a local minimizer with $\lambda_* > 0$. The
bound holds for every $x_*$. If $\lambda_* < 0$, the region $\mathcal{Q}_*$ is empty.

The least eigenvalue $\lambda_{\min}$ is `CartisGouldToint.Chapter01.hessianMinEig`, and f.HL is
`CartisGouldToint.Chapter03.AssumptionHL`, which includes $L \ge 1$. -/
theorem lemma_5_4_1 (hf : AssumptionHL f L) {xs x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L)) :
    Chapter01.hessianMinEig f xs / 2 ≤ Chapter01.hessianMinEig f x := by
  have hL := hf.pos
  have h := hessianMinEig_sub_le hf xs x
  have h' : L * ‖x - xs‖ ≤ Chapter01.hessianMinEig f xs / 4 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * L)] at hx
    linarith
  have h0 : 0 ≤ Chapter01.hessianMinEig f xs := by
    have := mul_nonneg hL.le (norm_nonneg (x - xs)); linarith
  linarith

/-- Let $f$ satisfy assumption f.HL with constant $L$, let $\nabla f(x_*) = 0$, and let
$\lambda_* = \lambda_{\min}[\nabla^2 f(x_*)]$. If $\|y - x_*\| \le 2q_* = \lambda_*/(2L)$, then
$$\tfrac34 \lambda_* \|y - x_*\| \le \|\nabla f(y)\|.$$
The proof of Lemma 5.4.2 of [cartis2022evaluation] uses this bound in place of the book's
strong-convexity argument. -/
theorem mul_norm_sub_le_norm_gradient (hf : AssumptionHL f L) {xs y : EuclideanSpace ℝ (Fin n)}
    (hcrit : gradient f xs = 0)
    (hy : ‖y - xs‖ ≤ Chapter01.hessianMinEig f xs / (2 * L)) :
    3 / 4 * Chapter01.hessianMinEig f xs * ‖y - xs‖ ≤ ‖gradient f y‖ := by
  set d := y - xs
  set lam := Chapter01.hessianMinEig f xs
  have hL := hf.pos
  have hyd : y = xs + d := by simp [d]
  have hc := hf.contDiffAt xs
  -- the first-order Taylor error of the gradient
  have hT := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun z _ => hf.contDiffAt z) hf.iteratedFDerivLipschitzOn (mem_univ xs) (mem_univ (xs + d))
    (j := 1) (by norm_num)
  rw [norm_iteratedFDeriv_one_sub] at hT
  norm_num [Nat.factorial] at hT
  -- the derivative of the Taylor polynomial
  have hTd : HasFDerivAt (taylorPolynomial f 2 xs)
      (innerSL ℝ (gradient f xs + hessianOperator f xs d)) d := by
    have heq : taylorPolynomial f 2 xs =
        fun s => f xs + quadModel (gradient f xs) (hessianOperator f xs) s := by
      funext s; exact taylorPolynomial_two_eq_quadModel hc s
    rw [heq]
    exact (hasFDerivAt_quadModel (hessianOperator_isSymmetric hc) d).const_add _
  rw [hTd.fderiv] at hT
  have happ : fderiv ℝ f (xs + d) d ≥
      ⟪gradient f xs + hessianOperator f xs d, d⟫ - L / 2 * ‖d‖ ^ 2 * ‖d‖ := by
    have h1 :=
      (fderiv ℝ f (xs + d) - innerSL ℝ (gradient f xs + hessianOperator f xs d)).le_opNorm d
    have h2 : |(fderiv ℝ f (xs + d) - innerSL ℝ (gradient f xs + hessianOperator f xs d)) d| ≤
        L / 2 * ‖d‖ ^ 2 * ‖d‖ :=
      (Real.norm_eq_abs _ ▸ h1).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
    rw [sub_apply, innerSL_apply_apply] at h2
    linarith [neg_abs_le (fderiv ℝ f (xs + d) d - ⟪gradient f xs + hessianOperator f xs d, d⟫)]
  rw [hcrit, zero_add, real_inner_comm] at happ
  have hcurv := Chapter03.hessianMinEig_mul_le_inner hc d
  have hup : fderiv ℝ f (xs + d) d ≤ ‖gradient f y‖ * ‖d‖ := by
    rw [← hyd, norm_gradient_eq]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ (fderiv ℝ f y).le_opNorm d)
  have hLd : L / 2 * ‖d‖ ≤ lam / 4 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)] at hy
    linarith
  have key : 3 / 4 * lam * ‖d‖ ^ 2 ≤ ‖gradient f y‖ * ‖d‖ := by
    have : L / 2 * ‖d‖ ^ 2 * ‖d‖ ≤ lam / 4 * ‖d‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hLd (sq_nonneg ‖d‖)
      nlinarith [norm_nonneg d]
    linarith
  rcases (norm_nonneg d).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · nlinarith

end Convexity

/-! ### The constants of Lemma 5.4.2 -/

section Constants

/-- The step-bound constant $\kappa_s = 2(1 + \theta_1)/\lambda$ of the corrected bound (5.4.8) of
[cartis2022evaluation], with $\lambda = \lambda_*$. The book prints
$(1 + \theta_1)/(\lambda_* + \sigma_{\min}/2)$. The value here is the factor of
`CartisGouldToint.Chapter05.norm_step_le_of_strict` for $\mu = \lambda_*/2$. -/
noncomputable def kappaStep (P : AR2Params) (lam : ℝ) : ℝ := 2 * (1 + P.θ₁) / lam

/-- If $\lambda > 0$, then $\kappa_s > 0$. -/
theorem kappaStep_pos (P : AR2Params) {lam : ℝ} (hlam : 0 < lam) : 0 < kappaStep P lam := by
  have := P.θ₁_pos; unfold kappaStep; positivity

/-- The first four terms of the corrected radius (5.4.5) of [cartis2022evaluation]:
$$\min\left[\frac{2}{(L + \theta_1 + \sigma_{\max})\kappa_s^2}, \frac{\lambda}{4L\kappa_s},
  \frac{\lambda^2}{16L}, \frac{3(1 - \eta_2)\lambda}{4L\kappa_s}\right],$$
with $\kappa_s$ = `CartisGouldToint.Chapter05.kappaStep P λ` and $\sigma_{\max}$ =
`CartisGouldToint.Chapter03.sigmaMaxAR2 P L`. -/
noncomputable def zetaStarBase (P : AR2Params) (L lam : ℝ) : ℝ :=
  min (2 / ((L + P.θ₁ + sigmaMaxAR2 P L) * kappaStep P lam ^ 2))
    (min (lam / (4 * L * kappaStep P lam))
      (min (lam ^ 2 / (16 * L)) (3 * (1 - P.η₂) * lam / (4 * L * kappaStep P lam))))

/-- **Equation (5.4.5)** of [cartis2022evaluation], corrected: the **radius $\zeta_*$ of quadratic
convergence**. With $\lambda = \lambda_*$, it is the minimum of the first four terms
(`CartisGouldToint.Chapter05.zetaStarBase P L λ`) if $\theta_1 \le \sigma_{\min}$, and the
minimum of these terms and $\lambda/(4(\theta_1 - \sigma_{\min})\kappa_s)$ if
$\sigma_{\min} < \theta_1$.

**Correction.** The printed terms contain the factor
$(\lambda_* + \sigma_{\min}/2)/(1 + \theta_1)$, which comes from the false step bound (5.4.8).
Here each such factor is $1/\kappa_s$, with $\kappa_s = 2(1 + \theta_1)/\lambda_*$ (see
`CartisGouldToint.Chapter05.lemma_5_4_2`). The printed last term $\lambda_*/(4\max(\theta_1 -
\sigma_{\min}, 0)) \cdot 1/\kappa_s$ is absent when $\theta_1 \le \sigma_{\min}$. -/
noncomputable def zetaStar (P : AR2Params) (L lam : ℝ) : ℝ :=
  if P.σmin < P.θ₁ then
    min (zetaStarBase P L lam) (lam / (4 * (P.θ₁ - P.σmin) * kappaStep P lam))
  else zetaStarBase P L lam

variable {P : AR2Params} {L lam : ℝ}

/-- The radius $\zeta_*$ is at most the minimum of the first four terms of (5.4.5). -/
theorem zetaStar_le_base : zetaStar P L lam ≤ zetaStarBase P L lam := by
  unfold zetaStar; split_ifs <;> simp

/-- If $L > 0$ and $\lambda > 0$, then $\zeta_* > 0$. -/
theorem zetaStar_pos (hL : 0 < L) (hlam : 0 < lam) : 0 < zetaStar P L lam := by
  have hκ := kappaStep_pos P hlam
  have := P.θ₁_pos; have := arSigmaMax_pos P.ar L; have := P.ar.one_sub_η₂_pos
  have hb : 0 < zetaStarBase P L lam := by
    unfold zetaStarBase
    have : 0 < L + P.θ₁ + sigmaMaxAR2 P L := by linarith
    refine lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) ?_))
    have : 0 < 1 - P.η₂ := P.ar.one_sub_η₂_pos
    positivity
  unfold zetaStar
  split_ifs with h
  · exact lt_min hb (by have : 0 < P.θ₁ - P.σmin := sub_pos.2 h; positivity)
  · exact hb

/-- If $L > 0$ and $\lambda > 0$, then $\zeta_* (L + \theta_1 + \sigma_{\max}) \kappa_s^2 \le 2$.
This is the first term of (5.4.5). -/
theorem zetaStar_mul_le_newton (hL : 0 < L) (hlam : 0 < lam) :
    zetaStar P L lam * ((L + P.θ₁ + sigmaMaxAR2 P L) * kappaStep P lam ^ 2) ≤ 2 := by
  have hκ := kappaStep_pos P hlam
  have := P.θ₁_pos; have := arSigmaMax_pos P.ar L
  have hC : 0 < (L + P.θ₁ + sigmaMaxAR2 P L) * kappaStep P lam ^ 2 := by
    have : 0 < L + P.θ₁ + sigmaMaxAR2 P L := by linarith
    positivity
  rw [← le_div_iff₀ hC]
  exact zetaStar_le_base.trans (min_le_left _ _)

/-- If $L > 0$ and $\lambda > 0$, then $\kappa_s \zeta_* \le \lambda/(4L) = q_*$. This is the second
term of (5.4.5). -/
theorem kappaStep_mul_zetaStar_le_region (hL : 0 < L) (hlam : 0 < lam) :
    kappaStep P lam * zetaStar P L lam ≤ lam / (4 * L) := by
  have hκ := kappaStep_pos P hlam
  have h : zetaStar P L lam ≤ lam / (4 * L * kappaStep P lam) :=
    zetaStar_le_base.trans ((min_le_right _ _).trans (min_le_left _ _))
  rw [le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The radius satisfies $\zeta_* \le \lambda^2/(16L)$. This is the third term of (5.4.5). -/
theorem zetaStar_le_sq : zetaStar P L lam ≤ lam ^ 2 / (16 * L) :=
  zetaStar_le_base.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))

/-- If $L > 0$ and $\lambda > 0$, then $\kappa_s \zeta_* \le 3(1 - \eta_2)\lambda/(4L)$. This is the
fourth term of (5.4.5). -/
theorem kappaStep_mul_zetaStar_le_ratio (hL : 0 < L) (hlam : 0 < lam) :
    kappaStep P lam * zetaStar P L lam ≤ 3 * (1 - P.η₂) * lam / (4 * L) := by
  have hκ := kappaStep_pos P hlam
  have h : zetaStar P L lam ≤ 3 * (1 - P.η₂) * lam / (4 * L * kappaStep P lam) :=
    zetaStar_le_base.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  rw [le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- If $\lambda > 0$ and $\sigma_{\min} < \theta_1$, then $\kappa_s \zeta_* \le
\lambda/(4(\theta_1 - \sigma_{\min}))$. This is the last term of (5.4.5). -/
theorem kappaStep_mul_zetaStar_le_reg (hlam : 0 < lam) (h : P.σmin < P.θ₁) :
    kappaStep P lam * zetaStar P L lam ≤ lam / (4 * (P.θ₁ - P.σmin)) := by
  have hκ := kappaStep_pos P hlam
  have hθ : 0 < P.θ₁ - P.σmin := sub_pos.2 h
  have h' : zetaStar P L lam ≤ lam / (4 * (P.θ₁ - P.σmin) * kappaStep P lam) := by
    unfold zetaStar; simp only [h, ↓reduceIte]; exact min_le_right _ _
  rw [le_div_iff₀ (by positivity)] at h'
  rw [le_div_iff₀ (by positivity)]
  linarith

end Constants

/-- The neighbourhood (5.4.6) of [cartis2022evaluation]:
$$\mathcal{Q}_*^1 = \{x : \|x - x_*\| \le \lambda_*/(4L), \ \|\nabla f(x)\| \le \zeta_*\},$$
the intersection of the region $\mathcal{Q}_*$ of (5.4.1) with the set where the gradient norm
is at most $\zeta_*$. Here $\lambda_* = \lambda_{\min}[\nabla^2 f(x_*)]$ and $\zeta_*$ =
`CartisGouldToint.Chapter05.zetaStar P L λ_*`. -/
def quadRegion (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (L : ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L) ∧
    ‖gradient f x‖ ≤ zetaStar P L (Chapter01.hessianMinEig f xs)}

/-- A point $x$ lies in $\mathcal{Q}_*^1$ if and only if $\|x - x_*\| \le \lambda_*/(4L)$ and
$\|\nabla f(x)\| \le \zeta_*$. -/
theorem mem_quadRegion {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {L : ℝ}
    {xs x : EuclideanSpace ℝ (Fin n)} :
    x ∈ quadRegion f P L xs ↔ ‖x - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L) ∧
      ‖gradient f x‖ ≤ zetaStar P L (Chapter01.hessianMinEig f xs) :=
  Iff.rfl

/-! ### AR2 with the model-termination test (5.4.3) -/

/-- **Equation (5.4.3)** of [cartis2022evaluation]: AR2 with the more stringent model-termination
test. Let $f : \mathbb{R}^n \to \mathbb{R}$, let $P$ be the constants of Algorithm 3.3.1, and
let $\epsilon_1 \in \mathbb{R}$. Sequences of iterates $x_k$, steps $s_k$ and weights $\sigma_k$
form a **run of AR2 with the test (5.4.3)** if they form a run of AR2 (Algorithm 3.3.1) with the
tolerance $\epsilon_1 \in (0, 1]$ and $\epsilon_2 = +\infty$, and if every step $s_k$ computed
before termination also satisfies $\|\nabla m_k(s_k)\| \le \theta_1 \|\nabla f(x_k)\|$. Together
with the condition (3.3.5) $\|\nabla m_k(s_k)\| \le \frac{\theta_1}{2}\|s_k\|^2$ of AR2, this is
(5.4.3):
$$\|\nabla m_k(s_k)\| \le \theta_1 \min\left(\|\nabla f(x_k)\|, \tfrac12 \|s_k\|^2\right).$$

The run of AR2 is `CartisGouldToint.Chapter03.algorithm_3_3_1 f P ε₁ none x s σ`, where `none`
stands for $\epsilon_2 = +\infty$. An iteration $k$ is before termination if
$\|\nabla f(x_j)\| > \epsilon_1$ for all $j \le k$. -/
structure IsAR2StrictRun (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (ε₁ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- The sequences form a run of AR2 with $\epsilon_2 = +\infty$. -/
  toAlgorithm_3_3_1 : algorithm_3_3_1 f P ε₁ none x s σ
  /-- Every step before termination satisfies $\|\nabla m_k(s_k)\| \le \theta_1 \|\nabla f(x_k)\|$,
  the additional part of (5.4.3). -/
  strict : ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) →
    ‖fderiv ℝ (ar2Model f (x k) (σ k)) (s k)‖ ≤ P.θ₁ * ‖gradient f (x k)‖

/-- Runs of AR2 with the test (5.4.3) exist. For a twice continuously differentiable $f$, every
$\epsilon_1 \in (0, 1]$ and every $x_0 \in \mathbb{R}^n$, there is such a run that starts at
$x_0$. A global minimizer of the model has $\nabla m_k(s_k) = 0$, and it is an admissible step. -/
theorem exists_isAR2StrictRun {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (P : AR2Params) {ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ IsAR2StrictRun f P ε₁ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.ar (Inv := fun _ => True)
    (test := stopTest f ε₁ none)
    (stepOK := fun y σ s => ar2Step f P none y σ s ∧
      ‖fderiv ℝ (ar2Model f y σ) s‖ ≤ P.θ₁ * ‖gradient f y‖)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement 2 t))
    (fun y σ _ _ hσ hnot => by
      obtain ⟨s, hmin, hd, -, -⟩ := exists_isMinOn_regularizedModel
        (D := ftaylorSeries ℝ f y) (p := 2) hσ (by norm_num)
      have hg : gradient f y ≠ 0 := by
        intro h0
        exact hnot (stopTest_none.2 (by rw [h0, norm_zero]; exact hε₁.le))
      have hdec : ar2Model f y σ s < ar2Model f y σ 0 := by
        refine regularizedModel_lt_of_isMinOn_of_fderiv_ne_zero hmin ?_
        rw [fderiv_regularizedModel_ftaylorSeries_zero hf.contDiffAt (by norm_num)]
        intro h0
        exact hg (by rw [← norm_eq_zero, norm_gradient_eq, h0, norm_zero])
      refine ⟨s, ⟨ar2Step_of_isMinOn P none hmin hdec, ?_⟩, trivial⟩
      change ‖fderiv ℝ (regularizedModel (ftaylorSeries ℝ f y) 2 σ) s‖ ≤ _
      rw [hd, norm_zero]
      have := P.θ₁_pos
      positivity) trivial
  refine ⟨x, s, σ, hx0, ⟨⟨hε₁, hε₁1, (fun e he => by cases he), hrun.mono fun _ h => h.1⟩,
    fun k hk => (hrun.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)).2⟩⟩

/-! ### Lemma 5.4.2 -/

section Lemma542

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ L : ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ} {xs : EuclideanSpace ℝ (Fin n)}

/-- A local minimizer $x_*$ of $f$ satisfies $\nabla f(x_*) = 0$. If $f$ is not differentiable at
$x_*$, the gradient is $0$ by the convention of `gradient`. -/
theorem gradient_eq_zero_of_isLocalMin (hmin : IsLocalMin f xs) : gradient f xs = 0 := by
  rw [← norm_eq_zero, norm_gradient_eq, hmin.fderiv_eq_zero, norm_zero]

namespace IsAR2StrictRun

/-- The corrected step bound (5.4.8) along a run. Let $f$ satisfy assumption f.HL with constant $L$,
let $\lambda_* > 0$, and let $(x_k, s_k, \sigma_k)$ be a run of AR2 with the test (5.4.3). If
iteration $k$ is before termination and $\|x_k - x_*\| \le q_*$, then
$\|s_k\| \le \kappa_s \|\nabla f(x_k)\|$ with $\kappa_s = 2(1 + \theta_1)/\lambda_*$. -/
theorem norm_step_le (hf : AssumptionHL f L) (h : IsAR2StrictRun f P ε₁ x s σ)
    (hlam : 0 < Chapter01.hessianMinEig f xs) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j))
    (hx : ‖x k - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L)) :
    ‖s k‖ ≤ kappaStep P (Chapter01.hessianMinEig f xs) * ‖gradient f (x k)‖ := by
  have hσ := h.toAlgorithm_3_3_1.sigma_pos (fun j hj => hk j hj.le)
  have h1 := norm_step_le_of_strict (hf.contDiffAt (x k)) hσ.le P.θ₁_pos.le
    (by linarith : 0 < Chapter01.hessianMinEig f xs / 2) (lemma_5_4_1 hf hx) (h.strict k hk)
  have : (1 + P.θ₁) / (Chapter01.hessianMinEig f xs / 2) =
      kappaStep P (Chapter01.hessianMinEig f xs) := by
    unfold kappaStep; field_simp
  rwa [this] at h1

/-- The quadratic decrease (5.4.4), the first part of Lemma 5.4.2 of [cartis2022evaluation]. Let $f$
satisfy assumption f.HL with constant $L$, let $\lambda_* > 0$, and let $(x_k, s_k, \sigma_k)$
be a run of AR2 with the test (5.4.3). If iteration $k$ is before termination and successful
($\rho_k \ge \eta_1$), and $\|x_k - x_*\| \le q_*$, then
$$\|\nabla f(x_{k+1})\| \le \frac{\|\nabla f(x_k)\|^2}{\zeta_*}.$$
-/
theorem norm_gradient_succ_le (hf : AssumptionHL f L) (h : IsAR2StrictRun f P ε₁ x s σ)
    (hlam : 0 < Chapter01.hessianMinEig f xs) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j))
    (hx : ‖x k - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L))
    (hs : P.η₁ ≤ taylorRatio f 2 x s k) :
    ‖gradient f (x (k + 1))‖ ≤
      ‖gradient f (x k)‖ ^ 2 / zetaStar P L (Chapter01.hessianMinEig f xs) := by
  set lam := Chapter01.hessianMinEig f xs
  set κ := kappaStep P lam
  set ζ := zetaStar P L lam
  set C := L + P.θ₁ + sigmaMaxAR2 P L
  have hL := hf.pos
  have hζ : 0 < ζ := zetaStar_pos hL hlam
  have hC : 0 < C := by have := P.θ₁_pos; have := arSigmaMax_pos P.ar L; simp only [C]; linarith
  have h3 := lemma_3_3_3 hf h.toAlgorithm_3_3_1 hk hs
  have hst := h.norm_step_le hf hlam hk hx
  have hst2 : ‖s k‖ ^ 2 ≤ κ ^ 2 * ‖gradient f (x k)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hst 2
  have hN : ζ * (C * κ ^ 2) ≤ 2 := zetaStar_mul_le_newton hL hlam
  have e1 : 2 * ‖gradient f (x (k + 1))‖ ≤ C * ‖s k‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC] at h3; linarith
  rw [le_div_iff₀ hζ]
  have : 2 * (‖gradient f (x (k + 1))‖ * ζ) ≤ 2 * ‖gradient f (x k)‖ ^ 2 :=
    calc 2 * (‖gradient f (x (k + 1))‖ * ζ) = (2 * ‖gradient f (x (k + 1))‖) * ζ := by ring
      _ ≤ (C * ‖s k‖ ^ 2) * ζ := by gcongr
      _ ≤ (C * (κ ^ 2 * ‖gradient f (x k)‖ ^ 2)) * ζ := by gcongr
      _ = (ζ * (C * κ ^ 2)) * ‖gradient f (x k)‖ ^ 2 := by ring
      _ ≤ 2 * ‖gradient f (x k)‖ ^ 2 := by gcongr
  linarith

/-- One iteration in $\mathcal{Q}_*^1$, from the proof of Lemma 5.4.2 of [cartis2022evaluation]. Let
$f$ satisfy assumption f.HL with constant $L$, let $\nabla f(x_*) = 0$ and $\lambda_* > 0$, and
let $(x_k, s_k, \sigma_k)$ be a run of AR2 with the test (5.4.3). If $x_k \in \mathcal{Q}_*^1$
and iteration $k$ is before termination, then iteration $k$ is very successful,
$\rho_k \ge \eta_2$, and $x_{k+1} \in \mathcal{Q}_*^1$. The proof uses the bounds
(5.4.9)–(5.4.12). -/
theorem succ_mem_quadRegion (hf : AssumptionHL f L) (h : IsAR2StrictRun f P ε₁ x s σ)
    (hcrit : gradient f xs = 0) (hlam : 0 < Chapter01.hessianMinEig f xs) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) (hx : x k ∈ quadRegion f P L xs) :
    P.η₂ ≤ taylorRatio f 2 x s k ∧ x (k + 1) ∈ quadRegion f P L xs := by
  set lam := Chapter01.hessianMinEig f xs
  set κ := kappaStep P lam
  set ζ := zetaStar P L lam
  obtain ⟨hxk, hgk⟩ := hx
  have hL := hf.pos
  have hκ : 0 < κ := kappaStep_pos P hlam
  have hζ : 0 < ζ := zetaStar_pos hL hlam
  have hA := h.toAlgorithm_3_3_1
  have hσ := hA.sigma_pos (fun j hj => hk j hj.le)
  have hσmin := hA.sigmaMin_le (fun j hj => hk j hj.le)
  have hst := h.norm_step_le hf hlam hk hxk
  have hsz : ‖s k‖ ≤ κ * ζ := hst.trans (mul_le_mul_of_nonneg_left hgk hκ.le)
  have hc := hf.contDiffAt (x k)
  have hdec := taylorDecrement_ge_of_ar2Model hc (lemma_5_4_1 hf hxk) (hA.step hk).2.1
  set Δ := (ftaylorSeries ℝ f (x k)).taylorDecrement 2 (s k)
  have hs0 := norm_nonneg (s k)
  -- (5.4.12): `Δ ≥ λ_*/8 ‖s_k‖²`
  have hΔ8 : lam / 8 * ‖s k‖ ^ 2 ≤ Δ := by
    have hs3 : ‖s k‖ ^ 3 = ‖s k‖ * ‖s k‖ ^ 2 := by ring
    by_cases hθ : P.σmin < P.θ₁
    · have hr := kappaStep_mul_zetaStar_le_reg (L := L) hlam hθ
      have hθ' : 0 < P.θ₁ - P.σmin := sub_pos.2 hθ
      rw [le_div_iff₀ (by positivity)] at hr
      have h1 : (P.θ₁ - σ k) * ‖s k‖ ≤ (P.θ₁ - P.σmin) * ‖s k‖ :=
        mul_le_mul_of_nonneg_right (by linarith) hs0
      have h2 : (P.θ₁ - P.σmin) * ‖s k‖ ≤ (P.θ₁ - P.σmin) * (κ * ζ) :=
        mul_le_mul_of_nonneg_left hsz hθ'.le
      have h3 : (P.θ₁ - σ k) * ‖s k‖ ≤ lam / 4 := by nlinarith
      have h4 : (P.θ₁ - σ k) * ‖s k‖ * ‖s k‖ ^ 2 ≤ lam / 4 * ‖s k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      nlinarith
    · push Not at hθ
      have : 0 ≤ (σ k - P.θ₁) / 2 * ‖s k‖ ^ 3 :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
  have hΔpos : 0 < Δ := lt_of_le_of_lt (by positivity) (lemma_3_3_1 hA hk)
  -- (5.4.9)
  have hT := abs_sub_taylorPolynomial_le_of_lipschitz convex_univ (fun y _ => hf.contDiffAt y)
    hf.iteratedFDerivLipschitzOn (mem_univ (x k)) (mem_univ (x k + s k))
  norm_num [Nat.factorial] at hT
  have hLs : L * ‖s k‖ ≤ 3 * (1 - P.η₂) * lam / 4 := by
    have hr := kappaStep_mul_zetaStar_le_ratio (P := P) hL hlam
    rw [le_div_iff₀ (by positivity)] at hr
    nlinarith
  have hη := P.ar.one_sub_η₂_pos
  have hratio : P.η₂ ≤ taylorRatio f 2 x s k := by
    have hle : |f (x k + s k) - (f (x k) - Δ)| ≤ (1 - P.η₂) * Δ := by
      rw [show f (x k) - Δ = taylorPolynomial f 2 (x k) (s k) from
        Chapter03.sub_taylorDecrement_eq 2 (s k)]
      calc |f (x k + s k) - taylorPolynomial f 2 (x k) (s k)| ≤ L / 6 * ‖s k‖ ^ 3 := hT
        _ = (L * ‖s k‖) / 6 * ‖s k‖ ^ 2 := by ring
        _ ≤ (3 * (1 - P.η₂) * lam / 4) / 6 * ‖s k‖ ^ 2 := by gcongr
        _ = (1 - P.η₂) * (lam / 8 * ‖s k‖ ^ 2) := by ring
        _ ≤ (1 - P.η₂) * Δ := by gcongr
    have := le_reductionRatio_of_abs_sub_le hΔpos hle
    rw [taylorRatio_def]
    linarith
  have hsucc : P.η₁ ≤ taylorRatio f 2 x s k := P.η₁_le_η₂.trans hratio
  have hxs : x (k + 1) = x k + s k :=
    hA.run.eq_add_of_succ (IsARRun.forall_le_not_stop_iff.2 hk) hsucc
  have hg' := h.norm_gradient_succ_le hf hlam hk hxk hsucc
  have hg'ζ : ‖gradient f (x (k + 1))‖ ≤ ζ := by
    refine hg'.trans ?_
    rw [div_le_iff₀ hζ]
    have := norm_nonneg (gradient f (x k))
    nlinarith
  have hdist : ‖x (k + 1) - xs‖ ≤ lam / (2 * L) := by
    have hreg := kappaStep_mul_zetaStar_le_region (P := P) hL hlam
    calc ‖x (k + 1) - xs‖ = ‖(x k - xs) + s k‖ := by rw [hxs]; congr 1; abel
      _ ≤ ‖x k - xs‖ + ‖s k‖ := norm_add_le _ _
      _ ≤ lam / (4 * L) + lam / (4 * L) := add_le_add hxk (hsz.trans hreg)
      _ = lam / (2 * L) := by field_simp; ring
  have hm := mul_norm_sub_le_norm_gradient hf hcrit hdist
  refine ⟨hratio, ?_, hg'ζ⟩
  have hsq : ζ ≤ lam ^ 2 / (16 * L) := zetaStar_le_sq
  have h1 : 3 / 4 * lam * ‖x (k + 1) - xs‖ * (16 * L) ≤ lam ^ 2 :=
    (le_div_iff₀ (by positivity)).1 ((hm.trans hg'ζ).trans hsq)
  have h2 : 12 * L * ‖x (k + 1) - xs‖ ≤ lam :=
    le_of_mul_le_mul_right (by nlinarith) hlam
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (x (k + 1) - xs)]

/-- The invariance of $\mathcal{Q}_*^1$, the second part of Lemma 5.4.2 of [cartis2022evaluation].
Let $f$ satisfy assumption f.HL with constant $L$, let $\nabla f(x_*) = 0$ and $\lambda_* > 0$,
and let $(x_k, s_k, \sigma_k)$ be a run of AR2 with the test (5.4.3). If
$x_{k_0} \in \mathcal{Q}_*^1$, then $x_k \in \mathcal{Q}_*^1$ for every $k \ge k_0$ such that
the run has not terminated at any iteration $j < k$, that is, up to and including the
termination index. -/
theorem mem_quadRegion_of_ge (hf : AssumptionHL f L) (h : IsAR2StrictRun f P ε₁ x s σ)
    (hcrit : gradient f xs = 0) (hlam : 0 < Chapter01.hessianMinEig f xs) {k₀ : ℕ}
    (h₀ : x k₀ ∈ quadRegion f P L xs) :
    ∀ k, k₀ ≤ k → (∀ j < k, ¬ stopTest f ε₁ none (x j)) → x k ∈ quadRegion f P L xs := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => h₀
  | succ k _ ih =>
    intro hlt
    exact (h.succ_mem_quadRegion hf hcrit hlam (fun j hj => hlt j (Nat.lt_succ_of_le hj))
      (ih fun j hj => hlt j (hj.trans k.lt_succ_self))).2

end IsAR2StrictRun

/-- **Lemma 5.4.2** of [cartis2022evaluation] (region of quadratic convergence). Let $f$ satisfy
assumption f.HL with constant $L$, let $x_*$ be a local minimizer of $f$ with $\lambda_* =
\lambda_{\min}[\nabla^2 f(x_*)] > 0$, and let $(x_k, s_k, \sigma_k)$ be a run of AR2 with the
model-termination test (5.4.3). Let $q_* = \lambda_*/(4L)$, and let $\zeta_*$ be the corrected
radius (5.4.5). Then two statements hold. First, for every successful iteration $k$ before
termination with $\|x_k - x_*\| \le q_*$,
$$\|\nabla f(x_{k+1})\| \le \frac{\|\nabla f(x_k)\|^2}{\zeta_*}. \qquad (5.4.4)$$
Second, if $x_{k_0} \in \mathcal{Q}_*^1$ (5.4.6), then for every $k \ge k_0$ before termination,
$x_k \in \mathcal{Q}_*^1$, iteration $k$ is very successful ($\rho_k \ge \eta_2$), and (5.4.4)
holds.

**Correction.** The book proves the step bound (5.4.8), $\|s_k\| \le \frac{1 +
\theta_1}{\lambda_* + \sigma_{\min}/2}\|\nabla f(x_k)\|$, from $(\lambda_* +
\sigma_{\min}/2)\|s_k\|^2 \le \langle s_k, (\nabla^2 f(x_k) + \frac{\sigma_k}{2} I) s_k\rangle$.
This uses $\lambda_{\min}[\nabla^2 f(x_k)] \ge \lambda_*$, while only $\lambda_*/2$ is available
on $\mathcal{Q}_*$ (5.4.7). It also drops the factor $\|s_k\|$ of the regularization term of the
model gradient $\nabla f(x_k) + \nabla^2 f(x_k) s_k + \frac{\sigma_k}{2}\|s_k\| s_k$ (3.3.2).
The printed constant is false: for $\theta_1 < 1$, $\sigma_{\min} \to 0$,
$\nabla^2 f(x_k) = \frac{\lambda_*}{2} I$ and an exact model minimizer,
$\|s_k\| \approx 2\|\nabla f(x_k)\|/\lambda_*$. The correct constant is
$\kappa_s = 2(1 + \theta_1)/\lambda_*$ (`CartisGouldToint.Chapter05.norm_step_le_of_strict`),
and the radius $\zeta_*$ of (5.4.5) changes accordingly (`CartisGouldToint.Chapter05.zetaStar`).

The proof uses of the local minimizer only $\nabla f(x_*) = 0$. It replaces the book's
strong-convexity argument for $x_{k+1} \in \mathcal{Q}_*$ by the bound
`CartisGouldToint.Chapter05.mul_norm_sub_le_norm_gradient`. -/
theorem lemma_5_4_2 (hf : AssumptionHL f L) (hmin : IsLocalMin f xs)
    (hlam : 0 < Chapter01.hessianMinEig f xs) (h : IsAR2StrictRun f P ε₁ x s σ) :
    (∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) →
        ‖x k - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L) →
        P.η₁ ≤ taylorRatio f 2 x s k →
        ‖gradient f (x (k + 1))‖ ≤
          ‖gradient f (x k)‖ ^ 2 / zetaStar P L (Chapter01.hessianMinEig f xs)) ∧
      ∀ k₀, x k₀ ∈ quadRegion f P L xs → ∀ k, k₀ ≤ k →
        (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) →
        x k ∈ quadRegion f P L xs ∧ P.η₂ ≤ taylorRatio f 2 x s k ∧
          ‖gradient f (x (k + 1))‖ ≤
            ‖gradient f (x k)‖ ^ 2 / zetaStar P L (Chapter01.hessianMinEig f xs) := by
  have hcrit := gradient_eq_zero_of_isLocalMin hmin
  refine ⟨fun k hk hx hs => h.norm_gradient_succ_le hf hlam hk hx hs,
    fun k₀ h₀ k hk hle => ?_⟩
  have hmem := h.mem_quadRegion_of_ge hf hcrit hlam h₀ k hk fun j hj => hle j hj.le
  have hstep := h.succ_mem_quadRegion hf hcrit hlam hle hmem
  exact ⟨hmem, hstep.1, h.norm_gradient_succ_le hf hlam hle hmem.1
    (P.η₁_le_η₂.trans hstep.1)⟩

end Lemma542

/-! ### Lemma 5.4.3 -/

section Lemma543

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ L : ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ} {xs : EuclideanSpace ℝ (Fin n)}

/-- **Lemma 5.4.3** of [cartis2022evaluation] (asymptotic evaluation count). Let $f$ satisfy
assumption f.HL with constant $L$, let $x_*$ be a local minimizer of $f$ with $\lambda_* > 0$,
and let $(x_k, s_k, \sigma_k)$ be a run of AR2 with the test (5.4.3) that has not terminated
before iteration $k_0$. Suppose (5.4.13): $\|x_{k_0} - x_*\| \le q_*$ and
$\|\nabla f(x_{k_0})\| \le \zeta \le \zeta_*/2$. Then the run terminates at an index $j$, the
first index with $\|\nabla f(x_j)\| \le \epsilon_1$, such that
$$k_0 \le j \le k_0 + \left\lceil \log_2 \log_2 \frac{\zeta_*}{\epsilon_1} \right\rceil_+,$$
and every iteration $k$ with $k_0 \le k < j$ is very successful ($\rho_k \ge \eta_2$).

**Correction.** The book's count (5.4.14) is $\log_2 \log_2(\zeta/\epsilon)$. It is too small by
one in the worst case: for $\|\nabla f(x_{k_0})\| = \zeta = \zeta_*/2$, $\|\nabla f(x_{k+1})\| =
\|\nabla f(x_k)\|^2/\zeta_*$ and $\epsilon = \zeta 2^{-2^m}$, the run needs $m + 1$ iterations.
The printed count also has no ceiling and is undefined for $\epsilon \ge \zeta$.

The functions `Nat.ceil` and `Real.logb 2` are $\lceil \cdot \rceil_+$ and $\log_2$. -/
theorem lemma_5_4_3 (hf : AssumptionHL f L) (hmin : IsLocalMin f xs)
    (hlam : 0 < Chapter01.hessianMinEig f xs) (h : IsAR2StrictRun f P ε₁ x s σ) {k₀ : ℕ}
    {ζ : ℝ} (hk₀ : ∀ j < k₀, ¬ stopTest f ε₁ none (x j))
    (hx : ‖x k₀ - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L))
    (hg : ‖gradient f (x k₀)‖ ≤ ζ) (hζ : ζ ≤ zetaStar P L (Chapter01.hessianMinEig f xs) / 2) :
    ∃ j, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) j ∧ k₀ ≤ j ∧
      j ≤ k₀ + ⌈Real.logb 2 (Real.logb 2 (zetaStar P L (Chapter01.hessianMinEig f xs) / ε₁))⌉₊ ∧
      ∀ k, k₀ ≤ k → k < j → P.η₂ ≤ taylorRatio f 2 x s k := by
  classical
  set ζs := zetaStar P L (Chapter01.hessianMinEig f xs)
  set N := ⌈Real.logb 2 (Real.logb 2 (ζs / ε₁))⌉₊
  have hζs : 0 < ζs := zetaStar_pos hf.pos hlam
  have hε := h.toAlgorithm_3_3_1.ε₁_pos
  have h₀ : x k₀ ∈ quadRegion f P L xs := ⟨hx, by linarith⟩
  have hloc := (lemma_5_4_2 hf hmin hlam h).2 k₀ h₀
  -- the test holds at some `j ≤ k₀ + N`
  have hex : ∃ j ≤ k₀ + N, ‖gradient f (x j)‖ ≤ ε₁ := by
    by_contra hne
    push Not at hne
    have hnot : ∀ j ≤ k₀ + N, ¬ stopTest f ε₁ none (x j) := fun j hj hs =>
      (hne j hj).not_ge (stopTest_none.1 hs)
    let u : ℕ → ℝ := fun m => if m ≤ N then ‖gradient f (x (k₀ + m))‖ else 0
    have hu : ∀ m, 0 ≤ u m := fun m => by
      simp only [u]; split_ifs
      · exact norm_nonneg _
      · exact le_rfl
    have hrec : ∀ m, u (m + 1) ≤ u m ^ 2 / ζs := by
      intro m
      by_cases hm : m + 1 ≤ N
      · simp only [u, hm, Nat.le_of_succ_le hm, ↓reduceIte]
        rw [← add_assoc]
        exact (hloc (k₀ + m) (Nat.le_add_right _ _) fun j hj => hnot j (by omega)).2.2
      · simp only [u, hm, ↓reduceIte]
        exact div_nonneg (sq_nonneg _) hζs.le
    have h0 : u 0 ≤ ζs / 2 := by simp only [u, zero_le, ↓reduceIte, add_zero]; linarith
    have := (le_two_pow_two_pow_of_sq hζs hu hrec h0).2 ε₁ hε N (Or.inr le_rfl)
    simp only [u, le_rfl, ↓reduceIte] at this
    exact (hne _ le_rfl).not_ge this
  obtain ⟨j₁, hj₁, hj₁t⟩ := hex
  obtain ⟨j, hjj₁, hj⟩ := exists_isFirstHit_le (p := fun k => ‖gradient f (x k)‖ ≤ ε₁) hj₁t
  have hk₀j : k₀ ≤ j := by
    by_contra hlt
    push Not at hlt
    exact hk₀ j hlt (stopTest_none.2 hj.test)
  refine ⟨j, hj, hk₀j, hjj₁.trans hj₁, fun k hk hkj => ?_⟩
  exact (hloc k hk fun i hi => fun hs =>
    hj.not_test_of_lt (hi.trans_lt hkj) (stopTest_none.1 hs)).2.1

end Lemma543

/-! ### Theorem 5.4.4 -/

section Theorem544

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ L flow : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ} {xs : EuclideanSpace ℝ (Fin n)}

/-- The first part (5.4.16) of Theorem 5.4.4 of [cartis2022evaluation], for any AR2 run with
$\epsilon_2 = +\infty$. Let $f$ satisfy assumption f.Bb with the lower bound $f_{\rm low}$ and
assumption f.HL with constant $L$, let $(x_k, s_k, \sigma_k)$ be a run of AR2 with
$\epsilon_2 = +\infty$, and let $\zeta > 0$. At every iteration $k$ before termination, the
number of successful iterations $j \le k$ with $\|\nabla f(x_j)\| > \zeta$ is at most
$$\kappa^S_{\rm AR2} \frac{f(x_0) - f_{\rm low}}{\zeta^{3/2}} + 1.$$
-/
theorem card_succ_norm_gradient_gt_le (hb : Chapter02.AssumptionBb f flow)
    (hf : AssumptionHL f L) (h : algorithm_3_3_1 f P ε₁ none x s σ) {ζ : ℝ} (hζ : 0 < ζ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) :
    ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧ ζ < ‖gradient f (x j)‖) k).card : ℝ) ≤
      kappaSAR2 P L * (f (x 0) - flow) / ζ ^ (3 / 2 : ℝ) + 1 := by
  have hκ := kappaSAR2_pos (P := P) hf.nonneg
  set δ := ζ ^ (3 / 2 : ℝ) / kappaSAR2 P L
  have hδ : 0 < δ := by positivity
  have hcard := h.run.card_successSet_le_card_succ_add_one (fun y => ζ < ‖gradient f y‖) hk
  have hT' := card_mul_le_of_decrease (φ := fun j => f (x j)) (k := k) (c := δ)
    (T := successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧ ζ < ‖gradient f (x (j + 1))‖) k)
    successSet_subset_range
    (fun j hj =>
      (h.run.accept j (IsARRun.forall_le_not_stop_iff.2 fun i hi => hk i (hi.trans hj))).le
      (w := f) rfl (lt_of_le_of_lt (by
        have := h.sigma_pos (k := j) fun i hi => hk i (hi.le.trans hj)
        positivity) (lemma_3_3_1 h fun i hi => hk i (hi.trans hj))))
    (fun j hj => by
      rw [mem_successSet] at hj
      exact Chapter03.ar2_decrease_of_le hf h (fun i hi => hk i (hi.trans hj.1)) hj.2.1 hζ
        hj.2.2.le)
    (hb _)
  have hNδ : (f (x 0) - flow) / δ = kappaSAR2 P L * (f (x 0) - flow) / ζ ^ (3 / 2 : ℝ) := by
    simp only [δ]; field_simp
  have hcard' : ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧
      ζ < ‖gradient f (x j)‖) k).card : ℝ) ≤ (successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧
      ζ < ‖gradient f (x (j + 1))‖) k).card + 1 := by exact_mod_cast hcard
  have h2 : ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧
      ζ < ‖gradient f (x (j + 1))‖) k).card : ℝ) ≤ (f (x 0) - flow) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  rw [← hNδ]
  linarith

/-- The second part (5.4.17) of Theorem 5.4.4 of [cartis2022evaluation], with the corrected local
count. Let $f$ satisfy assumptions f.Bb and f.HL, let $x_*$ be a local minimizer of $f$ with
$\lambda_* > 0$, let $(x_k, s_k, \sigma_k)$ be a run of AR2 with the test (5.4.3), and let
$0 < \zeta \le \zeta_*/2$. Suppose that every iterate $x_k$ before termination with
$\|\nabla f(x_k)\| \le \zeta$ satisfies $\|x_k - x_*\| \le q_*$, so that no iterate before
termination satisfies (5.4.18). Then at every iteration $k$ before termination, the set
$\mathcal{S}_k$ of successful iterations $j \le k$ satisfies
$$|\mathcal{S}_k| \le \kappa^S_{\rm AR2} \frac{f(x_0) - f_{\rm low}}{\zeta^{3/2}} + \left\lceil
  \log_2 \log_2 \frac{\zeta_*}{\epsilon_1} \right\rceil_+ + 1.$$
-/
theorem card_successSet_le_of_local (hb : Chapter02.AssumptionBb f flow)
    (hf : AssumptionHL f L) (hmin : IsLocalMin f xs) (hlam : 0 < Chapter01.hessianMinEig f xs)
    (h : IsAR2StrictRun f P ε₁ x s σ) {ζ : ℝ} (hζ : 0 < ζ)
    (hζs : ζ ≤ zetaStar P L (Chapter01.hessianMinEig f xs) / 2)
    (hreg : ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) → ‖gradient f (x k)‖ ≤ ζ →
      ‖x k - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L))
    {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) :
    ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) k).card : ℝ) ≤
      kappaSAR2 P L * (f (x 0) - flow) / ζ ^ (3 / 2 : ℝ) +
        ⌈Real.logb 2 (Real.logb 2 (zetaStar P L (Chapter01.hessianMinEig f xs) / ε₁))⌉₊ + 1 := by
  classical
  set N := ⌈Real.logb 2 (Real.logb 2 (zetaStar P L (Chapter01.hessianMinEig f xs) / ε₁))⌉₊
  set S := successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) k
  set T := successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧ ζ < ‖gradient f (x j)‖) k
  have hT := card_succ_norm_gradient_gt_le hb hf h.toAlgorithm_3_3_1 hζ hk
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  by_cases hex : ∃ j, j ≤ k ∧ ‖gradient f (x j)‖ ≤ ζ
  · obtain ⟨hk1k, hk1g⟩ := Nat.find_spec hex
    have hmin1 : ∀ j < Nat.find hex, ζ < ‖gradient f (x j)‖ := fun j hj => by
      have := Nat.find_min hex hj
      push Not at this
      exact this (by omega)
    obtain ⟨jt, hjt, -, hjtN, -⟩ := lemma_5_4_3 hf hmin hlam h (k₀ := Nat.find hex)
      (fun j hj => hk j (by omega))
      (hreg _ (fun j hj => hk j (hj.trans hk1k)) hk1g) hk1g hζs
    have hkjt : k < jt := by
      by_contra hle
      push Not at hle
      exact hk jt hle (stopTest_none.2 hjt.test)
    have hsub : S ⊆ T ∪ Icc (Nat.find hex) k := by
      intro j hj
      rw [mem_successSet] at hj
      rw [Finset.mem_union, Finset.mem_Icc]
      by_cases hj1 : j < Nat.find hex
      · exact Or.inl (mem_successSet.2 ⟨hj.1, hj.2, hmin1 j hj1⟩)
      · exact Or.inr ⟨by omega, hj.1⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Nat.card_Icc] at hc
    have hc' : S.card ≤ T.card + N := by omega
    have : (S.card : ℝ) ≤ T.card + N := by exact_mod_cast hc'
    linarith
  · have hsub : S ⊆ T := by
      intro j hj
      rw [mem_successSet] at hj ⊢
      refine ⟨hj.1, hj.2, ?_⟩
      by_contra hle
      exact hex ⟨j, hj.1, not_lt.1 hle⟩
    have : (S.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hsub
    linarith

/-- **Theorem 5.4.4** of [cartis2022evaluation] (global complexity bound for locally convex
functions). Let $f$ satisfy assumption f.Bb with the lower bound $f_{\rm low}$ and assumption
f.HL with constant $L$, let $x_*$ be a local minimizer of $f$ with $\lambda_* =
\lambda_{\min}[\nabla^2 f(x_*)] > 0$, let $(x_k, s_k, \sigma_k)$ be a run of AR2 with the
model-termination test (5.4.3), and let $0 < \zeta \le \zeta_*/2$. Then two statements hold.
First, at every iteration $k$ before termination, the number of successful iterations $j \le k$
with $\|\nabla f(x_j)\| > \zeta$ is at most
$$\kappa^S_{\rm AR2} \frac{f(x_0) - f_{\rm low}}{\zeta^{3/2}} + 1. \qquad (5.4.16)$$
Second, suppose that no iterate $x_k$ before termination satisfies (5.4.18), that is,
$\|x_k - x_*\| > q_*$ and $\|\nabla f(x_k)\| \le \zeta$. Then at every iteration $k$ before
termination, the set $\mathcal{S}_k$ of successful iterations $j \le k$ satisfies
$$|\mathcal{S}_k| \le \kappa^S_{\rm AR2} \frac{f(x_0) - f_{\rm low}}{\zeta^{3/2}} + \left\lceil
  \log_2 \log_2 \frac{\zeta_*}{\epsilon_1} \right\rceil_+ + 1. \qquad (5.4.17)$$

**Correction.** The book's second term in (5.4.17) is $\log_2 \log_2(\zeta/\epsilon)$. It is
corrected as in Lemma 5.4.3 (see `CartisGouldToint.Chapter05.lemma_5_4_3`).

**Reading.** The second part is stated, like Lemma 3.3.4, as a bound on $|\mathcal{S}_k|$ at
every iteration $k$ before termination, and the condition (5.4.18) is restricted to the
iterations before termination.

The constant $\kappa^S_{\rm AR2}$ of Lemma 3.3.4 is `CartisGouldToint.Chapter03.kappaSAR2 P L`.
The first part is `CartisGouldToint.Chapter05.card_succ_norm_gradient_gt_le`, and the second
part is `CartisGouldToint.Chapter05.card_successSet_le_of_local`. -/
theorem theorem_5_4_4 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L)
    (hmin : IsLocalMin f xs) (hlam : 0 < Chapter01.hessianMinEig f xs)
    (h : IsAR2StrictRun f P ε₁ x s σ) {ζ : ℝ} (hζ : 0 < ζ)
    (hζs : ζ ≤ zetaStar P L (Chapter01.hessianMinEig f xs) / 2) :
    (∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) →
      ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧ ζ < ‖gradient f (x j)‖) k).card :
          ℝ) ≤ kappaSAR2 P L * (f (x 0) - flow) / ζ ^ (3 / 2 : ℝ) + 1) ∧
    ((∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) → ‖gradient f (x k)‖ ≤ ζ →
        ‖x k - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L)) →
      ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) →
        ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) k).card : ℝ) ≤
          kappaSAR2 P L * (f (x 0) - flow) / ζ ^ (3 / 2 : ℝ) +
            ⌈Real.logb 2 (Real.logb 2 (zetaStar P L (Chapter01.hessianMinEig f xs) / ε₁))⌉₊ +
              1) :=
  ⟨fun _ hk => card_succ_norm_gradient_gt_le hb hf h.toAlgorithm_3_3_1 hζ hk,
    fun hreg _ hk => card_successSet_le_of_local hb hf hmin hlam h hζ hζs hreg hk⟩

end Theorem544

end CartisGouldToint.Chapter05
