/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Optimization.ModelBased.RatioTest
import Numlib.Optimization.Optimality.Approximate
import Numlib.Optimization.Subproblem.TrustRegion

/-!
# Quadratic models of trust-region methods

The trust-region methods TR1 (Algorithm 2.3.1) and TR2 (Algorithm 3.2.1) of [cartis2022evaluation]
use, at an iterate $x$, the quadratic model (2.3.1)
$$m(s) = f(x) + q(s), \qquad q(s) = \langle g, s \rangle + \tfrac12 \langle s, H s \rangle,$$
where $g \in E$, $H$ is a bounded linear operator on a real inner product space $E$, and $\|H\|$ is
its operator norm. For a twice continuously differentiable $f$ with $g = \nabla f(x)$ and
$H = \nabla^2 f(x)$, the model is the second-order Taylor polynomial of $f$ at $x$.

This file proves the model decreases that drive these methods: the decrease at the Cauchy step,
which minimizes the model along $-g$ in the trust region $\|s\| \le \Delta$ (Lemma 2.3.2), and the
decrease at the eigenpoint along a direction of negative curvature (Lemma 3.2.3). It then bounds the
reduction ratio $\rho$ of one iteration, so that a small enough radius makes the iteration very
successful (Lemmas 2.3.3 and 3.2.4). Finally, in finite dimension a global minimizer of the model in
the trust region exists and satisfies both decrease conditions.

## Main definitions

* `Optimization.IsCauchyStep`: $t \ge 0$ is a Cauchy step (2.3.5): $s^C = -t g$ is in the trust
  region and minimizes $q$ along $-g$ there.

## Main results

* `Optimization.exists_isCauchyStep`: a Cauchy step exists for every radius $\Delta \ge 0$.
* `Optimization.neg_quadModel_cauchy_ge`: the Cauchy decrease $-q(s^C) \ge \frac{\|g\|}{2}
  \min\left(\frac{\|g\|}{1 + \|H\|}, \Delta\right)$ of Lemma 2.3.2.
* `Optimization.quadModel_smul_le_of_curvature` and
  `Optimization.le_neg_quadModel_smul_of_curvature`: the eigenpoint decrease
  $-q(\Delta u) \ge |\lambda| \Delta^2 / 2$ of Lemma 3.2.3.
* `Optimization.taylorPolynomial_two_eq_quadModel`: the second-order Taylor polynomial of $f$ at $x$
  is $f(x) + q(s)$ with $g = \nabla f(x)$ and $H = \nabla^2 f(x)$.
* `Optimization.abs_reductionRatio_sub_one_le_trust_first` and
  `Optimization.le_reductionRatio_trust_first`: Lemma 2.3.3 for one iteration, with the predicted
  decrease as a hypothesis. The form of the source is
  `Optimization.le_reductionRatio_trust_first_of_isCauchyStep`.
* `Optimization.abs_reductionRatio_sub_one_le_trust_second` and
  `Optimization.le_reductionRatio_trust_second`: Lemma 3.2.4 in the same way. The form of the source
  is `Optimization.le_reductionRatio_trust_second_of_curvature`.
* `Optimization.exists_isMinOn_quadModel_ball`: in finite dimension, a global minimizer of $q$ in
  the trust region exists and satisfies both the Cauchy and the eigenpoint conditions.

## Implementation notes

* The function $q$ is `Subproblem.quadModel g H`, with `H : E →L[ℝ] E`. The Hessian $\nabla^2 f(x)$
  is `Optimization.hessianOperator f x`.
* The trust-region constraints on the Cauchy step and on the eigenpoint are $\|t g\| \le \Delta_k$
  and $\|t u\| \le \Delta_k$. The source writes them as $x_k - t g \in \mathcal{R}_k$ and
  $x_k + t u \in \mathcal{B}_{\Delta_k}$.
-/

open Set Metric
open scoped RealInnerProductSpace Nat

namespace Optimization

open Subproblem

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a bounded linear operator $H$ on a real inner product space,
$|\langle s, H s \rangle| \le \|H\| \|s\|^2$. -/
private theorem abs_inner_self_apply_le (H : E →L[ℝ] E) (s : E) : |⟪s, H s⟫| ≤ ‖H‖ * ‖s‖ ^ 2 := by
  simpa [real_inner_comm] using H.abs_re_inner_apply_self_le s

/-- The model along the ray $-t g$:
$$q(-t g) = -t \|g\|^2 + \frac{t^2}{2} \langle g, H g \rangle.$$
-/
theorem quadModel_neg_smul (g : E) (H : E →L[ℝ] E) (t : ℝ) :
    quadModel g H (-(t • g)) = -t * ‖g‖ ^ 2 + t ^ 2 / 2 * ⟪g, H g⟫ := by
  rw [quadModel_def, map_neg, map_smul, inner_neg_right, inner_neg_left, inner_neg_right,
    inner_smul_right, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [conj_trivial]
  ring

/-- The model along the ray $t u$:
$$q(t u) = t \langle g, u \rangle + \frac{t^2}{2} \langle u, H u \rangle.$$
-/
theorem quadModel_smul (g : E) (H : E →L[ℝ] E) (t : ℝ) (u : E) :
    quadModel g H (t • u) = t * ⟪g, u⟫ + t ^ 2 / 2 * ⟪u, H u⟫ := by
  rw [quadModel_def, map_smul, inner_smul_right, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  ring

/-- A **Cauchy step** of the model $q(s) = \langle g, s \rangle + \frac12 \langle s, H s \rangle$
for the radius $\Delta$, as in (2.3.5) of [cartis2022evaluation]. A real number $t$ is a Cauchy
step if $t \ge 0$, the point $-t g$ is in the trust region ($t \|g\| \le \Delta$), and
$$q(-t g) \le q(-\tau g) \quad \text{for all } \tau \ge 0 \text{ with } \tau \|g\| \le \Delta.$$
The Cauchy step of the source is the vector $s^C = -t g$. -/
def IsCauchyStep (g : E) (H : E →L[ℝ] E) (Δ t : ℝ) : Prop :=
  0 ≤ t ∧ t * ‖g‖ ≤ Δ ∧
    ∀ τ, 0 ≤ τ → τ * ‖g‖ ≤ Δ → quadModel g H (-(t • g)) ≤ quadModel g H (-(τ • g))

/-- The defining property of a Cauchy step: $t$ is a Cauchy step if and only if $t \ge 0$,
$t \|g\| \le \Delta$, and $q(-t g) \le q(-\tau g)$ for all $\tau \ge 0$ with
$\tau \|g\| \le \Delta$. -/
theorem isCauchyStep_iff {g : E} {H : E →L[ℝ] E} {Δ t : ℝ} :
    IsCauchyStep g H Δ t ↔ 0 ≤ t ∧ t * ‖g‖ ≤ Δ ∧
      ∀ τ, 0 ≤ τ → τ * ‖g‖ ≤ Δ → quadModel g H (-(t • g)) ≤ quadModel g H (-(τ • g)) :=
  Iff.rfl

/-- For every $g$, $H$ and every radius $\Delta \ge 0$, a Cauchy step exists.

The model along $-g$ is continuous on a compact interval of $\tau$. If $g = 0$, every $t \ge 0$
is a Cauchy step, for example $t = 0$. -/
theorem exists_isCauchyStep (g : E) (H : E →L[ℝ] E) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ t, IsCauchyStep g H Δ t := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact ⟨0, le_rfl, by simpa using hΔ, fun τ _ _ => by simp [quadModel_def]⟩
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hcont : Continuous fun t : ℝ => quadModel g H (-(t • g)) :=
    (continuous_quadModel g H).comp (continuous_id.smul continuous_const).neg
  obtain ⟨t, ht, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Δ / ‖g‖)).exists_isMinOn
    (nonempty_Icc.2 (div_nonneg hΔ hgpos.le)) hcont.continuousOn
  refine ⟨t, ht.1, (le_div_iff₀ hgpos).1 ht.2, fun τ hτ hτΔ => ?_⟩
  exact hmin ⟨hτ, (le_div_iff₀ hgpos).2 hτΔ⟩

/-- The **Cauchy decrease**, Lemma 2.3.2 of [cartis2022evaluation], bound (2.3.12). Let $E$ be a
real inner product space, $g \in E$, $H$ a bounded linear operator on $E$ and
$\Delta \in \mathbb{R}$. If $t$ is a Cauchy step for $\Delta$, then the decrease
$m(0) - m(s^C) = -q(-t g)$ satisfies
$$-q(-t g) \ge \frac{\|g\|}{2} \min\left(\frac{\|g\|}{1 + \|H\|}, \Delta\right).$$

The proof compares with the step $\tau = \min(1 / (1 + \|H\|), \Delta / \|g\|)$, along which
$q(-\tau g) \le -\tau \|g\|^2 / 2$. -/
theorem neg_quadModel_cauchy_ge {g : E} {H : E →L[ℝ] E} {Δ t : ℝ} (ht : IsCauchyStep g H Δ t) :
    ‖g‖ / 2 * min (‖g‖ / (1 + ‖H‖)) Δ ≤ -quadModel g H (-(t • g)) := by
  have hΔ : 0 ≤ Δ := (mul_nonneg ht.1 (norm_nonneg g)).trans ht.2.1
  rcases eq_or_ne g 0 with rfl | hg
  · have := ht.2.2 0 le_rfl (by simpa using hΔ)
    simp only [zero_smul, neg_zero, quadModel_zero] at this
    simp only [norm_zero, zero_div, zero_mul]
    linarith
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hH : 0 ≤ ‖H‖ := norm_nonneg H
  set τ := min (1 / (1 + ‖H‖)) (Δ / ‖g‖) with hτ
  have hτ0 : 0 ≤ τ := le_min (by positivity) (div_nonneg hΔ hgpos.le)
  have hτg : τ * ‖g‖ ≤ Δ := (le_div_iff₀ hgpos).1 (min_le_right _ _)
  have hτH : τ * ‖H‖ ≤ 1 := by
    calc τ * ‖H‖ ≤ 1 / (1 + ‖H‖) * ‖H‖ := by gcongr; exact min_le_left _ _
      _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hq : quadModel g H (-(τ • g)) ≤ -(τ * ‖g‖ ^ 2) / 2 := by
    rw [quadModel_neg_smul]
    have h1 := (le_abs_self _).trans (abs_inner_self_apply_le H g)
    have h2 : τ ^ 2 / 2 * ⟪g, H g⟫ ≤ τ ^ 2 / 2 * (‖H‖ * ‖g‖ ^ 2) := by gcongr
    have h3 : τ ^ 2 / 2 * (‖H‖ * ‖g‖ ^ 2) ≤ τ / 2 * ‖g‖ ^ 2 := by
      have : τ ^ 2 / 2 * (‖H‖ * ‖g‖ ^ 2) = (τ * ‖H‖) * (τ / 2 * ‖g‖ ^ 2) := by ring
      rw [this]
      exact mul_le_of_le_one_left (by positivity) hτH
    linarith
  have hmin := ht.2.2 τ hτ0 hτg
  have hτeq : ‖g‖ * τ = min (‖g‖ / (1 + ‖H‖)) Δ := by
    rw [hτ, mul_min_of_nonneg _ _ hgpos.le, mul_one_div, mul_div_cancel₀ _ hgpos.ne']
  calc ‖g‖ / 2 * min (‖g‖ / (1 + ‖H‖)) Δ = τ * ‖g‖ ^ 2 / 2 := by rw [← hτeq]; ring
    _ ≤ -quadModel g H (-(τ • g)) := by linarith
    _ ≤ -quadModel g H (-(t • g)) := neg_le_neg hmin

/-- The core of Lemma 3.2.3 of [cartis2022evaluation], (3.2.5) and (3.2.15). Let $E$ be a real inner
product space, $g, u \in E$ and $H$ a bounded linear operator on $E$. Suppose that $u$ has
nonpositive curvature, $\langle u, H u \rangle = \lambda \le 0$, that
$\langle g, u \rangle \le 0$, and that $\Delta \ge 0$. Then
$$q(\Delta u) \le \frac{\lambda \Delta^2}{2},$$
and $\tau = \Delta$ minimizes $\tau \mapsto q(\tau u)$ over $[0, \Delta]$. Thus the eigenpoint
lies on the boundary of the trust region.

The direction $u$ need not be a unit vector here. In Lean, $\lambda$ is `lam`. -/
theorem quadModel_smul_le_of_curvature {g : E} {H : E →L[ℝ] E} {u : E} {lam Δ : ℝ}
    (hHu : ⟪u, H u⟫ = lam) (hlam : lam ≤ 0) (hgu : ⟪g, u⟫ ≤ 0) (hΔ : 0 ≤ Δ) :
    quadModel g H (Δ • u) ≤ lam * Δ ^ 2 / 2 ∧
      ∀ τ ∈ Icc 0 Δ, quadModel g H (Δ • u) ≤ quadModel g H (τ • u) := by
  refine ⟨?_, fun τ hτ => ?_⟩
  · rw [quadModel_smul, hHu]
    nlinarith
  · rw [quadModel_smul, quadModel_smul, hHu]
    obtain ⟨hτ0, hτΔ⟩ := hτ
    nlinarith [mul_nonneg (sub_nonneg.2 hτΔ) (add_nonneg hτ0 hΔ)]

/-- The **eigenpoint decrease**, Lemma 3.2.3 of [cartis2022evaluation], bound (3.2.15). Let $E$ be a
real inner product space, $g, u \in E$ and $H$ a bounded linear operator on $E$. If
$\langle u, H u \rangle = \lambda \le 0$, $\langle g, u \rangle \le 0$ and $\Delta \ge 0$, then
the decrease $m(0) - m(\Delta u) = -q(\Delta u)$ satisfies
$$-q(\Delta u) \ge \frac{|\lambda| \Delta^2}{2}.$$
-/
theorem le_neg_quadModel_smul_of_curvature {g : E} {H : E →L[ℝ] E} {u : E} {lam Δ : ℝ}
    (hHu : ⟪u, H u⟫ = lam) (hlam : lam ≤ 0) (hgu : ⟪g, u⟫ ≤ 0) (hΔ : 0 ≤ Δ) :
    |lam| * Δ ^ 2 / 2 ≤ -quadModel g H (Δ • u) := by
  have h := (quadModel_smul_le_of_curvature hHu hlam hgu hΔ).1
  rw [abs_of_nonpos hlam]
  linarith

end Inner

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The second-order Taylor polynomial is the quadratic model with the gradient and the Hessian, as
in (2.3.1) and (3.1.2) of [cartis2022evaluation]. Let $E$ be a real Hilbert space and let
$f : E \to \mathbb{R}$ be twice continuously differentiable at $x$. Then for all $s \in E$,
$$T_{f,2}(x, s) = f(x) + \langle \nabla f(x), s \rangle + \tfrac12 \langle s, \nabla^2 f(x) s
  \rangle.$$

Here $T_{f,2}(x, s)$ is `taylorPolynomial f 2 x s`, and $\nabla^2 f(x)$ is
`Optimization.hessianOperator f x`. -/
theorem taylorPolynomial_two_eq_quadModel {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (s : E) :
    taylorPolynomial f 2 x s = f x + quadModel (gradient f x) (hessianOperator f x) s := by
  rw [taylorPolynomial_two_apply, quadModel_def, inner_gradient_left,
    inner_hessianOperator_apply hf, ← apply_diag_eq_vec]
  ring

/-- The first-order Taylor polynomial: for every $f : E \to \mathbb{R}$ on a real Hilbert space and
all $x, s \in E$, $T_{f,1}(x, s) = f(x) + \langle \nabla f(x), s \rangle$.

No differentiability is needed, because the gradient in Lean is $0$ where $f$ is not
differentiable, and so is the derivative in the Taylor polynomial. -/
theorem taylorPolynomial_one_eq_inner (f : E → ℝ) (x s : E) :
    taylorPolynomial f 1 x s = f x + ⟪gradient f x, s⟫ := by
  rw [taylorPolynomial_apply, inner_gradient_left]
  simp [Finset.sum_range_succ, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply]

variable {f : E → ℝ} {x s : E} {H : E →L[ℝ] E} {C : Set E} {L κB Δ : ℝ}

/-- **Lemma 2.3.3** of [cartis2022evaluation] for one iteration: a bound on the reduction ratio of a
trust-region iteration with a quadratic model. Let $E$ be a real Hilbert space, $C \subseteq E$
convex, and $f : E \to \mathbb{R}$ continuously differentiable at every point of $C$, with
$\nabla f$ Lipschitz on $C$ with constant $L$. Let $x, x + s \in C$, let
$g = \nabla f(x) \neq 0$, and let $H$ be a bounded linear operator with $\|H\| \le \kappa_B$.
Let $q(s) = \langle g, s \rangle + \frac12 \langle s, H s \rangle$. Suppose that
$\|s\| \le \Delta$ with $\Delta > 0$, and that the predicted decrease $-q(s)$ is at least
$\|g\| \Delta / 2$, as in the Cauchy decrease (2.3.16). Then the ratio $\rho$ with predicted
decrease $-q(s)$ satisfies
$$|\rho - 1| \le \frac{(L + \kappa_B) \Delta}{\|g\|}.$$

The mean-value argument of the source gives the constant $2(L + \kappa_B)$. The bound (A.19) of
[cartis2022evaluation] on the Taylor remainder gives $L + \kappa_B$. The Lipschitz condition is
`IteratedFDerivLipschitzOn f 1 L C`. The ratio is `Optimization.reductionRatio` with the predicted
decrease $-q(s)$. -/
theorem abs_reductionRatio_sub_one_le_trust_first (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 1 f y) (hL : IteratedFDerivLipschitzOn f 1 L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hH : ‖H‖ ≤ κB) (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) (hg : 0 < ‖gradient f x‖)
    (hpred : ‖gradient f x‖ * Δ / 2 ≤ -quadModel (gradient f x) H s) :
    |reductionRatio f x s (-quadModel (gradient f x) H s) - 1| ≤
      (L + κB) * Δ / ‖gradient f x‖ := by
  set g := gradient f x
  have hpredpos : 0 < -quadModel g H s := lt_of_lt_of_le (by positivity) hpred
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpredpos
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hT := abs_sub_taylorPolynomial_le_of_lipschitz (p := 1) hC (by simpa using hf) hL hx hxs
  rw [taylorPolynomial_one_eq_inner] at hT
  have hL0 : 0 ≤ L := nonneg_of_abs_le_div_mul_pow (by positivity) hspos hT
  have hLκ : 0 ≤ L + κB := by linarith [norm_nonneg H]
  refine abs_reductionRatio_sub_one_le hpredpos ?_
  have hq : |(1 / 2 : ℝ) * ⟪s, H s⟫| ≤ κB / 2 * ‖s‖ ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := abs_inner_self_apply_le H s
    have : ‖H‖ * ‖s‖ ^ 2 ≤ κB * ‖s‖ ^ 2 := by gcongr
    linarith
  have heq : f (x + s) - (f x - -quadModel g H s) =
      (f (x + s) - (f x + ⟪g, s⟫)) - (1 / 2) * ⟪s, H s⟫ := by
    rw [quadModel_def]; ring
  rw [heq]
  calc _ ≤ |f (x + s) - (f x + ⟪g, s⟫)| + |(1 / 2 : ℝ) * ⟪s, H s⟫| := abs_sub _ _
    _ ≤ L / ((1 + 1)! : ℝ) * ‖s‖ ^ (1 + 1) + κB / 2 * ‖s‖ ^ 2 := add_le_add hT hq
    _ = (L + κB) / 2 * ‖s‖ ^ 2 := by norm_num; ring
    _ ≤ (L + κB) / 2 * Δ ^ 2 := by gcongr
    _ = (L + κB) * Δ / ‖g‖ * (‖g‖ * Δ / 2) := by field_simp
    _ ≤ (L + κB) * Δ / ‖g‖ * -quadModel g H s := by gcongr

/-- **Lemma 2.3.3** of [cartis2022evaluation], with the predicted decrease as a hypothesis. Under
the hypotheses of `Optimization.abs_reductionRatio_sub_one_le_trust_first`, let
$\eta \in \mathbb{R}$ with
$$(L + \kappa_B) \Delta \le (1 - \eta) \|\nabla f(x)\|.$$
Then $\rho \ge \eta$.

The form of the source, which derives the bound on the predicted decrease from the Cauchy
condition and (2.3.15), is `Optimization.le_reductionRatio_trust_first_of_isCauchyStep`. -/
theorem le_reductionRatio_trust_first (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 1 f y) (hL : IteratedFDerivLipschitzOn f 1 L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hH : ‖H‖ ≤ κB) (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) (hg : 0 < ‖gradient f x‖)
    (hpred : ‖gradient f x‖ * Δ / 2 ≤ -quadModel (gradient f x) H s) {η : ℝ}
    (hηΔ : (L + κB) * Δ ≤ (1 - η) * ‖gradient f x‖) :
    η ≤ reductionRatio f x s (-quadModel (gradient f x) H s) := by
  have h := abs_reductionRatio_sub_one_le_trust_first hC hf hL hx hxs hH hs hΔ hg hpred
  have : (L + κB) * Δ / ‖gradient f x‖ ≤ 1 - η := (div_le_iff₀ hg).2 hηΔ
  linarith [neg_abs_le (reductionRatio f x s (-quadModel (gradient f x) H s) - 1)]

/-- **Lemma 3.2.4** of [cartis2022evaluation] for one iteration: a bound on the reduction ratio with
the exact second-order model. Let $E$ be a real Hilbert space, $C \subseteq E$ convex, and
$f : E \to \mathbb{R}$ twice continuously differentiable at every point of $C$, with
$\nabla^2 f$ Lipschitz on $C$ with constant $L$. Let $x, x + s \in C$ and $q(s) = \langle \nabla
f(x), s \rangle + \frac12 \langle s, \nabla^2 f(x) s \rangle$. Suppose that $\|s\| \le \Delta$
with $\Delta > 0$, that $\lambda < 0$, and that the predicted decrease $-q(s)$ is at least
$|\lambda| \Delta^2 / 2$, as in the eigenpoint decrease (3.2.15). Then the ratio $\rho$ with
predicted decrease $-q(s)$ satisfies
$$|\rho - 1| \le \frac{L \Delta}{3 |\lambda|}.$$

The number $\lambda$ is arbitrary here. The form of the source takes it to be the curvature
along a direction, see `Optimization.le_reductionRatio_trust_second_of_curvature`. -/
theorem abs_reductionRatio_sub_one_le_trust_second (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 2 f y) (hL : IteratedFDerivLipschitzOn f 2 L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) {lam : ℝ} (hlam : lam < 0)
    (hpred : |lam| * Δ ^ 2 / 2 ≤ -quadModel (gradient f x) (hessianOperator f x) s) :
    |reductionRatio f x s (-quadModel (gradient f x) (hessianOperator f x) s) - 1| ≤
      L * Δ / (3 * |lam|) := by
  set q := quadModel (gradient f x) (hessianOperator f x) s
  have habs : 0 < |lam| := abs_pos.2 hlam.ne
  have hpredpos : 0 < -q := lt_of_lt_of_le (by have := mul_pos habs (pow_pos hΔ 2); linarith) hpred
  have hs0 : s ≠ 0 := by rintro rfl; simp [q] at hpredpos
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hT := abs_sub_taylorPolynomial_le_of_lipschitz (p := 2) hC (by simpa using hf) hL hx hxs
  rw [taylorPolynomial_two_eq_quadModel (hf x hx)] at hT
  have hL0 : 0 ≤ L := nonneg_of_abs_le_div_mul_pow (by positivity) hspos hT
  refine abs_reductionRatio_sub_one_le hpredpos ?_
  have heq : f (x + s) - (f x - -q) = f (x + s) - (f x + q) := by ring
  rw [heq]
  calc |f (x + s) - (f x + q)| ≤ L / ((2 + 1)! : ℝ) * ‖s‖ ^ (2 + 1) := hT
    _ ≤ L / 6 * Δ ^ 3 := by norm_num [Nat.factorial]; gcongr
    _ = L * Δ / (3 * |lam|) * (|lam| * Δ ^ 2 / 2) := by field_simp; ring
    _ ≤ L * Δ / (3 * |lam|) * -q := by gcongr

/-- **Lemma 3.2.4** of [cartis2022evaluation], bound (3.2.16), with the predicted decrease as a
hypothesis. Under the hypotheses of `Optimization.abs_reductionRatio_sub_one_le_trust_second`,
let $\eta \in \mathbb{R}$ with
$$L \Delta \le 3 (1 - \eta) |\lambda|.$$
Then $\rho \ge \eta$.

The form of the source, which derives the bound on the predicted decrease from the eigenpoint
condition, is `Optimization.le_reductionRatio_trust_second_of_curvature`. -/
theorem le_reductionRatio_trust_second (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 2 f y) (hL : IteratedFDerivLipschitzOn f 2 L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) {lam : ℝ} (hlam : lam < 0)
    (hpred : |lam| * Δ ^ 2 / 2 ≤ -quadModel (gradient f x) (hessianOperator f x) s) {η : ℝ}
    (hηΔ : L * Δ ≤ 3 * (1 - η) * |lam|) :
    η ≤ reductionRatio f x s (-quadModel (gradient f x) (hessianOperator f x) s) := by
  have h := abs_reductionRatio_sub_one_le_trust_second hC hf hL hx hxs hs hΔ hlam hpred
  have habs : 0 < 3 * |lam| := mul_pos three_pos (abs_pos.2 hlam.ne)
  have : L * Δ / (3 * |lam|) ≤ 1 - η := (div_le_iff₀ habs).2 (by linarith)
  linarith [neg_abs_le (reductionRatio f x s
    (-quadModel (gradient f x) (hessianOperator f x) s) - 1)]

/-- **Lemma 2.3.3** of [cartis2022evaluation], in the form of the source. Let $E$ be a real Hilbert
space, $C \subseteq E$ convex, and $f : E \to \mathbb{R}$ continuously differentiable at every
point of $C$, with $\nabla f$ Lipschitz on $C$ with constant $L \ge 1$. Let $x, x + s \in C$,
let $g = \nabla f(x) \neq 0$, and let $H$ be a bounded linear operator with
$\|H\| \le \kappa_B$. Let $t$ be a Cauchy step for the radius $\Delta > 0$. Suppose that the
step $s$ is in the trust region, $\|s\| \le \Delta$, and satisfies the Cauchy condition (2.3.4),
$q(s) \le q(-t g)$. If $\eta \ge 0$ and (2.3.15) holds,
$$\Delta < \frac{(1 - \eta) \|g\|}{2 (L + \kappa_B)},$$
then $\rho \ge \eta$. With $\eta = \eta_2$, the iteration is very successful. -/
theorem le_reductionRatio_trust_first_of_isCauchyStep (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 1 f y) (hL : IteratedFDerivLipschitzOn f 1 L C) (hL1 : 1 ≤ L)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hH : ‖H‖ ≤ κB) {t : ℝ}
    (ht : IsCauchyStep (gradient f x) H Δ t)
    (hsC : quadModel (gradient f x) H s ≤ quadModel (gradient f x) H (-(t • gradient f x)))
    (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) (hg : 0 < ‖gradient f x‖) {η : ℝ} (hη : 0 ≤ η)
    (hΔη : Δ < (1 - η) * ‖gradient f x‖ / (2 * (L + κB))) :
    η ≤ reductionRatio f x s (-quadModel (gradient f x) H s) := by
  set g := gradient f x
  have hκ : 0 ≤ κB := (norm_nonneg H).trans hH
  have hLκ : 0 < L + κB := by linarith
  rw [lt_div_iff₀ (by positivity)] at hΔη
  have hΔg : Δ ≤ ‖g‖ / (1 + ‖H‖) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hcau := neg_quadModel_cauchy_ge ht
  rw [min_eq_right hΔg] at hcau
  refine le_reductionRatio_trust_first hC hf hL hx hxs hH hs hΔ hg (by linarith) ?_
  nlinarith

/-- **Lemma 3.2.4** of [cartis2022evaluation], in the form of the source. Let $E$ be a real Hilbert
space, $C \subseteq E$ convex, and $f : E \to \mathbb{R}$ twice continuously differentiable at
every point of $C$, with $\nabla^2 f$ Lipschitz on $C$ with constant $L > 0$. Let
$x, x + s \in C$. Let $u \in E$ be a direction of negative curvature, $\langle u, \nabla^2 f(x)
u \rangle = \lambda < 0$, with $\langle \nabla f(x), u \rangle \le 0$; for example, $u$ can be a
unit eigenvector for $\lambda_{\min}[\nabla^2 f(x)]$. Suppose that the step $s$ is in the trust
region, $\|s\| \le \Delta$ with $\Delta > 0$, and satisfies the eigenpoint condition (3.2.10),
$T_{f,2}(x, s) \le T_{f,2}(x, \Delta u)$. If (3.2.16) holds,
$$\Delta < \frac{3 (1 - \eta) |\lambda|}{L},$$
then $\rho \ge \eta$.

The eigenpoint condition is stated as $q(s) \le q(\Delta u)$ for the model $q$ with
$\nabla f(x)$ and $\nabla^2 f(x)$. The direction $u$ need not be a unit vector. -/
theorem le_reductionRatio_trust_second_of_curvature (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 2 f y) (hL : IteratedFDerivLipschitzOn f 2 L C) (hL0 : 0 < L)
    (hx : x ∈ C) (hxs : x + s ∈ C) {u : E} {lam : ℝ}
    (hHu : ⟪u, hessianOperator f x u⟫ = lam) (hlam : lam < 0) (hgu : ⟪gradient f x, u⟫ ≤ 0)
    (hsE : quadModel (gradient f x) (hessianOperator f x) s ≤
      quadModel (gradient f x) (hessianOperator f x) (Δ • u))
    (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) {η : ℝ} (hΔη : Δ < 3 * (1 - η) * |lam| / L) :
    η ≤ reductionRatio f x s (-quadModel (gradient f x) (hessianOperator f x) s) := by
  have hE := le_neg_quadModel_smul_of_curvature hHu hlam.le hgu hΔ.le
  rw [lt_div_iff₀ hL0] at hΔη
  exact le_reductionRatio_trust_second hC hf hL hx hxs hs hΔ hlam (by linarith) (by linarith)

end Taylor

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let $E$ be a real inner product space and let $s$ minimize $q$ on the trust region
$\|s\| \le \Delta$. Then $s$ satisfies the Cauchy condition (2.3.4), $q(s) \le q(-t g)$, for
every Cauchy step $t$. If $\Delta \ge 0$, then $s$ also satisfies the eigenpoint condition
(3.2.10), $q(s) \le q(\Delta u)$, for every unit vector $u$. -/
theorem quadModel_le_of_isMinOn_ball {g : E} {H : E →L[ℝ] E} {Δ : ℝ} {s : E}
    (hmin : IsMinOn (quadModel g H) (closedBall 0 Δ) s) :
    (∀ t, IsCauchyStep g H Δ t → quadModel g H s ≤ quadModel g H (-(t • g))) ∧
      (0 ≤ Δ → ∀ u, ‖u‖ = 1 → quadModel g H s ≤ quadModel g H (Δ • u)) := by
  refine ⟨fun t ht => hmin ?_, fun hΔ u hu => hmin ?_⟩
  · rw [mem_closedBall_zero_iff, norm_neg, norm_smul, Real.norm_of_nonneg ht.1]
    exact ht.2.1
  · rw [mem_closedBall_zero_iff, norm_smul, hu, mul_one, Real.norm_of_nonneg hΔ]

/-- Existence of the steps of TR1 and TR2, Section 3.2.1 of [cartis2022evaluation]. Let $E$ be a
finite-dimensional real inner product space, $g \in E$, $H$ a linear operator on $E$ and
$\Delta \ge 0$. Then $q$ attains its minimum on the trust region $\|s\| \le \Delta$ at some $s$,
and this $s$ satisfies
* the Cauchy condition $q(s) \le q(-t g)$ for every Cauchy step $t$, and
* the eigenpoint condition $q(s) \le q(\Delta u)$ for every unit vector $u$. -/
theorem exists_isMinOn_quadModel_ball [FiniteDimensional ℝ E] (g : E) (H : E →L[ℝ] E) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    ∃ s, ‖s‖ ≤ Δ ∧ IsMinOn (quadModel g H) (closedBall 0 Δ) s ∧
      (∀ t, IsCauchyStep g H Δ t → quadModel g H s ≤ quadModel g H (-(t • g))) ∧
      (∀ u, ‖u‖ = 1 → quadModel g H s ≤ quadModel g H (Δ • u)) := by
  obtain ⟨s, hs, hmin⟩ := exists_isMinOn_closedBall g H hΔ
  exact ⟨s, hs, hmin, (quadModel_le_of_isMinOn_ball hmin).1,
    (quadModel_le_of_isMinOn_ball hmin).2 hΔ⟩

end Existence

end Optimization
