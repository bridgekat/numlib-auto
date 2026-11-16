/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter10.Section03

/-!
# Conn, Gould and Toint, Section 10.3: The backtracking trust-region algorithm

This module formalizes Algorithm 10.3.2 of [conn2000trust], which combines the basic trust-region
algorithm with a backtracking line search. After a rejected step, the algorithm does not solve a new
subproblem. It searches along a direction $d$ of trust-region norm $\Delta$ for the first exponent
$j$ with the Armijo condition (10.3.5)
$$f(x + q^j d) \le f(x) + b q^j \langle \nabla f(x), d \rangle,$$
and uses the step $q^j d$. The module defines the corrected search direction, the Armijo test, the
trial test with a positive predicted decrease, and a run of the corrected algorithm, and proves that
the searches terminate. The run uses the radius update `ConnGouldToint.Chapter06.BTRRadiusUpdate`
and the ratio `ConnGouldToint.Chapter06.btrRatio` of the basic trust-region algorithm in
`NumlibSurface.ConnGouldToint.Chapter06.Section01`.

## Main definitions

* Algorithm 10.3.2, `ConnGouldToint.Chapter10.backtrackingTRDirection`: the rejected step if it is a
  descent direction, and the negative gradient otherwise, scaled to trust-region norm $\Delta$.
* Equation (10.3.5), `ConnGouldToint.Chapter10.backtrackingTRArmijo`: the Armijo test with the same
  exponent $j$ on both sides.
* Algorithm 10.3.2, `ConnGouldToint.Chapter10.backtrackingTRTrial`: the Armijo test together with a
  positive predicted decrease.
* Algorithm 10.3.2, `ConnGouldToint.Chapter10.BacktrackingTRRun`: a nonterminating run of the
  corrected algorithm.

## Main results

* Algorithm 10.3.2, `ConnGouldToint.Chapter10.backtrackingTRDirection_spec`: the direction lies on
  the trust-region boundary and has negative slope at a nonstationary point.
* Algorithm 10.3.2, `ConnGouldToint.Chapter10.exists_backtrackingTRArmijo`: a negative slope and a
  quadratic upper estimate give a first accepted exponent.
* Algorithm 10.3.2, `ConnGouldToint.Chapter10.exists_backtrackingTRTrial`: if the objective and the
  model share the slope and the estimate, the trial test passes at a first exponent.
* Algorithm 10.3.2, `ConnGouldToint.Chapter10.backtrackingTR_ascent_reuse_counterexample`: under the
  printed absolute angle condition, a rejected step can point uphill, and no positive multiple of it
  passes the Armijo test.

## Conventions

* The gradient $\nabla f(x)$ is `gradient f x`, the Riesz representative in the real inner product
  space $E$, which is assumed complete for the run.
* The trust-region norms are seminorms `Seminorm ℝ E` that vanish only at $0$.

## Deviations from the source

* **Equation (10.3.5)** (correction). The Armijo test uses the same exponent $j$ on both sides. See
  `ConnGouldToint.Chapter10.backtrackingTRArmijo`.
* **Algorithm 10.3.2, reuse of the rejected step** (correction). The rejected step is reused only if
  it is a descent direction; otherwise the negative gradient is used. Under the printed absolute
  angle condition, the rejected step can point uphill. See
  `ConnGouldToint.Chapter10.backtrackingTR_ascent_reuse_counterexample`.
* **Algorithm 10.3.2, trial test** (correction). An accepted probe must also have a positive
  predicted decrease, so that the ratio test is defined. See
  `ConnGouldToint.Chapter10.backtrackingTRTrial`.
-/

open Filter Optimization ConnGouldToint.Chapter06
open scoped RealInnerProductSpace Topology

namespace ConnGouldToint.Chapter10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Algorithm 10.3.2** of [conn2000trust], Step 1b, search direction. Let $p$ be a seminorm on
$E$, let $\Delta \in \mathbb{R}$, let $g \in E$ be the gradient and $s \in E$ the rejected step.
Let $d = s$ if $\langle g, s \rangle < 0$, and $d = -g$ otherwise. The **backtracking
direction** is $(\Delta / p(d)) \, d$.

**Correction.** The rejected step is reused only if it is a descent direction. Otherwise the
direction is the negative gradient. See
`ConnGouldToint.Chapter10.backtrackingTR_ascent_reuse_counterexample`.

The direction is normalized in the current trust-region norm $p$. -/
noncomputable def backtrackingTRDirection (p : Seminorm ℝ E) (Δ : ℝ) (g previous : E) : E :=
  let d := if ⟪g, previous⟫ < 0 then previous else -g
  (Δ / p d) • d

/-- **Algorithm 10.3.2** of [conn2000trust], properties of the direction. Let $p$ be a seminorm on
$E$ that vanishes only at $0$, let $\Delta > 0$, and let $g \neq 0$. For every rejected step
$s$, the backtracking direction $d$ satisfies $p(d) = \Delta$ and $\langle g, d \rangle < 0$. -/
theorem backtrackingTRDirection_spec (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 → v = 0) {Δ : ℝ} {g previous : E}
    (hΔ : 0 < Δ) (hg : g ≠ 0) :
    let d := backtrackingTRDirection p Δ g previous
    p d = Δ ∧ ⟪g, d⟫ < 0 := by
  let d := if ⟪g, previous⟫ < 0 then previous else -g
  have hslope : ⟪g, d⟫ < 0 := by
    dsimp [d]
    split
    · assumption
    · rw [inner_neg_right, real_inner_self_eq_norm_sq]
      exact neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hg))
  have hd : d ≠ 0 := by
    intro h
    simp [h] at hslope
  have hpd : 0 < p d := lt_of_le_of_ne (apply_nonneg p d) (fun h ↦ hd (hp d h.symm))
  have hscale := div_pos hΔ hpd
  change p ((Δ / p d) • d) = Δ ∧ ⟪g, (Δ / p d) • d⟫ < 0
  constructor
  · rw [map_smul_eq_mul, Real.norm_of_nonneg hscale.le, div_mul_cancel₀ _ hpd.ne']
  · rw [real_inner_smul_right]
    exact mul_neg_of_pos_of_neg hscale hslope

/-- **Equation (10.3.5)** of [conn2000trust]. Given $f : E \to \mathbb{R}$, a point $x$, a direction
$d$, numbers $q$, $b$ and a slope $\sigma$, the exponent $j \in \mathbb{N}$ passes the **Armijo
test** if
$$f(x + q^j d) \le f(x) + b q^j \sigma.$$

**Correction.** The test uses the same exponent $j$ in the step and in the predicted decrease. -/
def backtrackingTRArmijo (f : E → ℝ) (x d : E) (q b slope : ℝ) (j : ℕ) : Prop :=
  f (x + q ^ j • d) ≤ f x + b * q ^ j * slope

/-- **Algorithm 10.3.2** of [conn2000trust], termination of the Armijo search. Let $0 < q < 1$,
$b < 1$, $\sigma < 0$ and $L > 0$, and suppose that
$$f(x + t d) \le f(x) + t \sigma + L t^2 \quad \text{for all } t \in (0, 1].$$
Then there is an exponent $j$ that passes the Armijo test (10.3.5), while no exponent $i < j$
passes it. -/
theorem exists_backtrackingTRArmijo {f : E → ℝ} {x d : E}
    {q b slope L : ℝ} (hq : q ∈ Set.Ioo 0 1) (hb : b < 1)
    (hs : slope < 0) (hL : 0 < L)
    (hTaylor : ∀ t ∈ Set.Ioc (0 : ℝ) 1, f (x + t • d) ≤ f x + t * slope + L * t ^ 2) :
    ∃ j, backtrackingTRArmijo f x d q b slope j ∧
      ∀ i < j, ¬ backtrackingTRArmijo f x d q b slope i := by
  classical
  let r := (1 - b) * (-slope) / L
  have hr : 0 < r := div_pos (mul_pos (sub_pos.mpr hb) (neg_pos.mpr hs)) hL
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq.1.le hq.2).eventually (gt_mem_nhds hr)
  obtain ⟨j, hj⟩ := ht.exists
  have hpow : 0 < q ^ j := pow_pos hq.1 _
  have hqj : q ^ j ≤ 1 := pow_le_one₀ hq.1.le hq.2.le
  have hsmall : L * q ^ j ≤ (1 - b) * (-slope) := by
    have h := (le_div_iff₀ hL).mp hj.le
    linarith only [h]
  have hgood : backtrackingTRArmijo f x d q b slope j := by
    unfold backtrackingTRArmijo
    exact (hTaylor _ ⟨hpow, hqj⟩).trans (by
      nlinarith only [mul_le_mul_of_nonneg_right hsmall hpow.le])
  let hex : ∃ i, backtrackingTRArmijo f x d q b slope i := ⟨j, hgood⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hi ↦ Nat.find_min hex hi⟩

/-- **Algorithm 10.3.2** of [conn2000trust], trial test. Given $f, m : E \to \mathbb{R}$, $x$, $d$,
$q$, $b$ and a slope $\sigma$, the exponent $j$ passes the **trial test** if it passes the
Armijo test (10.3.5) and $m(x + q^j d) < m(x)$.

**Correction.** The positive predicted decrease is required, so that the probe can be used in
the ratio test. -/
def backtrackingTRTrial (f m : E → ℝ) (x d : E) (q b slope : ℝ) (j : ℕ) : Prop :=
  backtrackingTRArmijo f x d q b slope j ∧ m (x + q ^ j • d) < m x

/-- **Algorithm 10.3.2** of [conn2000trust], termination of Step 1b. Let $0 < q < 1$, $0 < b < 1$,
$\sigma < 0$ and $L > 0$, and suppose that for all $t \in (0, 1]$
$$f(x + t d) - f(x) \le t \sigma + L t^2 \quad \text{and} \quad m(x + t d) - m(x) \le t \sigma +
  L t^2.$$
Then there is an exponent $j$ that passes the trial test, while no exponent $i < j$ passes it.

The objective and the model have the same slope $\sigma$, as when the model gradient agrees with
the objective gradient. -/
theorem exists_backtrackingTRTrial {f m : E → ℝ} {x d : E}
    {q b slope L : ℝ} (hq : q ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1)
    (hs : slope < 0) (hL : 0 < L)
    (hTaylor : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      f (x + t • d) - f x ≤ t * slope + L * t ^ 2 ∧
      m (x + t • d) - m x ≤ t * slope + L * t ^ 2) :
    ∃ j, backtrackingTRTrial f m x d q b slope j ∧
      ∀ i < j, ¬ backtrackingTRTrial f m x d q b slope i := by
  classical
  let h (y : E) := max (f y - f x) (m y - m x)
  obtain ⟨j, hj, _⟩ := exists_backtrackingTRArmijo (f := h) (x := x) (d := d)
    hq hb.2 hs hL (fun t ht ↦ by
      have hbound := hTaylor t ht
      simpa [h] using (max_le hbound.1 hbound.2))
  have hh : h (x + q ^ j • d) ≤ b * q ^ j * slope := by
    simpa [backtrackingTRArmijo, h] using hj
  have hneg : b * q ^ j * slope < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hb.1 (pow_pos hq.1 _)) hs
  have hgood : backtrackingTRTrial f m x d q b slope j := by
    constructor
    · unfold backtrackingTRArmijo
      linarith only [(le_max_left _ _).trans hh]
    · exact sub_neg.mp ((le_max_right _ _).trans_lt (hh.trans_lt hneg))
  let hex : ∃ i, backtrackingTRTrial f m x d q b slope i := ⟨j, hgood⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hi ↦ Nat.find_min hex hi⟩

/-- **Algorithm 10.3.2** of [conn2000trust], a nonterminating run of the corrected algorithm. Let
$E$ be a real Hilbert space, $f : E \to \mathbb{R}$, $P$ the parameters of the basic
trust-region algorithm, $q, b, \Delta_{\max}, \kappa_1, \kappa_2 \in \mathbb{R}$ and
$\theta : E \to \mathbb{R}$ an angle function. A **backtracking trust-region run** consists of
iterates $x_k$, steps $s_k$, incoming radii $\Delta^{\mathrm{in}}_k$, radii $\Delta_k$,
trust-region seminorms $p_k$, models $m_k$, curvature constants $\beta_k$ and curvatures
$\tau_k$, with $0 < q < 1$ and $0 < b < 1/2$, such that for every $k$:

* $p_k$ vanishes only at $0$, $0 < \Delta^{\mathrm{in}}_k \le \Delta_{\max}$,
  $p_k(s_k) \le \Delta_k$ and $m_k(x_k) - m_k(x_k + s_k) > 0$;
* if $k = 0$ or iteration $k - 1$ is successful, then $\Delta_k = \Delta^{\mathrm{in}}_k$,
  $0 < \kappa_1 < 1$, $\kappa_2 > 0$, $\theta(x_k) \|\nabla f(x_k)\| \|s_k\| \le |\langle \nabla
  f(x_k), s_k \rangle|$, and with $g_k = \nabla f(x_k)$ the decrease
  $\delta_k = m_k(x_k) - m_k(x_k + s_k)$ satisfies $\kappa_1 \|g_k\| \min\{\|g_k\| / \beta_k,
  \Delta_k\} \le \delta_k$, and also $\kappa_2 |\tau_k| \min\{\tau_k^2, \Delta_k^2\} \le
  \delta_k$ if $\tau_k < 0$;
* if iteration $k$ is unsuccessful, then iteration $k + 1$ keeps the model,
  $\nabla f(x_{k+1}) \neq 0$, and its step is $q^j d$ for the backtracking direction $d$ of
  $s_k$ at radius $\Delta^{\mathrm{in}}_{k+1}$ and the first exponent $j$ that passes the trial
  test, with $\Delta_{k+1} = p_{k+1}(s_{k+1})$;
* $x_{k+1}$ is $x_k + s_k$ if the ratio $\rho_k$ is at least $\eta_1$, and $x_k$ otherwise;
* the radii $\Delta_k$ and $\Delta^{\mathrm{in}}_{k+1}$ satisfy the radius update (6.1.5) for
  $\rho_k$.

**Correction.** This is the corrected algorithm: the rejected step is reused only if it is a
descent direction, the Armijo test uses one exponent, and the accepted probe has positive
predicted decrease.

The incoming radius and the radius after a backtracking search are separate, so that the reset
of the radius is not counted as an update of the basic algorithm. -/
structure BacktrackingTRRun [CompleteSpace E] (f : E → ℝ) (P : BTRParams)
    (q b Δmax κ₁ κ₂ : ℝ) (angle : E → ℝ) where
  /-- The iterate $x_k$. -/
  x : ℕ → E
  /-- The step $s_k$. -/
  step : ℕ → E
  /-- The incoming radius $\Delta^{\mathrm{in}}_k$, which the radius update produces. -/
  incomingRadius : ℕ → ℝ
  /-- The radius $\Delta_k$ of the step actually taken. -/
  radius : ℕ → ℝ
  /-- The trust-region seminorm $p_k$. -/
  norm : ℕ → Seminorm ℝ E
  /-- The model $m_k$. -/
  model : ℕ → E → ℝ
  /-- The curvature constant $\beta_k$ of the sufficient model decrease condition. -/
  β : ℕ → ℝ
  /-- The curvature $\tau_k$ of the negative curvature decrease. -/
  curvature : ℕ → ℝ
  /-- The backtracking factor satisfies $0 < q < 1$. -/
  q_range : q ∈ Set.Ioo 0 1
  /-- The Armijo constant satisfies $0 < b < 1/2$. -/
  b_range : b ∈ Set.Ioo 0 (1 / 2)
  /-- Each seminorm $p_k$ vanishes only at $0$. -/
  separates : ∀ k v, norm k v = 0 → v = 0
  /-- Each incoming radius is positive. -/
  incoming_pos : ∀ k, 0 < incomingRadius k
  /-- Each incoming radius is at most $\Delta_{\max}$. -/
  incoming_cap : ∀ k, incomingRadius k ≤ Δmax
  /-- The step lies in the trust region: $p_k(s_k) \le \Delta_k$. -/
  feasible : ∀ k, norm k (step k) ≤ radius k
  /-- The predicted decrease is positive: $m_k(x_k) - m_k(x_k + s_k) > 0$. -/
  predicted_pos : ∀ k, 0 < model k (x k) - model k (x k + step k)
  /-- At iteration $0$ and after a successful iteration, the radius is the incoming radius, and the
  step satisfies the sufficient model decrease, the negative curvature decrease and the absolute
  angle condition $\theta(x_k) \|\nabla f(x_k)\| \|s_k\| \le |\langle \nabla f(x_k), s_k
  \rangle|$. -/
  fresh_trial : ∀ k,
    (k = 0 ∨ P.η₁ ≤ btrRatio f (model (k - 1)) (x (k - 1)) (step (k - 1))) →
    radius k = incomingRadius k ∧
    HasSufficientModelDecrease (model k) (x k) (step k) (gradient f (x k)) (β k) (radius k) κ₁ ∧
    HasNegativeCurvatureDecrease (model k) (x k) (step k) (curvature k) (radius k) κ₂ ∧
    angle (x k) * ‖gradient f (x k)‖ * ‖step k‖ ≤ |⟪gradient f (x k), step k⟫|
  /-- After an unsuccessful iteration $k$, iteration $k + 1$ keeps the model, has a nonzero
  gradient, and takes the step $q^j d$ along the backtracking direction $d$ for the first
  exponent $j$ that passes the trial test, with radius $p_{k+1}(q^j d)$. -/
  rejected_trial : ∀ k, btrRatio f (model k) (x k) (step k) < P.η₁ →
    let i := k + 1
    let g := gradient f (x i)
    let d := backtrackingTRDirection (norm i) (incomingRadius i) g (step k)
    model i = model k ∧ g ≠ 0 ∧
    ∃ j, backtrackingTRTrial f (model i) (x i) d q b ⟪g, d⟫ j ∧
      (∀ l < j, ¬ backtrackingTRTrial f (model i) (x i) d q b ⟪g, d⟫ l) ∧
      step i = q ^ j • d ∧ radius i = norm i (step i)
  /-- The iterate moves to $x_k + s_k$ exactly when $\rho_k \ge \eta_1$. -/
  iterate_update : ∀ k,
    x (k + 1) = acceptStep P.η₁ f (x k) (step k) (model k (x k) - model k (x k + step k))
  /-- The radius $\Delta_k$ and the next incoming radius satisfy the radius update (6.1.5) for the
  ratio $\rho_k$. -/
  radius_update : ∀ k, BTRRadiusUpdate P (btrRatio f (model k) (x k) (step k))
    (radius k) (incomingRadius (k + 1))

/-- **Algorithm 10.3.2** of [conn2000trust], counterexample to the unconditional reuse of the
rejected step. Let $f(x) = x + x^2$ and $m(x) = x - 2x^2$ on $\mathbb{R}$. Then $f$ and $m$ are
twice continuously differentiable, $f$ is bounded below, $m(0) = f(0)$ and $m'(0) = f'(0) = 1$.
The step $s = 1$ from $x = 0$ satisfies the sufficient model decrease with $\beta = 5$,
$\Delta = 1$ and $\kappa = 1/2$, and its ratio is below $\eta_1$ of the default parameters. But
for every $t > 0$,
$$f(0) + \tfrac{1}{4} t f'(0) < f(t),$$
so no positive multiple of the rejected step passes the Armijo test with $b = 1/4$.

The step points uphill, and still satisfies the printed absolute angle condition $|\langle
\nabla f(0), s \rangle| = \|\nabla f(0)\| \|s\|$. The default parameters are
`ConnGouldToint.Chapter06.defaultBTRParams`. -/
theorem backtrackingTR_ascent_reuse_counterexample :
    let f : ℝ → ℝ := fun x ↦ x + x ^ 2
    let m : ℝ → ℝ := fun x ↦ x - 2 * x ^ 2
    ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧ ContDiff ℝ 2 m ∧
      m 0 = f 0 ∧ deriv m 0 = deriv f 0 ∧ deriv f 0 = 1 ∧
      HasSufficientModelDecrease m 0 1 (gradient f 0) 5 1 (1 / 2) ∧
      btrRatio f m 0 1 < defaultBTRParams.η₁ ∧
      ∀ t > 0, f 0 + (1 / 4) * t * deriv f 0 < f (0 + t) := by
  dsimp only
  let f : ℝ → ℝ := fun x ↦ x + x ^ 2
  let m : ℝ → ℝ := fun x ↦ x - 2 * x ^ 2
  have hf : HasDerivAt f 1 0 := by
    convert (hasDerivAt_id (0 : ℝ)).add ((hasDerivAt_id (0 : ℝ)).pow 2) using 1
    · rfl
    · norm_num [id]
  have hm : HasDerivAt m 1 0 := by
    convert (hasDerivAt_id (0 : ℝ)).sub (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 2) using 1
    · rfl
    · norm_num [id]
  change ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧ ContDiff ℝ 2 m ∧
    m 0 = f 0 ∧ deriv m 0 = deriv f 0 ∧ deriv f 0 = 1 ∧
    HasSufficientModelDecrease m 0 1 (gradient f 0) 5 1 (1 / 2) ∧
    btrRatio f m 0 1 < defaultBTRParams.η₁ ∧
    ∀ t > 0, f 0 + (1 / 4) * t * deriv f 0 < f (0 + t)
  refine ⟨by unfold f; fun_prop, ⟨-1 / 4, ?_⟩, by unfold m; fun_prop,
    by norm_num [f, m], hm.deriv.trans hf.deriv.symm, hf.deriv, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    change -1 / 4 ≤ x + x ^ 2
    nlinarith [sq_nonneg (x + 1 / 2)]
  · rw [hf.hasGradientAt.gradient]
    norm_num [HasSufficientModelDecrease, m]
  · norm_num [btrRatio, reductionRatio, f, m, defaultBTRParams]
  · intro t ht
    rw [hf.deriv]
    dsimp [f]
    nlinarith [sq_nonneg t]

end ConnGouldToint.Chapter10
