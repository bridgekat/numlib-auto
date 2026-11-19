/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.QuadraticModel
import NumlibSurface.ConnGouldToint.Chapter17.Section01

/-!
# Conn, Gould and Toint, Section 17.2: Choosing the initial radius

Section 17.2 of [conn2000trust] discusses how to choose the initial trust-region radius $\Delta_0$
at a point $x$ with gradient $g \neq 0$ and model Hessian $H$ on a real inner product space $E$. The
simple choices are $\Delta_0 = 1$ and $\Delta_0 = \|g\| / 10$. A second choice is the length of the
minimizer of the quadratic model along the steepest-descent ray. A third choice, Algorithm 17.2.1,
probes the objective $f$ at the points $x - (\Delta / \|g\|) g$, compares the actual decrease with
the model decrease through the ratio $\rho$, and updates $\Delta$ by safeguarded quadratic
interpolation factors until the model predicts well. This module formalizes the formulas
(17.2.1)–(17.2.14), the corrected Algorithm 17.2.1 with bounded restarts, and its bound on the
number of objective evaluations. The interpolation factors come from
`NumlibSurface.ConnGouldToint.Chapter17.Section01`, and the quadratic model from
`Numlib.Optimization.Subproblem.Model`.

## Main definitions

* Equation (17.2.1), `ConnGouldToint.Chapter17.initialRadiusChoices`: the radii $1$ and
  $\|g\| / 10$.
* Equation (17.2.2), `ConnGouldToint.Chapter17.cauchyRayParameter`: the printed right-hand side
  $\|g\|^2 / \langle g, H g \rangle$.
* Equation (17.2.2), `ConnGouldToint.Chapter17.cauchyInitialRadius`: the corrected radius
  $\|g\|^3 / \langle g, H g \rangle$.
* Equation (17.2.3), `ConnGouldToint.Chapter17.initialProbeDisplacement`: the displacement
  $(\Delta / \|g\|) g$.
* Equation (17.2.4), `ConnGouldToint.Chapter17.initialProbeRatio`: the ratio of actual to predicted
  decrease at the probe.
* `ConnGouldToint.Chapter17.ProbeRadiusParams`: the safeguard constants $\gamma_1, \dots, \gamma_4$
  and the tolerances $\mu_1$, $\mu_2$ and $\theta$.
* Equation (17.2.5), `ConnGouldToint.Chapter17.probePredictsBadly`: $|\rho - 1| > \mu_1$.
* Equation (17.2.6), `ConnGouldToint.Chapter17.probePredictsWell`: $|\rho - 1| \le \mu_2$.
* Equations (17.2.8)–(17.2.9), `ConnGouldToint.Chapter17.probeInterpolationFactors`: the
  interpolation factors for the target ratios $1 - \theta$ and $1 + \theta$.
* Equation (17.2.10), `ConnGouldToint.Chapter17.probeFactorExtrema`: the smaller and the larger
  factor.
* Equations (17.2.11)–(17.2.13), `ConnGouldToint.Chapter17.safeguardedProbeFactor`: the safeguarded
  choice of the factor.
* Equation (17.2.7), `ConnGouldToint.Chapter17.probeRadiusUpdate`: the new radius, the safeguarded
  factor times $\Delta$.
* Equation (17.2.14), `ConnGouldToint.Chapter17.recommendedProbeParams` and
  `ConnGouldToint.Chapter17.recommendedProbeLimits`: the recommended constants and limits.
* Algorithm 17.2.1, `ConnGouldToint.Chapter17.InitialRadiusResult`: the output of the algorithm.
* Algorithm 17.2.1, `ConnGouldToint.Chapter17.chooseInitialRadius`: the corrected algorithm with
  bounded restarts.

## Main results

* Equation (17.2.2), `ConnGouldToint.Chapter17.cauchyInitialRadius_spec`: for
  $\langle g, H g \rangle > 0$, the corrected radius is the length of the model minimizer on the
  steepest-descent ray.
* Equation (17.2.3), `ConnGouldToint.Chapter17.norm_initialProbeDisplacement`: the probe
  displacement has length $\Delta$.
* Equation (17.2.7), `ConnGouldToint.Chapter17.safeguardedProbeFactor_mem`: the safeguarded factor
  lies in the interval that (17.2.7) prescribes for its case.
* Algorithm 17.2.1, `ConnGouldToint.Chapter17.chooseInitialRadius_evaluations_le`: at most
  $(i_{\max} + 1)(j_{\max} + 1)$ extra objective evaluations.
* Algorithm 17.2.1, `ConnGouldToint.Chapter17.chooseInitialRadius_value_spec`: the returned value is
  the objective value at the returned point and is at most $f(x)$.

## Deviations from the source

* **Correction.** Equation (17.2.2) multiplies the printed ray parameter by the gradient norm to
  obtain the radius. See `ConnGouldToint.Chapter17.cauchyInitialRadius`,
  `ConnGouldToint.Chapter17.cauchyInitialRadius_spec`.
* **Totalized ratio.** Equation (17.2.4) has a totalized ratio and the probe loop handles zero
  prediction explicitly. See `ConnGouldToint.Chapter17.initialProbeRatio`.
* **Completed shrink safeguard.** The poor-prediction safeguard strictly contracts the radius,
  including when both interpolation factors equal one. See
  `ConnGouldToint.Chapter17.safeguardedProbeFactor`,
  `ConnGouldToint.Chapter17.safeguardedProbeFactor_mem`,
  `ConnGouldToint.Chapter17.probeRadiusUpdate`.
* **Corrected finite probing.** Algorithm 17.2.1 enforces the advertised budgets, takes only
  improving restarts and handles zero gradient and zero prediction. See
  `ConnGouldToint.Chapter17.chooseInitialRadius`,
  `ConnGouldToint.Chapter17.chooseInitialRadius_evaluations_le`,
  `ConnGouldToint.Chapter17.chooseInitialRadius_value_spec`.
* **Equation (17.2.2)** (correction). The printed right-hand side $\|g\|^2 / \langle g, H g \rangle$
  is the ray parameter of the minimizer; the radius is this parameter times $\|g\|$. See
  `ConnGouldToint.Chapter17.cauchyInitialRadius_spec`.
* **Equations (17.2.7) and (17.2.11)–(17.2.13)** (reading). The shrink branch admits only factors
  strictly below $1$, and its fallback $\gamma_2$ is strictly below $1$. See
  `ConnGouldToint.Chapter17.safeguardedProbeFactor`.
* **Algorithm 17.2.1** (correction). A restart keeps the restart counter, so at most $j_{\max}$
  restarts happen, and each pass tests at most $i_{\max} + 1$ radii. See
  `ConnGouldToint.Chapter17.chooseInitialRadius`.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter17

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (17.2.1)** of [conn2000trust]. For a gradient $g \in E$, the two simple initial radii
are $\Delta_0 = 1$ and $\Delta_0 = \|g\| / 10$. -/
noncomputable def initialRadiusChoices (g : E) : ℝ × ℝ :=
  (1, ‖g‖ / 10)

/-- **Equation (17.2.2)** of [conn2000trust], printed right-hand side. For $g \in E$ and a
continuous linear map $H : E \to E$, the **Cauchy ray parameter** is
$$t = \frac{\|g\|^2}{\langle g, H g \rangle}.$$
If $\langle g, H g \rangle > 0$, the quadratic model is minimized along the ray $-u g$,
$u \in \mathbb{R}$, at $u = t$. The Lean division gives $t = 0$ when
$\langle g, H g \rangle = 0$. -/
noncomputable def cauchyRayParameter (g : E) (H : E →L[ℝ] E) : ℝ :=
  ‖g‖ ^ 2 / ⟪g, H g⟫

/-- **Equation (17.2.2)** of [conn2000trust], corrected. For $g \in E$ and a continuous linear map
$H : E \to E$, the **Cauchy initial radius** is
$$\Delta_0 = \frac{\|g\|^2}{\langle g, H g \rangle} \, \|g\|,$$
the Cauchy ray parameter times $\|g\|$.

**Correction.** The source prints $\Delta_0 = \|g\|^2 / \langle g, H g \rangle$. This is the
parameter of the minimizer on the unnormalized ray $-u g$, not the length of the minimizing
step. The length is this parameter times $\|g\|$; see
`ConnGouldToint.Chapter17.cauchyInitialRadius_spec`.

**Correction.** The printed right-hand side is the minimizing ray parameter. The initial radius is
its product with the gradient norm, which is the length of the minimizing displacement when the ray
curvature is positive.
-/
noncomputable def cauchyInitialRadius (g : E) (H : E →L[ℝ] E) : ℝ :=
  cauchyRayParameter g H * ‖g‖

/-- **Equation (17.2.2)** of [conn2000trust], corrected. Let $g \in E$ and let $H : E \to E$ be a
continuous linear map with $\langle g, H g \rangle > 0$. Let
$t = \|g\|^2 / \langle g, H g \rangle$ and let $q(s) = \langle g, s \rangle + \frac{1}{2}
\langle s, H s \rangle$. Then $\|-t g\| = \Delta_0$, the Cauchy initial radius, and
$$q(-t g) \le q(-u g) \quad \text{for all } u \in \mathbb{R}.$$

The model $q$ is `Subproblem.quadModel`.

**Correction.** The printed right-hand side is the minimizing ray parameter. The initial radius is
its product with the gradient norm, which is the length of the minimizing displacement when the ray
curvature is positive.
-/
theorem cauchyInitialRadius_spec {g : E} {H : E →L[ℝ] E} (hH : 0 < ⟪g, H g⟫) :
    let t := cauchyRayParameter g H
    ‖-(t • g)‖ = cauchyInitialRadius g H ∧
      ∀ u : ℝ, Subproblem.quadModel g H (-(t • g)) ≤
        Subproblem.quadModel g H (-(u • g)) := by
  let t := cauchyRayParameter g H
  have ht : 0 ≤ t := div_nonneg (sq_nonneg _) hH.le
  refine ⟨by rw [norm_neg, norm_smul, Real.norm_of_nonneg ht]; rfl, fun u ↦ ?_⟩
  rw [Optimization.quadModel_neg_smul, Optimization.quadModel_neg_smul]
  have hparam : t * ⟪g, H g⟫ = ‖g‖ ^ 2 := div_mul_cancel₀ _ hH.ne'
  rw [← hparam]
  nlinarith only [mul_nonneg (sq_nonneg (u - t)) hH.le]

/-- **Equation (17.2.3)** of [conn2000trust]. For $g \in E$ and $\Delta \in \mathbb{R}$, the **probe
displacement** is $d = (\Delta / \|g\|) g$. The probe point is $x - d$. When $g = 0$, the Lean
division gives $d = 0$. -/
noncomputable def initialProbeDisplacement (g : E) (Δ : ℝ) : E :=
  (Δ / ‖g‖) • g

/-- **Equation (17.2.3)** of [conn2000trust], length of the probe. If $g \neq 0$ and $\Delta \ge 0$,
then the probe displacement $d = (\Delta / \|g\|) g$ satisfies $\|d\| = \Delta$. -/
theorem norm_initialProbeDisplacement {g : E} (hg : g ≠ 0) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ‖initialProbeDisplacement g Δ‖ = Δ := by
  rw [initialProbeDisplacement, norm_smul, Real.norm_of_nonneg (by positivity),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hg)]

/-- **Equation (17.2.4)** of [conn2000trust]. Let $f, m : E \to \mathbb{R}$ and $x, d \in E$, where
the model $m$ agrees with $f$ at $x$. The **probe ratio** is
$$\rho = \frac{f(x) - f(x - d)}{f(x) - m(x - d)}.$$

The value $f(x)$ replaces $m(x)$ in the denominator, so the definition assumes $m(x) = f(x)$.
When the denominator is $0$, the Lean division gives $\rho = 0$.

**Reading.** The algebraic formula is evaluated in Lean's totalized real division, so the standalone
ratio is zero at zero predicted decrease. The probing procedure guards this case separately.
-/
noncomputable def initialProbeRatio (f m : E → ℝ) (x d : E) : ℝ :=
  (f x - f (x - d)) / (f x - m (x - d))

/-- The constants of the initial-radius probe in Section 17.2 of [conn2000trust]. An element
consists of real numbers $\gamma_1, \gamma_2, \gamma_3, \gamma_4, \mu_1, \mu_2, \theta$ with
$$0 < \gamma_1 \le \gamma_2 < 1 \le \gamma_3 \le \gamma_4, \qquad 0 < \theta \le \mu_2 <
  \mu_1.$$

The shrink fallback $\gamma_2$ is strictly below $1$, because the first branch of (17.2.7)
requires a factor in $[\gamma_1, 1)$. -/
structure ProbeRadiusParams where
  /-- The lower end $\gamma_1$ of the shrink interval $[\gamma_1, 1)$. -/
  γ₁ : ℝ
  /-- The shrink fallback $\gamma_2$, also the lower end of the interval $[\gamma_2, \gamma_3]$. -/
  γ₂ : ℝ
  /-- The default expansion factor $\gamma_3$, also the upper end of $[\gamma_2, \gamma_3]$. -/
  γ₃ : ℝ
  /-- The largest expansion factor $\gamma_4$. -/
  γ₄ : ℝ
  /-- The tolerance $\mu_1$: the probe predicts badly if $|\rho - 1| > \mu_1$. -/
  μ₁ : ℝ
  /-- The tolerance $\mu_2$: the probe predicts well if $|\rho - 1| \le \mu_2$. -/
  μ₂ : ℝ
  /-- The perturbation $\theta$ of the target ratios $1 - \theta$ and $1 + \theta$. -/
  θ : ℝ
  /-- The constant $\gamma_1$ is positive. -/
  gamma₁_pos : 0 < γ₁
  /-- The constants satisfy $\gamma_1 \le \gamma_2$. -/
  gamma₁_le_gamma₂ : γ₁ ≤ γ₂
  /-- The shrink fallback satisfies $\gamma_2 < 1$. -/
  gamma₂_lt_one : γ₂ < 1
  /-- The default expansion factor satisfies $1 \le \gamma_3$. -/
  one_le_gamma₃ : 1 ≤ γ₃
  /-- The expansion factors satisfy $\gamma_3 \le \gamma_4$. -/
  gamma₃_le_gamma₄ : γ₃ ≤ γ₄
  /-- The perturbation $\theta$ is positive. -/
  theta_pos : 0 < θ
  /-- The perturbation satisfies $\theta \le \mu_2$. -/
  theta_le_mu₂ : θ ≤ μ₂
  /-- The tolerances satisfy $\mu_2 < \mu_1$. -/
  mu₂_lt_mu₁ : μ₂ < μ₁

/-- **Equation (17.2.5)** of [conn2000trust]. The probe with ratio $\rho$ **predicts badly** if
$|\rho - 1| > \mu_1$. -/
abbrev probePredictsBadly (P : ProbeRadiusParams) (ρ : ℝ) : Prop := P.μ₁ < |ρ - 1|

/-- **Equation (17.2.6)** of [conn2000trust]. The probe with ratio $\rho$ **predicts well** if
$|\rho - 1| \le \mu_2$. -/
abbrev probePredictsWell (P : ProbeRadiusParams) (ρ : ℝ) : Prop := |ρ - 1| ≤ P.μ₂

/-- **Equations (17.2.8)–(17.2.9)** of [conn2000trust]. Let $a$ be the objective value at the base
point, $l$ the common slope along the probe ray, and $f_1$ and $m_1$ the values of the objective
and the model at the probe point. The **probe interpolation factors** are $t_1$ and $t_2$, the
interpolated radius factors of (17.1.3) for the target ratios $1 - \theta$ and $1 + \theta$:
$$t_{1,2} = \frac{\pm \theta\, l}{\pm \theta (a + l) + (1 \mp \theta) m_1 - f_1}.$$

Each factor is `ConnGouldToint.Chapter17.interpolatedRadiusFactor`. In Algorithm 17.2.1 the
slope along the probe ray $-d$ is $l = -\langle g, d \rangle$. -/
noncomputable def probeInterpolationFactors (P : ProbeRadiusParams) (a l f₁ m₁ : ℝ) : ℝ × ℝ :=
  (interpolatedRadiusFactor (1 - P.θ) a l f₁ m₁,
    interpolatedRadiusFactor (1 + P.θ) a l f₁ m₁)

/-- **Equation (17.2.10)** of [conn2000trust]. For $t_1, t_2 \in \mathbb{R}$, the smaller and the
larger interpolation factor are $(\min\{t_1, t_2\}, \max\{t_1, t_2\})$. -/
def probeFactorExtrema (t₁ t₂ : ℝ) : ℝ × ℝ := (min t₁ t₂, max t₁ t₂)

/-- **Equations (17.2.11)–(17.2.13)** of [conn2000trust]. Let $\rho$ be the probe ratio and
$t_1, t_2$ the interpolation factors. The **safeguarded factor** is chosen as follows.

* If the probe predicts badly, the factor is the largest of $t_1, t_2$ in $[\gamma_1, 1)$. If
  neither lies in this interval, it is $\gamma_2$ when $\min\{t_1, t_2\} \ge 1$ and $\gamma_1$
  otherwise.
* Otherwise, if the probe predicts well, the factor is $\gamma_3$ when $\max\{t_1, t_2\} < 1$
  and $\min\{\gamma_4, \max\{t_1, t_2\}\}$ otherwise.
* Otherwise the factor is $\max\{\gamma_2, \min\{\gamma_3, \max\{t_1, t_2\}\}\}$.

**Reading.** The first branch of (17.2.7) requires a factor in $[\gamma_1, 1)$. Therefore a
candidate equal to $1$ is not admissible on the shrink branch, and if both candidates are at
least $1$ the factor is the fallback $\gamma_2 < 1$.

**Correction.** A poor-prediction factor is always strictly below one. If both proposed factors are
at least one, the fallback is the interior shrink factor, including at equality where the printed
cases may return one.
-/
noncomputable def safeguardedProbeFactor (P : ProbeRadiusParams) (ρ t₁ t₂ : ℝ) : ℝ :=
  if probePredictsBadly P ρ then
    if t₁ ∈ Set.Ico P.γ₁ 1 then
      if t₂ ∈ Set.Ico P.γ₁ 1 then max t₁ t₂ else t₁
    else if t₂ ∈ Set.Ico P.γ₁ 1 then t₂
    else if 1 ≤ min t₁ t₂ then P.γ₂ else P.γ₁
  else if probePredictsWell P ρ then
    if max t₁ t₂ < 1 then P.γ₃ else min P.γ₄ (max t₁ t₂)
  else max P.γ₂ (min P.γ₃ (max t₁ t₂))

/-- **Equation (17.2.7)** of [conn2000trust], the safeguard intervals. For all probe parameters,
$\rho$, $t_1$ and $t_2$, the safeguarded factor lies in $[\gamma_1, 1)$ if the probe predicts
badly, in $[1, \gamma_4]$ if it does not predict badly but predicts well, and in
$[\gamma_2, \gamma_3]$ otherwise.

**Correction.** A poor-prediction factor is always strictly below one. If both proposed factors are
at least one, the fallback is the interior shrink factor, including at equality where the printed
cases may return one.
-/
theorem safeguardedProbeFactor_mem (P : ProbeRadiusParams) (ρ t₁ t₂ : ℝ) :
    safeguardedProbeFactor P ρ t₁ t₂ ∈
      (if probePredictsBadly P ρ then Set.Ico P.γ₁ 1
       else if probePredictsWell P ρ then Set.Icc 1 P.γ₄ else Set.Icc P.γ₂ P.γ₃) := by
  unfold safeguardedProbeFactor
  by_cases hb : probePredictsBadly P ρ
  · simp only [ite_eq_left hb]
    split
    · rename_i h₁
      split
      · rename_i h₂
        exact ⟨h₁.1.trans (le_max_left _ _), max_lt h₁.2 h₂.2⟩
      · exact h₁
    · split
      · assumption
      · split
        · exact ⟨P.gamma₁_le_gamma₂, P.gamma₂_lt_one⟩
        · exact ⟨le_rfl, P.gamma₁_le_gamma₂.trans_lt P.gamma₂_lt_one⟩
  · simp only [ite_eq_right hb]
    by_cases hw : probePredictsWell P ρ
    · simp only [ite_eq_left hw]
      split
      · exact ⟨P.one_le_gamma₃, P.gamma₃_le_gamma₄⟩
      · rename_i hn
        exact ⟨le_min (P.one_le_gamma₃.trans P.gamma₃_le_gamma₄) (le_of_not_gt hn), min_le_left _ _⟩
    · simp only [ite_eq_right hw]
      exact ⟨le_max_left _ _, max_le (P.gamma₂_lt_one.le.trans P.one_le_gamma₃) (min_le_left _ _)⟩

/-- **Equation (17.2.7)** of [conn2000trust]. The **probe radius update** is
$\Delta^+ = \gamma \Delta$, where $\gamma$ is the safeguarded factor for the probe ratio $\rho$
and the interpolation factors $t_1, t_2$.

**Correction.** A poor-prediction factor is always strictly below one. If both proposed factors are
at least one, the fallback is the interior shrink factor, including at equality where the printed
cases may return one.
-/
noncomputable def probeRadiusUpdate (P : ProbeRadiusParams) (ρ t₁ t₂ Δ : ℝ) : ℝ :=
  safeguardedProbeFactor P ρ t₁ t₂ * Δ

/-- **Equation (17.2.14)** of [conn2000trust]. The recommended probe constants are
$$\gamma_1 = 0.0625, \quad \gamma_2 = 0.5, \quad \gamma_3 = 2, \quad \gamma_4 = 5, \quad \mu_1 =
  0.5, \quad \mu_2 = 0.35, \quad \theta = 0.25.$$
-/
noncomputable def recommendedProbeParams : ProbeRadiusParams where
  γ₁ := 0.0625
  γ₂ := 0.5
  γ₃ := 2
  γ₄ := 5
  μ₁ := 0.5
  μ₂ := 0.35
  θ := 0.25
  gamma₁_pos := by norm_num
  gamma₁_le_gamma₂ := by norm_num
  gamma₂_lt_one := by norm_num
  one_le_gamma₃ := by norm_num
  gamma₃_le_gamma₄ := by norm_num
  theta_pos := by norm_num
  theta_le_mu₂ := by norm_num
  mu₂_lt_mu₁ := by norm_num

/-- **Equation (17.2.14)** of [conn2000trust]. The recommended limits are $i_{\max} = 4$ on the
trial index and $j_{\max} = 1$ on the number of restarts. -/
def recommendedProbeLimits : ℕ × ℕ := (4, 1)

/-- **Algorithm 17.2.1** of [conn2000trust], output. A result consists of a point, the cached
objective value at that point, the initial radius, and the number of additional objective
evaluations. -/
structure InitialRadiusResult (E : Type*) where
  /-- The returned point. -/
  point : E
  /-- The cached objective value at the returned point. -/
  value : ℝ
  /-- The returned initial radius. -/
  radius : ℝ
  /-- The number of objective evaluations after the evaluation at the starting point. -/
  evaluations : ℕ

private structure RadiusProbePass (E : Type*) where
  bestPoint : E
  bestValue : ℝ
  adequate : ℝ
  radius : ℝ

private noncomputable def radiusProbePass (P : ProbeRadiusParams) (f m : E → ℝ)
    (x g : E) (fx : ℝ) : ℕ → RadiusProbePass E → RadiusProbePass E
  | i, state =>
    let d := initialProbeDisplacement g state.radius
    let trial := x - d
    let fTrial := f trial
    let mTrial := m trial
    let pred := fx - mTrial
    let ρ := (fx - fTrial) / pred
    let next : RadiusProbePass E := {
      bestPoint := if fTrial < state.bestValue then trial else state.bestPoint
      bestValue := min fTrial state.bestValue
      adequate := if pred ≠ 0 ∧ |ρ - 1| ≤ P.μ₁ then max state.adequate state.radius
        else state.adequate
      radius := state.radius }
    match i with
    | 0 => next
    | i + 1 =>
      let candidates := probeInterpolationFactors P fx (-⟪g, d⟫) fTrial mTrial
      let radius := if pred = 0 then P.γ₂ * state.radius
        else probeRadiusUpdate P ρ candidates.1 candidates.2 state.radius
      radiusProbePass P f m x g fx i { next with radius := radius }

private noncomputable def radiusProbeRestarts (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax : ℕ) :
    ℕ → E → ℝ → ℝ → InitialRadiusResult E
  | j, x, fx, adequate =>
    let Δ := seed x
    if ‖g x‖ = 0 then ⟨x, fx, max Δ adequate, 0⟩
    else
      let pass := radiusProbePass P f (m x) x (g x) fx iMax ⟨x, fx, adequate, Δ⟩
      let result : InitialRadiusResult E := ⟨x, fx, max pass.radius pass.adequate, iMax + 1⟩
      match j with
      | 0 => result
      | j + 1 =>
        if pass.bestValue < fx then
          let later := radiusProbeRestarts P f m g seed iMax j
            pass.bestPoint pass.bestValue pass.adequate
          { later with evaluations := iMax + 1 + later.evaluations }
        else result

/-- **Algorithm 17.2.1** of [conn2000trust], corrected. Let $f : E \to \mathbb{R}$, and for each
base point $x$ let $m_x$ be a model, $g(x)$ a gradient and $\sigma(x)$ a seed radius. Let
$i_{\max}, j_{\max} \in \mathbb{N}$. The algorithm starts at $x$ with the cached value $f(x)$
and the adequate radius $0$, and runs one pass at each base point.

* If $g(x) = 0$, it returns $x$, $f(x)$, the radius $\max\{\sigma(x), \Delta_{\mathrm{ad}}\}$,
  where $\Delta_{\mathrm{ad}}$ is the adequate radius, and $0$ evaluations.
* Otherwise a pass probes $i_{\max} + 1$ radii, starting from $\Delta = \sigma(x)$. At each
  radius it evaluates $f$ and $m_x$ at $x - d$ with $d = (\Delta / \|g(x)\|) g(x)$, records the
  best probe point, and replaces $\Delta_{\mathrm{ad}}$ by
  $\max\{\Delta_{\mathrm{ad}}, \Delta\}$ if the predicted decrease $f(x) - m_x(x - d)$ is
  nonzero and $|\rho - 1| \le \mu_1$. Before the next probe, $\Delta$ is multiplied by the
  safeguarded factor of (17.2.7), or by $\gamma_2$ if the predicted decrease is $0$.
* After the pass, if restarts remain and the best probe value is less than the cached value, the
  algorithm restarts at the best probe point with one restart fewer and keeps
  $\Delta_{\mathrm{ad}}$. Otherwise it returns $x$, the cached value, the radius
  $\max\{\Delta, \Delta_{\mathrm{ad}}\}$ for the last probed $\Delta$, and $i_{\max} + 1$
  evaluations. The evaluations of all passes are added.

**Correction.** A restart keeps the remaining restart count, so at most $j_{\max}$ restarts
happen, and each pass probes at most $i_{\max} + 1$ radii. Then the number of objective
evaluations is bounded; see `ConnGouldToint.Chapter17.chooseInitialRadius_evaluations_le`.

The probe at a zero predicted decrease cannot be adequate, and the next probe uses the strict
shrink fallback $\gamma_2$. The probe parameters are
`ConnGouldToint.Chapter17.ProbeRadiusParams`.

**Correction.** Each pass tests at most the declared number of radii, the restart budget is carried
between passes, and only strict objective improvement restarts the pass. A zero gradient stops
probing and a zero prediction uses fallback shrinkage. The evaluation bound counts only trial
evaluations.
-/
noncomputable def chooseInitialRadius (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax jMax : ℕ) (x : E) :
    InitialRadiusResult E :=
  radiusProbeRestarts P f m g seed iMax jMax x (f x) 0

private theorem radiusProbeRestarts_evaluations_le (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax j : ℕ) (x : E) (fx adequate : ℝ) :
    (radiusProbeRestarts P f m g seed iMax j x fx adequate).evaluations ≤ (iMax + 1) * (j + 1) := by
  induction j generalizing x fx adequate with
  | zero =>
    rw [radiusProbeRestarts]
    split <;> simp
  | succ j ih =>
    rw [radiusProbeRestarts]
    dsimp only
    split
    · exact Nat.zero_le _
    · split
      · rw [Nat.mul_succ, Nat.add_comm ((iMax + 1) * (j + 1))]
        exact Nat.add_le_add_left (ih _ _ _) _
      · exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

/-- **Algorithm 17.2.1** of [conn2000trust], evaluation bound. For all probe parameters, objectives,
models, gradients, seed radii, limits $i_{\max}, j_{\max}$ and starting points, the corrected
algorithm uses at most $(i_{\max} + 1)(j_{\max} + 1)$ objective evaluations after the evaluation
of $f$ at the starting point.

**Correction.** Each pass tests at most the declared number of radii, the restart budget is carried
between passes, and only strict objective improvement restarts the pass. A zero gradient stops
probing and a zero prediction uses fallback shrinkage. The evaluation bound counts only trial
evaluations.
-/
theorem chooseInitialRadius_evaluations_le (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax jMax : ℕ) (x : E) :
    (chooseInitialRadius P f m g seed iMax jMax x).evaluations ≤ (iMax + 1) * (jMax + 1) :=
  radiusProbeRestarts_evaluations_le P f m g seed iMax jMax x (f x) 0

private theorem radiusProbePass_bestValue (P : ProbeRadiusParams) (f m : E → ℝ)
    (x g : E) (fx : ℝ) (i : ℕ) (state : RadiusProbePass E)
    (hstate : state.bestValue = f state.bestPoint) :
    let result := radiusProbePass P f m x g fx i state
    result.bestValue = f result.bestPoint := by
  induction i generalizing state with
  | zero =>
    rw [radiusProbePass]
    dsimp only
    split
    · rename_i h
      exact min_eq_left h.le
    · rename_i h
      exact (min_eq_right (le_of_not_gt h)).trans hstate
  | succ i ih =>
    rw [radiusProbePass]
    dsimp only
    apply ih
    dsimp only
    split
    · rename_i h
      exact min_eq_left h.le
    · rename_i h
      exact (min_eq_right (le_of_not_gt h)).trans hstate

private theorem radiusProbeRestarts_value_spec (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax j : ℕ)
    (x : E) (fx adequate : ℝ) (hfx : fx = f x) :
    let result := radiusProbeRestarts P f m g seed iMax j x fx adequate
    result.value = f result.point ∧ result.value ≤ fx := by
  induction j generalizing x fx adequate with
  | zero =>
    rw [radiusProbeRestarts]
    dsimp only
    split <;> exact ⟨hfx, le_rfl⟩
  | succ j ih =>
    rw [radiusProbeRestarts]
    dsimp only
    split
    · exact ⟨hfx, le_rfl⟩
    · split
      · rename_i hbetter
        have hb := radiusProbePass_bestValue P f (m x) x (g x) fx iMax
          ⟨x, fx, adequate, seed x⟩ hfx
        let pass := radiusProbePass P f (m x) x (g x) fx iMax ⟨x, fx, adequate, seed x⟩
        have h := ih pass.bestPoint pass.bestValue pass.adequate hb
        exact ⟨h.1, h.2.trans hbetter.le⟩
      · exact ⟨hfx, le_rfl⟩

/-- **Algorithm 17.2.1** of [conn2000trust], returned value. For all probe parameters, objectives,
models, gradients, seed radii, limits and starting points $x$, the value returned by the
corrected algorithm is the objective value at the returned point, and it is at most $f(x)$. Thus
restarts can only improve the objective value.

**Correction.** Each pass tests at most the declared number of radii, the restart budget is carried
between passes, and only strict objective improvement restarts the pass. A zero gradient stops
probing and a zero prediction uses fallback shrinkage. The evaluation bound counts only trial
evaluations.
-/
theorem chooseInitialRadius_value_spec (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax jMax : ℕ) (x : E) :
    let result := chooseInitialRadius P f m g seed iMax jMax x
    result.value = f result.point ∧ result.value ≤ f x :=
  radiusProbeRestarts_value_spec P f m g seed iMax jMax x (f x) 0 rfl

end ConnGouldToint.Chapter17
