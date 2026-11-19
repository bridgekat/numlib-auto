/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter06.Section06

/-!
# Conn, Gould and Toint, Section 10.6: Dynamic accuracy in objective evaluations

This module formalizes the accuracy test for inexact objective values from Section 10.6 of
[conn2000trust]. The algorithm computes approximations $\tilde f(x_k)$ and $\tilde f(x_k + s_k)$
with errors at most $\delta_k^c$ and $\delta_k^t$, and requires both tolerances to be at most a
fixed fraction $\eta_0$ of the predicted decrease (10.6.2). An accepted step then decreases the
exact objective by at least $(\eta_1 - 2\eta_0)$ times the predicted decrease. Lemma 10.6.1 shows
that the refinement loop of Algorithm 10.6.1, which keeps the center and the radius fixed and
reduces the tolerances, passes the test after finitely many refinements at a center that is not
second-order critical.

The decrease conditions are AA.1, `ConnGouldToint.Chapter06.HasSufficientModelDecrease`, and the
negative-curvature condition `ConnGouldToint.Chapter06.HasNegativeCurvatureDecrease` of Chapter 6.

## Main definitions

* Equation (10.6.2), `ConnGouldToint.Chapter10.HasDecreaseAccuracy`: both tolerances are at most
  $\eta$ times the predicted decrease.

## Main results

* Equation (10.6.2), `ConnGouldToint.Chapter10.actual_decrease_of_accurate_ratio`: an accepted step
  with accurate evaluations decreases $f$ by at least $(\eta_1 - 2\eta_0)$ times the predicted
  decrease.
* Lemma 10.6.1, `ConnGouldToint.Chapter10.lemma_10_6_1`: at a center that is first-order
  noncritical, or critical with negative curvature, vanishing tolerances eventually pass the test
  (10.6.2).
* Algorithm 10.6.1, `ConnGouldToint.Chapter10.lemma_10_6_1_of_geometric_refinement`: if the
  tolerances contract by a uniform factor and the predicted decreases stay above a positive floor,
  the refinement loop ends.

## Implementation notes

* Lemma 10.6.1 is stated for a sequence of refinements $j$ with tolerances that tend to zero. At a
  first-order critical center, the negative curvature is given as an eventual margin
  $\tau_j \le -a < 0$ on the model curvatures.

## Deviations from the source

* **Lemma 10.6.1** (reading). The first-order clause uses a relative bound on the model gradient
  error. For the second-order clause, the statement takes an eventual negative model curvature
  margin in place of deriving it from Hessian agreement. The tolerances are assumed to tend
  to zero in the abstract form, and the geometric refinement theorem supplies this premise.
-/

open Filter Topology
open ConnGouldToint.Chapter06

namespace ConnGouldToint.Chapter10

/-- **Equation (10.6.2)** of [conn2000trust]. The tolerances $\delta^c$ and $\delta^t$ of the
objective values at the center and at the trial point satisfy the **decrease accuracy**
condition for $\eta$ and the predicted decrease $\delta^m$ if
$$\max\{\delta^c, \delta^t\} \le \eta\, \delta^m.$$
-/
def HasDecreaseAccuracy (η predicted centerTol trialTol : ℝ) : Prop :=
  max centerTol trialTol ≤ η * predicted

/-- **Equation (10.6.2)** of [conn2000trust], decrease of the exact objective. Let the predicted
decrease be $\delta^m > 0$, let the approximations satisfy $|\tilde f(x) - f(x)| \le \delta^c$
and $|\tilde f(x + s) - f(x + s)| \le \delta^t$, and let the tolerances satisfy (10.6.2) with
$\eta_0$. If the approximate ratio satisfies $(\tilde f(x) - \tilde f(x + s)) / \delta^m \ge
\eta_1$, then
$$(\eta_1 - 2\eta_0)\, \delta^m \le f(x) - f(x + s).$$

The real numbers `center` and `trial` stand for $f(x)$ and $f(x + s)$, and `centerApprox` and
`trialApprox` for their approximations. -/
theorem actual_decrease_of_accurate_ratio
    {center trial centerApprox trialApprox centerTol trialTol predicted η₀ η₁ : ℝ}
    (hp : 0 < predicted)
    (hc : |centerApprox - center| ≤ centerTol) (ht : |trialApprox - trial| ≤ trialTol)
    (hacc : HasDecreaseAccuracy η₀ predicted centerTol trialTol)
    (hratio : η₁ ≤ (centerApprox - trialApprox) / predicted) :
    (η₁ - 2 * η₀) * predicted ≤ center - trial := by
  have hr := (le_div_iff₀ hp).mp hratio
  have h₁ := (le_abs_self (centerApprox - center)).trans
    (hc.trans ((le_max_left _ _).trans hacc))
  have h₂ := (neg_abs_le (trialApprox - trial)).trans' (neg_le_neg
    (ht.trans ((le_max_right _ _).trans hacc)))
  linarith only [hr, h₁, h₂]

private theorem eventually_decreaseAccuracy_of_floor {η d : ℝ} (hη : 0 < η) (hd : 0 < d)
    {predicted centerTol trialTol : ℕ → ℝ}
    (hp : ∀ᶠ j in atTop, d ≤ predicted j)
    (ht : Tendsto (fun j ↦ max (centerTol j) (trialTol j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, HasDecreaseAccuracy η (predicted j) (centerTol j) (trialTol j) := by
  filter_upwards [hp, ht.eventually_lt_const (mul_pos hη hd)] with j hj hsmall
  exact hsmall.le.trans (mul_le_mul_of_nonneg_left hj hη.le)

/-- **Lemma 10.6.1** of [conn2000trust]. Let $E$ be a real normed space, $x \in E$ a fixed center,
$g \in E$ the objective gradient at $x$, and $\Delta, B, \eta > 0$. For each refinement $j$, let
$m_j$ be a model with gradient $g_j$ and curvature $\tau_j$, and $s_j$ a step, and assume:
* $0 < \beta_j \le B$, and $\|g_j - g\| \le e \|g\|$ for all $j$ with a fixed $e \in [0, 1)$;
* each $s_j$ satisfies AA.1 for $m_j$, $g_j$, $\beta_j$, $\Delta$ and $\kappa_1$;
* if $g = 0$, each $s_j$ satisfies the negative-curvature decrease condition for $m_j$,
  $\tau_j$, $\Delta$ and $\kappa_2$, and there is $a > 0$ with $\tau_j \le -a$ for all large
  $j$;
* the tolerances satisfy $\max\{\delta^c_j, \delta^t_j\} \to 0$.

Then, for all sufficiently large $j$, the tolerances satisfy the accuracy condition (10.6.2)
with $\eta$ and the predicted decrease $m_j(x) - m_j(x + s_j)$.

During refinement the center and the radius stay fixed. At a first-order noncritical center, the
gradient agreement gives a positive floor for $\|g_j\|$; at a first-order critical center, the
curvature margin gives a positive floor for the predicted decrease. In either case the vanishing
tolerances eventually pass the test. The curvature margin is a hypothesis of the statement.

**Reading.** Uses vanishing tolerances and directly assumes eventual negative model curvature at a
critical center.
-/
theorem lemma_10_6_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E) (gModel : ℕ → E) (τ : ℕ → ℝ) (m : ℕ → E → ℝ) (x : E) (s : ℕ → E)
    (β : ℕ → ℝ) (centerTol trialTol : ℕ → ℝ) {η Δ B κ₁ κ₂ : ℝ}
    (hη : 0 < η) (hΔ : 0 < Δ) (hB : 0 < B)
    (hβ : ∀ j, 0 < β j ∧ β j ≤ B)
    (hgrad : ∃ e ∈ Set.Ico (0 : ℝ) 1, ∀ j, ‖gModel j - g‖ ≤ e * ‖g‖)
    (hfirst : ∀ j, HasSufficientModelDecrease (m j) x (s j) (gModel j) (β j) Δ κ₁)
    (hsecond : g = 0 → ∀ j, HasNegativeCurvatureDecrease (m j) x (s j) (τ j) Δ κ₂)
    (hcurv : g = 0 → ∃ a > (0 : ℝ), ∀ᶠ j in atTop, τ j ≤ -a)
    (ht : Tendsto (fun j ↦ max (centerTol j) (trialTol j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop,
      HasDecreaseAccuracy η (m j x - m j (x + s j)) (centerTol j) (trialTol j) := by
  by_cases hg : g = 0
  · obtain ⟨a, ha, hτ⟩ := hcurv hg
    have hκ := (hsecond hg 0).1
    have hd : 0 < κ₂ * a * min (a ^ 2) (Δ ^ 2) :=
      mul_pos (mul_pos hκ ha) (lt_min (sq_pos_of_pos ha) (sq_pos_of_pos hΔ))
    exact eventually_decreaseAccuracy_of_floor hη hd
      (hτ.mono fun j hj ↦ negativeCurvatureDecrease_lower_bound (hsecond hg j)
        ha hΔ.le le_rfl hj) ht
  · obtain ⟨e, he, he'⟩ := hgrad
    let a := (1 - e) * ‖g‖
    have ha : 0 < a := mul_pos (sub_pos.mpr he.2) (norm_pos_iff.mpr hg)
    have hκ := (hfirst 0).1.1
    have hd : 0 < κ₁ * a * min (a / B) Δ :=
      mul_pos (mul_pos hκ ha) (lt_min (div_pos ha hB) hΔ)
    refine eventually_decreaseAccuracy_of_floor hη hd (Eventually.of_forall fun j ↦ ?_) ht
    have hgn : a ≤ ‖gModel j‖ := by
      have hh := norm_sub_le (gModel j) (gModel j - g)
      rw [sub_sub_cancel] at hh
      dsimp [a]
      linarith only [hh, he' j]
    have hh := div_le_div₀ (norm_nonneg _) hgn (hβ j).1 (hβ j).2
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hgn hκ.le) (min_le_min hh le_rfl)
      (le_min (div_nonneg ha.le hB.le) hΔ.le) (by positivity)).trans (hfirst j).2

/-- **Algorithm 10.6.1** of [conn2000trust], termination of the refinement loop. Let $\eta, d > 0$
and $0 \le q < 1$. Let the tolerances satisfy $\max\{\delta^c_j, \delta^t_j\} \ge 0$ and
$\max\{\delta^c_{j+1}, \delta^t_{j+1}\} \le q \max\{\delta^c_j, \delta^t_j\}$ for all $j$, and
let the predicted decreases satisfy $\delta^m_j \ge d$ for all large $j$. Then the accuracy
condition (10.6.2) holds with $\eta$ for some $j$.

**Reading.** Abstract geometric tolerance refinement with a uniform positive prediction floor.
-/
theorem lemma_10_6_1_of_geometric_refinement {η d q : ℝ} (hη : 0 < η) (hd : 0 < d)
    (hq : 0 ≤ q) (hq' : q < 1) {predicted centerTol trialTol : ℕ → ℝ}
    (ht₀ : ∀ j, 0 ≤ max (centerTol j) (trialTol j))
    (ht : ∀ j, max (centerTol (j + 1)) (trialTol (j + 1)) ≤
      q * max (centerTol j) (trialTol j))
    (hp : ∀ᶠ j in atTop, d ≤ predicted j) :
    ∃ j, HasDecreaseAccuracy η (predicted j) (centerTol j) (trialTol j) := by
  have hbound (j : ℕ) : max (centerTol j) (trialTol j) ≤
      q ^ j * max (centerTol 0) (trialTol 0) := by
    induction j with
    | zero => simp
    | succ j ih =>
      exact (ht j).trans ((mul_le_mul_of_nonneg_left ih hq).trans_eq (by rw [pow_succ]; ring))
  have hlim : Tendsto (fun j ↦ max (centerTol j) (trialTol j)) atTop (𝓝 0) := by
    apply squeeze_zero ht₀ hbound
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq').mul_const
      (max (centerTol 0) (trialTol 0))
  exact (eventually_decreaseAccuracy_of_floor hη hd hp hlim).exists

end ConnGouldToint.Chapter10
