/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Numlib.Nonlinear.MonotoneNewton
import Numlib.Optimization.Subproblem.Secular

/-!
# Iterations for the secular equation

Let $H$ be a symmetric operator on a finite-dimensional real inner product space, with leftmost
eigenvalue $\lambda_1$, let $g \neq 0$, let $s(\lambda) = -(H + \lambda)^{-1} g$, and let
$\pi(\lambda) = \|s(\lambda)\|^2$ be the secular function of
`Numlib.Optimization.Subproblem.Secular`. Write $\lambda_s = \max(0, -\lambda_1)$. In the easy case,
the multiplier $\lambda_*$ of the trust-region and regularization subproblems is the root in
$(\lambda_s, \infty)$ of a secular equation $\pi(\lambda) = \tau(\lambda)$, with $\tau = \Delta^2$
for the trust region and $\tau(\lambda) = (\lambda/\sigma)^{2/(r-2)}$ for regularization. This file
follows §8.2–§8.3 of [cartis2022evaluation]. It proves that the corrections computed there from a
current value $\lambda_c$ in $\mathcal{L} = (\lambda_s, \lambda_*]$ never pass $\lambda_*$, and that
the resulting monotone iterations converge to $\lambda_*$.

Two kinds of correction are treated. A Newton correction is a Newton step on a transformed secular
function $\theta_\beta = \pi^\beta - \tau^\beta$, which is convex and decreasing or concave and
increasing, so that the Newton step stays on the left of the root. A Taylor correction of odd order
$k$ is the rightmost root $\delta$ of $t_k(\delta) = \tau(\lambda_c + \delta)$, where $t_k$ is the
Taylor polynomial of $\pi$ at $\lambda_c$; since $t_k \le \pi$ to the right of $\lambda_c$, this
root does not pass $\lambda_*$. From a point $\lambda_c \in \mathcal{G} = (\lambda_*, \infty)$, the
Newton corrections overshoot to a point at most $\lambda_*$.

## Main definitions

* `Subproblem.secularTaylor`: the Taylor polynomial $t_k(\delta)$ of $\pi$ at $\lambda_c$, as in
  (8.2.12).
* `Subproblem.taylorCorrection`: the rightmost root of $t_k(\delta) = \tau(\lambda_c + \delta)$, as
  in (8.2.15).
* `Subproblem.trSecular`, `Subproblem.regSecular`: the transformed secular functions
  $\theta_\beta = \pi^\beta - \tau^\beta$ of the two subproblems.
* `Subproblem.trNewtonCorrection`, `Subproblem.regNewtonCorrection`: the Newton corrections (8.2.24)
  and (8.2.25) on $\theta_\beta$.
* `Subproblem.IsSecularTarget`: the standing hypotheses of the Taylor iterations.

## Main results

* `Subproblem.newtonCorrection_eq`, `Subproblem.trNewtonCorrection_eq`,
  `Subproblem.regNewtonCorrection_eq`: the Newton corrections in closed form, as in (B.8.7),
  (8.2.24) and (8.2.25).
* `Subproblem.trSecular_shape`, `Subproblem.regSecular_shape`: convexity, monotonicity and the sign
  of the derivative of $\theta_\beta$.
* `Subproblem.trNewtonCorrection_mem`, `Subproblem.regNewtonCorrection_mem`: from
  $\lambda_c \le \lambda_*$ the Newton corrections land in $[\lambda_c, \lambda_*]$, and from
  $\lambda_c > \lambda_*$ they land at most at $\lambda_*$.
* `Subproblem.IsSecularTarget.taylorCorrection_mem`,
  `Subproblem.IsSecularTarget.isGreatest_taylorCorrection`: the Taylor corrections of odd order are
  attained roots of (8.2.15) and land in $[\lambda_c, \lambda_*]$.
* `Subproblem.tendsto_of_trNewtonCorrection_le`, `Subproblem.tendsto_of_regNewtonCorrection_le`:
  iterations that take steps at least as long as a Newton correction without passing $\lambda_*$
  increase to $\lambda_*$, globally $Q$-linearly and $Q$-superlinearly. This covers plain Newton,
  the $\beta$-maximizing iteration (8.2.26) and Algorithms 8.3.1 and 8.3.2.
* `Subproblem.IsSecularTarget.tendsto_of_taylorCorrection_le`: the same iterations with Taylor
  corrections of odd order increase to $\lambda_*$.

## Implementation notes

* The root $\lambda_*$ is a hypothesis ($\pi(\lambda_*) = \tau(\lambda_*)$ with
  $\lambda_* > \lambda_s$, the easy case), not the multiplier of a global minimizer. The two agree
  by the optimality conditions of §8.3 of [cartis2022evaluation].
* The domain is $\lambda > -\lambda_1$ for the trust region and the Taylor corrections, and
  $\lambda > \lambda_s = \max(0, -\lambda_1)$ for regularization, where
  $\lambda \mapsto (\lambda/\sigma)^\gamma$ needs $\lambda > 0$. The convexity of $-\lambda^\gamma$
  for $\gamma \in (0, 1]$ and its concavity for $\gamma < 0$ hold on $\lambda > 0$, and the interval
  $\lambda \ge \lambda_s$ may contain $0$ when $\lambda_1 \ge 0$.
* In (8.2.25) the parameter $\beta_j \in [-1/2, (r-2)/2]$ must be nonzero, since
  $\theta_0 \equiv 0$. The limit $\beta \to 0$ of the trust-region factor is
  $\operatorname{newtonFactor}(m, 0) = -\log m$ (`Subproblem.newtonFactor`), which gives the Newton
  step for $\log \pi - \log \tau$; this step is not treated here.
* The file does not prove the ultimate $Q$-order $k$ of the Taylor iterations of odd order that §8.3
  states; it proves only their convergence.
* The file does not treat the overshoot from $\mathcal{G}$ in the hard case, where
  $\lambda_* = \lambda_s$ is not a root in the open domain, nor the remark on the least negative
  root in §8.2.1.
-/

open Set Filter Topology
open Finset (range)
open scoped Nat RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E}

/-! ### Definitions -/

/-- The **Taylor polynomial** of order $k$ of the secular function at $\lambda_c$:
$$t_k(\delta) = \sum_{j=0}^{k} \frac{\pi^{(j)}(\lambda_c)}{j!} \delta^j.$$
This is (8.2.12) of [cartis2022evaluation]. -/
noncomputable def secularTaylor (g : E) (H : E →L[ℝ] E) (k : ℕ) (lamc δ : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j

/-- The **Taylor correction** $\delta_k^T(\lambda_c)$ of [cartis2022evaluation], §8.2.1 and
Algorithm 8.3.1: the rightmost real root $\delta$ of the equation (8.2.15)
$$t_k(\delta) = \tau(\lambda_c + \delta),$$
where $t_k$ is the Taylor polynomial `Subproblem.secularTaylor` of order $k$ of $\pi$ at
$\lambda_c$.

It is defined as the supremum of the set of roots. If this set is empty or not bounded above,
the value is $0$, by the Lean convention for `sSup` on $\mathbb{R}$. For odd $k$ and
$\lambda_c \in \mathcal{L}$ the set is nonempty and bounded above
(`Subproblem.IsSecularTarget.taylorCorrection_mem`), and the supremum is attained
(`Subproblem.IsSecularTarget.isGreatest_taylorCorrection`). -/
noncomputable def taylorCorrection (g : E) (H : E →L[ℝ] E) (τ : ℝ → ℝ) (k : ℕ) (lamc : ℝ) : ℝ :=
  sSup {δ | secularTaylor g H k lamc δ = τ (lamc + δ)}

/-- The **transformed trust-region secular function** $\theta_\beta(\lambda) = \pi(\lambda)^\beta -
\Delta^{2\beta}$. This is (8.2.16) of [cartis2022evaluation] with $\tau = \Delta^2$. -/
noncomputable def trSecular (g : E) (H : E →L[ℝ] E) (Δ β lam : ℝ) : ℝ :=
  secular g H lam ^ β - Δ ^ (2 * β)

/-- The **trust-region Newton correction** at $\lambda_c$:
$$\delta^N(\lambda_c) = \frac{2 \pi(\lambda_c)}{\pi'(\lambda_c)} \left(1 -
  \frac{\|s(\lambda_c)\|}{\Delta}\right).$$
This is (8.2.24) of [cartis2022evaluation].

By `Subproblem.trNewtonCorrection_eq`, it is the Newton step for
$\pi(\lambda)^{-1/2} = \Delta^{-1}$, that is, for $\theta_{-1/2} = 0$. -/
noncomputable def trNewtonCorrection (g : E) (H : E →L[ℝ] E) (Δ lamc : ℝ) : ℝ :=
  2 * secular g H lamc / deriv (secular g H) lamc * (1 - ‖step g H lamc‖ / Δ)

/-- The **transformed regularization secular function** $\theta_\beta(\lambda) =
\pi(\lambda)^\beta - (\lambda / \sigma)^{2\beta/(r-2)}$, as in §8.2.2 of [cartis2022evaluation]. -/
noncomputable def regSecular (g : E) (H : E →L[ℝ] E) (σ r β lam : ℝ) : ℝ :=
  secular g H lam ^ β - (lam / σ) ^ (2 * β / (r - 2))

/-- The **regularization Newton correction** at $\lambda_c$: the Newton step
$$\delta^N(\lambda_c, \beta) = -\frac{\theta_\beta(\lambda_c)}{\theta_\beta'(\lambda_c)}$$
on the transformed regularization secular function $\theta_\beta$. This is the first line of
(8.2.25) of [cartis2022evaluation].

The closed form of the last line of (8.2.25) is `Subproblem.regNewtonCorrection_eq`. -/
noncomputable def regNewtonCorrection (g : E) (H : E →L[ℝ] E) (σ r β lamc : ℝ) : ℝ :=
  -regSecular g H σ r β lamc / deriv (regSecular g H σ r β) lamc

variable {g : E} {hH : (H : E →ₗ[ℝ] E).IsSymmetric}

/-! ### Derivatives -/

/-- For $g \neq 0$, $\lambda > -\lambda_1$ and $\Delta, \beta \in \mathbb{R}$, the transformed
trust-region secular function $\theta_\beta$ has the derivative $\beta \, \pi(\lambda)^{\beta -
1} \pi'(\lambda)$ at $\lambda$. -/
theorem hasDerivAt_trSecular (hg : g ≠ 0) {lam : ℝ} (hlam : -leftmost hH < lam) (Δ β : ℝ) :
    HasDerivAt (trSecular g H Δ β)
      (β * secular g H lam ^ (β - 1) * deriv (secular g H) lam) lam :=
  (hasDerivAt_secular_rpow hg hlam β).sub_const _

/-- For $g \neq 0$, $\sigma > 0$, $\lambda > -\lambda_1$ and $\lambda > 0$, the transformed
regularization secular function $\theta_\beta$ has the derivative
$$\beta \, \pi(\lambda)^{\beta - 1} \pi'(\lambda) - \frac{2\beta}{r - 2}
  \left(\frac{\lambda}{\sigma}\right)^{2\beta/(r-2) - 1} \frac{1}{\sigma}$$
at $\lambda$. -/
theorem hasDerivAt_regSecular (hg : g ≠ 0) {σ r β lam : ℝ} (hσ : 0 < σ)
    (hlam : -leftmost hH < lam) (hpos : 0 < lam) :
    HasDerivAt (regSecular g H σ r β)
      (β * secular g H lam ^ (β - 1) * deriv (secular g H) lam -
        2 * β / (r - 2) * (lam / σ) ^ (2 * β / (r - 2) - 1) / σ) lam := by
  have h2 := ((hasDerivAt_id' lam).div_const σ).rpow_const (p := 2 * β / (r - 2))
    (Or.inl (div_pos hpos hσ).ne')
  exact ((hasDerivAt_secular_rpow hg hlam β).sub h2).congr_deriv (by ring)

/-! ### Closed forms of the Newton corrections -/

/-- **The Newton step on the transformed trust-region secular equation.** Let $g \neq 0$,
$\lambda_c > -\lambda_1$, $\Delta > 0$ and $\beta \neq 0$, and write $\pi = \pi(\lambda_c)$ and
$\pi' = \pi'(\lambda_c)$. Then the Newton correction for $\theta_\beta(\lambda) =
\pi(\lambda)^\beta - \Delta^{2\beta} = 0$ from $\lambda_c$ is
$$-\frac{\theta_\beta(\lambda_c)}{\theta_\beta'(\lambda_c)} = -\frac{\pi}{\pi'}
  \operatorname{newtonFactor}\left(\frac{\Delta^2}{\pi}, \beta\right) = -\frac{\pi}{\pi'} \cdot
  \frac{1 - (\Delta^2/\pi)^\beta}{\beta}.$$
This is (B.8.7) of [cartis2022evaluation].

By `Subproblem.antitone_newtonFactor` (Lemma B.8.2), the correction decreases as $\beta$
increases. So $\beta = -1/2$ (`Subproblem.trNewtonCorrection_eq`) gives the longest step among
$\beta \ge -1/2$. -/
theorem newtonCorrection_eq (hg : g ≠ 0) {lamc Δ β : ℝ} (hlam : -leftmost hH < lamc)
    (hΔ : 0 < Δ) (hβ : β ≠ 0) :
    -trSecular g H Δ β lamc / deriv (trSecular g H Δ β) lamc =
      -secular g H lamc / deriv (secular g H) lamc *
        newtonFactor (Δ ^ 2 / secular g H lamc) β := by
  rw [(hasDerivAt_trSecular hg hlam Δ β).deriv, newtonFactor_of_ne_zero _ hβ, trSecular,
    Real.div_rpow (sq_nonneg _) (secular_pos hg hlam).le, Real.rpow_mul hΔ.le, Real.rpow_two,
    Real.rpow_sub_one (secular_pos hg hlam).ne']
  have hp := (secular_pos (hH := hH) hg hlam).ne'
  have hp' := (deriv_secular_neg (hH := hH) hg hlam).ne
  have hA : secular g H lamc ^ β ≠ 0 := (Real.rpow_pos_of_pos (secular_pos hg hlam) _).ne'
  field_simp

/-- The trust-region Newton correction is the Newton step for $\theta_{-1/2}$. Let $g \neq 0$,
$\lambda_c > -\lambda_1$ and $\Delta > 0$. Then
$$\delta^N(\lambda_c) = -\frac{\theta_{-1/2}(\lambda_c)}{\theta_{-1/2}'(\lambda_c)},$$
where $\theta_{-1/2}(\lambda) = \pi(\lambda)^{-1/2} - \Delta^{-1}$. This is (8.2.24) of
[cartis2022evaluation], the case $\beta = -1/2$ of `Subproblem.newtonCorrection_eq`. -/
theorem trNewtonCorrection_eq (hg : g ≠ 0) {lamc Δ : ℝ} (hlam : -leftmost hH < lamc)
    (hΔ : 0 < Δ) :
    trNewtonCorrection g H Δ lamc = -trSecular g H Δ (-1 / 2) lamc /
      deriv (trSecular g H Δ (-1 / 2)) lamc := by
  rw [newtonCorrection_eq hg hlam hΔ (by norm_num), newtonFactor_of_ne_zero _ (by norm_num),
    trNewtonCorrection]
  have hs : 0 < ‖step g H lamc‖ := by
    have := secular_pos (hH := hH) hg hlam
    rw [secular] at this
    exact norm_pos_iff.2 fun h => by simp [h] at this
  have hpow : (Δ ^ 2 / secular g H lamc) ^ (-1 / 2 : ℝ) = ‖step g H lamc‖ / Δ := by
    rw [secular, ← div_pow, ← Real.rpow_two, ← Real.rpow_mul (div_pos hΔ hs).le]
    norm_num [Real.rpow_neg_one, inv_div]
  rw [hpow]
  ring

/-- **The regularization Newton correction in closed form.** Let $g \neq 0$, $\sigma > 0$, $r > 2$,
$\beta \neq 0$, and $\lambda_c > \max(0, -\lambda_1)$. Write $\pi = \pi(\lambda_c)$,
$\pi' = \pi'(\lambda_c)$,
$$\mu = \frac{(\lambda_c / \sigma)^{2/(r-2)}}{\pi}, \qquad \omega = \frac{2\pi}{(r - 2)
  \lambda_c \pi'}.$$
Then $1 - \omega \mu^\beta > 0$ and
$$\delta^N(\lambda_c, \beta) = -\frac{\pi}{\pi'} \cdot \frac{1 - \mu^\beta}{\beta (1 - \omega
  \mu^\beta)}.$$
This is the last line of (8.2.25) of [cartis2022evaluation].

The positivity of $1 - \omega \mu^\beta$ holds because $\pi' < 0$, so that $\omega < 0$. -/
theorem regNewtonCorrection_eq (hg : g ≠ 0) {σ r β lamc : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hβ : β ≠ 0) (hlam : -leftmost hH < lamc) (hpos : 0 < lamc) :
    0 < 1 - 2 * secular g H lamc / ((r - 2) * lamc * deriv (secular g H) lamc) *
        ((lamc / σ) ^ (2 / (r - 2)) / secular g H lamc) ^ β ∧
    regNewtonCorrection g H σ r β lamc =
      -secular g H lamc / deriv (secular g H) lamc *
        ((1 - ((lamc / σ) ^ (2 / (r - 2)) / secular g H lamc) ^ β) /
          (β * (1 - 2 * secular g H lamc / ((r - 2) * lamc * deriv (secular g H) lamc) *
            ((lamc / σ) ^ (2 / (r - 2)) / secular g H lamc) ^ β))) := by
  have hp := secular_pos (hH := hH) hg hlam
  have hp' := deriv_secular_neg (hH := hH) hg hlam
  have hr2 : 0 < r - 2 := by linarith
  have hx : 0 < lamc / σ := div_pos hpos hσ
  have hμ : ((lamc / σ) ^ (2 / (r - 2)) / secular g H lamc) ^ β =
      (lamc / σ) ^ (2 * β / (r - 2)) / secular g H lamc ^ β := by
    rw [Real.div_rpow (Real.rpow_nonneg hx.le _) hp.le, ← Real.rpow_mul hx.le]
    congr 2
    ring
  rw [hμ]
  set A := secular g H lamc ^ β with hA_def
  set B := (lamc / σ) ^ (2 * β / (r - 2)) with hB_def
  have hA : 0 < A := Real.rpow_pos_of_pos hp _
  have hB : 0 < B := Real.rpow_pos_of_pos hx _
  have hω : 2 * secular g H lamc / ((r - 2) * lamc * deriv (secular g H) lamc) < 0 :=
    div_neg_of_pos_of_neg (by positivity) (mul_neg_of_pos_of_neg (by positivity) hp')
  have hpos' : 0 < 1 - 2 * secular g H lamc / ((r - 2) * lamc * deriv (secular g H) lamc) *
      (B / A) := by
    have : 0 < B / A := div_pos hB hA
    nlinarith
  refine ⟨hpos', ?_⟩
  rw [regNewtonCorrection, (hasDerivAt_regSecular hg hσ hlam hpos).deriv, regSecular,
    Real.rpow_sub_one hp.ne', Real.rpow_sub_one hx.ne', ← hA_def, ← hB_def]
  have hpne := hp.ne'
  have hp'ne := hp'.ne
  have hAne := hA.ne'
  have hσne := hσ.ne'
  have hlne := hpos.ne'
  have hr2ne := hr2.ne'
  have hD : β * (A / secular g H lamc) * deriv (secular g H) lamc -
      2 * β / (r - 2) * (B / (lamc / σ)) / σ =
      β * deriv (secular g H) lamc / secular g H lamc * A *
        (1 - 2 * secular g H lamc / ((r - 2) * lamc * deriv (secular g H) lamc) * (B / A)) := by
    field_simp
  rw [hD]
  have := hpos'.ne'
  field_simp

/-! ### Shape of the transformed secular functions -/

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For $p \le 0$, the function $x \mapsto x^p$ is convex on $(0, \infty)$. -/
theorem convexOn_rpow_Ioi_of_nonpos {p : ℝ} (hp : p ≤ 0) :
    ConvexOn ℝ (Ioi 0) fun x : ℝ => x ^ p := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
    (fun x hx => (Real.continuousAt_rpow_const x p (Or.inl (ne_of_gt hx))).continuousWithinAt)
    ?_ ?_
  · rw [interior_Ioi]
    exact fun x hx =>
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi, Real.deriv_rpow_const']
    intro x hx y _ hxy
    exact mul_le_mul_of_nonpos_left (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)) hp

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The regularization target $t \mapsto (t / \sigma)^\gamma$ on $(0, \infty)$, for $\sigma > 0$: it
is concave and monotone for $\gamma \in [0, 1]$, and convex and antitone for $\gamma \le 0$. -/
theorem regTarget_shape {σ γ : ℝ} (hσ : 0 < σ) :
    (0 ≤ γ → γ ≤ 1 → ConcaveOn ℝ (Ioi 0) (fun t : ℝ => (t / σ) ^ γ) ∧
      MonotoneOn (fun t : ℝ => (t / σ) ^ γ) (Ioi 0)) ∧
    (γ ≤ 0 → ConvexOn ℝ (Ioi 0) (fun t : ℝ => (t / σ) ^ γ) ∧
      AntitoneOn (fun t : ℝ => (t / σ) ^ γ) (Ioi 0)) := by
  have heq : EqOn (fun t : ℝ => (σ ^ γ)⁻¹ • t ^ γ) (fun t : ℝ => (t / σ) ^ γ) (Ioi 0) :=
    fun t ht => by
      simp only [smul_eq_mul]
      rw [Real.div_rpow (le_of_lt ht) hσ.le, div_eq_inv_mul]
  have hc : 0 ≤ (σ ^ γ)⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hσ.le _)
  refine ⟨fun h0 h1 => ⟨(((Real.concaveOn_rpow h0 h1).subset Ioi_subset_Ici_self
      (convex_Ioi 0)).smul hc).congr heq, fun x hx y _ hxy => ?_⟩, fun h0 =>
    ⟨((convexOn_rpow_Ioi_of_nonpos h0).smul hc).congr heq, fun x hx y _ hxy => ?_⟩⟩
  · exact Real.rpow_le_rpow (div_pos hx hσ).le (div_le_div_of_nonneg_right hxy hσ.le) h0
  · exact Real.rpow_le_rpow_of_nonpos (div_pos hx hσ) (div_le_div_of_nonneg_right hxy hσ.le) h0

/-- **Shape of the transformed trust-region secular function.** Let $g \neq 0$,
$\Delta \in \mathbb{R}$ and $\beta \in [-1/2, 0)$. Then on $(-\lambda_1, \infty)$ the function
$\theta_\beta = \pi^\beta - \Delta^{2\beta}$ is concave and strictly increasing, and its
derivative is positive. -/
theorem trSecular_shape (hg : g ≠ 0) (Δ : ℝ) {β : ℝ} (hβ : β ∈ Ico (-1 / 2) 0) :
    ConcaveOn ℝ (Ioi (-leftmost hH)) (trSecular g H Δ β) ∧
      StrictMonoOn (trSecular g H Δ β) (Ioi (-leftmost hH)) ∧
      ∀ x ∈ Ioi (-leftmost hH), 0 < deriv (trSecular g H Δ β) x := by
  obtain ⟨hm, hc, -⟩ := (secular_shape (hH := hH) hg β).2.2.2.2.2.2 hβ
  refine ⟨hc.sub (convexOn_const _ (convex_Ioi _)), fun x hx y hy hxy => ?_, fun x hx => ?_⟩
  · simp only [trSecular]
    linarith [hm hx hy hxy]
  · rw [(hasDerivAt_trSecular hg hx Δ β).deriv]
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos hβ.2 (Real.rpow_pos_of_pos (secular_pos hg hx) _))
      (deriv_secular_neg hg hx)

/-- **Shape of the transformed regularization secular function.** Let $g \neq 0$, $\sigma > 0$ and
$r > 2$, and let $\theta_\beta = \pi^\beta - (\lambda/\sigma)^{2\beta/(r-2)}$ on
$(\lambda_s, \infty)$, where $\lambda_s = \max(0, -\lambda_1)$. Then:

* for $\beta \in (0, (r-2)/2]$, $\theta_\beta$ is convex and strictly decreasing, with negative
  derivative;
* for $\beta \in [-1/2, 0)$, $\theta_\beta$ is concave and strictly increasing, with positive
  derivative.

This is the shape used in §8.2.2 of [cartis2022evaluation]. -/
theorem regSecular_shape (hg : g ≠ 0) {σ r β : ℝ} (hσ : 0 < σ) (hr : 2 < r) :
    (β ∈ Ioc 0 ((r - 2) / 2) →
      ConvexOn ℝ (Ioi (shiftThreshold hH)) (regSecular g H σ r β) ∧
      StrictAntiOn (regSecular g H σ r β) (Ioi (shiftThreshold hH)) ∧
      ∀ x ∈ Ioi (shiftThreshold hH), deriv (regSecular g H σ r β) x < 0) ∧
    (β ∈ Ico (-1 / 2) 0 →
      ConcaveOn ℝ (Ioi (shiftThreshold hH)) (regSecular g H σ r β) ∧
      StrictMonoOn (regSecular g H σ r β) (Ioi (shiftThreshold hH)) ∧
      ∀ x ∈ Ioi (shiftThreshold hH), 0 < deriv (regSecular g H σ r β) x) := by
  have hr2 : 0 < r - 2 := by linarith
  have hS1 : Ioi (shiftThreshold hH) ⊆ Ioi (-leftmost hH) := Ioi_shiftThreshold_subset
  have hS0 : Ioi (shiftThreshold hH) ⊆ Ioi 0 := Ioi_subset_Ioi shiftThreshold_nonneg
  have hconv : Convex ℝ (Ioi (shiftThreshold hH)) := convex_Ioi _
  have hderiv : ∀ x ∈ Ioi (shiftThreshold hH), deriv (regSecular g H σ r β) x =
      β * secular g H x ^ (β - 1) * deriv (secular g H) x -
        2 * β / (r - 2) * (x / σ) ^ (2 * β / (r - 2) - 1) / σ := fun x hx =>
    (hasDerivAt_regSecular hg hσ (hS1 hx) (hS0 hx)).deriv
  have hφ : ∀ x ∈ Ioi (shiftThreshold hH), 0 < (x / σ) ^ (2 * β / (r - 2) - 1) / σ :=
    fun x hx => div_pos (Real.rpow_pos_of_pos (div_pos (hS0 hx) hσ) _) hσ
  have hψ : ∀ x ∈ Ioi (shiftThreshold hH), 0 < secular g H x ^ (β - 1) :=
    fun x hx => Real.rpow_pos_of_pos (secular_pos hg (hS1 hx)) _
  constructor
  · intro hβ
    have hγ0 : 0 ≤ 2 * β / (r - 2) := div_nonneg (by linarith [hβ.1]) hr2.le
    have hγ1 : 2 * β / (r - 2) ≤ 1 := (div_le_one hr2).2 (by linarith [hβ.2])
    obtain ⟨hφc, hφm⟩ := (regTarget_shape (γ := 2 * β / (r - 2)) hσ).1 hγ0 hγ1
    obtain ⟨hm, hc, -⟩ := (secular_shape (hH := hH) hg β).2.2.2.2.2.1 hβ.1
    refine ⟨(hc.convexOn.subset hS1 hconv).sub (hφc.subset hS0 hconv),
      fun x hx y hy hxy => ?_, fun x hx => ?_⟩
    · simp only [regSecular]
      linarith [hm (hS1 hx) (hS1 hy) hxy, hφm (hS0 hx) (hS0 hy) hxy.le]
    · rw [hderiv x hx]
      have h1 : β * secular g H x ^ (β - 1) * deriv (secular g H) x < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hβ.1 (hψ x hx)) (deriv_secular_neg hg (hS1 hx))
      have h2 : 0 < 2 * β / (r - 2) * ((x / σ) ^ (2 * β / (r - 2) - 1) / σ) :=
        mul_pos (div_pos (by linarith [hβ.1]) hr2) (hφ x hx)
      rw [mul_div_assoc]
      linarith
  · intro hβ
    have hγ0 : 2 * β / (r - 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hβ.2]) hr2.le
    obtain ⟨hφc, hφm⟩ := (regTarget_shape (γ := 2 * β / (r - 2)) hσ).2 hγ0
    obtain ⟨hm, hc, -⟩ := (secular_shape (hH := hH) hg β).2.2.2.2.2.2 hβ
    refine ⟨(hc.subset hS1 hconv).sub (hφc.subset hS0 hconv),
      fun x hx y hy hxy => ?_, fun x hx => ?_⟩
    · simp only [regSecular]
      linarith [hm (hS1 hx) (hS1 hy) hxy, hφm (hS0 hx) (hS0 hy) hxy.le]
    · rw [hderiv x hx]
      have h1 : 0 < β * secular g H x ^ (β - 1) * deriv (secular g H) x :=
        mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hβ.2 (hψ x hx))
          (deriv_secular_neg hg (hS1 hx))
      have h2 : 2 * β / (r - 2) * ((x / σ) ^ (2 * β / (r - 2) - 1) / σ) < 0 :=
        mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith [hβ.2]) hr2) (hφ x hx)
      rw [mul_div_assoc]
      linarith

/-! ### Newton corrections stay on the correct side -/

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $\theta$ be convex and antitone on a set $S$, let $r \in S$ with $\theta(r) = 0$, and let
$x \in S$ be a point where $\theta$ has the derivative $\theta'(x) < 0$. Then the Newton
correction does not pass the root, $x - \theta(x)/\theta'(x) \le r$, and the correction
$-\theta(x)/\theta'(x)$ is nonnegative if $x \le r$. -/
theorem newtonCorrection_mem_of_convexOn {θ : ℝ → ℝ} {S : Set ℝ} {r x : ℝ}
    (hc : ConvexOn ℝ S θ) (hm : AntitoneOn θ S) (hr : r ∈ S) (hθr : θ r = 0) (hx : x ∈ S)
    (hd : HasDerivAt θ (deriv θ x) x) (hneg : deriv θ x < 0) :
    x + -θ x / deriv θ x ≤ r ∧ (x ≤ r → 0 ≤ -θ x / deriv θ x) := by
  refine ⟨?_, fun hxr => ?_⟩
  · have := Newton.scalarStep_le_of_convexOn hc hr hθr hx hd.hasDerivWithinAt hneg
    rwa [Newton.scalarStep, sub_eq_add_neg, ← neg_div] at this
  · have : 0 ≤ θ x := hθr ▸ hm hx hr hxr
    exact div_nonneg_of_nonpos (neg_nonpos.2 this) hneg.le

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $\theta$ be concave and monotone on a set $S$, let $r \in S$ with $\theta(r) = 0$, and let
$x \in S$ be a point where $\theta$ has the derivative $\theta'(x) > 0$. Then the Newton
correction does not pass the root, $x - \theta(x)/\theta'(x) \le r$, and the correction
$-\theta(x)/\theta'(x)$ is nonnegative if $x \le r$. This is the concave counterpart of
`Subproblem.newtonCorrection_mem_of_convexOn`. -/
theorem newtonCorrection_mem_of_concaveOn {θ : ℝ → ℝ} {S : Set ℝ} {r x : ℝ}
    (hc : ConcaveOn ℝ S θ) (hm : MonotoneOn θ S) (hr : r ∈ S) (hθr : θ r = 0) (hx : x ∈ S)
    (hd : HasDerivAt θ (deriv θ x) x) (hpos : 0 < deriv θ x) :
    x + -θ x / deriv θ x ≤ r ∧ (x ≤ r → 0 ≤ -θ x / deriv θ x) := by
  refine ⟨?_, fun hxr => ?_⟩
  · have := Newton.scalarStep_le_of_concaveOn hc hr hθr hx hd.hasDerivWithinAt hpos
    rwa [Newton.scalarStep, sub_eq_add_neg, ← neg_div] at this
  · have : θ x ≤ 0 := hθr ▸ hm hx hr hxr
    exact div_nonneg (neg_nonneg.2 this) hpos.le

/-- **Trust-region Newton corrections do not pass the root.** Let $\Delta > 0$, and let
$\lambda_* > -\lambda_1$ satisfy $\pi(\lambda_*) = \Delta^2$. Then for every
$\lambda_c > -\lambda_1$,
$$\lambda_c + \delta^N(\lambda_c) \le \lambda_*,$$
and if moreover $\lambda_c \le \lambda_*$, then $\lambda_c \le \lambda_c + \delta^N(\lambda_c)$.
Here $\delta^N$ is the trust-region Newton correction (8.2.24).

This is the easy case of §8.2.2 and §8.3.2 of [cartis2022evaluation]. From $\lambda_c \in
\mathcal{G} = (\lambda_*, \infty)$, the correction overshoots to a point at most $\lambda_*$;
from $\lambda_c \in \mathcal{L}$, the new point lies in $[\lambda_c, \lambda_*]$.

The proof applies `Subproblem.newtonCorrection_mem_of_concaveOn` to $\theta_{-1/2}$, which is
concave and increasing by `Subproblem.trSecular_shape`. -/
theorem trNewtonCorrection_mem {Δ lamStar lamc : ℝ} (hΔ : 0 < Δ)
    (hstar : -leftmost hH < lamStar) (hroot : secular g H lamStar = Δ ^ 2)
    (hc : -leftmost hH < lamc) :
    lamc + trNewtonCorrection g H Δ lamc ≤ lamStar ∧
      (lamc ≤ lamStar → lamc ≤ lamc + trNewtonCorrection g H Δ lamc) := by
  have hg : g ≠ 0 := ne_zero_of_secular_pos (lam := lamStar) (by rw [hroot]; positivity)
  obtain ⟨hcv, hm, hd⟩ := trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)
  have hθr : trSecular g H Δ (-1 / 2) lamStar = 0 := by
    rw [trSecular, hroot, ← Real.rpow_two, ← Real.rpow_mul hΔ.le, sub_self]
  have h := newtonCorrection_mem_of_concaveOn hcv hm.monotoneOn hstar hθr hc
    ((hasDerivAt_trSecular hg hc Δ _).differentiableAt.hasDerivAt) (hd lamc hc)
  rw [← trNewtonCorrection_eq hg hc hΔ] at h
  exact ⟨h.1, fun hle => le_add_of_nonneg_right (h.2 hle)⟩

omit [FiniteDimensional ℝ E] in
/-- Let $\sigma > 0$ and $\lambda_* > 0$ satisfy the regularization secular equation
$\pi(\lambda_*) = (\lambda_*/\sigma)^{2/(r-2)}$. Then $\lambda_*$ is a root of every transformed
function: $\theta_\beta(\lambda_*) = 0$ for every $\beta \in \mathbb{R}$. -/
theorem regSecular_root {σ r β lamStar : ℝ} (hσ : 0 < σ) (hpos : 0 < lamStar)
    (hroot : secular g H lamStar = (lamStar / σ) ^ (2 / (r - 2))) :
    regSecular g H σ r β lamStar = 0 := by
  rw [regSecular, hroot, ← Real.rpow_mul (div_pos hpos hσ).le, sub_eq_zero]
  congr 1
  ring

/-- **Regularization Newton corrections do not pass the root.** Let $\sigma > 0$, $r > 2$ and
$\beta \in [-1/2, 0) \cup (0, (r-2)/2]$, and let $\lambda_* > \lambda_s$ solve the secular
equation (8.2.42)
$$\pi(\lambda_*) = \left(\frac{\lambda_*}{\sigma}\right)^{2/(r-2)}.$$
Then for every $\lambda_c > \lambda_s$,
$$\lambda_c + \delta^N(\lambda_c, \beta) \le \lambda_*,$$
and if moreover $\lambda_c \le \lambda_*$, then $\lambda_c \le \lambda_c + \delta^N(\lambda_c,
\beta)$. Here $\delta^N(\lambda_c, \beta)$ is the regularization Newton correction (8.2.25).

This is the easy case of §8.2.2 and §8.3.1 of [cartis2022evaluation]. The value $\beta = 0$ is
excluded, since $\theta_0 \equiv 0$.

The proof applies `Subproblem.newtonCorrection_mem_of_convexOn` or
`Subproblem.newtonCorrection_mem_of_concaveOn` to $\theta_\beta$, according to the sign of
$\beta$, with `Subproblem.regSecular_shape`. -/
theorem regNewtonCorrection_mem {σ r β lamStar lamc : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hβ : β ∈ Ico (-1 / 2) 0 ∪ Ioc 0 ((r - 2) / 2)) (hstar : shiftThreshold hH < lamStar)
    (hroot : secular g H lamStar = (lamStar / σ) ^ (2 / (r - 2)))
    (hc : shiftThreshold hH < lamc) :
    lamc + regNewtonCorrection g H σ r β lamc ≤ lamStar ∧
      (lamc ≤ lamStar → lamc ≤ lamc + regNewtonCorrection g H σ r β lamc) := by
  have h0 : ∀ {x}, shiftThreshold hH < x → 0 < x := fun h =>
    lt_of_le_of_lt shiftThreshold_nonneg h
  have h1 : ∀ {x}, shiftThreshold hH < x → -leftmost hH < x := fun h =>
    lt_of_le_of_lt neg_leftmost_le_shiftThreshold h
  have hg : g ≠ 0 := ne_zero_of_secular_pos
    (hroot ▸ Real.rpow_pos_of_pos (div_pos (h0 hstar) hσ) _)
  have hθr := regSecular_root (β := β) (g := g) (H := H) hσ (h0 hstar) hroot
  have hd := (hasDerivAt_regSecular (β := β) (r := r) hg hσ (h1 hc) (h0 hc)).differentiableAt
    |>.hasDerivAt
  have h : lamc + regNewtonCorrection g H σ r β lamc ≤ lamStar ∧
      (lamc ≤ lamStar → 0 ≤ regNewtonCorrection g H σ r β lamc) := by
    rcases hβ with hβ | hβ
    · obtain ⟨hcv, hm, hd'⟩ := (regSecular_shape (hH := hH) hg hσ hr).2 hβ
      exact newtonCorrection_mem_of_concaveOn hcv hm.monotoneOn hstar hθr hc hd (hd' lamc hc)
    · obtain ⟨hcv, hm, hd'⟩ := (regSecular_shape (hH := hH) hg hσ hr).1 hβ
      exact newtonCorrection_mem_of_convexOn hcv hm.antitoneOn hstar hθr hc hd (hd' lamc hc)
  exact ⟨h.1, fun hle => le_add_of_nonneg_right (h.2 hle)⟩

/-! ### Convergence of Newton-type iterations -/

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Iterations at least as long as Newton's** on a convex decreasing function. Let $\theta$ have
the derivative $\theta'$ on $(a, \infty)$, and let $r$ be a root of $\theta$ in the sense of
`Newton.IsConvexAntiRoot`: $\theta$ is convex and strictly decreasing on $(a, \infty)$, $r > a$,
$\theta(r) = 0$ and $\theta'(r) \neq 0$. Let $\theta'$ be continuous at $r$ within
$(a, \infty)$. Let $(x_j)$ be a sequence with $x_0 \in (a, r]$ and, for every $j$,
$x_{j+1} \le r$ and
$$x_j > a \implies N(x_j) \le x_{j+1}, \qquad N(x) = x - \theta(x)/\theta'(x).$$
Then $(x_j)$ is increasing and converges to $r$, the number
$\gamma = 1 - \theta'(r)/\theta'(x_0)$ lies in $[0, 1)$, and
$$r - x_{j+1} \le \gamma \, (r - x_j)$$
for every $j$; moreover the convergence is $Q$-superlinear.

This is the convergence argument behind Algorithms 8.3.1 and 8.3.2 of [cartis2022evaluation],
under the hypotheses of Lemma B.8.1 there. The Newton step $N$ is `Newton.scalarStep`, and
$Q$-superlinear convergence is `ConvergesSuperlinearly`. -/
theorem tendsto_of_scalarStep_le {θ θ' : ℝ → ℝ} {a r : ℝ}
    (h : Newton.IsConvexAntiRoot θ θ' (Ioi a) r) (hcont : ContinuousWithinAt θ' (Ioi a) r)
    {x : ℕ → ℝ} (hx0 : x 0 ∈ Ioc a r)
    (hstep : ∀ j, x j ∈ Ioi a → Newton.scalarStep θ θ' (x j) ≤ x (j + 1))
    (hle : ∀ j, x (j + 1) ≤ r) :
    Monotone x ∧ Tendsto x atTop (𝓝 r) ∧ 1 - θ' r / θ' (x 0) ∈ Ico 0 1 ∧
      (∀ j, r - x (j + 1) ≤ (1 - θ' r / θ' (x 0)) * (r - x j)) ∧
      ConvergesSuperlinearly x r := by
  have hmem : ∀ j, x j ∈ Icc (x 0) r := by
    intro j
    induction j with
    | zero => exact ⟨le_rfl, hx0.2⟩
    | succ j ih =>
      have hS : x j ∈ Ioi a := lt_of_lt_of_le hx0.1 ih.1
      exact ⟨ih.1.trans (((h.scalarStep_mem_Icc_and_sub_le hS ih.2).1.1).trans (hstep j hS)),
        hle j⟩
  have hS : ∀ j, x j ∈ Ioi a := fun j => lt_of_lt_of_le hx0.1 (hmem j).1
  have har : a < r := hx0.1.trans_le hx0.2
  have hneg : θ' r < 0 :=
    h.deriv_root_neg (x := (a + r) / 2) (show a < (a + r) / 2 by linarith) (by linarith)
  have hbound : ∀ j, r - x (j + 1) ≤ (1 - θ' r / θ' (x j)) * (r - x j) := fun j =>
    (sub_le_sub_left (hstep j (hS j)) r).trans
      (h.scalarStep_mem_Icc_and_sub_le (hS j) (hmem j).2).2
  have hd0 : ∀ j, θ' (x 0) ≤ θ' (x j) := fun j => h.monotoneOn_deriv (hS 0) (hS j) (hmem j).1
  have hdr : ∀ j, θ' (x j) ≤ θ' r := fun j => h.monotoneOn_deriv (hS j) h.mem (hmem j).2
  have hlin : ∀ j, r - x (j + 1) ≤ (1 - θ' r / θ' (x 0)) * (r - x j) := fun j =>
    (hbound j).trans (mul_le_mul_of_nonneg_right
      (Newton.one_sub_div_le_one_sub_div (hd0 j) (hdr j) hneg) (sub_nonneg.2 (hmem j).2))
  have hγ' : 1 - θ' r / θ' (x 0) ∈ Ico 0 1 :=
    Newton.one_sub_div_mem_Ico (hdr 0) hneg
  have hpow : ∀ j, r - x j ≤ (1 - θ' r / θ' (x 0)) ^ j * (r - x 0) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, mul_comm _ (1 - θ' r / θ' (x 0)), mul_assoc]
      exact (hlin j).trans (mul_le_mul_of_nonneg_left ih hγ'.1)
  have h0 : Tendsto (fun j => r - x j) atTop (𝓝 0) :=
    squeeze_zero (fun j => sub_nonneg.2 (hmem j).2) hpow (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ'.1 hγ'.2).mul_const (r - x 0))
  have hlim : Tendsto x atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).sub h0
  refine ⟨monotone_nat_of_le_succ fun j =>
      ((h.scalarStep_mem_Icc_and_sub_le (hS j) (hmem j).2).1.1).trans (hstep j (hS j)),
    hlim, hγ', hlin, ?_⟩
  refine Newton.convergesSuperlinearly_of_le_one_sub_div (d := fun k => θ' (x k)) hneg.ne
    (hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hS⟩))
    (fun _ => le_rfl) hdr fun k => ?_
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hle k)), abs_sub_comm,
    abs_of_nonneg (sub_nonneg.2 (hmem k).2)]
  exact hbound k

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Iterations at least as long as Newton's** on a concave increasing function. Let $\theta$ be
concave and strictly increasing on $(a, \infty)$, with derivative $\theta'$ there, let $r$
satisfy $\theta(r) = 0$ and $\theta'(r) \neq 0$, and let $\theta'$ be continuous at $r$ within
$(a, \infty)$. Let $(x_j)$ be a sequence with $x_0 \in (a, r]$ and, for every $j$,
$x_{j+1} \le r$ and $N(x_j) \le x_{j+1}$ whenever $x_j > a$, where $N$ is the Newton step
`Newton.scalarStep`. Then the conclusions of `Subproblem.tendsto_of_scalarStep_le` hold: $(x_j)$
increases to $r$, $\gamma = 1 - \theta'(r)/\theta'(x_0) \in [0, 1)$,
$r - x_{j+1} \le \gamma (r - x_j)$ for every $j$, and the convergence is $Q$-superlinear. -/
theorem tendsto_of_scalarStep_le_of_concaveOn {θ θ' : ℝ → ℝ} {a r : ℝ}
    (hc : ConcaveOn ℝ (Ioi a) θ) (hm : StrictMonoOn θ (Ioi a))
    (hd : ∀ x ∈ Ioi a, HasDerivWithinAt θ (θ' x) (Ioi a) x) (hθr : θ r = 0) (hθ'r : θ' r ≠ 0)
    (hcont : ContinuousWithinAt θ' (Ioi a) r) {x : ℕ → ℝ} (hx0 : x 0 ∈ Ioc a r)
    (hstep : ∀ j, x j ∈ Ioi a → Newton.scalarStep θ θ' (x j) ≤ x (j + 1))
    (hle : ∀ j, x (j + 1) ≤ r) :
    Monotone x ∧ Tendsto x atTop (𝓝 r) ∧ 1 - θ' r / θ' (x 0) ∈ Ico 0 1 ∧
      (∀ j, r - x (j + 1) ≤ (1 - θ' r / θ' (x 0)) * (r - x j)) ∧
      ConvergesSuperlinearly x r := by
  have h := Newton.isConvexAntiRoot_neg hc hm hd (hx0.1.trans_le hx0.2) hθr hθ'r
  have := tendsto_of_scalarStep_le h hcont.neg hx0
    (fun j hj => by rw [Newton.scalarStep_neg]; exact hstep j hj) hle
  simpa only [neg_div_neg_eq] using this

/-- **Convergence of trust-region Newton-type iterations.** Let $\Delta > 0$, and let
$\lambda_* > -\lambda_1$ satisfy $\pi(\lambda_*) = \Delta^2$. Let $(\lambda_j)$ be a sequence
that takes steps at least as long as the Newton correction (8.2.24) without passing $\lambda_*$:
$$\lambda_0 \in (-\lambda_1, \lambda_*], \qquad \lambda_j + \delta^N(\lambda_j) \le
  \lambda_{j+1} \le \lambda_* \quad \text{for all } j.$$
Let $\theta = \theta_{-1/2}$ be the transformed trust-region secular function with
$\beta = -1/2$, and let $\gamma = 1 - \theta'(\lambda_*)/\theta'(\lambda_0)$. Then $(\lambda_j)$
is increasing and converges to $\lambda_*$, $\gamma \in [0, 1)$,
$$\lambda_* - \lambda_{j+1} \le \gamma \, (\lambda_* - \lambda_j) \quad \text{for all } j,$$
and the convergence is $Q$-superlinear.

This is the easy case of Algorithm 8.3.2 in §8.3.2 of [cartis2022evaluation]. The function
$\theta$ is `Subproblem.trSecular g H Δ (-1 / 2)`, and its derivative is taken with `deriv`. -/
theorem tendsto_of_trNewtonCorrection_le {Δ lamStar : ℝ} (hΔ : 0 < Δ)
    (hstar : -leftmost hH < lamStar) (hroot : secular g H lamStar = Δ ^ 2) {x : ℕ → ℝ}
    (hx0 : x 0 ∈ Ioc (-leftmost hH) lamStar)
    (hstep : ∀ j, x j + trNewtonCorrection g H Δ (x j) ≤ x (j + 1) ∧ x (j + 1) ≤ lamStar) :
    Monotone x ∧ Tendsto x atTop (𝓝 lamStar) ∧
      1 - deriv (trSecular g H Δ (-1 / 2)) lamStar / deriv (trSecular g H Δ (-1 / 2)) (x 0) ∈
        Ico 0 1 ∧
      (∀ j, lamStar - x (j + 1) ≤ (1 - deriv (trSecular g H Δ (-1 / 2)) lamStar /
        deriv (trSecular g H Δ (-1 / 2)) (x 0)) * (lamStar - x j)) ∧
      ConvergesSuperlinearly x lamStar := by
  have hg : g ≠ 0 := ne_zero_of_secular_pos (lam := lamStar) (by rw [hroot]; positivity)
  obtain ⟨hcv, hm, hd⟩ := trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)
  have hθr : trSecular g H Δ (-1 / 2) lamStar = 0 := by
    rw [trSecular, hroot, ← Real.rpow_two, ← Real.rpow_mul hΔ.le, sub_self]
  have hsmooth : ContDiffOn ℝ 2 (trSecular g H Δ (-1 / 2)) (Ioi (-leftmost hH)) :=
    (contDiffOn_secular_rpow hg _).sub contDiffOn_const
  refine tendsto_of_scalarStep_le_of_concaveOn hcv hm
    (fun y hy => (hasDerivAt_trSecular hg hy Δ _).differentiableAt.hasDerivAt.hasDerivWithinAt)
    hθr (hd lamStar hstar).ne'
    ((hsmooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).continuousWithinAt hstar)
    hx0 (fun j hj => ?_) fun j => (hstep j).2
  rw [Newton.scalarStep, sub_eq_add_neg, ← neg_div, ← trNewtonCorrection_eq hg hj hΔ]
  exact (hstep j).1

/-- **Convergence of regularization Newton-type iterations.** Let $\sigma > 0$, $r > 2$ and
$\beta \in [-1/2, 0) \cup (0, (r-2)/2]$, and let $\lambda_* > \lambda_s$ satisfy
$\pi(\lambda_*) = (\lambda_*/\sigma)^{2/(r-2)}$. Let $(\lambda_j)$ be a sequence with
$$\lambda_0 \in (\lambda_s, \lambda_*], \qquad \lambda_j + \delta^N(\lambda_j, \beta) \le
  \lambda_{j+1} \le \lambda_* \quad \text{for all } j,$$
and let $\gamma = 1 - \theta_\beta'(\lambda_*)/\theta_\beta'(\lambda_0)$. Then $(\lambda_j)$ is
increasing and converges to $\lambda_*$, $\gamma \in [0, 1)$,
$$\lambda_* - \lambda_{j+1} \le \gamma \, (\lambda_* - \lambda_j) \quad \text{for all } j,$$
and the convergence is $Q$-superlinear.

This is the easy case of §8.2.2, §8.3.1 and Algorithm 8.3.1 of [cartis2022evaluation], with
Lemma B.8.1 there. The hypotheses hold for the plain Newton iteration, for the
$\beta$-maximizing iteration (8.2.26), and for Algorithm 8.3.1, which takes the largest of
several corrections. -/
theorem tendsto_of_regNewtonCorrection_le {σ r β lamStar : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hβ : β ∈ Ico (-1 / 2) 0 ∪ Ioc 0 ((r - 2) / 2)) (hstar : shiftThreshold hH < lamStar)
    (hroot : secular g H lamStar = (lamStar / σ) ^ (2 / (r - 2))) {x : ℕ → ℝ}
    (hx0 : x 0 ∈ Ioc (shiftThreshold hH) lamStar)
    (hstep : ∀ j, x j + regNewtonCorrection g H σ r β (x j) ≤ x (j + 1) ∧ x (j + 1) ≤ lamStar) :
    Monotone x ∧ Tendsto x atTop (𝓝 lamStar) ∧
      1 - deriv (regSecular g H σ r β) lamStar / deriv (regSecular g H σ r β) (x 0) ∈ Ico 0 1 ∧
      (∀ j, lamStar - x (j + 1) ≤ (1 - deriv (regSecular g H σ r β) lamStar /
        deriv (regSecular g H σ r β) (x 0)) * (lamStar - x j)) ∧
      ConvergesSuperlinearly x lamStar := by
  have h0 : ∀ {x}, shiftThreshold hH < x → 0 < x := fun h =>
    lt_of_le_of_lt shiftThreshold_nonneg h
  have h1 : ∀ {x}, shiftThreshold hH < x → -leftmost hH < x := fun h =>
    lt_of_le_of_lt neg_leftmost_le_shiftThreshold h
  have hg : g ≠ 0 := ne_zero_of_secular_pos
    (hroot ▸ Real.rpow_pos_of_pos (div_pos (h0 hstar) hσ) _)
  have hθr := regSecular_root (β := β) (g := g) (H := H) hσ (h0 hstar) hroot
  have hderiv : ∀ y ∈ Ioi (shiftThreshold hH),
      HasDerivWithinAt (regSecular g H σ r β) (deriv (regSecular g H σ r β) y)
        (Ioi (shiftThreshold hH)) y := fun y hy =>
    (hasDerivAt_regSecular hg hσ (h1 hy) (h0 hy)).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hsmooth : ContDiffOn ℝ 2 (regSecular g H σ r β) (Ioi (shiftThreshold hH)) := by
    refine ((contDiffOn_secular_rpow hg β).mono Ioi_shiftThreshold_subset).sub fun y hy => ?_
    exact ((contDiffAt_id.div_const σ).rpow_const_of_ne
      (div_pos (h0 hy) hσ).ne').contDiffWithinAt
  have hcont : ContinuousWithinAt (deriv (regSecular g H σ r β)) (Ioi (shiftThreshold hH))
      lamStar :=
    (hsmooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).continuousWithinAt hstar
  have hstep' : ∀ j, x j ∈ Ioi (shiftThreshold hH) →
      Newton.scalarStep (regSecular g H σ r β) (deriv (regSecular g H σ r β)) (x j) ≤
        x (j + 1) := fun j _ => by
    rw [Newton.scalarStep, sub_eq_add_neg, ← neg_div]
    exact (hstep j).1
  rcases hβ with hβ | hβ
  · obtain ⟨hcv, hm, hd⟩ := (regSecular_shape (hH := hH) hg hσ hr).2 hβ
    exact tendsto_of_scalarStep_le_of_concaveOn hcv hm hderiv hθr (hd lamStar hstar).ne' hcont
      hx0 hstep' fun j => (hstep j).2
  · obtain ⟨hcv, hm, hd⟩ := (regSecular_shape (hH := hH) hg hσ hr).1 hβ
    exact tendsto_of_scalarStep_le ⟨hcv, hm, hderiv, hstar, hθr, (hd lamStar hstar).ne⟩ hcont
      hx0 hstep' fun j => (hstep j).2

/-! ### Taylor corrections -/

omit [FiniteDimensional ℝ E] in
/-- The Taylor polynomial of the secular function takes the value $t_k(0) = \pi(\lambda_c)$ at $0$.
-/
theorem secularTaylor_zero (g : E) (H : E →L[ℝ] E) (k : ℕ) (lamc : ℝ) :
    secularTaylor g H k lamc 0 = secular g H lamc := by
  simp [secularTaylor, Finset.sum_range_succ']

omit [FiniteDimensional ℝ E] in
/-- The Taylor polynomial $t_k$ of the secular function at $\lambda_c$ is continuous. -/
theorem continuous_secularTaylor (g : E) (H : E →L[ℝ] E) (k : ℕ) (lamc : ℝ) :
    Continuous (secularTaylor g H k lamc) :=
  continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_pow j)

/-- **Taylor polynomials of odd order underestimate $\pi$ to the right.** For
$\lambda_c > -\lambda_1$, odd $k$ and $\delta > 0$, $t_k(\delta) \le \pi(\lambda_c + \delta)$.
This is part of Theorem 8.2.2 of [cartis2022evaluation]. -/
theorem secularTaylor_le_secular {lamc δ : ℝ} {k : ℕ} (hlam : -leftmost hH < lamc) (hk : Odd k)
    (hδ : 0 < δ) : secularTaylor g H k lamc δ ≤ secular g H (lamc + δ) :=
  ((secular_taylor_bounds hlam k).1 δ hδ).2 hk

/-- **Taylor polynomials of even order overestimate $\pi$ to the right.** For
$\lambda_c > -\lambda_1$, even $k$ and $\delta > 0$, $\pi(\lambda_c + \delta) \le t_k(\delta)$.
This is part of Theorem 8.2.2 of [cartis2022evaluation]. -/
theorem secular_le_secularTaylor {lamc δ : ℝ} {k : ℕ} (hlam : -leftmost hH < lamc) (hk : Even k)
    (hδ : 0 < δ) : secular g H (lamc + δ) ≤ secularTaylor g H k lamc δ :=
  ((secular_taylor_bounds hlam k).1 δ hδ).1 hk

/-- The **standing hypotheses of the Taylor iterations** for a target
$\tau : \mathbb{R} \to \mathbb{R}$, a left end $a$ and a root $\lambda_*$. They consist of
$g \neq 0$; $a \ge -\lambda_1$, so that $(a, \infty) \subseteq (-\lambda_1, \infty)$; $\tau$
continuous and monotone on $(a, \infty)$; and $\lambda_* > a$ with
$\pi(\lambda_*) = \tau(\lambda_*)$.

Lemma 8.2.1 of [cartis2022evaluation] gives such a root when $\pi > \tau$ near $a$. -/
structure IsSecularTarget (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (g : E) (τ : ℝ → ℝ)
    (a lamStar : ℝ) : Prop where
  /-- The vector $g$ is nonzero. -/
  ne_zero : g ≠ 0
  /-- The left end lies to the right of the pole: $-\lambda_1 \le a$. -/
  le_left : -leftmost hH ≤ a
  /-- The target $\tau$ is continuous on $(a, \infty)$. -/
  continuousOn : ContinuousOn τ (Ioi a)
  /-- The target $\tau$ is monotone on $(a, \infty)$. -/
  monotoneOn : MonotoneOn τ (Ioi a)
  /-- The root lies to the right of the left end: $a < \lambda_*$. -/
  lt_root : a < lamStar
  /-- The root solves the secular equation: $\pi(\lambda_*) = \tau(\lambda_*)$. -/
  root : secular g H lamStar = τ lamStar

namespace IsSecularTarget

variable {τ : ℝ → ℝ} {a lamStar : ℝ} (h : IsSecularTarget hH g τ a lamStar)
include h

/-- Every $x > a$ satisfies $x > -\lambda_1$. -/
theorem neg_leftmost_lt {x : ℝ} (hx : a < x) : -leftmost hH < x := h.le_left.trans_lt hx

/-- On $\mathcal{L} = (a, \lambda_*]$ the secular function dominates the target:
$\tau(x) \le \pi(x)$ for $x \in (a, \lambda_*]$. -/
theorem tau_le_secular {x : ℝ} (hx : x ∈ Ioc a lamStar) : τ x ≤ secular g H x := by
  have hm := (secular_shape (hH := hH) h.ne_zero 0).2.2.1
  calc τ x ≤ τ lamStar := h.monotoneOn hx.1 h.lt_root hx.2
    _ = secular g H lamStar := h.root.symm
    _ ≤ secular g H x := hm.antitoneOn (h.neg_leftmost_lt hx.1) (h.neg_leftmost_lt h.lt_root) hx.2

/-- For odd $k$ and $\lambda_c \in (a, \lambda_*]$, every root $\delta$ of
$t_k(\delta) = \tau(\lambda_c + \delta)$ satisfies $\delta \le \lambda_* - \lambda_c$. If
$\lambda_c + \delta > \lambda_*$, then $t_k(\delta) \le \pi(\lambda_c + \delta) <
\pi(\lambda_*) = \tau(\lambda_*) \le \tau(\lambda_c + \delta)$, so $\delta$ is not a root. -/
theorem taylor_root_le {k : ℕ} (hk : Odd k) {lamc δ : ℝ} (hc : lamc ∈ Ioc a lamStar)
    (hδ : secularTaylor g H k lamc δ = τ (lamc + δ)) : δ ≤ lamStar - lamc := by
  by_contra hlt
  push Not at hlt
  have hδ0 : 0 < δ := by linarith [hc.2]
  have hlam := h.neg_leftmost_lt hc.1
  have h1 := secularTaylor_le_secular (g := g) hlam hk hδ0
  have h2 := (secular_shape (hH := hH) h.ne_zero 0).2.2.1 (h.neg_leftmost_lt h.lt_root)
    (show -leftmost hH < lamc + δ by linarith) (show lamStar < lamc + δ by linarith)
  have h3 := h.monotoneOn h.lt_root (show a < lamc + δ by linarith [hc.1])
    (show lamStar ≤ lamc + δ by linarith)
  linarith [h.root]

/-- Let $k$ be odd, $\lambda_c \in (a, \lambda_*]$ and $0 \le \eta \le \lambda_* - \lambda_c$ with
$\tau(\lambda_c + \eta) \le t_k(\eta)$. Then the equation
$t_k(\delta) = \tau(\lambda_c + \delta)$ has a root $\delta \in [\eta, \lambda_* - \lambda_c]$.
The proof is the intermediate value theorem; for $\eta = 0$ the hypothesis holds on
$\mathcal{L}$. -/
theorem exists_taylor_root {k : ℕ} (hk : Odd k) {lamc η : ℝ} (hc : lamc ∈ Ioc a lamStar)
    (hη0 : 0 ≤ η) (hη : η ≤ lamStar - lamc)
    (hfη : τ (lamc + η) ≤ secularTaylor g H k lamc η) :
    ∃ δ ∈ Icc η (lamStar - lamc), secularTaylor g H k lamc δ = τ (lamc + δ) := by
  have hlam := h.neg_leftmost_lt hc.1
  -- the value at the right end is `≤ 0`
  have hend : secularTaylor g H k lamc (lamStar - lamc) ≤ τ (lamc + (lamStar - lamc)) := by
    have e : lamc + (lamStar - lamc) = lamStar := by ring
    rw [e, ← h.root]
    rcases (sub_nonneg.2 hc.2).lt_or_eq with hpos | hzero
    · have := secularTaylor_le_secular (g := g) hlam hk hpos
      rw [e] at this
      exact this
    · rw [← hzero, secularTaylor_zero, show lamc = lamStar by linarith [hzero]]
  have hcont : ContinuousOn (fun δ => secularTaylor g H k lamc δ - τ (lamc + δ))
      (Icc η (lamStar - lamc)) := by
    refine (continuous_secularTaylor g H k lamc).continuousOn.sub ?_
    refine h.continuousOn.comp (continuous_const.add continuous_id).continuousOn fun δ hδ => ?_
    change a < lamc + δ
    linarith [hc.1, hδ.1]
  obtain ⟨δ, hδ, hfδ⟩ := intermediate_value_Icc' hη hcont
    (show (0 : ℝ) ∈ Icc _ _ from ⟨sub_nonpos.2 hend, sub_nonneg.2 hfη⟩)
  exact ⟨δ, hδ, sub_eq_zero.1 hfδ⟩

/-- **Taylor corrections of odd order underestimate $\lambda_*$.** Assume the standing hypotheses
`Subproblem.IsSecularTarget` for $\tau$, $a$ and $\lambda_*$. Let $k$ be odd and
$\lambda_c \in (a, \lambda_*]$. Then the set of roots $\delta$ of the equation (8.2.15)
$$t_k(\delta) = \tau(\lambda_c + \delta)$$
is nonempty and bounded above, and its supremum $\delta_k^T(\lambda_c)$ satisfies
$$\lambda_c \le \lambda_c + \delta_k^T(\lambda_c) \le \lambda_*.$$
This is §8.2.1 of [cartis2022evaluation], with Theorem 8.2.2 there. -/
theorem taylorCorrection_mem {k : ℕ} (hk : Odd k) {lamc : ℝ} (hc : lamc ∈ Ioc a lamStar) :
    {δ | secularTaylor g H k lamc δ = τ (lamc + δ)}.Nonempty ∧
      BddAbove {δ | secularTaylor g H k lamc δ = τ (lamc + δ)} ∧
      lamc ≤ lamc + taylorCorrection g H τ k lamc ∧
      lamc + taylorCorrection g H τ k lamc ≤ lamStar := by
  obtain ⟨δ, hδ, hroot⟩ := h.exists_taylor_root hk hc le_rfl (sub_nonneg.2 hc.2)
    (by rw [add_zero, secularTaylor_zero]; exact h.tau_le_secular hc)
  have hbdd : BddAbove {δ | secularTaylor g H k lamc δ = τ (lamc + δ)} :=
    ⟨lamStar - lamc, fun δ hδ => h.taylor_root_le hk hc hδ⟩
  refine ⟨⟨δ, hroot⟩, hbdd, ?_, ?_⟩
  · have : δ ≤ taylorCorrection g H τ k lamc := le_csSup hbdd hroot
    linarith [hδ.1]
  · have : taylorCorrection g H τ k lamc ≤ lamStar - lamc :=
      csSup_le ⟨δ, hroot⟩ fun δ hδ => h.taylor_root_le hk hc hδ
    linarith

/-- **The rightmost root is attained.** Assume the standing hypotheses `Subproblem.IsSecularTarget`
for $\tau$, $a$ and $\lambda_*$. For odd $k$ and $\lambda_c \in (a, \lambda_*]$, the Taylor
correction $\delta_k^T(\lambda_c)$ is the greatest root of (8.2.15)
$t_k(\delta) = \tau(\lambda_c + \delta)$.

The set of roots is closed near its supremum, because $\tau$ is continuous on $(a, \infty)$. -/
theorem isGreatest_taylorCorrection {k : ℕ} (hk : Odd k) {lamc : ℝ}
    (hc : lamc ∈ Ioc a lamStar) :
    IsGreatest {δ | secularTaylor g H k lamc δ = τ (lamc + δ)} (taylorCorrection g H τ k lamc) := by
  obtain ⟨hne, hbdd, hlo, -⟩ := h.taylorCorrection_mem hk hc
  refine ⟨?_, fun δ hδ => le_csSup hbdd hδ⟩
  set T := taylorCorrection g H τ k lamc with hT
  have haT : a < lamc + T := by linarith [hc.1]
  -- `f = tₖ - τ(λc + ·)` is continuous at `T`
  have hf : ContinuousAt (fun δ => secularTaylor g H k lamc δ - τ (lamc + δ)) T :=
    (continuous_secularTaylor g H k lamc).continuousAt.sub
      ((h.continuousOn.continuousAt (Ioi_mem_nhds haT)).comp
        (continuous_const.add continuous_id).continuousAt)
  by_contra hT0
  have hev := hf.eventually_ne (sub_ne_zero.2 hT0)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨δ, hδ, hlt⟩ := exists_lt_of_lt_csSup hne (show T - η < T by linarith)
  have hδT : δ ≤ T := le_csSup hbdd hδ
  exact hball (show dist δ T < η by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    (sub_eq_zero.2 hδ)

/-- For odd $k$ and $\lambda_c \in (a, \lambda_*]$, the Taylor correction solves (8.2.15):
$t_k(\delta_k^T(\lambda_c)) = \tau(\lambda_c + \delta_k^T(\lambda_c))$. -/
theorem secularTaylor_taylorCorrection {k : ℕ} (hk : Odd k) {lamc : ℝ}
    (hc : lamc ∈ Ioc a lamStar) :
    secularTaylor g H k lamc (taylorCorrection g H τ k lamc) =
      τ (lamc + taylorCorrection g H τ k lamc) :=
  (h.isGreatest_taylorCorrection hk hc).1

end IsSecularTarget

/-- A uniform first-order bound on the Taylor polynomials. Let $x_0 > -\lambda_1$, $x \ge x_0$,
$\delta \in [0, 1]$ and $k \in \mathbb{N}$, and let $t_k$ be the Taylor polynomial of $\pi$ at
$x$. Then
$$|t_k(\delta) - \pi(x)| \le B \delta, \qquad B = \sum_{j=0}^{k} \frac{(j + 1)! \,
  M_{j+2}(x_0)}{j!},$$
where $M_m(x_0) = \sum_i \gamma_i^2 / (x_0 + \lambda_i)^m$ is the moment of order $m$ of the
spectral form of $\pi$, with the eigenvalues $\lambda_i$ of $H$ and the weights $\gamma_i^2$ of
$g$. The bound $B$ depends only on $x_0$ and $k$.

The moment is `Subproblem.secularMoment` with the eigenvalues `hH.eigenvalues rfl` and the
weights `Subproblem.secularWeight hH g`. -/
theorem abs_secularTaylor_sub_le {x₀ x δ : ℝ} (hx₀ : -leftmost hH < x₀) (hx : x₀ ≤ x)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    |secularTaylor g H k x δ - secular g H x| ≤
      (∑ j ∈ range (k + 1), ((j + 1)! : ℝ) *
        secularMoment (hH.eigenvalues rfl) (secularWeight hH g) (j + 2) x₀ / j !) * δ := by
  have hxl : -leftmost hH < x := hx₀.trans_le hx
  rw [← secularTaylor_zero g H k x, secularTaylor, secularTaylor, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, abs_mul, abs_div, iteratedDeriv_secular_eq hxl, abs_mul, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
    abs_of_nonneg (secularMoment_nonneg secularWeight_nonneg (mem_secularDomain_of_lt hxl) _),
    Nat.abs_cast]
  have hmom := secularMoment_le_of_le (g := g) hx₀ hx (j + 2)
  have hpow : |δ ^ j - 0 ^ j| ≤ δ := by
    rcases j with _ | j
    · simpa using hδ0
    · rw [zero_pow (Nat.succ_ne_zero j), sub_zero, abs_of_nonneg (pow_nonneg hδ0 _)]
      exact pow_le_of_le_one hδ0 hδ1 (Nat.succ_ne_zero j)
  have hfac : (0 : ℝ) < j ! := by positivity
  calc ((j + 1)! : ℝ) * secularMoment (hH.eigenvalues rfl) (secularWeight hH g) (j + 2) x /
        j ! * |δ ^ j - 0 ^ j|
      ≤ ((j + 1)! : ℝ) * secularMoment (hH.eigenvalues rfl) (secularWeight hH g) (j + 2) x₀ /
        j ! * δ :=
        mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmom (by positivity))
          hfac.le) hpow (abs_nonneg _) (div_nonneg (mul_nonneg (by positivity)
            (secularMoment_nonneg secularWeight_nonneg (mem_secularDomain_of_lt hx₀) _))
            hfac.le)

namespace IsSecularTarget

variable {τ : ℝ → ℝ} {a lamStar : ℝ} (h : IsSecularTarget hH g τ a lamStar)
include h

/-- **Convergence of Taylor iterations of odd order.** Assume the standing hypotheses
`Subproblem.IsSecularTarget` for $\tau$, $a$ and $\lambda_*$, and let $k$ be odd. Let
$(\lambda_j)$ be a sequence with
$$\lambda_0 \in (a, \lambda_*], \qquad \lambda_j + \delta_k^T(\lambda_j) \le \lambda_{j+1} \le
  \lambda_* \quad \text{for all } j.$$
Then $(\lambda_j)$ is increasing and converges to $\lambda_*$.

This is §8.2.1 of [cartis2022evaluation] and Algorithm 8.3.1 there without Newton candidates.

The proof is by contradiction. At a limit $\bar\lambda < \lambda_*$, the difference $\pi - \tau$
is bounded below near $\bar\lambda$ by a positive constant and the Taylor coefficients are
bounded (`Subproblem.abs_secularTaylor_sub_le`), so the corrections stay bounded below, which
contradicts convergence. -/
theorem tendsto_of_taylorCorrection_le {k : ℕ} (hk : Odd k) {x : ℕ → ℝ}
    (hx0 : x 0 ∈ Ioc a lamStar)
    (hstep : ∀ j, x j + taylorCorrection g H τ k (x j) ≤ x (j + 1) ∧ x (j + 1) ≤ lamStar) :
    Monotone x ∧ Tendsto x atTop (𝓝 lamStar) := by
  have hmem : ∀ j, x j ∈ Ioc a lamStar ∧ x j ≤ x (j + 1) := by
    intro j
    induction j with
    | zero => exact ⟨hx0, (h.taylorCorrection_mem hk hx0).2.2.1.trans (hstep 0).1⟩
    | succ j ih =>
      have h1 : x (j + 1) ∈ Ioc a lamStar := ⟨ih.1.1.trans_le ih.2, (hstep j).2⟩
      exact ⟨h1, (h.taylorCorrection_mem hk h1).2.2.1.trans (hstep (j + 1)).1⟩
  have hmono : Monotone x := monotone_nat_of_le_succ fun j => (hmem j).2
  have hbdd : BddAbove (range x) := ⟨lamStar, by rintro _ ⟨j, rfl⟩; exact (hmem j).1.2⟩
  set L := ⨆ j, x j with hL_def
  have hlim : Tendsto x atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  have hxL : ∀ j, x j ≤ L := fun j => le_ciSup hbdd j
  have hLs : L ≤ lamStar := ciSup_le fun j => (hmem j).1.2
  have haL : a < L := hx0.1.trans_le (hxL 0)
  refine ⟨hmono, ?_⟩
  suffices hLeq : L = lamStar by rwa [← hLeq]
  by_contra hne
  have hLlt : L < lamStar := lt_of_le_of_ne hLs hne
  have hLl := h.neg_leftmost_lt haL
  have hanti := (secular_shape (hH := hH) h.ne_zero 0).2.2.1
  -- the gap `m = π(L) - τ(L) > 0`
  set m := secular g H L - τ L with hm_def
  have hm : 0 < m := by
    have h1 := hanti hLl (h.neg_leftmost_lt h.lt_root) hLlt
    have h2 := h.monotoneOn haL h.lt_root hLlt.le
    rw [hm_def]
    linarith [h.root]
  set B := ∑ j ∈ range (k + 1), ((j + 1)! : ℝ) *
    secularMoment (hH.eigenvalues rfl) (secularWeight hH g) (j + 2) (x 0) / j ! with hB_def
  -- a uniform lower bound `η` on the corrections
  have hτL : Tendsto (fun η => τ (L + η)) (𝓝 0) (𝓝 (τ L)) := by
    have := (h.continuousOn.continuousAt (Ioi_mem_nhds haL)).tendsto
    have hadd : Tendsto (fun η : ℝ => L + η) (𝓝 0) (𝓝 L) := by
      simpa using (tendsto_const_nhds (x := L)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    exact this.comp hadd
  have hBη : Tendsto (fun η => B * η) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const_mul B).tendsto 0
  obtain ⟨η, hη0, ⟨hη1, hη2⟩, hη3, hη4⟩ :=
    ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)).and (nhdsWithin_le_nhds
      (((eventually_lt_nhds one_pos).and (eventually_lt_nhds (sub_pos.2 hLlt))).and
        (((tendsto_order.1 hBη).2 _ (by positivity : 0 < m / 4)).and
          ((tendsto_order.1 hτL).2 _ (by linarith : τ L < τ L + m / 4)))))).exists
  have hη0' : (0 : ℝ) < η := hη0
  have hcorr : ∀ j, η ≤ taylorCorrection g H τ k (x j) := by
    intro j
    have hxj := (hmem j).1
    have hxjl := h.neg_leftmost_lt hxj.1
    have ht : |secularTaylor g H k (x j) η - secular g H (x j)| ≤ B * η :=
      abs_secularTaylor_sub_le (h.neg_leftmost_lt hx0.1) (hmono (Nat.zero_le j)) hη0'.le hη1.le k
    have hπ : secular g H L ≤ secular g H (x j) := hanti.antitoneOn hxjl hLl (hxL j)
    have hτ : τ (x j + η) ≤ τ (L + η) :=
      h.monotoneOn (show a < x j + η by linarith [hxj.1]) (show a < L + η by linarith)
        (by linarith [hxL j])
    have hfη : τ (x j + η) ≤ secularTaylor g H k (x j) η := by
      have := (abs_le.1 ht).1
      linarith
    obtain ⟨δ, hδ, hroot⟩ := h.exists_taylor_root hk hxj hη0'.le
      (by linarith [hxL j]) hfη
    exact hδ.1.trans (le_csSup ⟨lamStar - x j, fun δ hδ => h.taylor_root_le hk hxj hδ⟩ hroot)
  have hgrow : ∀ j, x 0 + j * η ≤ x j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      push_cast
      linarith [(hstep j).1, hcorr j]
  obtain ⟨j, hj⟩ := exists_nat_gt ((lamStar - x 0) / η)
  have := hgrow j
  rw [div_lt_iff₀ hη0'] at hj
  linarith [(hmem j).1.2]

end IsSecularTarget

end Subproblem
