/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter07.Section03

/-!
# Conn, Gould and Toint, Section 7.3: Separate safeguards and the eigenvalue-based method

This module formalizes Algorithms 7.3.2, 7.3.3 and 7.3.6 of Section 7.3 of [conn2000trust], which
accompany the Moré–Sorensen method of `NumlibSurface.ConnGouldToint.Chapter07.Section03`. Algorithm
7.3.2 safeguards a Newton candidate for the secular equation by a bracket $[\lambda^L, \lambda^U]$,
and Algorithm 7.3.3 updates the bracket after a trial multiplier $\lambda$: the upper end when
$H + \lambda I$ is positive definite and $\|s(\lambda)\| < \Delta$, and the lower end otherwise.
This update keeps the optimal multiplier in the bracket. Algorithm 7.3.6 uses the least eigenvalue
$\lambda_1$ of $H$: it first tests whether the system $(H + \lambda_s I) s = -g$ at the threshold
$\lambda_s = \max\{0, -\lambda_1\}$ has a solution in the ball, and otherwise runs Newton's method
from a point just above the pole until the step norm is within a relative tolerance of $\Delta$.

## Main definitions

* Algorithm 7.3.2, `ConnGouldToint.Chapter07.algorithm_7_3_2`: the Newton candidate with a bracket
  safeguard, with midpoint trials.
* Algorithm 7.3.3, `ConnGouldToint.Chapter07.algorithm_7_3_3`: the update of the bracket after a
  trial multiplier.
* Algorithm 7.3.6, `ConnGouldToint.Chapter07.algorithm_7_3_6`: the corrected eigenvalue-based
  algorithm.

## Main results

* Algorithm 7.3.2, `ConnGouldToint.Chapter07.algorithm_7_3_2_failed_newton`: a Newton candidate at
  or below the pole raises the lower end, and the next trial lies strictly inside the bracket.
* Algorithm 7.3.3, `ConnGouldToint.Chapter07.algorithm_7_3_3_preserves_bracket` and
  `ConnGouldToint.Chapter07.algorithm_7_3_3_preserves_multiplier`: the update keeps the optimal
  multiplier in the bracket.
* Algorithm 7.3.6, `ConnGouldToint.Chapter07.algorithm_7_3_6_exact_threshold`: if the threshold
  system has a solution in the ball, the exact threshold step is a global minimizer.
* Algorithm 7.3.6, `ConnGouldToint.Chapter07.algorithm_7_3_6_perturbation_counterexample`: a
  feasible step at a perturbed shift does not make the threshold system solvable.
* Algorithm 7.3.6, `ConnGouldToint.Chapter07.algorithm_7_3_6_easy_stop` and
  `ConnGouldToint.Chapter07.algorithm_7_3_6_easy_start`: in the easy case the Newton iteration
  reaches the radius test in finitely many steps.
* Algorithm 7.3.6, `ConnGouldToint.Chapter07.algorithm_7_3_6_returns_exact` and
  `ConnGouldToint.Chapter07.algorithm_7_3_6_returns_easy`: the algorithm returns a global minimizer
  in the terminal branch and a step that passes the radius test in the easy branch.

## Conventions

* The notation is that of `NumlibSurface.ConnGouldToint.Chapter07.Section03`. The step $s(\lambda)$,
  the secular function $\phi$ and the threshold $\lambda_s$ are
  `ConnGouldToint.Chapter07.shiftedStep`, `ConnGouldToint.Chapter07.phi` and
  `Subproblem.shiftThreshold hH`.
* The solution of the threshold system is the minimum-norm solution
  `Subproblem.particular hH g λ_s`. The system has a solution if and only if $g$ is orthogonal to
  the kernel of $H + \lambda_s I$.

## Deviations from the source

* **Algorithm 7.3.2** (reading). The bracket choices that the source leaves open are midpoints. See
  `ConnGouldToint.Chapter07.algorithm_7_3_2`.
* **Algorithm 7.3.6** (correction). The terminal branch tests solvability and feasibility at the
  exact threshold, because a feasible step at a perturbed shift can report the hard case when the
  exact test would not. See `ConnGouldToint.Chapter07.algorithm_7_3_6_exact_threshold` and
  `ConnGouldToint.Chapter07.algorithm_7_3_6_perturbation_counterexample`.
-/

namespace ConnGouldToint.Chapter07

open Subproblem Set Filter
open scoped Topology RealInnerProductSpace

section Safeguards

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Algorithm 7.3.2** of [conn2000trust], with midpoint trials. For a pole
$\lambda_{\mathrm{pole}}$, a radius $\Delta$, a bracket $[\lambda^L, \lambda^U]$ and a trial
multiplier $\lambda$, the algorithm returns a pair (lower end, next trial):

* if $\lambda > \lambda_{\mathrm{pole}}$ and $g \neq 0$, let $\lambda^N$ be the Newton step
  (7.3.11) from $\lambda$. If $\|s(\lambda)\| \ge \Delta$ or
  $\lambda^N > \lambda_{\mathrm{pole}}$, the result is $(\lambda^L, \lambda^N)$. Otherwise, with
  $\lambda^{L\prime} = \max\{\lambda^L, \lambda^N\}$, the result is $(\lambda^{L\prime},
  (\lambda^{L\prime} + \lambda^U)/2)$;
* otherwise the result is $(\lambda^L, (\lambda^L + \lambda^U)/2)$.

**Reading.** The source leaves the choice of a trial in the bracket open. The definition takes
the midpoint.

A zero gradient goes directly to the bracket choice, since the Newton formula would divide by
the norm of a zero solve. -/
noncomputable def algorithm_7_3_2 (g : E) (H : E →L[ℝ] E)
    (pole Δ lo hi x : ℝ) : ℝ × ℝ :=
  if pole < x ∧ ‖g‖ ≠ 0 then
    let candidate := moreSorensenNewtonStep g H Δ x
    if Δ ≤ ‖shiftedStep g H x‖ ∨ pole < candidate then (lo, candidate)
    else let lo' := max lo candidate; (lo', (lo' + hi) / 2)
  else (lo, (lo + hi) / 2)

/-- **Algorithm 7.3.2** of [conn2000trust], Steps 2b–2c. Let $\lambda > \lambda_{\mathrm{pole}}$,
$g \neq 0$, $\|s(\lambda)\| < \Delta$, and let the Newton step $\lambda^N$ from $\lambda$
satisfy $\lambda^N \le \lambda_{\mathrm{pole}}$. If $\lambda^L < \lambda^U$ and
$\lambda_{\mathrm{pole}} < \lambda^U$, then the algorithm returns the lower end
$\max\{\lambda^L, \lambda^N\}$ and a next trial strictly between this lower end and $\lambda^U$. -/
theorem algorithm_7_3_2_failed_newton {g : E} {H : E →L[ℝ] E} {pole Δ lo hi x : ℝ}
    (hx : pole < x) (hg : g ≠ 0) (hG : ‖shiftedStep g H x‖ < Δ)
    (hN : moreSorensenNewtonStep g H Δ x ≤ pole) (hlh : lo < hi) (hph : pole < hi) :
    let state := algorithm_7_3_2 g H pole Δ lo hi x
    state.1 = max lo (moreSorensenNewtonStep g H Δ x) ∧ state.2 ∈ Ioo state.1 hi := by
  have hc := max_lt hlh (hN.trans_lt hph)
  have hf : pole < x ∧ ‖g‖ ≠ 0 := ⟨hx, norm_ne_zero_iff.mpr hg⟩
  simp only [algorithm_7_3_2, ite_eq_left hf, not_le.mpr hG, not_lt.mpr hN,
    false_or, ite_false, mem_Ioo, true_and]
  exact ⟨by linarith, by linarith⟩

/-- **Algorithm 7.3.3** of [conn2000trust]. For a pole $\lambda_{\mathrm{pole}}$, a radius $\Delta$,
a bracket $[\lambda^L, \lambda^U]$ and a trial multiplier $\lambda$, the new bracket is
$[\lambda^L, \lambda]$ if $\lambda > \lambda_{\mathrm{pole}}$ and $\|s(\lambda)\| < \Delta$, and
$[\lambda, \lambda^U]$ otherwise. -/
noncomputable def algorithm_7_3_3 (g : E) (H : E →L[ℝ] E)
    (pole Δ lo hi x : ℝ) : ℝ × ℝ :=
  if pole < x ∧ ‖shiftedStep g H x‖ < Δ then (lo, x) else (x, hi)

/-- **Algorithm 7.3.3** of [conn2000trust], bracket invariant. Let $r \in [\lambda^L, \lambda^U]$.
Suppose that $r \le \lambda$ whenever $\lambda > \lambda_{\mathrm{pole}}$ and
$\|s(\lambda)\| < \Delta$, and that $\lambda \le r$ otherwise. Then $r$ lies in the updated
bracket.

For the optimal multiplier, the comparison of the secular function supplies the two hypotheses;
see `ConnGouldToint.Chapter07.algorithm_7_3_3_preserves_multiplier`. -/
theorem algorithm_7_3_3_preserves_bracket {g : E} {H : E →L[ℝ] E}
    {pole Δ lo hi x r : ℝ} (hr : r ∈ Icc lo hi)
    (hG : (pole < x ∧ ‖shiftedStep g H x‖ < Δ) → r ≤ x)
    (hother : ¬(pole < x ∧ ‖shiftedStep g H x‖ < Δ) → x ≤ r) :
    let state := algorithm_7_3_3 g H pole Δ lo hi x
    r ∈ Icc state.1 state.2 := by
  unfold algorithm_7_3_3
  split
  · rename_i h
    exact ⟨hr.1, hG h⟩
  · rename_i h
    exact ⟨hother h, hr.2⟩

end Safeguards

section Eigensolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E} {H : E →L[ℝ] E} {hH : (H : E →ₗ[ℝ] E).IsSymmetric}

/-- **Algorithm 7.3.3** of [conn2000trust], the update keeps the multiplier. Let $\Delta > 0$,
$\lambda \ge 0$, and let $r$ be an optimal multiplier for a global minimizer $s_M$ with
$\|s_M\| \le \Delta$. If $r \in [\lambda^L, \lambda^U]$, then $r$ lies in the bracket updated by
Algorithm 7.3.3 with the pole $-\lambda_1$.

This includes a feasible unshifted trial $\lambda = 0$. -/
theorem algorithm_7_3_3_preserves_multiplier {Δ r lo hi x : ℝ}
    (hΔ : 0 < Δ) (hx : 0 ≤ x) {sM : E} (hsM : ‖sM‖ ≤ Δ)
    (hmul : IsTrustRegionMultiplier g H Δ sM r) (hr : r ∈ Icc lo hi) :
    let state := algorithm_7_3_3 g H (-leftmost hH) Δ lo hi x
    r ∈ Icc state.1 state.2 := by
  have hle : -leftmost hH ≤ r := neg_leftmost_le_shiftThreshold.trans
    (shiftThreshold_le_of_isTrustRegionMultiplier (hH := hH) hmul).1
  apply algorithm_7_3_3_preserves_bracket hr
  · rintro ⟨hp, hn⟩
    rcases hx.eq_or_lt with hz | hx'
    · subst x
      have hm : IsTrustRegionMultiplier g H Δ (shiftedStep g H 0) 0 :=
        ⟨le_rfl, (step_spec hp).1, isPositive_add_smul_of_le hp.le, zero_mul _⟩
      exact (hmul.unique hH hΔ hsM hm hn.le).le
    · have ht : shiftThreshold hH < x := max_lt hx' hp
      have hh := (le_secular_iff_of_trustRegion (hH := hH) hΔ hmul hsM ht).not
      exact (lt_of_not_ge (hh.mp (not_le.mpr
        (pow_lt_pow_left₀ hn (norm_nonneg _) two_ne_zero)))).le
  · intro hn
    rcases hx.eq_or_lt with hz | hx'
    · simpa [← hz] using hmul.nonneg
    · by_cases hp : -leftmost hH < x
      · have ht : shiftThreshold hH < x := max_lt hx' hp
        have hn' : Δ ≤ ‖shiftedStep g H x‖ := le_of_not_gt fun h => hn ⟨hp, h⟩
        exact (le_secular_iff_of_trustRegion (hH := hH) hΔ hmul hsM ht).mp
          (pow_le_pow_left₀ hΔ.le hn' 2)
      · exact (le_of_not_gt hp).trans hle

/-- **Algorithm 7.3.6** of [conn2000trust], corrected terminal branch. Let
$\lambda_s = \max\{0, -\lambda_1\}$, and suppose that $g$ is orthogonal to the kernel of
$H + \lambda_s I$ and that the minimum-norm solution $p$ of $(H + \lambda_s I) p = -g$ satisfies
$\|p\| \le \Delta$. If $\lambda_s > 0$, let $u$ be a unit vector in the kernel of
$H + \lambda_s I$. Let $s = p$ if $\lambda_s = 0$, and $s = p + \alpha u$ with the boundary
coefficient $\alpha$ of `ConnGouldToint.Chapter07.moreSorensenBoundaryCoefficient` otherwise.
Then $\|s\| \le \Delta$ and $s$ is a global minimizer of $q$ on the ball of radius $\Delta$.

**Correction.** The printed algorithm tests feasibility of the step at a positive perturbation
of the shift. A perturbation can shorten the raw step, so this is not an exact test of the hard
case; see `ConnGouldToint.Chapter07.algorithm_7_3_6_perturbation_counterexample`. The corrected
branch tests solvability and feasibility at the exact threshold. -/
theorem algorithm_7_3_6_exact_threshold {Δ : ℝ}
    (hg : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ)
    (hs : ‖particular hH g (shiftThreshold hH)‖ ≤ Δ) {u : E}
    (hu : 0 < shiftThreshold hH → ‖u‖ = 1 ∧
      u ∈ LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E)) :
    let μ := shiftThreshold hH
    let p := particular hH g μ
    let s := if μ = 0 then p else p + moreSorensenBoundaryCoefficient Δ p u • u
    s ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) s := by
  let μ := shiftThreshold hH
  let p := particular hH g μ
  have hμ : 0 ≤ μ := shiftThreshold_nonneg
  have hpole : -leftmost hH ≤ μ := neg_leftmost_le_shiftThreshold
  change (if μ = 0 then p else p + moreSorensenBoundaryCoefficient Δ p u • u) ∈
    Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ)
      (if μ = 0 then p else p + moreSorensenBoundaryCoefficient Δ p u • u)
  by_cases hz : μ = 0
  · rw [ite_eq_left hz]
    simpa only [add_zero] using isMinOn_closedBall_of_hardCase (hH := hH)
      hμ hpole hg (w := (0 : E)) (Submodule.zero_mem _) (by simpa only [add_zero] using hs)
      (Or.inl hz)
  · rw [ite_eq_right hz]
    obtain ⟨hun, huk⟩ := hu (lt_of_le_of_ne hμ (Ne.symm hz))
    have hb := norm_add_boundaryCorrection hs hun
    exact isMinOn_closedBall_of_hardCase (hH := hH) hμ hpole hg
      (Submodule.smul_mem _ _ huk) hb.le (Or.inr hb)

/-- **Algorithm 7.3.6** of [conn2000trust], Steps 4–6, finite Newton stopping. Let $g \neq 0$,
$\Delta > 0$, $\kappa > 0$, and let $r \ge 0$ with $r > -\lambda_1$ and $\|s(r)\|^2 = \Delta^2$.
Let $\lambda_0 > -\lambda_1$ with $\phi(\lambda_0) < 0$, and let $\lambda_k$ be the Newton
iterates from $\lambda_0$. Then there is $k$ with
$$\bigl|\|s(\lambda_k)\| - \Delta\bigr| \le \kappa \Delta.$$
-/
theorem algorithm_7_3_6_easy_stop (hg : g ≠ 0) {Δ r x₀ κ : ℝ} (hΔ : 0 < Δ)
    (hr : -leftmost hH < r) (hr₀ : 0 ≤ r) (hroot : secular g H r = Δ ^ 2)
    (hx₀ : -leftmost hH < x₀) (hbelow : phi g H Δ x₀ < 0) (hκ : 0 < κ) :
    let x := fun k : ℕ => (moreSorensenNewtonStep g H Δ)^[k] x₀
    ∃ k, |‖shiftedStep g H (x k)‖ - Δ| ≤ κ * Δ := by
  let x := fun k : ℕ => (moreSorensenNewtonStep g H Δ)^[k] x₀
  have h := (moreSorensen_easy_newton_convergence hg hΔ hr hr₀ hroot hx₀ hbelow).2.1
  have hnorm : ‖shiftedStep g H r‖ = Δ := by
    change ‖shiftedStep g H r‖ ^ 2 = Δ ^ 2 at hroot
    nlinarith [norm_nonneg (shiftedStep g H r)]
  have ht : Tendsto (fun k => ‖shiftedStep g H (x k)‖) atTop (𝓝 Δ) := hnorm ▸ h.norm
  obtain ⟨k, hk⟩ := (ht.eventually (Metric.ball_mem_nhds Δ (mul_pos hκ hΔ))).exists
  exact ⟨k, (by simpa [Metric.mem_ball, Real.dist_eq] using hk : _ < _).le⟩

/-- **Counterexample** to Step 3 of Algorithm 7.3.6 of [conn2000trust] as printed. Let
$\varepsilon > 0$, and on $\mathbb{R}$ let $H = -1$, $g = \varepsilon / 2$ and $s = -1/2$. Then
$(H + (1 + \varepsilon)) s = -g$ and $|s| < 1$, but the threshold system $(H + 1) t = -g$ has no
solution.

So with $\Delta = 1$ and threshold $\lambda_s = 1$, a feasible step at the perturbed shift
$1 + \varepsilon$ does not imply that the exact threshold system is solvable, however small
$\varepsilon$ is. -/
theorem algorithm_7_3_6_perturbation_counterexample {ε : ℝ} (hε : 0 < ε) :
    let H : ℝ →L[ℝ] ℝ := -(1 : ℝ →L[ℝ] ℝ)
    let g : ℝ := ε / 2
    let s : ℝ := -(1 / 2)
    (H + (1 + ε) • (1 : ℝ →L[ℝ] ℝ)) s = -g ∧ ‖s‖ < 1 ∧
      ¬ ∃ t : ℝ, (H + 1 • (1 : ℝ →L[ℝ] ℝ)) t = -g := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [smul_eq_mul]
    ring
  · norm_num [Real.norm_eq_abs]
  · rintro ⟨t, ht⟩
    simp at ht
    linarith

/-- **Algorithm 7.3.6** of [conn2000trust], Steps 1–2 and 4–6, corrected easy start. Let $g \neq 0$,
$\Delta > 0$, $\kappa > 0$, and let $r$ be an optimal multiplier for a global minimizer $s_M$
with $\|s_M\| \le \Delta$. Suppose that the exact threshold test fails: $g$ is not orthogonal to
the kernel of $H + \lambda_s I$, or the minimum-norm solution of the threshold system has norm
greater than $\Delta$. Let $0 < \varepsilon < r - \lambda_s$, and let $\lambda_0 = 0$ if $H$ is
positive definite and $\lambda_0 = -\lambda_1 + \varepsilon$ otherwise. Then
$\lambda_0 > -\lambda_1$, $\phi(\lambda_0) < 0$, and the Newton iterates $\lambda_k$ from
$\lambda_0$ satisfy $\bigl|\|s(\lambda_k)\| - \Delta\bigr| \le \kappa \Delta$ for some $k$. -/
theorem algorithm_7_3_6_easy_start (hg : g ≠ 0) {Δ r ε κ : ℝ} (hΔ : 0 < Δ)
    {sM : E} (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM r)
    (heasy : ¬ (g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) :
      E →ₗ[ℝ] E))ᗮ ∧ ‖particular hH g (shiftThreshold hH)‖ ≤ Δ))
    (hε : 0 < ε) (hnear : ε < r - shiftThreshold hH) (hκ : 0 < κ) :
    let x₀ := if -leftmost hH < 0 then 0 else -leftmost hH + ε
    let x := fun k : ℕ => (moreSorensenNewtonStep g H Δ)^[k] x₀
    (-leftmost hH < x₀ ∧ phi g H Δ x₀ < 0 ∧
      ∃ k, |‖shiftedStep g H (x k)‖ - Δ| ≤ κ * Δ) := by
  let x₀ := if -leftmost hH < 0 then 0 else -leftmost hH + ε
  have hclass := multiplier_classification_of_trustRegion (hH := hH) hΔ hmul hsM
  have hle := (shiftThreshold_le_of_isTrustRegionMultiplier (hH := hH) hmul).1
  have hr : shiftThreshold hH < r := hle.lt_of_ne (fun h => heasy (hclass.1.mp h.symm))
  have hrp := neg_leftmost_le_shiftThreshold.trans_lt hr
  have hnorm : ‖step g H r‖ = Δ := by
    rw [← hclass.2 hr]
    exact hmul.eq_zero_or_norm_eq.resolve_left (shiftThreshold_nonneg.trans_lt hr).ne'
  have hroot : secular g H r = Δ ^ 2 := by rw [secular, hnorm]
  have hφr : phi g H Δ r = 0 := by
    rw [phi_eq_inv_norm_sub_inv]
    change 1 / ‖step g H r‖ - 1 / Δ = 0
    rw [hnorm, sub_self]
  have hx₀ : -leftmost hH < x₀ ∧ x₀ < r := by
    unfold x₀
    split
    · exact ⟨‹-leftmost hH < 0›, shiftThreshold_nonneg.trans_lt hr⟩
    · exact ⟨lt_add_of_pos_right _ hε, by linarith [neg_leftmost_le_shiftThreshold (hH := hH)]⟩
  have hφ : phi g H Δ x₀ < 0 := hφr ▸
    (trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)).2.1 hx₀.1 hrp hx₀.2
  exact ⟨hx₀.1, hφ, algorithm_7_3_6_easy_stop hg hΔ hrp hmul.nonneg hroot hx₀.1 hφ hκ⟩

/-- **Algorithm 7.3.6** of [conn2000trust], corrected. Let $\lambda_s = \max\{0, -\lambda_1\}$ and
let $p$ be the minimum-norm solution of $(H + \lambda_s I) p = -g$. The algorithm with
perturbation $\varepsilon$, tolerance $\kappa$ and direction $u$ returns:

* if $g$ is orthogonal to the kernel of $H + \lambda_s I$ and $\|p\| \le \Delta$: the step $p$
  if $\lambda_s = 0$, and $p + \alpha u$ with the boundary coefficient $\alpha$ otherwise;
* otherwise: with $\lambda_0 = 0$ if $H$ is positive definite and
  $\lambda_0 = -\lambda_1 + \varepsilon$ if not, the step $s(\lambda_k)$ at the first Newton
  iterate $\lambda_k$ from $\lambda_0$ with $\bigl|\|s(\lambda_k)\| - \Delta\bigr| \le \kappa
  \Delta$, or no result if there is no such iterate.

The result is an `Option`, so that a proposed perturbation for which the radius test is never
met gives no step. -/
noncomputable def algorithm_7_3_6 (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (g : E) (Δ ε κ : ℝ) (u : E) : Option E := by
  classical
  exact
    let μ := shiftThreshold hH
    let p := particular hH g μ
    if g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧ ‖p‖ ≤ Δ then
      some (if μ = 0 then p else p + moreSorensenBoundaryCoefficient Δ p u • u)
    else
      let x₀ := if -leftmost hH < 0 then 0 else -leftmost hH + ε
      let s := fun k : ℕ => shiftedStep g H ((moreSorensenNewtonStep g H Δ)^[k] x₀)
      if h : ∃ k, |‖s k‖ - Δ| ≤ κ * Δ then some (s (Nat.find h)) else none

/-- **Algorithm 7.3.6** of [conn2000trust], corrected terminal branch. Under the hypotheses of
`ConnGouldToint.Chapter07.algorithm_7_3_6_exact_threshold`, the algorithm returns a step $s$
with $\|s\| \le \Delta$ that is a global minimizer of $q$ on the ball of radius $\Delta$. -/
theorem algorithm_7_3_6_returns_exact {Δ ε κ : ℝ}
    (hg : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ)
    (hs : ‖particular hH g (shiftThreshold hH)‖ ≤ Δ) {u : E}
    (hu : 0 < shiftThreshold hH → ‖u‖ = 1 ∧
      u ∈ LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E)) :
    ∃ s, algorithm_7_3_6 hH g Δ ε κ u = some s ∧
      s ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) s := by
  have htest : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) :
      E →ₗ[ℝ] E))ᗮ ∧ ‖particular hH g (shiftThreshold hH)‖ ≤ Δ := ⟨hg, hs⟩
  unfold algorithm_7_3_6
  dsimp only
  rw [ite_eq_left htest]
  exact ⟨_, rfl, algorithm_7_3_6_exact_threshold hg hs hu⟩

/-- **Algorithm 7.3.6** of [conn2000trust], finite return in the easy branch. Under the hypotheses
of `ConnGouldToint.Chapter07.algorithm_7_3_6_easy_start`, for every direction $u$ the algorithm
returns a step $s$ with $\bigl|\|s\| - \Delta\bigr| \le \kappa \Delta$. -/
theorem algorithm_7_3_6_returns_easy (hg : g ≠ 0) {Δ r ε κ : ℝ} (hΔ : 0 < Δ)
    {sM : E} (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM r)
    (heasy : ¬ (g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) :
      E →ₗ[ℝ] E))ᗮ ∧ ‖particular hH g (shiftThreshold hH)‖ ≤ Δ))
    (hε : 0 < ε) (hnear : ε < r - shiftThreshold hH) (hκ : 0 < κ) (u : E) :
    ∃ s, algorithm_7_3_6 hH g Δ ε κ u = some s ∧ |‖s‖ - Δ| ≤ κ * Δ := by
  let x₀ := if -leftmost hH < 0 then 0 else -leftmost hH + ε
  let s := fun k : ℕ => shiftedStep g H ((moreSorensenNewtonStep g H Δ)^[k] x₀)
  have h : ∃ k, |‖s k‖ - Δ| ≤ κ * Δ :=
    (algorithm_7_3_6_easy_start hg hΔ hsM hmul heasy hε hnear hκ).2.2
  unfold algorithm_7_3_6
  dsimp only
  rw [ite_eq_right heasy, dite_eq_left h]
  exact ⟨s (Nat.find h), rfl, Nat.find_spec h⟩

end Eigensolution

end ConnGouldToint.Chapter07
