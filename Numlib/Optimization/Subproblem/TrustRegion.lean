/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Optimization.Subproblem.Model

/-!
# Global optimality for the trust-region subproblem

Let $H$ be a symmetric operator on a real inner product space $E$, let $g \in E$, and let
$\Delta > 0$. The trust-region subproblem minimizes the quadratic model $m(s) = \langle g, s
\rangle + \frac12 \langle s, H s \rangle$ over the closed ball $\|s\| \le \Delta$. A feasible step
$s$ is a global minimizer if and only if there is a multiplier $\mu \ge 0$ with
$$(H + \mu I) s = -g, \qquad H + \mu I \succeq 0, \qquad \mu (\|s\| - \Delta) = 0.$$
This characterization is due to Gay, Sorensen, and Moré and Sorensen; it is Theorem 8.2.7 of
[cartis2022evaluation]. Here it holds on any real inner product space; only the existence of a
minimizer uses finite dimension. The file also proves that the multiplier is unique, that the
minimizer is unique when $H + \mu I$ is positive definite, and the properties of the optimal value
$m_\Delta$ as a function of the radius that §9.4.2 of [cartis2022evaluation] uses.

## Main definitions

* `Subproblem.IsTrustRegionMultiplier`: $\mu$ is a trust-region multiplier for the step $s$.
* `Subproblem.trustRegionValue`: the optimal value $m_\Delta = \inf \{m(s) : \|s\| \le \Delta\}$.

## Main results

* `Subproblem.isMinOn_closedBall_iff`: a feasible step is a global minimizer if and only if it has a
  trust-region multiplier.
* `Subproblem.exists_isMinOn_closedBall`: in finite dimension, a global minimizer exists.
* `Subproblem.IsTrustRegionMultiplier.unique`: all global minimizers have the same multiplier.
* `Subproblem.eq_of_isMinOn_closedBall_of_posDef`: the minimizer is unique when $H + \mu I$ is
  positive definite.
* `Subproblem.exists_shift_of_isMinOn_sphere`: a minimizer on the sphere $\|s\| = \Delta$ has a
  shift $\mu$ with $(H + \mu I) s = -g$ and $H + \mu I \succeq 0$.
* `Subproblem.trustRegionValue_antitone`, `Subproblem.trustRegionValue_mem_Icc`,
  `Subproblem.trustRegionValue_le_min`: the optimal value decreases as the radius grows, and the
  bounds (9.4.6) and (9.4.7) of [cartis2022evaluation].

## Proof outline

Sufficiency follows from the identity `Subproblem.quadModel_sub_eq_of_shifted` for a solution of the
shifted system. For necessity, an interior minimizer has zero gradient and $H \succeq 0$. At a
boundary minimizer, every inward direction $v$ with $\langle v, s \rangle < 0$ is a feasible
direction, so it is not a descent direction; hence the gradient is a nonpositive multiple of $s$.
The positive semidefiniteness of $H + \mu I$ follows by reflecting $s$ through hyperplanes, which
keeps the norm, together with a limit argument for the directions orthogonal to $s$.

## Implementation notes

* The complementarity condition $\mu (\|s\|^2 - \Delta^2) = 0$ of (8.2.32) of [cartis2022evaluation]
  is replaced by the equivalent condition $\mu (\|s\| - \Delta) = 0$.
* The source states in (9.4.5) that $m_{\Delta_2} \le m_{\Delta_1}$ if and only if
  $\Delta_2 \ge \Delta_1$. Only the "if" direction holds: the optimal value is constant once the
  unconstrained minimizer is interior, and also for $g = 0$, $H = 0$. Only that direction is
  formalized (`Subproblem.trustRegionValue_antitone`).
* `IsMinOn (Subproblem.quadModel g H) (closedBall 0 Δ) s` says that $m(s) \le m(u)$ for all $u$ in
  the ball; it does not say that $s$ lies in the ball. Feasibility is a separate hypothesis.
-/

open Filter Topology Metric Set
open scoped RealInnerProductSpace

noncomputable section

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Limits

/-- If $a + b t + c t^2 \ge 0$ for all sufficiently small $t > 0$, then $a \ge 0$. -/
theorem nonneg_of_eventually_nonneg_quadratic {a b c : ℝ}
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ a + b * t + c * t ^ 2) : 0 ≤ a := by
  have hc : Continuous fun t : ℝ => a + b * t + c * t ^ 2 := by fun_prop
  have ht : Tendsto (fun t : ℝ => a + b * t + c * t ^ 2) (𝓝[>] 0) (𝓝 a) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht h

/-- Let $H$ be symmetric, and let $s$ minimize the quadratic model $m$ on a set $S$. If
$s + t v \in S$ for all sufficiently small $t > 0$, then $v$ is not a descent direction:
$\langle g + H s, v \rangle \ge 0$. -/
theorem inner_add_apply_nonneg_of_isMinOn {g : E} {H : E →L[ℝ] E}
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {S : Set E} {s v : E} (hmin : IsMinOn (quadModel g H) S s)
    (hv : ∀ᶠ t in 𝓝[>] (0 : ℝ), s + t • v ∈ S) : 0 ≤ ⟪g + H s, v⟫ := by
  refine nonneg_of_eventually_nonneg_quadratic (b := ⟪v, H v⟫ / 2) (c := 0) ?_
  filter_upwards [hv, self_mem_nhdsWithin] with t ht (htpos : 0 < t)
  have h := hmin ht
  simp only [mem_ofPred_eq, quadModel_add_smul hH] at h
  have h' : 0 ≤ t * (⟪g + H s, v⟫ + ⟪v, H v⟫ / 2 * t) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left htpos).mp h'
  linarith

/-- If $\|s\| < \Delta$, then for every direction $v$, $s + t v$ lies in the closed ball of radius
$\Delta$ for all sufficiently small $t > 0$. -/
theorem eventually_add_smul_mem_closedBall_of_norm_lt {Δ : ℝ} {s : E} (hs : ‖s‖ < Δ) (v : E) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), s + t • v ∈ closedBall (0 : E) Δ := by
  have hc : Continuous fun t : ℝ => s + t • v := by fun_prop
  have hmem : ball (0 : E) Δ ∈ 𝓝 (s + (0 : ℝ) • v) := by
    simpa using isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hs)
  exact nhdsWithin_le_nhds ((hc.tendsto 0).eventually_mem hmem |>.mono
    fun _ h => ball_subset_closedBall h)

/-- If $\|s\| \le \Delta$ and $\langle s, v \rangle < 0$, then $s + t v$ lies in the closed ball of
radius $\Delta$ for all sufficiently small $t > 0$. -/
theorem eventually_add_smul_mem_closedBall_of_inner_neg {Δ : ℝ} {s v : E} (hs : ‖s‖ ≤ Δ)
    (hv : ⟪s, v⟫ < 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), s + t • v ∈ closedBall (0 : E) Δ := by
  have hc : Continuous fun t : ℝ => 2 * ⟪s, v⟫ + t * ‖v‖ ^ 2 := by fun_prop
  have hneg : ∀ᶠ t in 𝓝 (0 : ℝ), 2 * ⟪s, v⟫ + t * ‖v‖ ^ 2 < 0 :=
    (hc.tendsto 0).eventually (gt_mem_nhds (by simpa using (by linarith : 2 * ⟪s, v⟫ < 0)))
  filter_upwards [nhdsWithin_le_nhds hneg, self_mem_nhdsWithin] with t ht (htpos : 0 < t)
  rw [mem_closedBall_zero_iff]
  have hΔ : 0 ≤ Δ := (norm_nonneg _).trans hs
  have hsq : ‖s + t • v‖ ^ 2 = ‖s‖ ^ 2 + t * (2 * ⟪s, v⟫ + t * ‖v‖ ^ 2) := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have : ‖s + t • v‖ ^ 2 ≤ Δ ^ 2 := by
    rw [hsq]
    nlinarith [pow_le_pow_left₀ (norm_nonneg s) hs 2]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hΔ two_ne_zero).mp this

end Limits

/-- A real number $\mu$ is a **trust-region multiplier** for the step $s$ of the subproblem
$\min \{m(s) : \|s\| \le \Delta\}$ if
$$\mu \ge 0, \qquad (H + \mu I) s = -g, \qquad H + \mu I \succeq 0, \qquad \mu (\|s\| -
  \Delta) = 0.$$
These are the conditions (8.2.31)–(8.2.32) of [cartis2022evaluation].

The source writes the complementarity condition as $\mu (\|s\|^2 - \Delta^2) = 0$; the form
$\mu (\|s\| - \Delta) = 0$ is equivalent. Feasibility $\|s\| \le \Delta$ is not part of the
structure; results that need it take it as a separate hypothesis (see
`Subproblem.isMinOn_closedBall_iff`). Positive semidefiniteness is `LinearMap.IsPositive`, which
includes symmetry. -/
structure IsTrustRegionMultiplier (g : E) (H : E →L[ℝ] E) (Δ : ℝ) (s : E) (μ : ℝ) : Prop where
  /-- The multiplier is nonnegative: $\mu \ge 0$. -/
  nonneg : 0 ≤ μ
  /-- The step solves the shifted system $(H + \mu I) s = -g$. -/
  shifted : (H + μ • (1 : E →L[ℝ] E)) s = -g
  /-- The shifted operator $H + \mu I$ is positive semidefinite. -/
  isPositive : ((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive
  /-- Complementarity: $\mu (\|s\| - \Delta) = 0$, so the multiplier vanishes unless the constraint
  is active. -/
  complementarity : μ * (‖s‖ - Δ) = 0

section Optimality

variable {g : E} {H : E →L[ℝ] E} {Δ μ : ℝ} {s : E}

/-- A positive multiplier makes the constraint active: if $\mu > 0$, then $\|s\| = \Delta$. -/
theorem IsTrustRegionMultiplier.norm_eq_of_pos (h : IsTrustRegionMultiplier g H Δ s μ)
    (hμ : 0 < μ) : ‖s‖ = Δ :=
  sub_eq_zero.mp ((mul_eq_zero.mp h.complementarity).resolve_left hμ.ne')

/-- Complementarity as a disjunction: $\mu = 0$ or $\|s\| = \Delta$. -/
theorem IsTrustRegionMultiplier.eq_zero_or_norm_eq (h : IsTrustRegionMultiplier g H Δ s μ) :
    μ = 0 ∨ ‖s‖ = Δ :=
  (mul_eq_zero.mp h.complementarity).imp_right sub_eq_zero.mp

/-- If $\mu$ is a trust-region multiplier for $s$, then $\frac{\mu}{2} (\|s\|^2 - \|u\|^2) \ge 0$
for every $u$ with $\|u\| \le \Delta$. This is the multiplier term of the identity for the
shifted system. -/
theorem IsTrustRegionMultiplier.mul_sub_nonneg (h : IsTrustRegionMultiplier g H Δ s μ) {u : E}
    (hu : ‖u‖ ≤ Δ) : 0 ≤ μ / 2 * (‖s‖ ^ 2 - ‖u‖ ^ 2) := by
  rcases h.eq_zero_or_norm_eq with hμ | hs
  · simp [hμ]
  · have : ‖u‖ ^ 2 ≤ ‖s‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg u) (hs ▸ hu) 2
    have : 0 ≤ ‖s‖ ^ 2 - ‖u‖ ^ 2 := by linarith
    exact mul_nonneg (by linarith [h.nonneg]) this

/-- Quantitative sufficiency. Let $H$ be symmetric, and let $\mu$ be a trust-region multiplier for
$s$. Then for every $u$ with $\|u\| \le \Delta$,
$$m(u) - m(s) \ge \tfrac12 \langle u - s, (H + \mu I)(u - s) \rangle.$$
-/
theorem IsTrustRegionMultiplier.inner_le_quadModel_sub (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (h : IsTrustRegionMultiplier g H Δ s μ) {u : E} (hu : ‖u‖ ≤ Δ) :
    (1 / 2) * ⟪u - s, (H + μ • (1 : E →L[ℝ] E)) (u - s)⟫ ≤ quadModel g H u - quadModel g H s := by
  rw [quadModel_sub_eq_of_shifted hH h.shifted]
  linarith [h.mul_sub_nonneg hu]

/-- Sufficiency. Let $H$ be symmetric, and let $\mu$ be a trust-region multiplier for $s$. Then
$m(s) \le m(u)$ for every $u$ with $\|u\| \le \Delta$.

The conclusion `IsMinOn` does not say that $s$ lies in the ball; see
`Subproblem.IsTrustRegionMultiplier.isMinOn_of_norm_le` for the feasible version. -/
theorem IsTrustRegionMultiplier.isMinOn (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (h : IsTrustRegionMultiplier g H Δ s μ) : IsMinOn (quadModel g H) (closedBall 0 Δ) s := by
  intro u hu
  have hu' : ‖u‖ ≤ Δ := mem_closedBall_zero_iff.mp hu
  have := h.inner_le_quadModel_sub hH hu'
  have := ContinuousLinearMap.inner_apply_nonneg_of_isPositive h.isPositive (u - s)
  simp only [mem_ofPred_eq]
  linarith

/-- Sufficiency for a feasible step. Let $H$ be symmetric, let $\mu$ be a trust-region multiplier
for $s$, and let $\|s\| \le \Delta$. Then $s$ lies in the closed ball of radius $\Delta$ and
minimizes the quadratic model there. -/
theorem IsTrustRegionMultiplier.isMinOn_of_norm_le (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (h : IsTrustRegionMultiplier g H Δ s μ) (hs : ‖s‖ ≤ Δ) :
    s ∈ closedBall (0 : E) Δ ∧ IsMinOn (quadModel g H) (closedBall 0 Δ) s :=
  ⟨mem_closedBall_zero_iff.mpr hs, h.isMinOn hH⟩

/-- An interior minimizer has the multiplier $0$. Let $H$ be symmetric, let $\|s\| < \Delta$, and
let $s$ minimize the quadratic model on the closed ball of radius $\Delta$. Then $0$ is a
trust-region multiplier for $s$: $H s = -g$ and $H \succeq 0$. -/
theorem isTrustRegionMultiplier_zero_of_isMinOn_of_norm_lt (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (hs : ‖s‖ < Δ) (hmin : IsMinOn (quadModel g H) (closedBall 0 Δ) s) :
    IsTrustRegionMultiplier g H Δ s 0 := by
  have hd : ∀ v, 0 ≤ ⟪g + H s, v⟫ := fun v =>
    inner_add_apply_nonneg_of_isMinOn hH hmin (eventually_add_smul_mem_closedBall_of_norm_lt hs v)
  have hd0 : g + H s = 0 := by
    have := hd (-(g + H s))
    rw [inner_neg_right, real_inner_self_eq_norm_sq] at this
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (g + H s)])
  refine ⟨le_rfl, ?_, ?_, by simp⟩
  · simp only [zero_smul, add_zero]
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hd0
  · rw [ContinuousLinearMap.isPositive_add_smul_one_iff hH]
    intro v
    obtain ⟨t, ht, htpos⟩ := ((eventually_add_smul_mem_closedBall_of_norm_lt hs v).and
      self_mem_nhdsWithin).exists
    have h := hmin ht
    simp only [mem_ofPred_eq, quadModel_add_smul hH, hd0, inner_zero_left, mul_zero,
      add_zero] at h
    have htpos' : (0 : ℝ) < t ^ 2 / 2 := by have : (0 : ℝ) < t := htpos; positivity
    simpa using nonneg_of_mul_nonneg_right (by linarith) htpos'

/-- A minimizer on the boundary has a multiplier. Let $H$ be symmetric, let $\Delta > 0$ and
$\|s\| = \Delta$, and let $s$ minimize the quadratic model on the closed ball of radius
$\Delta$. Then $s$ has a trust-region multiplier. -/
theorem exists_isTrustRegionMultiplier_of_isMinOn_of_norm_eq
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hΔ : 0 < Δ) (hs : ‖s‖ = Δ)
    (hmin : IsMinOn (quadModel g H) (closedBall 0 Δ) s) :
    ∃ μ, IsTrustRegionMultiplier g H Δ s μ := by
  set d := g + H s with hd_def
  have hsq : 0 < ‖s‖ ^ 2 := by rw [hs]; positivity
  have hin : ∀ v, ⟪s, v⟫ < 0 → 0 ≤ ⟪d, v⟫ := fun v hv =>
    inner_add_apply_nonneg_of_isMinOn hH hmin
      (eventually_add_smul_mem_closedBall_of_inner_neg hs.le hv)
  -- the gradient is a multiple of `s`
  set α := ⟪d, s⟫ / ‖s‖ ^ 2 with hα_def
  set w := d - α • s with hw_def
  have hsw : ⟪s, w⟫ = 0 := by
    rw [hw_def, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hα_def,
      div_mul_cancel₀ _ hsq.ne', real_inner_comm, sub_self]
  have hdw : ⟪d, w⟫ = ‖w‖ ^ 2 := by
    have : d = w + α • s := by rw [hw_def]; abel
    rw [this, inner_add_left, inner_smul_left, hsw, real_inner_self_eq_norm_sq]
    simp
  have hw : w = 0 := by
    have key : 0 ≤ -‖w‖ ^ 2 := by
      refine nonneg_of_eventually_nonneg_quadratic (b := -⟪d, s⟫) (c := 0) ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have h := hin (-w - t • s) (by
        rw [inner_sub_right, inner_neg_right, hsw, inner_smul_right, real_inner_self_eq_norm_sq]
        nlinarith)
      rw [inner_sub_right, inner_neg_right, hdw, inner_smul_right] at h
      linarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])
  have hd : g + H s = α • s := by
    rw [← hd_def]; exact sub_eq_zero.mp hw
  have hα : α ≤ 0 := by
    have h := hin (-s) (by rw [inner_neg_right, real_inner_self_eq_norm_sq]; linarith)
    rw [inner_neg_right, hd_def, hd, inner_smul_left, real_inner_self_eq_norm_sq] at h
    simp only [conj_trivial] at h
    nlinarith
  have hshift : (H + (-α) • (1 : E →L[ℝ] E)) s = -g := by
    have : H s = α • s - g := by rw [← hd]; abel
    simp only [add_apply, smul_apply, one_apply_eq_self]
    rw [this, neg_smul]
    abel
  refine ⟨-α, ⟨by linarith, hshift, ?_, by simp [hs]⟩⟩
  -- positive semidefiniteness by reflection
  set T := H + (-α) • (1 : E →L[ℝ] E)
  have hrefl : ∀ v, ⟪v, s⟫ ≠ 0 → 0 ≤ ⟪v, T v⟫ := by
    intro v hv
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    have hvn : 0 < ‖v‖ ^ 2 := by positivity
    set c := 2 * ⟪v, s⟫ / ‖v‖ ^ 2 with hc_def
    have hc0 : c ≠ 0 := by rw [hc_def]; exact div_ne_zero (mul_ne_zero two_ne_zero hv) hvn.ne'
    have hnorm : ‖s - c • v‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        real_inner_comm, hc_def]
      field_simp
      ring
    have hmem : s - c • v ∈ closedBall (0 : E) Δ := by
      rw [mem_closedBall_zero_iff, ← hs]
      exact le_of_eq (by
        have := congrArg Real.sqrt hnorm
        rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this)
    have h := hmin hmem
    simp only [mem_ofPred_eq] at h
    have hid := quadModel_sub_eq_of_shifted hH hshift (s - c • v)
    rw [hnorm, sub_self, mul_zero, add_zero, sub_sub_cancel_left, map_neg, inner_neg_left,
      inner_neg_right, neg_neg, map_smul, inner_smul_left, inner_smul_right] at hid
    simp only [conj_trivial] at hid
    have : 0 ≤ c * c * ⟪v, T v⟫ := by nlinarith
    exact nonneg_of_mul_nonneg_right (by linarith) (mul_self_pos.mpr hc0)
  rw [ContinuousLinearMap.isPositive_add_smul_one_iff hH]
  intro v
  by_cases hv : ⟪v, s⟫ = 0
  · refine nonneg_of_eventually_nonneg_quadratic (b := ⟪v, T s⟫ + ⟪s, T v⟫) (c := ⟪s, T s⟫) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have h := hrefl (v + t • s) (by
      rw [inner_add_left, hv, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [conj_trivial, zero_add]
      positivity)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, conj_trivial] at h
    linarith
  · exact hrefl v hv

/-- **Global optimality for the trust-region subproblem.** Let $H$ be symmetric, let $\Delta > 0$,
and let $s \in E$ satisfy $\|s\| \le \Delta$. Then $s$ is a global minimizer of the quadratic
model $m$ on the ball $\{u : \|u\| \le \Delta\}$ if and only if $s$ has a trust-region
multiplier, that is, some $\mu \ge 0$ with
$$(H + \mu I) s = -g, \qquad H + \mu I \succeq 0, \qquad \mu (\|s\| - \Delta) = 0.$$
This is Theorem 8.2.7 of [cartis2022evaluation].

The space $E$ is any real inner product space; finite dimension is not needed. Sufficiency is
`Subproblem.IsTrustRegionMultiplier.isMinOn`, and necessity is
`Subproblem.isTrustRegionMultiplier_zero_of_isMinOn_of_norm_lt` for an interior minimizer and
`Subproblem.exists_isTrustRegionMultiplier_of_isMinOn_of_norm_eq` for a minimizer on the
boundary. -/
theorem isMinOn_closedBall_iff (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hΔ : 0 < Δ) (hs : ‖s‖ ≤ Δ) :
    IsMinOn (quadModel g H) (closedBall 0 Δ) s ↔ ∃ μ, IsTrustRegionMultiplier g H Δ s μ := by
  refine ⟨fun hmin => ?_, fun ⟨μ, h⟩ => h.isMinOn hH⟩
  rcases hs.lt_or_eq with hlt | heq
  · exact ⟨0, isTrustRegionMultiplier_zero_of_isMinOn_of_norm_lt hH hlt hmin⟩
  · exact exists_isTrustRegionMultiplier_of_isMinOn_of_norm_eq hH hΔ heq hmin

/-- **Existence of a minimizer.** Let $E$ be finite-dimensional, let $g \in E$, let $H$ be a
continuous linear operator on $E$, and let $\Delta \ge 0$. Then the quadratic model attains its
minimum on the closed ball of radius $\Delta$: there is $s$ with $\|s\| \le \Delta$ and
$m(s) \le m(u)$ for all $u$ with $\|u\| \le \Delta$.

The ball is compact and $m$ is continuous. Symmetry of $H$ is not needed. -/
theorem exists_isMinOn_closedBall [FiniteDimensional ℝ E] (g : E) (H : E →L[ℝ] E) (hΔ : 0 ≤ Δ) :
    ∃ s, ‖s‖ ≤ Δ ∧ IsMinOn (quadModel g H) (closedBall 0 Δ) s := by
  obtain ⟨s, hs, hmin⟩ := (isCompact_closedBall (0 : E) Δ).exists_isMinOn
    (nonempty_closedBall.mpr hΔ) (continuous_quadModel g H).continuousOn
  exact ⟨s, mem_closedBall_zero_iff.mp hs, hmin⟩

/-- Let $H$ be symmetric, and let $s$ and $s'$ be feasible steps with trust-region multipliers $\mu$
and $\mu'$. Then $(\mu - \mu') s' = 0$: the second step also solves the first shifted system. -/
theorem IsTrustRegionMultiplier.sub_smul_eq_zero (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (h : IsTrustRegionMultiplier g H Δ s μ) (hs : ‖s‖ ≤ Δ) {s' : E} {μ' : ℝ}
    (h' : IsTrustRegionMultiplier g H Δ s' μ') (hs' : ‖s'‖ ≤ Δ) : (μ - μ') • s' = 0 := by
  have h1 := h.inner_le_quadModel_sub hH hs'
  have h2 := h'.isMinOn hH (mem_closedBall_zero_iff.mpr hs)
  have h3 := ContinuousLinearMap.inner_apply_nonneg_of_isPositive h.isPositive (s' - s)
  simp only [mem_ofPred_eq] at h2
  have hq : ⟪(((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E)) (s' - s), s' - s⟫ = 0 := by
    rw [ContinuousLinearMap.coe_coe, real_inner_comm]; linarith
  have hk := h.isPositive.apply_eq_zero_of_inner_eq_zero hq
  rw [ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero, h.shifted] at hk
  exact sub_smul_eq_zero_of_shifted hk h'.shifted

/-- If $\Delta > 0$ and $\mu$ is a trust-region multiplier for the zero step, then $\mu = 0$. -/
theorem IsTrustRegionMultiplier.eq_zero_of_eq_zero (h : IsTrustRegionMultiplier g H Δ 0 μ)
    (hΔ : 0 < Δ) : μ = 0 :=
  h.eq_zero_or_norm_eq.resolve_right (by rw [norm_zero]; exact hΔ.ne)

/-- **The multiplier of a given step is unique.** Let $\Delta > 0$, and let $\mu$ and $\mu'$ be
trust-region multipliers for the same step $s$. Then $\mu = \mu'$.

Neither symmetry of $H$ nor feasibility of $s$ is needed. If $s = 0$, both multipliers are $0$
by complementarity; otherwise the two shifted systems give $(\mu - \mu') s = 0$. -/
theorem IsTrustRegionMultiplier.eq_of_same_step (hΔ : 0 < Δ)
    (h : IsTrustRegionMultiplier g H Δ s μ) {μ' : ℝ} (h' : IsTrustRegionMultiplier g H Δ s μ') :
    μ = μ' := by
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [h.eq_zero_of_eq_zero hΔ, h'.eq_zero_of_eq_zero hΔ]
  · have := sub_smul_eq_zero_of_shifted h.shifted h'.shifted
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hs0)

/-- **Uniqueness of the multiplier.** Let $H$ be symmetric and $\Delta > 0$, and let $s$ and $s'$ be
steps with $\|s\| \le \Delta$ and $\|s'\| \le \Delta$ that have trust-region multipliers $\mu$
and $\mu'$. Then $\mu = \mu'$.

By `Subproblem.isMinOn_closedBall_iff`, all global minimizers therefore have the same
multiplier. For a single step, see `Subproblem.IsTrustRegionMultiplier.eq_of_same_step`. -/
theorem IsTrustRegionMultiplier.unique (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hΔ : 0 < Δ)
    (h : IsTrustRegionMultiplier g H Δ s μ) (hs : ‖s‖ ≤ Δ) {s' : E} {μ' : ℝ}
    (h' : IsTrustRegionMultiplier g H Δ s' μ') (hs' : ‖s'‖ ≤ Δ) : μ = μ' := by
  rcases eq_or_ne s' 0 with rfl | hs'0
  · have hμ' := h'.eq_zero_of_eq_zero hΔ
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [h.eq_zero_of_eq_zero hΔ, hμ']
    · have := h'.sub_smul_eq_zero hH hs' h hs
      rw [smul_eq_zero] at this
      linarith [this.resolve_right hs0]
  · have := h.sub_smul_eq_zero hH hs h' hs'
    rw [smul_eq_zero] at this
    linarith [this.resolve_right hs'0]

/-- **Uniqueness of the minimizer.** Let $H$ be symmetric, let $s$ satisfy $\|s\| \le \Delta$ and
have a trust-region multiplier $\mu$, and let $H + \mu I$ be coercive (positive definite). Then
every $u$ with $\|u\| \le \Delta$ that minimizes the quadratic model on the closed ball of
radius $\Delta$ equals $s$. This is the last sentence of Theorem 8.2.7 of
[cartis2022evaluation].

Coercivity is `LinearMap.IsCoercive`: $\langle (H + \mu I) v, v \rangle \ge c \|v\|^2$ for some
$c > 0$ and all $v$. -/
theorem eq_of_isMinOn_closedBall_of_posDef (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (h : IsTrustRegionMultiplier g H Δ s μ) (hs : ‖s‖ ≤ Δ)
    (hc : ((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsCoercive) {u : E} (hu : ‖u‖ ≤ Δ)
    (hmin : IsMinOn (quadModel g H) (closedBall 0 Δ) u) : u = s := by
  obtain ⟨c, hc0, hc⟩ := hc
  have h1 := h.inner_le_quadModel_sub hH hu
  have h2 := hmin (mem_closedBall_zero_iff.mpr hs)
  simp only [mem_ofPred_eq] at h2
  have h3 := hc (u - s)
  simp only [ContinuousLinearMap.coe_coe, RCLike.re_to_real] at h3
  rw [real_inner_comm] at h3
  have : ‖u - s‖ ^ 2 ≤ 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (u - s)]))

/-- **Minimizers on the sphere.** Let $H$ be symmetric, let $\Delta > 0$, and let $s$ with
$\|s\| = \Delta$ minimize the quadratic model on the sphere $\{u : \|u\| = \Delta\}$. Then there
is a real number $\mu$ with
$$(H + \mu I) s = -g \qquad \text{and} \qquad H + \mu I \succeq 0.$$
If moreover $H + \mu I$ is coercive (positive definite), then every $u$ with $\|u\| = \Delta$
that minimizes the quadratic model on the sphere equals $s$.

The shift $\mu$ need not be nonnegative, because the constraint is an equality. -/
theorem exists_shift_of_isMinOn_sphere (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (hΔ : 0 < Δ) (hs : ‖s‖ = Δ) (hmin : IsMinOn (quadModel g H) (sphere 0 Δ) s) :
    ∃ μ : ℝ, (H + μ • (1 : E →L[ℝ] E)) s = -g ∧
      ((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive ∧
      (((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsCoercive →
        ∀ u : E, ‖u‖ = Δ → IsMinOn (quadModel g H) (sphere 0 Δ) u → u = s) := by
  -- Subtracting a multiple of the squared norm preserves the ordering on the
  -- sphere. Choose the multiple so that the new model is concave on diameters.
  let K := H + (-‖H‖) • (1 : E →L[ℝ] E)
  have hK := ContinuousLinearMap.isSymmetric_add_smul_one hH (-‖H‖)
  have hshift (v : E) : ⟪v, K v⟫ = ⟪v, H v⟫ - ‖H‖ * ‖v‖ ^ 2 := by
    simp [K, inner_add_right, inner_smul_right, sub_eq_add_neg]
  have hmodel (v : E) : quadModel g K v = quadModel g H v - ‖H‖ / 2 * ‖v‖ ^ 2 := by
    rw [quadModel_def, hshift, quadModel_def]
    ring
  have hcurv (v : E) : ⟪v, K v⟫ ≤ 0 := by
    have h := (real_inner_le_norm v (H v)).trans
      (mul_le_mul_of_nonneg_left (H.le_opNorm v) (norm_nonneg v))
    rw [hshift]
    nlinarith
  have hsphere : IsMinOn (quadModel g K) (sphere 0 Δ) s := by
    intro v hv
    have hv' : ‖v‖ = Δ := by simpa [mem_sphere, dist_zero_right] using hv
    have h := hmin hv
    simpa [hmodel, hs, hv', mem_ofPred_eq] using h
  have hdiameter (v : E) (hv : ‖v‖ = Δ) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
      quadModel g K s ≤ quadModel g K (t • v) := by
    have h₁ := hsphere (show v ∈ sphere (0 : E) Δ by simpa [mem_sphere, dist_zero_right] using hv)
    have h₂ := hsphere (show -v ∈ sphere (0 : E) Δ by simpa [mem_sphere, dist_zero_right] using hv)
    simp only [mem_ofPred_eq] at h₁ h₂
    have hcombine := add_le_add (mul_le_mul_of_nonneg_left h₁ (show 0 ≤ (1 + t) / 2 by linarith))
      (mul_le_mul_of_nonneg_left h₂ (show 0 ≤ (1 - t) / 2 by linarith))
    simp only [quadModel_def, map_neg, inner_neg_left, inner_neg_right, neg_neg] at hcombine
    simp only [quadModel_def, map_smul, inner_smul_left, inner_smul_right, conj_trivial]
    have hdiff := mul_nonneg (mul_nonneg (show 0 ≤ 1 - t by linarith)
      (show 0 ≤ 1 + t by linarith)) (neg_nonneg.mpr (hcurv v))
    nlinarith only [hcombine, hdiff]
  have hball : IsMinOn (quadModel g K) (closedBall 0 Δ) s := by
    intro u hu
    change quadModel g K s ≤ quadModel g K u
    have hu' := mem_closedBall_zero_iff.mp hu
    by_cases huz : u = 0
    · simpa [huz] using hdiameter s hs 0 le_rfl zero_le_one
    · have hn : 0 < ‖u‖ := norm_pos_iff.mpr huz
      have hv : ‖(Δ / ‖u‖) • u‖ = Δ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_mul_cancel₀ _ hn.ne']
      have h := hdiameter _ hv (‖u‖ / Δ) (by positivity) ((div_le_one hΔ).mpr hu')
      rwa [smul_smul, show ‖u‖ / Δ * (Δ / ‖u‖) = 1 by field_simp, one_smul] at h
  obtain ⟨ν, hν⟩ := (isMinOn_closedBall_iff hK hΔ hs.le).mp hball
  have hoperator : H + (ν - ‖H‖) • (1 : E →L[ℝ] E) = K + ν • 1 := by
    dsimp [K]
    rw [show ν - ‖H‖ = -‖H‖ + ν by ring, add_smul, add_assoc]
  refine ⟨ν - ‖H‖, ?_⟩
  rw [hoperator]
  refine ⟨hν.shifted, hν.isPositive, fun hc u hu hmu => ?_⟩
  have hmu' : IsMinOn (quadModel g K) (closedBall 0 Δ) u := by
    intro v hv
    have h₁ := hball hv
    have h₂ := hmu (show s ∈ sphere (0 : E) Δ by simpa [mem_sphere, dist_zero_right] using hs)
    have h₃ : quadModel g K u ≤ quadModel g K s := by
      simp only [mem_ofPred_eq] at h₂
      simpa [hmodel, hu, hs] using h₂
    exact h₃.trans h₁
  exact eq_of_isMinOn_closedBall_of_posDef hK hν hs.le hc hu.le hmu'

end Optimality

section Value

variable {g : E} {H : E →L[ℝ] E}

/-- The **optimal value** of the trust-region subproblem:
$$m_\Delta = \inf \{m(s) : \|s\| \le \Delta\}.$$
This is the value $m_\Delta$ of §9.4.2 of [cartis2022evaluation].

The infimum is `sInf` on $\mathbb{R}$. It is $0$ when the ball is empty ($\Delta < 0$) or when
the model is not bounded below on the ball; the second case does not occur in finite dimension
(`Subproblem.bddBelow_image_closedBall`). -/
def trustRegionValue (g : E) (H : E →L[ℝ] E) (Δ : ℝ) : ℝ :=
  sInf (quadModel g H '' closedBall 0 Δ)

/-- If $s$ with $\|s\| \le \Delta$ minimizes the quadratic model on the closed ball of radius
$\Delta$, then the optimal value is $m_\Delta = m(s)$. -/
theorem IsMinOn.trustRegionValue_eq {Δ : ℝ} {s : E} (hs : ‖s‖ ≤ Δ)
    (hmin : IsMinOn (quadModel g H) (closedBall 0 Δ) s) :
    trustRegionValue g H Δ = quadModel g H s :=
  IsLeast.csInf_eq ⟨mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hs),
    forall_mem_image.mpr fun _ hu => hmin hu⟩

variable [FiniteDimensional ℝ E]

/-- In finite dimension, the quadratic model is bounded below on every closed ball. -/
theorem bddBelow_image_closedBall (g : E) (H : E →L[ℝ] E) (Δ : ℝ) :
    BddBelow (quadModel g H '' closedBall 0 Δ) :=
  ((isCompact_closedBall (0 : E) Δ).image (continuous_quadModel g H)).bddBelow

/-- In finite dimension, the optimal value is a lower bound for the model on the ball:
$m_\Delta \le m(u)$ for every $u$ with $\|u\| \le \Delta$. -/
theorem trustRegionValue_le {Δ : ℝ} {u : E} (hu : ‖u‖ ≤ Δ) :
    trustRegionValue g H Δ ≤ quadModel g H u :=
  csInf_le (bddBelow_image_closedBall g H Δ) (mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hu))

/-- **The optimal value decreases as the radius grows.** Let $E$ be finite-dimensional, and let
$0 \le \Delta_1 \le \Delta_2$. Then $m_{\Delta_2} \le m_{\Delta_1}$.

This is the valid direction of (9.4.5) of [cartis2022evaluation]. The source states an
equivalence, but the converse fails; see the module documentation. -/
theorem trustRegionValue_antitone {Δ₁ Δ₂ : ℝ} (h₁ : 0 ≤ Δ₁) (h : Δ₁ ≤ Δ₂) :
    trustRegionValue g H Δ₂ ≤ trustRegionValue g H Δ₁ :=
  csInf_le_csInf (bddBelow_image_closedBall g H Δ₂) ((nonempty_closedBall.mpr h₁).image _)
    (image_mono (closedBall_subset_closedBall h))

/-- In finite dimension, rescaling any vector $v$ to the radius $\Delta \ge 0$ gives an upper bound
on the optimal value: $m_\Delta \le m\bigl((\Delta / \|v\|) v\bigr)$. For $v = 0$ the rescaled
vector is $0$, by the Lean convention $\Delta / 0 = 0$. -/
theorem trustRegionValue_le_smul {Δ : ℝ} (hΔ : 0 ≤ Δ) (v : E) :
    trustRegionValue g H Δ ≤ quadModel g H ((Δ / ‖v‖) • v) := by
  refine trustRegionValue_le ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using hΔ
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)]

/-- **Bounds from a larger radius.** Let $E$ be finite-dimensional, let $0 \le \Delta \le \Delta^+$,
and let $s^+ \in E$ satisfy $\|s^+\| = \Delta^+$. Then
$$m_{\Delta^+} \le m_\Delta \le m\bigl((\Delta / \Delta^+) s^+\bigr).$$
This is (9.4.6) of [cartis2022evaluation].

The vector $s^+$ need not be a minimizer for the radius $\Delta^+$. If $\Delta^+ = 0$, then
$\Delta = 0$ and $s^+ = 0$, so the rescaled vector is $0$. -/
theorem trustRegionValue_mem_Icc {Δ Δp : ℝ} (hΔ : 0 ≤ Δ) (h : Δ ≤ Δp) {sp : E}
    (hsp : ‖sp‖ = Δp) :
    trustRegionValue g H Δ ∈
      Icc (trustRegionValue g H Δp) (quadModel g H ((Δ / Δp) • sp)) :=
  ⟨trustRegionValue_antitone hΔ h, hsp ▸ trustRegionValue_le_smul hΔ sp⟩

/-- **Bounds from a smaller radius.** Let $E$ be finite-dimensional, let
$0 \le \Delta^- \le \Delta$, and let $s^- \in E$ satisfy $\|s^-\| = \Delta^-$. Then
$$m_\Delta \le \min\bigl\{m\bigl((\Delta / \Delta^-) s^-\bigr), \ m_{\Delta^-}\bigr\}.$$
This is (9.4.7) of [cartis2022evaluation].

The vector $s^-$ need not be a minimizer for the radius $\Delta^-$. If $\Delta^- = 0$, then
$s^- = 0$, so the rescaled vector is $0$ and the first bound is $m_\Delta \le m(0) = 0$. -/
theorem trustRegionValue_le_min {Δ Δm : ℝ} (hΔm : 0 ≤ Δm) (h : Δm ≤ Δ) {sm : E}
    (hsm : ‖sm‖ = Δm) :
    trustRegionValue g H Δ ≤ min (quadModel g H ((Δ / Δm) • sm)) (trustRegionValue g H Δm) :=
  le_min (hsm ▸ trustRegionValue_le_smul (hΔm.trans h) sm) (trustRegionValue_antitone hΔm h)

end Value

end Subproblem

end
