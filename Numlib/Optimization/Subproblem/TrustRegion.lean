import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Optimization.Subproblem.Model

/-!
# Global optimality for the trust-region subproblem

The trust-region subproblem minimizes the quadratic model `m(s) = ⟪g, s⟫ + ½ ⟪s, H s⟫` over the
closed ball `‖s‖ ≤ Δ`. Its global minimizers are characterized by the existence of a multiplier
`μ ≥ 0` with `(H + μ I) s = -g`, `H + μ I` positive semidefinite and `μ (‖s‖ - Δ) = 0`
(Gay, Sorensen, Moré–Sorensen; [cartis2022evaluation] Theorem 8.2.7). The characterization is
necessary *and* sufficient and holds on any real inner product space; only the existence of a
minimizer uses finite dimension.

Sufficiency is immediate from the shifted-system identity `quadModel_sub_eq_of_shifted`.
Necessity is proved from first principles: an interior minimizer has zero gradient and `H ⪰ 0`;
at a boundary minimizer the gradient is a nonpositive multiple of `s` (every inward direction
`⟪v, s⟫ < 0` is a feasible ascent direction), and positive semidefiniteness of `H + μ I` follows by
reflecting `s` through hyperplanes, which keeps the norm, plus a limiting argument for directions
orthogonal to `s`.

## Main definitions

* `Subproblem.IsTrustRegionMultiplier g H Δ s μ`: `μ` is a trust-region multiplier for `s`.
* `Subproblem.trustRegionValue g H Δ`: the optimal value `inf {m(s) : ‖s‖ ≤ Δ}`.

## Main statements

* `Subproblem.isMinOn_closedBall_iff`: the global optimality characterization.
* `Subproblem.exists_isMinOn_closedBall`: existence of a global minimizer in finite dimension.
* `Subproblem.IsTrustRegionMultiplier.unique`: all global minimizers share the same multiplier.
* `Subproblem.eq_of_isMinOn_closedBall_of_posDef`: uniqueness when `H + μ I` is positive
  definite.
* `Subproblem.trustRegionValue_antitone`, `Subproblem.trustRegionValue_mem_Icc`,
  `Subproblem.trustRegionValue_le_min`: monotonicity of the optimal value in the radius and the
  bounds (9.4.6)–(9.4.7) of [cartis2022evaluation] §9.4.2.

## Implementation notes

The book's `‖s‖² - Δ²` in the complementarity condition (8.2.32) is replaced by the equivalent
`‖s‖ - Δ`. The book's (9.4.5) states `m_{Δ₂} ≤ m_{Δ₁}` *if and only if* `Δ₂ ≥ Δ₁`; only the "if"
direction holds (the optimal value is constant once the unconstrained minimizer is interior, and
for `g = 0`, `H = 0`), and only that direction is formalized.
-/

open Filter Topology Metric Set
open scoped RealInnerProductSpace

noncomputable section

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Limits

/-- If `a + b t + c t² ≥ 0` for all small enough `t > 0`, then `a ≥ 0`. -/
theorem nonneg_of_eventually_nonneg_quadratic {a b c : ℝ}
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ a + b * t + c * t ^ 2) : 0 ≤ a := by
  have hc : Continuous fun t : ℝ => a + b * t + c * t ^ 2 := by fun_prop
  have ht : Tendsto (fun t : ℝ => a + b * t + c * t ^ 2) (𝓝[>] 0) (𝓝 a) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht h

/-- If `s + t v` stays in `S` for all small `t > 0` and `s` minimizes the quadratic model on `S`,
then `v` is not a descent direction: `0 ≤ ⟪g + H s, v⟫`. -/
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

/-- From an interior point of a closed ball, every direction stays in the ball for small steps. -/
theorem eventually_add_smul_mem_closedBall_of_norm_lt {Δ : ℝ} {s : E} (hs : ‖s‖ < Δ) (v : E) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), s + t • v ∈ closedBall (0 : E) Δ := by
  have hc : Continuous fun t : ℝ => s + t • v := by fun_prop
  have hmem : ball (0 : E) Δ ∈ 𝓝 (s + (0 : ℝ) • v) := by
    simpa using isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hs)
  exact nhdsWithin_le_nhds ((hc.tendsto 0).eventually_mem hmem |>.mono
    fun _ h => ball_subset_closedBall h)

/-- From a point of a closed ball, every strictly inward direction `⟪s, v⟫ < 0` stays in the
ball for small steps. -/
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

/-- `μ` is a **trust-region multiplier** for the step `s` of the subproblem
`min {m(s) : ‖s‖ ≤ Δ}`: `μ ≥ 0`, `(H + μ I) s = -g`, `H + μ I` is positive semidefinite and
`μ (‖s‖ - Δ) = 0` ([cartis2022evaluation] (8.2.31)–(8.2.32), with the complementarity
`μ (‖s‖² - Δ²) = 0` written in the equivalent form `μ (‖s‖ - Δ) = 0`).

Feasibility `‖s‖ ≤ Δ` is *not* part of this structure; results that need it take it as a separate
hypothesis (see `isMinOn_closedBall_iff`). -/
structure IsTrustRegionMultiplier (g : E) (H : E →L[ℝ] E) (Δ : ℝ) (s : E) (μ : ℝ) : Prop where
  /-- The multiplier is nonnegative. -/
  nonneg : 0 ≤ μ
  /-- The step solves the shifted system. -/
  shifted : (H + μ • (1 : E →L[ℝ] E)) s = -g
  /-- The shifted operator is positive semidefinite. -/
  isPositive : ((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive
  /-- Complementarity: the multiplier vanishes unless the constraint is active. -/
  complementarity : μ * (‖s‖ - Δ) = 0

section Optimality

variable {g : E} {H : E →L[ℝ] E} {Δ μ : ℝ} {s : E}

/-- A positive multiplier forces the constraint to be active: `0 < μ → ‖s‖ = Δ`. -/
theorem IsTrustRegionMultiplier.norm_eq_of_pos (h : IsTrustRegionMultiplier g H Δ s μ)
    (hμ : 0 < μ) : ‖s‖ = Δ :=
  sub_eq_zero.mp ((mul_eq_zero.mp h.complementarity).resolve_left hμ.ne')

/-- Complementarity as a disjunction: either `μ = 0` or the constraint is active. -/
theorem IsTrustRegionMultiplier.eq_zero_or_norm_eq (h : IsTrustRegionMultiplier g H Δ s μ) :
    μ = 0 ∨ ‖s‖ = Δ :=
  (mul_eq_zero.mp h.complementarity).imp_right sub_eq_zero.mp

/-- Under complementarity, the multiplier term of the shifted-system identity is nonnegative on
the ball: `0 ≤ μ/2 (‖s‖² - ‖u‖²)` for `‖u‖ ≤ Δ`. -/
theorem IsTrustRegionMultiplier.mul_sub_nonneg (h : IsTrustRegionMultiplier g H Δ s μ) {u : E}
    (hu : ‖u‖ ≤ Δ) : 0 ≤ μ / 2 * (‖s‖ ^ 2 - ‖u‖ ^ 2) := by
  rcases h.eq_zero_or_norm_eq with hμ | hs
  · simp [hμ]
  · have : ‖u‖ ^ 2 ≤ ‖s‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg u) (hs ▸ hu) 2
    have : 0 ≤ ‖s‖ ^ 2 - ‖u‖ ^ 2 := by linarith
    exact mul_nonneg (by linarith [h.nonneg]) this

/-- Quantitative sufficiency: if `μ` is a trust-region multiplier for `s`, then on the ball
`m(u) - m(s) ≥ ½ ⟪u - s, (H + μ I)(u - s)⟫`. -/
theorem IsTrustRegionMultiplier.inner_le_quadModel_sub (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (h : IsTrustRegionMultiplier g H Δ s μ) {u : E} (hu : ‖u‖ ≤ Δ) :
    (1 / 2) * ⟪u - s, (H + μ • (1 : E →L[ℝ] E)) (u - s)⟫ ≤ quadModel g H u - quadModel g H s := by
  rw [quadModel_sub_eq_of_shifted hH h.shifted]
  linarith [h.mul_sub_nonneg hu]

/-- Sufficiency: a step with a trust-region multiplier minimizes the quadratic model on the
ball, in the sense that `m(s) ≤ m(u)` for every `u` in the ball. `IsMinOn` does not assert that
`s` itself lies in the ball; see `IsTrustRegionMultiplier.isMinOn_of_norm_le` for the feasible
version. -/
theorem IsTrustRegionMultiplier.isMinOn (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (h : IsTrustRegionMultiplier g H Δ s μ) : IsMinOn (quadModel g H) (closedBall 0 Δ) s := by
  intro u hu
  have hu' : ‖u‖ ≤ Δ := mem_closedBall_zero_iff.mp hu
  have := h.inner_le_quadModel_sub hH hu'
  have := ContinuousLinearMap.inner_apply_nonneg_of_isPositive h.isPositive (u - s)
  simp only [mem_ofPred_eq]
  linarith

/-- Sufficiency for a feasible step: `s` lies in the ball and minimizes the quadratic model
there. -/
theorem IsTrustRegionMultiplier.isMinOn_of_norm_le (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (h : IsTrustRegionMultiplier g H Δ s μ) (hs : ‖s‖ ≤ Δ) :
    s ∈ closedBall (0 : E) Δ ∧ IsMinOn (quadModel g H) (closedBall 0 Δ) s :=
  ⟨mem_closedBall_zero_iff.mpr hs, h.isMinOn hH⟩

/-- An interior global minimizer on the ball is an unconstrained critical point with `H ⪰ 0`;
its multiplier is `0`. -/
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

/-- A global minimizer on the boundary `‖s‖ = Δ > 0` of the ball has a trust-region multiplier. -/
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

/-- **Trust-region subproblem global optimality** ([cartis2022evaluation] Theorem 8.2.7). For
symmetric `H`, `Δ > 0` and `‖s‖ ≤ Δ`, the step `s` is a global minimizer of the quadratic model
on the ball `‖s‖ ≤ Δ` if and only if it has a trust-region multiplier: some `μ ≥ 0` with
`(H + μ I) s = -g`, `H + μ I` positive semidefinite and `μ (‖s‖ - Δ) = 0`. -/
theorem isMinOn_closedBall_iff (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hΔ : 0 < Δ) (hs : ‖s‖ ≤ Δ) :
    IsMinOn (quadModel g H) (closedBall 0 Δ) s ↔ ∃ μ, IsTrustRegionMultiplier g H Δ s μ := by
  refine ⟨fun hmin => ?_, fun ⟨μ, h⟩ => h.isMinOn hH⟩
  rcases hs.lt_or_eq with hlt | heq
  · exact ⟨0, isTrustRegionMultiplier_zero_of_isMinOn_of_norm_lt hH hlt hmin⟩
  · exact exists_isTrustRegionMultiplier_of_isMinOn_of_norm_eq hH hΔ heq hmin

/-- In finite dimension, the quadratic model attains its minimum on every closed ball of
nonnegative radius. -/
theorem exists_isMinOn_closedBall [FiniteDimensional ℝ E] (g : E) (H : E →L[ℝ] E) (hΔ : 0 ≤ Δ) :
    ∃ s, ‖s‖ ≤ Δ ∧ IsMinOn (quadModel g H) (closedBall 0 Δ) s := by
  obtain ⟨s, hs, hmin⟩ := (isCompact_closedBall (0 : E) Δ).exists_isMinOn
    (nonempty_closedBall.mpr hΔ) (continuous_quadModel g H).continuousOn
  exact ⟨s, mem_closedBall_zero_iff.mp hs, hmin⟩

/-- If two feasible steps have trust-region multipliers `μ` and `μ'`, then `(μ - μ') s' = 0`:
the second step solves the first shifted system as well. -/
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

/-- A multiplier vanishes at the zero step when `Δ > 0`. -/
theorem IsTrustRegionMultiplier.eq_zero_of_eq_zero (h : IsTrustRegionMultiplier g H Δ 0 μ)
    (hΔ : 0 < Δ) : μ = 0 :=
  h.eq_zero_or_norm_eq.resolve_right (by rw [norm_zero]; exact hΔ.ne)

/-- The multiplier of a given step is unique when `Δ > 0` (no symmetry or feasibility needed):
two multipliers `μ`, `μ'` for the same `s` coincide. -/
theorem IsTrustRegionMultiplier.eq_of_same_step (hΔ : 0 < Δ)
    (h : IsTrustRegionMultiplier g H Δ s μ) {μ' : ℝ} (h' : IsTrustRegionMultiplier g H Δ s μ') :
    μ = μ' := by
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [h.eq_zero_of_eq_zero hΔ, h'.eq_zero_of_eq_zero hΔ]
  · have := sub_smul_eq_zero_of_shifted h.shifted h'.shifted
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hs0)

/-- **Uniqueness of the multiplier.** For symmetric `H` and `Δ > 0`, all feasible steps with a
trust-region multiplier (equivalently, by `isMinOn_closedBall_iff`, all global minimizers) have
the same multiplier (for a single step see `IsTrustRegionMultiplier.eq_of_same_step`). -/
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

/-- **Uniqueness of the minimizer** ([cartis2022evaluation] Theorem 8.2.7, last sentence). If
`s` is feasible with trust-region multiplier `μ` and `H + μ I` is coercive (positive definite),
then `s` is the only global minimizer of the quadratic model on the ball. -/
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

end Optimality

section Value

variable {g : E} {H : E →L[ℝ] E}

/-- The optimal value `inf {m(s) : ‖s‖ ≤ Δ}` of the trust-region subproblem
(`m_Δ` of [cartis2022evaluation] §9.4.2). -/
def trustRegionValue (g : E) (H : E →L[ℝ] E) (Δ : ℝ) : ℝ :=
  sInf (quadModel g H '' closedBall 0 Δ)

/-- The optimal value is attained at any global minimizer. -/
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

/-- The optimal value is a lower bound for the model on the ball. -/
theorem trustRegionValue_le {Δ : ℝ} {u : E} (hu : ‖u‖ ≤ Δ) :
    trustRegionValue g H Δ ≤ quadModel g H u :=
  csInf_le (bddBelow_image_closedBall g H Δ) (mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hu))

/-- The optimal value is antitone in the radius: `Δ₁ ≤ Δ₂ → m_{Δ₂} ≤ m_{Δ₁}`
([cartis2022evaluation] (9.4.5), the valid direction). -/
theorem trustRegionValue_antitone {Δ₁ Δ₂ : ℝ} (h₁ : 0 ≤ Δ₁) (h : Δ₁ ≤ Δ₂) :
    trustRegionValue g H Δ₂ ≤ trustRegionValue g H Δ₁ :=
  csInf_le_csInf (bddBelow_image_closedBall g H Δ₂) ((nonempty_closedBall.mpr h₁).image _)
    (image_mono (closedBall_subset_closedBall h))

/-- Rescaling any vector to the radius `Δ ≥ 0` gives an upper bound on the optimal value:
`m_Δ ≤ m((Δ / ‖v‖) v)`. -/
theorem trustRegionValue_le_smul {Δ : ℝ} (hΔ : 0 ≤ Δ) (v : E) :
    trustRegionValue g H Δ ≤ quadModel g H ((Δ / ‖v‖) • v) := by
  refine trustRegionValue_le ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using hΔ
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)]

/-- Bounds from a larger radius ([cartis2022evaluation] (9.4.6)): if `0 ≤ Δ ≤ Δ⁺` and
`‖s⁺‖ = Δ⁺` (in the book, `s⁺` is a minimizer for the radius `Δ⁺`, which is not needed), then
`m_{Δ⁺} ≤ m_Δ ≤ m((Δ / Δ⁺) s⁺)`. -/
theorem trustRegionValue_mem_Icc {Δ Δp : ℝ} (hΔ : 0 ≤ Δ) (h : Δ ≤ Δp) {sp : E}
    (hsp : ‖sp‖ = Δp) :
    trustRegionValue g H Δ ∈
      Icc (trustRegionValue g H Δp) (quadModel g H ((Δ / Δp) • sp)) :=
  ⟨trustRegionValue_antitone hΔ h, hsp ▸ trustRegionValue_le_smul hΔ sp⟩

/-- Bounds from a smaller radius ([cartis2022evaluation] (9.4.7)): if `0 ≤ Δ⁻ ≤ Δ` and
`‖s⁻‖ = Δ⁻`, then `m_Δ ≤ min (m((Δ / Δ⁻) s⁻)) m_{Δ⁻}`. -/
theorem trustRegionValue_le_min {Δ Δm : ℝ} (hΔm : 0 ≤ Δm) (h : Δm ≤ Δ) {sm : E}
    (hsm : ‖sm‖ = Δm) :
    trustRegionValue g H Δ ≤ min (quadModel g H ((Δ / Δm) • sm)) (trustRegionValue g H Δm) :=
  le_min (hsm ▸ trustRegionValue_le_smul (hΔm.trans h) sm) (trustRegionValue_antitone hΔm h)

end Value

end Subproblem

end
