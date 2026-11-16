/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.MeanInequalities
import Numlib.Optimization.Subproblem.TrustRegion

/-!
# Global optimality for the regularization subproblem

Let $E$ be a real inner product space, let $H : E \to E$ be a symmetric continuous linear operator,
let $g \in E$, and let $\sigma > 0$ and $r > 2$. The **regularization subproblem** minimizes the
regularized model
$$m^R(s) = \langle g, s \rangle + \tfrac12 \langle s, H s \rangle + \frac{\sigma}{r} \|s\|^r$$
over all of $E$. Its global minimizers are exactly the steps $s$ with $(H + \lambda I) s = -g$ and
$H + \lambda I$ positive semidefinite, where $\lambda = \sigma \|s\|^{r-2}$. This is Theorem 8.2.8
of [cartis2022evaluation]. The result is due to Griewank, Nesterov and Polyak, and Cartis, Gould and
Toint for $r = 3$, and to Hsia, Sheu and Yuan for general $r$. The characterization holds on every
real inner product space. Only the existence of a minimizer uses finite dimension.

## Main results

* `Subproblem.isMinOn_regModel_iff`: $s$ is a global minimizer of $m^R$ if and only if
  $(H + \lambda I) s = -g$ and $H + \lambda I$ is positive semidefinite, with
  $\lambda = \sigma \|s\|^{r-2}$.
* `Subproblem.exists_isMinOn_regModel`: in finite dimension, $m^R$ has a global minimizer.
* `Subproblem.eq_of_isMinOn_regModel_of_posDef`: if $H + \lambda I$ is positive definite at a global
  minimizer, then that minimizer is unique.
* `Subproblem.norm_eq_of_isMinOn_regModel`: all global minimizers have the same norm, and hence the
  same multiplier $\lambda$.

## Proof outline

The proof uses the trust-region theory instead of a separate argument. A global minimizer $s$ of
$m^R$ minimizes the quadratic model on the ball of radius $\|s\|$. So it has a trust-region
multiplier, and the first-order condition identifies this multiplier with $\sigma \|s\|^{r-2}$.
Sufficiency follows from the shifted-system identity and the weighted arithmetic–geometric mean
inequality $a^2 b^{r-2} \le \frac{2}{r} a^r + \left(1 - \frac{2}{r}\right) b^r$.
-/

open Filter Topology Metric Set
open scoped RealInnerProductSpace

noncomputable section

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A weighted arithmetic–geometric mean inequality: for $a, b \ge 0$ and $r \ge 2$,
$$a^2 b^{r-2} \le \frac{2}{r} a^r + \left(1 - \frac{2}{r}\right) b^r.$$
-/
theorem sq_mul_rpow_sub_two_le {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 2 ≤ r) :
    a ^ 2 * b ^ (r - 2) ≤ 2 / r * a ^ r + (1 - 2 / r) * b ^ r := by
  have hr0 : 0 < r := by linarith
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 2 / r) (w₂ := 1 - 2 / r)
    (p₁ := a ^ r) (p₂ := b ^ r) (by positivity)
    (by rw [sub_nonneg, div_le_one hr0]; exact hr) (Real.rpow_nonneg ha _)
    (Real.rpow_nonneg hb _) (by ring)
  rwa [← Real.rpow_mul ha, ← Real.rpow_mul hb, mul_div_cancel₀ _ hr0.ne', mul_sub, mul_one,
    mul_div_cancel₀ _ hr0.ne', Real.rpow_two] at h

/-- For $a, b \ge 0$, $\sigma \ge 0$ and $r > 2$, with $\lambda = \sigma b^{r-2}$,
$$\frac{\lambda}{2} \left(b^2 - a^2\right) + \frac{\sigma}{r} \left(a^r - b^r\right) \ge 0.$$
That is, the regularization term dominates the multiplier term. -/
theorem mul_sub_add_div_mul_sub_nonneg {a b σ r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hσ : 0 ≤ σ)
    (hr : 2 < r) :
    0 ≤ σ * b ^ (r - 2) / 2 * (b ^ 2 - a ^ 2) + σ / r * (a ^ r - b ^ r) := by
  have hr0 : 0 < r := by linarith
  have hY := sq_mul_rpow_sub_two_le ha hb hr.le
  have hb2 : b ^ (r - 2) * b ^ 2 = b ^ r := by
    rw [← Real.rpow_two, ← Real.rpow_add' hb (by linarith)]; ring_nf
  have key : 0 ≤ σ / 2 * (2 / r * a ^ r + (1 - 2 / r) * b ^ r - a ^ 2 * b ^ (r - 2)) :=
    mul_nonneg (by positivity) (by linarith)
  have e : σ * b ^ (r - 2) / 2 * (b ^ 2 - a ^ 2) + σ / r * (a ^ r - b ^ r) =
      σ / 2 * (2 / r * a ^ r + (1 - 2 / r) * b ^ r - a ^ 2 * b ^ (r - 2)) := by
    rw [← hb2]; field_simp; ring
  rw [e]; exact key

variable {g : E} {H : E →L[ℝ] E} {σ r : ℝ} {s : E}

/-- Let $\sigma \ge 0$ and $r > 0$. If $s$ is a global minimizer of the regularized model $m^R$ on
$E$, then $s$ minimizes the quadratic model $m$ on the closed ball
$\{u \in E : \|u\| \le \|s\|\}$.

This reduces the regularization subproblem to the trust-region subproblem with radius $\|s\|$. -/
theorem isMinOn_closedBall_of_isMinOn_regModel (hσ : 0 ≤ σ) (hr : 0 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) :
    IsMinOn (quadModel g H) (closedBall 0 ‖s‖) s := by
  intro u hu
  have hu' : ‖u‖ ≤ ‖s‖ := mem_closedBall_zero_iff.mp hu
  have h := hmin (mem_univ u)
  simp only [mem_ofPred_eq, regModel] at h ⊢
  have : ‖u‖ ^ r ≤ ‖s‖ ^ r := Real.rpow_le_rpow (norm_nonneg _) hu' hr.le
  have : σ / r * ‖u‖ ^ r ≤ σ / r * ‖s‖ ^ r := mul_le_mul_of_nonneg_left this (by positivity)
  linarith

/-- Quantitative sufficiency. Let $H$ be symmetric, $\sigma \ge 0$ and $r > 2$, and let $s \in E$
satisfy $(H + \lambda I) s = -g$ with $\lambda = \sigma \|s\|^{r-2}$. Then for every $u \in E$
$$m^R(u) - m^R(s) \ge \tfrac12 \langle u - s, (H + \lambda I)(u - s) \rangle.$$
-/
theorem inner_le_regModel_sub_of_shifted (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hσ : 0 ≤ σ)
    (hr : 2 < r) (hs : (H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E)) s = -g) (u : E) :
    (1 / 2) * ⟪u - s, (H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E)) (u - s)⟫ ≤
      regModel g H σ r u - regModel g H σ r s := by
  have hid := quadModel_sub_eq_of_shifted hH hs u
  have := mul_sub_add_div_mul_sub_nonneg (norm_nonneg u) (norm_nonneg s) hσ hr
  simp only [regModel]
  linarith

/-- The first-order condition at a global minimizer of the regularized model. Let $H$ be symmetric
and $r > 1$. If $s$ is a global minimizer of $m^R$ on $E$, then $(H + \lambda I) s = -g$ with
$\lambda = \sigma \|s\|^{r-2}$. -/
theorem shifted_of_isMinOn_regModel (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hr : 1 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) :
    (H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E)) s = -g := by
  have h0 := (hmin.isLocalMin univ_mem).hasFDerivAt_eq_zero (hasFDerivAt_regModel hH σ hr s)
  have hv : g + H s + (σ * ‖s‖ ^ (r - 2)) • s = 0 := by
    have := congrArg (fun L : E →L[ℝ] ℝ => L (g + H s + (σ * ‖s‖ ^ (r - 2)) • s)) h0
    simp only [innerSL_apply_apply, zero_apply] at this
    exact inner_self_eq_zero.mp this
  simp only [add_apply, smul_apply, one_apply_eq_self]
  rw [eq_neg_iff_add_eq_zero, ← hv]
  abel

/-- Let $r > 2$ and $g = 0$. If $s = 0$ is a global minimizer of the regularized model $m^R$ on $E$,
then $H$ is positive semidefinite: $\langle v, H v \rangle \ge 0$ for every $v \in E$.

The reason is that $m^R(t v) = \frac{t^2}{2} \langle v, H v \rangle + \frac{\sigma}{r} |t|^r
\|v\|^r \ge 0$ for all $t$, and the second term is $o(t^2)$ as $t \to 0$. -/
theorem inner_apply_nonneg_of_isMinOn_regModel_zero (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ 0) (hg : g = 0) (v : E) : 0 ≤ ⟪v, H v⟫ := by
  have hr0 : r ≠ 0 := by linarith
  have hc : Continuous fun t : ℝ => ⟪v, H v⟫ / 2 + σ / r * ‖v‖ ^ r * t ^ (r - 2) :=
    continuous_const.add (continuous_const.mul
      (Real.continuous_rpow_const (by linarith)))
  have ht : Tendsto (fun t : ℝ => ⟪v, H v⟫ / 2 + σ / r * ‖v‖ ^ r * t ^ (r - 2)) (𝓝[>] 0)
      (𝓝 (⟪v, H v⟫ / 2)) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [Real.zero_rpow (show r - 2 ≠ 0 by linarith)] using this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ ⟪v, H v⟫ / 2 + σ / r * ‖v‖ ^ r * t ^ (r - 2) := by
    filter_upwards [self_mem_nhdsWithin] with t (htpos : 0 < t)
    have h := hmin (mem_univ (t • v))
    simp only [mem_ofPred_eq, regModel, quadModel, hg, inner_zero_left, norm_zero,
      Real.zero_rpow hr0, mul_zero, inner_zero_right,
      zero_add, map_smul, inner_smul_left, inner_smul_right, conj_trivial, norm_smul,
      Real.norm_eq_abs, abs_of_pos htpos, Real.mul_rpow htpos.le (norm_nonneg v)] at h
    have ht2 : t ^ r = t ^ 2 * t ^ (r - 2) := by
      rw [← Real.rpow_two, ← Real.rpow_add htpos]; ring_nf
    rw [ht2] at h
    have : 0 ≤ t ^ 2 * (⟪v, H v⟫ / 2 + σ / r * ‖v‖ ^ r * t ^ (r - 2)) := by
      linarith [show t ^ 2 * (⟪v, H v⟫ / 2 + σ / r * ‖v‖ ^ r * t ^ (r - 2)) =
        1 / 2 * (t * (t * ⟪v, H v⟫)) + σ / r * (t ^ 2 * t ^ (r - 2) * ‖v‖ ^ r) by ring]
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp this
  have := ge_of_tendsto ht hev
  linarith

/-- **Global optimality for the regularization subproblem.** Let $E$ be a real inner product space,
let $H : E \to E$ be a symmetric continuous linear operator, let $g \in E$, and let $\sigma > 0$
and $r > 2$. For $s \in E$ put $\lambda = \sigma \|s\|^{r-2}$. Then $s$ is a global minimizer of
the regularized model $m^R$ on $E$ if and only if
$$(H + \lambda I) s = -g \quad \text{and} \quad H + \lambda I \text{ is positive
  semidefinite}.$$

This is Theorem 8.2.8 of [cartis2022evaluation]. The statement holds on every real inner product
space, also of infinite dimension. Positive semidefinite is `LinearMap.IsPositive` of the
operator $H + \lambda I$. -/
theorem isMinOn_regModel_iff (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hσ : 0 < σ) (hr : 2 < r) :
    IsMinOn (regModel g H σ r) univ s ↔
      (H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E)) s = -g ∧
        ((H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive := by
  constructor
  · intro hmin
    have hshift := shifted_of_isMinOn_regModel hH (by linarith) hmin
    refine ⟨hshift, ?_⟩
    rcases eq_or_ne s 0 with rfl | hs0
    · have hlam : σ * ‖(0 : E)‖ ^ (r - 2) = 0 := by
        simp [Real.zero_rpow (show r - 2 ≠ 0 by linarith)]
      have hg : g = 0 := by simpa [hlam] using hshift.symm
      rw [hlam, ContinuousLinearMap.isPositive_add_smul_one_iff hH]
      intro v
      simpa using inner_apply_nonneg_of_isMinOn_regModel_zero hr hmin hg v
    · have hball := isMinOn_closedBall_of_isMinOn_regModel hσ.le (by linarith) hmin
      obtain ⟨μ, hμ⟩ := (isMinOn_closedBall_iff hH (norm_pos_iff.mpr hs0) le_rfl).mp hball
      have h := sub_smul_eq_zero_of_shifted hμ.shifted hshift
      rw [smul_eq_zero] at h
      have : μ = σ * ‖s‖ ^ (r - 2) := sub_eq_zero.mp (h.resolve_right hs0)
      exact this ▸ hμ.isPositive
  · rintro ⟨hshift, hpos⟩ u _
    have h1 := inner_le_regModel_sub_of_shifted hH hσ.le hr hshift u
    have h2 := ContinuousLinearMap.inner_apply_nonneg_of_isPositive hpos (u - s)
    simp only [mem_ofPred_eq]
    linarith

/-- For every $s \in E$ with $\|s\| \ge 1$, the regularized model satisfies
$$m^R(s) \ge \frac{\sigma}{r} \|s\|^r - \left(\|g\| + \frac{\|H\|}{2}\right) \|s\|^2.$$
-/
theorem regModel_ge (g : E) (H : E →L[ℝ] E) (σ r : ℝ) {s : E} (hs : 1 ≤ ‖s‖) :
    σ / r * ‖s‖ ^ r - (‖g‖ + ‖H‖ / 2) * ‖s‖ ^ 2 ≤ regModel g H σ r s := by
  have h1 : -(‖g‖ * ‖s‖) ≤ ⟪g, s⟫ := by
    have := abs_real_inner_le_norm g s; rw [abs_le] at this; exact this.1
  have h2 : -(‖H‖ * ‖s‖ ^ 2) ≤ ⟪s, H s⟫ := by
    have := abs_real_inner_le_norm s (H s); rw [abs_le] at this
    have h3 : ‖s‖ * ‖H s‖ ≤ ‖H‖ * ‖s‖ ^ 2 := by
      have := H.le_opNorm s
      nlinarith [norm_nonneg s]
    linarith [this.1]
  have h4 : ‖g‖ * ‖s‖ ≤ ‖g‖ * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (norm_nonneg g)
  simp only [regModel, quadModel]
  nlinarith

/-- Let $E$ be a proper space, for example a finite-dimensional space. For $\sigma > 0$ and $r > 2$,
the regularized model $m^R$ tends to $+\infty$ as $\|s\| \to \infty$, that is, along the
cocompact filter. -/
theorem tendsto_regModel_cocompact [ProperSpace E] (g : E) (H : E →L[ℝ] E) (hσ : 0 < σ)
    (hr : 2 < r) : Tendsto (regModel g H σ r) (cocompact E) atTop := by
  set C := ‖g‖ + ‖H‖ / 2
  have hφ : Tendsto (fun t : ℝ => t ^ 2 * (σ / r * t ^ (r - 2) - C)) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_mul_atTop₀
      (tendsto_atTop_add_const_right _ _
        ((tendsto_rpow_atTop (by linarith)).const_mul_atTop (by positivity)))
  have hψ : Tendsto (fun t : ℝ => σ / r * t ^ r - C * t ^ 2) atTop atTop := by
    refine hφ.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [show t ^ r = t ^ 2 * t ^ (r - 2) by
      rw [← Real.rpow_two, ← Real.rpow_add ht]; ring_nf]
    ring
  refine tendsto_atTop_mono' _ ?_ (hψ.comp tendsto_norm_cocompact_atTop)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop 1)] with s hs
  exact regModel_ge g H σ r hs

/-- **Existence of a global minimizer.** Let $E$ be a finite-dimensional real inner product space,
let $g \in E$, let $H : E \to E$ be a continuous linear operator, and let $\sigma > 0$ and
$r > 2$. Then the regularized model $m^R$ has a global minimizer on $E$.

The proof uses that $m^R$ is continuous and tends to $+\infty$ at infinity. The operator $H$
need not be symmetric. -/
theorem exists_isMinOn_regModel [FiniteDimensional ℝ E] (g : E) (H : E →L[ℝ] E) (hσ : 0 < σ)
    (hr : 2 < r) : ∃ s, IsMinOn (regModel g H σ r) univ s := by
  obtain ⟨s, hs⟩ := (continuous_regModel g H σ (by linarith : (0 : ℝ) ≤ r)).exists_forall_le
    (tendsto_regModel_cocompact g H hσ hr)
  exact ⟨s, fun u _ => hs u⟩

/-- **Uniqueness of the global minimizer.** Let $H$ be symmetric, and let $\sigma > 0$ and $r > 2$.
Let $s$ be a global minimizer of the regularized model $m^R$ on $E$, and suppose that
$H + \lambda I$ with $\lambda = \sigma \|s\|^{r-2}$ is coercive: there is $c > 0$ with $\langle
(H + \lambda I) x, x \rangle \ge c \|x\|^2$ for all $x \in E$. Then every global minimizer $u$
of $m^R$ equals $s$.

This is the last sentence of Theorem 8.2.8 of [cartis2022evaluation]. Coercivity is a form of
positive definiteness. In finite dimension the two are the same. The condition is
`LinearMap.IsCoercive`. -/
theorem eq_of_isMinOn_regModel_of_posDef (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hσ : 0 < σ)
    (hr : 2 < r) (hmin : IsMinOn (regModel g H σ r) univ s)
    (hc : ((H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsCoercive)
    {u : E} (hu : IsMinOn (regModel g H σ r) univ u) : u = s := by
  obtain ⟨c, hc0, hc⟩ := hc
  have h1 := inner_le_regModel_sub_of_shifted hH hσ.le hr
    (shifted_of_isMinOn_regModel hH (by linarith) hmin) u
  have h2 := hu (mem_univ s)
  simp only [mem_ofPred_eq] at h2
  have h3 := hc (u - s)
  simp only [ContinuousLinearMap.coe_coe, RCLike.re_to_real] at h3
  rw [real_inner_comm] at h3
  have : ‖u - s‖ ^ 2 ≤ 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (u - s)]))

/-- Let $H$ be symmetric, and let $\sigma > 0$ and $r > 2$. If $s$ and $s'$ are global minimizers of
the regularized model $m^R$ on $E$, then
$$(\lambda - \lambda') s' = 0, \qquad \lambda = \sigma \|s\|^{r-2}, \quad \lambda' = \sigma
  \|s'\|^{r-2}.$$
So $s'$ also solves the shifted system $(H + \lambda I) s' = -g$ of $s$. -/
theorem sub_smul_eq_zero_of_isMinOn_regModel (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hσ : 0 < σ)
    (hr : 2 < r) (hmin : IsMinOn (regModel g H σ r) univ s) {s' : E}
    (hmin' : IsMinOn (regModel g H σ r) univ s') :
    (σ * ‖s‖ ^ (r - 2) - σ * ‖s'‖ ^ (r - 2)) • s' = 0 := by
  obtain ⟨hshift, hpos⟩ := (isMinOn_regModel_iff hH hσ hr).mp hmin
  have hshift' := shifted_of_isMinOn_regModel hH (by linarith) hmin'
  have h1 := inner_le_regModel_sub_of_shifted hH hσ.le hr hshift s'
  have h2 := hmin' (mem_univ s)
  have h3 := ContinuousLinearMap.inner_apply_nonneg_of_isPositive hpos (s' - s)
  simp only [mem_ofPred_eq] at h2
  have hq : ⟪(((H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E)) (s' - s),
      s' - s⟫ = 0 := by
    rw [ContinuousLinearMap.coe_coe, real_inner_comm]; linarith
  have hk := hpos.apply_eq_zero_of_inner_eq_zero hq
  rw [ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero, hshift] at hk
  exact sub_smul_eq_zero_of_shifted hk hshift'

/-- **All global minimizers have the same norm.** Let $H$ be symmetric, and let $\sigma > 0$ and
$r > 2$. If $s$ and $s'$ are global minimizers of the regularized model $m^R$ on $E$, then
$$\|s\| = \|s'\|.$$
Hence all global minimizers have the same multiplier $\lambda_* = \sigma \|s\|^{r-2}$.

This is stated in Section 8.2.4 of [cartis2022evaluation]. -/
theorem norm_eq_of_isMinOn_regModel (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) {s' : E}
    (hmin' : IsMinOn (regModel g H σ r) univ s') : ‖s‖ = ‖s'‖ := by
  have hr2 : r - 2 ≠ 0 := by linarith
  have hlam : σ * ‖s‖ ^ (r - 2) = σ * ‖s'‖ ^ (r - 2) := by
    have h := sub_smul_eq_zero_of_isMinOn_regModel hH hσ hr hmin hmin'
    have h' := sub_smul_eq_zero_of_isMinOn_regModel hH hσ hr hmin' hmin
    rw [smul_eq_zero] at h h'
    rcases h with h | h
    · exact sub_eq_zero.mp h
    rcases h' with h' | h'
    · exact (sub_eq_zero.mp h').symm
    · simp [h, h']
  have := mul_left_cancel₀ hσ.ne' hlam
  exact (Real.rpow_left_injOn hr2 |>.eq_iff (norm_nonneg _) (norm_nonneg _)).mp this

end Subproblem

end
