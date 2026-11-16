/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Subproblem.Regularization
import Numlib.Optimization.Subproblem.Secular

/-!
# The optimal multiplier and the secular equation

Let $E$ be a finite-dimensional real inner product space, let $H : E \to E$ be a symmetric
continuous linear operator with leftmost eigenvalue $\lambda_1$, and let $g \in E$. Put
$\lambda_s = \max\{0, -\lambda_1\}$. Write $s(\lambda) = -(H + \lambda I)^{-1} g$ for the step and
$\pi(\lambda) = \|s(\lambda)\|^2$ for the secular function. A global minimizer $s$ of the
trust-region subproblem or of the regularization subproblem solves a shifted system
$(H + \lambda_* I) s = -g$ with $\lambda_* \ge \lambda_s$ and $\|s\|^2 = \tau(\lambda_*)$, for a
target function $\tau$. The target is $\tau(\lambda) = \Delta^2$ for the trust region and
$\tau(\lambda) = (\lambda / \sigma)^{2/(r-2)}$ for the regularization, as in (8.2.9) of
[cartis2022evaluation]. This file locates the multiplier $\lambda_*$ with the secular function,
following Lemma 8.2.1 and Section 8.3 of [cartis2022evaluation].

The results are first proved for an abstract target $\tau$, monotone on $[\lambda_s, \infty)$ and
positive on $(\lambda_s, \infty)$, and an abstract solution $s$ of $(H + \mu I) s = -g$ with
$\lambda_s \le \mu$, $\|s\|^2 \le \tau(\mu)$, and equality when $\mu > \lambda_s$. The two
subproblems are then special cases. For $\lambda > \lambda_s$ the multiplier splits
$(\lambda_s, \infty)$ into the set $\mathcal{L} = (\lambda_s, \lambda_*]$, where
$\tau(\lambda) \le \pi(\lambda)$, and the set $\mathcal{G} = (\lambda_*, \infty)$, where
$\pi(\lambda) < \tau(\lambda)$.

## Main results

* `Subproblem.existsUnique_secular_root`: if $\tau < \pi$ just to the right of $\lambda_s$, then the
  secular equation $\pi(\lambda) = \tau(\lambda)$ has a unique root $\lambda_* > \lambda_s$ (Lemma
  8.2.1).
* `Subproblem.existsUnique_secular_root_of_lt`: the same under the hypothesis
  $\pi(\lambda_s) > \tau(\lambda_s)$ of the source, where $\pi(\lambda_s)$ is the right limit of
  $\pi$.
* `Subproblem.tendsto_secular_shiftThreshold` and `Subproblem.tendsto_secular_shiftThreshold_atTop`:
  as $\lambda \downarrow \lambda_s$, $\pi(\lambda)$ tends to the squared norm of the minimum-norm
  solution of $(H + \lambda_s I) x = -g$ if this system is consistent, and to $+\infty$ otherwise.
* `Subproblem.le_secular_iff_of_shifted`, `Subproblem.le_secular_iff_of_trustRegion` and
  `Subproblem.le_secular_iff_of_regularization`: for $\lambda > \lambda_s$,
  $\tau(\lambda) \le \pi(\lambda)$ if and only if $\lambda \le \lambda_*$. This includes the hard
  case, where $\mathcal{L} = \emptyset$.
* `Subproblem.shiftThreshold_le_of_isTrustRegionMultiplier` and
  `Subproblem.shiftThreshold_le_of_isMinOn_regModel`: $\lambda_s \le \lambda_*$, and every minimizer
  is the minimum-norm solution of $(H + \lambda_* I) x = -g$ plus a kernel vector orthogonal to $g$,
  which vanishes when $\lambda_* > -\lambda_1$ (Corollaries 8.3.1 and 8.3.2, (8.3.1)–(8.3.2)).
* `Subproblem.multiplier_classification`, `Subproblem.multiplier_classification_of_trustRegion` and
  `Subproblem.multiplier_classification_of_regularization`: $\lambda_* = \lambda_s$ exactly when $g$
  is orthogonal to $\ker(H + \lambda_s I)$ and the minimum-norm solution $s_s$ at $\lambda_s$ has
  $\|s_s\|^2 \le \tau(\lambda_s)$ (the interior and hard cases). Otherwise $\lambda_* > \lambda_s$
  (the easy case) and the minimizer is $s(\lambda_*)$.
* `Subproblem.isMinOn_closedBall_of_hardCase`, `Subproblem.isMinOn_regModel_of_hardCase` and
  `Subproblem.exists_norm_particular_add_smul_eq`: the hard-case solutions $s_s + \alpha v_1$ are
  global minimizers.
* `Subproblem.optimalValue_eq_of_trustRegion` and `Subproblem.optimalValue_eq_of_regularization`:
  the optimal values (8.3.5) and (8.3.3).

## Implementation notes

* The source describes the set $\mathcal{N} = (-\infty, \lambda_s]$ also as the set of $\lambda$ for
  which $H + \lambda M$ is not positive definite. The two descriptions differ when $\lambda_1 > 0$:
  then $(-\lambda_1, 0]$ lies in the first set but not in the second. This file uses the interval
  $(-\infty, \lambda_s]$.
* The leftmost eigenvalue is `Subproblem.leftmost`, the threshold $\lambda_s$ is
  `Subproblem.shiftThreshold`, the step and the secular function are `Subproblem.step` and
  `Subproblem.secular`, and the minimum-norm solution of $(H + \lambda I) x = -g$ is
  `Subproblem.particular`.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E} {hH : (H : E →ₗ[ℝ] E).IsSymmetric} {g : E}

/-! ### Solutions of a shifted system -/

section Shifted

/-- **Structure of the solutions of a shifted system.** Let $H$ be symmetric, $\mu \in \mathbb{R}$,
and let $s \in E$ satisfy $(H + \mu I) s = -g$. Let $p$ be the minimum-norm solution
`Subproblem.particular` of this system. Then:
* the system is consistent: $g$ is orthogonal to $\ker(H + \mu I)$;
* the vector $w = s - p$ lies in $\ker(H + \mu I)$ and satisfies $\langle g, w \rangle = 0$;
* $\|p\| \le \|s\|$;
* if $\mu > -\lambda_1$, then $s = s(\mu)$, the step `Subproblem.step`. -/
theorem particular_add_of_shifted {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧
      s - particular hH g μ ∈ LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) ∧
      ⟪g, s - particular hH g μ⟫ = 0 ∧ ‖particular hH g μ‖ ≤ ‖s‖ ∧
      (-leftmost hH < μ → s = step g H μ) := by
  have hcons : g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
    have h := ContinuousLinearMap.isSymmetric_add_smul_one hH μ v s
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← neg_neg g, ← hs, inner_neg_right, ← h, hv, inner_zero_left, neg_zero]
  obtain ⟨-, hiff, hmin, horth⟩ := (particular_spec (hH := hH) (g := g) μ).2.1 hcons
  have hker := (hiff s).1 hs
  exact ⟨hcons, hker, horth _ hker, hmin s hs, fun hμ => (step_spec hμ).2 s hs⟩

/-- For symmetric $H$ and every $g \in E$, the secular function $\pi$ is antitone on
$(-\lambda_1, \infty)$.

For $g \neq 0$ it is strictly decreasing there. This declaration states only the weak form. -/
theorem secular_antitoneOn : AntitoneOn (secular g H) (Ioi (-leftmost hH)) := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [secular_zero_left]; exact fun _ _ _ _ _ => le_rfl
  · exact ((secular_shape (hH := hH) hg 1).2.2.1).antitoneOn

/-- For $0 < d \le e$, $(a / e)^2 \le (a / d)^2$. -/
private theorem div_sq_le_div_sq {a d e : ℝ} (hd : 0 < d) (hde : d ≤ e) :
    (a / e) ^ 2 ≤ (a / d) ^ 2 := by
  rw [div_pow, div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg a) (by positivity) (pow_le_pow_left₀ hd.le hde 2)

/-- For $0 < d < e$ and $a \neq 0$, $(a / e)^2 < (a / d)^2$. -/
private theorem div_sq_lt_div_sq {a d e : ℝ} (ha : a ≠ 0) (hd : 0 < d) (hde : d < e) :
    (a / e) ^ 2 < (a / d) ^ 2 := by
  rw [div_pow, div_pow]
  exact div_lt_div_of_pos_left (by positivity) (by positivity)
    (pow_lt_pow_left₀ hde hd.le two_ne_zero)

/-- **The secular function lies below the minimum-norm solution.** Let $H$ be symmetric, let
$g \neq 0$, and let $\mu \ge -\lambda_1$ be such that $g$ is orthogonal to $\ker(H + \mu I)$.
Let $p$ be the minimum-norm solution `Subproblem.particular` of $(H + \mu I) x = -g$. Then for
every $\lambda > \mu$
$$\pi(\lambda) < \|p\|^2.$$

In the hard case $\mu = -\lambda_1$, this says that $\pi$ stays below its limit $\|s_s\|^2$ at
the threshold. -/
theorem secular_lt_norm_particular_sq (hg : g ≠ 0) {μ lam : ℝ} (hμ : -leftmost hH ≤ μ)
    (hlt : μ < lam) (hcons : g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ) :
    secular g H lam < ‖particular hH g μ‖ ^ 2 := by
  have hlam : -leftmost hH < lam := by linarith
  have hγ : ∀ i, μ + hH.eigenvalues rfl i = 0 → ⟪hH.eigenvectorBasis rfl i, g⟫ = 0 :=
    fun i hi => Submodule.inner_right_of_mem_orthogonal (eigenvectorBasis_mem_ker hi) hcons
  have hd : ∀ i, 0 ≤ μ + hH.eigenvalues rfl i := fun i => by
    have := leftmost_le_eigenvalues (hH := hH) i; linarith
  obtain ⟨i, hi⟩ : ∃ i, ⟪hH.eigenvectorBasis rfl i, g⟫ ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (eq_of_inner_eigenvectorBasis (hH := hH) fun i => by rw [h i, inner_zero_right])
  rw [secular, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_eq_sum_eigenvectorBasis (hH := hH), inner_eq_sum_eigenvectorBasis (hH := hH)]
  simp only [inner_eigenvectorBasis_step hlam, inner_eigenvectorBasis_particular, ← sq]
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
  · rcases (hd j).eq_or_lt with h | h
    · rw [hγ j h.symm]; simp
    · exact div_sq_le_div_sq h (by linarith)
  · have hdi : 0 < μ + hH.eigenvalues rfl i :=
      (hd i).lt_of_ne fun h => hi (hγ i h.symm)
    exact div_sq_lt_div_sq (neg_ne_zero.2 hi) hdi (by linarith)

/-- Let $H$ be symmetric, let $g \neq 0$, let $\mu \ge -\lambda_1$, and let $s \in E$ satisfy
$(H + \mu I) s = -g$. Then $\pi(\lambda) < \|s\|^2$ for every $\lambda > \mu$. -/
theorem secular_lt_norm_sq_of_shifted (hg : g ≠ 0) {μ lam : ℝ} {s : E}
    (hμ : -leftmost hH ≤ μ) (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hlt : μ < lam) :
    secular g H lam < ‖s‖ ^ 2 := by
  obtain ⟨hcons, -, -, hle, -⟩ := particular_add_of_shifted (hH := hH) hs
  exact (secular_lt_norm_particular_sq hg hμ hlt hcons).trans_le
    (pow_le_pow_left₀ (norm_nonneg _) hle 2)

end Shifted

/-!
### The root of the secular equation

This section proves Lemma 8.2.1 of [cartis2022evaluation].
-/

section Root

/-- **Root of the secular equation.** Let $H$ be symmetric and $g \in E$. Let
$\tau : \mathbb{R} \to \mathbb{R}$ be continuous, monotone and nonnegative on
$(\lambda_s, \infty)$, and not identically zero there. Suppose that
$\tau(\lambda) < \pi(\lambda)$ for all $\lambda > \lambda_s$ close enough to $\lambda_s$. Then
there is a unique $\lambda_* > \lambda_s$ with
$$\pi(\lambda_*) = \tau(\lambda_*).$$
Moreover $\tau(\lambda) < \pi(\lambda)$ for $\lambda \in (\lambda_s, \lambda_*)$, and
$\pi(\lambda) < \tau(\lambda)$ for $\lambda > \lambda_*$.

This is Lemma 8.2.1 of [cartis2022evaluation]. The hypothesis on $\tau$ near $\lambda_s$ is the
condition $\pi(\lambda_s) > \tau(\lambda_s)$ of the source, with $\pi(\lambda_s)$ read as the
right limit of $\pi$ at $\lambda_s$, which can be $+\infty$ (see
`Subproblem.tendsto_step_threshold`). It is stated with the filter `𝓝[>] (shiftThreshold hH)`. -/
theorem existsUnique_secular_root {τ : ℝ → ℝ} (hτc : ContinuousOn τ (Ioi (shiftThreshold hH)))
    (hτm : MonotoneOn τ (Ioi (shiftThreshold hH)))
    (hτ0 : ∀ lam ∈ Ioi (shiftThreshold hH), 0 ≤ τ lam)
    (hτne : ∃ lam ∈ Ioi (shiftThreshold hH), τ lam ≠ 0)
    (hleft : ∀ᶠ lam in 𝓝[>] (shiftThreshold hH), τ lam < secular g H lam) :
    ∃ lamStar, shiftThreshold hH < lamStar ∧ secular g H lamStar = τ lamStar ∧
      (∀ lam ∈ Ioo (shiftThreshold hH) lamStar, τ lam < secular g H lam) ∧
      (∀ lam ∈ Ioi lamStar, secular g H lam < τ lam) ∧
      ∀ lam, shiftThreshold hH < lam → secular g H lam = τ lam → lam = lamStar := by
  set ls := shiftThreshold hH
  obtain ⟨a, ⟨hτa, has⟩⟩ := (hleft.and self_mem_nhdsWithin).exists
  have has : ls < a := has
  have hg : g ≠ 0 := by
    rintro rfl
    rw [secular_zero_left] at hτa
    exact (hτ0 a has).not_gt hτa
  -- `Ψ = π - τ` is strictly decreasing and continuous on `(λₛ, ∞)`
  have hsub := Ioi_shiftThreshold_subset (hH := hH)
  obtain ⟨-, hπc, hπa, -, hπ0, -⟩ := secular_shape (hH := hH) hg 1
  have hΨ : StrictAntiOn (fun lam => secular g H lam - τ lam) (Ioi ls) := fun x hx y hy hxy => by
    have := hπa (hsub hx) (hsub hy) hxy
    have := hτm hx hy hxy.le
    simp only; linarith
  have hΨc : ContinuousOn (fun lam => secular g H lam - τ lam) (Ioi ls) :=
    (hπc.mono hsub).sub hτc
  -- a point where `Ψ < 0`
  obtain ⟨c, hcs, hτc0⟩ := hτne
  have hτcpos : 0 < τ c := (hτ0 c hcs).lt_of_ne' hτc0
  obtain ⟨b, hb⟩ := (eventually_ge_atTop (max a c) |>.and
    (hπ0.eventually (gt_mem_nhds hτcpos))).exists
  have hab : a ≤ b := (le_max_left _ _).trans hb.1
  have hcb : c ≤ b := (le_max_right _ _).trans hb.1
  have hbs : ls < b := has.trans_le hab
  have hΨb : secular g H b - τ b < 0 := by have := hτm hcs hbs hcb; linarith [hb.2]
  have hΨa : 0 < secular g H a - τ a := by linarith
  obtain ⟨lamStar, hmem, hroot⟩ := intermediate_value_Icc' hab
    (hΨc.mono fun x hx => has.trans_le hx.1) ⟨hΨb.le, hΨa.le⟩
  have hls : ls < lamStar := has.trans_le hmem.1
  simp only at hroot
  refine ⟨lamStar, hls, by linarith, fun lam hlam => ?_, fun lam hlam => ?_, fun lam hlam h => ?_⟩
  · have := hΨ hlam.1 hls hlam.2; simp only at this; linarith
  · have := hΨ hls (hls.trans hlam) hlam; simp only at this; linarith
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hΨ hlam hls hlt; simp only at this; linarith
    · have := hΨ hls hlam hlt; simp only at this; linarith

/-- Let $H$ be symmetric, and suppose that $g$ is orthogonal to $\ker(H + \lambda_s I)$. Let $p$ be
the minimum-norm solution `Subproblem.particular` of $(H + \lambda_s I) x = -g$. Then
$$\pi(\lambda) \to \|p\|^2 \quad \text{as } \lambda \downarrow \lambda_s.$$

At $\lambda_s = -\lambda_1$ this is `Subproblem.tendsto_step_threshold`. For
$\lambda_s > -\lambda_1$ it is the continuity of $\pi$ at $\lambda_s$, where $p = s(\lambda_s)$. -/
theorem tendsto_secular_shiftThreshold
    (hg : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ) :
    Tendsto (secular g H) (𝓝[>] (shiftThreshold hH))
      (𝓝 (‖particular hH g (shiftThreshold hH)‖ ^ 2)) := by
  rcases neg_leftmost_le_shiftThreshold (hH := hH).eq_or_lt with h | h
  · rw [← h] at hg ⊢
    exact ((tendsto_step_threshold (hH := hH) (g := g)).1 hg).2
  · have hc : ContinuousAt (secularSum (hH.eigenvalues rfl) (secularWeight hH g))
        (shiftThreshold hH) :=
      continuousOn_secularSum.continuousAt (secularDomain_mem_nhds (mem_secularDomain_of_lt h))
    have hc' : ContinuousAt (secular g H) (shiftThreshold hH) :=
      hc.congr (secular_eventuallyEq h).symm
    rw [(particular_spec (hH := hH) (g := g) _).2.2 h]
    exact hc'.tendsto.mono_left nhdsWithin_le_nhds

/-- Let $H$ be symmetric, and suppose that $g$ is not orthogonal to $\ker(H + \lambda_s I)$. Then
$$\pi(\lambda) \to +\infty \quad \text{as } \lambda \downarrow \lambda_s.$$

This case occurs only when $\lambda_s = -\lambda_1$, because for $\lambda_s > -\lambda_1$ the
operator $H + \lambda_s I$ is invertible. -/
theorem tendsto_secular_shiftThreshold_atTop
    (hg : g ∉ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ) :
    Tendsto (secular g H) (𝓝[>] (shiftThreshold hH)) atTop := by
  rcases neg_leftmost_le_shiftThreshold (hH := hH).eq_or_lt with h | h
  · rw [← h] at hg ⊢
    exact (tendsto_step_threshold (hH := hH) (g := g)).2 hg
  · exfalso
    refine hg ((Submodule.mem_orthogonal' _ _).2 fun v hv => ?_)
    have hv0 : v = 0 := by
      refine injective_add_smul (hH := hH) h ?_
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
      rw [hv, map_zero]
    rw [hv0, inner_zero_right]

/-- **Root of the secular equation, with the hypothesis of the source.** Let $H$ be symmetric and
$g \in E$. Let $\tau : \mathbb{R} \to \mathbb{R}$ be continuous on $[\lambda_s, \infty)$,
monotone and nonnegative on $(\lambda_s, \infty)$, and not identically zero there. Let $p$ be
the minimum-norm solution `Subproblem.particular` of $(H + \lambda_s I) x = -g$, and suppose
that $\tau(\lambda_s) < \|p\|^2$ if $g$ is orthogonal to $\ker(H + \lambda_s I)$. Then there is
a unique $\lambda_* > \lambda_s$ with
$$\pi(\lambda_*) = \tau(\lambda_*).$$
Moreover $\tau(\lambda) < \pi(\lambda)$ for $\lambda \in (\lambda_s, \lambda_*)$, and
$\pi(\lambda) < \tau(\lambda)$ for $\lambda > \lambda_*$.

This is Lemma 8.2.1 of [cartis2022evaluation] with its hypothesis
$\pi(\lambda_s) > \tau(\lambda_s)$. Here $\pi(\lambda_s)$ is the right limit of $\pi$ at
$\lambda_s$. This limit is $\|p\|^2$ if the system at $\lambda_s$ is consistent, and then
$p = s(\lambda_s)$ when $\lambda_s > -\lambda_1$; otherwise the limit is $+\infty$
(`Subproblem.tendsto_secular_shiftThreshold`,
`Subproblem.tendsto_secular_shiftThreshold_atTop`). So the hypothesis of the source is the
implication above. -/
theorem existsUnique_secular_root_of_lt {τ : ℝ → ℝ}
    (hτc : ContinuousOn τ (Ici (shiftThreshold hH)))
    (hτm : MonotoneOn τ (Ioi (shiftThreshold hH)))
    (hτ0 : ∀ lam ∈ Ioi (shiftThreshold hH), 0 ≤ τ lam)
    (hτne : ∃ lam ∈ Ioi (shiftThreshold hH), τ lam ≠ 0)
    (hπ : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      τ (shiftThreshold hH) < ‖particular hH g (shiftThreshold hH)‖ ^ 2) :
    ∃ lamStar, shiftThreshold hH < lamStar ∧ secular g H lamStar = τ lamStar ∧
      (∀ lam ∈ Ioo (shiftThreshold hH) lamStar, τ lam < secular g H lam) ∧
      (∀ lam ∈ Ioi lamStar, secular g H lam < τ lam) ∧
      ∀ lam, shiftThreshold hH < lam → secular g H lam = τ lam → lam = lamStar := by
  have hτt : Tendsto τ (𝓝[>] (shiftThreshold hH)) (𝓝 (τ (shiftThreshold hH))) :=
    ((hτc (shiftThreshold hH) self_mem_Ici).mono Ioi_subset_Ici_self).tendsto
  refine existsUnique_secular_root (hτc.mono Ioi_subset_Ici_self) hτm hτ0 hτne ?_
  by_cases hg : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ
  · exact hτt.eventually_lt (tendsto_secular_shiftThreshold hg) (hπ hg)
  · filter_upwards [hτt.eventually (gt_mem_nhds (lt_add_one (τ (shiftThreshold hH)))),
      (tendsto_secular_shiftThreshold_atTop hg).eventually_gt_atTop (τ (shiftThreshold hH) + 1)]
      with lam h1 h2
    exact h1.trans h2

end Root

/-! ### The multiplier versus the secular function, for an abstract target -/

section Abstract

variable {τ : ℝ → ℝ} {μ : ℝ} {s : E}

/-- **Location of the multiplier, for an abstract target.** Let $H$ be symmetric and $g \in E$. Let
$\tau : \mathbb{R} \to \mathbb{R}$ be monotone on $[\lambda_s, \infty)$ and positive on
$(\lambda_s, \infty)$. Let $\mu \ge \lambda_s$ and let $s \in E$ satisfy $(H + \mu I) s = -g$
and $\|s\|^2 \le \tau(\mu)$, with $\|s\|^2 = \tau(\mu)$ when $\mu > \lambda_s$. Then for every
$\lambda > \lambda_s$
$$\tau(\lambda) \le \pi(\lambda) \iff \lambda \le \mu.$$

The equality case is stated as $\tau(\mu) \le \|s\|^2$ when $\mu > \lambda_s$. -/
theorem le_secular_iff_of_shifted (hτ : MonotoneOn τ (Ici (shiftThreshold hH)))
    (hτpos : ∀ lam, shiftThreshold hH < lam → 0 < τ lam) (hμ : shiftThreshold hH ≤ μ)
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hsτ : ‖s‖ ^ 2 ≤ τ μ)
    (heq : shiftThreshold hH < μ → τ μ ≤ ‖s‖ ^ 2) {lam : ℝ} (hlam : shiftThreshold hH < lam) :
    τ lam ≤ secular g H lam ↔ lam ≤ μ := by
  have hμ1 : -leftmost hH ≤ μ := neg_leftmost_le_shiftThreshold.trans hμ
  have hlam1 : -leftmost hH < lam := neg_leftmost_le_shiftThreshold.trans_lt hlam
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hlt' : secular g H lam < τ lam := by
      rcases eq_or_ne g 0 with rfl | hg
      · rw [secular_zero_left]; exact hτpos lam hlam
      · calc secular g H lam < ‖s‖ ^ 2 := secular_lt_norm_sq_of_shifted hg hμ1 hs hlt
          _ ≤ τ μ := hsτ
          _ ≤ τ lam := hτ hμ (hμ.trans hlt.le) hlt.le
    linarith
  · intro hle
    have hμs : shiftThreshold hH < μ := hlam.trans_le hle
    have hstep := (particular_add_of_shifted (hH := hH) hs).2.2.2.2
      (neg_leftmost_le_shiftThreshold.trans_lt hμs)
    calc τ lam ≤ τ μ := hτ hlam.le hμ hle
      _ ≤ ‖s‖ ^ 2 := heq hμs
      _ = secular g H μ := by rw [secular, hstep]
      _ ≤ secular g H lam := secular_antitoneOn hlam1 (hlam1.trans_le hle) hle

/-- **Classification into the easy and hard cases, for an abstract target.** Assume the hypotheses
of `Subproblem.le_secular_iff_of_shifted`: $H$ is symmetric, $\tau$ is monotone on
$[\lambda_s, \infty)$ and positive on $(\lambda_s, \infty)$, $\mu \ge \lambda_s$,
$(H + \mu I) s = -g$, $\|s\|^2 \le \tau(\mu)$, and $\|s\|^2 = \tau(\mu)$ when $\mu > \lambda_s$.
Let $s_s$ be the minimum-norm solution `Subproblem.particular` of $(H + \lambda_s I) x = -g$.
Then:
* $\mu = \lambda_s$ if and only if $g$ is orthogonal to $\ker(H + \lambda_s I)$ and
  $\|s_s\|^2 \le \tau(\lambda_s)$ (the interior and hard cases);
* if $\mu > \lambda_s$ (the easy case), then $s = s(\mu)$. -/
theorem multiplier_classification (hτ : MonotoneOn τ (Ici (shiftThreshold hH)))
    (hτpos : ∀ lam, shiftThreshold hH < lam → 0 < τ lam) (hμ : shiftThreshold hH ≤ μ)
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hsτ : ‖s‖ ^ 2 ≤ τ μ)
    (heq : shiftThreshold hH < μ → τ μ ≤ ‖s‖ ^ 2) :
    (μ = shiftThreshold hH ↔
      g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧
        ‖particular hH g (shiftThreshold hH)‖ ^ 2 ≤ τ (shiftThreshold hH)) ∧
    (shiftThreshold hH < μ → s = step g H μ) := by
  refine ⟨⟨?_, fun ⟨hcons, hnorm⟩ => ?_⟩, fun hμs => ?_⟩
  · rintro rfl
    obtain ⟨hcons, -, -, hle, -⟩ := particular_add_of_shifted (hH := hH) hs
    exact ⟨hcons, (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans hsτ⟩
  · by_contra hne
    have hμs : shiftThreshold hH < μ := hμ.lt_of_ne (Ne.symm hne)
    have hstep := (particular_add_of_shifted (hH := hH) hs).2.2.2.2
      (neg_leftmost_le_shiftThreshold.trans_lt hμs)
    have h1 : τ μ ≤ secular g H μ := by rw [secular, ← hstep]; exact heq hμs
    rcases eq_or_ne g 0 with rfl | hg
    · rw [secular_zero_left] at h1
      exact (hτpos μ hμs).not_ge h1
    · have := secular_lt_norm_particular_sq hg neg_leftmost_le_shiftThreshold hμs hcons
      have := hτ (mem_Ici.2 le_rfl) hμ hμs.le
      linarith
  · exact (particular_add_of_shifted (hH := hH) hs).2.2.2.2
      (neg_leftmost_le_shiftThreshold.trans_lt hμs)

end Abstract

/-! ### The trust-region subproblem -/

section TrustRegion

variable {Δ μ : ℝ} {s : E}

/-- **Trust-region multipliers lie at or to the right of the threshold.** Let $H$ be symmetric, and
let $\mu$ be a trust-region multiplier for the step $s$ and the radius $\Delta$
(`Subproblem.IsTrustRegionMultiplier`). Let $p$ be the minimum-norm solution
`Subproblem.particular` of $(H + \mu I) x = -g$. Then:
* $\lambda_s \le \mu$;
* $s - p$ lies in $\ker(H + \mu I)$ and $\langle g, s - p \rangle = 0$;
* if $\mu > -\lambda_1$, then $s = p = s(\mu)$.

This is Corollary 8.3.2 and (8.3.1)–(8.3.2) of [cartis2022evaluation]. The step $s$ need not be
feasible. -/
theorem shiftThreshold_le_of_isTrustRegionMultiplier (h : IsTrustRegionMultiplier g H Δ s μ) :
    shiftThreshold hH ≤ μ ∧
      s - particular hH g μ ∈ LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) ∧
      ⟪g, s - particular hH g μ⟫ = 0 ∧
      (-leftmost hH < μ → s = particular hH g μ ∧ s = step g H μ) := by
  obtain ⟨-, hker, horth, -, hstep⟩ := particular_add_of_shifted (hH := hH) h.shifted
  refine ⟨shiftThreshold_le_of_isPositive h.nonneg h.isPositive, hker, horth, fun hμ => ?_⟩
  rw [(particular_spec (hH := hH) (g := g) μ).2.2 hμ]
  exact ⟨hstep hμ, hstep hμ⟩

/-- Let $H$ be symmetric, and let $\mu$ be a trust-region multiplier for a feasible step $s$,
$\|s\| \le \Delta$. Then $\|s\|^2 \le \Delta^2$, with $\|s\|^2 = \Delta^2$ when
$\mu > \lambda_s$. -/
theorem IsTrustRegionMultiplier.norm_sq_le (h : IsTrustRegionMultiplier g H Δ s μ)
    (hs : ‖s‖ ≤ Δ) : ‖s‖ ^ 2 ≤ Δ ^ 2 ∧ (shiftThreshold hH < μ → ‖s‖ ^ 2 = Δ ^ 2) :=
  ⟨pow_le_pow_left₀ (norm_nonneg _) hs 2, fun hμ => by
    rw [h.norm_eq_of_pos (shiftThreshold_nonneg.trans_lt hμ)]⟩

/-- **The sets $\mathcal{L}$ and $\mathcal{G}$ of the trust-region subproblem.** Let $H$ be
symmetric and $\Delta > 0$, and let $s$ be a feasible step, $\|s\| \le \Delta$, with
trust-region multiplier $\mu$. Then for every $\lambda > \lambda_s$
$$\Delta^2 \le \pi(\lambda) \iff \lambda \le \mu.$$
So $(\lambda_s, \infty)$ splits into $\mathcal{L} = (\lambda_s, \mu]$, where
$\|s(\lambda)\| \ge \Delta$, and $\mathcal{G} = (\mu, \infty)$, where $\|s(\lambda)\| < \Delta$.

This is the partition of Section 8.3.2 of [cartis2022evaluation]. A feasible step with a
trust-region multiplier is the same as a global minimizer, by
`Subproblem.isMinOn_closedBall_iff`. -/
theorem le_secular_iff_of_trustRegion (hΔ : 0 < Δ) (h : IsTrustRegionMultiplier g H Δ s μ)
    (hs : ‖s‖ ≤ Δ) {lam : ℝ} (hlam : shiftThreshold hH < lam) :
    Δ ^ 2 ≤ secular g H lam ↔ lam ≤ μ :=
  le_secular_iff_of_shifted (τ := fun _ => Δ ^ 2) (fun _ _ _ _ _ => le_rfl)
    (fun _ _ => by positivity) (shiftThreshold_le_of_isTrustRegionMultiplier h).1 h.shifted
    (h.norm_sq_le (hH := hH) hs).1 (fun hμ => ((h.norm_sq_le (hH := hH) hs).2 hμ).ge) hlam

/-- Let $H$ be symmetric, and let $\mu$ be a trust-region multiplier for the step $s$ and the radius
$\Delta$. In the easy case $\mu > \lambda_s$, $\mu$ is a root of the secular equation:
$$\pi(\mu) = \Delta^2.$$

This is in Section 8.3.2 of [cartis2022evaluation]. By
`Subproblem.le_secular_iff_of_trustRegion`, $\mu$ is the only root in $(\lambda_s, \infty)$. -/
theorem secular_eq_of_trustRegion (h : IsTrustRegionMultiplier g H Δ s μ)
    (hμ : shiftThreshold hH < μ) : secular g H μ = Δ ^ 2 := by
  have hstep := ((shiftThreshold_le_of_isTrustRegionMultiplier (hH := hH) h).2.2.2
    (neg_leftmost_le_shiftThreshold.trans_lt hμ)).2
  rw [secular, ← hstep, h.norm_eq_of_pos (shiftThreshold_nonneg.trans_lt hμ)]

/-- **Classification into the easy and hard cases for the trust-region subproblem.** Let $H$ be
symmetric and $\Delta > 0$, and let $s$ be a feasible step, $\|s\| \le \Delta$, with
trust-region multiplier $\mu$. Let $s_s$ be the minimum-norm solution `Subproblem.particular` of
$(H + \lambda_s I) x = -g$. Then:
* $\mu = \lambda_s$ if and only if $g$ is orthogonal to $\ker(H + \lambda_s I)$ and
  $\|s_s\| \le \Delta$;
* if $\mu > \lambda_s$, then $s = s(\mu)$.

This is Section 8.3.2 and Corollary 8.3.2 of [cartis2022evaluation]. For $\lambda_1 \ge 0$, so
$\lambda_s = 0$, the first case is the interior case $g \in \operatorname{range} H$ and
$\|H^+ g\| \le \Delta$. For $\lambda_1 < 0$ it is the hard case. -/
theorem multiplier_classification_of_trustRegion (hΔ : 0 < Δ)
    (h : IsTrustRegionMultiplier g H Δ s μ) (hs : ‖s‖ ≤ Δ) :
    (μ = shiftThreshold hH ↔
      g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧
        ‖particular hH g (shiftThreshold hH)‖ ≤ Δ) ∧
    (shiftThreshold hH < μ → s = step g H μ) := by
  have := multiplier_classification (τ := fun _ => Δ ^ 2) (fun _ _ _ _ _ => le_rfl)
    (fun _ _ => by positivity) (shiftThreshold_le_of_isTrustRegionMultiplier (hH := hH) h).1
    h.shifted (h.norm_sq_le (hH := hH) hs).1 fun hμ => ((h.norm_sq_le (hH := hH) hs).2 hμ).ge
  refine ⟨this.1.trans (and_congr_right fun _ => ?_), this.2⟩
  exact pow_le_pow_iff_left₀ (norm_nonneg _) hΔ.le two_ne_zero

/-- **Hard-case solutions of the trust-region subproblem are global minimizers.** Let $H$ be
symmetric, let $\mu \ge 0$ with $\mu \ge -\lambda_1$, and suppose that $g$ is orthogonal to
$\ker(H + \mu I)$. Let $p$ be the minimum-norm solution `Subproblem.particular` of
$(H + \mu I) x = -g$, and let $w \in \ker(H + \mu I)$. If $\|p + w\| \le \Delta$, and
$\|p + w\| = \Delta$ or $\mu = 0$, then $p + w$ lies in the ball $\{u : \|u\| \le \Delta\}$ and
minimizes the quadratic model $m$ on this ball.

This is the sufficiency part of Section 8.3.2 of [cartis2022evaluation]. -/
theorem isMinOn_closedBall_of_hardCase {w : E} (hμ0 : 0 ≤ μ) (hμ : -leftmost hH ≤ μ)
    (hg : g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ)
    (hw : w ∈ LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))
    (hΔ : ‖particular hH g μ + w‖ ≤ Δ) (hact : μ = 0 ∨ ‖particular hH g μ + w‖ = Δ) :
    particular hH g μ + w ∈ Metric.closedBall (0 : E) Δ ∧
      IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) (particular hH g μ + w) := by
  obtain ⟨-, hiff, -, -⟩ := (particular_spec (hH := hH) (g := g) μ).2.1 hg
  have hsol : (H + μ • (1 : E →L[ℝ] E)) (particular hH g μ + w) = -g :=
    (hiff _).2 (by rwa [add_sub_cancel_left])
  refine IsTrustRegionMultiplier.isMinOn_of_norm_le hH
    ⟨hμ0, hsol, isPositive_add_smul_of_le hμ, ?_⟩ hΔ
  rcases hact with h | h
  · rw [h, zero_mul]
  · rw [h, sub_self, mul_zero]

/-- **Optimal value of the trust-region subproblem.** Let $H$ be symmetric, and let $\mu$ be a
trust-region multiplier for the step $s$ and the radius $\Delta$. Let $p$ be the minimum-norm
solution `Subproblem.particular` of $(H + \mu I) x = -g$. Then
$$m(s) = \tfrac12 \left(\langle g, p \rangle - \mu \Delta^2\right).$$

This is (8.3.5) of [cartis2022evaluation]. -/
theorem optimalValue_eq_of_trustRegion (h : IsTrustRegionMultiplier g H Δ s μ) :
    quadModel g H s = (1 / 2) * (⟪g, particular hH g μ⟫ - μ * Δ ^ 2) := by
  obtain ⟨-, -, horth, -, -⟩ := particular_add_of_shifted (hH := hH) h.shifted
  have hg : ⟪g, s⟫ = ⟪g, particular hH g μ⟫ := by
    rw [inner_sub_right, sub_eq_zero] at horth; exact horth
  have hc : μ * ‖s‖ ^ 2 = μ * Δ ^ 2 := by
    have := h.complementarity
    have h2 : μ * ‖s‖ = μ * Δ := by linarith [show μ * (‖s‖ - Δ) = μ * ‖s‖ - μ * Δ by ring]
    calc μ * ‖s‖ ^ 2 = (μ * ‖s‖) * ‖s‖ := by ring
      _ = (μ * Δ) * ‖s‖ := by rw [h2]
      _ = Δ * (μ * ‖s‖) := by ring
      _ = μ * Δ ^ 2 := by rw [h2]; ring
  rw [quadModel_eq_of_shifted h.shifted, hg, hc]

end TrustRegion

/-! ### The regularization subproblem -/

section Regularization

variable {σ r : ℝ} {s : E}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $\sigma > 0$ and $r > 2$. For every vector $s$ of a normed space, the regularization target
$\tau(\lambda) = (\lambda / \sigma)^{2/(r-2)}$ of (8.2.9) of [cartis2022evaluation], at the
multiplier $\lambda = \sigma \|s\|^{r-2}$, is $\|s\|^2$:
$$\|s\|^2 = \left(\frac{\sigma \|s\|^{r-2}}{\sigma}\right)^{2/(r-2)}.$$
-/
theorem norm_sq_eq_rpow (hσ : 0 < σ) (hr : 2 < r) (s : E) :
    ‖s‖ ^ 2 = (σ * ‖s‖ ^ (r - 2) / σ) ^ (2 / (r - 2)) := by
  rw [mul_div_cancel_left₀ _ hσ.ne', ← Real.rpow_mul (norm_nonneg _),
    mul_div_cancel₀ _ (by linarith : r - 2 ≠ 0)]
  norm_cast

/-- For $\sigma > 0$ and $r > 2$, the regularization target
$\lambda \mapsto (\lambda / \sigma)^{2/(r-2)}$ is monotone on $[0, \infty)$. -/
theorem monotoneOn_regTarget (hσ : 0 < σ) (hr : 2 < r) :
    MonotoneOn (fun lam : ℝ => (lam / σ) ^ (2 / (r - 2))) (Ici 0) := fun x hx y _ hxy =>
  Real.rpow_le_rpow (div_nonneg hx hσ.le) (div_le_div_of_nonneg_right hxy hσ.le)
    (div_nonneg zero_le_two (by linarith))

/-- **Regularization multipliers lie at or to the right of the threshold.** Let $H$ be symmetric,
$\sigma > 0$ and $r > 2$, and let $s$ be a global minimizer of the regularized model $m^R$ on
$E$. Put $\mu = \sigma \|s\|^{r-2}$, and let $p$ be the minimum-norm solution
`Subproblem.particular` of $(H + \mu I) x = -g$. Then:
* $\lambda_s \le \mu$;
* $s - p$ lies in $\ker(H + \mu I)$ and $\langle g, s - p \rangle = 0$;
* if $\mu > -\lambda_1$, then $s = p = s(\mu)$.

This is Corollary 8.3.1 and (8.3.1)–(8.3.2) of [cartis2022evaluation]. -/
theorem shiftThreshold_le_of_isMinOn_regModel (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) :
    shiftThreshold hH ≤ σ * ‖s‖ ^ (r - 2) ∧
      s - particular hH g (σ * ‖s‖ ^ (r - 2)) ∈
        LinearMap.ker ((H + (σ * ‖s‖ ^ (r - 2)) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) ∧
      ⟪g, s - particular hH g (σ * ‖s‖ ^ (r - 2))⟫ = 0 ∧
      (-leftmost hH < σ * ‖s‖ ^ (r - 2) →
        s = particular hH g (σ * ‖s‖ ^ (r - 2)) ∧ s = step g H (σ * ‖s‖ ^ (r - 2))) := by
  obtain ⟨hshift, hpos⟩ := (isMinOn_regModel_iff hH hσ hr).1 hmin
  obtain ⟨-, hker, horth, -, hstep⟩ := particular_add_of_shifted (hH := hH) hshift
  refine ⟨shiftThreshold_le_of_isPositive (by positivity) hpos, hker, horth, fun hμ => ?_⟩
  rw [(particular_spec (hH := hH) (g := g) _).2.2 hμ]
  exact ⟨hstep hμ, hstep hμ⟩

/-- **The sets $\mathcal{L}$ and $\mathcal{G}$ of the regularization subproblem.** Let $H$ be
symmetric, $\sigma > 0$ and $r > 2$, let $s$ be a global minimizer of the regularized model
$m^R$ on $E$, and put $\mu = \sigma \|s\|^{r-2}$. Then for every $\lambda > \lambda_s$
$$\left(\frac{\lambda}{\sigma}\right)^{2/(r-2)} \le \pi(\lambda) \iff \lambda \le \mu.$$
So $(\lambda_s, \infty)$ splits into $\mathcal{L} = (\lambda_s, \mu]$, where $\|s(\lambda)\| \ge
(\lambda / \sigma)^{1/(r-2)}$, and $\mathcal{G} = (\mu, \infty)$.

This is the partition of Section 8.3.1 of [cartis2022evaluation]. -/
theorem le_secular_iff_of_regularization (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) {lam : ℝ} (hlam : shiftThreshold hH < lam) :
    (lam / σ) ^ (2 / (r - 2)) ≤ secular g H lam ↔ lam ≤ σ * ‖s‖ ^ (r - 2) :=
  le_secular_iff_of_shifted (τ := fun lam => (lam / σ) ^ (2 / (r - 2)))
    ((monotoneOn_regTarget hσ hr).mono fun _ hx => shiftThreshold_nonneg.trans hx)
    (fun _ hl => Real.rpow_pos_of_pos (div_pos (shiftThreshold_nonneg.trans_lt hl) hσ) _)
    (shiftThreshold_le_of_isMinOn_regModel (hH := hH) hσ hr hmin).1
    ((isMinOn_regModel_iff hH hσ hr).1 hmin).1 (norm_sq_eq_rpow hσ hr s).le
    (fun _ => (norm_sq_eq_rpow hσ hr s).ge) hlam

/-- Let $H$ be symmetric, $\sigma > 0$ and $r > 2$, let $s$ be a global minimizer of the regularized
model $m^R$ on $E$, and put $\mu = \sigma \|s\|^{r-2}$. In the easy case $\mu > \lambda_s$,
$\mu$ is a root of the secular equation:
$$\pi(\mu) = \left(\frac{\mu}{\sigma}\right)^{2/(r-2)}.$$

This is (8.2.42) and Section 8.3.1 of [cartis2022evaluation]. By
`Subproblem.le_secular_iff_of_regularization`, $\mu$ is the only root in $(\lambda_s, \infty)$. -/
theorem secular_eq_of_regularization (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) (hμ : shiftThreshold hH < σ * ‖s‖ ^ (r - 2)) :
    secular g H (σ * ‖s‖ ^ (r - 2)) = (σ * ‖s‖ ^ (r - 2) / σ) ^ (2 / (r - 2)) := by
  have hstep := ((shiftThreshold_le_of_isMinOn_regModel (hH := hH) hσ hr hmin).2.2.2
    (neg_leftmost_le_shiftThreshold.trans_lt hμ)).2
  rw [secular, ← hstep, norm_sq_eq_rpow hσ hr s]

/-- **Classification into the easy and hard cases for the regularization subproblem.** Let $H$ be
symmetric, $\sigma > 0$ and $r > 2$, let $s$ be a global minimizer of the regularized model
$m^R$ on $E$, and put $\mu = \sigma \|s\|^{r-2}$. Let $s_s$ be the minimum-norm solution
`Subproblem.particular` of $(H + \lambda_s I) x = -g$. Then:
* $\mu = \lambda_s$ if and only if $g$ is orthogonal to $\ker(H + \lambda_s I)$ and
  $\|s_s\|^2 \le (\lambda_s / \sigma)^{2/(r-2)}$;
* if $\mu > \lambda_s$, then $s = s(\mu)$.

This is Section 8.3.1 and Corollary 8.3.1 of [cartis2022evaluation]. For $\lambda_1 \ge 0$, so
$\lambda_s = 0$, the first case says $g = 0$. For $\lambda_1 < 0$ it is the hard case. -/
theorem multiplier_classification_of_regularization (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) :
    (σ * ‖s‖ ^ (r - 2) = shiftThreshold hH ↔
      g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧
        ‖particular hH g (shiftThreshold hH)‖ ^ 2 ≤ (shiftThreshold hH / σ) ^ (2 / (r - 2))) ∧
    (shiftThreshold hH < σ * ‖s‖ ^ (r - 2) → s = step g H (σ * ‖s‖ ^ (r - 2))) :=
  multiplier_classification (τ := fun lam => (lam / σ) ^ (2 / (r - 2)))
    ((monotoneOn_regTarget hσ hr).mono fun _ hx => shiftThreshold_nonneg.trans hx)
    (fun _ hl => Real.rpow_pos_of_pos (div_pos (shiftThreshold_nonneg.trans_lt hl) hσ) _)
    (shiftThreshold_le_of_isMinOn_regModel (hH := hH) hσ hr hmin).1
    ((isMinOn_regModel_iff hH hσ hr).1 hmin).1 (norm_sq_eq_rpow hσ hr s).le
    fun _ => (norm_sq_eq_rpow hσ hr s).ge

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $\sigma > 0$, $r > 2$ and $\mu \ge 0$. If a vector $s$ of a normed space satisfies
$\|s\|^2 = (\mu / \sigma)^{2/(r-2)}$, then $\sigma \|s\|^{r-2} = \mu$. -/
theorem mul_norm_rpow_eq_of_norm_sq_eq (hσ : 0 < σ) (hr : 2 < r) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : ‖s‖ ^ 2 = (μ / σ) ^ (2 / (r - 2))) : σ * ‖s‖ ^ (r - 2) = μ := by
  have hr2 : r - 2 ≠ 0 := by linarith
  have h1 : ‖s‖ ^ (r - 2) = (‖s‖ ^ 2) ^ ((r - 2) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; congr 1; push_cast; ring
  have he : 2 / (r - 2) * ((r - 2) / 2) = 1 := by field_simp
  rw [h1, h, ← Real.rpow_mul (div_nonneg hμ hσ.le), he, Real.rpow_one, mul_div_cancel₀ _ hσ.ne']

/-- **Hard-case solutions of the regularization subproblem are global minimizers.** Let $H$ be
symmetric, $\sigma > 0$ and $r > 2$, let $\mu \ge 0$ with $\mu \ge -\lambda_1$, and suppose that
$g$ is orthogonal to $\ker(H + \mu I)$. Let $p$ be the minimum-norm solution
`Subproblem.particular` of $(H + \mu I) x = -g$, and let $w \in \ker(H + \mu I)$ with
$$\|p + w\|^2 = \left(\frac{\mu}{\sigma}\right)^{2/(r-2)}.$$
Then $p + w$ is a global minimizer of the regularized model $m^R$ on $E$.

This is the sufficiency part of Section 8.3.1 of [cartis2022evaluation]. -/
theorem isMinOn_regModel_of_hardCase (hσ : 0 < σ) (hr : 2 < r) {μ : ℝ} {w : E} (hμ0 : 0 ≤ μ)
    (hμ : -leftmost hH ≤ μ)
    (hg : g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ)
    (hw : w ∈ LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))
    (hnorm : ‖particular hH g μ + w‖ ^ 2 = (μ / σ) ^ (2 / (r - 2))) :
    IsMinOn (regModel g H σ r) univ (particular hH g μ + w) := by
  obtain ⟨-, hiff, -, -⟩ := (particular_spec (hH := hH) (g := g) μ).2.1 hg
  have hsol : (H + μ • (1 : E →L[ℝ] E)) (particular hH g μ + w) = -g :=
    (hiff _).2 (by rwa [add_sub_cancel_left])
  rw [isMinOn_regModel_iff hH hσ hr, mul_norm_rpow_eq_of_norm_sq_eq hσ hr hμ0 hnorm]
  exact ⟨hsol, isPositive_add_smul_of_le hμ⟩

/-- **Optimal value of the regularization subproblem.** Let $H$ be symmetric, $\sigma > 0$ and
$r > 2$, let $s$ be a global minimizer of the regularized model $m^R$ on $E$, and put
$\mu = \sigma \|s\|^{r-2}$. Let $p$ be the minimum-norm solution `Subproblem.particular` of
$(H + \mu I) x = -g$. Then
$$m^R(s) = \tfrac12 \left(\langle g, p \rangle - \frac{r - 2}{r} \mu
  \left(\frac{\mu}{\sigma}\right)^{2/(r-2)}\right).$$

This is (8.3.3) of [cartis2022evaluation]. -/
theorem optimalValue_eq_of_regularization (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) :
    regModel g H σ r s = (1 / 2) * (⟪g, particular hH g (σ * ‖s‖ ^ (r - 2))⟫ -
      ((r - 2) / r) * (σ * ‖s‖ ^ (r - 2)) * (σ * ‖s‖ ^ (r - 2) / σ) ^ (2 / (r - 2))) := by
  have hshift := ((isMinOn_regModel_iff hH hσ hr).1 hmin).1
  obtain ⟨-, -, horth, -, -⟩ := particular_add_of_shifted (hH := hH) hshift
  have hg : ⟪g, s⟫ = ⟪g, particular hH g (σ * ‖s‖ ^ (r - 2))⟫ := by
    rw [inner_sub_right, sub_eq_zero] at horth; exact horth
  rw [regModel_eq_of_shifted (by linarith) hshift, hg, ← norm_sq_eq_rpow hσ hr s]

end Regularization

/-! ### Existence of hard-case solutions -/

omit [FiniteDimensional ℝ E] in
/-- **The coefficients $\alpha$ of the hard case.** Let $E$ be a real inner product space, and let
$p, v \in E$ with $\langle p, v \rangle = 0$ and $v \neq 0$. Let $t \in \mathbb{R}$ with
$\|p\|^2 \le t$. Then there is $\alpha \in \mathbb{R}$ with
$$\|p + \alpha v\|^2 = t \quad \text{and} \quad \|p - \alpha v\|^2 = t.$$

The proof takes $\alpha = \sqrt{t - \|p\|^2} / \|v\|$. With $p = s_s$, the minimum-norm solution
`Subproblem.particular` at $-\lambda_1$, and an eigenvector $v = v_1$ for $\lambda_1$, which is
orthogonal to $s_s$ by `Subproblem.particular_spec`, this gives the hard-case solutions
$s_s + \alpha v_1$ of Section 8.3 of [cartis2022evaluation]. -/
theorem exists_norm_particular_add_smul_eq {p v : E} (hpv : ⟪p, v⟫ = 0) (hv : v ≠ 0) {t : ℝ}
    (ht : ‖p‖ ^ 2 ≤ t) :
    ∃ α : ℝ, ‖p + α • v‖ ^ 2 = t ∧ ‖p - α • v‖ ^ 2 = t := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have key : ∀ β : ℝ, ‖p + β • v‖ ^ 2 = ‖p‖ ^ 2 + β ^ 2 * ‖v‖ ^ 2 := fun β => by
    rw [norm_add_sq_real, inner_smul_right, hpv, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  set α := √(t - ‖p‖ ^ 2) / ‖v‖
  have hα : α ^ 2 * ‖v‖ ^ 2 = t - ‖p‖ ^ 2 := by
    rw [div_pow, Real.sq_sqrt (sub_nonneg.2 ht)]
    field_simp
  refine ⟨α, ?_, ?_⟩
  · rw [key, hα]; ring
  · rw [sub_eq_add_neg, ← neg_smul, key, neg_sq, hα]; ring

end Subproblem
