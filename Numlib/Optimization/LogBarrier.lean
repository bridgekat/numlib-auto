/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Boundary behavior of the logarithmic barrier

Let $\iota$ be a finite index set and $\mu \in \mathbb{R}$. The logarithmic barrier of the positive
orthant is the function $x \mapsto -\mu \sum_{i \in \iota} \log x_i$ on $\mathbb{R}^\iota$. This
file proves the facts about it that barrier methods use. The barrier is smooth on the open positive
orthant, with gradient and Hessian
$$\nabla(-\mu \textstyle\sum_i \log x_i)[d] = -\mu \sum_i \frac{d_i}{x_i}, \qquad \nabla^2(-\mu
  \textstyle\sum_i \log x_i)[d, e] = \mu \sum_i \frac{d_i e_i}{x_i^2}.$$
For $\mu > 0$ it tends to $+\infty$ along every bounded sequence of positive vectors whose distance
to the boundary of the nonnegative orthant tends to $0$. The distance of a positive vector to that
boundary is at most each of its coordinates, and a uniform lower bound $\varepsilon$ on the
coordinates bounds the Hessian by $|\mu| \, |\iota| / \varepsilon^2$.

## Main definitions

* `Optimization.logBarrier`: the barrier $x \mapsto -\mu \sum_i \log x_i$.
* `Optimization.nonnegativeOrthant`: the closed orthant $\{x \mid x_i \ge 0 \text{ for all } i\}$.

## Main results

* `Optimization.mem_frontier_nonnegativeOrthant`: a point is on the boundary of the nonnegative
  orthant if and only if all its coordinates are nonnegative and one of them is $0$.
* `Optimization.tendsto_logBarrier_of_bounded_of_infDist_frontier`: for $\mu > 0$ the barrier
  diverges to $+\infty$ along bounded positive sequences that approach the boundary.
* `Optimization.contDiffAt_logBarrier`: the barrier is smooth at every positive vector.
* `Optimization.fderiv_logBarrier_apply`, `Optimization.fderiv_fderiv_logBarrier_apply`: the first
  and second derivatives.
* `Optimization.norm_fderiv_fderiv_logBarrier_le`: the operator-norm bound on the Hessian.

## Implementation notes

* The barrier is defined on all of $\mathbb{R}^\iota$ with Mathlib's `Real.log`, which satisfies
  $\log 0 = 0$ and $\log(-t) = \log t$. Its values at vectors with a nonpositive coordinate have no
  meaning; all results assume positive coordinates where they need them.
* The distance to the boundary is `Metric.infDist x (frontier (Optimization.nonnegativeOrthant ι))`
  for the sup norm of `ι → ℝ`.
-/

open Filter Metric
open scoped BigOperators Topology ContDiff

namespace Optimization

variable {ι : Type*} [Fintype ι]

/-- The **logarithmic barrier** with weight $\mu \in \mathbb{R}$ is the function
$x \mapsto -\mu \sum_{i \in \iota} \log x_i$ on $\mathbb{R}^\iota$.

It is meant for vectors with positive coordinates. At other vectors the value follows Mathlib's
`Real.log`, with $\log 0 = 0$ and $\log(-t) = \log t$. -/
noncomputable def logBarrier (μ : ℝ) (x : ι → ℝ) : ℝ :=
  -μ * ∑ i, Real.log (x i)

/-- The **closed nonnegative orthant** $\{x \in \mathbb{R}^\iota \mid x_i \ge 0 \text{ for all } i
\in \iota\}$. -/
def nonnegativeOrthant (ι : Type*) : Set (ι → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ici 0

omit [Fintype ι] in
/-- Let $\iota$ be finite. A vector $x \in \mathbb{R}^\iota$ lies on the boundary of the nonnegative
orthant if and only if $x_i \ge 0$ for all $i$ and $x_i = 0$ for some $i$. -/
theorem mem_frontier_nonnegativeOrthant [Finite ι] {x : ι → ℝ} :
    x ∈ frontier (nonnegativeOrthant ι) ↔ (∀ i, 0 ≤ x i) ∧ ∃ i, x i = 0 := by
  classical
  have hclosed : IsClosed (nonnegativeOrthant ι) :=
    isClosed_set_pi fun _ _ ↦ isClosed_Ici
  rw [frontier, hclosed.closure_eq]
  unfold nonnegativeOrthant
  rw [interior_pi_set Set.finite_univ]
  simp only [Set.mem_sdiff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ici,
    interior_Ici, Set.mem_Ioi]
  constructor
  · rintro ⟨hn, hp⟩
    push Not at hp
    obtain ⟨i, hi⟩ := hp
    exact ⟨hn, i, le_antisymm hi (hn i)⟩
  · rintro ⟨hn, i, hi⟩
    exact ⟨hn, fun h ↦ (h i).ne' hi⟩

private theorem exists_coordinate_le_boundary_distance [Nonempty ι] {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) :
    ∃ i, x i ≤ infDist x (frontier (nonnegativeOrthant ι)) := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  have hfront : (frontier (nonnegativeOrthant ι)).Nonempty := by
    exact ⟨0, mem_frontier_nonnegativeOrthant.mpr ⟨fun _ ↦ le_rfl, i, rfl⟩⟩
  refine ⟨i, (le_infDist hfront).mpr fun y hy ↦ ?_⟩
  obtain ⟨-, j, hj⟩ := mem_frontier_nonnegativeOrthant.mp hy
  calc
    x i ≤ x j := hi j (Finset.mem_univ j)
    _ = dist (x j) (y j) := by rw [hj, Real.dist_eq, sub_zero, abs_of_pos (hx j)]
    _ ≤ dist x y := (dist_pi_le_iff dist_nonneg).mp le_rfl j

/-- Let $\iota$ be finite and nonempty, let $\mu > 0$ and $M \in \mathbb{R}$, and let $(x_n)$ be a
sequence in $\mathbb{R}^\iota$ with $0 < x_{n,i} \le M$ for all $n$ and $i$. If the distance
from $x_n$ to the boundary of the nonnegative orthant tends to $0$, then
$$-\mu \sum_{i \in \iota} \log x_{n,i} \to +\infty \qquad (n \to \infty).$$

The distance is `Metric.infDist` to `frontier (Optimization.nonnegativeOrthant ι)`. -/
theorem tendsto_logBarrier_of_bounded_of_infDist_frontier [Nonempty ι]
    {μ M : ℝ} (hμ : 0 < μ) {x : ℕ → ι → ℝ}
    (hx : ∀ n i, 0 < x n i) (hbounded : ∀ n i, x n i ≤ M)
    (ht : Tendsto (fun n ↦ infDist (x n) (frontier (nonnegativeOrthant ι))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ logBarrier μ (x n)) atTop atTop := by
  classical
  let d (n : ℕ) := infDist (x n) (frontier (nonnegativeOrthant ι))
  let B := (Fintype.card ι : ℝ) * max 0 (Real.log M)
  have hd (n : ℕ) : 0 < d n := by
    obtain ⟨i, hi⟩ := exists_coordinate_le_boundary_distance (hx n)
    exact (hx n i).trans_le hi
  have hlog : Tendsto (fun n ↦ Real.log (d n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp <| tendsto_nhdsWithin_iff.mpr
      ⟨ht, Eventually.of_forall hd⟩
  have hsum (n : ℕ) : (∑ i, Real.log (x n i)) ≤ Real.log (d n) + B := by
    obtain ⟨i, hi⟩ := exists_coordinate_le_boundary_distance (hx n)
    have hothers : (∑ j ∈ Finset.univ.erase i, Real.log (x n j)) ≤ B := by
      calc
        _ ≤ ∑ _ ∈ Finset.univ.erase i, max 0 (Real.log M) :=
          Finset.sum_le_sum fun j _ ↦
            (Real.log_le_log (hx n j) (hbounded n j)).trans (le_max_right _ _)
        _ ≤ B := by
          simp only [Finset.sum_const, nsmul_eq_mul, B]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _)
            (le_max_left _ _)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact add_le_add hothers (Real.log_le_log (hx n i) hi) |>.trans_eq (add_comm _ _)
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_atBot.mp hlog (-b / μ - B)] with n hn
  have hs : (∑ i, Real.log (x n i)) ≤ -b / μ := by linarith [hsum n]
  have hs' := (le_div_iff₀ hμ).mp hs
  unfold logBarrier
  nlinarith only [hs']

private def coordinate (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

private noncomputable def logBarrierFDeriv (μ : ℝ) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  (-μ) • ∑ i, (x i)⁻¹ • coordinate i

/-- Let $\mu \in \mathbb{R}$ and let $x \in \mathbb{R}^\iota$ have positive coordinates. Then the
logarithmic barrier $y \mapsto -\mu \sum_i \log y_i$ is $C^n$ at $x$ for every order $n$,
including $n = \infty$ and the analytic order $\omega$. -/
theorem contDiffAt_logBarrier (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i) {n : ℕ∞ω} :
    ContDiffAt ℝ n (logBarrier μ) x := by
  have hi (i : ι) : ContDiffAt ℝ n (fun y : ι → ℝ ↦ Real.log (y i)) x :=
    (coordinate i).contDiff.contDiffAt.log (hx i).ne'
  exact (ContDiffAt.sum fun i (_ : i ∈ Finset.univ) ↦ hi i).const_smul (-μ)

private theorem hasFDerivAt_logBarrier (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    HasFDerivAt (logBarrier μ) (logBarrierFDeriv μ x) x := by
  have hi (i : ι) : HasFDerivAt (fun y : ι → ℝ ↦ Real.log (y i))
      ((x i)⁻¹ • coordinate i) x :=
    let h : HasDerivAt Real.log (x i)⁻¹ (coordinate i x) :=
      Real.hasDerivAt_log (hx i).ne'
    h.comp_hasFDerivAt x (coordinate i).hasFDerivAt
  exact (HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) ↦ hi i).const_smul (-μ)

/-- Let $\mu \in \mathbb{R}$ and let $x \in \mathbb{R}^\iota$ have positive coordinates. The
derivative of the logarithmic barrier at $x$ in the direction $d \in \mathbb{R}^\iota$ is
$$-\mu \sum_{i \in \iota} \frac{d_i}{x_i}.$$
-/
theorem fderiv_logBarrier_apply (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i) (d : ι → ℝ) :
    fderiv ℝ (logBarrier μ) x d = -μ * ∑ i, (x i)⁻¹ * d i := by
  rw [(hasFDerivAt_logBarrier μ hx).fderiv]
  simp [logBarrierFDeriv, coordinate]

/-- Let $\mu \in \mathbb{R}$ and let $x \in \mathbb{R}^\iota$ have positive coordinates. The second
derivative of the logarithmic barrier at $x$ is diagonal: for $d, e \in \mathbb{R}^\iota$,
$$\nabla^2 \Bigl(-\mu \sum_i \log x_i\Bigr)[d, e] = \mu \sum_{i \in \iota} \frac{d_i
  e_i}{x_i^2}.$$

The second derivative is `fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x`, applied to `d` and
then to `e`. -/
theorem fderiv_fderiv_logBarrier_apply (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (d e : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (logBarrier μ)) x d e =
      μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * e i := by
  have hU : Set.univ.pi (fun _ : ι ↦ Set.Ioi (0 : ℝ)) ∈ 𝓝 x :=
    (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi).mem_nhds (by simpa using hx)
  have hEq : fderiv ℝ (logBarrier μ) =ᶠ[𝓝 x] logBarrierFDeriv μ := by
    filter_upwards [hU] with y hy
    exact (hasFDerivAt_logBarrier μ (by simpa using hy)).fderiv
  have hi (i : ι) : HasFDerivAt (fun y : ι → ℝ ↦ (y i)⁻¹)
      (-((x i) ^ 2)⁻¹ • coordinate i) x :=
    (hasDerivAt_inv (hx i).ne').comp_hasFDerivAt x (coordinate i).hasFDerivAt
  have hD := (HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) ↦
    (hi i).smul_const (coordinate i)).const_smul (-μ)
  rw [hEq.fderiv_eq]
  change fderiv ℝ ((-μ) • fun y : ι → ℝ ↦
    ∑ i, (y i)⁻¹ • coordinate i) x d e = _
  rw [hD.fderiv]
  simp [coordinate, Finset.sum_neg_distrib, mul_assoc]

/-- Let $x \in \mathbb{R}^\iota$ have positive coordinates. Then for every $i \in \iota$ the
distance from $x$ to the boundary of the nonnegative orthant is at most $x_i$. -/
theorem infDist_frontier_le_coordinate {x : ι → ℝ} (hx : ∀ i, 0 < x i) (i : ι) :
    infDist x (frontier (nonnegativeOrthant ι)) ≤ x i := by
  classical
  let y := Function.update x i 0
  have hy : y ∈ frontier (nonnegativeOrthant ι) := by
    apply mem_frontier_nonnegativeOrthant.mpr
    refine ⟨fun j ↦ ?_, i, Function.update_self i 0 x⟩
    by_cases hj : j = i
    · subst j
      rw [show y i = 0 from Function.update_self i 0 x]
    · rw [show y j = x j from Function.update_of_ne hj 0 x]
      exact (hx j).le
  refine (infDist_le_dist_of_mem hy).trans ((dist_pi_le_iff (hx i).le).mpr fun j ↦ ?_)
  by_cases hj : j = i
  · subst j
    rw [show y i = 0 from Function.update_self i 0 x, Real.dist_eq, sub_zero, abs_of_pos (hx i)]
  · rw [show y j = x j from Function.update_of_ne hj 0 x, dist_self]
    exact (hx i).le

/-- Let $\mu \in \mathbb{R}$ and $\varepsilon > 0$, and let $x \in \mathbb{R}^\iota$ satisfy
$x_i \ge \varepsilon$ for all $i$. Then the second derivative of the logarithmic barrier at $x$
has operator norm
$$\bigl\|\nabla^2 \bigl(-\mu \textstyle\sum_i \log x_i\bigr)\bigr\| \le \frac{|\mu| \,
  |\iota|}{\varepsilon^2},$$
where $|\iota|$ is the number of indices.

The norm is the operator norm of `fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x` for the sup
norm on `ι → ℝ`. -/
theorem norm_fderiv_fderiv_logBarrier_le (μ : ℝ) {x : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hx : ∀ i, ε ≤ x i) :
    ‖fderiv ℝ (fderiv ℝ (logBarrier μ)) x‖ ≤ |μ| * Fintype.card ι * (ε ^ 2)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro e
  rw [fderiv_fderiv_logBarrier_apply μ (fun i ↦ hε.trans_le (hx i)), Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |μ| * ∑ i, |((x i) ^ 2)⁻¹ * d i * e i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |μ| * ∑ _ : ι, (ε ^ 2)⁻¹ * ‖d‖ * ‖e‖ := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      have hi : ((x i) ^ 2)⁻¹ ≤ (ε ^ 2)⁻¹ :=
        (inv_le_inv₀ (pow_pos (hε.trans_le (hx i)) 2) (pow_pos hε 2)).mpr
          (pow_le_pow_left₀ hε.le (hx i) 2)
      simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (x i))), ← Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul hi (norm_le_pi_norm d i) (norm_nonneg _) (by positivity))
        (norm_le_pi_norm e i) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Optimization
