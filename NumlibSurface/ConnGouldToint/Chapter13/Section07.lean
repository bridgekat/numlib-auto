/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter13.Section06

/-!
# Conn, Gould and Toint, Section 13.7: Scaling of barrier methods

This module formalizes the scaled stopping tests of Section 13.7 of [conn2000trust] for barrier
methods on the nonnegative orthant of $\mathbb{R}^n$. For a primal point $x > 0$, a dual point
$z \ge 0$ and a Hessian form $H$, the barrier metric is
$$\|d\|_{x,z}^2 = H(d) + \sum_i \frac{z_i}{x_i} d_i^2.$$
The dual and Hessian stopping tests are measured in this metric. On a layer where the primal
coordinates are bounded away from zero, the metric is uniformly equivalent to the Euclidean norm
(Theorem 13.7.1). As the barrier parameter $\mu$ tends to zero, the scaled tests give first-order
and weak second-order conditions in the limit (Theorems 13.7.2 and 13.7.3). The objective gradient
is `ConnGouldToint.Chapter13.barrierCoordinateGradient`.

## Main definitions

* Equations (13.7.2)–(13.7.3), `ConnGouldToint.Chapter13.barrierMetricQuadratic`: the quadratic form
  $H(d) + \sum_i (z_i / x_i) d_i^2$ of the barrier metric.
* Equations (13.7.9)–(13.7.11), `ConnGouldToint.Chapter13.ScaledBarrierDualTest`: the dual residual
  is at most $\varepsilon$ in the dual norm of the metric.
* Equations (13.7.12)–(13.7.13), `ConnGouldToint.Chapter13.ScaledBarrierHessianTest`: the Hessian
  form is at least $-\varepsilon$ times the metric.

## Main results

* Theorem 13.7.1, `ConnGouldToint.Chapter13.theorem_13_7_1`: on a uniformly positive layer with
  bounded duals, the barrier metric is uniformly equivalent to the Euclidean norm.
* Theorem 13.7.2, `ConnGouldToint.Chapter13.theorem_13_7_2`: the scaled primal-dual tests with
  vanishing tolerances give nonnegative limiting gradients, zero limiting gradients on the
  coordinates bounded away from zero, and nonnegative limiting curvature on those coordinates.
* Theorem 13.7.3, `ConnGouldToint.Chapter13.theorem_13_7_3`: the same conclusions for the primal
  method, where $z_i = \mu / x_i$.

## Implementation notes

* Vectors are functions `ι → ℝ` on a finite index type `ι`. The Hessian form $H$ is any function
  `(ι → ℝ) → ℝ` with an upper bound $H(d) \le K \|d\|^2$; it stands for the quadratic form of the
  Hessian.
* The limits in Theorems 13.7.2 and 13.7.3 are taken along an arbitrary filter, and the iterates are
  indexed by an arbitrary type.

## Deviations from the source

* **Representation.** Scaled stopping tests are expressed as dual and Hessian inequalities on
  quadratic forms. See `ConnGouldToint.Chapter13.barrierMetricQuadratic`,
  `ConnGouldToint.Chapter13.ScaledBarrierDualTest`,
  `ConnGouldToint.Chapter13.ScaledBarrierHessianTest`.
* **Reading.** The uniform norm equivalence is stated in terms of explicit primal and dual
  coordinate bounds. See `ConnGouldToint.Chapter13.theorem_13_7_1`.
* **Generalization.** The scaled primal-dual conclusions use filter limits and eventual relative
  complementarity control. See `ConnGouldToint.Chapter13.theorem_13_7_2`.
* **Correction.** The primal scaled theorem retains a gradient-tolerance rate; a scalar quadratic
  gives a counterexample without it. See `ConnGouldToint.Chapter13.theorem_13_7_3`,
  `ConnGouldToint.Chapter13.theorem_13_7_3_counterexample`.
* **Theorem 13.7.2** (generalization). The bound $\varepsilon^C_k \le L \mu_k$ on the
  complementarity tolerance is assumed only eventually. The condition (13.7.15) implies it after
  increasing the constant. See `ConnGouldToint.Chapter13.theorem_13_7_2`.
* **Theorem 13.7.3** (correction). The theorem keeps the gradient-tolerance rate (13.7.16) of
  Theorem 13.7.2. A one-dimensional quadratic example shows that vanishing scaled tolerances alone
  are insufficient. See `ConnGouldToint.Chapter13.theorem_13_7_3_counterexample`.
-/

open Filter Set
open scoped Topology

namespace ConnGouldToint.Chapter13

variable {ι : Type*} [Fintype ι]

/-- **Equations (13.7.2)–(13.7.3)** of [conn2000trust]. For a Hessian form $H$, a primal point $x$
and a dual point $z$, the **barrier metric quadratic** is
$$q_{x,z}(d) = H(d) + \sum_i \frac{z_i}{x_i} d_i^2.$$
The metric (13.7.2) is its square root.

**Reading.** The scaled norm tests use the underlying quadratic form, a dual pairing inequality and
a Hessian quadratic-form inequality. This avoids writing a matrix inverse or square root. It agrees
with the scaled tests when the metric is positive definite.
-/
noncomputable def barrierMetricQuadratic (H : (ι → ℝ) → ℝ) (x z d : ι → ℝ) : ℝ :=
  H d + ∑ i, (z i / x i) * (d i) ^ 2

/-- **Theorem 13.7.1** of [conn2000trust]. Let $x_j, z_j \in \mathbb{R}^n$ and Hessian forms $H_j$
be given for $j \in \mathbb{N}$, and let $\delta > 0$, $\varepsilon > 0$ and $K \ge 0$. Assume
that $x_{j,i} \ge \delta$ and $0 \le z_{j,i} \le K \max\{x_{j,i}^{-1}, 1\}$ for all $j$ and $i$,
that $H_j(d) \le K_H \|d\|^2$, and that $\varepsilon \|d\|^2 \le q_{x_j,z_j}(d)$ for all $j$ and
$d$. Then for all $j$ and $d$,
$$\varepsilon \|d\|^2 \le q_{x_j,z_j}(d) \le \left(K_H + \frac{K \max\{\delta^{-1},
  1\}}{\delta}\right) \|d\|^2.$$

The layer $x_{j,i} \ge \delta$ is the uniformly positive layer supplied by Theorem 13.2.1. After
taking square roots, the two bounds give AN.1 for the metric (13.7.2). The bound on $z$ is AA.7,
which contributes the factor $\max\{\delta^{-1}, 1\}$, so the estimate also holds when
$\delta > 1$. The lower bound is a hypothesis and is restated in the conclusion. The norm
$\|d\|$ is Euclidean, and $q$ is `ConnGouldToint.Chapter13.barrierMetricQuadratic`.

**Reading.** The uniform metric bounds expose a positive primal lower bound and a dual coordinate
upper bound directly. The result supplies explicit squared norm equivalence constants.
-/
theorem theorem_13_7_1 {x z : ℕ → ι → ℝ} {H : ℕ → (ι → ℝ) → ℝ}
    {δ ε K KH : ℝ} (hδ : 0 < δ) (_hε : 0 < ε) (hK : 0 ≤ K)
    (hx : ∀ j i, δ ≤ x j i) (hz : ∀ j i, 0 ≤ z j i ∧ z j i ≤ K * max (x j i)⁻¹ 1)
    (hH : ∀ j d, H j d ≤ KH * ∑ i, (d i) ^ 2)
    (hpos : ∀ j d, ε * (∑ i, (d i) ^ 2) ≤ barrierMetricQuadratic (H j) (x j) (z j) d) :
    ∀ j d, ε * (∑ i, (d i) ^ 2) ≤ barrierMetricQuadratic (H j) (x j) (z j) d ∧
      barrierMetricQuadratic (H j) (x j) (z j) d ≤
        (KH + K * max δ⁻¹ 1 / δ) * ∑ i, (d i) ^ 2 := by
  intro j d
  refine ⟨hpos j d, ?_⟩
  have hb (i : ι) : z j i / x j i ≤ K * max δ⁻¹ 1 / δ := calc
    _ ≤ z j i / δ := div_le_div_of_nonneg_left (hz j i).1 hδ (hx j i)
    _ ≤ _ := div_le_div_of_nonneg_right ((hz j i).2.trans (mul_le_mul_of_nonneg_left
      (max_le_max (inv_anti₀ hδ (hx j i)) le_rfl) hK)) hδ.le
  rw [barrierMetricQuadratic, add_mul, Finset.mul_sum (s := Finset.univ)
    (a := K * max δ⁻¹ 1 / δ)]
  exact add_le_add (hH j d) (Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _))

/-- **Equations (13.7.9)–(13.7.11)** of [conn2000trust]. A residual $r \in \mathbb{R}^n$ passes the
**scaled dual test** with tolerance $\varepsilon$ for the quadratic form $q$ if
$$\left|\sum_i r_i d_i\right| \le \varepsilon \sqrt{q(d)} \quad \text{for all } d \in
  \mathbb{R}^n.$$

This is the test (13.7.9) or (13.7.10) on the dual norm of $r$, written as a pointwise bound on
the dual pairing.

**Reading.** The scaled norm tests use the underlying quadratic form, a dual pairing inequality and
a Hessian quadratic-form inequality. This avoids writing a matrix inverse or square root. It agrees
with the scaled tests when the metric is positive definite.
-/
def ScaledBarrierDualTest (q : (ι → ℝ) → ℝ) (r : ι → ℝ) (ε : ℝ) : Prop :=
  ∀ d : ι → ℝ, |∑ i, r i * d i| ≤ ε * Real.sqrt (q d)

/-- **Equations (13.7.12)–(13.7.13)** of [conn2000trust]. A quadratic form $B$ passes the **scaled
Hessian test** with tolerance $\varepsilon$ for the metric quadratic $q$ if
$B(d) \ge -\varepsilon q(d)$ for all $d \in \mathbb{R}^n$.

This is the eigenvalue test (13.7.12) or (13.7.13) after the change of variables by the square
root of the positive-definite metric.

**Reading.** The scaled norm tests use the underlying quadratic form, a dual pairing inequality and
a Hessian quadratic-form inequality. This avoids writing a matrix inverse or square root. It agrees
with the scaled tests when the metric is positive definite.
-/
def ScaledBarrierHessianTest (q B : (ι → ℝ) → ℝ) (ε : ℝ) : Prop :=
  ∀ d, -ε * q d ≤ B d

variable [DecidableEq ι]

private theorem barrierMetric_coordinate_bound {x z : ι → ℝ} {H : (ι → ℝ) → ℝ}
    {K : ℝ} (hH : ∀ d, H d ≤ K * ∑ i, (d i) ^ 2) (i : ι) :
    barrierMetricQuadratic H x z (Pi.single i 1) ≤ K + z i / x i := by
  have h := hH (Pi.single i 1)
  have hsum : (∑ j, ((Pi.single i (1 : ℝ) : ι → ℝ) j) ^ 2) = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have hdiag : (∑ j, (z j / x j) * ((Pi.single i (1 : ℝ) : ι → ℝ) j) ^ 2) = z i / x i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  simpa only [barrierMetricQuadratic, hdiag, hsum, mul_one] using add_le_add_left h (z i / x i)

private theorem scaledBarrier_coordinate_residual {q : (ι → ℝ) → ℝ} {r : ι → ℝ} {ε : ℝ}
    (h : ScaledBarrierDualTest q r ε) (i : ι) :
    |r i| ≤ ε * Real.sqrt (q (Pi.single i 1)) := by
  have hs := h (Pi.single i 1)
  have he : (∑ j, r j * (Pi.single i (1 : ℝ) : ι → ℝ) j) = r i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  rwa [he] at hs

/-- **Theorem 13.7.2** of [conn2000trust]. Let $f : \mathbb{R}^n \to \mathbb{R}$, and let
$x_k, z_k \in \mathbb{R}^n$, Hessian forms $H_k$, and numbers $\mu_k, \varepsilon^D_k,
\varepsilon^C_k, \varepsilon^E_k, \rho_k$ be indexed by $k$ in a set with a filter $l$. Assume
that $x_k > 0$, $z_k > 0$, $\mu_k > 0$, $\rho_k > 0$, $\rho_k \le x_{k,i}$ for all $i$,
$\varepsilon^D_k \ge 0$ and $\varepsilon^E_k \ge 0$, and that along $l$
$$\mu_k \to 0, \quad \varepsilon^D_k \to 0, \quad \varepsilon^C_k \to 0, \quad \varepsilon^E_k
  \to 0, \quad \frac{\varepsilon^D_k \sqrt{\mu_k}}{\rho_k} \to 0,$$
with eventually $\varepsilon^C_k \le L \mu_k$, where $K, L \ge 0$. Assume
$H_k(d) \le K \|d\|^2$, and let $q_k = q_{x_k,z_k}$ be the barrier metric quadratic. Assume the
stopping tests: $\nabla f(x_k) - z_k$ passes the scaled dual test with tolerance
$\varepsilon^D_k$ for $q_k$, $|x_{k,i} z_{k,i} - \mu_k| \le \varepsilon^C_k$ for all $i$, and $d
\mapsto \nabla^2 f(x_k)[d, d] + \sum_i (z_{k,i} / x_{k,i}) d_i^2$ passes the scaled Hessian test
with tolerance $\varepsilon^E_k$ for $q_k$. Then:
* for every $i$ and every $\eta > 0$, eventually $\partial_i f(x_k) \ge -\eta$;
* for every $i$ such that eventually $x_{k,i} \ge \delta$ for some $\delta > 0$,
  $\partial_i f(x_k) \to 0$;
* for every $d$ whose nonzero coordinates $i$ all satisfy eventually $x_{k,i} \ge \delta$ for
  some $\delta > 0$, and for every $\eta > 0$, eventually $\nabla^2 f(x_k)[d, d] \ge -\eta$.

**Generalization.** The bound $\varepsilon^C_k \le L \mu_k$ on relative complementarity is
assumed only eventually. It follows from (13.7.15) after increasing the constant.

The number $\rho_k$ may be chosen as the smallest primal coordinate of $x_k$. The partial
derivative $\partial_i f(x_k)$ is `ConnGouldToint.Chapter13.barrierCoordinateGradient`.

**Generalization.** The conclusions hold along a filter for prescribed points satisfying the
residual tests. The relative complementarity tolerance need only hold eventually, and a positive
lower bound on all coordinates may replace the exact smallest coordinate in the gradient-tolerance
rate.
-/
theorem theorem_13_7_2 {α : Type*} {l : Filter α} {f : (ι → ℝ) → ℝ}
    {x z : α → ι → ℝ} {H : α → (ι → ℝ) → ℝ}
    {μ εD εC εE ρ : α → ℝ} {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hx : ∀ k i, 0 < x k i) (hz : ∀ k i, 0 < z k i)
    (hμpos : ∀ k, 0 < μ k) (hρ : ∀ k, 0 < ρ k) (hρx : ∀ k i, ρ k ≤ x k i)
    (hμ : Tendsto μ l (𝓝 0)) (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k)
    (hC : Tendsto εC l (𝓝 0)) (hE : Tendsto εE l (𝓝 0)) (hEpos : ∀ k, 0 ≤ εE k)
    (hrel : ∀ᶠ k in l, εC k ≤ L * μ k)
    (hrate : Tendsto (fun k ↦ εD k * Real.sqrt (μ k) / ρ k) l (𝓝 0))
    (hH : ∀ k d, H k d ≤ K * ∑ i, (d i) ^ 2)
    (hd : ∀ k, ScaledBarrierDualTest (barrierMetricQuadratic (H k) (x k) (z k))
      (fun i ↦ barrierCoordinateGradient f (x k) i - z k i) (εD k))
    (hc : ∀ k i, |x k i * z k i - μ k| ≤ εC k)
    (he : ∀ k, ScaledBarrierHessianTest (barrierMetricQuadratic (H k) (x k) (z k))
      (fun d ↦ fderiv ℝ (fderiv ℝ f) (x k) d d + ∑ i, (z k i / x k i) * d i * d i) (εE k)) :
    (∀ i η, 0 < η → ∀ᶠ k in l, -η ≤ barrierCoordinateGradient f (x k) i) ∧
    (∀ i, (∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i) l (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      ∀ η, 0 < η → ∀ᶠ k in l, -η ≤ fderiv ℝ (fderiv ℝ f) (x k) d d := by
  have hprod (i : ι) : Tendsto (fun k ↦ x k i * z k i) l (𝓝 0) := by
    have he : Tendsto (fun k ↦ x k i * z k i - μ k) l (𝓝 0) :=
      squeeze_zero_norm' (Eventually.of_forall fun k ↦ by simpa [Real.norm_eq_abs] using hc k i) hC
    simpa only [sub_add_cancel, add_zero] using he.add hμ
  have hratio (i : ι) : ∀ᶠ k in l, z k i / x k i ≤ (1 + L) * μ k / (ρ k) ^ 2 := by
    filter_upwards [hrel] with k hk
    have hp := (abs_le.mp (hc k i)).2
    have hn : x k i * z k i ≤ (1 + L) * μ k := by linarith
    have he : z k i / x k i = (x k i * z k i) / (x k i) ^ 2 := by
      field_simp [(hx k i).ne']
    rw [he]
    exact (div_le_div_of_nonneg_right hn (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left (mul_nonneg (by linarith) (hμpos k).le) (sq_pos_of_pos (hρ k))
        ((sq_le_sq₀ (hρ k).le (hx k i).le).mpr (hρx k i)))
  have herr (i : ι) : Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i - z k i) l (𝓝 0) := by
    refine squeeze_zero_norm'
      (a := fun k ↦ εD k * Real.sqrt K + Real.sqrt (1 + L) * (εD k * Real.sqrt (μ k) / ρ k))
      ?_ ?_
    · filter_upwards [hratio i] with k hk
      rw [Real.norm_eq_abs]
      refine (scaledBarrier_coordinate_residual (hd k) i).trans ?_
      have hq := (barrierMetric_coordinate_bound (x := x k) (z := z k) (hH k) i).trans
        (add_le_add_right hk K)
      let B := (1 + L) * μ k / (ρ k) ^ 2
      have hB : 0 ≤ B := div_nonneg (mul_nonneg (by linarith) (hμpos k).le) (sq_nonneg _)
      have hs : Real.sqrt (K + B) ≤ Real.sqrt K + Real.sqrt B := by
        apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
        rw [Real.sq_sqrt (add_nonneg hK hB)]
        nlinarith [Real.sq_sqrt hK, Real.sq_sqrt hB,
          mul_nonneg (Real.sqrt_nonneg K) (Real.sqrt_nonneg B)]
      refine (mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt hq).trans hs)
        (hDpos k)).trans_eq ?_
      dsimp only [B]
      rw [Real.sqrt_div (mul_nonneg (by linarith) (hμpos k).le), Real.sqrt_mul (by linarith),
        Real.sqrt_sq (hρ k).le]
      ring
    · simpa only [mul_zero, zero_mul, add_zero] using
        (hD.mul_const (Real.sqrt K)).add (hrate.const_mul (Real.sqrt (1 + L)))
  have hzfree (i : ι) {δ : ℝ} (hδ : 0 < δ) (hxi : ∀ᶠ k in l, δ ≤ x k i) :
      Tendsto (fun k ↦ z k i) l (𝓝 0) := by
    apply squeeze_zero' (g := fun k ↦ (x k i * z k i) / δ)
      (Eventually.of_forall fun k ↦ (hz k i).le)
    · filter_upwards [hxi] with k hk
      exact (le_div_iff₀ hδ).mpr (by
        rw [mul_comm (z k i) δ]
        exact mul_le_mul_of_nonneg_right hk (hz k i).le)
    · simpa using (hprod i).div_const δ
  refine ⟨?_, ?_, ?_⟩
  · intro i η hη
    filter_upwards [(herr i).eventually (lt_mem_nhds (show -η < (0 : ℝ) by linarith))] with k hk
    linarith [hz k i]
  · intro i ⟨δ, hδ, hxi⟩
    simpa only [sub_add_cancel, zero_add] using (herr i).add (hzfree i hδ hxi)
  · intro d hfree η hη
    have hdiag : Tendsto (fun k ↦ ∑ i, (z k i / x k i) * (d i) ^ 2) l (𝓝 0) := by
      rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
      apply tendsto_finsetSum Finset.univ
      intro i _
      by_cases hi : d i = 0
      · simpa [hi] using (tendsto_const_nhds : Tendsto (fun _ : α ↦ (0 : ℝ)) l (𝓝 0))
      obtain ⟨δ, hδ, hxi⟩ := hfree i hi
      have hr : Tendsto (fun k ↦ z k i / x k i) l (𝓝 0) := by
        apply squeeze_zero' (g := fun k ↦ z k i / δ)
        · exact Eventually.of_forall fun k ↦ div_nonneg (hz k i).le (hx k i).le
        · filter_upwards [hxi] with k hk
          exact div_le_div_of_nonneg_left (hz k i).le hδ hk
        · simpa using (hzfree i hδ hxi).div_const δ
      simpa only [zero_mul] using hr.mul_const ((d i) ^ 2)
    have hb : Tendsto (fun k ↦ εE k * (K * ∑ i, (d i) ^ 2 +
          ∑ i, (z k i / x k i) * (d i) ^ 2) + ∑ i, (z k i / x k i) * (d i) ^ 2) l (𝓝 0) := by
      simpa only [zero_mul, zero_add, add_zero] using
        (hE.mul (tendsto_const_nhds.add hdiag)).add hdiag
    filter_upwards [hb.eventually (gt_mem_nhds hη)] with k hk
    have hq := mul_le_mul_of_nonneg_left (add_le_add_right (hH k d)
      (∑ i, (z k i / x k i) * (d i) ^ 2)) (hEpos k)
    have hh := he k d
    unfold barrierMetricQuadratic at hh
    simp only [pow_two, ← mul_assoc, mul_add, add_comm] at hq hk hh
    linarith only [hh, hq, hk]

/-- **Theorem 13.7.3** of [conn2000trust]. Let $f$, $x_k$, $H_k$, $\mu_k$, $\varepsilon^D_k$,
$\varepsilon^E_k$, $\rho_k$, $l$ and $K \ge 0$ be as in Theorem 13.7.2, without the dual points
and the complementarity tolerance. Use the exact dual values $z_{k,i} = \mu_k / x_{k,i}$, and
let $q_k$ be the barrier metric quadratic for $x_k$ and these values. Assume that $x_k > 0$,
$\mu_k > 0$, $\rho_k > 0$, $\rho_k \le x_{k,i}$, $\varepsilon^D_k, \varepsilon^E_k \ge 0$, that
$\mu_k$, $\varepsilon^D_k$, $\varepsilon^E_k$ and $\varepsilon^D_k \sqrt{\mu_k} / \rho_k$ tend
to $0$ along $l$, and that $H_k(d) \le K \|d\|^2$. Assume that
$\partial_i f(x_k) - \mu_k / x_{k,i}$ passes the scaled dual test with tolerance
$\varepsilon^D_k$ for $q_k$, and that $d \mapsto \nabla^2 f(x_k)[d, d] + \mu_k \sum_i
x_{k,i}^{-2} d_i^2$ passes the scaled Hessian test with tolerance $\varepsilon^E_k$ for $q_k$.
Then the three conclusions of Theorem 13.7.2 hold.

**Correction.** The source omits a rate for the gradient tolerance. The exact dual values make
the complementarity error zero, but a rate on the gradient tolerance is still needed when the
metric diverges. The statement assumes the rate (13.7.16) of the primal-dual theorem,
$\varepsilon^D_k \sqrt{\mu_k} / \rho_k \to 0$. Without it the conclusion fails; see
`ConnGouldToint.Chapter13.theorem_13_7_3_counterexample`.

The proof applies `ConnGouldToint.Chapter13.theorem_13_7_2` with zero complementarity tolerance.

**Correction.** Exact dual values cancel the complementarity residual, but the gradient tolerance
must also shrink at a rate compensating for the diverging metric. A quadratic counterexample shows
that vanishing scaled tolerances alone allow a negative limiting gradient.
-/
theorem theorem_13_7_3 {α : Type*} {l : Filter α} {f : (ι → ℝ) → ℝ}
    {x : α → ι → ℝ} {H : α → (ι → ℝ) → ℝ} {μ εD εE ρ : α → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hx : ∀ k i, 0 < x k i) (hμpos : ∀ k, 0 < μ k)
    (hρ : ∀ k, 0 < ρ k) (hρx : ∀ k i, ρ k ≤ x k i)
    (hμ : Tendsto μ l (𝓝 0)) (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k)
    (hE : Tendsto εE l (𝓝 0)) (hEpos : ∀ k, 0 ≤ εE k)
    (hrate : Tendsto (fun k ↦ εD k * Real.sqrt (μ k) / ρ k) l (𝓝 0))
    (hH : ∀ k d, H k d ≤ K * ∑ i, (d i) ^ 2)
    (hd : ∀ k, ScaledBarrierDualTest (barrierMetricQuadratic (H k) (x k) (fun i ↦ μ k / x k i))
      (fun i ↦ barrierCoordinateGradient f (x k) i - μ k / x k i) (εD k))
    (he : ∀ k, ScaledBarrierHessianTest (barrierMetricQuadratic (H k) (x k) (fun i ↦ μ k / x k i))
      (fun d ↦ fderiv ℝ (fderiv ℝ f) (x k) d d + μ k * ∑ i, ((x k i) ^ 2)⁻¹ * d i * d i)
      (εE k)) :
    (∀ i η, 0 < η → ∀ᶠ k in l, -η ≤ barrierCoordinateGradient f (x k) i) ∧
    (∀ i, (∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i) l (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      ∀ η, 0 < η → ∀ᶠ k in l, -η ≤ fderiv ℝ (fderiv ℝ f) (x k) d d := by
  apply theorem_13_7_2 (L := 0) hK le_rfl hx (fun k i ↦ div_pos (hμpos k) (hx k i))
    hμpos hρ hρx hμ hD hDpos (εC := fun _ ↦ 0) tendsto_const_nhds hE hEpos
    (Eventually.of_forall fun _ ↦ by simp) hrate hH hd
  · intro k i
    rw [mul_div_cancel₀ _ (hx k i).ne', sub_self, abs_zero]
  · intro k d
    have hh := he k d
    have hc : (∑ i, (μ k / x k i / x k i) * d i * d i) =
        μ k * ∑ i, ((x k i) ^ 2)⁻¹ * d i * d i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by
        simp only [div_eq_mul_inv, ← inv_pow]
        ring
    simpa only [hc] using hh

/-- A one-dimensional counterexample to Theorem 13.7.3 without the gradient-tolerance rate of
[conn2000trust]. There are positive sequences $\mu_k, \varepsilon^D_k, \varepsilon^E_k, x_k$
such that $\mu_k$, $\varepsilon^D_k$ and $\varepsilon^E_k$ tend to $0$, and for all $k$
$$\frac{\mu_k}{x_k^2} \ge 1, \qquad \left|x_k - 1 - \frac{\mu_k}{x_k}\right| \le \varepsilon^D_k
  \sqrt{\frac{\mu_k}{x_k^2}}, \qquad -\varepsilon^E_k \frac{\mu_k}{x_k^2} \le 1 +
  \frac{\mu_k}{x_k^2},$$
and $x_k - 1 \to -1$.

For the smooth objective $f(x) = (x - 1)^2 / 2$, which is bounded below, $f'(x) = x - 1$ and
$f''(x) = 1$. The two inequalities are the scaled dual and Hessian tests of Theorem 13.7.3 with
$H = 0$ and the metric weight $\mu_k / x_k^2$, but the gradient $f'(x_k)$ tends to $-1$. The
proof takes $x_k = \mu_k = t_k^2$, $\varepsilon^D_k = 2 t_k$ and $\varepsilon^E_k = t_k$ with
$t_k = 1 / (k + 1)$, so the exact dual value $\mu_k / x_k$ equals $1$.

**Correction.** Exact dual values cancel the complementarity residual, but the gradient tolerance
must also shrink at a rate compensating for the diverging metric. A quadratic counterexample shows
that vanishing scaled tolerances alone allow a negative limiting gradient.
-/
theorem theorem_13_7_3_counterexample :
    ∃ μ εD εE x : ℕ → ℝ,
      Tendsto μ atTop (𝓝 0) ∧ Tendsto εD atTop (𝓝 0) ∧ Tendsto εE atTop (𝓝 0) ∧
      (∀ k, 0 < μ k ∧ 0 < εD k ∧ 0 < εE k ∧ 0 < x k ∧
        1 ≤ μ k / (x k) ^ 2 ∧
        |x k - 1 - μ k / x k| ≤ εD k * Real.sqrt (μ k / (x k) ^ 2) ∧
        -εE k * (μ k / (x k) ^ 2) ≤ 1 + μ k / (x k) ^ 2) ∧
      Tendsto (fun k ↦ x k - 1) atTop (𝓝 (-1)) := by
  let t (k : ℕ) := 1 / ((k : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htpos (k : ℕ) : 0 < t k := by dsimp [t]; positivity
  have htle (k : ℕ) : t k ≤ 1 := by
    change 1 / ((k : ℝ) + 1) ≤ 1
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hsq : Tendsto (fun k ↦ (t k) ^ 2) atTop (𝓝 0) := by simpa using ht.pow 2
  refine ⟨fun k ↦ t k ^ 2, fun k ↦ 2 * t k, t, fun k ↦ t k ^ 2, hsq, ?_, ht, ?_, ?_⟩
  · simpa using ht.const_mul (2 : ℝ)
  · intro k
    have hp := htpos k
    have hl := htle k
    have hq : (t k) ^ 2 / ((t k) ^ 2) ^ 2 = ((t k)⁻¹) ^ 2 := by
      field_simp [hp.ne']
    have hi : 1 ≤ (t k)⁻¹ := (one_le_inv₀ hp).mpr hl
    rw [hq, div_self (sq_pos_of_pos hp).ne', Real.sqrt_sq (inv_nonneg.mpr hp.le)]
    have htinv : 2 * t k * (t k)⁻¹ = 2 := by field_simp [hp.ne']
    rw [htinv]
    refine ⟨sq_pos_of_pos hp, by positivity, hp, sq_pos_of_pos hp, ?_, ?_, ?_⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hi) (show 0 ≤ (t k)⁻¹ by positivity)]
    · apply abs_le.mpr
      have hmul := mul_nonneg hp.le (sub_nonneg.mpr hl)
      constructor <;> nlinarith [sq_nonneg (t k)]
    · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.le) (sq_nonneg _)).trans
        (by positivity)
  · simpa using hsq.sub_const 1

end ConnGouldToint.Chapter13
