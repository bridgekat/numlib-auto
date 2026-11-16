/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.LinearDecrease
import Numlib.Analysis.InnerProductSpace.BoxProjection
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Conn, Gould and Toint, Section 12.1: The projected-gradient path

This module formalizes Section 12.1 of [conn2000trust] on projections onto a closed convex set $C$
in a real Hilbert space $E$. It gives the projection onto a box (12.1.2) and onto a ball (12.1.3),
and studies the projected-gradient path
$$p(t) = P_C\bigl(x - t \nabla f(x)\bigr), \qquad t \ge 0,$$
of (12.1.4). The path is constant from a point at which $-\nabla f(x)$ is normal (Theorem 12.1.1),
and it is constant from $x$ exactly when $x$ satisfies the first-order condition
$\langle \nabla f(x), y - x \rangle \ge 0$ for all $y \in C$ (Theorem 12.1.2). Its displacements
minimize the linear model on feasible balls (Theorem 12.1.4). The criticality measure (12.1.13),
$$\chi(x, r) = \sup\{\langle -\nabla f(x), d \rangle : x + d \in C, \ \|d\| \le r\},$$
is continuous and nondecreasing in $r$ with $\chi(x, r)/r$ nonincreasing (Theorem 12.1.5), and
$\chi(x, 1)$ vanishes exactly at first-order critical points (Theorem 12.1.6).

The projection is `bestApprox`, the projected ray is `Optimization.projectedRay` of
`Numlib.Optimization.ModelBased.ProjectedPath`, and the criticality measure is
`Optimization.linearDecrease` of `Numlib.Optimization.ModelBased.LinearDecrease`.

## Main definitions

* Equation (12.1.1), `ConnGouldToint.Chapter12.box`: the box with extended-real bounds $l$ and $u$.
* Equation (12.1.4), `ConnGouldToint.Chapter12.projectedGradientPath`: the projected-gradient path
  $p(t)$.
* Equation (12.1.13), `ConnGouldToint.Chapter12.criticality`: the criticality measure $\chi(x, r)$.

## Main results

* Equation (12.1.2), `ConnGouldToint.Chapter12.projection_box_apply`: the projection onto a box
  clips each coordinate.
* Equation (12.1.3), `ConnGouldToint.Chapter12.projection_closedBall`: the projection onto a closed
  ball.
* Theorem 12.1.1, `ConnGouldToint.Chapter12.theorem_12_1_1`: if $-\nabla f(x)$ is normal at $p(s)$,
  then $p(t) = p(s)$ for all $t \ge s$.
* Theorem 12.1.2, `ConnGouldToint.Chapter12.theorem_12_1_2`: $p(t) = x$ for all $t \ge 0$ if and
  only if $x$ satisfies the first-order variational inequality.
* Theorem 12.1.3, `ConnGouldToint.Chapter12.theorem_12_1_3`: $\|p(t) - x\|$ is nondecreasing, and if
  it has a finite limit, the projection of $-\nabla f(x)$ onto the tangent cone at $p(t)$ tends to
  zero.
* Theorem 12.1.4, `ConnGouldToint.Chapter12.theorem_12_1_4`: $p(t) - x$ minimizes the linear model
  on the feasible displacements of at most its norm.
* Equations (12.1.13) and (12.1.17), `ConnGouldToint.Chapter12.criticality_eq_abs_min`: in finite
  dimension, $\chi(x, r)$ is the absolute value of an attained minimum of the linear model.
* Theorem 12.1.5, `ConnGouldToint.Chapter12.theorem_12_1_5`: continuity and monotonicity of
  $\chi(x, \cdot)$, and the tangent-projection bounds.
* Theorem 12.1.6, `ConnGouldToint.Chapter12.theorem_12_1_6`: $\chi(\cdot, 1)$ is nonnegative and
  continuous on $C$ and vanishes exactly at first-order critical points.

## Implementation notes

* First-order criticality is the variational inequality $\langle \nabla f(x), y - x \rangle \ge 0$
  for all $y \in C$. The path moves along the negative gradient, in agreement with Theorem 3.2.9.
* The normal cone $N_C(y)$ is `Optimization.normalDirections C y`, and the tangent cone $T_C(y)$ is
  its polar `Optimization.tangentDirections C y`.

## Deviations from the source

* **Equation (12.1.3)** (correction). The radial formula holds only outside the closed ball; a point
  inside the ball is its own projection. See `ConnGouldToint.Chapter12.projection_closedBall`.
* **Theorem 12.1.3** (generalization). The statement does not use the assumptions AC.1 and AC.7 on
  smooth constraints and a finite representation. See `ConnGouldToint.Chapter12.theorem_12_1_3`.
-/

open Filter Optimization
open scoped RealInnerProductSpace Topology

namespace ConnGouldToint.Chapter12

/-- **Equation (12.1.1)** of [conn2000trust]. For bounds $l, u \in [-\infty, \infty]^\iota$, the
**box** is the set of $x \in \mathbb{R}^\iota$ with $l_i \le x_i \le u_i$ for every $i$. -/
abbrev box {ι : Type*} [Fintype ι] (l u : ι → EReal) : Set (EuclideanSpace ℝ ι) :=
  euclideanBox l u

/-- **Equation (12.1.2)** of [conn2000trust]. If the box is nonempty, the projection of $x$ onto it
has the coordinates
$$P(x)_i = \begin{cases} l_i & \text{if } x_i < l_i, \\ u_i & \text{if } x_i > u_i, \\ x_i &
  \text{otherwise.} \end{cases}$$

The choice at equality is immaterial. The coordinate formula is `clipCoordinate`. -/
theorem projection_box_apply {ι : Type*} [Fintype ι] {l u : ι → EReal}
    (hne : (box l u).Nonempty) (x : EuclideanSpace ℝ ι) (i : ι) :
    bestApprox (box l u) x i = clipCoordinate (l i) (u i) (x i) :=
  bestApprox_euclideanBox_apply hne x i

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Equation (12.1.3)** of [conn2000trust], corrected. Let $x, y \in E$ and $r \ge 0$. The
projection of $y$ onto the closed ball of radius $r$ about $x$ is $y$ if $\|y - x\| \le r$, and
$$x + \frac{r}{\|y - x\|} (y - x)$$
otherwise.

**Correction.** The source gives the radial formula for every $y$. Inside the ball it moves $y$
to the sphere, but there $y$ is feasible and is its own projection. -/
theorem projection_closedBall (x y : E) {r : ℝ} (hr : 0 ≤ r) :
    bestApprox (Metric.closedBall x r) y =
      if ‖y - x‖ ≤ r then y else x + (r / ‖y - x‖) • (y - x) :=
  bestApprox_closedBall_eq_radial x y hr

/-- **Equation (12.1.4)** of [conn2000trust]. The **projected-gradient path** of $f$ at $x$ is
$p(t) = P_C(x - t \nabla f(x))$ for $t \in \mathbb{R}$, where $P_C$ is the projection onto $C$. -/
noncomputable def projectedGradientPath (C : Set E) (f : E → ℝ) (x : E) (t : ℝ) : E :=
  projectedRay C x (-gradient f x) t

variable {C : Set E} (hclosed : IsClosed C) (hconv : Convex ℝ C) {f : E → ℝ} {x : E}
include hclosed hconv

/-- **Theorem 12.1.1** of [conn2000trust]. Let $C$ be a nonempty closed convex subset of a real
Hilbert space $E$, and let $s \le t$. If $-\nabla f(x)$ lies in the normal cone of $C$ at
$p(s)$, then $p(t) = p(s)$. -/
theorem theorem_12_1_1 (hne : C.Nonempty) {s t : ℝ} (hst : s ≤ t)
    (hd : -gradient f x ∈ normalDirections C (projectedGradientPath C f x s)) :
    projectedGradientPath C f x t = projectedGradientPath C f x s :=
  projectedRay_eq_of_normal hne hclosed hconv hst hd

/-- **Theorem 12.1.2** of [conn2000trust]. Let $C$ be a closed convex subset of a real Hilbert space
$E$, and let $x \in C$. Then
$$\langle \nabla f(x), y - x \rangle \ge 0 \text{ for all } y \in C \iff p(t) = x \text{ for all
  } t \ge 0.$$

For a differentiable objective, the left side is the first-order criticality condition. -/
theorem theorem_12_1_2 (hx : x ∈ C) :
    (∀ y ∈ C, 0 ≤ ⟪gradient f x, y - x⟫) ↔
      ∀ t : ℝ, 0 ≤ t → projectedGradientPath C f x t = x := by
  rw [show projectedGradientPath C f x = projectedRay C x (-gradient f x) by rfl,
    projectedRay_eq_self_iff ⟨x, hx⟩ hclosed hconv hx, mem_normalDirections]
  simp only [inner_neg_left, neg_nonpos]

/-- **Theorem 12.1.3** of [conn2000trust]. Let $C$ be a closed convex subset of a real Hilbert space
$E$, and let $x \in C$. Then $t \mapsto \|p(t) - x\|$ is nondecreasing on $[0, \infty)$, and if
$\|p(t) - x\|$ has a finite limit as $t \to \infty$, then
$$\bigl\|P_{T_C(p(t))}\bigl(-\nabla f(x)\bigr)\bigr\| \to 0 \quad (t \to \infty),$$
where $P_{T_C(y)}$ is the projection onto the tangent cone of $C$ at $y$.

**Generalization.** The source assumes AC.1 and AC.7, the smoothness of the constraints and a
finite representation of $C$. The quantitative bound for projected rays makes these assumptions
unnecessary, so the statement holds for every closed convex set. -/
theorem theorem_12_1_3 (hx : x ∈ C) :
    MonotoneOn (fun t ↦ ‖projectedGradientPath C f x t - x‖) (Set.Ici 0) ∧
    ∀ L : ℝ, Tendsto (fun t ↦ ‖projectedGradientPath C f x t - x‖) atTop (𝓝 L) →
      Tendsto (fun t ↦
        ‖bestApprox (tangentDirections C (projectedGradientPath C f x t)) (-gradient f x)‖)
        atTop (𝓝 0) := by
  refine ⟨fun _ hs _ _ hst ↦ norm_projectedRay_sub_le ⟨x, hx⟩ hclosed hconv hs hst, ?_⟩
  intro L hL
  have hub : Tendsto (fun t ↦ ‖projectedGradientPath C f x t - x‖ / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hL.mul tendsto_inv_atTop_zero
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hub
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact norm_tangentProjection_projectedRay_le ⟨x, hx⟩ hclosed hconv x (-gradient f x) ht

/-- **Theorem 12.1.4** of [conn2000trust]. Let $C$ be a closed convex subset of a real Hilbert space
$E$, let $x \in C$ and $t \ge 0$, and let $d = p(t) - x$. Then $p(t) \in C$, and $d$ minimizes
the linear model $w \mapsto \langle \nabla f(x), w \rangle$ on
$\{w : x + w \in C, \ \|w\| \le \|d\|\}$. If moreover $-\nabla f(x)$ lies in the normal cone of
$C$ at $p(t)$, then $d$ minimizes the linear model on $\{w : x + w \in C, \ \|w\| \le \theta\}$
for every $\theta \ge \|d\|$. -/
theorem theorem_12_1_4 (hx : x ∈ C) {t : ℝ} (ht : 0 ≤ t) :
    let p := projectedGradientPath C f x t
    let d := p - x
    p ∈ C ∧
    IsMinOn (fun w ↦ ⟪gradient f x, w⟫) {w | x + w ∈ C ∧ ‖w‖ ≤ ‖d‖} d ∧
    (-gradient f x ∈ normalDirections C p → ∀ θ : ℝ, ‖d‖ ≤ θ →
      IsMinOn (fun w ↦ ⟪gradient f x, w⟫) {w | x + w ∈ C ∧ ‖w‖ ≤ θ} d) := by
  let g := gradient f x
  let p := projectedGradientPath C f x t
  let d := p - x
  have hp : p ∈ C := projectedRay_mem ⟨x, hx⟩ hclosed hconv x (-g) t
  have hnormal (w : E) (hw : x + w ∈ C) :
      ⟪t • (-g) - d, w - d⟫ ≤ 0 := by
    have h := mem_normalDirections.mp
      (projectedRay_residual_mem_normal ⟨x, hx⟩ hclosed hconv x (-g) t) (x + w) hw
    change ⟪x + t • (-g) - p, x + w - p⟫ ≤ 0 at h
    simpa only [show x + t • (-g) - p = t • (-g) - d by dsimp [d]; abel,
      show x + w - p = w - d by dsimp [d]; abel] using h
  refine ⟨hp, ?_, ?_⟩
  · apply isMinOn_iff.mpr
    intro w hw
    change x + w ∈ C ∧ ‖w‖ ≤ ‖d‖ at hw
    rcases ht.eq_or_lt with ht₀ | ht
    · have hp₀ : p = x := by
        change bestApprox C (x + t • (-g)) = x
        rw [← ht₀, zero_smul, add_zero]
        exact (bestApprox_eq_iff ⟨x, hx⟩ hclosed hconv).2 ⟨hx, by simp⟩
      have hd₀ : d = 0 := sub_eq_zero.mpr hp₀
      have hw₀ : w = 0 := by simpa [hd₀] using hw.2
      change ⟪g, d⟫ ≤ ⟪g, w⟫
      rw [hd₀, hw₀]
    · have h := hnormal w hw.1
      have hwd : ⟪d, w - d⟫ ≤ 0 := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq, sub_nonpos, pow_two]
        exact (real_inner_le_norm d w).trans (mul_le_mul_of_nonneg_left hw.2 (norm_nonneg d))
      rw [inner_sub_left, real_inner_smul_left, inner_neg_left] at h
      have hg : 0 ≤ ⟪g, w - d⟫ := by
        have hh : 0 ≤ t * ⟪g, w - d⟫ := by linarith
        exact nonneg_of_mul_nonneg_right hh ht
      rwa [inner_sub_right, sub_nonneg] at hg
  · intro hn θ _
    apply isMinOn_iff.mpr
    intro w hw
    have h := mem_normalDirections.mp hn (x + w) hw.1
    change ⟪-g, x + w - p⟫ ≤ 0 at h
    rwa [show x + w - p = w - d by dsimp [d]; abel, inner_neg_left,
      neg_nonpos, inner_sub_right, sub_nonneg] at h

omit hclosed hconv

/-- **Equation (12.1.13)** of [conn2000trust]. The **criticality measure** of $f$ at $x$ with radius
$r$ is
$$\chi(x, r) = \sup\{\langle -\nabla f(x), d \rangle : x + d \in C, \ \|d\| \le r\}.$$

The supremum is the real `sSup`, which is $0$ for an empty set or a set that is not bounded
above. At a feasible point $x$ the zero step is admissible, so $\chi(x, r) = |\inf_d \langle
\nabla f(x), d \rangle|$ over the same set. -/
noncomputable def criticality (C : Set E) (f : E → ℝ) (x : E) (r : ℝ) : ℝ :=
  linearDecrease C x (-gradient f x) r

/-- **Equations (12.1.13) and (12.1.17)** of [conn2000trust]. Let $E$ be finite-dimensional, $C$
closed, $x \in C$ and $r \ge 0$. Then there is $d$ with $x + d \in C$ and $\|d\| \le r$ that
minimizes $\langle \nabla f(x), w \rangle$ on $\{w : x + w \in C, \ \|w\| \le r\}$, and
$$\chi(x, r) = |\langle \nabla f(x), d \rangle|.$$
The radius $r = 1$ gives (12.1.17). -/
theorem criticality_eq_abs_min [FiniteDimensional ℝ E] (hC : IsClosed C) (hx : x ∈ C)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ d : E, x + d ∈ C ∧ ‖d‖ ≤ r ∧
      IsMinOn (fun w ↦ ⟪gradient f x, w⟫) {w | x + w ∈ C ∧ ‖w‖ ≤ r} d ∧
      criticality C f x r = |⟪gradient f x, d⟫| := by
  let g := gradient f x
  have hcontinuous : Continuous (fun w : E ↦ ⟪-g, w⟫) :=
    continuous_const.inner continuous_id
  obtain ⟨d, hd, he⟩ := exists_decrementMeasure_eq (isClosed_feasibleSteps hC x)
    (zero_mem_feasibleSteps.mpr hx) hr hcontinuous.continuousOn
  change ⟪-g, d⟫ = criticality C f x r at he
  refine ⟨d, hd.2, mem_closedBall_zero_iff.mp hd.1, ?_, ?_⟩
  · refine isMinOn_iff.mpr fun w hw ↦ ?_
    have h := inner_le_linearDecrease (v := -g) hw.1 hw.2
    change ⟪-g, w⟫ ≤ criticality C f x r at h
    rwa [← he, inner_neg_left, inner_neg_left, neg_le_neg_iff] at h
  · have h := linearDecrease_nonneg (v := -g) hx hr
    change 0 ≤ criticality C f x r at h
    rw [← he, inner_neg_left, neg_nonneg] at h
    rw [← he, inner_neg_left, abs_of_nonpos h]

/-- **Theorem 12.1.5** of [conn2000trust]. Let $C$ be a convex subset of a real Hilbert space $E$
and $x \in C$. Then:
* $r \mapsto \chi(x, r)$ is continuous and nondecreasing on $[0, \infty)$;
* $r \mapsto \chi(x, r)/r$ is nonincreasing on $(0, \infty)$;
* for every $d$ with $x + d \in C$ and every $r > \|d\|$,
$$\chi(x, r) \le |\langle \nabla f(x), d \rangle| + 2 r \bigl\|P_{T_C(x + d)}\bigl(-\nabla
  f(x)\bigr)\bigr\|;$$
* for every $r > 0$, $\chi(x, r)/r \le \|P_{T_C(x)}(-\nabla f(x))\|$.

The proof compares with the tangent projection directly, with sign, and needs no separate
estimate of the absolute value. -/
theorem theorem_12_1_5 (hC : Convex ℝ C) (hx : x ∈ C) :
    (ContinuousOn (criticality C f x) (Set.Ici 0) ∧
      MonotoneOn (criticality C f x) (Set.Ici 0)) ∧
    AntitoneOn (fun r ↦ criticality C f x r / r) (Set.Ioi 0) ∧
    (∀ d, x + d ∈ C → ∀ r, ‖d‖ < r →
      criticality C f x r ≤ |⟪gradient f x, d⟫| +
        2 * r * ‖bestApprox (tangentDirections C (x + d)) (-gradient f x)‖) ∧
    ∀ r, 0 < r → criticality C f x r / r ≤
      ‖bestApprox (tangentDirections C x) (-gradient f x)‖ := by
  refine ⟨⟨(linearDecrease_lipschitzOnWith_radius hC hx).continuousOn, ?_⟩,
    linearDecrease_antitoneOn_ratio hC hx, ?_, ?_⟩
  · intro s hs t _ hst
    exact linearDecrease_mono_radius hx hs hst
  · intro d _ r hr
    have hr₀ := (norm_nonneg d).trans hr.le
    have h := linearDecrease_le_tangent (v := -gradient f x) (d := d) hx hr₀
    exact h.trans (add_le_add (by rw [inner_neg_left]; exact neg_le_abs _)
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))
  · intro r hr
    apply (div_le_iff₀ hr).mpr
    have h := linearDecrease_le_tangent (v := -gradient f x) (d := (0 : E)) hx hr.le
    simpa [criticality, mul_comm] using h

/-- **Theorem 12.1.6** of [conn2000trust]. Let $C$ be a convex subset of a real Hilbert space $E$,
and let $f$ be continuously differentiable. Then $x \mapsto \chi(x, 1)$ is continuous on $C$,
and for every $x \in C$, $\chi(x, 1) \ge 0$ and
$$\chi(x, 1) = 0 \iff \langle \nabla f(x), y - x \rangle \ge 0 \text{ for all } y \in C.$$
-/
theorem theorem_12_1_6 (hC : Convex ℝ C) (hf : ContDiff ℝ 1 f) :
    ContinuousOn (fun x ↦ criticality C f x 1) C ∧
    ∀ x ∈ C, 0 ≤ criticality C f x 1 ∧
      (criticality C f x 1 = 0 ↔ ∀ y ∈ C, 0 ≤ ⟪gradient f x, y - x⟫) := by
  have hg : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  refine ⟨continuousOn_linearDecrease_one hC hg.neg.continuousOn, fun x hx ↦
    ⟨linearDecrease_nonneg hx zero_le_one, ?_⟩⟩
  change linearDecrease C x (-gradient f x) 1 = 0 ↔ _
  rw [linearDecrease_eq_zero_iff hC hx, mem_normalDirections]
  simp only [inner_neg_left, neg_nonpos]

end ConnGouldToint.Chapter12
