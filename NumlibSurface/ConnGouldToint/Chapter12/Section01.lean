import Numlib.Optimization.ModelBased.ProjectedPath
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The projected-gradient path

[conn2000trust], Section 12.1.3. First-order criticality is expressed by the
variational inequality over feasible displacements. The path uses the negative
gradient, in agreement with Theorem 3.2.9.
-/

open Filter Optimization
open scoped RealInnerProductSpace Topology

namespace ConnGouldToint.Chapter12

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Corrected (12.1.3). The radial expression applies outside the ball. Inside,
the input is already feasible and is its own projection. -/
theorem projection_closedBall (x y : E) {r : ℝ} (hr : 0 ≤ r) :
    bestApprox (Metric.closedBall x r) y =
      if ‖y - x‖ ≤ r then y else x + (r / ‖y - x‖) • (y - x) :=
  bestApprox_closedBall_eq_radial x y hr

/-- The projected-gradient path (12.1.4), parametrized by the step length. -/
noncomputable def projectedGradientPath (C : Set E) (f : E → ℝ) (x : E) (t : ℝ) : E :=
  projectedRay C x (-gradient f x) t

variable {C : Set E} (hclosed : IsClosed C) (hconv : Convex ℝ C) {f : E → ℝ} {x : E}
include hclosed hconv

/-- Theorem 12.1.1. If the negative gradient is normal at a projected point, the path
is constant from that point onward. -/
theorem theorem_12_1_1 (hne : C.Nonempty) {s t : ℝ} (hst : s ≤ t)
    (hd : -gradient f x ∈ normalDirections C (projectedGradientPath C f x s)) :
    projectedGradientPath C f x t = projectedGradientPath C f x s :=
  projectedRay_eq_of_normal hne hclosed hconv hst hd

/-- Theorem 12.1.2. The projected-gradient path is constant exactly when the
variational inequality holds. For a differentiable objective, this inequality
is the first-order criticality condition. -/
theorem theorem_12_1_2 (hx : x ∈ C) :
    (∀ y ∈ C, 0 ≤ ⟪gradient f x, y - x⟫) ↔
      ∀ t : ℝ, 0 ≤ t → projectedGradientPath C f x t = x := by
  rw [show projectedGradientPath C f x = projectedRay C x (-gradient f x) by rfl,
    projectedRay_eq_self_iff ⟨x, hx⟩ hclosed hconv hx, mem_normalDirections]
  simp only [inner_neg_left, neg_nonpos]

/-- Theorem 12.1.3. The displacement norm is nondecreasing and, if it has a finite
limit, the tangent projection of the negative gradient tends to zero.
The quantitative bound for projected rays makes the smooth-constraint and
finite-representation assumptions AC.1 and AC.7 unnecessary. -/
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

/-- Theorem 12.1.4. The projected displacement minimizes the linear model on the
feasible displacements of at most its norm. If the descent direction is normal at
the projected point, it also minimizes the model at every larger radius. -/
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

end ConnGouldToint.Chapter12
