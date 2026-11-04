/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter17.Section03
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Model decrease and stopping residuals -/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter17

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The model change (17.4.1) for a conjugate-gradient line step. -/
theorem cgModelChange (g v p : E) (H : E →L[ℝ] E) (α : ℝ)
    (hpair : ⟪g, p⟫ = -⟪g, v⟫) (hline : α * ⟪p, H p⟫ = ⟪g, v⟫) :
    Subproblem.quadModel g H (α • p) = -(1 / 2 : ℝ) * α * ⟪g, v⟫ := by
  rw [Subproblem.quadModel_def, map_smul, inner_smul_right,
    real_inner_smul_left, inner_smul_right, hpair]
  nlinarith only [congrArg (α * ·) hline]

/-- The absolute unconstrained stopping test (17.4.2). -/
def gradientSmall [CompleteSpace E] (f : E → ℝ) (x : E) (ε : ℝ) : Prop :=
  ‖gradient f x‖ ≤ ε

/-- The constraint violation vector used in (17.4.4). -/
def constraintViolation {ι : Type*} (ineq : ι → Bool) (c : ι → ℝ) : ι → ℝ :=
  fun i ↦ if ineq i then min (c i) 0 else c i

/-- The projected stationarity residual (17.4.7) for a supplied gradient. -/
noncomputable def projectedStationarityResidual (C : Set E) (x g : E) : E :=
  bestApprox C (x - g) - x

variable [CompleteSpace E]

/-- The projected residual vanishes exactly under the convex first-order inequality. -/
theorem projectedStationarityResidual_eq_zero_iff {C : Set E} (hc : IsClosed C)
    (hconv : Convex ℝ C) {x g : E} (hx : x ∈ C) :
    projectedStationarityResidual C x g = 0 ↔ ∀ y ∈ C, 0 ≤ ⟪g, y - x⟫ := by
  rw [projectedStationarityResidual, sub_eq_zero, bestApprox_eq_iff ⟨x, hx⟩ hc hconv]
  simp [hx, sub_sub_cancel_left, inner_neg_left]

/-- Corrected (17.4.9). The trial point subtracts the Lagrangian gradient
`g - a`, where `a` is the multiplier-weighted equality gradient. -/
noncomputable def projectedLagrangianResidual (C : Set E) (x g a : E) : E :=
  projectedStationarityResidual C x (g - a)

/-- The corrected projected Lagrangian residual expresses the corresponding
variational inequality. -/
theorem projectedLagrangianResidual_eq_zero_iff {C : Set E} (hc : IsClosed C)
    (hconv : Convex ℝ C) {x g a : E} (hx : x ∈ C) :
    projectedLagrangianResidual C x g a = 0 ↔ ∀ y ∈ C, 0 ≤ ⟪g - a, y - x⟫ :=
  projectedStationarityResidual_eq_zero_iff hc hconv hx

/-- With equal objective and multiplier gradients, the Lagrangian gradient
vanishes while the printed projection subtracts their sum. -/
theorem printedProjectionSign_counterexample :
    projectedLagrangianResidual Set.univ (0 : ℝ) 1 1 = 0 ∧
      bestApprox Set.univ ((0 : ℝ) - 1 - 1) - 0 ≠ 0 := by
  have hproj (z : ℝ) : bestApprox Set.univ z = z :=
    (bestApprox_eq_iff Set.univ_nonempty isClosed_univ convex_univ).mpr
      ⟨Set.mem_univ z, by simp⟩
  norm_num [projectedLagrangianResidual, projectedStationarityResidual, hproj]

end ConnGouldToint.Chapter17
