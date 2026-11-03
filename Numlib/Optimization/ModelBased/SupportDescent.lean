import Numlib.Analysis.InnerProductSpace.ConvexProjection
import Numlib.Analysis.Convex.Duality.Support
import Mathlib.Tactic.Linarith

/-! # Descent directions of a support function -/

open Metric ConvexAnalysis
open scoped RealInnerProductSpace

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The negative unit vector along a vector, with value zero at zero. -/
noncomputable def negativeUnit (g : E) : E :=
  (-‖g‖⁻¹) • g

theorem norm_negativeUnit_le_one (g : E) : ‖negativeUnit g‖ ≤ 1 := by
  by_cases hg : g = 0
  · simp [hg, negativeUnit]
  have hpos := norm_pos_iff.mpr hg
  rw [negativeUnit, norm_smul, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']

section Complete

variable [CompleteSpace E] {K : Set E} (hne : K.Nonempty) (hclosed : IsClosed K)
  (hconv : Convex ℝ K)
include hne hclosed hconv

theorem neg_norm_bestApprox_le_supportFn {d : E} (hd : ‖d‖ ≤ 1) :
    ((-‖bestApprox K 0‖ : ℝ) : EReal) ≤ supportFn (innerₗ E) K d := by
  let g := bestApprox K 0
  have hg : g ∈ K := bestApprox_mem hne hclosed hconv _
  refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (le_supportFn hg d)
  rw [innerₗ_apply_apply]
  have h := (neg_le_abs ⟪g, d⟫).trans
    ((abs_real_inner_le_norm g d).trans (mul_le_of_le_one_right (norm_nonneg g) hd))
  linarith

/-- The direction opposite the nearest point to zero attains the sharp support bound. -/
theorem supportFn_negativeUnit_bestApprox :
    supportFn (innerₗ E) K (negativeUnit (bestApprox K 0)) =
      ((-‖bestApprox K 0‖ : ℝ) : EReal) := by
  refine le_antisymm ?_ (neg_norm_bestApprox_le_supportFn hne hclosed hconv
    (norm_negativeUnit_le_one _))
  apply supportFn_le_coe_iff.mpr
  intro z hz
  let g := bestApprox K 0
  change ⟪z, negativeUnit g⟫ ≤ -‖g‖
  by_cases hg : g = 0
  · simp [hg, negativeUnit]
  have hpos := norm_pos_iff.mpr hg
  have hr := inner_sub_bestApprox_le_zero hne hclosed hconv (0 : E) z hz
  change ⟪0 - g, z - g⟫ ≤ 0 at hr
  rw [zero_sub, inner_neg_left, neg_nonpos, inner_sub_right, sub_nonneg,
    real_inner_self_eq_norm_sq, real_inner_comm z g] at hr
  rw [negativeUnit, real_inner_smul_right]
  calc
    _ ≤ (-‖g‖⁻¹) * ‖g‖ ^ 2 :=
      mul_le_mul_of_nonpos_left hr (neg_nonpos.mpr (inv_nonneg.mpr hpos.le))
    _ = _ := by rw [pow_two, ← mul_assoc, neg_mul, inv_mul_cancel₀ hpos.ne', neg_one_mul]

/-- The least support value over the closed unit ball is minus the distance to the set. -/
theorem supportFn_isLeast_closedBall :
    IsLeast (supportFn (innerₗ E) K '' closedBall 0 1) ((-‖bestApprox K 0‖ : ℝ) : EReal) := by
  refine ⟨?_, ?_⟩
  · exact ⟨negativeUnit (bestApprox K 0),
      mem_closedBall_zero_iff.mpr (norm_negativeUnit_le_one _),
      supportFn_negativeUnit_bestApprox hne hclosed hconv⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact neg_norm_bestApprox_le_supportFn hne hclosed hconv (mem_closedBall_zero_iff.mp hd)

end Complete
end Optimization
