import Numlib.Analysis.InnerProductSpace.NormPow.Second
/-!
# Sharp Hessian norm bound for real radial powers above two

The exact radial coefficient applies also to fractional exponents between two
and four, with the actual zero Hessian at the origin handled explicitly.
-/

namespace NormPower
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The exact radial Hessian norm bound has coefficient `a(a - 1)`. -/
theorem norm_second_le_of_two_lt {a : ℝ} (ha : 2 < a) (s : E) :
    ‖second a s‖ ≤ a * (a - 1) * ‖s‖ ^ (a - 2) := by
  by_cases hs : s = 0
  · subst s
    have hz : ‖second a (0 : E)‖ = 0 := by
      rw [second_zero_of_two_lt ha]
      exact ContinuousLinearMap.opNorm_zero
    rw [hz]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith))
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hpow : ‖s‖ ^ (a - 4) * ‖s‖ ^ 2 = ‖s‖ ^ (a - 2) := by
    rw [←Real.rpow_natCast, ←Real.rpow_add hr]
    congr 1
    norm_num
    ring
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hJ : ‖J‖ ≤ 1 := norm_innerSL_le ℝ
  have hR : ‖(innerSL ℝ s).smulRight (innerSL ℝ s)‖ = ‖s‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    ring
  have houter := ContinuousLinearMap.opNorm_smul_le a
    (‖s‖ ^ (a - 2) • J +
      ((a - 2) * ‖s‖ ^ (a - 4)) • (innerSL ℝ s).smulRight (innerSL ℝ s))
  rw [Real.norm_of_nonneg (by linarith : 0 ≤ a)] at houter
  change ‖a • (‖s‖ ^ (a - 2) • J +
    ((a - 2) * ‖s‖ ^ (a - 4)) • (innerSL ℝ s).smulRight (innerSL ℝ s))‖ ≤ _
  have hA := ContinuousLinearMap.opNorm_smul_le (‖s‖ ^ (a - 2)) J
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg s) _)] at hA
  have hA' : ‖‖s‖ ^ (a - 2) • J‖ ≤ ‖s‖ ^ (a - 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg (norm_nonneg s) (a - 2))]
  have hR' := ContinuousLinearMap.opNorm_smul_le ((a - 2) * ‖s‖ ^ (a - 4))
    ((innerSL ℝ s).smulRight (innerSL ℝ s))
  rw [Real.norm_of_nonneg
    (mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg s) _)), hR] at hR'
  have hsum := norm_add_le (‖s‖ ^ (a - 2) • J)
    (((a - 2) * ‖s‖ ^ (a - 4)) • (innerSL ℝ s).smulRight (innerSL ℝ s))
  have he : (a - 2) * ‖s‖ ^ (a - 4) * ‖s‖ ^ 2 = (a - 2) * ‖s‖ ^ (a - 2) := by
    rw [mul_assoc, hpow]
  rw [he] at hR'
  have hsum' : ‖‖s‖ ^ (a - 2) • J +
      ((a - 2) * ‖s‖ ^ (a - 4)) • (innerSL ℝ s).smulRight (innerSL ℝ s)‖ ≤
        (a - 1) * ‖s‖ ^ (a - 2) := by linarith
  nlinarith [houter, mul_le_mul_of_nonneg_left hsum' (by linarith : 0 ≤ a)]


end NormPower
