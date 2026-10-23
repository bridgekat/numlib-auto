import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Norm bounds for symmetric real bilinear forms

Real polarization and the parallelogram identity recover the full bilinear
operator norm bound from repeated-direction bounds, without completeness or a
finite-dimensional hypothesis.
-/

section Bilinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A symmetric real bilinear form has operator norm bounded by any nonnegative
constant bounding its diagonal by that constant times the squared norm. -/
theorem norm_bilinear_le_of_diagonal_bound (B : E →L[ℝ] E →L[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ v w, B v w = B w v) (hdiag : ∀ v, |B v v| ≤ C * ‖v‖ ^ 2) :
    ‖B‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro w hw
  have hid : 4 * B v w = B (v + w) (v + w) - B (v - w) (v - w) := by
    simp only [map_add, map_sub, add_apply,
      sub_apply]
    rw [hB w v]
    ring
  have hh := abs_sub (B (v + w) (v + w)) (B (v - w) (v - w))
  have hp := parallelogram_law_with_norm ℝ v w
  rw [hv, hw] at hp
  rw [← hid, abs_mul] at hh
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hh
  have hh1 := hdiag (v + w)
  have hh2 := hdiag (v - w)
  rw [Real.norm_eq_abs]
  nlinarith
end Bilinear

section Bilinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- For a symmetric real bilinear form, it suffices to bound its values on
repeated unit vectors to bound its full operator norm. -/
theorem norm_bilinear_le_of_unit_diagonal_bound (B : E →L[ℝ] E →L[ℝ] ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hB : ∀ v w, B v w = B w v)
    (hdiag : ∀ v, ‖v‖ = 1 → |B v v| ≤ C) : ‖B‖ ≤ C := by
  apply norm_bilinear_le_of_diagonal_bound B hC hB
  intro v
  by_cases hv : v = 0
  · simp [hv]
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
  have hvu : ‖v‖ • u = v := by
    simp [u, smul_smul, norm_ne_zero_iff.mpr hv]
  calc
    |B v v| = ‖v‖ ^ 2 * |B u u| := by
      have he : B v v = ‖v‖ ^ 2 * B u u := by
        calc B v v = B (‖v‖ • u) (‖v‖ • u) := congrArg (fun z => B z z) hvu.symm
          _ = _ := by simp only [map_smul, smul_apply, smul_eq_mul]; ring
      rw [he, abs_mul, abs_of_nonneg (sq_nonneg ‖v‖)]
    _ ≤ ‖v‖ ^ 2 * C := mul_le_mul_of_nonneg_left (hdiag u hu) (sq_nonneg _)
    _ = _ := by ring
end Bilinear
