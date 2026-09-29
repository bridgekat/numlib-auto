/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.Normalize` and
`Mathlib.Analysis.InnerProductSpace.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Perturbing a direction and a rank-one projection

Two stability facts behind the perturbation of a Householder reflector `x ↦ x - 2 ⟪w, x⟫ w`:

* `NormedSpace.norm_normalize_sub_normalize_le`: the directions `a / ‖a‖` and `b / ‖b‖` of two
  nearby vectors are close, `‖b/‖b‖ - a/‖a‖‖ ≤ 2 ‖b - a‖ / ‖a‖` (with
  `NormedSpace.norm_normalize_le_one`, `‖x / ‖x‖‖ ≤ 1` also for `x = 0`);
* `norm_inner_smul_sub_inner_smul_le`: the rank-one maps `x ↦ ⟪a, x⟫ a` and `x ↦ ⟪b, x⟫ b` of two
  vectors of length at most one differ by at most `2 ‖b - a‖` in operator norm.
-/

open scoped RealInnerProductSpace

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A normalized vector has length at most one (one, or zero for the zero vector). -/
theorem norm_normalize_le_one (x : E) : ‖normalize x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (norm_normalize hx).le

/-- The directions of two nearby vectors are close: `‖b/‖b‖ - a/‖a‖‖ ≤ 2 ‖b - a‖ / ‖a‖`. -/
theorem norm_normalize_sub_normalize_le {a : E} (ha : a ≠ 0) (b : E) :
    ‖normalize b - normalize a‖ ≤ 2 * ‖b - a‖ / ‖a‖ := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [le_div_iff₀ hpos]
  have key : ‖a‖ • (normalize b - normalize a) = (b - a) + (‖a‖ - ‖b‖) • normalize b := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  have h1 : |‖a‖ - ‖b‖| ≤ ‖b - a‖ := by
    rw [norm_sub_rev]
    exact abs_norm_sub_norm_le a b
  have h2 : |‖a‖ - ‖b‖| * ‖normalize b‖ ≤ ‖b - a‖ :=
    (mul_le_of_le_one_right (abs_nonneg _) (norm_normalize_le_one b)).trans h1
  calc ‖normalize b - normalize a‖ * ‖a‖ = ‖‖a‖ • (normalize b - normalize a)‖ := by
        rw [norm_smul, norm_norm, mul_comm]
    _ ≤ ‖b - a‖ + |‖a‖ - ‖b‖| * ‖normalize b‖ := by
        rw [key]
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 2 * ‖b - a‖ := by linarith

end NormedSpace

/-- Two rank-one maps `x ↦ ⟪a, x⟫ a` of vectors of length at most one differ by at most
`2 ‖b - a‖` in operator norm. -/
theorem norm_inner_smul_sub_inner_smul_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a b : E} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (x : E) :
    ‖⟪b, x⟫ • b - ⟪a, x⟫ • a‖ ≤ 2 * ‖b - a‖ * ‖x‖ := by
  have hsplit : ⟪b, x⟫ • b - ⟪a, x⟫ • a = ⟪b - a, x⟫ • b + ⟪a, x⟫ • (b - a) := by
    rw [inner_sub_left, sub_smul, smul_sub]
    abel
  have h1 : |⟪b - a, x⟫| * ‖b‖ ≤ ‖b - a‖ * ‖x‖ :=
    (mul_le_mul (abs_real_inner_le_norm _ _) hb (norm_nonneg _) (by positivity)).trans_eq
      (mul_one _)
  have h2 : |⟪a, x⟫| * ‖b - a‖ ≤ ‖x‖ * ‖b - a‖ :=
    mul_le_mul_of_nonneg_right ((abs_real_inner_le_norm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg x) ha)) (norm_nonneg _)
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  linarith
