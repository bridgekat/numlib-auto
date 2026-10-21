import Numlib.Analysis.Calculus.BoundedJetInterpolation

/-!
# Bounded extensions of affine segments

A fixed bounded smooth transition extends finite affine segments without enlarging the
second derivative bound according to the length of the segment.
-/
noncomputable section
open scoped NNReal
namespace BoundedAffineExtension

/-- A fixed bounded C² transition interpolates a unit affine jet and a stationary endpoint. -/
theorem exists_transition : ∃ B : ℝ≥0, ∃ R : ℝ → ℝ,
    ContDiff ℝ 2 R ∧ (∀ j ≤ 2, ∀ t, |iteratedDeriv j R t| ≤ B) ∧
    R 0 = 0 ∧ deriv R 0 = 1 ∧ deriv (deriv R) 0 = 0 ∧
    R 1 = 1 ∧ deriv R 1 = 0 ∧ deriv (deriv R) 1 = 0 := by
  obtain ⟨_, B, hi⟩ := Hermite.exists_contDiff_bounded_of_unit_knots 2 1 (by norm_num)
  let a : ℕ → ℕ → ℝ := fun i j => if j = 0 then (i : ℝ) else
    if j = 1 ∧ i = 0 then 1 else 0
  obtain ⟨R, hR, _, hj, hb⟩ := hi 1 (by omega) a (by
    intro i hi j _
    interval_cases i <;> simp [a] <;> split_ifs <;> norm_num)
  refine ⟨B, R, hR, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | simpa [a, iteratedDeriv_succ, iteratedDeriv_zero] using hj 0 (by omega) 0 (by omega)
    | simpa [a, iteratedDeriv_succ, iteratedDeriv_zero] using hj 0 (by omega) 1 (by omega)
    | simpa [a, iteratedDeriv_succ, iteratedDeriv_zero] using hj 0 (by omega) 2 (by omega)
    | simpa [a, iteratedDeriv_succ, iteratedDeriv_zero] using hj 1 (by omega) 0 (by omega)
    | simpa [a, iteratedDeriv_succ, iteratedDeriv_zero] using hj 1 (by omega) 1 (by omega)
    | simpa [a, iteratedDeriv_succ, iteratedDeriv_zero] using hj 1 (by omega) 2 (by omega)

/-- A transition transported to an interval with signed width. -/
def scaled (R : ℝ → ℝ) (a b c x : ℝ) : ℝ := b + a * R ((x - c) / a)

/-- Smoothness is preserved by affine transport. -/
theorem scaled_contDiff {R : ℝ → ℝ} (hR : ContDiff ℝ 2 R) (a b c : ℝ) :
    ContDiff ℝ 2 (scaled R a b c) := by
  fun_prop [scaled]

/-- The derivative of an affinely transported transition. -/
theorem deriv_scaled {R : ℝ → ℝ} (hR : ContDiff ℝ 2 R) {a : ℝ} (ha : a ≠ 0)
    (b c x : ℝ) : deriv (scaled R a b c) x = deriv R ((x - c) / a) := by
  have hd : Differentiable ℝ R := hR.differentiable (by norm_num)
  have hh := (((hd ((x - c) / a)).hasDerivAt.comp x
    (((hasDerivAt_id x).sub_const c).div_const a)).const_mul a).const_add b
  convert hh.deriv using 1 <;> first | rfl | field_simp

/-- The second derivative of an affinely transported transition. -/
theorem deriv_deriv_scaled {R : ℝ → ℝ} (hR : ContDiff ℝ 2 R) {a : ℝ} (ha : a ≠ 0)
    (b c x : ℝ) : deriv (deriv (scaled R a b c)) x = deriv (deriv R) ((x - c) / a) / a := by
  have hd : Differentiable ℝ (deriv R) := by
    simpa only [iteratedDeriv_one] using hR.differentiable_iteratedDeriv 1 (by norm_num)
  rw [show deriv (scaled R a b c) = fun x => deriv R ((x - c) / a) from
    funext (deriv_scaled hR ha b c)]
  convert ((hd ((x - c) / a)).hasDerivAt.comp x
    (((hasDerivAt_id x).sub_const c).div_const a)).deriv using 1 <;>
      simp [div_eq_mul_inv, Function.comp_def]

/-- An affine interval has a bounded C² extension with second derivative controlled by the
reciprocal transition width. The constants do not depend on the interval length. -/
theorem exists_extension : ∃ B : ℝ≥0, ∀ h l : ℝ, 0 < h → 0 ≤ l →
    ∃ c : ℝ → ℝ, ContDiff ℝ 2 c ∧
      (∀ x ∈ Set.Icc 0 l, c x = x ∧ deriv c x = 1 ∧ deriv (deriv c) x = 0) ∧
      c (l + h) = l + h ∧ deriv c (l + h) = 0 ∧ deriv (deriv c) (l + h) = 0 ∧
      (∀ x, |c x| ≤ l + h * B) ∧
      (∀ x, |deriv (deriv c) x| ≤ B / h) := by
  obtain ⟨B, R, hR, hb, hR0, hR'0, hR''0, hR1, hR'1, hR''1⟩ := exists_transition
  refine ⟨B, ?_⟩
  intro h l hh hl
  let left := scaled R (-h) 0 0
  let right := scaled R h l l
  have hn : -h ≠ 0 := neg_ne_zero.mpr hh.ne'
  have hj0 (j : ℕ) (hj : j ≤ 2) : iteratedDeriv j left 0 = iteratedDeriv j id 0 := by
    interval_cases j <;>
      simp [left, scaled, iteratedDeriv_succ, iteratedDeriv_zero,
        deriv_scaled hR hn, deriv_deriv_scaled hR hn, hR0, hR'0, hR''0]
  have hjl (j : ℕ) (hj : j ≤ 2) : iteratedDeriv j id l = iteratedDeriv j right l := by
    interval_cases j <;>
      simp [right, scaled, iteratedDeriv_succ, iteratedDeriv_zero,
        deriv_scaled hR hh.ne', deriv_deriv_scaled hR hh.ne', hR0, hR'0, hR''0]
  have h1 := contDiff_joinAt_of_matching_jets (contDiff_id (𝕜 := ℝ))
    (scaled_contDiff hR h l l) hjl
  let d := joinAt l id right
  have hjd (j : ℕ) (hj : j ≤ 2) : iteratedDeriv j left 0 = iteratedDeriv j d 0 := by
    rw [h1.2 j hj]
    simpa [d, joinAt_of_le _ _ hl] using hj0 j hj
  have h0 := contDiff_joinAt_of_matching_jets (scaled_contDiff hR (-h) 0 0) h1.1 hjd
  let c := joinAt 0 left d
  have hcjet (j : ℕ) (hj : j ≤ 2) (x : ℝ) :
      iteratedDeriv j c x = joinAt 0 (iteratedDeriv j left)
        (joinAt l (iteratedDeriv j id) (iteratedDeriv j right)) x := by
    rw [h0.2 j hj, h1.2 j hj]
  have hcmid (j : ℕ) (hj : j ≤ 2) {x : ℝ} (hx : x ∈ Set.Icc 0 l) :
      iteratedDeriv j c x = iteratedDeriv j id x := by
    rw [hcjet j hj x, joinAt_of_ge (by
      rw [joinAt_of_le _ _ hl]
      exact hj0 j hj) hx.1, joinAt_of_le _ _ hx.2]
  have hcend (j : ℕ) (hj : j ≤ 2) :
      iteratedDeriv j c (l + h) = iteratedDeriv j right (l + h) := by
    rw [hcjet j hj, joinAt_of_gt _ _ (by linarith), joinAt_of_gt _ _ (by linarith)]
  refine ⟨c, h0.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hcmid 0 (by omega) hx, by simpa using hcmid 1 (by omega) hx,
      by simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hcmid 2 le_rfl hx⟩
  · simpa [right, scaled, hh.ne', hR1] using hcend 0 (by omega)
  · simpa [right, iteratedDeriv_succ, iteratedDeriv_zero,
      deriv_scaled hR hh.ne', hh.ne', hR'1] using hcend 1 (by omega)
  · simpa [right, iteratedDeriv_succ, iteratedDeriv_zero,
      deriv_deriv_scaled hR hh.ne', hh.ne', hR''1] using hcend 2 le_rfl
  · intro x
    change |joinAt 0 left d x| ≤ _
    by_cases hx : x ≤ 0
    · rw [joinAt_of_le _ _ hx]
      have hhB := mul_le_mul_of_nonneg_left (hb 0 (by omega) (-x / h)) hh.le
      dsimp [left, scaled]
      simpa only [zero_add, abs_mul, abs_neg, abs_of_pos hh, iteratedDeriv_zero,
        sub_zero, div_neg, neg_div] using hhB.trans
        (show h * (B : ℝ) ≤ l + h * B by linarith)
    · rw [joinAt_of_gt _ _ (lt_of_not_ge hx)]
      change |joinAt l id right x| ≤ _
      by_cases hxl : x ≤ l
      · rw [joinAt_of_le _ _ hxl, id_eq, abs_of_pos (lt_of_not_ge hx)]
        linarith [mul_nonneg hh.le B.coe_nonneg]
      · rw [joinAt_of_gt _ _ (lt_of_not_ge hxl)]
        dsimp [right, scaled]
        have hhB := mul_le_mul_of_nonneg_left (hb 0 (by omega) ((x - l) / h)) hh.le
        exact (abs_add_le _ _).trans (by
          simp only [iteratedDeriv_zero] at hhB
          rw [abs_of_nonneg hl, abs_mul, abs_of_pos hh]
          linarith)
  · intro x
    have heq := hcjet 2 le_rfl x
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at heq
    rw [heq]
    by_cases hx : x ≤ 0
    · rw [joinAt_of_le _ _ hx, deriv_deriv_scaled hR hn]
      simp only [abs_div, abs_neg, abs_of_pos hh]
      apply div_le_div_of_nonneg_right _ hh.le
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        (hb 2 le_rfl ((x - 0) / (-h)))
    · rw [joinAt_of_gt _ _ (lt_of_not_ge hx)]
      by_cases hxl : x ≤ l
      · simp [joinAt_of_le _ _ hxl, div_nonneg B.coe_nonneg hh.le]
      · rw [joinAt_of_gt _ _ (lt_of_not_ge hxl), deriv_deriv_scaled hR hh.ne']
        simp only [abs_div, abs_of_pos hh]
        apply div_le_div_of_nonneg_right _ hh.le
        simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
          (hb 2 le_rfl ((x - l) / h))

end BoundedAffineExtension
