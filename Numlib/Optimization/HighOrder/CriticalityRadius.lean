import Numlib.Optimization.HighOrder.CriticalityApproximate

/-!
# Unit-radius consequences of low-order normalized Taylor criticality

First-order criticality scales linearly. For quadratic criticality, orienting
a displacement to make its linear term nonpositive can only improve the
model decrement. The normalized decrease at a smaller radius then controls
the actual unit-radius measure. No analogous statement is assumed at higher
orders.
-/

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

omit [ProperSpace E] in
/-- A quadratic Taylor displacement can be oriented to have nonpositive
linear term while preserving its norm and improving its actual decrement. -/
theorem exists_quadratic_decrement_orientation (f : E → ℝ) (x u : E) :
    ∃ v : E, ‖v‖ = ‖u‖ ∧ inner ℝ (gradient f x) v ≤ 0 ∧
      decrement f 2 x u ≤ decrement f 2 x v := by
  by_cases hu : inner ℝ (gradient f x) u ≤ 0
  · exact ⟨u, rfl, hu, le_rfl⟩
  · refine ⟨-u, norm_neg _, ?_, ?_⟩
    · rw [inner_neg_right]
      linarith
    · have hp := decrement_two_smul f x u 1
      have hm := decrement_two_smul f x u (-1)
      simp only [one_smul, neg_one_smul, one_pow, one_mul] at hp hm
      norm_num only at hm
      linarith

omit [ProperSpace E] in
/-- A quadratic decrement with nonpositive linear term has normalized
small-radius decrease at least as large as its unit-scale decrement. -/
theorem mul_sq_decrement_two_le (f : E → ℝ) (x v : E) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hg : inner ℝ (gradient f x) v ≤ 0) :
    δ ^ 2 * decrement f 2 x v ≤ decrement f 2 x (δ • v) := by
  have hp := decrement_two_smul f x v 1
  have hm := decrement_two_smul f x v δ
  simp only [one_smul, one_pow, one_mul] at hp
  have hd : 0 ≤ δ - δ ^ 2 := by nlinarith
  nlinarith [mul_nonneg hd (neg_nonneg.mpr hg)]

/-- The actual quadratic unit-radius measure is bounded by the normalized
measure on every smaller nonnegative ball, including radius zero. -/
theorem sq_mul_criticality_two_one_le (f : E → ℝ) (x : E) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ ^ 2 * criticality f 2 x 1 ≤ criticality f 2 x δ := by
  obtain ⟨u, hu, hcrit⟩ := exists_decrement_eq_criticality f 2 x (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨v, hv, hg, hdecr⟩ := exists_quadratic_decrement_orientation f x u
  have hfeas : ‖δ • v‖ ≤ δ := by
    rw [norm_smul, Real.norm_of_nonneg hδ, hv]
    exact mul_le_of_le_one_right hδ hu
  calc
    _ = δ ^ 2 * decrement f 2 x u := by rw [hcrit]
    _ ≤ δ ^ 2 * decrement f 2 x v := mul_le_mul_of_nonneg_left hdecr (sq_nonneg _)
    _ ≤ decrement f 2 x (δ • v) := mul_sq_decrement_two_le f x v hδ hδ1 hg
    _ ≤ _ := decrement_le_criticality f 2 x hfeas

/-- A normalized first-order test at any positive radius certifies its
unit-radius version with the same requested accuracy. -/
theorem criticality_one_unit_le_of_radius (f : E → ℝ) (x : E) {δ ε : ℝ}
    (hδ : 0 < δ) (h : criticality f 1 x δ ≤ ε * δ) : criticality f 1 x 1 ≤ ε := by
  rw [criticality_one f x hδ] at h
  rw [criticality_one f x zero_lt_one, one_mul]
  nlinarith

/-- A normalized quadratic test at any positive radius at most one certifies
the unit-radius version with the same requested accuracy. -/
theorem criticality_two_unit_le_of_radius (f : E → ℝ) (x : E) {δ ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : criticality f 2 x δ ≤ ε * δ ^ 2 / 2) : criticality f 2 x 1 ≤ ε / 2 := by
  have hh := (sq_mul_criticality_two_one_le f x hδ.le hδ1).trans h
  have hp := sq_pos_of_pos hδ
  nlinarith

/-- In orders one and two, true normalized criticality at an actual smaller
radius always implies the source unit-radius approximate-optimality test. -/
theorem criticality_unit_le_of_radius (f : E → ℝ) (x : E) {j : ℕ}
    (hj : 1 ≤ j) (hj2 : j ≤ 2) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : criticality f j x δ ≤ ε * δ ^ j / j.factorial) :
    criticality f j x 1 ≤ ε / j.factorial := by
  have hcases : j = 1 ∨ j = 2 := by omega
  rcases hcases with rfl | rfl
  · norm_num at h ⊢
    exact criticality_one_unit_le_of_radius f x hδ h
  · norm_num at h ⊢
    exact criticality_two_unit_le_of_radius f x hδ hδ1 h

end TaylorModel
