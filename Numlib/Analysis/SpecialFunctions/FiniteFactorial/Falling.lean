import Numlib.Analysis.SpecialFunctions.FiniteFactorial
/-!
# Falling products and shifted factorial quotients

Splitting genuine finite products identifies radial derivative coefficients
with the shifted-factorial ratios used for noninteger regularization powers.
-/

namespace Real
/-- A falling product splits the upper part of a shifted factorial. -/
theorem prod_falling_mul_shiftedFactorial (j k : ℕ) (β : ℝ) :
    (∏ i : Fin j, (((j + k : ℕ) : ℝ) + β - i)) * shiftedFactorial k β =
      shiftedFactorial (j + k) β := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Fin.prod_univ_succ]
    have hh : (∏ i : Fin j, (((j + 1 + k : ℕ) : ℝ) + β - (i.succ : ℕ))) =
        ∏ i : Fin j, (((j + k : ℕ) : ℝ) + β - i) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [Fin.val_succ]
      push_cast
      ring
    simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
    rw [hh, mul_assoc, ih, show j + 1 + k = (j + k) + 1 by omega]
    simp only [shiftedFactorial, Finset.prod_range_succ]
    push_cast
    ring
/-- The falling derivative coefficient is the positive-denominator shifted
factorial quotient, also at the integer endpoint beta one. -/
theorem prod_falling_eq_shiftedFactorial_div {j p : ℕ} (hj : j ≤ p)
    {β : ℝ} (hβ : 0 ≤ β) :
    (∏ i : Fin j, ((p : ℝ) + β - i)) = shiftedFactorial p β /
      shiftedFactorial (p-j) β := by
  apply (eq_div_iff (ne_of_gt (shiftedFactorial_pos _ hβ))).mpr
  simpa only [Nat.add_sub_of_le hj] using prod_falling_mul_shiftedFactorial j (p-j) β
end Real
