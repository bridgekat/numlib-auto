import NumlibSurface.CartisGouldToint.AppendixA.Section08

/-!
# Finite-product factorial quotients

The book's fractional factorial is positive and its quotients are falling products.
-/

namespace CartisGouldToint.AppendixA.Section08

/-- Every factor of the fractional factorial is positive for a positive fractional part. -/
theorem fractionalFactorial_pos {β : ℝ} (hβ : 0 < β) (p : ℕ) :
    0 < fractionalFactorial p β := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [fractionalFactorial_succ]
    exact mul_pos ih (by positivity)

/-- Cancelling the last factors of the book's finite factorial leaves a falling product. -/
theorem fallingProduct_eq_fractionalFactorial_div {β : ℝ} (hβ : 0 < β)
    {p j : ℕ} (hj : j ≤ p) :
    (∏ i : Fin j, ((p : ℝ) + β - i)) =
      fractionalFactorial p β / fractionalFactorial (p - j) β := by
  have hmul : ∀ j ≤ p, fractionalFactorial (p - j) β *
      (∏ i : Fin j, ((p : ℝ) + β - i)) = fractionalFactorial p β := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hrec : fractionalFactorial (p - j) β =
          fractionalFactorial (p - (j + 1)) β * ((p : ℝ) + β - j) := by
        rw [show p - j = (p - (j + 1)) + 1 by omega, fractionalFactorial_succ]
        congr 1
        rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : j + 1 ≤ p)]
        push_cast
        ring
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [← mul_assoc, mul_right_comm, ← hrec]
      exact ih (by omega)
  apply (eq_div_iff (fractionalFactorial_pos hβ _).ne').mpr
  simpa only [mul_comm] using hmul j hj

end CartisGouldToint.AppendixA.Section08
