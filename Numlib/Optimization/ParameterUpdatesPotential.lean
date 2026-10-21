import Numlib.Optimization.HigherOrderRegularizationComplexity

/-!
# Accepted trials and scalar potential budgets

An independent nonnegative potential can bound accepted trials even when the acceptance
ratio is defined by a different objective. The last accepted trial is counted separately.
-/

namespace Optimization.ParameterUpdates

/-- A nonnegative decreasing scalar potential bounds the number of accepted trials before
first quality, allowing one final accepted trial whose successor already passes the test. -/
theorem successCount_le_of_potential {N : ℕ} {accepted P : ℕ → Prop}
    {u : ℕ → ℝ} {delta : ℝ} (hd : 0 < delta)
    (hlow : ∀ k ≤ N, 0 ≤ u k) (hmono : ∀ k < N, u (k + 1) ≤ u k)
    (hdec : ∀ k < N, accepted k → ¬P (k + 1) → delta ≤ u k - u (k + 1))
    (hfirst : ∀ k < N, ¬P k) :
    (successCount accepted N : ℝ) ≤ u 0 / delta + 1 := by
  classical
  cases N with
  | zero =>
    simp only [successCount, Finset.range_zero, Finset.filter_empty, Finset.card_empty,
      Nat.cast_zero]
    exact le_add_of_nonneg_of_le (div_nonneg (hlow 0 le_rfl) hd.le) zero_le_one
  | succ n =>
    have hb : (successCount accepted n : ℝ) ≤ u 0 / delta := by
      apply (le_div_iff₀ hd).mpr
      have hc := EvaluationComplexity.card_mul_le_gap (u := u) (n := n)
        (S := (Finset.range n).filter accepted) (low := 0) (δ := delta)
        (Finset.filter_subset _ _) (hlow n (by omega))
        (fun k hk => hmono k (by omega))
        (fun k hk => hdec k
          (by have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1; omega)
          (Finset.mem_filter.mp hk).2
          (hfirst (k + 1)
            (by have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1; omega)))
      simpa only [successCount, sub_zero] using hc
    have hs : (successCount accepted (n + 1) : ℝ) ≤
        (successCount accepted n : ℝ) + 1 := by exact_mod_cast successCount_succ_le accepted n
    linarith

end Optimization.ParameterUpdates
