import Numlib.Optimization.AdaptiveRegularizationComplexity

/-!
# Finite-prefix budgets for adaptive regularization

Only executed transitions contribute to a descent budget. No continuation after the final
inspection is required. A last successful transition can be charged separately when its
successor already satisfies a stopping test. Logarithmic parameter budgets are solved by
one scalar inequality, independently of the representation of trials and refinements.
-/

noncomputable section
namespace Optimization.ParameterUpdates

/-- A finite set of successful transitions consumes the objective gap. Only the executed
prefix must be nonincreasing, and only its endpoint needs a lower bound. -/
theorem successCount_le_of_finite_decrease {u : ℕ → ℝ} {low delta : ℝ}
    (success : ℕ → Prop) (hd : 0 < delta) (n : ℕ) (hlow : low ≤ u n)
    (hmono : ∀ k < n, u (k + 1) ≤ u k)
    (hdec : ∀ k < n, success k → delta ≤ u k - u (k + 1)) :
    (successCount success n : ℝ) ≤ (u 0 - low) / delta := by
  classical
  apply (le_div_iff₀ hd).mpr
  exact EvaluationComplexity.card_mul_le_gap (Finset.filter_subset _ _) hlow hmono
    (fun k hk => hdec k (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
      (Finset.mem_filter.mp hk).2)

/-- Successful transitions whose successors precede the endpoint consume the gap; the last
transition costs at most one extra success. No transition beyond the prefix is assumed. -/
theorem successCount_le_of_finite_successor_decrease {u : ℕ → ℝ} {low delta : ℝ}
    (success : ℕ → Prop) (hd : 0 < delta) (n : ℕ) (hlow : low ≤ u (n - 1))
    (hmono : ∀ k, k + 1 < n → u (k + 1) ≤ u k)
    (hdec : ∀ k, k + 1 < n → success k → delta ≤ u k - u (k + 1)) :
    (successCount success n : ℝ) ≤ (u 0 - low) / delta + 1 := by
  cases n with
  | zero =>
    have hb : 0 ≤ (u 0 - low) / delta := div_nonneg (sub_nonneg.mpr hlow) hd.le
    simp only [successCount, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]
    linarith
  | succ n =>
    have hb := successCount_le_of_finite_decrease success hd n hlow
      (fun k hk => hmono k (by omega)) (fun k hk => hdec k (by omega))
    have hc : (successCount success (n + 1) : ℝ) ≤
        (successCount success n : ℝ) + 1 := by
      exact_mod_cast successCount_succ_le success n
    linarith

/-- Solving the scalar logarithmic parameter budget bounds all trials by accepted trials
and the endpoint parameter bound. It applies equally when accuracy-only passes are present. -/
theorem trial_budget_of_log_budget (P : RegularizationParameters)
    {a t sigma0 sigmaN M : ℝ} (h0 : 0 < sigma0) (hN : 0 < sigmaN)
    (hM : sigmaN ≤ M)
    (hbudget : a * (Real.log P.gamma1 - Real.log P.gamma2) +
      t * Real.log P.gamma2 ≤ Real.log (sigmaN / sigma0)) :
    t ≤ a * (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (M / sigma0) / Real.log P.gamma2 := by
  have hm := Real.log_le_log (div_pos hN h0) (div_le_div_of_nonneg_right hM h0.le)
  have hg : 0 < Real.log P.gamma2 := Real.log_pos P.one_lt_gamma2
  rw [abs_of_neg (Real.log_neg P.gamma1_pos P.gamma1_lt_one)]
  apply (mul_le_mul_iff_left₀ hg).mp
  have he : (a * (1 + -Real.log P.gamma1 / Real.log P.gamma2) +
      Real.log (M / sigma0) / Real.log P.gamma2) * Real.log P.gamma2 =
      a * (Real.log P.gamma2 - Real.log P.gamma1) + Real.log (M / sigma0) := by
    field_simp
    ring
  rw [he]
  linarith

end Optimization.ParameterUpdates
