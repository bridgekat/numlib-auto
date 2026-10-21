import Numlib.Optimization.ParameterUpdates
import Numlib.Optimization.EvaluationComplexity

/-!
# Evaluation budgets for adaptive regularization

Every successful step whose successor has not terminated pays a positive objective decrease.
Telescoping bounds the accepted steps, with one extra step for the last successor. Shared
parameter updates then bound all trials and produce the first successful termination test.
-/
noncomputable section
namespace Optimization.ParameterUpdates

/-- Adding one trial adds at most one success. -/
theorem successCount_succ_le (success : ℕ → Prop) (n : ℕ) :
    successCount success (n + 1) ≤ successCount success n + 1 := by
  classical
  simp only [successCount, Finset.range_add_one, Finset.filter_insert]
  split_ifs <;> simp

variable {p : RegularizationParameters} {rho sigma u : ℕ → ℝ} {P : ℕ → Prop}
    {low delta : ℝ}

/-- Successful trials with untested successors consume the finite objective budget. -/
theorem successCount_le_of_successor_decrease
    (success : ℕ → Prop) (hd : 0 < delta)
    (hmono : ∀ k, u (k + 1) ≤ u k)
    (hdec : ∀ k, success k → ¬P (k + 1) → delta ≤ u k - u (k + 1))
    (n : ℕ) (hlow : low ≤ u n) (htest : ∀ j ≤ n, ¬P j) :
    (successCount (success) n : ℝ) ≤ (u 0 - low) / delta := by
  classical
  exact (le_div_iff₀ hd).mpr (EvaluationComplexity.card_mul_le_gap
    (Finset.filter_subset (success) (Finset.range n)) hlow
    (fun k _ => hmono k) (fun k hk => hdec k (Finset.mem_filter.mp hk).2
      (htest (k + 1) (by have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1; omega))))

/-- At most one accepted trial has a successor outside the failed-test prefix. -/
theorem successCount_before_test_le_of_successor_decrease
    (success : ℕ → Prop) (hd : 0 < delta)
    (hlow : ∀ k, low ≤ u k) (hmono : ∀ k, u (k + 1) ≤ u k)
    (hdec : ∀ k, success k → ¬P (k + 1) → delta ≤ u k - u (k + 1))
    (n : ℕ) (htest : ∀ j < n, ¬P j) :
    (successCount (success) n : ℝ) ≤ (u 0 - low) / delta + 1 := by
  cases n with
  | zero =>
    simp only [successCount, Finset.range_zero, Finset.filter_empty, Finset.card_empty,
      Nat.cast_zero]
    have := div_nonneg (sub_nonneg.mpr (hlow 0)) hd.le
    linarith
  | succ n =>
    have hb := successCount_le_of_successor_decrease success hd hmono hdec n (hlow n)
      (fun j hj => htest j (by omega))
    have hc : (successCount (success) (n + 1) : ℝ) ≤
        (successCount (success) n : ℝ) + 1 := by
      exact_mod_cast successCount_succ_le (success) n
    linarith

/-- Finite objective decrease and bounded regularization parameters force first termination.
Initialization costs one function and derivative call; accepted trials reuse cached derivatives. -/
theorem RegularizationUpdates.exists_first_with_cost
    (h : RegularizationUpdates p rho sigma) {M : ℝ} (hM : ∀ k, sigma k ≤ M)
    (hd : 0 < delta) (hlow : ∀ k, low ≤ u k) (hmono : ∀ k, u (k + 1) ≤ u k)
    (hdec : ∀ k, p.eta1 ≤ rho k → ¬P (k + 1) → delta ≤ u k - u (k + 1)) :
    let C := 1 + |Real.log p.gamma1| / Real.log p.gamma2
    let D := Real.log (M / sigma 0) / Real.log p.gamma2
    ∃ K : ℕ, P K ∧ (∀ j < K, ¬P j) ∧
      (K : ℝ) + 1 ≤ C * ((u 0 - low) / delta) + C + D + 1 ∧
      (successCount (fun k => p.eta1 ≤ rho k) K : ℝ) + 1 ≤ (u 0 - low) / delta + 2 := by
  dsimp only
  let C := 1 + |Real.log p.gamma1| / Real.log p.gamma2
  have hC : 0 ≤ C := add_nonneg zero_le_one
    (div_nonneg (abs_nonneg _) (Real.log_pos p.one_lt_gamma2).le)
  have hprefix : ∀ n, (∀ j < n, ¬P j) →
      (n : ℝ) ≤ ((u 0 - low) / delta + 1) * C +
        Real.log (M / sigma 0) / Real.log p.gamma2 := by
    intro n hn
    have ht := h.total_count_le n (hM n)
    have hb := mul_le_mul_of_nonneg_right
      (successCount_before_test_le_of_successor_decrease
        (fun k => p.eta1 ≤ rho k) hd hlow hmono hdec n hn) hC
    change (n : ℝ) ≤ (successCount _ n : ℝ) * C + _ at ht
    linarith
  obtain ⟨K, _, hk, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hprefix
  refine ⟨K, hk, hfirst, ?_, ?_⟩
  · dsimp [C] at hprefix
    nlinarith [hprefix K hfirst]
  · linarith [successCount_before_test_le_of_successor_decrease
      (fun k => p.eta1 ≤ rho k) hd hlow hmono hdec K hfirst]

end Optimization.ParameterUpdates
