/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Cumulative decrease with past reference iterates -/

open scoped BigOperators

namespace Optimization

/-- If every transition pays the accumulated decrease since some reference index,
the initial value bounds the sum of all prescribed decreases. -/
theorem reference_decrease_sum (value cost : ℕ → ℝ)
    (h : ∀ k, ∃ r ≤ k, (∑ i ∈ Finset.Ico r (k + 1), cost i) ≤ value r - value (k + 1))
    (n : ℕ) : (∑ i ∈ Finset.range n, cost i) ≤ value 0 - value n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ k =>
      obtain ⟨r, hr, hstep⟩ := h k
      have hprefix := ih r (Nat.lt_succ_of_le hr)
      rw [Finset.sum_Ico_eq_sub _ (hr.trans (Nat.le_succ k))] at hstep
      linarith

end Optimization
