import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite counters with gated increments

A natural counter which increases by at most one at a pass stays bounded when every increase
requires its current value to be below a fixed real threshold. The counter may also stay
constant or decrease; no assumption on passes beyond the finite horizon is needed.
-/

namespace Optimization

/-- A counter starting at zero cannot exceed the ceiling of an increment threshold plus
one when every increase is at most one and starts strictly below that threshold. -/
theorem nat_count_le_ceil_of_increment_gate {count : ℕ → ℕ} {B : ℝ} {N : ℕ}
    (hzero : count 0 = 0) (hstep : ∀ k < N, count (k + 1) ≤ count k + 1)
    (hgate : ∀ k < N, count k < count (k + 1) → (count k : ℝ) < B) :
    count N ≤ ⌈B⌉₊ + 1 := by
  have hb : ∀ k ≤ N, count k ≤ ⌈B⌉₊ + 1 := by
    intro k hk
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      by_cases hi : count k < count (k + 1)
      · have hr := (hgate k (by omega) hi).le.trans (Nat.le_ceil B)
        have hn : count k ≤ ⌈B⌉₊ := by exact_mod_cast hr
        exact (hstep k (by omega)).trans (Nat.add_le_add_right hn 1)
      · exact (le_of_not_gt hi).trans (ih (by omega))
  exact hb N le_rfl

/-- The same finite increment gate gives a real-valued bound with a rounding allowance
of two. Nonnegativity of the real threshold is needed only for this rounding estimate. -/
theorem nat_count_le_real_of_increment_gate {count : ℕ → ℕ} {B : ℝ} {N : ℕ}
    (hzero : count 0 = 0) (hstep : ∀ k < N, count (k + 1) ≤ count k + 1)
    (hgate : ∀ k < N, count k < count (k + 1) → (count k : ℝ) < B)
    (hB : 0 ≤ B) :
    (count N : ℝ) ≤ B + 2 := by
  have hn := nat_count_le_ceil_of_increment_gate hzero hstep hgate
  have hr : (count N : ℝ) ≤ (⌈B⌉₊ : ℝ) + 1 := by exact_mod_cast hn
  have hc := Nat.ceil_lt_add_one hB
  linarith

end Optimization
