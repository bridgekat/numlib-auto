import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

/-!
# Actual points on unsuccessful iteration blocks

A trajectory whose rejected steps preserve the point is constant on every
contiguous block containing no successful iteration.
-/

namespace EvaluationComplexity

/-- Rejection preserves the actual point throughout any block with no success. -/
theorem point_eq_of_no_success {E : Type*} {x : ℕ → E} {S : Set ℕ}
    (hrej : ∀ k, k ∉ S → x (k + 1) = x k) {i j : ℕ} (hij : i ≤ j)
    (hblock : ∀ k, i ≤ k → k < j → k ∉ S) : x j = x i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [hrej j (hblock j hj (Nat.lt_succ_self _))]
    exact ih (fun k hk hkj => hblock k hk (hkj.trans (Nat.lt_succ_self _)))

end EvaluationComplexity
