/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Cumulative decrease with past reference iterates

Some model-based methods do not decrease the objective at every iteration. Instead, each transition
from iterate $k$ to iterate $k + 1$ decreases the value, measured from an earlier reference iterate
$r \le k$, by at least the sum of the prescribed decreases since $r$. This file shows that such a
condition still bounds the sum of all prescribed decreases by the total decrease of the value.

## Main results

* `Optimization.reference_decrease_sum`: if every transition pays the prescribed decreases
  accumulated since some earlier reference index, then $\sum_{i < n} c_i \le v_0 - v_n$.
-/

open scoped BigOperators

namespace Optimization

/-- Let $(v_k)_{k \ge 0}$ and $(c_k)_{k \ge 0}$ be real sequences. Suppose that for every $k$ there
is a reference index $r \le k$ with
$$\sum_{i = r}^{k} c_i \le v_r - v_{k+1}.$$
Then for every $n$,
$$\sum_{i = 0}^{n - 1} c_i \le v_0 - v_n.$$

No sign condition on the $c_i$ is needed. In the Lean statement, $v$ is `value` and $c$ is
`cost`. The proof is by strong induction on $n$: the condition at $k = n - 1$ reduces the claim
to the claim at the reference index $r$. -/
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
