/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Fin.SuccPred`, beside `Fin.succAbove_of_castSucc_lt`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Fin.SuccPred

/-!
# The value of `Fin.succAbove`

For $k \in \{0, \dots, n\}$, the map `Fin.succAbove k` is the order embedding $\sigma_k$ of
$\{0, \dots, n - 1\}$ into $\{0, \dots, n\}$ whose image misses $k$. Its value is $\sigma_k(j) = j$
for $j < k$ and $\sigma_k(j) = j + 1$ for $j \ge k$, so that always $j \le \sigma_k(j) \le j + 1$.
When column $k$ of a matrix is deleted, the remaining columns are reindexed by $\sigma_k$, and these
bounds say how far a column moves.

## Main results

* `Fin.val_succAbove_le`: $\sigma_k(j) \le j + 1$.
* `Fin.le_val_succAbove`: $j \le \sigma_k(j)$.
* `Fin.val_succAbove_of_lt`: if $j < k$, then $\sigma_k(j) = j$.
* `Fin.val_succAbove_of_le`: if $k \le j$, then $\sigma_k(j) = j + 1$.

## Implementation notes

* The statements are about the natural-number values of elements of `Fin`, the form that `omega`
  uses. They are the arithmetic forms of Mathlib's `Fin.succAbove_of_castSucc_lt` and
  `Fin.succAbove_of_le_castSucc`.
-/

namespace Fin

variable {n : ℕ}

/-- Let $k \in \{0, \dots, n\}$ and $j \in \{0, \dots, n - 1\}$, and let $\sigma_k(j)$ be the value
of `Fin.succAbove k j`. Then $$\sigma_k(j) \le j + 1.$$
-/
theorem val_succAbove_le (k : Fin (n + 1)) (j : Fin n) : (k.succAbove j : ℕ) ≤ j + 1 := by
  unfold Fin.succAbove
  split_ifs <;> simp

/-- Let $k \in \{0, \dots, n\}$ and $j \in \{0, \dots, n - 1\}$, and let $\sigma_k(j)$ be the value
of `Fin.succAbove k j`. Then $$j \le \sigma_k(j).$$
-/
theorem le_val_succAbove (k : Fin (n + 1)) (j : Fin n) : (j : ℕ) ≤ k.succAbove j := by
  unfold Fin.succAbove
  split_ifs <;> simp

/-- Let $k \in \{0, \dots, n\}$ and $j \in \{0, \dots, n - 1\}$, and let $\sigma_k(j)$ be the value
of `Fin.succAbove k j`. If $j < k$, then $$\sigma_k(j) = j.$$
-/
theorem val_succAbove_of_lt {k : Fin (n + 1)} {j : Fin n} (h : (j : ℕ) < k) :
    (k.succAbove j : ℕ) = j := by
  rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), Fin.val_castSucc]

/-- Let $k \in \{0, \dots, n\}$ and $j \in \{0, \dots, n - 1\}$, and let $\sigma_k(j)$ be the value
of `Fin.succAbove k j`. If $k \le j$, then $$\sigma_k(j) = j + 1.$$
-/
theorem val_succAbove_of_le {k : Fin (n + 1)} {j : Fin n} (h : (k : ℕ) ≤ j) :
    (k.succAbove j : ℕ) = j + 1 := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h), Fin.val_succ]

end Fin
