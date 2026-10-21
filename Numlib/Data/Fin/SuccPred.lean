/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Fin.SuccPred`, beside `Fin.succAbove_of_castSucc_lt`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Fin.SuccPred

/-!
# The value of `Fin.succAbove`

`k.succAbove j` is `j` below `k` and `j + 1` from `k` on (`Fin.val_succAbove_of_lt`,
`Fin.val_succAbove_of_le`), so its value is always `j` or `j + 1` (`Fin.le_val_succAbove`,
`Fin.val_succAbove_le`): the arithmetic form, for `omega`, of Mathlib's
`Fin.succAbove_of_castSucc_lt` and `Fin.succAbove_of_le_castSucc`. Deleting a column `k` of a
matrix reindexes the columns by `k.succAbove`, and these are the bounds that keep track of how far
a column moves.
-/

namespace Fin

variable {n : ℕ}

/-- The value of `k.succAbove j` is at most `j + 1`. -/
theorem val_succAbove_le (k : Fin (n + 1)) (j : Fin n) : (k.succAbove j : ℕ) ≤ j + 1 := by
  unfold Fin.succAbove
  split_ifs <;> simp

/-- The value of `k.succAbove j` is at least `j`. -/
theorem le_val_succAbove (k : Fin (n + 1)) (j : Fin n) : (j : ℕ) ≤ k.succAbove j := by
  unfold Fin.succAbove
  split_ifs <;> simp

/-- Below `k`, `k.succAbove j` is `j`. -/
theorem val_succAbove_of_lt {k : Fin (n + 1)} {j : Fin n} (h : (j : ℕ) < k) :
    (k.succAbove j : ℕ) = j := by
  rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), Fin.val_castSucc]

/-- From `k` on, `k.succAbove j` is `j + 1`. -/
theorem val_succAbove_of_le {k : Fin (n + 1)} {j : Fin n} (h : (k : ℕ) ≤ j) :
    (k.succAbove j : ℕ) = j + 1 := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h), Fin.val_succ]

end Fin
