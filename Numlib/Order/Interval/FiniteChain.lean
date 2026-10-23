import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

/-!
# Adjacent intervals cover a finite chain

Any point between a sequence's first and last values belongs to some adjacent
closed interval. No monotonicity is needed: the first crossing suffices.
-/

open Set

/-- Adjacent closed intervals cover the closed interval between the first and
last values of any nonempty finite chain in a linear order. -/
theorem exists_mem_Icc_adjacent {α : Type*} [LinearOrder α] (x : ℕ → α)
    {n : ℕ} (hn : 0 < n) {t : α} (ht : t ∈ Icc (x 0) (x n)) :
    ∃ k < n, t ∈ Icc (x k) (x (k + 1)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases htn : t ≤ x n
    · by_cases hn0 : n = 0
      · subst n
        exact ⟨0, by omega, ht⟩
      · obtain ⟨k, hk, hkt⟩ := ih (by omega) ⟨ht.1, htn⟩
        exact ⟨k, by omega, hkt⟩
    · exact ⟨n, by omega, ⟨(lt_of_not_ge htn).le, ht.2⟩⟩
