import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# Successful checks before and after point updates

Rejected trials preserve the checked predicate. Telescoping its indicators
transfers endpoint counts to current-point counts with one initialization.
-/

namespace EvaluationComplexity

/-- Rejected trials preserve the measured point, so current-point successful
checks outnumber endpoint successful checks by at most one initialization. -/
theorem card_current_le_endpoint_add_one {S : Set ℕ} {P : ℕ → Prop} {N : ℕ}
    (hu : ∀ i < N, i ∉ S → (P (i + 1) ↔ P i)) :
    (successfulIterations {i | i ∈ S ∧ P i} N).card ≤
      (successfulIterations {i | i ∈ S ∧ P (i + 1)} N).card + 1 := by
  classical
  have hsum : (∑ i ∈ Finset.range N,
      ((if i ∈ S ∧ P i then (1 : ℤ) else 0) -
        (if i ∈ S ∧ P (i + 1) then (1 : ℤ) else 0))) =
      (if P 0 then (1 : ℤ) else 0) - (if P N then (1 : ℤ) else 0) := by
    calc
      _ = ∑ i ∈ Finset.range N,
          ((if P i then (1 : ℤ) else 0) - (if P (i + 1) then (1 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hs : i ∈ S
        · simp only [hs, true_and]
        · have he := hu i (Finset.mem_range.mp hi) hs
          simp only [hs, false_and, ite_false, sub_self]
          simp only [he, sub_self]
      _ = _ := Finset.sum_range_sub' (fun i => if P i then (1 : ℤ) else 0) N
  have ha : ∑ i ∈ Finset.range N, (if i ∈ S ∧ P i then (1 : ℤ) else 0) =
      ((successfulIterations {i | i ∈ S ∧ P i} N).card : ℤ) := by
    simp [successfulIterations]
  have hb : ∑ i ∈ Finset.range N, (if i ∈ S ∧ P (i + 1) then (1 : ℤ) else 0) =
      ((successfulIterations {i | i ∈ S ∧ P (i + 1)} N).card : ℤ) := by
    simp [successfulIterations]
  rw [Finset.sum_sub_distrib, ha, hb] at hsum
  split_ifs at hsum <;> omega

end EvaluationComplexity
