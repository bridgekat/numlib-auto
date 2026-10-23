import Numlib.Optimization.EvaluationComplexity.Updates

/-!
# Finite objective budgets and evaluation complexity

Summing a positive objective reduction on each successful iteration bounds their
number by the available objective gap. A stopping test must therefore hold within
any prefix whose guaranteed reductions would exhaust that gap.
-/

namespace EvaluationComplexity

/-- An objective bounded below cannot sustain more successful iterations than
its initial gap divided by the guaranteed decrease per successful iteration. -/
theorem card_successful_mul_le_gap {S : Set ℕ} {f : ℕ → ℝ} {flow d : ℝ} {k : ℕ}
    (hlow : flow ≤ f k)
    (hs : ∀ i < k, i ∈ S → d ≤ f i - f (i + 1))
    (hu : ∀ i < k, i ∉ S → f (i + 1) ≤ f i) :
    (successfulIterations S k).card * d ≤ f 0 - flow := by
  have h := potential_change_le (S := S) (v := f) (a := -d) (b := 0)
    (fun i hi hS => by linarith [hs i hi hS])
    (fun i hi hS => by linarith [hu i hi hS])
  simp only [mul_zero, add_zero, mul_neg] at h
  linarith

/-- The cardinality bound obtained by dividing the finite objective budget by a
strictly positive per-successful-iteration decrease. -/
theorem card_successful_le_gap_div {S : Set ℕ} {f : ℕ → ℝ} {flow d : ℝ} {k : ℕ}
    (hd : 0 < d) (hlow : flow ≤ f k)
    (hs : ∀ i < k, i ∈ S → d ≤ f i - f (i + 1))
    (hu : ∀ i < k, i ∉ S → f (i + 1) ≤ f i) :
    ((successfulIterations S k).card : ℝ) ≤ (f 0 - flow) / d :=
  (le_div_iff₀ hd).mpr (card_successful_mul_le_gap hlow hs hu)

/-- If `N` nonterminating steps would consume more than the objective budget,
then the stopping test `measure i ≤ ε` holds at an index strictly smaller than `N`.
The decrease assumption is conditional on failure of that test. -/
theorem exists_measure_le_of_budget {f measure : ℕ → ℝ} {flow d ε : ℝ} {N : ℕ}
    (hlow : flow ≤ f N) (hbudget : f 0 - flow < (N : ℝ) * d)
    (hstep : ∀ i < N, ε < measure i → d ≤ f i - f (i + 1)) :
    ∃ i < N, measure i ≤ ε := by
  by_contra h
  push Not at h
  have hsum : (N : ℝ) * d ≤ f 0 - f N := by
    calc
      (N : ℝ) * d = ∑ _i ∈ Finset.range N, d := by simp
      _ ≤ ∑ i ∈ Finset.range N, (f i - f (i + 1)) := by
        exact Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi)
          (h i (Finset.mem_range.mp hi)))
      _ = f 0 - f N := Finset.sum_range_sub' f N
  linarith

end EvaluationComplexity
