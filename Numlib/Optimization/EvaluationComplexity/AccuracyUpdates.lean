import Numlib.Optimization.EvaluationComplexity.TrialCounting

/-!
# Counting multiplicative accuracy reductions

Requested accuracies shrink by a fixed factor on accuracy-improving iterations
and stay unchanged otherwise. If the primitive branching tests disallow further
reductions below a threshold, logarithms bound their number, including the last
reduction that crosses the threshold.
-/

namespace EvaluationComplexity

open Classical in
/-- Adding one index to a prefix increments its count exactly when it belongs
to the specified class of iterations. -/
theorem card_successful_succ (A : Set ℕ) (i : ℕ) :
    (successfulIterations A (i + 1)).card =
      (successfulIterations A i).card + if i ∈ A then 1 else 0 := by
  classical
  simp only [successfulIterations, Finset.range_add_one, Finset.filter_insert]
  split_ifs with hi
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

open Classical in
/-- Primitive multiplicative request reductions on a specified iteration class. -/
structure AccuracyUpdates (A : Set ℕ) (request : ℕ → ℝ) (γ : ℝ) (N : ℕ) : Prop where
  initial_pos : 0 < request 0
  reduction_pos : 0 < γ
  reduction_lt_one : γ < 1
  update : ∀ i < N, request (i + 1) = if i ∈ A then γ * request i else request i

namespace AccuracyUpdates
variable {A : Set ℕ} {request : ℕ → ℝ} {γ : ℝ} {N : ℕ}

/-- Every actual requested accuracy stays strictly positive. -/
theorem pos (h : AccuracyUpdates A request γ N) {i : ℕ} (hi : i ≤ N) : 0 < request i := by
  induction i with
  | zero => exact h.initial_pos
  | succ i ih =>
    rw [h.update i (by omega)]
    split_ifs
    · exact mul_pos h.reduction_pos (ih (by omega))
    · exact ih (by omega)

/-- The exact number of accuracy-only updates gives the actual request value. -/
theorem eq_initial_mul_pow (h : AccuracyUpdates A request γ N) {i : ℕ} (hi : i ≤ N) :
    request i = request 0 * γ ^ (successfulIterations A i).card := by
  classical
  induction i with
  | zero => simp [successfulIterations]
  | succ i ih =>
    rw [h.update i (by omega), card_successful_succ]
    split_ifs with hA
    · rw [ih (by omega), pow_succ]
      ring
    · simpa using ih (by omega)

/-- A threshold condition on actual reduction branches yields an endpoint floor;
the final multiplication is included. -/
theorem min_initial_threshold_le (h : AccuracyUpdates A request γ N) {τ : ℝ}
    (hbranch : ∀ i < N, i ∈ A → τ < request i) {i : ℕ} (hi : i ≤ N) :
    min (request 0) (γ * τ) ≤ request i := by
  classical
  induction i with
  | zero => exact min_le_left _ _
  | succ i ih =>
    rw [h.update i (by omega)]
    split_ifs with hA
    · exact (min_le_right _ _).trans
        (mul_le_mul_of_nonneg_left (hbranch i (by omega) hA).le h.reduction_pos.le)
    · exact ih (by omega)

/-- The number of actual request reductions is logarithmic in the threshold,
with the endpoint multiplication and initialization accounted for exactly. -/
theorem reductions_le (h : AccuracyUpdates A request γ N) {τ : ℝ} (hτ : 0 < τ)
    (hbranch : ∀ i < N, i ∈ A → τ < request i) :
    ((successfulIterations A N).card : ℝ) ≤
      1 + |Real.log (τ / request 0)| / |Real.log γ| := by
  classical
  let δmin := min (request 0) (γ * τ)
  have hδ : 0 < δmin := lt_min h.initial_pos (mul_pos h.reduction_pos hτ)
  have hb := iteration_bound_of_parameter_lower_on_trials
    (S := ∅) (T := A) (δ := request) (γs := 1) (γu := γ) (δmin := δmin)
    (Set.empty_subset A) (fun i hi => h.pos hi) (by norm_num) h.reduction_pos
    h.reduction_lt_one (h.min_initial_threshold_le hbranch le_rfl) hδ
    (by simp) (fun i hi hA _ => by rw [h.update i hi, ite_eq_left hA])
    (fun i hi hA => by rw [h.update i hi, ite_eq_right hA])
  simp only [successfulIterations, Set.mem_empty_iff_false, Finset.filter_false,
    Finset.card_empty, Nat.cast_zero, zero_mul, zero_add] at hb
  have hlogγ := Real.log_neg h.reduction_pos h.reduction_lt_one
  have hp : 0 < |Real.log γ| := abs_pos.mpr hlogγ.ne
  have hlog : |Real.log (δmin / request 0)| ≤ |Real.log γ| +
      |Real.log (τ / request 0)| := by
    by_cases hc : request 0 ≤ γ * τ
    · simp only [δmin, min_eq_left hc, div_self h.initial_pos.ne', Real.log_one, abs_zero]
      positivity
    · rw [show δmin / request 0 = γ * (τ / request 0) by
        dsimp [δmin]; rw [min_eq_right (not_le.mp hc).le]; ring,
        Real.log_mul h.reduction_pos.ne' (div_pos hτ h.initial_pos).ne']
      exact abs_add_le _ _
  calc _ ≤ |Real.log (δmin / request 0)| / |Real.log γ| := hb
    _ ≤ (|Real.log γ| + |Real.log (τ / request 0)|) / |Real.log γ| :=
      div_le_div_of_nonneg_right hlog hp.le
    _ = _ := by rw [add_div, div_self hp.ne']

end AccuracyUpdates
end EvaluationComplexity
