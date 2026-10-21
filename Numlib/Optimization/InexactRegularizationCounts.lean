import Numlib.Optimization.InexactRegularizationRun
import Numlib.Optimization.AdaptiveRegularizationComplexity

/-!
# Actual cached evaluation counts for implicit-accuracy regularization

Every pass is a trial or an accuracy refinement. A fresh tensor batch occurs initially,
after acceptance, or after refinement. Rejected trials reuse the actual derivative cache.
These are properties of the transition relation, with no complexity or quality premise.
-/

noncomputable section
namespace Optimization.InexactRegularization
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Parameters} {checked N : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E}

/-- A transition prepares fresh tensors exactly after acceptance or accuracy refinement. -/
theorem Transition.next_fresh {a b : State E} {trial accepted : Bool}
    (h : Transition P checked f oracle a b trial accepted) :
    b.fresh = (accepted || !trial) := by
  cases h with
  | refineInspection => rfl
  | refineStep => rfl
  | trial => split_ifs <;> simp_all

/-- The fresh successor batch is charged once to acceptance or to refinement. -/
theorem Transition.fresh_cost {a b : State E} {trial accepted : Bool}
    (h : Transition P checked f oracle a b trial accepted) :
    (if b.fresh then 1 else 0 : ℕ) =
      (if accepted then 1 else 0) + (if trial then 0 else 1) := by
  have ha := h.accepted_is_trial
  rw [h.next_fresh]
  cases trial <;> cases accepted <;> simp_all

/-- Every actual pass is either a trial or one geometric accuracy refinement. -/
theorem Execution.trialCount_add_refinementCount (r : Execution P checked f oracle N) :
    r.trialCount + r.refinementCount N = N := by
  classical
  simp only [trialCount, refinementCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  have he (k : ℕ) : (if r.trial k then 1 else 0 : ℕ) +
      (if r.trial k then 0 else 1) = 1 := by cases r.trial k <;> rfl
  simp only [he, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- The actual objective log pays initialization and exactly one value at each trial. -/
theorem Execution.functionCount_eq_trialCount_add_one (r : Execution P checked f oracle N) :
    r.functionCount = r.trialCount + 1 := by
  simp only [Execution.functionCount, trialCount, Nat.add_comm]

/-- Every actual fresh derivative batch is paid by initialization, an earlier accepted
trial, or an earlier accuracy refinement. No rejection adds a tensor batch. -/
theorem Execution.derivativeBatches_le (r : Execution P checked f oracle N) :
    r.derivativeBatches ≤ r.acceptedCount + r.refinementCount N + 1 := by
  classical
  have hsum : r.derivativeBatches =
      ∑ k ∈ Finset.range N, if (r.state k).fresh then 1 else 0 := by
    simp only [Execution.derivativeBatches, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hsum]
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), if (r.state k).fresh then 1 else 0 := by
      rw [Finset.sum_range_succ]
      exact Nat.le_add_right _ _
    _ = r.acceptedCount + r.refinementCount N + 1 := by
      rw [Finset.sum_range_succ']
      simp only [r.initial_fresh, ↓reduceIte]
      have he : (∑ k ∈ Finset.range N, if (r.state (k + 1)).fresh then 1 else 0) =
          r.acceptedCount + r.refinementCount N := by
        unfold acceptedCount refinementCount
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        exact (r.transition k (Finset.mem_range.mp hk)).fresh_cost
      rw [he]

/-- Every actual complete run is nonincreasing in the true objective at every pass. -/
theorem Run.objective_nonincrease (r : Run P checked f oracle) (k : ℕ) :
    f (r.state (k + 1)).point ≤ f (r.state k).point := by
  let rp := r.prefix (k + 1)
  exact (r.transition_all k).objective_nonincrease
    (P.sigmaMin_pos.le.trans (rp.sigma_floor (k := k) (by omega)))
    (rp.valid_radii (k := k) (by omega))

/-- Before a first test, actual accepted transitions consume their positive successor
payment, with one possible last accepted transition attaining the test. This delegates to
the generic adaptive-regularization counting theorem using the complete run's true values. -/
theorem Run.accepted_count_before_test_le (r : Run P checked f oracle)
    {Q : E → Prop} {delta low : ℝ} (hd : 0 < delta) (hlow : ∀ x, low ≤ f x)
    (hdec : ∀ k, r.accepted k = true → ¬Q (r.state (k + 1)).point →
      delta ≤ f (r.state k).point - f (r.state (k + 1)).point)
    (n : ℕ) (hfirst : ∀ k < n, ¬Q (r.state k).point) :
    ((r.prefix n).acceptedCount : ℝ) ≤ (f (r.state 0).point - low) / delta + 1 := by
  have hb := ParameterUpdates.successCount_before_test_le_of_successor_decrease
    (u := fun k => f (r.state k).point) (P := fun k => Q (r.state k).point)
    (fun k => r.accepted k = true) hd (fun k => hlow (r.state k).point)
    r.objective_nonincrease hdec n hfirst
  have he : (r.prefix n).acceptedCount =
      ParameterUpdates.successCount (fun k => r.accepted k = true) n := by
    classical
    unfold Execution.acceptedCount ParameterUpdates.successCount
    dsimp only [Run.prefix]
    congr 1
    exact @Finset.filter_congr_decidable ℕ (Finset.range n)
      (fun k => r.accepted k = true)
      (fun k => instDecidableEqBool (r.accepted k) true)
      (fun k => Classical.propDecidable (r.accepted k = true))
  rw [he]
  exact hb

end Optimization.InexactRegularization
