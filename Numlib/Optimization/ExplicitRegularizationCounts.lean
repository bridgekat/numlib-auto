import Numlib.Optimization.ExplicitRegularizationBounds
import Numlib.Optimization.AdaptiveRegularizationFiniteComplexity

/-!
# Counts for finite explicit-accuracy regularization executions

Every pass is a trial or an accuracy refinement. Derivative batches are charged exactly
once initially and once after acceptance or refinement, including the final inspection.
Only actual transitions before the endpoint enter the descent and logarithmic budgets.
The value-query log includes one or two calls per trial and no initialization call.
-/

noncomputable section
namespace Optimization.ExplicitRegularization
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Parameters} {N : ℕ} {f : E → ℝ} {O : Oracle f P.p}

/-- An accepted event is necessarily an actual trial. -/
theorem Transition.accepted_is_trial {a b : State E} {I : Inspection P O.derivative a}
    {trial accepted : Bool} {queries : List (E × ℝ)}
    (h : Transition P O a I b trial accepted queries) (ha : accepted = true) :
    trial = true := by
  cases h <;> simp_all

/-- Every fresh successor is charged once to acceptance or to accuracy refinement. -/
theorem Transition.fresh_cost {a b : State E} {I : Inspection P O.derivative a}
    {trial accepted : Bool} {queries : List (E × ℝ)}
    (h : Transition P O a I b trial accepted queries) :
    (if b.fresh then 1 else 0 : ℕ) =
      (if accepted then 1 else 0) + (if trial then 0 else 1) := by
  have hf := h.fresh_iff
  have ha := h.accepted_is_trial
  cases hfresh : b.fresh <;> cases trial <;> cases accepted <;> simp_all

/-- The actual number of trials in the executed prefix. -/
def Execution.trialCount (r : Execution P O N) : ℕ :=
  ((Finset.range N).filter fun k => r.trial k).card

/-- The actual number of accepted trials in the executed prefix. -/
def Execution.acceptedCount (r : Execution P O N) : ℕ :=
  ((Finset.range N).filter fun k => r.accepted k).card

/-- The actual number of accuracy refinements before a selected index. -/
def Execution.refinementCount (r : Execution P O N) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun j => r.trial j = false).card

/-- A refinement count increases only at a nontrial pass. -/
theorem Execution.refinementCount_succ (r : Execution P O N) (k : ℕ) :
    r.refinementCount (k + 1) = r.refinementCount k + if r.trial k then 0 else 1 := by
  classical
  simp only [refinementCount, Finset.range_add_one, Finset.filter_insert]
  cases h : r.trial k <;> simp [h]

/-- The executed passes partition into trials and refinements. -/
theorem Execution.trialCount_add_refinementCount (r : Execution P O N) :
    r.trialCount + r.refinementCount N = N := by
  classical
  simp only [trialCount, refinementCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  have he (k : ℕ) : (if r.trial k then 1 else 0 : ℕ) +
      (if r.trial k = false then 1 else 0) = 1 := by cases r.trial k <;> rfl
  simp only [he, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- Actual value calls are bounded above and below by their actual trial count. -/
theorem Execution.functionQueries_count_bounds (r : Execution P O N) :
    r.trialCount ≤ r.functionQueries.length ∧ r.functionQueries.length ≤ 2 * r.trialCount :=
  r.functionQueries_bounds

/-- The actual tensor-query schedule pays exactly once for initialization and once for
each accepted trial or accuracy refinement, including the final inspected state. -/
theorem Execution.derivativeQueries_count (r : Execution P O N) :
    r.derivativeQueries.length = r.acceptedCount + r.refinementCount N + 1 := by
  classical
  rw [r.derivativeQueries_length]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_range_succ']
  simp only [r.initial_fresh, ↓reduceIte]
  have he : (∑ k ∈ Finset.range N, if (r.state (k + 1)).fresh then 1 else 0) =
      r.acceptedCount + r.refinementCount N := by
    unfold acceptedCount refinementCount
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hc := (r.transition k (Finset.mem_range.mp hk)).fresh_cost
    cases ht : r.trial k <;> simpa [ht] using hc
  omega

/-- Accepted trials whose successor has not reached the final inspection pay the finite
objective budget. The last accepted transition is charged by the extra one. -/
theorem Execution.accepted_count_le (r : Execution P O N) {delta low : ℝ}
    (hd : 0 < delta) (hlow : ∀ x, low ≤ f x)
    (hdec : ∀ k, k + 1 < N → r.accepted k = true →
      delta ≤ f (r.state k).point - f (r.state (k + 1)).point) :
    (r.acceptedCount : ℝ) ≤ (f (r.state 0).point - low) / delta + 1 := by
  have hb := ParameterUpdates.successCount_le_of_finite_successor_decrease
    (u := fun k => f (r.state k).point) (fun k => r.accepted k = true) hd N
    (hlow _) (fun k hk => r.objective_nonincrease (by omega)) hdec
  have he : r.acceptedCount = ParameterUpdates.successCount (fun k => r.accepted k = true) N := by
    unfold acceptedCount ParameterUpdates.successCount
    congr 1
    exact @Finset.filter_congr_decidable ℕ (Finset.range N)
      (fun k => r.accepted k = true)
      (fun k => instDecidableEqBool (r.accepted k) true)
      (fun k => Classical.propDecidable (r.accepted k = true))
  rw [he]
  exact hb

/-- Accepted trials whose successor remains uncertified pay the objective budget. The
execution itself supplies all required failures strictly before its endpoint. -/
theorem Execution.accepted_count_before_certified_le (r : Execution P O N) {delta low : ℝ}
    (hd : 0 < delta) (hlow : ∀ x, low ≤ f x)
    (hdec : ∀ k, k < N → r.accepted k = true →
      ¬Certified P (r.state (k + 1)) (r.inspection (k + 1)) →
      delta ≤ f (r.state k).point - f (r.state (k + 1)).point) :
    (r.acceptedCount : ℝ) ≤ (f (r.state 0).point - low) / delta + 1 :=
  r.accepted_count_le hd hlow (fun k hk ha => hdec k (by omega) ha (r.not_certified hk))

/-- Accuracy-only passes have zero logarithmic parameter contribution. Every trial pays
its actual accepted or rejected update factor, even with inexact endpoint values. -/
theorem Transition.log_step {a b : State E} {I : Inspection P O.derivative a}
    {trial accepted : Bool} {queries : List (E × ℝ)}
    (t : Transition P O a I b trial accepted queries) (hσ : 0 < a.sigma) :
    (if accepted then Real.log P.gamma1 - Real.log P.gamma2 else 0) +
      (if trial then Real.log P.gamma2 else 0) ≤ Real.log b.sigma - Real.log a.sigma := by
  cases t with
  | refineInspection => simp [refine, InexactRegularization.refine]
  | refineStep => simp [refine, InexactRegularization.refine]
  | trial hq s hacc v next hu =>
    have hh := InexactRegularization.parameter_update_log_lower P.toImplicitParameters hσ hu
    by_cases hs : P.eta1 ≤ v.ratio
    · simpa [trialState, hs] using hh
    · simpa [trialState, hs] using hh

/-- Telescoping the actual parameter changes bounds the trial count independently of the
number of geometric accuracy refinements. -/
theorem Execution.log_budget (r : Execution P O N) :
    (r.acceptedCount : ℝ) * (Real.log P.gamma1 - Real.log P.gamma2) +
      (r.trialCount : ℝ) * Real.log P.gamma2 ≤
        Real.log ((r.state N).sigma / (r.state 0).sigma) := by
  have hh := Finset.sum_le_sum (s := Finset.range N) (fun k hk =>
    (r.transition k (Finset.mem_range.mp hk)).log_step
      (P.sigmaMin_pos.trans_le (r.sigma_floor (Finset.mem_range.mp hk).le)))
  rw [show (∑ k ∈ Finset.range N, (Real.log (r.state (k + 1)).sigma -
      Real.log (r.state k).sigma)) = Real.log (r.state N).sigma - Real.log (r.state 0).sigma
    from Finset.sum_range_sub (fun k => Real.log (r.state k).sigma) N] at hh
  rw [Real.log_div (P.sigmaMin_pos.trans_le (r.sigma_floor le_rfl)).ne'
    (P.sigmaMin_pos.trans_le (r.sigma_floor (Nat.zero_le N))).ne']
  simpa [Execution.acceptedCount, Execution.trialCount, Finset.sum_add_distrib,
    Finset.sum_ite, mul_sub] using hh

/-- A terminal parameter upper bound controls the number of actual trials, with no cost
for accuracy-only passes and no requirement of transitions after certification. -/
theorem Execution.trial_count_le (r : Execution P O N) {M : ℝ}
    (hM : (r.state N).sigma ≤ M) :
    (r.trialCount : ℝ) ≤ (r.acceptedCount : ℝ) *
      (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (M / (r.state 0).sigma) / Real.log P.gamma2 :=
  ParameterUpdates.trial_budget_of_log_budget
    P.toImplicitParameters.toParameters.toRegularizationParameters
    (P.sigmaMin_pos.trans_le (r.sigma_floor (Nat.zero_le N)))
    (P.sigmaMin_pos.trans_le (r.sigma_floor le_rfl)) hM r.log_budget


/-- A finite successor-payment bound, a terminal parameter bound and a refinement budget
control the actual query logs. Value calls carry no extra refinement term; tensor calls
are charged once per success or refinement, with initialization and the last success. -/
theorem Execution.evaluation_bounds_of_successor_decrease (r : Execution P O N)
    {delta low M R : ℝ} (hd : 0 < delta) (hlow : ∀ x, low ≤ f x)
    (hdec : ∀ k, k + 1 < N → r.accepted k = true →
      delta ≤ f (r.state k).point - f (r.state (k + 1)).point)
    (hM : (r.state N).sigma ≤ M) (hR : (r.refinementCount N : ℝ) ≤ R) :
    let gap := f (r.state 0).point - low
    let G := 1 + |Real.log P.gamma1| / Real.log P.gamma2
    let C := Real.log (M / (r.state 0).sigma) / Real.log P.gamma2
    (r.trialCount : ℝ) ≤ G * (gap / delta) + G + C ∧
      (r.functionQueries.length : ℝ) ≤ 2 * (G * (gap / delta) + G + C) ∧
      (r.derivativeQueries.length : ℝ) ≤ gap / delta + R + 2 ∧
      (N : ℝ) ≤ G * (gap / delta) + G + C + R := by
  dsimp only
  have ha := r.accepted_count_le hd hlow hdec
  have ht := r.trial_count_le hM
  have hG : 0 ≤ 1 + |Real.log P.gamma1| / Real.log P.gamma2 :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _)
      (Real.log_pos P.one_lt_gamma2).le)
  have hm := mul_le_mul_of_nonneg_right ha hG
  have htrial : (r.trialCount : ℝ) ≤
      (1 + |Real.log P.gamma1| / Real.log P.gamma2) *
        ((f (r.state 0).point - low) / delta) +
      (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
        Real.log (M / (r.state 0).sigma) / Real.log P.gamma2 := by
    nlinarith
  have hvalue : (r.functionQueries.length : ℝ) ≤ 2 * (r.trialCount : ℝ) := by
    exact_mod_cast r.functionQueries_count_bounds.2
  have htensor : (r.derivativeQueries.length : ℝ) =
      (r.acceptedCount : ℝ) + (r.refinementCount N : ℝ) + 1 := by
    exact_mod_cast r.derivativeQueries_count
  have hpass : (r.trialCount : ℝ) + (r.refinementCount N : ℝ) = N := by
    exact_mod_cast r.trialCount_add_refinementCount
  exact ⟨htrial, by linarith, by linarith, by linarith⟩

end Optimization.ExplicitRegularization
