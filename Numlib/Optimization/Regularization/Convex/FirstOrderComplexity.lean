import Numlib.Optimization.Regularization.Convex.FirstOrderStep
import Numlib.Optimization.Regularization.HighOrder.Complexity

/-!
# Full first-order constrained regularization termination and evaluation counts

The exact successful decrease pays for all but at most one terminal accepted
step. Actual parameter intervals pay for every rejected trial. Fixed positive
source constants precede every accuracy request and every primitive execution.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- Actual source regularization cap for the fixed constrained settings. -/
noncomputable def parameterCap {p : ℕ} (P : Settings p) (L : ℝ) : ℝ :=
  max P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))

/-- Exact successful-decrease coefficient for the first-order constrained measure. -/
noncomputable def firstDecreaseCoefficient {p : ℕ} (P : Settings p) (L : ℝ) : ℝ :=
  decreaseConstant p p P.eta1 P.sigmaMin L (parameterCap P L) P.theta

/-- Every fixed first-order constrained decrease coefficient is strictly positive. -/
theorem firstDecreaseCoefficient_pos {p : ℕ} (P : Settings p) {L : ℝ} (hL : 0 < L) :
    0 < firstDecreaseCoefficient P L := by
  apply decreaseConstant_pos p p P.eta1_pos P.sigmaMin_pos hL
    (P.sigmaMin_pos.le.trans (P.sigmaMin_le_initial.trans (le_max_left _ _)))
  have := P.theta_lower
  have := P.tau_pos
  linarith

/-- The reciprocal of the true decrease coefficient is precisely the source κS. -/
theorem inv_firstDecreaseCoefficient {p : ℕ} (P : Settings p) {L : ℝ} (hL : 0 < L) :
    1 / firstDecreaseCoefficient P L = (p + 1).factorial / (P.eta1 * P.sigmaMin) *
      ((L + parameterCap P L + P.theta * p.factorial) / p.factorial) ^
        (((p + 1 : ℕ) : ℝ) / p) := by
  exact inv_decreaseConstant_eq p p hL
    (P.sigmaMin_pos.le.trans (P.sigmaMin_le_initial.trans (le_max_left _ _)))
    (by have := P.theta_lower; have := P.tau_pos; linarith)

/-- Actual initialized objective evaluations: one initial value and one per trial. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- First-derivative evaluation indices: initialization and every accepted endpoint. -/
noncomputable def derivativeEvaluationNodes {p : ℕ} (P : Settings p) (D : Data E)
    (N : ℕ) : Finset ℕ := by
  classical
  exact insert 0 ((successfulIterations {i | P.eta1 ≤ D.ratio i} N).image Nat.succ)

/-- The actual first-derivative count, also a common upper budget for the
higher derivatives. Rejection retains the current derivative data. -/
noncomputable def derivativeEvaluations {p : ℕ} (P : Settings p) (D : Data E)
    (N : ℕ) : ℕ := (derivativeEvaluationNodes P D N).card

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- The actual initialized derivative schedule has one more node than successes. -/
theorem derivativeEvaluations_eq {p : ℕ} (P : Settings p) (D : Data E) (N : ℕ) :
    derivativeEvaluations P D N = (successfulIterations {i | P.eta1 ≤ D.ratio i} N).card +
      1 := by
  classical
  rw [derivativeEvaluations, derivativeEvaluationNodes, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ Nat.succ_injective]
  · simp

/-- Actual higher derivative evaluations exclude the terminal point, where
only the first-order stopping test is evaluated. All rejected trials reuse jets. -/
noncomputable def derivativeEvaluationNodesAtOrder {p : ℕ} (P : Settings p) (D : Data E)
    (N j : ℕ) : Finset ℕ := by
  classical
  exact if j = 1 then derivativeEvaluationNodes P D N
    else (derivativeEvaluationNodes P D N).filter (fun i => i < N)

/-- The actual per-order evaluation count on the explicit derivative schedule. -/
noncomputable def derivativeEvaluationsAtOrder {p : ℕ} (P : Settings p) (D : Data E)
    (N j : ℕ) : ℕ := (derivativeEvaluationNodesAtOrder P D N j).card

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- Every actual per-order derivative schedule is contained in the initialized
first-derivative schedule, including a zero-trial initial stop. -/
theorem derivativeEvaluationsAtOrder_le {p : ℕ} (P : Settings p) (D : Data E) (N j : ℕ) :
    derivativeEvaluationsAtOrder P D N j ≤ derivativeEvaluations P D N := by
  classical
  unfold derivativeEvaluationsAtOrder derivativeEvaluationNodesAtOrder derivativeEvaluations
  split_ifs
  · exact le_rfl
  · exact Finset.card_filter_le _ _

variable {p : ℕ} {f : E → ℝ} {C S : Set E} {P : Settings p}
  {ε L flow : ℝ} {D : Data E} {N : ℕ}

omit [ProperSpace E] in
/-- Failed actual trials preserve both the iterate and its objective value. -/
theorem ScaledRun.rejected (h : ScaledRun f C P ε D N) {i : ℕ} (hi : i < N)
    (hs : ¬P.eta1 ≤ D.ratio i) : D.point (i + 1) = D.point i := by
  rw [h.modelTrace.point_update i hi, ite_eq_right hs]

/-- The exact first-order decrease applies to every nonterminal accepted endpoint. -/
theorem ScaledRun.nonterminal_decrease (h : ScaledRun f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i + 1 < N) (hs : P.eta1 ≤ D.ratio i) :
    firstDecreaseCoefficient P L * ε ^ (((p + 1 : ℕ) : ℝ) / p) ≤
      f (D.point i) - f (D.point (i + 1)) := by
  apply (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow h.accuracy_pos.le (h.continues (i + 1) hi).le
      (by positivity : (0 : ℝ) ≤ ((p + 1 : ℕ) : ℝ) / p))
    (firstDecreaseCoefficient_pos P hL).le).trans
  exact h.successful_decrease hclosed hS hCS hC hf hL hlip (by omega) hs

/-- At most one accepted endpoint escapes the pretermination decrease budget. -/
theorem ScaledRun.successful_card_le (h : ScaledRun f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y ∈ C, flow ≤ f y) :
    ((successfulIterations {i | P.eta1 ≤ D.ratio i} N).card : ℝ) ≤
      (f (D.point 0) - flow) /
        (firstDecreaseCoefficient P L * ε ^ (((p + 1 : ℕ) : ℝ) / p)) + 1 := by
  have hgap : 0 ≤ f (D.point 0) - flow := sub_nonneg.mpr (hlow _ h.initial_mem)
  have hd : 0 < firstDecreaseCoefficient P L * ε ^ (((p + 1 : ℕ) : ℝ) / p) :=
    mul_pos (firstDecreaseCoefficient_pos P hL) (Real.rpow_pos_of_pos h.accuracy_pos _)
  cases N with
  | zero => simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]; positivity
  | succ k =>
    have hc := card_successful_le_gap_div
      (S := {i | P.eta1 ≤ D.ratio i}) (f := fun i => f (D.point i)) hd
      (hlow _ (h.mem (show k ≤ k + 1 by omega)))
      (fun i hi hs => h.nonterminal_decrease hclosed hS hCS hC hf hL hlip (by omega) hs)
      (fun i hi hs => by rw [h.rejected (by omega) hs])
    have hs : ((successfulIterations {i | P.eta1 ≤ D.ratio i} (k + 1)).card : ℝ) ≤
        (successfulIterations {i | P.eta1 ≤ D.ratio i} k).card + 1 := by
      exact_mod_cast card_successful_succ_le {i | P.eta1 ≤ D.ratio i} k
    exact hs.trans (add_le_add hc le_rfl)

/-- Actual parameter intervals control all trials by the successful objective budget. -/
theorem ScaledRun.iterations_le (h : ScaledRun f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y ∈ C, flow ≤ f y) :
    (N : ℝ) ≤ ((f (D.point 0) - flow) /
      (firstDecreaseCoefficient P L * ε ^ (((p + 1 : ℕ) : ℝ) / p)) + 1) *
        (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (parameterCap P L / P.sigmaInitial) / Real.log P.gamma2 := by
  have ht := iteration_bound_of_parameter_upper
    (S := {i | P.eta1 ≤ D.ratio i}) (fun _ hi => h.modelTrace.updates.pos hi)
    P.gamma1_pos P.gamma1_lt_one P.one_lt_gamma2 (h.parameter_le hS hCS hC hf hL.le hlip
      le_rfl) (fun _ hi hs => h.modelTrace.updates.successful_ge hi hs)
    (fun _ hi hs => h.modelTrace.updates.unsuccessful_ge hi hs)
  rw [h.initial_parameter] at ht
  have hA : 0 ≤ 1 + |Real.log P.gamma1| / Real.log P.gamma2 := by
    have := Real.log_pos P.one_lt_gamma2
    positivity
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right (h.successful_card_le hclosed hS hCS hC hf hL hlip hlow)
      hA) le_rfl)

/-- Consistent primitive prefixes reach the first actual constrained stopping test. -/
theorem exists_first_order_termination (hclosed : IsClosed C) (hS : IsOpen S)
    (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y ∈ C, flow ≤ f y)
    (hprefix : ∀ N, (∀ i < N, ε < constrainedCriticality f 1 C (D.point i) 1) →
      ScaledRun f C P ε D N) :
    ∃ K, constrainedCriticality f 1 C (D.point K) 1 ≤ ε ∧
      ScaledRun f C P ε D K ∧
      ∀ i < K, ε < constrainedCriticality f 1 C (D.point i) 1 := by
  classical
  have hex : ∃ K, constrainedCriticality f 1 C (D.point K) 1 ≤ ε := by
    by_contra hn
    have hnon : ∀ i, ε < constrainedCriticality f 1 C (D.point i) 1 := by
      simpa using not_exists.mp hn
    let bound := ((f (D.point 0) - flow) /
      (firstDecreaseCoefficient P L * ε ^ (((p + 1 : ℕ) : ℝ) / p)) + 1) *
        (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (parameterCap P L / P.sigmaInitial) / Real.log P.gamma2
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    exact (not_le_of_gt hN) ((hprefix N (fun i _ => hnon i)).iterations_le
      hclosed hS hCS hC hf hL hlip hlow)
  have hnon : ∀ i < Nat.find hex, ε < constrainedCriticality f 1 C (D.point i) 1 := by
    intro i hi
    exact lt_of_not_ge (Nat.find_min hex hi)
  exact ⟨Nat.find hex, Nat.find_spec hex, hprefix _ hnon, hnon⟩

/-- Exact positive source constants precede every accuracy and every actual
scaled-test constrained execution, including initialized evaluation counts. -/
theorem exists_uniform_first_order_complexity {f : E → ℝ} {C S : Set E} {p : ℕ}
    (P : Settings p) (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S)
    (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S) {L flow : ℝ} (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y ∈ C, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = (p + 1).factorial / (P.eta1 * P.sigmaMin) *
        ((L + parameterCap P L + P.theta * p.factorial) / p.factorial) ^
          (((p + 1 : ℕ) : ℝ) / p) ∧
      κA = κS * (1 + |Real.log P.gamma1| / Real.log P.gamma2) ∧
      κC = |Real.log P.gamma1| / Real.log P.gamma2 +
        Real.log (parameterCap P L / P.sigmaInitial) / Real.log P.gamma2 + 2 ∧
      ∀ (ε : ℝ) (D : Data E),
        (∀ N, (∀ i < N, ε < constrainedCriticality f 1 C (D.point i) 1) →
          ScaledRun f C P ε D N) →
        ∃ K, constrainedCriticality f 1 C (D.point K) 1 ≤ ε ∧
          ScaledRun f C P ε D K ∧
          (∀ i < K, ε < constrainedCriticality f 1 C (D.point i) 1) ∧
          (functionEvaluations K : ℝ) ≤ κA * (f (D.point 0) - flow) /
            ε ^ (((p + 1 : ℕ) : ℝ) / p) + κC ∧
          (derivativeEvaluations P D K : ℝ) ≤ κS * (f (D.point 0) - flow) /
            ε ^ (((p + 1 : ℕ) : ℝ) / p) + 2 ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ p →
            (derivativeEvaluationsAtOrder P D K j : ℝ) ≤
              κS * (f (D.point 0) - flow) / ε ^ (((p + 1 : ℕ) : ℝ) / p) + 2 := by
  let c := firstDecreaseCoefficient P L
  let A := 1 + |Real.log P.gamma1| / Real.log P.gamma2
  let B := Real.log (parameterCap P L / P.sigmaInitial) / Real.log P.gamma2
  have hc : 0 < c := firstDecreaseCoefficient_pos P hL
  have hA : 0 < A := by have := Real.log_pos P.one_lt_gamma2; dsimp [A]; positivity
  have hratio : 1 ≤ parameterCap P L / P.sigmaInitial := by
    apply (le_div_iff₀ (P.sigmaMin_pos.trans_le P.sigmaMin_le_initial)).mpr
    simpa only [one_mul, parameterCap] using
      le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))
  have hB : 0 ≤ B := div_nonneg (Real.log_nonneg hratio)
    (Real.log_pos P.one_lt_gamma2).le
  refine ⟨1 / c, by positivity, (1 / c) * A, by positivity, A + B + 1,
    by positivity, inv_firstDecreaseCoefficient P hL, rfl, ?_, ?_⟩
  · dsimp [A, B]
    ring
  intro ε D hprefix
  obtain ⟨K, hstop, hK, hfirst⟩ := exists_first_order_termination
    hclosed hS hCS hC hf hL hlip hlow hprefix
  have hF := hK.iterations_le hclosed hS hCS hC hf hL hlip hlow
  have hD := hK.successful_card_le hclosed hS hCS hC hf hL hlip hlow
  refine ⟨K, hstop, hK, hfirst, ?_, ?_⟩
  · simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
    convert add_le_add hF (le_refl (1 : ℝ)) using 1
    dsimp [c, A, B]
    push_cast
    ring
  · have hb : (derivativeEvaluations P D K : ℝ) ≤
        (1 / c) * (f (D.point 0) - flow) / ε ^ (((p + 1 : ℕ) : ℝ) / p) + 2 := by
      rw [derivativeEvaluations_eq, Nat.cast_add, Nat.cast_one]
      have hh := add_le_add hD (le_refl (1 : ℝ))
      convert hh using 1
      dsimp [c]
      push_cast
      ring
    exact ⟨hb, fun j _ _ =>
      (Nat.cast_le.mpr (derivativeEvaluationsAtOrder_le P D K j)).trans hb⟩

end ConvexRegularization
