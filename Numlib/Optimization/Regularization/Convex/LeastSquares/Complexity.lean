import Numlib.Optimization.Regularization.Convex.LeastSquares.Budget

/-!
# Full convexly constrained least-norm evaluation complexity

Actual scaled model solves and true normalized constrained criticality give
the source dyadic residual budget. The exact success and parameter counts
force a first actual stop and bound every initialized residual and derivative
schedule, with all constants fixed before either accuracy.
-/

namespace ConvexLeastSquares
open Set TaylorModel HighOrderRegularization LeastSquares ConvexRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] {p : ℕ} {r : E → F} {ℓ L β : ℝ} {C S : Set E}
  {P : Settings p} {ε₀ ε₁ : ℝ} {D : Data E} {N : ℕ}

/-- Every actual successful prefix is paid by the exact dyadic initial residual budget. -/
theorem Run.successful_card_le (h : Run r ℓ C P ε₀ ε₁ D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (powerObjective r ℓ) S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
        iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ) (hι : 0 ≤ cascadingExponent p ℓ a 1) :
    ((successfulIterations {i | P.eta1 ≤ D.ratio i} N).card : ℝ) ≤
      lowerSuccessfulIterationConstant false p ℓ a P.sigmaInitial P.sigmaMin P.eta1 P.eta2
        P.gamma3 L P.theta 1 β * lowerBudget false p ℓ a ‖r (D.point 0)‖ /
          lowerAccuracyFactor false p a ε₀ ε₁ 1 + 1 := by
  have hσ := P.sigmaMin_pos.trans_le P.sigmaMin_le_initial
  have hθ : 0 < P.theta := by have := P.theta_lower; have := P.tau_pos; linarith
  have hc := lowerDecreaseCoefficient_pos (η₂ := P.eta2) (γ₃ := P.gamma3) false p ℓ a
    hσ P.sigmaMin_pos P.eta1_pos hL
    hθ zero_lt_one hβ hβ1
  have hinv := inverse_lowerDecreaseCoefficient (η₂ := P.eta2) (γ₃ := P.gamma3) false p ℓ a
    hσ P.sigmaMin_pos P.eta1_pos hL
    hθ zero_lt_one hβ hβ1
  have hKS := hinv ▸ one_div_pos.mpr hc
  have hA := lowerAccuracyFactor_pos false p a h.accuracy_global_pos h.accuracy_first_pos
    zero_lt_one
  have hB := lowerDenominator_pos false p ℓ a ‖r (D.point 0)‖
  cases N with
  | zero =>
    simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]
    have hb := lowerBudget_nonneg (norm_nonneg (r (D.point 0))) false p ℓ a
    positivity
  | succ k =>
    have hd := div_pos (mul_pos hc hA) hB
    have hcount := card_successful_le_gap_div
      (S := {i | P.eta1 ≤ D.ratio i}) (f := fun i => ‖r (D.point i)‖ ^ (1 / (2 : ℝ) ^ a))
      (flow := 0) (k := k) hd (Real.rpow_nonneg (norm_nonneg _) _)
      (fun i hi hs => h.successful_root_decrease hclosed hS hCS hC hf hL hlip hβ hβ1 a hι
        (by omega) hs)
      (fun i hi hu => by
        change ¬P.eta1 ≤ D.ratio i at hu
        rw [h.trace.point_update i (by omega), ite_eq_right hu])
    have hsucc : ((successfulIterations {i | P.eta1 ≤ D.ratio i} (k + 1)).card : ℝ) ≤
        (successfulIterations {i | P.eta1 ≤ D.ratio i} k).card + 1 := by
      exact_mod_cast card_successful_succ_le {i | P.eta1 ≤ D.ratio i} k
    have hR : 0 < ‖r (D.point 0)‖ := h.accuracy_global_pos.trans (h.residual_gt (by omega))
    have heq : (‖r (D.point 0)‖ ^ (1 / (2 : ℝ) ^ a) - 0) /
        (lowerDecreaseCoefficient false p ℓ a P.sigmaInitial P.sigmaMin P.eta1 P.eta2
          P.gamma3 L P.theta 1 β * lowerAccuracyFactor false p a ε₀ ε₁ 1 /
          lowerDenominator false p ℓ a ‖r (D.point 0)‖) =
        lowerSuccessfulIterationConstant false p ℓ a P.sigmaInitial P.sigmaMin P.eta1 P.eta2
          P.gamma3 L P.theta 1 β * lowerBudget false p ℓ a ‖r (D.point 0)‖ /
          lowerAccuracyFactor false p a ε₀ ε₁ 1 := by
      rw [←hinv, ←lowerBudget_eq hR false p ℓ a]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, sub_zero]
      ring
    rw [heq] at hcount
    exact hsucc.trans (add_le_add hcount le_rfl)

/-- Genuine parameter intervals convert the accepted residual budget into the
full number of actual residual trials. -/
theorem Run.iterations_le (h : Run r ℓ C P ε₀ ε₁ D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (powerObjective r ℓ) S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
        iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ) (hι : 0 ≤ cascadingExponent p ℓ a 1) :
    (N : ℝ) ≤ (lowerSuccessfulIterationConstant false p ℓ a P.sigmaInitial P.sigmaMin
      P.eta1 P.eta2 P.gamma3 L P.theta 1 β * lowerBudget false p ℓ a ‖r (D.point 0)‖ /
      lowerAccuracyFactor false p a ε₀ ε₁ 1 + 1) *
        (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (parameterCap P L / P.sigmaInitial) / Real.log P.gamma2 := by
  have ht := iteration_bound_of_parameter_upper
    (S := {i | P.eta1 ≤ D.ratio i}) (fun _ hi => h.trace.updates.pos hi)
    P.gamma1_pos P.gamma1_lt_one P.one_lt_gamma2
    (h.scaledRun.parameter_le hS hCS hC hf hL.le hlip le_rfl)
    (fun _ hi hs => h.trace.updates.successful_ge hi hs)
    (fun _ hi hs => h.trace.updates.unsuccessful_ge hi hs)
  rw [h.initial_parameter] at ht
  have hfac : 0 ≤ 1 + |Real.log P.gamma1| / Real.log P.gamma2 := by
    have := Real.log_pos P.one_lt_gamma2
    positivity
  exact ht.trans (add_le_add (mul_le_mul_of_nonneg_right
    (h.successful_card_le hclosed hS hCS hC hf hL hlip hβ hβ1 a hι) hfac) le_rfl)

/-- Every consistent actual constrained residual execution reaches its first
true residual or normalized first-order criticality stopping alternative. -/
theorem exists_termination (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S)
    (hC : Convex ℝ C) (hf : ContDiffOn ℝ p (powerObjective r ℓ) S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
        iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ) (hι : 0 ≤ cascadingExponent p ℓ a 1)
    (hprefix : ∀ N, (∀ i < N, ¬Stop r ℓ C ε₀ ε₁ (D.point i)) →
      Run r ℓ C P ε₀ ε₁ D N) :
    ∃ K, Stop r ℓ C ε₀ ε₁ (D.point K) ∧ Run r ℓ C P ε₀ ε₁ D K ∧
      ∀ i < K, ¬Stop r ℓ C ε₀ ε₁ (D.point i) := by
  classical
  have hex : ∃ K, Stop r ℓ C ε₀ ε₁ (D.point K) := by
    by_contra hn
    have hnon := not_exists.mp hn
    let bound := (lowerSuccessfulIterationConstant false p ℓ a P.sigmaInitial P.sigmaMin
      P.eta1 P.eta2 P.gamma3 L P.theta 1 β * lowerBudget false p ℓ a ‖r (D.point 0)‖ /
      lowerAccuracyFactor false p a ε₀ ε₁ 1 + 1) *
        (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (parameterCap P L / P.sigmaInitial) / Real.log P.gamma2
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    exact (not_le_of_gt hN) ((hprefix N (fun i _ => hnon i)).iterations_le
      hclosed hS hCS hC hf hL hlip hβ hβ1 a hι)
  have hn : ∀ i < Nat.find hex, ¬Stop r ℓ C ε₀ ε₁ (D.point i) :=
    fun i hi => Nat.find_min hex hi
  exact ⟨Nat.find hex, Nat.find_spec hex, hprefix _ hn, hn⟩

/-- The exact common success constant has the complete printed first-order
formula, with no disabled curvature coefficient left in the result. -/
theorem source_success_constant {p : ℕ} (P : Settings p) (ℓ : ℝ) (a : ℕ)
    {L β : ℝ} (hL : 0 < L) :
    lowerSuccessfulIterationConstant false p ℓ a P.sigmaInitial P.sigmaMin P.eta1 P.eta2
      P.gamma3 L P.theta 1 β =
      max (1 / (1 - β ^ (1 / (2 : ℝ) ^ a)))
        ((2 : ℝ) ^ a / β ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / p) *
          ((p + 1).factorial / (P.eta1 * P.sigmaMin) *
            ((L + parameterCap P L + P.theta * p.factorial) / p.factorial) ^
              (((p + 1 : ℕ) : ℝ) / p))) := by
  rw [←inv_firstDecreaseCoefficient P hL]
  unfold lowerSuccessfulIterationConstant
  simp only [Bool.false_eq_true, ite_false]
  congr 1
  simp only [cascadingConstant, Nat.add_sub_cancel, firstDecreaseCoefficient, parameterCap,
    div_eq_mul_inv, mul_inv_rev, inv_inv]
  push_cast
  ring

/-- Actual derivative sites follow the initialized accepted-point schedule;
first derivatives are skipped if the final residual already passes globally,
and all higher derivatives are restricted to preterminal model points. -/
noncomputable def derivativeEvaluationNodes (r : E → F) (ε₀ : ℝ) {p : ℕ}
    (P : Settings p) (D : Data E) (N j : ℕ) : Finset ℕ := by
  classical
  exact (ConvexRegularization.derivativeEvaluationNodes P D N).filter
    (fun i => i < N ∨ j = 1 ∧ ε₀ < ‖r (D.point i)‖)

/-- The actual initialized per-order residual derivative evaluation count. -/
noncomputable def derivativeEvaluations (r : E → F) (ε₀ : ℝ) {p : ℕ}
    (P : Settings p) (D : Data E) (N j : ℕ) : ℕ :=
  (derivativeEvaluationNodes r ε₀ P D N j).card

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- Every genuine per-order residual derivative schedule fits the common
initialized accepted-point budget, including an initially zero residual. -/
theorem derivativeEvaluations_le (r : E → F) (ε₀ : ℝ) {p : ℕ}
    (P : Settings p) (D : Data E) (N j : ℕ) :
    derivativeEvaluations r ε₀ P D N j ≤ ConvexRegularization.derivativeEvaluations P D N := by
  classical
  exact Finset.card_filter_le _ _

/-- Fixed exact source constants precede every residual/criticality accuracy
and every actual constrained least-norm execution. The first true stop and all
initialized objective and actual per-order derivative counts satisfy the bounds. -/
theorem exists_uniform_complexity {r : E → F} {C S : Set E} {p : ℕ}
    (P : Settings p) (ℓ : ℝ) (a : ℕ) (hclosed : IsClosed C) (hS : IsOpen S)
    (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (powerObjective r ℓ) S) {L β : ℝ} (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
        iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (hι : 0 ≤ cascadingExponent p ℓ a 1) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = max (1 / (1 - β ^ (1 / (2 : ℝ) ^ a)))
        ((2 : ℝ) ^ a / β ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / p) *
          ((p + 1).factorial / (P.eta1 * P.sigmaMin) *
            ((L + parameterCap P L + P.theta * p.factorial) / p.factorial) ^
              (((p + 1 : ℕ) : ℝ) / p))) ∧
      κA = κS * (1 + |Real.log P.gamma1| / Real.log P.gamma2) ∧
      κC = |Real.log P.gamma1| / Real.log P.gamma2 +
        Real.log (parameterCap P L / P.sigmaInitial) / Real.log P.gamma2 + 2 ∧
      ∀ (ε₀ ε₁ : ℝ) (D : Data E),
        (∀ N, (∀ i < N, ¬Stop r ℓ C ε₀ ε₁ (D.point i)) →
          Run r ℓ C P ε₀ ε₁ D N) →
        ∃ K, Stop r ℓ C ε₀ ε₁ (D.point K) ∧ Run r ℓ C P ε₀ ε₁ D K ∧
          (∀ i < K, ¬Stop r ℓ C ε₀ ε₁ (D.point i)) ∧
          (ConvexRegularization.functionEvaluations K : ℝ) ≤
            κA * lowerBudget false p ℓ a ‖r (D.point 0)‖ /
            lowerAccuracyFactor false p a ε₀ ε₁ 1 + κC ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ p →
            (derivativeEvaluations r ε₀ P D K j : ℝ) ≤
            κS * lowerBudget false p ℓ a ‖r (D.point 0)‖ /
              lowerAccuracyFactor false p a ε₀ ε₁ 1 + 2 := by
  let κS := lowerSuccessfulIterationConstant false p ℓ a P.sigmaInitial P.sigmaMin P.eta1
    P.eta2 P.gamma3 L P.theta 1 β
  let A := 1 + |Real.log P.gamma1| / Real.log P.gamma2
  let B := Real.log (parameterCap P L / P.sigmaInitial) / Real.log P.gamma2
  have hσ := P.sigmaMin_pos.trans_le P.sigmaMin_le_initial
  have hθ : 0 < P.theta := by have := P.theta_lower; have := P.tau_pos; linarith
  have hc := lowerDecreaseCoefficient_pos (η₂ := P.eta2) (γ₃ := P.gamma3) false p ℓ a
    hσ P.sigmaMin_pos P.eta1_pos hL hθ
    zero_lt_one hβ hβ1
  have hinv := inverse_lowerDecreaseCoefficient (η₂ := P.eta2) (γ₃ := P.gamma3) false p ℓ a
    hσ P.sigmaMin_pos P.eta1_pos hL
    hθ zero_lt_one hβ hβ1
  have hKS : 0 < κS := by
    dsimp only [κS]
    rw [←hinv]
    exact one_div_pos.mpr hc
  have hA : 0 < A := by have := Real.log_pos P.one_lt_gamma2; dsimp [A]; positivity
  have hratio : 1 ≤ parameterCap P L / P.sigmaInitial := by
    apply (le_div_iff₀ hσ).mpr
    simpa only [one_mul, parameterCap] using
      le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))
  have hB : 0 ≤ B := div_nonneg (Real.log_nonneg hratio) (Real.log_pos P.one_lt_gamma2).le
  refine ⟨κS, hKS, κS * A, by positivity, A + B + 1, by positivity,
    source_success_constant P ℓ a hL, rfl, ?_, ?_⟩
  · dsimp [A, B]
    ring
  intro ε₀ ε₁ D hprefix
  obtain ⟨K, hstop, hK, hfirst⟩ := exists_termination hclosed hS hCS hC hf hL hlip
    hβ hβ1 a hι hprefix
  have hF := hK.iterations_le hclosed hS hCS hC hf hL hlip hβ hβ1 a hι
  have hD := hK.successful_card_le hclosed hS hCS hC hf hL hlip hβ hβ1 a hι
  refine ⟨K, hstop, hK, hfirst, ?_, ?_⟩
  · simp only [ConvexRegularization.functionEvaluations, Nat.cast_add, Nat.cast_one]
    convert add_le_add hF (le_refl (1 : ℝ)) using 1
    dsimp [κS, A, B]
    ring
  · intro j _ _
    have hb := add_le_add hD (le_refl (1 : ℝ))
    have hcount : (derivativeEvaluations r ε₀ P D K j : ℝ) ≤
        (successfulIterations {i | P.eta1 ≤ D.ratio i} K).card + 1 := by
      have hh : (derivativeEvaluations r ε₀ P D K j : ℝ) ≤
          ConvexRegularization.derivativeEvaluations P D K := by
        exact_mod_cast derivativeEvaluations_le r ε₀ P D K j
      rwa [ConvexRegularization.derivativeEvaluations_eq, Nat.cast_add, Nat.cast_one] at hh
    exact hcount.trans (by simpa only [add_assoc, one_add_one_eq_two] using hb)

end ConvexLeastSquares
