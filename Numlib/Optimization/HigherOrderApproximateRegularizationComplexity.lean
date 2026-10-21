import Numlib.Optimization.HigherOrderApproximateRegularizationBounds
import Numlib.Optimization.HigherOrderRegularizationComplexity
import Numlib.Optimization.EvaluationComplexity

/-!
# Actual outer executions and first true criterion attainment

The transition relation determines executed trial steps, interval updates and evaluation
costs. Rejected trials reuse the complete derivative cache. Conservative computed witnesses
may continue after the true compact-gap criterion has already been attained.
-/

noncomputable section
open scoped Nat
namespace Optimization.HigherOrderApproximateRegularization
open RegularizedTaylorModel TaylorCriticality ParameterUpdates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Data extracted from an actual continuing outer transition. The structure records the
constructor's trial and costs rather than any convergence conclusion. -/
structure ExecutedTrial (P : Parameters) (f : E → ℝ) (a b : OuterState E)
    (functionCalls derivativeCalls : ℕ) where
  trial : ModelStep P f a.point a.sigma a.radii
  strict : model f P.p a.point a.sigma trial.step < model f P.p a.point a.sigma 0
  nextSigma : ℝ
  update : ParameterUpdate P
    ((f a.point - f (a.point + trial.step)) / taylorDecrement f P.p a.point trial.step)
      a.sigma nextSigma
  next_state : b = if P.eta1 ≤
      (f a.point - f (a.point + trial.step)) / taylorDecrement f P.p a.point trial.step
    then ⟨a.point + trial.step, nextSigma, trial.radii, 0, true⟩
    else ⟨a.point, nextSigma, a.radii, P.p, false⟩
  function_cost : functionCalls = 1
  derivative_cost : derivativeCalls = P.p - a.cachedOrder

/-- A continuing outer transition supplies actual trial data. -/
theorem OuterTransition.exists_executedTrial {P : Parameters} {f : E → ℝ}
    {a b : OuterState E} {nf nd : ℕ} (h : OuterTransition P f a (.next b) nf nd) :
    Nonempty (ExecutedTrial P f a b nf nd) := by
  cases h with
  | trial a hfail trial hstrict nextSigma hupdate =>
    exact ⟨⟨trial, hstrict, nextSigma, hupdate, rfl, rfl, rfl⟩⟩

/-- Every executed strict model trial has a nonzero displacement. -/
theorem ExecutedTrial.step_ne_zero {P : Parameters} {f : E → ℝ}
    {a b : OuterState E} {nf nd : ℕ} (t : ExecutedTrial P f a b nf nd) : t.trial.step ≠ 0 := by
  intro he
  have h := t.strict
  rw [he] at h
  exact (lt_irrefl _ h)

/-- The canonical ratio agrees with the ratio used by the actual transition constructor. -/
theorem ExecutedTrial.ratio_eq {P : Parameters} {f : E → ℝ}
    {a b : OuterState E} {nf nd : ℕ} (t : ExecutedTrial P f a b nf nd) :
    HigherOrderRegularization.ratio f P.p a.point t.trial.step =
      (f a.point - f (a.point + t.trial.step)) /
        taylorDecrement f P.p a.point t.trial.step := by
  simp only [HigherOrderRegularization.ratio, ite_eq_right t.step_ne_zero, taylorDecrement]

/-- The constructor's next parameter is the parameter in the next actual state. -/
theorem ExecutedTrial.next_sigma {P : Parameters} {f : E → ℝ}
    {a b : OuterState E} {nf nd : ℕ} (t : ExecutedTrial P f a b nf nd) :
    b.sigma = t.nextSigma := by
  have h := congrArg OuterState.sigma t.next_state
  split_ifs at h <;> exact h

/-- The actual successor point follows the constructor's acceptance decision. -/
theorem ExecutedTrial.next_point {P : Parameters} {f : E → ℝ}
    {a b : OuterState E} {nf nd : ℕ} (t : ExecutedTrial P f a b nf nd) :
    b.point = if P.eta1 ≤ HigherOrderRegularization.ratio f P.p a.point t.trial.step
      then a.point + t.trial.step else a.point := by
  rw [t.ratio_eq]
  have h := congrArg OuterState.point t.next_state
  split_ifs at * <;> exact h

/-- Acceptance resets the derivative cache; rejection retains every model derivative. -/
theorem ExecutedTrial.next_cache {P : Parameters} {f : E → ℝ}
    {a b : OuterState E} {nf nd : ℕ} (t : ExecutedTrial P f a b nf nd) :
    b.cachedOrder = if P.eta1 ≤ HigherOrderRegularization.ratio f P.p a.point t.trial.step
      then 0 else P.p := by
  rw [t.ratio_eq]
  have h := congrArg OuterState.cachedOrder t.next_state
  split_ifs at * <;> exact h

/-- The successor radius vector follows the actual acceptance decision. -/
theorem ExecutedTrial.next_radii {P : Parameters} {f : E → ℝ}
    {a b : OuterState E} {nf nd : ℕ} (t : ExecutedTrial P f a b nf nd) :
    b.radii = if P.eta1 ≤ HigherOrderRegularization.ratio f P.p a.point t.trial.step
      then t.trial.radii else a.radii := by
  rw [t.ratio_eq]
  have h := congrArg OuterState.radii t.next_state
  split_ifs at * <;> exact h

/-- Actual trial data for an index before the endpoint of a finite outer execution. -/
def OuterExecution.executedTrial {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) (k : ℕ) (hk : k < N) :
    ExecutedTrial P f (run.state k) (run.state (k + 1))
      (run.functionCalls k) (run.derivativeCalls k) :=
  Classical.choice ((run.transition k hk).exists_executedTrial)

/-- The actual step sequence, extended by zero beyond the executed prefix. -/
def OuterExecution.step {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) (k : ℕ) : E :=
  if hk : k < N then (run.executedTrial k hk).trial.step else 0

/-- Inside the prefix the extracted step is precisely the actual constructor's trial step. -/
theorem OuterExecution.step_eq {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) {k : ℕ} (hk : k < N) :
    run.step k = (run.executedTrial k hk).trial.step := by simp only [step, dite_eq_left hk]

/-- Every legal outer execution is a canonical finite regularization trial prefix,
with its actual points, parameters and extracted executed steps. -/
theorem OuterExecution.trialPrefix {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) :
    HigherOrderRegularization.TrialPrefix P.toRegularizationParameters P.p f
      (fun k => (run.state k).point) run.step (fun k => (run.state k).sigma) N where
  initial_lower := (run.valid 0 (Nat.zero_le N)).1
  update := by
    intro k hk
    rw [run.step_eq hk]
    let t := run.executedTrial k hk
    change ParameterUpdate P (HigherOrderRegularization.ratio f P.p
      (run.state k).point t.trial.step) (run.state k).sigma (run.state (k + 1)).sigma
    rw [t.ratio_eq, t.next_sigma]
    exact t.update
  decrease := by
    intro k hk
    rw [run.step_eq hk]
    exact (run.executedTrial k hk).strict
  iterate := by
    intro k hk
    rw [run.step_eq hk]
    exact (run.executedTrial k hk).next_point

/-- Count passes that actually evaluate at least one new derivative order. -/
def OuterExecution.derivativeBatchCount {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) : ℕ :=
  ∑ k ∈ Finset.range (N + 1), if run.derivativeCalls k = 0 then 0 else 1

/-- A legal outer pass evaluates the objective at most once. -/
theorem OuterTransition.function_cost_le {P : Parameters} {f : E → ℝ}
    {a : OuterState E} {b : OuterOutcome E} {nf nd : ℕ}
    (h : OuterTransition P f a b nf nd) : nf ≤ 1 := by
  cases h <;> omega

/-- A full derivative cache eliminates every derivative evaluation on the next pass. -/
theorem OuterTransition.derivative_cost_eq_zero {P : Parameters} {f : E → ℝ}
    {a : OuterState E} {b : OuterOutcome E} {nf nd : ℕ}
    (h : OuterTransition P f a b nf nd) (hc : a.cachedOrder = P.p) : nd = 0 := by
  cases h <;> simp_all [Nat.sub_eq_zero_of_le P.order_le]

/-- Initial derivative data have not yet been evaluated. -/
theorem OuterExecution.initial_cache {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) :
    (run.state 0).cachedOrder = 0 := congrArg OuterState.cachedOrder run.initial.2.2

/-- A reachable cache is empty after acceptance, or complete after rejection. -/
theorem OuterExecution.cache_cases {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) {k : ℕ} (hk : k ≤ N) :
    (run.state k).cachedOrder = 0 ∨ (run.state k).cachedOrder = P.p := by
  cases k with
  | zero => exact Or.inl run.initial_cache
  | succ k =>
    rw [(run.executedTrial k (by omega)).next_cache]
    split_ifs <;> simp

/-- Every derivative batch can be charged to an empty actual cache. -/
theorem OuterExecution.batch_le_empty_cache {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) {k : ℕ} (hk : k ≤ N) :
    (if run.derivativeCalls k = 0 then 0 else 1) ≤
      (if (run.state k).cachedOrder = 0 then 1 else 0) := by
  classical
  rcases run.cache_cases hk with hc | hc
  · simp only [hc, ↓reduceIte]
    split_ifs <;> omega
  · have hd : run.derivativeCalls k = 0 := by
      by_cases hkn : k < N
      · exact (run.transition k hkn).derivative_cost_eq_zero hc
      · have he : k = N := by omega
        subst k
        exact run.final.derivative_cost_eq_zero hc
    simp [hd]

/-- The initial cache and each accepted trial account for every actual derivative batch. -/
theorem OuterExecution.derivativeBatchCount_le {P : Parameters} {f : E → ℝ} {x : E}
    {σ : ℝ} {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) :
    run.derivativeBatchCount ≤ successCount
      (fun k => P.eta1 ≤ HigherOrderRegularization.ratio f P.p (run.state k).point (run.step k)) N
        + 1 := by
  classical
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), if (run.state k).cachedOrder = 0 then 1 else 0 :=
      Finset.sum_le_sum (fun k hk => run.batch_le_empty_cache (by
        have := Finset.mem_range.mp hk; omega))
    _ = _ := by
      rw [Finset.sum_range_succ']
      simp only [run.initial_cache, ↓reduceIte]
      congr 1
      unfold successCount
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn := Finset.mem_range.mp hk
      simp only [(run.executedTrial k hkn).next_cache, run.step_eq hkn]
      have hp : P.p ≠ 0 := ne_of_gt
        (lt_of_lt_of_le Nat.zero_lt_one (P.order_pos.trans P.order_le))
      split_ifs <;> simp_all

/-- The actual objective-call count includes initialization and at most one final pass. -/
theorem OuterExecution.functionCount_le {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) :
    run.functionCount ≤ N + 2 := by
  unfold functionCount
  have hb : ∑ k ∈ Finset.range (N + 1), run.functionCalls k ≤ N + 1 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (N + 1), 1 := Finset.sum_le_sum (fun k hk => by
        have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
        by_cases hkn : k < N
        · exact (run.transition k hkn).function_cost_le
        · have he : k = N := by omega
          subst k
          exact run.final.function_cost_le)
      _ = N + 1 := by simp
  omega

/-- Truncate an actual execution at a legal prefix endpoint, retaining actual costs. -/
def OuterExecution.prefix {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N)
    (K : ℕ) (hK : K ≤ N) : OuterExecution P f x σ δ K where
  state := run.state
  functionCalls := run.functionCalls
  derivativeCalls := run.derivativeCalls
  last := if K < N then .next (run.state (K + 1)) else run.last
  initial := run.initial
  valid k hk := run.valid k (hk.trans hK)
  transition k hk := run.transition k (hk.trans_le hK)
  final := by
    split_ifs with hkn
    · exact run.transition K hkn
    · have he : K = N := by omega
      subst K
      exact run.final

/-- Every continuing pass evaluates the objective once. -/
theorem OuterExecution.le_functionCount {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) : N ≤ run.functionCount := by
  have hb : N ≤ ∑ k ∈ Finset.range (N + 1), run.functionCalls k := by
    calc
      N = ∑ _k ∈ Finset.range N, 1 := by simp
      _ = ∑ k ∈ Finset.range N, run.functionCalls k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (run.executedTrial k (Finset.mem_range.mp hk)).function_cost.symm
      _ ≤ ∑ k ∈ Finset.range (N + 1), run.functionCalls k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun _ _ _ => Nat.zero_le _)
  unfold functionCount
  omega

/-- The structural upper bound on every executed regularization parameter. -/
def parameterUpper (P : Parameters) (σ L : ℝ) : ℝ :=
  max σ (P.gamma3 * (L / (1 - P.eta2)))

/-- The positive multiplier converting successful trials to all trials. -/
def trialMultiplier (P : Parameters) : ℝ :=
  1 + |Real.log P.gamma1| / Real.log P.gamma2

/-- The initialization-dependent additive regularization budget. -/
def parameterBudget (P : Parameters) (σ L : ℝ) : ℝ :=
  Real.log (parameterUpper P σ L / σ) / Real.log P.gamma2

/-- The successful-trial complexity coefficient uses structural data only. -/
def derivativeComplexityCoefficient (P : Parameters) (σ L κ : ℝ) : ℝ :=
  (P.eta1 * modelDecreaseConstant P.p P.q P.order_pos P.theta
    (L + parameterUpper P σ L) κ P.sigmaMin)⁻¹

/-- The objective-call complexity coefficient uses structural data only. -/
def functionComplexityCoefficient (P : Parameters) (σ L κ : ℝ) : ℝ :=
  trialMultiplier P * derivativeComplexityCoefficient P σ L κ

/-- The additive objective-call budget, including initialization and the endpoint pass. -/
def additiveComplexityConstant (P : Parameters) (σ L : ℝ) : ℝ :=
  trialMultiplier P + parameterBudget P σ L + 2

/-- All three coefficients are positive when the initial parameter and radius scale are legal.
Their formulas contain no requested tolerance. -/
theorem complexityCoefficients_pos (P : Parameters) {σ L κ : ℝ}
    (hσ : P.sigmaMin ≤ σ) (hL : 1 ≤ L) (hκ : 0 < κ) :
    0 < derivativeComplexityCoefficient P σ L κ ∧
      0 < functionComplexityCoefficient P σ L κ ∧
        0 < additiveComplexityConstant P σ L := by
  have hσ0 := P.sigmaMin_pos.trans_le hσ
  have hS : 0 < parameterUpper P σ L := hσ0.trans_le (le_max_left _ _)
  have hC : 0 < L + parameterUpper P σ L := by linarith
  have hA := modelDecreaseConstant_pos P.p P.q P.order_pos P.theta_lt_one hC hκ P.sigmaMin_pos
  have hd : 0 < derivativeComplexityCoefficient P σ L κ := inv_pos.mpr (mul_pos P.eta1_pos hA)
  have hM : 0 < trialMultiplier P := by
    unfold trialMultiplier
    have := div_nonneg (abs_nonneg (Real.log P.gamma1))
      (Real.log_pos P.one_lt_gamma2).le
    linarith
  have hD : 0 ≤ parameterBudget P σ L := by
    apply div_nonneg _ (Real.log_pos P.one_lt_gamma2).le
    apply Real.log_nonneg
    apply (le_div_iff₀ hσ0).mpr
    simpa only [one_mul] using (show σ ≤ parameterUpper P σ L from le_max_left _ _)
  refine ⟨hd, mul_pos hM hd, ?_⟩
  unfold additiveComplexityConstant
  linarith

/-- Factoring the tolerance scale exhibits the tolerance-independent leading coefficient. -/
theorem decrease_budget_eq (P : Parameters) (σ L κ gap T : ℝ) :
    gap / (P.eta1 * (modelDecreaseConstant P.p P.q P.order_pos P.theta
      (L + parameterUpper P σ L) κ P.sigmaMin * T)) =
        derivativeComplexityCoefficient P σ L κ * (gap / T) := by
  simp only [derivativeComplexityCoefficient, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The initial state carries the declared initial point. -/
theorem OuterExecution.initial_point {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) :
    (run.state 0).point = x := congrArg OuterState.point run.initial.2.2

/-- The initial state carries the declared initial parameter. -/
theorem OuterExecution.initial_sigma {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N) :
    (run.state 0).sigma = σ := congrArg OuterState.sigma run.initial.2.2

section FiniteDimensional
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- The parameter bound is derived from the actual model prediction and update intervals. -/
theorem OuterExecution.sigma_upper {P : Parameters} {f : F → ℝ} {x : F} {σ L : ℝ}
    {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x σ δ N)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) {k : ℕ} (hk : k ≤ N) :
    (run.state k).sigma ≤ parameterUpper P σ L := by
  simpa only [run.initial_sigma, parameterUpper] using
    run.trialPrefix.sigma_upper hf (P.order_pos.trans P.order_le) hk

/-- An accepted actual trial before true successor attainment pays the uniform decrease. -/
theorem OuterExecution.accepted_decrease_of_true_gap_failure
    {P : Parameters} {f : F → ℝ} {x : F} {σ L κ : ℝ} {δ : ℕ → ℝ} {N : ℕ}
    (run : OuterExecution P f x σ δ N)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L) (hκ : 0 < κ)
    {k : ℕ} (hk : k < N)
    (hunit : P.q ≤ 2 → ∀ j, 1 ≤ j → j ≤ P.q → (run.executedTrial k hk).trial.radii j = 1)
    (hlower : 2 < P.q → ∀ j, 1 ≤ j → j ≤ P.q →
      κ * P.epsilon j ≤ (run.executedTrial k hk).trial.radii j)
    (hs : P.eta1 ≤ HigherOrderRegularization.ratio f P.p (run.state k).point (run.step k))
    (hfail : ¬SatisfiesCriteria P f (run.state (k + 1)).point (run.state (k + 1)).radii) :
    P.eta1 * (modelDecreaseConstant P.p P.q P.order_pos P.theta
      (L + parameterUpper P σ L) κ P.sigmaMin *
        toleranceMeasure P.p P.q P.order_pos P.epsilon) ≤
      f (run.state k).point - f (run.state (k + 1)).point := by
  let t := run.executedTrial k hk
  have hs' : P.eta1 ≤ HigherOrderRegularization.ratio f P.p (run.state k).point t.trial.step := by
    simpa only [run.step_eq hk] using hs
  have hp := t.next_point
  have hr := t.next_radii
  rw [ite_eq_left hs'] at hp hr
  have hfail' : ¬SatisfiesCriteria P f ((run.state k).point + t.trial.step) t.trial.radii := by
    simpa only [hp, hr] using hfail
  rw [hp]
  exact Optimization.HigherOrderApproximateRegularization.accepted_decrease_of_true_gap_failure
    hf hL t.trial t.step_ne_zero
    (run.valid k hk.le).1 (run.sigma_upper hf hk.le) hκ hunit hlower hfail'
    (by simpa only [t.ratio_eq] using hs')

/-- Before first true attainment, actual objective and cached derivative evaluations satisfy
both all-order tolerance exponent regimes. The endpoint pass is included explicitly. -/
theorem OuterExecution.evaluation_bounds_before_true_attainment
    {P : Parameters} {f : F → ℝ} {x : F} {σ L κ low : ℝ} {δ : ℕ → ℝ} {N : ℕ}
    (run : OuterExecution P f x σ δ N)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L) (hκ : 0 < κ)
    (hlow : ∀ y, low ≤ f y)
    (hunit : ∀ k (hk : k < N), P.q ≤ 2 →
      ∀ j, 1 ≤ j → j ≤ P.q → (run.executedTrial k hk).trial.radii j = 1)
    (hlower : ∀ k (hk : k < N), 2 < P.q →
      ∀ j, 1 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ (run.executedTrial k hk).trial.radii j)
    (hfirst : ∀ k < N, ¬SatisfiesCriteria P f (run.state k).point (run.state k).radii) :
    let A := modelDecreaseConstant P.p P.q P.order_pos P.theta
      (L + parameterUpper P σ L) κ P.sigmaMin
    let T := toleranceMeasure P.p P.q P.order_pos P.epsilon
    (run.functionCount : ℝ) ≤ trialMultiplier P * ((f x - low) / (P.eta1 * (A * T))) +
        trialMultiplier P + parameterBudget P σ L + 2 ∧
      (run.derivativeBatchCount : ℝ) ≤ (f x - low) / (P.eta1 * (A * T)) + 2 := by
  dsimp only
  have hS : 0 ≤ parameterUpper P σ L :=
    P.sigmaMin_pos.le.trans (run.initial.1.trans (le_max_left _ _))
  have hC : 0 < L + parameterUpper P σ L := by linarith
  have hA := modelDecreaseConstant_pos P.p P.q P.order_pos P.theta_lt_one hC hκ P.sigmaMin_pos
  have hd := mul_pos P.eta1_pos (mul_pos hA (toleranceMeasure_pos P))
  have hs := run.trialPrefix.success_count_le hd
    (fun k _ => hlow (run.state k).point)
    (fun k hk hacc hfail => run.accepted_decrease_of_true_gap_failure hf hL hκ hk
      (hunit k hk) (hlower k hk) hacc hfail) hfirst
  rw [run.initial_point] at hs
  have ht := run.trialPrefix.toRegularizationPrefix.total_count_le le_rfl
    (run.sigma_upper hf le_rfl)
  rw [run.initial_sigma] at ht
  have hM : 0 ≤ trialMultiplier P := add_nonneg zero_le_one
    (div_nonneg (abs_nonneg _) (Real.log_pos P.one_lt_gamma2).le)
  have hm := mul_le_mul_of_nonneg_right hs hM
  have hnf : (run.functionCount : ℝ) ≤ (N : ℝ) + 2 := by
    exact_mod_cast run.functionCount_le
  have hnd : (run.derivativeBatchCount : ℝ) ≤
      (successCount (fun k => P.eta1 ≤ HigherOrderRegularization.ratio f P.p
        (run.state k).point (run.step k)) N : ℝ) + 1 := by
    exact_mod_cast run.derivativeBatchCount_le
  change (N : ℝ) ≤ _ * trialMultiplier P + parameterBudget P σ L at ht
  constructor <;> linarith

/-- A sufficiently long actual execution contains a first true criterion point, and the
actual truncated evaluation counts obey both source tolerance exponents. No claim is made
that the conservative computed stopping test terminates at that point. -/
theorem OuterExecution.first_true_attainment_bounds
    {P : Parameters} {f : F → ℝ} {x : F} {σ L κ low : ℝ} {δ : ℕ → ℝ} {N : ℕ}
    (run : OuterExecution P f x σ δ N)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L) (hκ : 0 < κ)
    (hlow : ∀ y, low ≤ f y)
    (hunit : ∀ k (hk : k < N), P.q ≤ 2 →
      ∀ j, 1 ≤ j → j ≤ P.q → (run.executedTrial k hk).trial.radii j = 1)
    (hlower : ∀ k (hk : k < N), 2 < P.q →
      ∀ j, 1 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ (run.executedTrial k hk).trial.radii j)
    (hN : trialMultiplier P * ((f x - low) /
      (P.eta1 * (modelDecreaseConstant P.p P.q P.order_pos P.theta
        (L + parameterUpper P σ L) κ P.sigmaMin *
          toleranceMeasure P.p P.q P.order_pos P.epsilon))) +
            trialMultiplier P + parameterBudget P σ L + 2 < N) :
    let A := modelDecreaseConstant P.p P.q P.order_pos P.theta
      (L + parameterUpper P σ L) κ P.sigmaMin
    let T := toleranceMeasure P.p P.q P.order_pos P.epsilon
    ∃ K : ℕ, ∃ hK : K ≤ N,
      SatisfiesCriteria P f (run.state K).point (run.state K).radii ∧
      (∀ k < K, ¬SatisfiesCriteria P f (run.state k).point (run.state k).radii) ∧
      ((run.prefix K hK).functionCount : ℝ) ≤
        trialMultiplier P * ((f x - low) / (P.eta1 * (A * T))) +
          trialMultiplier P + parameterBudget P σ L + 2 ∧
      ((run.prefix K hK).derivativeBatchCount : ℝ) ≤ (f x - low) / (P.eta1 * (A * T)) + 2 := by
  classical
  dsimp only
  have hex : ∃ K ≤ N, SatisfiesCriteria P f (run.state K).point (run.state K).radii := by
    by_contra! h
    have hb := (run.evaluation_bounds_before_true_attainment hf hL hκ hlow hunit hlower
      (fun k hk => h k hk.le)).1
    have hn : (N : ℝ) ≤ run.functionCount := by exact_mod_cast run.le_functionCount
    linarith
  have hex' : ∃ K, SatisfiesCriteria P f (run.state K).point (run.state K).radii := by
    obtain ⟨K, _, ht⟩ := hex
    exact ⟨K, ht⟩
  let K := Nat.find hex'
  have hK : K ≤ N := by
    obtain ⟨n, hn, ht⟩ := hex
    exact (Nat.find_min' hex' ht).trans hn
  have hfirst : ∀ k < K, ¬SatisfiesCriteria P f (run.state k).point (run.state k).radii :=
    fun k hk => Nat.find_min hex' hk
  refine ⟨K, hK, Nat.find_spec hex', hfirst, ?_⟩
  exact (run.prefix K hK).evaluation_bounds_before_true_attainment hf hL hκ hlow
    (fun k hk => hunit k (hk.trans_le hK)) (fun k hk => hlower k (hk.trans_le hK)) hfirst

/-- First attainment from coherent actual legal prefixes. The availability premise concerns
operational prefixes only; every analytic decrease and evaluation bound is derived here.
A point predicate may allow a newly returned radius vector at an equality stop. -/
theorem exists_first_true_attainment_of_legal_prefixes
    {P : Parameters} {f : F → ℝ} {x : F} {σ L κ low : ℝ} {δ : ℕ → ℝ}
    (state : ℕ → OuterState F) (Q : F → Prop)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L) (hκ : 0 < κ)
    (hlow : ∀ y, low ≤ f y)
    (hcert : ∀ k, SatisfiesCriteria P f (state k).point (state k).radii → Q (state k).point)
    (hprefix : ∀ N, (∀ k < N, ¬Q (state k).point) →
      ∃ run : OuterExecution P f x σ δ N, run.state = state)
    (hunit : ∀ N (run : OuterExecution P f x σ δ N), run.state = state →
      ∀ k (hk : k < N), P.q ≤ 2 →
        ∀ j, 1 ≤ j → j ≤ P.q → (run.executedTrial k hk).trial.radii j = 1)
    (hlower : ∀ N (run : OuterExecution P f x σ δ N), run.state = state →
      ∀ k (hk : k < N), 2 < P.q →
        ∀ j, 1 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ (run.executedTrial k hk).trial.radii j) :
    let A := modelDecreaseConstant P.p P.q P.order_pos P.theta
      (L + parameterUpper P σ L) κ P.sigmaMin
    let T := toleranceMeasure P.p P.q P.order_pos P.epsilon
    ∃ K : ℕ, Q (state K).point ∧ (∀ k < K, ¬Q (state k).point) ∧
      ∃ run : OuterExecution P f x σ δ K, run.state = state ∧
        (run.functionCount : ℝ) ≤ trialMultiplier P * ((f x - low) / (P.eta1 * (A * T))) +
          trialMultiplier P + parameterBudget P σ L + 2 ∧
        (run.derivativeBatchCount : ℝ) ≤ (f x - low) / (P.eta1 * (A * T)) + 2 := by
  dsimp only
  have hb : ∀ N, (∀ k < N, ¬Q (state k).point) →
      (N : ℝ) ≤ trialMultiplier P * ((f x - low) /
        (P.eta1 * (modelDecreaseConstant P.p P.q P.order_pos P.theta
          (L + parameterUpper P σ L) κ P.sigmaMin *
            toleranceMeasure P.p P.q P.order_pos P.epsilon))) +
              trialMultiplier P + parameterBudget P σ L + 2 := by
    intro N hn
    obtain ⟨run, he⟩ := hprefix N hn
    have hfirst : ∀ k < N, ¬SatisfiesCriteria P f (run.state k).point (run.state k).radii := by
      intro k hk hc
      apply hn k hk
      exact hcert k (by simpa only [he] using hc)
    have heval := (run.evaluation_bounds_before_true_attainment hf hL hκ hlow
      (hunit N run he) (hlower N run he) hfirst).1
    exact (show (N : ℝ) ≤ run.functionCount by exact_mod_cast run.le_functionCount).trans heval
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hb
  obtain ⟨run, he⟩ := hprefix K hfirst
  refine ⟨K, hK, hfirst, run, he, ?_⟩
  apply run.evaluation_bounds_before_true_attainment hf hL hκ hlow
    (hunit K run he) (hlower K run he)
  intro k hk hc
  apply hfirst k hk
  exact hcert k (by simpa only [he] using hc)

end FiniteDimensional
end Optimization.HigherOrderApproximateRegularization
