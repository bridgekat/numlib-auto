import NumlibSurface.CartisGouldToint.Chapter12.Section02.ModelBounds
import Numlib.Optimization.HigherOrderApproximateRegularizationBounds
import Numlib.Optimization.TaylorCriticalityFirstOrder

/-!
# ARqp bounds before true criterion attainment

The conservative computed witness test may fail after true approximate optimality already
holds. The literal source nontermination inference therefore needs a separate true-gap premise.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter12.Section02
open Optimization
open HigherOrderApproximateRegularization RegularizedTaylorModel TaylorCriticality

private def counterParameters : HigherOrderApproximateRegularization.Parameters where
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 1
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := by norm_num
  p := 1
  q := 1
  order_pos := le_rfl
  order_le := le_rfl
  epsilon := fun _ => 1 / 2
  epsilon_pos := by intros; norm_num
  epsilon_lt_one := by intros; norm_num
  theta := 1 / 2
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  fraction := 1 / 100
  fraction_pos := by norm_num
  fraction_le_one := by norm_num

private def counterObjective (x : ℝ) : ℝ := x ^ 2 / 2 - x / 100

private theorem counter_deriv (x : ℝ) : deriv counterObjective x = x - 1 / 100 := by
  have h := (((hasDerivAt_id x).pow 2).div_const 2).sub
    ((hasDerivAt_id x).div_const 100)
  change HasDerivAt counterObjective _ x at h
  rw [h.deriv]
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

private theorem counter_model (x t : ℝ) :
    model counterObjective 1 x 2 t = counterObjective x + (x - 1 / 100) * t + t ^ 2 := by
  change taylorModel counterObjective 1 x t +
    2 / ((1 + 1)! : ℝ) * ‖t‖ ^ (1 + 1) = _
  rw [taylorModel_one, fderiv_eq_deriv_mul, counter_deriv]
  norm_num [Real.norm_eq_abs, sq_abs]

private theorem counter_model_deriv (x t : ℝ) :
    deriv (model counterObjective 1 x 2) t = x - 1 / 100 + 2 * t := by
  have he : model counterObjective 1 x 2 =
      fun t => counterObjective x + (x - 1 / 100) * t + t ^ 2 := funext (counter_model x)
  rw [he]
  have h := ((hasDerivAt_const t (counterObjective x)).add
    ((hasDerivAt_id t).const_mul (x - 1 / 100))).add ((hasDerivAt_id t).pow 2)
  simp only [id_eq] at h
  change HasDerivAt (fun t : ℝ => counterObjective x + (x - 1 / 100) * t + t ^ 2) _ t at h
  rw [h.deriv]
  simp

private theorem gap_one (f : ℝ → ℝ) (x : ℝ) :
    gapOn (taylorDecrement f 1 x) (Metric.closedBall 0 1) = |deriv f x| := by
  rw [gapOn_taylorDecrement_one _ _ (by norm_num), one_mul,
    ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]

private def counterStep (x : ℝ) :
    ModelStep counterParameters counterObjective x 2 (fun _ => 1) where
  step := (1 / 100 - x) / 2
  radii := fun _ => 1
  radii_valid := by intro j _ _; norm_num
  nonincrease := by
    change model counterObjective 1 x 2 ((1 / 100 - x) / 2) ≤ model counterObjective 1 x 2 0
    rw [counter_model, counter_model]
    nlinarith [sq_nonneg (x - 1 / 100)]
  direction := fun _ => 0
  quality := Or.inr (by
    intro j hj hjq
    have hj1 : j = 1 := by change j ≤ 1 at hjq; omega
    subst j
    constructor
    · constructor
      · norm_num
      · change counterParameters.fraction * gapOn
          (taylorDecrement (model counterObjective 1 x 2) 1 ((1 / 100 - x) / 2))
          (Metric.closedBall 0 1) ≤ taylorDecrement (model counterObjective 1 x 2) 1
            ((1 / 100 - x) / 2) 0
        rw [gap_one, counter_model_deriv]
        norm_num [counterParameters]
        ring_nf
        norm_num
    · rw [taylorDecrement_one, fderiv_eq_deriv_mul]
      norm_num [counterParameters])

private def counterFailed : FailedTest counterParameters counterObjective (1 / 200 : ℝ)
    (fun _ => 1) where
  order := 1
  order_pos := le_rfl
  order_le := le_rfl
  direction := fun _ => 1
  witness := by
    intro j hj hj1
    have hjj : j = 1 := by omega
    subst j
    constructor
    · norm_num
    · rw [gap_one, counter_deriv, taylorDecrement_one, fderiv_eq_deriv_mul, counter_deriv]
      norm_num [counterParameters]
  earlier := by intro j hj hj1; omega
  fails := by
    rw [taylorDecrement_one, fderiv_eq_deriv_mul, counter_deriv]
    norm_num [counterParameters]

private def counterFailedInitial : FailedTest counterParameters counterObjective (0 : ℝ)
    (fun _ => 1) where
  order := 1
  order_pos := le_rfl
  order_le := le_rfl
  direction := fun _ => 1
  witness := by
    intro j hj hj1
    have hjj : j = 1 := by omega
    subst j
    constructor
    · norm_num
    · rw [gap_one, counter_deriv, taylorDecrement_one, fderiv_eq_deriv_mul, counter_deriv]
      norm_num [counterParameters]
  earlier := by intro j hj hj1; omega
  fails := by
    rw [taylorDecrement_one, fderiv_eq_deriv_mul, counter_deriv]
    norm_num [counterParameters]

private theorem counter_transition (x : ℝ)
    (hfail : Nonempty (FailedTest counterParameters counterObjective x (fun _ => 1)))
    (hstrict : model counterObjective 1 x 2 (counterStep x).step <
      model counterObjective 1 x 2 0)
    (hratio : (counterObjective x - counterObjective (x + (counterStep x).step)) /
      taylorDecrement counterObjective 1 x (counterStep x).step = 3 / 4) :
    OuterTransition counterParameters counterObjective ⟨x, 2, fun _ => 1, 0, true⟩
      (.next ⟨x + (counterStep x).step, 2, fun _ => 1, 0, true⟩) 1 1 := by
  have hu : ParameterUpdate counterParameters
      ((counterObjective x - counterObjective (x + (counterStep x).step)) /
        taylorDecrement counterObjective 1 x (counterStep x).step) 2 2 := by
    rw [hratio]
    norm_num [ParameterUpdate, counterParameters]
  have ht := OuterTransition.trial ⟨x, 2, fun _ => 1, 0, true⟩ (fun _ => hfail)
    (show 0 ≤ counterParameters.p by decide) (counterStep x) hstrict 2 hu
  simpa only [show counterParameters.p = 1 from rfl, hratio,
    show counterParameters.eta1 = 1 / 4 from rfl,
    show (counterStep x).radii = fun _ => 1 from rfl,
    show (1 / 4 : ℝ) ≤ 3 / 4 by norm_num, ↓reduceIte, Nat.sub_zero] using ht

/-- Literal conservative ARqp test failure can persist at true approximate optimality,
and its accepted exact model step violates all three printed constants in Lemmas 11–13. -/
theorem conservative_test_counterexample :
    ∃ (P : HigherOrderApproximateRegularization.Parameters) (f : ℝ → ℝ)
      (trial : ModelStep P f 0 2 (fun _ => 1)),
      P.p = 1 ∧ P.q = 1 ∧ HigherOrderDerivativeFamily f 1 (fun _ => 1) ∧
      (∀ x, -(1 / 20000 : ℝ) ≤ f x) ∧
      trial.step = 1 / 200 ∧
      model f 1 0 2 trial.step < model f 1 0 2 0 ∧
      (f 0 - f trial.step) / taylorDecrement f 1 0 trial.step = 3 / 4 ∧
      Nonempty (FailedTest P f trial.step trial.radii) ∧
      SatisfiesCriteria P f trial.step trial.radii ∧
      OuterTransition P f ⟨0, 2, fun _ => 1, 0, true⟩
        (.next ⟨trial.step, 2, trial.radii, 0, true⟩) 1 1 ∧
      (∃ c, OuterTransition P f ⟨trial.step, 2, trial.radii, 0, true⟩ (.next c) 1 1) ∧
      (∃ next : ModelStep P f trial.step 2 trial.radii,
        model f 1 trial.step 2 next.step < model f 1 trial.step 2 0) ∧
      max (2 : ℝ) (P.gamma3 * (1 / (1 - P.eta2))) = 6 ∧
      (1 - P.theta) * P.epsilon 1 > (1 + 6) * ‖trial.step‖ ∧
      ‖trial.step‖ < (1 - P.theta) / (2 * (1 + 6)) * P.epsilon 1 ∧
      taylorDecrement f 1 0 trial.step <
        P.sigmaMin / 2 * ((1 - P.theta) / (2 * (1 + 6))) ^ 2 * P.epsilon 1 ^ 2 := by
  refine ⟨counterParameters, counterObjective, counterStep 0, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨by fun_prop [counterObjective], ?_, ?_⟩
    · intro j _ _; norm_num
    · intro j hj hj1 x y d
      have hjj : j = 1 := by omega
      subst j
      simp only [sub_apply, iteratedFDeriv_one_apply, fderiv_eq_deriv_mul, counter_deriv,
        Real.norm_eq_abs, pow_one, one_mul]
      rw [show (x - 1 / 100) * d - (y - 1 / 100) * d = (x - y) * d by ring, abs_mul]
  · intro x
    dsimp [counterObjective]
    nlinarith [sq_nonneg (x - 1 / 100)]
  · refine ⟨by norm_num [counterStep], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num [counterStep, counter_model, counterObjective]
    · rw [taylorDecrement_one, fderiv_eq_deriv_mul, counter_deriv]
      norm_num [counterStep, counterObjective]
    · constructor
      convert counterFailed using 1 <;> norm_num [counterStep]
    · intro j hj hj1
      have hjj : j = 1 := by change j ≤ 1 at hj1; omega
      subst j
      change gapOn (taylorDecrement counterObjective 1 ((counterStep 0).step))
        (Metric.closedBall 0 1) ≤ _
      rw [gap_one, counter_deriv]
      norm_num [counterParameters, counterStep]
    · convert counter_transition 0 ⟨counterFailedInitial⟩
        (by norm_num [counterStep, counter_model, counterObjective])
        (by rw [taylorDecrement_one, fderiv_eq_deriv_mul, counter_deriv]
            norm_num [counterStep, counterObjective]) using 1
      norm_num [counterStep]
    · refine ⟨⟨3 / 400, 2, fun _ => 1, 0, true⟩, ?_⟩
      convert counter_transition (1 / 200) ⟨counterFailed⟩
        (by norm_num [counterStep, counter_model, counterObjective])
        (by rw [taylorDecrement_one, fderiv_eq_deriv_mul, counter_deriv]
            norm_num [counterStep, counterObjective]) using 1 <;> norm_num [counterStep]
    · refine ⟨counterStep (counterStep 0).step, ?_⟩
      norm_num [counterStep, counter_model, counterObjective]
    · norm_num [counterParameters]
    · norm_num [counterParameters, counterStep]
    · norm_num [counterParameters, counterStep]
    · rw [taylorDecrement_one, fderiv_eq_deriv_mul, counter_deriv]
      norm_num [counterParameters, counterStep]

section CorrectedBounds
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {P : Parameters} {f : E → ℝ} {x : E}
  {σ S L κ : ℝ} {δ : ℕ → ℝ}

/-- Corrected Lemma 12.2.11: actual next-point true gap failure, rather than the
conservative computed outer test, supplies (12.2.52). -/
theorem lemma_12_2_11_of_true_gap_failure
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (trial : ModelStep P f x σ δ) (hne : trial.step ≠ 0) (hσ : 0 ≤ σ) (hS : σ ≤ S)
    (hfail : ¬SatisfiesCriteria P f (x + trial.step) trial.radii) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧ (1 - P.theta) * P.epsilon j * trial.radii j ^ j / (j ! : ℝ) ≤
      (L + S) * ∑ ℓ ∈ Finset.Icc 1 j,
        trial.radii j ^ ℓ * ‖trial.step‖ ^ (P.p - ℓ + 1) / (ℓ ! : ℝ) :=
  transfer_of_true_gap_failure hf hL trial hne hσ hS hfail

/-- Corrected Lemma 12.2.12: both source tolerance exponents hold with the safe
minimum of the two radius-branch coefficients. -/
theorem lemma_12_2_12_of_true_gap_failure
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (trial : ModelStep P f x σ δ) (hne : trial.step ≠ 0) (hσ : 0 ≤ σ) (hS : σ ≤ S)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hunit : ∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 → trial.radii j = 1)
    (hlower : ∀ j, 3 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ trial.radii j)
    (hfail : ¬SatisfiesCriteria P f (x + trial.step) trial.radii) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      stepBoundConstant P.p P.q j P.theta (L + S) κ *
        P.epsilon j ^ stepBoundExponent P.p P.q j ≤ ‖trial.step‖ :=
  step_lower_bound_of_true_gap_failure hf hL trial hne hσ hS hκ
    (regime_radii_of_unit_low_and_lower_high P hκ1 hunit hlower).1
    (regime_radii_of_unit_low_and_lower_high P hκ1 hunit hlower).2 hfail

/-- Corrected Lemma 12.2.13: the actual Taylor prediction pays a positive structural
constant times the minimum of all source tolerance powers. -/
theorem lemma_12_2_13_of_true_gap_failure
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (trial : ModelStep P f x σ δ) (hne : trial.step ≠ 0)
    (hfloor : P.sigmaMin ≤ σ) (hS : σ ≤ S) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hunit : ∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 → trial.radii j = 1)
    (hlower : ∀ j, 3 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ trial.radii j)
    (hfail : ¬SatisfiesCriteria P f (x + trial.step) trial.radii) :
    modelDecreaseConstant P.p P.q P.order_pos P.theta (L + S) κ P.sigmaMin *
      toleranceMeasure P.p P.q P.order_pos P.epsilon ≤ taylorDecrement f P.p x trial.step ∧
    (P.eta1 ≤ (f x - f (x + trial.step)) / taylorDecrement f P.p x trial.step →
      P.eta1 * (modelDecreaseConstant P.p P.q P.order_pos P.theta (L + S) κ P.sigmaMin *
        toleranceMeasure P.p P.q P.order_pos P.epsilon) ≤ f x - f (x + trial.step)) :=
  ⟨predicted_decrease_of_true_gap_failure hf hL trial hne hfloor hS hκ
      (regime_radii_of_unit_low_and_lower_high P hκ1 hunit hlower).1
      (regime_radii_of_unit_low_and_lower_high P hκ1 hunit hlower).2 hfail,
    accepted_decrease_of_true_gap_failure hf hL trial hne hfloor hS hκ
      (regime_radii_of_unit_low_and_lower_high P hκ1 hunit hlower).1
      (regime_radii_of_unit_low_and_lower_high P hκ1 hunit hlower).2 hfail⟩

end CorrectedBounds
end CartisGouldToint.Chapter12.Section02
