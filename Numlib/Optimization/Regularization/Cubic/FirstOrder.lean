import Numlib.Optimization.Regularization.Cubic.Gradient
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# First-order evaluation budgets for cubic regularization

The second-order stopping test is explicitly disabled. Valid finite prefixes
contain the actual cubic-model stationarity test, objective ratio, acceptance
rule and parameter updates. A possible final successful trial is counted
separately because its endpoint may already meet the stopping tolerance.
-/

namespace CubicRegularization

open TaylorModel EvaluationComplexity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first-order-only operational branch of AR2, with disabled second test. -/
structure FirstOrderRun (f : E → ℝ) (x s : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε : ℝ) (ε₂ : WithTop ℝ) (N : ℕ) : Prop where
  second_disabled : ε₂ = ⊤
  trace : ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  theta_pos : 0 < θ
  accuracy_pos : 0 < ε
  accuracy_le_one : ε ≤ 1
  not_terminated : ∀ i < N, ε < ‖fderiv ℝ f (x i)‖
  stationary : ∀ i < N,
    ‖fderiv ℝ (model f (x i) (σ i)) (s i)‖ ≤ θ / 2 * ‖s i‖ ^ 2
  step : ∀ i < N, x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i

/-- Fixed coefficient of the `ε^(3/2)` decrease at each successful,
nonterminal cubic-regularization trial. -/
noncomputable def decreaseCoefficient (σ₀ σmin η₁ η₂ γ₃ L θ : ℝ) : ℝ :=
  η₁ * σmin / 6 * (2 / (L + θ + max σ₀ (γ₃ * L / (1 - η₂)))) ^ (3 / 2 : ℝ)

/-- The reciprocal decrease coefficient is exactly the printed AR2 successful
iteration constant, with the `3/2` powers and all factors preserved. -/
theorem inv_decreaseCoefficient_eq {σ₀ σmin η₁ η₂ γ₃ L θ : ℝ}
    (hσ : 0 < σ₀) (hmin : 0 < σmin) (hη : 0 < η₁) (hL : 0 ≤ L) (hθ : 0 < θ) :
    1 / decreaseCoefficient σ₀ σmin η₁ η₂ γ₃ L θ =
      6 * (L + θ + max σ₀ (γ₃ * L / (1 - η₂))) ^ (3 / 2 : ℝ) /
        ((2 : ℝ) ^ (3 / 2 : ℝ) * η₁ * σmin) := by
  have hG : 0 < L + θ + max σ₀ (γ₃ * L / (1 - η₂)) := by
    have hm : 0 < max σ₀ (γ₃ * L / (1 - η₂)) := hσ.trans_le (le_max_left _ _)
    positivity
  have hp2 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (3 / 2)).ne'
  have hpG := (Real.rpow_pos_of_pos hG (3 / 2)).ne'
  unfold decreaseCoefficient
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hG.le]
  field_simp

namespace FirstOrderRun

variable {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε L : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}

/-- Each shorter prefix obeys the same algorithm. -/
theorem restrict (h : FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ε₂ N)
    {M : ℕ} (hM : M ≤ N) : FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ε₂ M where
  second_disabled := h.second_disabled
  trace := {
    updates := { h.trace.updates with
      update := fun i hi => h.trace.updates.update i (lt_of_lt_of_le hi hM) }
    improvement := fun i hi => h.trace.improvement i (lt_of_lt_of_le hi hM)
    ratio := fun i hi => h.trace.ratio i (lt_of_lt_of_le hi hM) }
  theta_pos := h.theta_pos
  accuracy_pos := h.accuracy_pos
  accuracy_le_one := h.accuracy_le_one
  not_terminated := fun i hi => h.not_terminated i (lt_of_lt_of_le hi hM)
  stationary := fun i hi => h.stationary i (lt_of_lt_of_le hi hM)
  step := fun i hi => h.step i (lt_of_lt_of_le hi hM)

/-- The coefficient in the nonterminal successful decrease is positive. -/
theorem decreaseCoefficient_pos
    (h : FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ε₂ N) (hL : 0 ≤ L) :
    0 < decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ := by
  have hη := h.trace.updates.eta1_pos
  have hσmin := h.trace.updates.min_pos
  have hσ₀ := h.trace.updates.pos (Nat.zero_le N)
  have hθ := h.theta_pos
  unfold decreaseCoefficient
  positivity

/-- An accepted trial yields the objective decrease dictated by the actual
model reduction and the parameter floor. -/
theorem successful_decrease
    (h : FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ε₂ N)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i) :
    η₁ * σmin / 6 * ‖s i‖ ^ 3 ≤ f (x i) - f (x (i + 1)) := by
  have hr := (le_div_iff₀ (h.trace.denominator_pos hi)).mp
    ((h.trace.ratio i hi) ▸ hs)
  have hd := mul_le_mul_of_nonneg_left (h.trace.model_decrease hi).le
    h.trace.updates.eta1_pos.le
  have hmin := mul_le_mul_of_nonneg_right (h.trace.updates.min_le (show i ≤ N by omega))
    (pow_nonneg (norm_nonneg (s i)) 3)
  rw [h.step i hi, ite_eq_left hs]
  nlinarith [mul_le_mul_of_nonneg_left hmin h.trace.updates.eta1_pos.le]

/-- A successful trial whose endpoint still fails the stopping test obtains
an explicit `ε^(3/2)` objective decrease. -/
theorem nonterminal_successful_decrease
    (h : FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i + 1 < N) (hs : η₁ ≤ ρ i) :
    decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ε ^ (3 / 2 : ℝ) ≤
      f (x i) - f (x (i + 1)) := by
  let c := 2 / (L + θ + max (σ 0) (γ₃ * L / (1 - η₂)))
  have hσ₀ := h.trace.updates.pos (Nat.zero_le N)
  have hθ := h.theta_pos
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hstep := h.trace.step_length_lower hf hL hθ.le hlip (by omega) (h.stationary i (by omega))
  have hn := h.not_terminated (i + 1) hi
  rw [h.step i (by omega), ite_eq_left hs] at hn
  have hbase : c * ε ≤ ‖s i‖ ^ 2 :=
    (mul_le_mul_of_nonneg_left hn.le hc).trans hstep
  have hp := Real.rpow_le_rpow (mul_nonneg hc h.accuracy_pos.le) hbase
    (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hs3 : (‖s i‖ ^ 2) ^ (3 / 2 : ℝ) = ‖s i‖ ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg (s i))]
    norm_num
  rw [hs3, Real.mul_rpow hc h.accuracy_pos.le] at hp
  have hcoeff : 0 ≤ η₁ * σmin / 6 := by
    have hη := h.trace.updates.eta1_pos
    have hmin := h.trace.updates.min_pos
    positivity
  have hb := mul_le_mul_of_nonneg_left hp hcoeff
  have hb' : decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ε ^ (3 / 2 : ℝ) ≤
      η₁ * σmin / 6 * ‖s i‖ ^ 3 := by
    simpa only [decreaseCoefficient, c, mul_assoc] using hb
  exact hb'.trans (h.successful_decrease (by omega) hs)

/-- Every unsuccessful trial preserves the current objective. -/
theorem objective_eq_of_unsuccessful
    (h : FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ε₂ N)
    {i : ℕ} (hi : i < N) (hu : ¬η₁ ≤ ρ i) : f (x (i + 1)) = f (x i) := by
  rw [h.step i hi, ite_eq_right hu]

/-- At most one successful trial can have an endpoint that already meets the
stopping test. All earlier successful trials consume the uniform objective budget. -/
theorem successful_card_le
    (h : FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤
      (f (x 0) - flow) /
        (decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ε ^ (3 / 2 : ℝ)) + 1 := by
  have hgap : 0 ≤ f (x 0) - flow := sub_nonneg.mpr (hlow _)
  have hdpos := mul_pos (h.decreaseCoefficient_pos hL)
    (Real.rpow_pos_of_pos h.accuracy_pos (3 / 2))
  cases N with
  | zero => simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]; positivity
  | succ k =>
    have hc := EvaluationComplexity.card_successful_le_gap_div
      (S := {i | η₁ ≤ ρ i}) (f := fun i => f (x i)) hdpos (hlow (x k))
      (fun i hi hs => h.nonterminal_successful_decrease hf hL hlip (by omega) hs)
      (fun i hi hu => (h.objective_eq_of_unsuccessful (by omega) hu).le)
    have hsucc : ((successfulIterations {i | η₁ ≤ ρ i} (k + 1)).card : ℝ) ≤
        (successfulIterations {i | η₁ ≤ ρ i} k).card + 1 := by
      exact_mod_cast card_successful_succ_le {i | η₁ ≤ ρ i} k
    exact hsucc.trans (add_le_add hc le_rfl)

/-- The full iteration budget combines the objective budget with the actual
regularization-parameter update mechanism. -/
theorem iterations_le
    (h : FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    (N : ℝ) ≤ ((f (x 0) - flow) /
        (decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ε ^ (3 / 2 : ℝ)) + 1) *
        (1 + |Real.log γ₁| / Real.log γ₂) +
      Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂ := by
  have ht := EvaluationComplexity.iteration_bound_of_parameter_upper
    (S := {i | η₁ ≤ ρ i}) (fun _ hi => h.trace.updates.pos hi)
    h.trace.updates.gamma1_pos h.trace.updates.gamma1_lt_one
    h.trace.updates.one_lt_gamma2 (h.trace.parameter_le hf hL hlip le_rfl)
    (fun _ hi hs => h.trace.updates.successful_ge hi hs)
    (fun _ hi hu => h.trace.updates.unsuccessful_ge hi hu)
  have hlog := Real.log_pos h.trace.updates.one_lt_gamma2
  have hA : 0 ≤ 1 + |Real.log γ₁| / Real.log γ₂ := by positivity
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right (h.successful_card_le hf hL hlip hlow) hA) le_rfl)

end FirstOrderRun
/-- A consistent first-order-only AR2 execution reaches the requested tolerance.
No termination or iteration bound is included in the trace specification. -/
theorem exists_firstOrder_termination {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε L flow : ℝ} {ε₂ : WithTop ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖fderiv ℝ f (x i)‖) →
      FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ K, ‖fderiv ℝ f (x K)‖ ≤ ε ∧
      FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ε₂ K := by
  have hex : ∃ K, ‖fderiv ℝ f (x K)‖ ≤ ε := by
    by_contra hnone
    push Not at hnone
    let bound := ((f (x 0) - flow) /
        (decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ε ^ (3 / 2 : ℝ)) + 1) *
        (1 + |Real.log γ₁| / Real.log γ₂) +
      Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have hb := (hprefix N (fun i _ => hnone i)).iterations_le hf hL hlip hlow
    exact (not_le_of_gt hN) hb
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_⟩
  intro i hi
  exact lt_of_not_ge (Nat.find_min hex hi)

end CubicRegularization
