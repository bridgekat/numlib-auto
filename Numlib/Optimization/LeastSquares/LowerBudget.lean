import Numlib.Optimization.LeastSquares.LowerOrder

/-!
# Actual lower-order dyadic residual decreases

Disabled derivative tests contribute no decrease or accuracy branch.
-/

namespace LeastSquares
open HighOrderRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]
namespace LowerRun
variable {literal second : Bool} {r : E → F} {ℓ : ℝ} {p : ℕ}
  {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ} {M : ℕ → Set E}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ : ℝ} {N : ℕ}

/-- Nonterminal disabled-third iterates fail either the first test or an enabled second test. -/
theorem endpoint_obstruction
    (h : LowerRun literal second r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ N) (hε₂ : 0 < ε₂) {i : ℕ} (hi : i < N) :
    ε₁ < firstMeasure r ℓ (x i) ∨
      second = true ∧ secondMeasure r ℓ (x i) (μ i) < -ε₂ := by
  have hn : ¬lowerStop second r ℓ (x i) (μ i) ε₀ ε₁ ε₂ :=
    (stop_lower_iff literal second r ℓ (x i) (μ i) ε₀ ε₁ ε₂ (M i) hε₂.le).not.mp
      (h.not_terminated i hi)
  by_cases hg : firstMeasure r ℓ (x i) ≤ ε₁
  · right
    have hh : ¬(second = true → -ε₂ ≤ secondMeasure r ℓ (x i) (μ i)) := by
      intro hh
      exact hn (Or.inr ⟨hg, hh⟩)
    push Not at hh
    exact hh
  · exact Or.inl (lt_of_not_ge hg)
end LowerRun
end LeastSquares

namespace LeastSquares
open HighOrderRegularization
/-- The minimum lower-order coefficient is bounded by every enabled branch coefficient. -/
theorem lowerDecreaseCoefficient_bounds (second : Bool) (p : ℕ) (ℓ : ℝ) (a : ℕ)
    (σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ β : ℝ) :
    let c := lowerDecreaseCoefficient second p ℓ a σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ β
    let σmax := max σ₀ (γ₃ * L / (1 - η₂))
    c ≤ 1 - β ^ (1 / (2 : ℝ) ^ a) ∧
    c ≤ cascadingConstant (decreaseConstant p p η₁ σmin L σmax θ₁) β ℓ p a 1 ∧
    (second = true → c ≤
      cascadingConstant (decreaseConstant p (p - 1) η₁ σmin L σmax θ₂) β ℓ p a 2) := by
  cases second with
  | false => exact ⟨min_le_left _ _, min_le_right _ _, by simp⟩
  | true => exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      fun _ => (min_le_right _ _).trans (min_le_right _ _)⟩

/-- The common lower-order accuracy factor is bounded by each enabled accuracy power. -/
theorem lowerAccuracyFactor_bounds (second : Bool) (p a : ℕ) (ε₀ ε₁ ε₂ : ℝ) :
    let A := lowerAccuracyFactor second p a ε₀ ε₁ ε₂
    A ≤ ε₀ ^ (1 / (2 : ℝ) ^ a) ∧ A ≤ ε₁ ^ (((p + 1 : ℕ) : ℝ) / p) ∧
    (second = true → A ≤ ε₂ ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))) := by
  cases second with
  | false => exact ⟨min_le_left _ _, min_le_right _ _, by simp⟩
  | true => exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      fun _ => (min_le_right _ _).trans (min_le_right _ _)⟩

/-- The common lower-order denominator dominates one and all enabled initial-residual factors. -/
theorem lowerDenominator_bounds (second : Bool) (p : ℕ) (ℓ : ℝ) (a : ℕ) (R : ℝ) :
    let D := lowerDenominator second p ℓ a R
    1 ≤ D ∧ R ^ cascadingExponent p ℓ a 1 ≤ D ∧
    (second = true → R ^ cascadingExponent p ℓ a 2 ≤ D) := by
  cases second with
  | false => exact ⟨le_max_left _ _, le_max_right _ _, by simp⟩
  | true => exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      fun _ => (le_max_right _ _).trans (le_max_right _ _)⟩
end LeastSquares


namespace LeastSquares.LowerRun
open HighOrderRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]
variable {literal second : Bool} {r : E → F} {ℓ L β : ℝ} {p : ℕ}
  {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ} {M : ℕ → Set E}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ : ℝ} {N : ℕ}

/-- Every successful nonterminal lower-order endpoint consumes its exact enabled dyadic budget. -/
theorem successful_root_decrease
    (h : LowerRun literal second r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ N) (hε₂ : 0 < ε₂)
    (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ)
    (hι₁ : 0 ≤ cascadingExponent p ℓ a 1)
    (hι₂ : second = true → 0 ≤ cascadingExponent p ℓ a 2)
    {i : ℕ} (hi : i + 1 < N) (hs : η₁ ≤ ρ i) :
    lowerDecreaseCoefficient second p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ β *
      lowerAccuracyFactor second p a ε₀ ε₁ ε₂ / lowerDenominator second p ℓ a
        ‖r (x 0)‖ ≤
      ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a) - ‖r (x (i + 1))‖ ^ (1 / (2 : ℝ) ^ a) := by
  let σmax := max (σ 0) (γ₃ * L / (1 - η₂))
  let K₁ := decreaseConstant p p η₁ σmin L σmax θ₁
  let K₂ := decreaseConstant p (p - 1) η₁ σmin L σmax θ₂
  let c := lowerDecreaseCoefficient second p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ β
  let A := lowerAccuracyFactor second p a ε₀ ε₁ ε₂
  let D := lowerDenominator second p ℓ a ‖r (x 0)‖
  have hℓ : 0 < ℓ := by linarith [h.residual_order]
  have hℓ1 : 1 ≤ ℓ := by linarith [h.residual_order]
  have hm : 0 ≤ σmax :=
    (h.trace.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hK₁ : 0 < K₁ := decreaseConstant_pos p p h.trace.updates.eta1_pos
    h.trace.updates.min_pos hL hm h.theta_first_pos.le
  have hK₂ : 0 < K₂ := decreaseConstant_pos p (p - 1) h.trace.updates.eta1_pos
    h.trace.updates.min_pos hL hm h.theta_second_pos.le
  have hA : 0 < A := lowerAccuracyFactor_pos second p a h.accuracy_global_pos
    h.accuracy_first_pos hε₂
  have hD : 0 < D := lowerDenominator_pos second p ℓ a ‖r (x 0)‖
  obtain ⟨hc₀, hc₁, hc₂⟩ := lowerDecreaseCoefficient_bounds second p ℓ a
    (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ β
  obtain ⟨hAcc₀, hAcc₁, hAcc₂⟩ := lowerAccuracyFactor_bounds second p a ε₀ ε₁ ε₂
  obtain ⟨hD₀, hD₁, hD₂⟩ := lowerDenominator_bounds second p ℓ a ‖r (x 0)‖
  have hiN : i < N := by omega
  have hx : 0 < ‖r (x i)‖ := h.accuracy_global_pos.trans (h.residual_gt_accuracy hiN)
  have hb := h.residual_step_le hiN
  have hq : 0 < (1 : ℝ) / 2 ^ a := by positivity
  by_cases hrel : β * ‖r (x i)‖ < ‖r (x (i + 1))‖
  · have branch (j : ℕ) (hjp : j ≤ p) (K eps v : ℝ)
        (hcK : c ≤ cascadingConstant K β ℓ p a j) (hK : 0 ≤ K) (hv : 0 ≤ v)
        (heps : 0 ≤ eps) (hepsv : eps ≤ v)
        (hAcc : A ≤ eps ^ (((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ)))
        (hι : 0 ≤ cascadingExponent p ℓ a j)
        (hDj : ‖r (x 0)‖ ^ cascadingExponent p ℓ a j ≤ D)
        (hd : K * ℓ * v ^ (((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ)) *
          ‖r (x (i + 1))‖ ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ)) ≤
            ‖r (x i)‖ ^ ℓ - ‖r (x (i + 1))‖ ^ ℓ) : c * A / D ≤
          ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a) - ‖r (x (i + 1))‖ ^ (1 / (2 : ℝ) ^ a) := by
      have ht := cascading_decrease_of_power (i := a) hx (norm_nonneg _) hb hβ hrel.le
        hℓ1 hK hv hjp hd
      apply budget_le_of_measure hA.le hD (show 0 ≤ cascadingConstant K β ℓ p a j by
        unfold cascadingConstant; positivity) hcK hAcc heps hepsv (by positivity)
        (Real.rpow_pos_of_pos hx _) _ ht
      exact (Real.rpow_le_rpow (norm_nonneg _) (h.residual_le_initial (by omega)) hι).trans hDj
    rcases h.endpoint_obstruction hε₂ hi with hg | ⟨hsecond, hμ⟩
    · apply branch 1 h.trace.order_pos K₁ ε₁ (firstMeasure r ℓ (x (i + 1)))
        hc₁ hK₁.le (div_nonneg (norm_nonneg _) (derivativeWeight_nonneg _ _ _))
        h.accuracy_first_pos.le hg.le (by simpa only [Nat.add_sub_cancel] using hAcc₁)
          hι₁ hD₁
      simpa only [Nat.add_sub_cancel] using h.trace.decrease_first hℓ hf hL
        h.theta_first_pos.le hlip hiN hs (h.stationary_first i hiN)
    · have hp2 : 2 ≤ p := h.second_order (by simp [hsecond])
      apply branch 2 hp2 K₂ ε₂ (max 0 (-secondMeasure r ℓ (x (i + 1)) (μ (i + 1))))
        (hc₂ hsecond) hK₂.le (le_max_left _ _) hε₂.le
        (le_trans (by linarith : ε₂ ≤ -secondMeasure r ℓ (x (i + 1)) (μ (i + 1)))
          (le_max_right _ _))
        (by simpa only [show p + 1 - 2 = p - 1 by omega] using hAcc₂ hsecond)
        (hι₂ hsecond) (hD₂ hsecond)
      simpa only [show p + 1 - 2 = p - 1 by omega] using h.trace.decrease_second hp2 hℓ hf hL
        h.theta_second_pos.le hlip hiN hs (h.stationary_second i hiN (by simp [hsecond]))
        (h.least_eigenpair (i + 1) (by omega) (by simp [hsecond]))
  · have hh := Real.relative_cascading_decrease (norm_nonneg _) hb hβ.le hβ1
      (not_lt.mp hrel) hq
    apply budget_le_of_measure hA.le hD hh.1.le hc₀ hAcc₀ h.accuracy_global_pos.le
      (h.residual_gt_accuracy hi).le hq.le zero_lt_one hD₀
    simpa only [div_one] using hh.2.2.trans hh.2.1
end LeastSquares.LowerRun
