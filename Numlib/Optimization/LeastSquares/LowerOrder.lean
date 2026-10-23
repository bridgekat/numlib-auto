import Numlib.Optimization.LeastSquares.Complexity

/-!
# ARpLE with disabled higher-order tests

The exact stopping alternatives, accuracy powers and coefficients retain only
the enabled first- and second-order tests.
-/

namespace LeastSquares
open HighOrderRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F]

/-- Actual first/second-order stopping with the third test disabled. -/
def lowerStop (second : Bool) (r : E → F) (ℓ : ℝ) (x : E) (μ ε₀ ε₁ ε₂ : ℝ)
  : Prop :=
  ‖r x‖ ≤ ε₀ ∨ firstMeasure r ℓ x ≤ ε₁ ∧ (second = true → -ε₂ ≤
    secondMeasure r ℓ x μ)

/-- The complete actual program specializes to the corresponding disabled-third stopping rule. -/
theorem stop_lower_iff (literal second : Bool) (r : E → F) (ℓ : ℝ) (x : E)
    (μ ε₀ ε₁ ε₂ : ℝ) (M : Set E) (hε₂ : 0 ≤ ε₂) :
    stop literal r ℓ x μ M ε₀ ε₁ (if second then (ε₂ : WithTop ℝ) else ⊤) ⊤ ↔
      lowerStop second r ℓ x μ ε₀ ε₁ ε₂ := by
  cases second with
  | false => simp [stop, lowerStop]
  | true =>
    have hh : (ε₂ < secondMeasure r ℓ x μ ∨ -ε₂ ≤ secondMeasure r ℓ x μ) ↔
        -ε₂ ≤ secondMeasure r ℓ x μ := by
      constructor
      · intro h; rcases h with h | h
        · linarith
        · exact h
      · exact Or.inr
    simp [stop, lowerStop, hh]


variable [CompleteSpace E]

/-- Either lower-order mode is a genuine source ARpLE execution with its third test disabled. -/
abbrev LowerRun (literal second : Bool) (r : E → F) (ℓ : ℝ) (p : ℕ)
    (x s u : ℕ → E) (μ σ ρ : ℕ → ℝ) (M : ℕ → Set E)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ : ℝ) (N :
      ℕ) : Prop :=
  Run literal r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃
    ε₀ ε₁
    (if second then (ε₂ : WithTop ℝ) else ⊤) ⊤ N
end LeastSquares

namespace LeastSquares
open HighOrderRegularization
/-- The exact accuracy factor includes only the enabled lower-order tests. -/
noncomputable def lowerAccuracyFactor (second : Bool) (p a : ℕ) (ε₀ ε₁ ε₂ : ℝ) : ℝ :=
  if second then min (ε₀ ^ (1 / (2 : ℝ) ^ a))
    (min (ε₁ ^ (((p + 1 : ℕ) : ℝ) / p)) (ε₂ ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))))
  else min (ε₀ ^ (1 / (2 : ℝ) ^ a)) (ε₁ ^ (((p + 1 : ℕ) : ℝ) / p))

/-- The exact coefficient minimum includes only the enabled lower-order decreases. -/
noncomputable def lowerDecreaseCoefficient (second : Bool) (p : ℕ) (ℓ : ℝ) (a : ℕ)
    (σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ β : ℝ) : ℝ :=
  let σmax := max σ₀ (γ₃ * L / (1 - η₂))
  let κ₀ := 1 - β ^ (1 / (2 : ℝ) ^ a)
  let κ₁ := cascadingConstant (decreaseConstant p p η₁ σmin L σmax θ₁) β ℓ p a 1
  let κ₂ := cascadingConstant (decreaseConstant p (p - 1) η₁ σmin L σmax θ₂) β ℓ p a 2
  if second then min κ₀ (min κ₁ κ₂) else min κ₀ κ₁

/-- The lower-order denominator uses only enabled residual exponents. -/
noncomputable def lowerDenominator (second : Bool) (p : ℕ) (ℓ : ℝ) (a : ℕ) (R : ℝ)
  : ℝ :=
  if second then max 1 (max (R ^ cascadingExponent p ℓ a 1) (R ^ cascadingExponent p ℓ a 2))
  else max 1 (R ^ cascadingExponent p ℓ a 1)

/-- The lower-order numerator retains the exact enabled source powers of the initial residual. -/
noncomputable def lowerBudget (second : Bool) (p : ℕ) (ℓ : ℝ) (a : ℕ) (R : ℝ) : ℝ :=
  if second then max (R ^ (1 / (2 : ℝ) ^ a))
    (max (R ^ (1 - (ℓ - 1) / p)) (R ^ (1 - 2 * (ℓ - 1) / (p - 1 : ℕ))))
  else max (R ^ (1 / (2 : ℝ) ^ a)) (R ^ (1 - (ℓ - 1) / p))

/-- Each lower-order count constant is the exact maximum of the enabled reciprocal coefficients. -/
noncomputable def lowerSuccessfulIterationConstant (second : Bool) (p : ℕ) (ℓ : ℝ) (a : ℕ)
    (σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ β : ℝ) : ℝ :=
  let σmax := max σ₀ (γ₃ * L / (1 - η₂))
  let κ₀ := 1 - β ^ (1 / (2 : ℝ) ^ a)
  let κ₁ := cascadingConstant (decreaseConstant p p η₁ σmin L σmax θ₁) β ℓ p a 1
  let κ₂ := cascadingConstant (decreaseConstant p (p - 1) η₁ σmin L σmax θ₂) β ℓ p a 2
  if second then max (1 / κ₀) (max (1 / κ₁) (1 / κ₂)) else max (1 / κ₀) (1 / κ₁)
end LeastSquares

namespace LeastSquares
open HighOrderRegularization
/-- Every enabled lower-order accuracy factor is strictly positive. -/
theorem lowerAccuracyFactor_pos (second : Bool) (p a : ℕ) {ε₀ ε₁ ε₂ : ℝ}
    (h₀ : 0 < ε₀) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) :
    0 < lowerAccuracyFactor second p a ε₀ ε₁ ε₂ := by
  cases second <;> dsimp [lowerAccuracyFactor] <;> positivity

/-- The exact inverse accuracy factor is the maximum of just the enabled inverse powers. -/
theorem inv_lowerAccuracyFactor_eq (second : Bool) (p a : ℕ) {ε₀ ε₁ ε₂ : ℝ}
    (h₀ : 0 < ε₀) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) :
    1 / lowerAccuracyFactor second p a ε₀ ε₁ ε₂ =
      if second then max (ε₀ ^ (-(1 / (2 : ℝ) ^ a)))
        (max (ε₁ ^ (-((p + 1 : ℕ) : ℝ) / p))
          (ε₂ ^ (-((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))))
      else max (ε₀ ^ (-(1 / (2 : ℝ) ^ a)))
        (ε₁ ^ (-((p + 1 : ℕ) : ℝ) / p)) := by
  have hpow₀ := Real.rpow_pos_of_pos h₀ (1 / (2 : ℝ) ^ a)
  have hpow₁ := Real.rpow_pos_of_pos h₁ (((p + 1 : ℕ) : ℝ) / p)
  have hpow₂ := Real.rpow_pos_of_pos h₂ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))
  cases second <;> dsimp [lowerAccuracyFactor]
  · rw [one_div_min_eq_max hpow₀ hpow₁]
    simp_rw [one_div, ← Real.rpow_neg h₀.le, ← Real.rpow_neg h₁.le, neg_div]
  · rw [one_div_min_eq_max hpow₀ (lt_min hpow₁ hpow₂), one_div_min_eq_max hpow₁ hpow₂]
    simp_rw [one_div, ← Real.rpow_neg h₀.le, ← Real.rpow_neg h₁.le,
      ← Real.rpow_neg h₂.le, neg_div]

/-- The lower-order common denominator is positive for every residual. -/
theorem lowerDenominator_pos (second : Bool) (p : ℕ) (ℓ : ℝ) (a : ℕ) (R : ℝ) :
    0 < lowerDenominator second p ℓ a R := by
  cases second <;> exact zero_lt_one.trans_le (le_max_left _ _)

/-- All enabled lower-order decrease coefficients are positive before accuracy requests. -/
theorem lowerDecreaseCoefficient_pos (second : Bool) (p : ℕ) (ℓ : ℝ) (a : ℕ)
    {σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ β : ℝ}
    (hσ : 0 < σ₀) (hmin : 0 < σmin) (hη : 0 < η₁) (hL : 0 < L)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hβ : 0 < β) (hβ1 : β < 1) :
    0 < lowerDecreaseCoefficient second p ℓ a σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ β := by
  have hm : 0 ≤ max σ₀ (γ₃ * L / (1 - η₂)) := hσ.le.trans (le_max_left _ _)
  have h₀ : 0 < 1 - β ^ (1 / (2 : ℝ) ^ a) :=
    sub_pos.mpr (Real.rpow_lt_one hβ.le hβ1 (by positivity))
  have h₁ := cascadingConstant_pos (ℓ := ℓ)
    (decreaseConstant_pos p p hη hmin hL hm hθ₁.le) hβ p a 1
  have h₂ := cascadingConstant_pos (ℓ := ℓ)
    (decreaseConstant_pos p (p - 1) hη hmin hL hm hθ₂.le) hβ p a 2
  cases second with
  | false => exact lt_min h₀ h₁
  | true => exact lt_min h₀ (lt_min h₁ h₂)

/-- The reciprocal minimum is the exact maximum of enabled reciprocal coefficients. -/
theorem inverse_lowerDecreaseCoefficient (second : Bool) (p : ℕ) (ℓ : ℝ) (a : ℕ)
    {σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ β : ℝ}
    (hσ : 0 < σ₀) (hmin : 0 < σmin) (hη : 0 < η₁) (hL : 0 < L)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hβ : 0 < β) (hβ1 : β < 1) :
    1 / lowerDecreaseCoefficient second p ℓ a σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ β =
      lowerSuccessfulIterationConstant second p ℓ a σ₀ σmin η₁ η₂ γ₃ L θ₁
        θ₂ β := by
  have hm : 0 ≤ max σ₀ (γ₃ * L / (1 - η₂)) := hσ.le.trans (le_max_left _ _)
  have h₀ : 0 < 1 - β ^ (1 / (2 : ℝ) ^ a) :=
    sub_pos.mpr (Real.rpow_lt_one hβ.le hβ1 (by positivity))
  have h₁ := cascadingConstant_pos (ℓ := ℓ)
    (decreaseConstant_pos p p hη hmin hL hm hθ₁.le) hβ p a 1
  have h₂ := cascadingConstant_pos (ℓ := ℓ)
    (decreaseConstant_pos p (p - 1) hη hmin hL hm hθ₂.le) hβ p a 2
  cases second with
  | false => exact one_div_min_eq_max h₀ h₁
  | true =>
    dsimp [lowerDecreaseCoefficient, lowerSuccessfulIterationConstant]
    rw [one_div_min_eq_max h₀ (lt_min h₁ h₂), one_div_min_eq_max h₁ h₂]

/-- The lower-order common numerator is the potential times its denominator, with exact
  source powers. -/
theorem lowerBudget_eq {R : ℝ} (hR : 0 < R) (second : Bool) (p : ℕ) (ℓ : ℝ) (a : ℕ) :
    R ^ (1 / (2 : ℝ) ^ a) * lowerDenominator second p ℓ a R =
      lowerBudget second p ℓ a R := by
  cases second <;> dsimp [lowerDenominator, lowerBudget]
  · rw [mul_max_of_nonneg _ _ (Real.rpow_nonneg hR.le _)]
    simp only [mul_one, ← Real.rpow_add hR, dyadic_add_cascadingExponent,
      Nat.cast_one, one_mul, Nat.add_sub_cancel]
  · rw [mul_max_of_nonneg _ _ (Real.rpow_nonneg hR.le _),
      mul_max_of_nonneg _ _ (Real.rpow_nonneg hR.le _)]
    simp only [mul_one, ← Real.rpow_add hR, dyadic_add_cascadingExponent,
      Nat.cast_one, one_mul, Nat.add_sub_cancel,
      show p + 1 - 2 = p - 1 by omega, Nat.cast_ofNat]

/-- Lower-order numerators are nonnegative for every nonnegative initial residual. -/
theorem lowerBudget_nonneg {R : ℝ} (hR : 0 ≤ R) (second : Bool) (p : ℕ) (ℓ : ℝ) (a
  : ℕ) :
    0 ≤ lowerBudget second p ℓ a R := by
  cases second <;> exact (Real.rpow_nonneg hR _).trans (le_max_left _ _)

end LeastSquares
