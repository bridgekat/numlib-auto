import Numlib.Analysis.SpecialFunctions.Log.GeometricBudget

/-!
# Chebyshev contraction factors and their logarithmic budgets

The actual square-root factor is monotone in the condition ratio. Uniform
condition bounds therefore give a genuine common geometric envelope.
-/

namespace Krylov
/-- The Chebyshev contraction factor for a spectral condition ratio. -/
noncomputable def chebyshevFactor (κ : ℝ) : ℝ :=
  (Real.sqrt κ - 1) / (Real.sqrt κ + 1)

/-- The Chebyshev factor is nonnegative at condition numbers at least one. -/
theorem chebyshevFactor_nonneg {κ : ℝ} (hκ : 1 ≤ κ) : 0 ≤ chebyshevFactor κ := by
  have hs : 1 ≤ Real.sqrt κ := by
    rw [Real.le_sqrt (by norm_num) (zero_le_one.trans hκ)]
    simpa using hκ
  unfold chebyshevFactor
  positivity

/-- The Chebyshev factor is positive for condition numbers greater than one. -/
theorem chebyshevFactor_pos {κ : ℝ} (hκ : 1 < κ) : 0 < chebyshevFactor κ := by
  have hs : 1 < Real.sqrt κ := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using hκ
  unfold chebyshevFactor
  positivity

/-- The Chebyshev factor is strictly less than one. -/
theorem chebyshevFactor_lt_one (κ : ℝ) : chebyshevFactor κ < 1 := by
  unfold chebyshevFactor
  rw [div_lt_one (by positivity)]
  linarith

/-- Increasing the condition ratio increases the Chebyshev factor. -/
theorem chebyshevFactor_monotone : Monotone chebyshevFactor := by
  intro a b hab
  unfold chebyshevFactor
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.sqrt_le_sqrt hab]

/-- A residual bound with a smaller condition ratio is bounded by the common-condition
geometric envelope. -/
theorem mul_chebyshevFactor_pow_le {C κ K : ℝ} (hC : 0 ≤ C) (hκ : 1 ≤ κ)
    (hK : κ ≤ K) (m : ℕ) :
    C * κ * chebyshevFactor κ ^ m ≤ C * K * chebyshevFactor K ^ m := by
  have hq := chebyshevFactor_nonneg hκ
  have hqK := chebyshevFactor_nonneg (hκ.trans hK)
  have hKn : 0 ≤ K := zero_le_one.trans (hκ.trans hK)
  gcongr
  exact chebyshevFactor_monotone hK

/-- The condition-one factor vanishes exactly. -/
@[simp]
theorem chebyshevFactor_one : chebyshevFactor 1 = 0 := by
  norm_num [chebyshevFactor]

/-- The generic natural logarithmic budget has the source Chebyshev log-ratio formula. -/
theorem budget_chebyshevFactor (C ε κ : ℝ) :
    GeometricDecay.budget C ε (chebyshevFactor κ) =
      ⌈Real.log (C / ε) /
        Real.log ((Real.sqrt κ + 1) / (Real.sqrt κ - 1))⌉₊ := by
  simp only [GeometricDecay.budget, chebyshevFactor, inv_div]
end Krylov
