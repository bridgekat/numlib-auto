import Numlib.Optimization.EvaluationComplexity.OracleSimulation.Counts
import Numlib.Optimization.Regularization.Inexact.Complexity

/-!
# Worst-component rates for regularization oracle simulation

The common exponent is the largest order exponent. The minimum requested
accuracy raised to this exponent bounds the actual finite minimum of powers.
This keeps the worst tolerance, repairing the displayed best-component rate.
-/

namespace InexactRegularization
open InexactTrustRegion

/-- The common worst-order exponent in the low-order-oracle complexity bound. -/
noncomputable def oracleRateExponent (p q : ℕ) : ℝ :=
  if q ≤ 2 then ((p + 1 : ℕ) : ℝ) / (p - q + 1 : ℕ)
  else (q : ℝ) * (p + 1 : ℕ) / p

/-- The common worst-order exponent is strictly positive. -/
theorem oracleRateExponent_pos {p q : ℕ} (P : Settings p q) :
    0 < oracleRateExponent p q := by
  have hp : 0 < p := P.order_pos.trans_le P.order_le
  have hq0 := P.order_pos
  unfold oracleRateExponent
  split_ifs <;> positivity

/-- Every actual order exponent is nonnegative and bounded by the fixed
largest-order exponent, in both source cases. -/
theorem evaluationExponent_le_oracleRate {p q : ℕ} (P : Settings p q) (a : Fin q) :
    0 ≤ evaluationExponent p q (modelOrder a) ∧
      evaluationExponent p q (modelOrder a) ≤ oracleRateExponent p q := by
  have hq := P.order_le
  have ha : modelOrder a ≤ q := a.isLt
  have hp : 0 < p := P.order_pos.trans_le hq
  rw [evaluationExponent_eq]
  unfold oracleRateExponent
  split_ifs
  · constructor
    · positivity
    · apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      exact_mod_cast (show p - q + 1 ≤ p - modelOrder a + 1 by omega)
  · constructor
    · positivity
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast ha

/-- The actual order-dependent accuracy factor is at least the minimum
requested accuracy raised to the common worst-order exponent. -/
theorem minimumAccuracy_pow_oracleRate_le {p q : ℕ} (P : Settings p q)
    (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a) (hε1 : ∀ a, ε a ≤ 1) :
    minimumAccuracy P.order_pos ε ^ oracleRateExponent p q ≤ accuracyFactor P ε :=
  OracleSimulation.minimum_power_lower P.order_pos ε
    (fun a => evaluationExponent p q (modelOrder a)) hε hε1
    (evaluationExponent_le_oracleRate P)

end InexactRegularization
