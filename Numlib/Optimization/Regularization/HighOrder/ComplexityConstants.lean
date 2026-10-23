import Numlib.Optimization.Regularization.HighOrder.RunBounds
import Numlib.Optimization.HighOrder.StepLower
import Numlib.Optimization.Regularization.Inexact.ComplexityConstants

/-!
# Fixed constants for exact high-order regularization complexity

The step exponents are the common low-order and high-order source exponents.
Actual finite minima of positive step/decrease coefficients give constants
chosen before all requested accuracies or execution arrays. The safe radius
coefficient repairs the high-order scalar comparison without changing rates.
-/

namespace HighOrderRegularization
open InexactTrustRegion HighOrderStep
open InexactRegularization (rootStepExponent evaluationExponent)

/-- The actual finite minimum of the source accuracy powers for exact ARqp. -/
noncomputable def accuracyFactor {p q : ℕ} (P : Settings p q) (ε : Fin q → ℝ) : ℝ :=
  minimumAccuracy P.order_pos (fun a => (ε a) ^ evaluationExponent p q (modelOrder a))

/-- Positive accuracies make the exact finite minimum rate positive. -/
theorem accuracyFactor_pos {p q : ℕ} (P : Settings p q) {ε : Fin q → ℝ}
    (hε : ∀ a, 0 < ε a) : 0 < accuracyFactor P ε :=
  minimumAccuracy_pos P.order_pos (fun a => Real.rpow_pos_of_pos (hε a) _)

/-- The common minimum rate does not exceed any order's accuracy power. -/
theorem accuracyFactor_le {p q : ℕ} (P : Settings p q) (ε : Fin q → ℝ) (a : Fin q) :
    accuracyFactor P ε ≤ (ε a) ^ evaluationExponent p q (modelOrder a) :=
  minimumAccuracy_le P.order_pos _ a

/-- The fixed exact step coefficient, with an explicitly safe high-order radius. -/
noncomputable def rootStepCoefficient {p q : ℕ} (P : Settings p q)
    (L S : ℝ) (j : ℕ) : ℝ :=
  if q ≤ 2 then (criticalityCoefficient P.theta (L + S) j) ^
    (1 / ((p - j + 1 : ℕ) : ℝ))
  else (criticalityCoefficient P.theta (L + S) j *
    regularizationRadiusCoefficient P.zeta P.theta L L S q ^ (j - 1)) ^ (1 / (p : ℝ))

/-- Every fixed step coefficient is positive before an accuracy is chosen. -/
theorem rootStepCoefficient_pos {p q : ℕ} (P : Settings p q)
    {L S : ℝ} (hL : 1 ≤ L) (hS : 0 ≤ S) (j : ℕ) :
    0 < rootStepCoefficient P L S j := by
  have hc := criticalityCoefficient_mem P.theta_pos P.theta_lt_one
    (by linarith : 1 ≤ L + S) j
  have hκ := (regularizationRadiusCoefficient_mem P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one hL hL hS q).1
  unfold rootStepCoefficient
  split_ifs
  · exact Real.rpow_pos_of_pos hc.1 _
  · exact Real.rpow_pos_of_pos (mul_pos hc.1 (pow_pos hκ _)) _

/-- The actual accepted objective-decrease coefficient in a particular order. -/
noncomputable def orderDecreaseCoefficient {p q : ℕ} (P : Settings p q)
    (L S : ℝ) (a : Fin q) : ℝ :=
  P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) *
    rootStepCoefficient P L S (modelOrder a) ^ (p + 1)

/-- The common fixed decrease coefficient is the genuine finite minimum. -/
noncomputable def commonDecreaseCoefficient {p q : ℕ} (P : Settings p q)
    (L S : ℝ) : ℝ := minimumAccuracy P.order_pos (orderDecreaseCoefficient P L S)

/-- The common decrease coefficient is positive independently of all accuracies. -/
theorem commonDecreaseCoefficient_pos {p q : ℕ} (P : Settings p q)
    {L S : ℝ} (hL : 1 ≤ L) (hS : 0 ≤ S) : 0 < commonDecreaseCoefficient P L S := by
  apply minimumAccuracy_pos P.order_pos
  intro a
  have hr := rootStepCoefficient_pos P hL hS (modelOrder a)
  have hη := P.eta1_pos
  have hσ := P.sigmaMin_pos
  unfold orderDecreaseCoefficient
  positivity

/-- The genuine common minimum is below each actual order coefficient. -/
theorem commonDecreaseCoefficient_le {p q : ℕ} (P : Settings p q) (L S : ℝ) (a : Fin q) :
    commonDecreaseCoefficient P L S ≤ orderDecreaseCoefficient P L S a :=
  minimumAccuracy_le P.order_pos _ a

/-- The finite minimum rate has the two literal source exponent formulas. -/
theorem accuracyFactor_eq {p q : ℕ} (P : Settings p q) (ε : Fin q → ℝ) :
    accuracyFactor P ε = minimumAccuracy P.order_pos (fun a => (ε a) ^
      (if q ≤ 2 then ((p + 1 : ℕ) : ℝ) / (p - modelOrder a + 1 : ℕ)
      else (modelOrder a : ℝ) * (p + 1 : ℕ) / p)) := by
  simp only [accuracyFactor, InexactRegularization.evaluationExponent_eq]

end HighOrderRegularization
