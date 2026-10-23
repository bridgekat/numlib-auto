import Numlib.Optimization.Composite.RunStepPowers
import Numlib.Optimization.Regularization.HighOrder.RunBounds
import Numlib.Optimization.Regularization.Inexact.ComplexityConstants

/-!
# Fixed composite complexity constants

The finite minima are the actual requested accuracy powers. Positive step and
decrease coefficients are fixed before the accuracies or execution arrays.
The first-order convex rate and the general composite rate are kept distinct.
-/

namespace Composite
open InexactTrustRegion
open HighOrderRegularization (parameterCap parameterCap_pos)

/-- The actual minimum of the general composite accuracy powers. -/
noncomputable def generalAccuracyFactor {p q : ℕ} (P : Settings p q)
    (ε : Fin q → ℝ) : ℝ :=
  minimumAccuracy P.order_pos (fun a => ε a ^ (modelOrder a + 1))

/-- Positive accuracies give a positive general composite rate factor. -/
theorem generalAccuracyFactor_pos {p q : ℕ} (P : Settings p q) {ε : Fin q → ℝ}
    (hε : ∀ a, 0 < ε a) : 0 < generalAccuracyFactor P ε :=
  minimumAccuracy_pos P.order_pos (fun a => pow_pos (hε a) _)

/-- The minimum general rate factor is below every actual order power. -/
theorem generalAccuracyFactor_le {p q : ℕ} (P : Settings p q)
    (ε : Fin q → ℝ) (a : Fin q) :
    generalAccuracyFactor P ε ≤ ε a ^ (modelOrder a + 1) :=
  minimumAccuracy_le P.order_pos _ a

/-- The first-order convex composite evaluation exponent. -/
noncomputable def unitExponent (p : ℕ) : ℝ := ((p + 1 : ℕ) : ℝ) / p

/-- The actual minimum of the unit-radius first-order accuracy powers. -/
noncomputable def unitAccuracyFactor {p q : ℕ} (P : Settings p q)
    (ε : Fin q → ℝ) : ℝ :=
  minimumAccuracy P.order_pos (fun a => ε a ^ unitExponent p)

/-- Positive accuracies give a positive unit-radius rate factor. -/
theorem unitAccuracyFactor_pos {p q : ℕ} (P : Settings p q) {ε : Fin q → ℝ}
    (hε : ∀ a, 0 < ε a) : 0 < unitAccuracyFactor P ε :=
  minimumAccuracy_pos P.order_pos (fun a => Real.rpow_pos_of_pos (hε a) _)

/-- The minimum unit-radius rate factor is below every component power. -/
theorem unitAccuracyFactor_le {p q : ℕ} (P : Settings p q)
    (ε : Fin q → ℝ) (a : Fin q) :
    unitAccuracyFactor P ε ≤ ε a ^ unitExponent p :=
  minimumAccuracy_le P.order_pos _ a

/-- The fixed first-order root-step coefficient, independent of accuracy. -/
noncomputable def unitStepCoefficient {p q : ℕ} (P : Settings p q) (L S : ℝ) : ℝ :=
  (CompositeStep.coefficient P.theta (L + S) (2 * L) 1) ^ (1 / (p : ℝ))

/-- The first-order root-step coefficient is positive. -/
theorem unitStepCoefficient_pos {p q : ℕ} (P : Settings p q) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 ≤ S) : 0 < unitStepCoefficient P L S := by
  exact Real.rpow_pos_of_pos (CompositeStep.coefficient_mem P.theta_pos P.theta_lt_one
    (by linarith : 1 ≤ L + S) (by linarith : 0 ≤ 2 * L) 1).1 _

/-- The actual fixed objective-decrease coefficient for the general composite rate. -/
noncomputable def generalDecreaseCoefficient {p q : ℕ} (P : Settings p q)
    (L S : ℝ) : ℝ :=
  P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) * stepCoefficient P L S ^ (q + 1)

/-- The general composite decrease coefficient is positive before accuracies. -/
theorem generalDecreaseCoefficient_pos {p q : ℕ} (P : Settings p q) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 ≤ S) : 0 < generalDecreaseCoefficient P L S :=
  mul_pos (div_pos (mul_pos P.eta1_pos P.sigmaMin_pos) (by positivity))
    (pow_pos (stepCoefficient_mem P hL hS).1 _)

/-- The actual fixed objective-decrease coefficient at unit first-order radii. -/
noncomputable def unitDecreaseCoefficient {p q : ℕ} (P : Settings p q)
    (L S : ℝ) : ℝ :=
  P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) * unitStepCoefficient P L S ^ (p + 1)

/-- The unit-radius decrease coefficient is positive before accuracies. -/
theorem unitDecreaseCoefficient_pos {p q : ℕ} (P : Settings p q) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 ≤ S) : 0 < unitDecreaseCoefficient P L S :=
  mul_pos (div_pos (mul_pos P.eta1_pos P.sigmaMin_pos) (by positivity))
    (pow_pos (unitStepCoefficient_pos P hL hS) _)

end Composite
