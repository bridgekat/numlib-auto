import Numlib.Optimization.Regularization.Inexact.Explicit.StepPowers
import Numlib.Optimization.Regularization.Inexact.ComplexityConstants

/-!
# Fixed effective-margin constants for explicit regularization

The added positive stopping margin changes the coefficients but preserves all
source accuracy exponents. Actual finite minima are positive before requested
accuracies, jets or execution data are supplied.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion HighOrderStep

/-- The repaired step coefficient, independent of the requested accuracy. -/
noncomputable def rootStepCoefficient {p q : ℕ} (P : Settings p q)
    (L M S : ℝ) (j : ℕ) : ℝ :=
  let C := L + S + 4 * P.stepCoefficient
  if q ≤ 2 then (criticalityCoefficient (1 - P.zeta / 2 + P.theta) C j) ^
    (1 / ((p - j + 1 : ℕ) : ℝ))
  else (criticalityCoefficient (1 - P.zeta / 2 + P.theta) C j *
    safeRadiusCoefficient P L M S ^ (j - 1)) ^
    (1 / (p : ℝ))

/-- Every repaired step coefficient is positive, before any accuracy is chosen. -/
theorem rootStepCoefficient_pos {p q : ℕ} (P : Settings p q) (hmargin : P.theta < P.zeta / 2)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M) (hS : 0 ≤ S) (j : ℕ) :
    0 < rootStepCoefficient P L M S j := by
  let C := L + S + 4 * P.stepCoefficient
  have hC : 1 ≤ C := by
    have hp := P.stepCoefficient_pos.le
    dsimp [C]
    nlinarith
  have heff0 : 0 < 1 - P.zeta / 2 + P.theta := by
    have := P.zeta_le_one; have := P.theta_pos; linarith
  have heff1 : 1 - P.zeta / 2 + P.theta < 1 := by linarith
  have hcoef := criticalityCoefficient_mem heff0 heff1 hC j
  have hκ : 0 < safeRadiusCoefficient P L M S := lt_min
    (stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one P.theta_pos
      P.theta_lt_one.le hM).1
    (criticalityCoefficient_mem heff0 heff1 hC q).1
  unfold rootStepCoefficient
  split_ifs
  · exact Real.rpow_pos_of_pos hcoef.1 _
  · exact Real.rpow_pos_of_pos (mul_pos hcoef.1 (pow_pos hκ _)) _

/-- The accepted-decrease coefficient in each derivative order. -/
noncomputable def orderDecreaseCoefficient {p q : ℕ} (P : Settings p q)
    (L M S : ℝ) (a : Fin q) : ℝ :=
  P.eta1 * P.sigmaMin / (2 * ((p + 1).factorial : ℝ)) *
    rootStepCoefficient P L M S (modelOrder a) ^ (p + 1)

/-- The common coefficient is the actual finite minimum of all order coefficients. -/
noncomputable def commonDecreaseCoefficient {p q : ℕ} (P : Settings p q)
    (L M S : ℝ) : ℝ :=
  minimumAccuracy P.order_pos (orderDecreaseCoefficient P L M S)

/-- The common decrease coefficient is strictly positive independently of accuracies. -/
theorem commonDecreaseCoefficient_pos {p q : ℕ} (P : Settings p q) (hmargin : P.theta <
  P.zeta / 2)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M) (hS : 0 ≤ S) :
    0 < commonDecreaseCoefficient P L M S := by
  apply minimumAccuracy_pos P.order_pos
  intro a
  have hr := rootStepCoefficient_pos P hmargin hL hM hS (modelOrder a)
  have hη := P.eta1_pos
  have hσ := P.sigmaMin_pos
  unfold orderDecreaseCoefficient
  positivity

/-- The common decrease coefficient is below each actual order coefficient. -/
theorem commonDecreaseCoefficient_le {p q : ℕ} (P : Settings p q)
    (L M S : ℝ) (a : Fin q) :
    commonDecreaseCoefficient P L M S ≤ orderDecreaseCoefficient P L M S a :=
  minimumAccuracy_le P.order_pos _ a

end InexactRegularization.Explicit
