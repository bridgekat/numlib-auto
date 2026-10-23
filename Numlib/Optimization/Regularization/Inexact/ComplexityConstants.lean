import Numlib.Optimization.Regularization.Inexact.RunStepPowers

/-!
# Accuracy-independent constants for inexact regularization complexity

The finitely many positive step coefficients have a common positive decrease
coefficient. The accuracy factor is the true minimum of the source fractional
accuracy powers. Constants are defined before the requested accuracies or
execution data; the parameter and radius repairs are explicit in the step
coefficients.
-/

namespace InexactRegularization
open InexactTrustRegion HighOrderStep

/-- The source step-length accuracy exponent for order `j`. -/
noncomputable def rootStepExponent (p q j : ℕ) : ℝ :=
  if q ≤ 2 then 1 / ((p - j + 1 : ℕ) : ℝ) else (j : ℝ) / p

/-- The source objective-decrease accuracy exponent for order `j`. -/
noncomputable def evaluationExponent (p q j : ℕ) : ℝ :=
  rootStepExponent p q j * (p + 1 : ℕ)

/-- The decrease exponent has the two printed source formulas. -/
theorem evaluationExponent_eq (p q j : ℕ) : evaluationExponent p q j =
    if q ≤ 2 then ((p + 1 : ℕ) : ℝ) / (p - j + 1 : ℕ)
    else (j : ℝ) * (p + 1 : ℕ) / p := by
  unfold evaluationExponent rootStepExponent
  split_ifs <;> ring

/-- The actual common minimum of the source accuracy powers. -/
noncomputable def accuracyFactor {p q : ℕ} (P : Settings p q) (ε : Fin q → ℝ) : ℝ :=
  minimumAccuracy P.order_pos (fun a => (ε a) ^ evaluationExponent p q (modelOrder a))

/-- Positive requested accuracies yield a positive minimum rate factor. -/
theorem accuracyFactor_pos {p q : ℕ} (P : Settings p q) {ε : Fin q → ℝ}
    (hε : ∀ a, 0 < ε a) : 0 < accuracyFactor P ε :=
  minimumAccuracy_pos P.order_pos (fun a => Real.rpow_pos_of_pos (hε a) _)

/-- The actual minimum rate factor is below each order's requested power. -/
theorem accuracyFactor_le {p q : ℕ} (P : Settings p q) (ε : Fin q → ℝ) (a : Fin q) :
    accuracyFactor P ε ≤ (ε a) ^ evaluationExponent p q (modelOrder a) :=
  minimumAccuracy_le P.order_pos _ a

/-- The repaired step coefficient, independent of the requested accuracy. -/
noncomputable def rootStepCoefficient {p q : ℕ} (P : Settings p q)
    (L M S : ℝ) (j : ℕ) : ℝ :=
  let C := L + S + 3 * P.errorBound * P.stepCoefficient
  if q ≤ 2 then (criticalityCoefficient P.theta C j) ^
    (1 / ((p - j + 1 : ℕ) : ℝ))
  else (criticalityCoefficient P.theta C j * safeRadiusCoefficient P L M S ^ (j - 1)) ^
    (1 / (p : ℝ))

/-- Every repaired step coefficient is positive, before any accuracy is chosen. -/
theorem rootStepCoefficient_pos {p q : ℕ} (P : Settings p q)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M) (hS : 0 ≤ S) (j : ℕ) :
    0 < rootStepCoefficient P L M S j := by
  let C := L + S + 3 * P.errorBound * P.stepCoefficient
  have hC : 1 ≤ C := by
    have hp := mul_nonneg P.errorBound_nonneg P.stepCoefficient_pos.le
    dsimp [C]
    nlinarith
  have hcoef := criticalityCoefficient_mem P.theta_pos P.theta_lt_one hC j
  have hκ : 0 < safeRadiusCoefficient P L M S := lt_min
    (stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one P.theta_pos
      P.theta_lt_one.le hM).1
    (criticalityCoefficient_mem P.theta_pos P.theta_lt_one hC q).1
  unfold rootStepCoefficient
  split_ifs
  · exact Real.rpow_pos_of_pos hcoef.1 _
  · exact Real.rpow_pos_of_pos (mul_pos hcoef.1 (pow_pos hκ _)) _

/-- The accepted-decrease coefficient in each derivative order. -/
noncomputable def orderDecreaseCoefficient {p q : ℕ} (P : Settings p q)
    (L M S : ℝ) (a : Fin q) : ℝ :=
  P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) *
    rootStepCoefficient P L M S (modelOrder a) ^ (p + 1)

/-- The common coefficient is the actual finite minimum of all order coefficients. -/
noncomputable def commonDecreaseCoefficient {p q : ℕ} (P : Settings p q)
    (L M S : ℝ) : ℝ :=
  minimumAccuracy P.order_pos (orderDecreaseCoefficient P L M S)

/-- The common decrease coefficient is strictly positive independently of accuracies. -/
theorem commonDecreaseCoefficient_pos {p q : ℕ} (P : Settings p q)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M) (hS : 0 ≤ S) :
    0 < commonDecreaseCoefficient P L M S := by
  apply minimumAccuracy_pos P.order_pos
  intro a
  have hr := rootStepCoefficient_pos P hL hM hS (modelOrder a)
  have hη := P.eta1_pos
  have hσ := P.sigmaMin_pos
  unfold orderDecreaseCoefficient
  positivity

/-- The common decrease coefficient is below each actual order coefficient. -/
theorem commonDecreaseCoefficient_le {p q : ℕ} (P : Settings p q)
    (L M S : ℝ) (a : Fin q) :
    commonDecreaseCoefficient P L M S ≤ orderDecreaseCoefficient P L M S a :=
  minimumAccuracy_le P.order_pos _ a

/-- A separated fractional step lower bound lifts to an exact decrease power. -/
theorem pow_lower_of_root_step {n : ℕ} {a ε s r : ℝ}
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hbound : a * ε ^ r ≤ s) :
    a ^ n * ε ^ (r * (n : ℝ)) ≤ s ^ n := by
  have hh := pow_le_pow_left₀ (mul_nonneg ha (Real.rpow_nonneg hε _)) hbound n
  rw [mul_pow, ←Real.rpow_natCast (ε ^ r) n, ←Real.rpow_mul hε] at hh
  exact hh

end InexactRegularization
