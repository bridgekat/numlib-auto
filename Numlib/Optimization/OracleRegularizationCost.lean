import Numlib.Optimization.OracleRegularization

/-!
# Dimension-independent order constants for oracle regularization

Scaling the regularization floor with the derivative Lipschitz budget yields the natural
one-over-order power of that budget. The leading and additive constants below are independent
of the objective dimension, gap, Lipschitz budget and requested tolerance.
-/

noncomputable section
open scoped Nat
namespace Optimization.DerivativeOracle
open HigherOrderRegularization

/-- The fixed counting coefficient for the chosen acceptance/update ratios. -/
def regularizationCountingConstant : ℝ := 1 + |Real.log (1 / 2)| / Real.log 2

/-- The fixed leading complexity coefficient, depending only on derivative order. -/
def regularizationRateConstant (p : ℕ) : ℝ :=
  regularizationCountingConstant * (4 * ((p + 1)! : ℝ) *
    (criticalityConstant p 1 1 6 (1 / 2)) ^ (((p + 1 : ℕ) : ℝ) / p))

/-- The fixed additive trial overhead for the chosen update ratios. -/
def regularizationOverhead : ℝ :=
  regularizationCountingConstant + Real.log 6 / Real.log 2 + 1

/-- The counting coefficient is strictly positive. -/
theorem regularizationCountingConstant_pos : 0 < regularizationCountingConstant := by
  unfold regularizationCountingConstant
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (abs_nonneg _) (Real.log_pos (by norm_num)).le)

/-- The leading coefficient is strictly positive for every order. -/
theorem regularizationRateConstant_pos (p : ℕ) : 0 < regularizationRateConstant p := by
  unfold regularizationRateConstant
  exact mul_pos regularizationCountingConstant_pos (mul_pos (by positivity)
    (Real.rpow_pos_of_pos (criticalityConstant_pos (by norm_num) (by norm_num)
      (by norm_num)) _))

/-- The additive overhead is strictly positive. -/
theorem regularizationOverhead_pos : 0 < regularizationOverhead := by
  unfold regularizationOverhead
  have hlog : 0 ≤ Real.log 6 / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_pos (by norm_num)).le
  linarith [regularizationCountingConstant_pos]

/-- Expanding the inverse decrease coefficient gives its positive-power form. -/
theorem firstOrderComplexityConstant_eq (P : ParameterUpdates.RegularizationParameters)
    (p : ℕ) {L S theta : ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S) (htheta : 0 < theta) :
    firstOrderComplexityConstant P p L S theta =
      ((p + 1)! : ℝ) / (P.eta1 * P.sigmaMin) *
        (criticalityConstant p 1 L S theta) ^
          (((p + 1 : ℕ) : ℝ) / (p - 1 + 1 : ℕ)) := by
  unfold firstOrderComplexityConstant decreaseConstant
  rw [Real.inv_rpow (criticalityConstant_pos hL hS htheta).le]
  simp only [mul_inv_rev, inv_inv, inv_div]
  ring

/-- The leading inverse-decrease coefficient has the natural `L^(1/p)` scaling. -/
theorem regularization_firstOrderConstant_le {p : ℕ} (hp : 1 ≤ p) {L : ℝ} (hL : 1 ≤ L) :
    firstOrderComplexityConstant (regularizationParameters L) p L (6 * L) (1 / 2) ≤
      (4 * ((p + 1)! : ℝ) * criticalityConstant p 1 1 6 (1 / 2) ^
        (((p + 1 : ℕ) : ℝ) / p)) * L ^ ((p : ℝ)⁻¹) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hCpos : 0 < criticalityConstant p 1 1 6 (1 / 2) :=
    criticalityConstant_pos (by norm_num) (by norm_num) (by norm_num)
  have hC : criticalityConstant p 1 L (6 * L) (1 / 2) ≤
      L * criticalityConstant p 1 1 6 (1 / 2) := by
    unfold criticalityConstant
    calc
      _ = L * (7 / ((p - 1 + 1)! : ℝ)) + 1 / 2 := by ring
      _ ≤ L * (7 / ((p - 1 + 1)! : ℝ)) + L / 2 := by linarith
      _ = _ := by ring
  rw [firstOrderComplexityConstant_eq _ _ hLpos.le (by positivity) (by norm_num)]
  simp only [regularizationParameters, max_eq_right hL, Nat.sub_add_cancel hp]
  have hr : ((p + 1 : ℕ) : ℝ) / p = 1 + (p : ℝ)⁻¹ := by
    push_cast
    field_simp
  calc
    _ ≤ ((p + 1)! : ℝ) / (1 / 4 * L) *
        (L * criticalityConstant p 1 1 6 (1 / 2)) ^
          (((p + 1 : ℕ) : ℝ) / p) := by
      gcongr
      · exact (criticalityConstant_pos hLpos.le (by positivity) (by norm_num)).le
    _ = _ := by
      rw [Real.mul_rpow hLpos.le hCpos.le, hr, Real.rpow_add hLpos]
      simp only [Real.rpow_one]
      field_simp

/-- The exact implementation budget is bounded by fixed positive order constants times
`Delta L^(1/p) epsilon^(-(p+1)/p)`, with a fixed additive overhead. -/
theorem regularizationCost_le_order {p : ℕ} (hp : 1 ≤ p) {Delta L epsilon : ℝ}
    (hDelta : 0 ≤ Delta) (hL : 1 ≤ L) (hepsilon : 0 < epsilon) :
    regularizationCost p Delta L epsilon ≤ regularizationRateConstant p *
      (Delta * L ^ ((p : ℝ)⁻¹) * epsilon ^ (-(((p + 1 : ℕ) : ℝ) / p))) +
        regularizationOverhead := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hS : max (max 1 L) (3 * (L / (1 - 1 / 2))) = 6 * L := by
    rw [max_eq_right hL]
    have : 3 * (L / (1 - 1 / 2)) = 6 * L := by ring
    rw [this, max_eq_right (by linarith)]
  have hratio : 6 * L / L = (6 : ℝ) := by field_simp
  have hcost : regularizationCost p Delta L epsilon =
      regularizationCountingConstant *
        (firstOrderComplexityConstant (regularizationParameters L) p L (6 * L) (1 / 2) *
          (Delta / epsilon ^ (((p + 1 : ℕ) : ℝ) / p))) + regularizationOverhead := by
    change regularizationCountingConstant *
      (firstOrderComplexityConstant (regularizationParameters L) p L
        (max (max 1 L) (3 * (L / (1 - 1 / 2)))) (1 / 2) *
          (Delta / epsilon ^ (((p + 1 : ℕ) : ℝ) / p))) +
        regularizationCountingConstant +
        Real.log (max (max 1 L) (3 * (L / (1 - 1 / 2))) / max 1 L) / Real.log 2 + 1 = _
    rw [hS, max_eq_right hL, hratio]
    unfold regularizationOverhead
    ring
  rw [hcost]
  have hA := regularization_firstOrderConstant_le hp hL
  have hQ : 0 ≤ Delta / epsilon ^ (((p + 1 : ℕ) : ℝ) / p) := by positivity
  have hm := mul_le_mul_of_nonneg_right hA hQ
  have hm' := mul_le_mul_of_nonneg_left hm regularizationCountingConstant_pos.le
  calc
    _ ≤ regularizationCountingConstant *
        (((4 * ((p + 1)! : ℝ) * criticalityConstant p 1 1 6 (1 / 2) ^
          (((p + 1 : ℕ) : ℝ) / p)) * L ^ ((p : ℝ)⁻¹)) *
            (Delta / epsilon ^ (((p + 1 : ℕ) : ℝ) / p))) + regularizationOverhead :=
      add_le_add hm' le_rfl
    _ = _ := by
      rw [Real.rpow_neg hepsilon.le]
      unfold regularizationRateConstant
      ring

end Optimization.DerivativeOracle
