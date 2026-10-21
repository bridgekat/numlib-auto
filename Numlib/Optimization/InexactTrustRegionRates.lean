import Numlib.Optimization.InexactTrustRegionComplexity

/-!
# Explicit tolerance rates for implicit trust-region evaluation budgets

All rate coefficients depend only on fixed algorithm and analytic bounds. Tolerances occur
only as inverse powers and absolute logarithms, including the geometric derivative-refinement
term. Zero oracle-error multipliers are allowed.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactTrustRegion
open HigherOrderTrustRegion

/-- The tolerance-independent testing-radius coefficient. -/
def radiusRate (p : Parameters) (a : AccuracyParameters) (q : ℕ) (initial L K : ℝ) : ℝ :=
  InexactTrustRegion.radiusCoefficient p initial (errorCoefficient q L K a.stepConstant) *
    p.fraction / 2

/-- A tolerance-independent lower coefficient for the request threshold. -/
def accuracyRate (a : AccuracyParameters) (q : ℕ) (v α M K : ℝ) : ℝ :=
  min (a.stepConstant * (min 1 (α * v ^ q / (2 * (q ! : ℝ) * M))) ^ q)
    (v ^ q / (4 * (q ! : ℝ) * (K + 1)))

/-- The accuracy coefficient stays positive, including zero tensor-error multipliers. -/
theorem accuracyRate_pos {a : AccuracyParameters} {q : ℕ} {v α M K : ℝ}
    (hv : 0 < v) (hα : 0 < α) (hM : 0 < M) (hK : 0 ≤ K) :
    0 < accuracyRate a q v α M K := by
  have hs := a.stepConstant_pos
  unfold accuracyRate
  positivity

/-- The actual two-branch accuracy threshold is bounded below by one fixed power of tolerance. -/
theorem accuracyRate_mul_pow_le_threshold {a : AccuracyParameters} {q : ℕ} (hq : 1 ≤ q)
    {v α M K e : ℝ} (hv : 0 < v) (hα : 0 < α) (hM : 0 < M) (hK : 0 ≤ K)
    (he : 0 < e) (he1 : e ≤ 1) :
    accuracyRate a q v α M K * e ^ (q * (q + 1)) ≤
      requestThreshold a q e (v * e) (α * e) M K := by
  let d := α * v ^ q / (2 * (q ! : ℝ) * M)
  have hd : 0 < d := by dsimp [d]; positivity
  have ht : e ^ (q + 1) ≤ 1 := pow_le_one₀ he.le he1
  have heq : ((α * e) * (v * e) ^ q / (q ! : ℝ)) / (2 * M) = d * e ^ (q + 1) := by
    dsimp [d]
    rw [mul_pow, pow_succ]
    ring
  have hmin : min 1 d * e ^ (q + 1) ≤ min 1 (d * e ^ (q + 1)) := by
    apply le_min
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg he.le _)).trans
        (by simpa using ht)
    · exact mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg he.le _)
  have hstep := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_nonneg (le_min (by norm_num) hd.le) (pow_nonneg he.le _)) hmin q)
    a.stepConstant_pos.le
  have hpow : (e ^ (q + 1)) ^ q = e ^ (q * (q + 1)) := by
    rw [← pow_mul, Nat.mul_comm]
  have hstep' : (a.stepConstant * (min 1 d) ^ q) * e ^ (q * (q + 1)) ≤
      a.stepConstant * (min 1 (d * e ^ (q + 1))) ^ q := by
    simpa only [mul_pow, hpow, mul_assoc] using hstep
  have hexp : q + 1 ≤ q * (q + 1) := by nlinarith
  have hp := pow_le_pow_of_le_one he.le he1 hexp
  have hpass : (v ^ q / (4 * (q ! : ℝ) * (K + 1))) * e ^ (q * (q + 1)) ≤
      e * (v * e) ^ q / (4 * (q ! : ℝ) * (K + 1)) := by
    have hm := mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ v ^ q / (4 * (q ! : ℝ) * (K + 1)))
    convert hm using 1
    rw [mul_pow, pow_succ]
    ring
  unfold requestThreshold
  rw [heq]
  apply le_min
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (pow_nonneg he.le _)).trans hstep'
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (pow_nonneg he.le _)).trans hpass

/-- A positive geometric refinement budget is at most its explicit absolute-log bound. -/
theorem refinementBudget_le_log {a : AccuracyParameters} {H0 H c e : ℝ} {r : ℕ}
    (hH0 : 0 < H0) (hc : 0 < c) (he : 0 < e) (hH : c * e ^ r ≤ H) :
    (refinementBudget a H0 H : ℝ) ≤
      (|Real.log (H0 / c)| + r * |Real.log e|) / |Real.log a.contraction| + 1 := by
  have hb : 1 < a.contraction⁻¹ := (one_lt_inv₀ a.contraction_pos).mpr a.contraction_lt_one
  have hbpos : 0 < a.contraction⁻¹ := inv_pos.mpr a.contraction_pos
  have hlog : 0 < Real.log a.contraction⁻¹ := Real.log_pos hb
  have habs : |Real.log a.contraction| = Real.log a.contraction⁻¹ := by
    rw [Real.log_inv, abs_of_neg (Real.log_neg a.contraction_pos a.contraction_lt_one)]
  have hHp : 0 < H := (mul_pos hc (pow_pos he _)).trans_le hH
  rw [habs]
  unfold refinementBudget MeasureDomination.geometricIterationCount
  split_ifs with hsmall
  · simp only [Nat.cast_zero]
    positivity
  · have hratio : 1 ≤ H0 / H := (one_le_div hHp).mpr (le_of_not_ge hsmall)
    have hx : 0 ≤ Real.log (H0 / H) / Real.log a.contraction⁻¹ :=
      div_nonneg (Real.log_nonneg hratio) hlog.le
    have hceil := (Nat.ceil_lt_add_one hx).le
    have hmono := Real.log_le_log (div_pos hH0 hHp)
      (div_le_div_of_nonneg_left hH0.le (mul_pos hc (pow_pos he _)) hH)
    have heq : Real.log (H0 / (c * e ^ r)) = Real.log (H0 / c) - r * Real.log e := by
      rw [Real.log_div hH0.ne' (mul_pos hc (pow_pos he _)).ne',
        Real.log_mul hc.ne' (pow_pos he _).ne', Real.log_pow,
        Real.log_div hH0.ne' hc.ne']
      ring
    rw [heq] at hmono
    have hsign := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log e)) (Nat.cast_nonneg r)
    have hlast : Real.log (H0 / H) ≤ |Real.log (H0 / c)| + r * |Real.log e| := by
      linarith [le_abs_self (Real.log (H0 / c))]
    exact hceil.trans (add_le_add (div_le_div_of_nonneg_right hlast hlog.le) le_rfl)

/-- Tolerance-independent successful-trial coefficient. -/
def successRate (p : Parameters) (q : ℕ) (v : ℝ) : ℝ :=
  (q ! : ℝ) / (p.eta1 * v ^ (q + 1))

/-- Successful-trial rates factor the exact inverse tolerance power from the descent budget. -/
theorem successBudget_eq {p : Parameters} {a : AccuracyParameters} {q : ℕ}
    {initial L K e gap : ℝ} (hv : 0 < radiusRate p a q initial L K) (he : 0 < e) :
    successBudget p a q initial L K e gap =
      successRate p q (radiusRate p a q initial L K) * gap / e ^ (q + 1) := by
  have heta := p.eta1_pos
  have hr : radiusFloor p a q initial L K e = radiusRate p a q initial L K * e := by
    unfold radiusFloor radiusRate
    ring
  unfold successBudget decreaseFloor
  rw [hr, mul_pow]
  unfold successRate
  field_simp [hv.ne', he.ne', heta.ne']

/-- Separating the radius and tolerance logarithms exposes the function-call rate. -/
theorem trialBudget_le_rate {p : Parameters} {a : AccuracyParameters} {q : ℕ}
    {initial L K e gap : ℝ} (hi : 0 < initial)
    (hv : 0 < radiusRate p a q initial L K) (he : 0 < e) :
    InexactTrustRegion.trialBudget p a q initial L K e gap ≤
      successRate p q (radiusRate p a q initial L K) * trialFactor p * gap / e ^ (q + 1) +
        (|Real.log (radiusRate p a q initial L K / initial)| + |Real.log e|) /
          |Real.log p.gamma2| := by
  have hr : radiusFloor p a q initial L K e / initial =
      (radiusRate p a q initial L K / initial) * e := by
    unfold radiusFloor radiusRate
    ring
  unfold InexactTrustRegion.trialBudget
  rw [successBudget_eq hv he, hr, Real.log_mul (div_pos hv hi).ne' he.ne']
  have ha := abs_add_le (Real.log (radiusRate p a q initial L K / initial)) (Real.log e)
  have hd := div_le_div_of_nonneg_right ha (abs_nonneg (Real.log p.gamma2))
  convert add_le_add le_rfl hd using 1
  ring

/-- The successful-trial evaluation coefficient, depending only on fixed analytic and
algorithm data. -/
def successEvaluationRate (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K : ℝ) : ℝ := successRate p q (radiusRate p a q initial L K)

/-- The function-evaluation inverse-power coefficient, independent of all tolerances and traces. -/
def functionRate (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K : ℝ) : ℝ := successEvaluationRate p a q initial L K * trialFactor p

/-- The function-evaluation logarithmic coefficient, independent of all tolerances and traces. -/
def functionLogRate (p : Parameters) : ℝ := 1 / |Real.log p.gamma2|

/-- The function-evaluation additive coefficient, independent of all tolerances and traces. -/
def functionOffsetRate (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K : ℝ) : ℝ :=
  |Real.log (radiusRate p a q initial L K / initial)| / |Real.log p.gamma2| + 1

/-- The eager derivative-batch logarithmic coefficient, independent of tolerances and traces. -/
def derivativeLogRate (a : AccuracyParameters) (q : ℕ) : ℝ :=
  (q * (q + 1) : ℕ) / |Real.log a.contraction| + 1

/-- The eager derivative-batch additive coefficient, depending only on fixed analytic, algorithm
and initial request bounds. No tolerance or execution trace occurs in its definition. -/
def derivativeOffsetRate (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K M H0 : ℝ) : ℝ :=
  |Real.log (H0 / accuracyRate a q (radiusRate p a q initial L K) (p.fraction / 2) M K)| /
    |Real.log a.contraction| + 2

/-- All six evaluation-rate coefficients are positive under fixed analytic bounds. -/
theorem evaluationRates_pos {p : Parameters} {a : AccuracyParameters} {q : ℕ}
    {initial L K M H0 : ℝ} (hi : 0 < initial) (hL : 0 < L) (hK : 0 ≤ K) :
    0 < functionRate p a q initial L K ∧ 0 < functionLogRate p ∧
    0 < functionOffsetRate p a q initial L K ∧ 0 < successEvaluationRate p a q initial L K ∧
    0 < derivativeLogRate a q ∧ 0 < derivativeOffsetRate p a q initial L K M H0 := by
  have hks := a.stepConstant_pos
  have hfrac := p.fraction_pos
  have heta := p.eta1_pos
  have hC : 0 < errorCoefficient q L K a.stepConstant := by
    dsimp [errorCoefficient]; positivity
  have hc := radiusCoefficient_pos (p := p) hi hC
  have hv : 0 < radiusRate p a q initial L K := by dsimp [radiusRate]; positivity
  have hg2 : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  have hgh : 0 < |Real.log a.contraction| := abs_pos.mpr
    (Real.log_neg a.contraction_pos a.contraction_lt_one).ne
  have hfactor : 0 < trialFactor p := by
    unfold trialFactor
    have hh := div_nonneg (Real.log_nonneg p.one_le_gamma3) hg2.le
    linarith
  have hs : 0 < successEvaluationRate p a q initial L K := by
    unfold successEvaluationRate successRate
    positivity
  refine ⟨mul_pos hs hfactor, one_div_pos.mpr hg2, ?_, hs, ?_, ?_⟩
  · dsimp [functionOffsetRate]; positivity
  · dsimp [derivativeLogRate]; positivity
  · dsimp [derivativeOffsetRate]; positivity

end Optimization.InexactTrustRegion
