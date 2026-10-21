import Numlib.Optimization.ExplicitTrustRegionComplexity
import Numlib.Optimization.InexactTrustRegionRates

/-!
# Explicit tolerance rates for certified trust-region evaluation budgets

All rate coefficients depend only on fixed algorithm and analytic bounds. Tolerances occur
only as inverse powers and absolute logarithms, including the geometric derivative-refinement
term. Zero oracle-error multipliers are allowed.
-/

noncomputable section
open scoped Nat
namespace Optimization.ExplicitTrustRegion
open HigherOrderTrustRegion

/-- The tolerance-independent testing-radius coefficient. -/
abbrev radiusRate := InexactTrustRegion.radiusRate

/-- A tolerance-independent lower coefficient for the request threshold. -/
def accuracyRate (p : Parameters) (a : AccuracyParameters) (q : ℕ) (v α M K : ℝ) : ℝ :=
  min (a.stepConstant * (min 1 (α * v ^ q / (2 * (q ! : ℝ) * M))) ^ q)
    (p.fraction * v ^ q / (4 * (q ! : ℝ) * (K + 1)))

/-- The accuracy coefficient stays positive, including zero tensor-error multipliers. -/
theorem accuracyRate_pos {p : Parameters} {a : AccuracyParameters} {q : ℕ} {v α M K : ℝ}
    (hv : 0 < v) (hα : 0 < α) (hM : 0 < M) (hK : 0 ≤ K) :
    0 < accuracyRate p a q v α M K := by
  have hs := a.stepConstant_pos
  have hv := p.fraction_pos
  unfold accuracyRate
  positivity

/-- The actual two-branch accuracy threshold is bounded below by one fixed power of tolerance. -/
theorem accuracyRate_mul_pow_le_threshold {p : Parameters} {a : AccuracyParameters} {q : ℕ} (hq
  : 1 ≤ q)
    {v α M K e : ℝ} (hv : 0 < v) (hα : 0 < α) (hM : 0 < M) (hK : 0 ≤ K)
    (he : 0 < e) (he1 : e ≤ 1) :
    accuracyRate p a q v α M K * e ^ (q * (q + 1)) ≤
      requestThreshold p a q e (v * e) (α * e) M K := by
  have hfrac := p.fraction_pos
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
  have hpass : (p.fraction * v ^ q / (4 * (q ! : ℝ) * (K + 1))) * e ^ (q * (q + 1)) ≤
      p.fraction * e * (v * e) ^ q / (4 * (q ! : ℝ) * (K + 1)) := by
    have hm := mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ p.fraction * v ^ q / (4 * (q ! : ℝ) * (K + 1)))
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

/-- The geometric countdown has the same explicit logarithmic bound as the shared IDA
countdown: its definition depends only on the contraction and requested absolute threshold. -/
theorem refinementBudget_le_log {a : AccuracyParameters} {H0 H c e : ℝ} {r : ℕ}
    (hH0 : 0 < H0) (hc : 0 < c) (he : 0 < e) (hH : c * e ^ r ≤ H) :
    (refinementBudget a H0 H : ℝ) ≤
      (|Real.log (H0 / c)| + r * |Real.log e|) / |Real.log a.contraction| + 1 :=
  InexactTrustRegion.refinementBudget_le_log hH0 hc he hH

/-- Tolerance-independent successful-trial coefficient. -/
def successRate (p : Parameters) (q : ℕ) (v : ℝ) : ℝ :=
  2 * (q ! : ℝ) / (p.eta1 * v ^ (q + 1))

/-- Successful-trial rates factor the exact inverse tolerance power from the descent budget. -/
theorem successBudget_eq {p : Parameters} {a : AccuracyParameters} {q : ℕ}
    {initial L K e gap : ℝ} (hv : 0 < radiusRate p a q initial L K) (he : 0 < e) :
    successBudget p a q initial L K e gap =
      successRate p q (radiusRate p a q initial L K) * gap / e ^ (q + 1) := by
  have heta := p.eta1_pos
  have hr : radiusFloor p a q initial L K e = radiusRate p a q initial L K * e := by
    unfold radiusFloor radiusRate InexactTrustRegion.radiusRate
    ring
  unfold successBudget decreaseFloor
  rw [hr, mul_pow]
  unfold successRate
  field_simp [hv.ne', he.ne', heta.ne']

/-- Separating the radius and tolerance logarithms exposes the function-call rate. -/
theorem trialBudget_le_rate {p : Parameters} {a : AccuracyParameters} {q : ℕ}
    {initial L K e gap : ℝ} (hi : 0 < initial)
    (hv : 0 < radiusRate p a q initial L K) (he : 0 < e) :
    ExplicitTrustRegion.trialBudget p a q initial L K e gap ≤
      successRate p q (radiusRate p a q initial L K) * trialFactor p * gap / e ^ (q + 1) +
        (|Real.log (radiusRate p a q initial L K / initial)| + |Real.log e|) /
          |Real.log p.gamma2| := by
  have hr : radiusFloor p a q initial L K e / initial =
      (radiusRate p a q initial L K / initial) * e := by
    unfold radiusFloor radiusRate InexactTrustRegion.radiusRate
    ring
  unfold ExplicitTrustRegion.trialBudget
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
abbrev functionLogRate := InexactTrustRegion.functionLogRate

/-- The function-evaluation additive coefficient, independent of all tolerances and traces. -/
abbrev functionOffsetRate := InexactTrustRegion.functionOffsetRate

/-- The eager derivative-batch logarithmic coefficient, independent of tolerances and traces. -/
abbrev derivativeLogRate := InexactTrustRegion.derivativeLogRate

/-- The eager derivative-batch additive coefficient, depending only on fixed analytic, algorithm
and initial request bounds. No tolerance or execution trace occurs in its definition. -/
def derivativeOffsetRate (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (initial L K M H0 : ℝ) : ℝ :=
  |Real.log (H0 / accuracyRate p a q (radiusRate p a q initial L K) (p.fraction / 2) M K)| /
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
    dsimp [errorCoefficient, InexactTrustRegion.errorCoefficient]; positivity
  have hc := radiusCoefficient_pos (p := p) hi hC
  have hv : 0 < radiusRate p a q initial L K := by
    dsimp [radiusRate, InexactTrustRegion.radiusRate]
    positivity
  have hg2 : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  have hgh : 0 < |Real.log a.contraction| := abs_pos.mpr
    (Real.log_neg a.contraction_pos a.contraction_lt_one).ne
  have hfactor : 0 < trialFactor p := by
    unfold trialFactor InexactTrustRegion.trialFactor
    have hh := div_nonneg (Real.log_nonneg p.one_le_gamma3) hg2.le
    linarith
  have hs : 0 < successEvaluationRate p a q initial L K := by
    unfold successEvaluationRate successRate
    positivity
  refine ⟨mul_pos hs hfactor, one_div_pos.mpr hg2, ?_, hs, ?_, ?_⟩
  · dsimp [functionOffsetRate, InexactTrustRegion.functionOffsetRate]; positivity
  · dsimp [derivativeLogRate, InexactTrustRegion.derivativeLogRate]; positivity
  · dsimp [derivativeOffsetRate]; positivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {q : ℕ} {p : Parameters} {a : AccuracyParameters}
  {epsilon : ℕ → ℝ} {emin H0 : ℝ} {O : Oracle f q} {t : Trace E}

/-- Fixed analytic data give explicit inverse-power and logarithmic query bounds at the first
observable certificate. The rate coefficients contain neither tolerances nor execution data. -/
theorem IsExecution.exists_first_certificate_rates
    (h : IsExecution p a epsilon emin O t) (hq : 1 ≤ q)
    (he : 0 < emin ∧ emin ≤ 1) (hetheta : emin ≤ p.theta)
    (heps : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j)
    (hh0 : ∀ i ∈ Finset.Icc 1 q, t.request 0 i ≤ H0) (hH0 : 0 < H0) {initial L K M : ℝ}
    (hinit : t.radius 0 = initial) (hL : 0 < L) (hK : 0 ≤ K) (hM : 0 < M)
    (hO : UniformAccuracy O K)
    (hfL : ∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L)
    (hA : ∀ k, (∀ j < k, ¬Certified p epsilon emin O t j) →
      ∀ i ∈ Finset.Icc 1 q, ‖coefficients O t k i‖ ≤ M)
    {low : ℝ} (hlow : ∀ x, low ≤ f x) :
    ∃ k : ℕ, Certified p epsilon emin O t k ∧
      (∀ j < k, ¬Certified p epsilon emin O t j) ∧
      (0 < ExplicitTrustRegion.testRadius p t k ∧ ExplicitTrustRegion.testRadius p t k ≤ 1) ∧
      ((functionQueries t k).length : ℝ) ≤
        2 * functionRate p a q initial L K * (f (t.point 0) - low) /
            emin ^ (q + 1) +
          2 * functionLogRate p * |Real.log (emin)| +
            2 * functionOffsetRate p a q initial L K ∧
      ((derivativeQueries p O t k).length : ℝ) ≤
        successEvaluationRate p a q initial L K * (f (t.point 0) - low) /
            emin ^ (q + 1) +
          derivativeLogRate a q * |Real.log (emin)| +
            derivativeOffsetRate p a q initial L K M H0 := by
  have hp := h 0 (by simp)
  let e := emin
  have hi : 0 < initial := by simpa only [hinit] using hp.initial_pos
  let v := radiusRate p a q initial L K
  have hks := a.stepConstant_pos
  have hfrac := p.fraction_pos
  have heta := p.eta1_pos
  have hC : 0 < errorCoefficient q L K a.stepConstant := by
    dsimp [errorCoefficient, InexactTrustRegion.errorCoefficient]; positivity
  have hc := ExplicitTrustRegion.radiusCoefficient_pos (p := p) hi hC
  have hv : 0 < v := by dsimp [v, radiusRate, InexactTrustRegion.radiusRate]; positivity
  let ca := accuracyRate p a q v (p.fraction / 2) M K
  have hca : 0 < ca := accuracyRate_pos hv (by positivity) hM hK
  have hthreshold : ca * e ^ (q * (q + 1)) ≤
      analysisThreshold p a q initial L K M e := by
    have ht := accuracyRate_mul_pow_le_threshold (p := p) (a := a) hq hv
      (by positivity : 0 < p.fraction / 2) hM hK he.1 he.2
    convert ht using 1
    simp only [analysisThreshold, radiusFloor, InexactTrustRegion.radiusRate, v]
    congr 2 <;> ring
  have hrbudget := refinementBudget_le_log (a := a) hH0 hca he.1 hthreshold
  let D := (q * (q + 1) : ℕ) / |Real.log a.contraction| + 1
  let F := |Real.log (H0 / ca)| / |Real.log a.contraction| + 2
  obtain ⟨k, _, hq, hfirst, hradius, hfc, hdc⟩ :=
    ExplicitTrustRegion.IsExecution.exists_first_certificate h he.1 he.2 hetheta heps
      hK hL hM hO hfL hA hh0 hlow
  rw [hinit] at hfc hdc
  refine ⟨k, hq, hfirst, hradius, ?_, ?_⟩
  · have ht := trialBudget_le_rate hi hv he.1
      (gap := f (t.point 0) - low)
    have hh := hfc.trans (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2))
    have hfinal := hh.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
    convert hfinal using 1
    dsimp [functionRate, functionLogRate, functionOffsetRate, successEvaluationRate,
      InexactTrustRegion.functionLogRate, InexactTrustRegion.functionOffsetRate, v, e]
    ring
  · change ((derivativeQueries p O t k).length : ℝ) ≤
      successRate p q v * (f (t.point 0) - low) / e ^ (q + 1) + D * |Real.log e| + F
    rw [successBudget_eq hv he.1] at hdc
    have hlog : 0 ≤ |Real.log e| := abs_nonneg _
    have hh := add_le_add (le_refl
      (successRate p q v * (f (t.point 0) - low) / e ^ (q + 1))) hrbudget
    have hfinal := hdc.trans (add_le_add hh le_rfl)
    dsimp [D, F]
    have heq : (|Real.log (H0 / ca)| + (q * (q + 1) : ℕ) * |Real.log e|) /
        |Real.log a.contraction| + 1 + 1 =
      (q * (q + 1) : ℕ) / |Real.log a.contraction| * |Real.log e| +
        (|Real.log (H0 / ca)| / |Real.log a.contraction| + 2) := by ring
    rw [add_assoc, heq] at hfinal
    dsimp [e] at hlog
    nlinarith only [hfinal, hlog]


end Optimization.ExplicitTrustRegion
