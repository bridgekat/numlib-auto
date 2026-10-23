import Numlib.Optimization.MeasureDomination.Blocks
import Numlib.Analysis.SpecialFunctions.Pow.SuperlinearBudget

/-!
# Full double-logarithmic gap and measure complexity

The genuine implicit orbit gives superlinear gap budgets. The exact printed
measure expression uses log|log κν + ν log ε|; a proved comparison also gives
ordinary double-logarithmic order. Fixed positive cutoffs keep every displayed
logarithm admissible, and all initialized cost constants precede the accuracy.
-/

open Set Filter Topology
namespace MeasureDomination
variable {E : Type*} {f ψ : E → ℝ} {fstar μ κψ ν κν κR κA : ℝ}
  {x : ℕ → E} {S : Set ℕ}

/-- A fixed positive threshold makes both logarithmic arguments admissible at every smaller
  accuracy. -/
theorem exists_log_cutoff (a b : ℝ) (hb : 0 < b) :
    ∃ εmax > 0, εmax ≤ Real.exp (-1) ∧ ∀ ε : ℝ, 0 < ε → ε ≤ εmax →
      1 ≤ |Real.log ε| ∧ 1 ≤ |a + b * Real.log ε| := by
  refine ⟨min (Real.exp (-1)) (Real.exp ((-1 - |a|) / b)),
    lt_min (Real.exp_pos _) (Real.exp_pos _), min_le_left _ _, ?_⟩
  intro ε hε hmax
  have hlog₁ := Real.log_le_log hε (hmax.trans (min_le_left _ _))
  have hlog₂ := Real.log_le_log hε (hmax.trans (min_le_right _ _))
  rw [Real.log_exp] at hlog₁ hlog₂
  have hm := mul_le_mul_of_nonneg_left hlog₂ hb.le
  have he : b * ((-1 - |a|) / b) = -1 - |a| := by field_simp
  rw [he] at hm
  constructor
  · linarith [neg_le_abs (Real.log ε)]
  · linarith [le_abs_self a, neg_le_abs (a + b * Real.log ε)]

/-- Exact source double-logarithmic costs on an explicit fixed small-accuracy interval,
with initialized counters and a nonzero inner logarithmic argument. -/
def DoubleLogarithmicCost (a b : ℝ) (target : ℕ → ℝ) (S : Set ℕ) : Prop :=
  ∃ εmax > 0, εmax ≤ Real.exp (-1) ∧
    ∃ B > 0, ∃ C > 0, ∃ D > 0, ∃ F > 0, ∀ ε : ℝ, 0 < ε → ε ≤ εmax →
      1 ≤ |a + b * Real.log ε| ∧
      ∃ K : ℕ, target K ≤ ε ∧ (∀ k < K, ε < target k) ∧
        ((K + 1 : ℕ) : ℝ) ≤ B * Real.log |a + b * Real.log ε| + C ∧
        ((EvaluationComplexity.successfulIterations S K).card + 1 : ℕ) ≤
          D * Real.log |a + b * Real.log ε| + F

/-- The displayed affine-log cost has ordinary double-logarithmic order for positive log slope. -/
theorem DoubleLogarithmicCost.to_plain {a b : ℝ} {target : ℕ → ℝ}
    (h : DoubleLogarithmicCost a b target S) (hb : 0 < b) :
    DoubleLogarithmicCost 0 1 target S := by
  obtain ⟨εmax, hmax, hmax1, B, hB, C, hC, D, hD, F, hF, h⟩ := h
  let L := max 1 (|a| + b)
  have hL : 0 < L := zero_lt_one.trans_le (le_max_left _ _)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (le_max_left _ _)
  refine ⟨εmax, hmax, hmax1, B, hB, C + B * Real.log L, by positivity,
    D, hD, F + D * Real.log L, by positivity, ?_⟩
  intro ε hε hεmax
  obtain ⟨hdom, K, hs, hfirst, hfunc, hderiv⟩ := h ε hε hεmax
  have hlog := Real.log_le_log hε (hεmax.trans hmax1)
  rw [Real.log_exp] at hlog
  have habs : 1 ≤ |Real.log ε| := by linarith [neg_le_abs (Real.log ε)]
  have haff : |a + b * Real.log ε| ≤ L * |Real.log ε| := by
    have hh : |a + b * Real.log ε| ≤ |a| + b * |Real.log ε| := by
      simpa only [abs_mul, abs_of_pos hb] using abs_add_le a (b * Real.log ε)
    have hm := mul_le_mul_of_nonneg_right (le_max_right 1 (|a| + b)) (abs_nonneg (Real.log ε))
    nlinarith [abs_nonneg a]
  have hll := Real.log_le_log (zero_lt_one.trans_le hdom) haff
  rw [Real.log_mul hL.ne' (zero_lt_one.trans_le habs).ne'] at hll
  refine ⟨by simpa only [one_mul, zero_add] using habs, K, hs, hfirst, ?_, ?_⟩
  · simp only [one_mul, zero_add]
    have hh := mul_le_mul_of_nonneg_left hll hB.le
    nlinarith
  · simp only [one_mul, zero_add]
    have hh := mul_le_mul_of_nonneg_left hll hD.le
    nlinarith

/-- Below the domination level actual gap targets have the source double-logarithmic complexity. -/
theorem ARRun.gap_doublelog_cost (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν < μ) :
    DoubleLogarithmicCost 0 1 (fun k => gap f fstar (x k)) S := by
  have hc : 0 < κν / κψ ^ (ν / μ) :=
    div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have ht : 0 < ν / μ := div_pos (zero_lt_one.trans_le hr.exponent_ge_one)
    (zero_lt_one.trans_le hd.level_ge_one)
  have ht1 : ν / μ < 1 := (div_lt_one (zero_lt_one.trans_le hd.level_ge_one)).mpr hνμ
  obtain ⟨A, hA, B, hB, hbudget⟩ := ImplicitGap.exists_superlinear_budget hc ht ht1
    (hd.gap_nonneg (x 0))
  obtain ⟨εmax, hmax, hmax1, hcut⟩ := exists_log_cutoff 0 1 zero_lt_one
  have hκR : 0 < κR := zero_lt_one.trans_le hr.density_factor
  have hκA : 0 ≤ κA := hr.density_additive
  refine ⟨εmax, hmax, hmax1, κR * A, by positivity, κR * B + κA + 1, by positivity,
    A, hA, B + 1, by positivity, ?_⟩
  intro ε hε hεmax
  have hlog := (hcut ε hε hεmax).1
  obtain ⟨M, htarg, hM⟩ := hbudget ε hε hlog
  obtain ⟨K, hs, hfirst, hcard, hK⟩ := hr.first_gap_budget hd hε htarg
  refine ⟨by simpa using hlog, K, hs, hfirst, ?_, ?_⟩
  · simp only [one_mul, zero_add]
    push_cast
    calc (K : ℝ) + 1 ≤ κR * M + κA + 1 := by linarith
         _ ≤ κR * (A * Real.log |Real.log ε| + B) + κA + 1 := by gcongr
         _ = _ := by ring
  · simp only [one_mul, zero_add]
    push_cast
    have hh : ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤ M :=
      by exact_mod_cast hcard
    linarith

/-- A further genuine accepted step gives precisely the source affine-log measure cost. -/
theorem ARRun.measure_doublelog_cost (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν < μ) :
    DoubleLogarithmicCost (Real.log κν) ν (fun k => ψ (x k)) S := by
  have hc : 0 < κν / κψ ^ (ν / μ) :=
    div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have ht : 0 < ν / μ := div_pos (zero_lt_one.trans_le hr.exponent_ge_one)
    (zero_lt_one.trans_le hd.level_ge_one)
  have ht1 : ν / μ < 1 := (div_lt_one (zero_lt_one.trans_le hd.level_ge_one)).mpr hνμ
  obtain ⟨A, hA, B, hB, hbudget⟩ := ImplicitGap.exists_superlinear_budget hc ht ht1
    (hd.gap_nonneg (x 0))
  have hν : 0 < ν := zero_lt_one.trans_le hr.exponent_ge_one
  obtain ⟨εmax, hmax, hmax1, hcut⟩ := exists_log_cutoff (Real.log κν) ν hν
  have hκR : 0 < κR := zero_lt_one.trans_le hr.density_factor
  have hκA : 0 ≤ κA := hr.density_additive
  refine ⟨εmax, hmax, hmax1, κR * A, by positivity,
    κR * (B + 1) + κA + 1, by positivity, A, hA, B + 2, by positivity, ?_⟩
  intro ε hε hεmax
  have hdom := (hcut ε hε hεmax).2
  have hδ : 0 < κν * ε ^ ν := mul_pos hr.coefficient_pos (Real.rpow_pos_of_pos hε ν)
  have he : Real.log (κν * ε ^ ν) = Real.log κν + ν * Real.log ε := by
    rw [Real.log_mul hr.coefficient_pos.ne' (Real.rpow_pos_of_pos hε ν).ne', Real.log_rpow hε]
  obtain ⟨M, htarg, hM⟩ := hbudget (κν * ε ^ ν) hδ (by rwa [he])
  rw [he] at hM
  obtain ⟨K, hs, hfirst, hcard, hK⟩ := hr.first_measure_budget hd hε htarg
  refine ⟨hdom, K, hs, hfirst, ?_, ?_⟩
  · push_cast at hK ⊢
    calc (K : ℝ) + 1 ≤ κR * (M + 1) + κA + 1 := by linarith
         _ ≤ κR * ((A * Real.log |Real.log κν + ν * Real.log ε| + B) + 1) + κA + 1
           := by gcongr
         _ = _ := by ring
  · push_cast
    have hh : ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤ M + 1 :=
      by exact_mod_cast hcard
    linarith
end MeasureDomination
