import Numlib.Optimization.TrustRegion.Inexact.MinRate.Function
import Mathlib.Analysis.Complex.ExponentialBounds
import Numlib.Optimization.HighOrder.JetCriticality
import Numlib.Analysis.Calculus.TaylorModel.Scalar
import Numlib.Optimization.TrustRegion.Inexact.Run
import Numlib.Optimization.EvaluationComplexity.OracleSimulation.Counts

/-!
# Actual Taylor criticality and acceptance along a fixed tail

The actual gradient and negative curvature at integer points give exact unit-ball Taylor
measures. Every positive unit trial has the same true objective ratio, greater than one.
-/

namespace OracleSimulation.MinRateCounterexample
open Real InexactTrustRegion EvaluationComplexity

/-- Successive trial points differ by the actual unit displacement. -/
theorem node_succ (k : ℕ) : node (k + 1) = node k + 1 := by
  simp only [node, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- The actual derivative magnitude decays by the fixed factor exp(-1) at every accepted
trial. -/
theorem magnitude_succ (k : ℕ) : magnitude (k + 1) = exp (-1) * magnitude k := by
  unfold magnitude
  rw [node_succ, neg_add, Real.exp_add]
  ring

/-- Actual derivative magnitudes decrease along the fixed sequence of trial points. -/
theorem magnitude_antitone : Antitone magnitude := by
  intro k l hkl
  unfold magnitude
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  apply Real.exp_le_exp.mpr
  dsimp [node]
  exact neg_le_neg (by exact_mod_cast (Nat.add_le_add_right hkl 3))

/-- The actual first-order measures strictly pass even when the requested first-order
accuracy is one half. -/
theorem magnitude_lt_quarter (k : ℕ) : magnitude k < 1 / 4 := by
  apply (magnitude_antitone (Nat.zero_le k)).trans_lt
  have he : (8 / 3 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have he2 : 7 < (exp 1) ^ 2 := by nlinarith
  have he3 : 16 < (exp 1) ^ 3 := by
    have hh := mul_lt_mul he he2.le (by norm_num : (0 : ℝ) < 7) (Real.exp_pos (1 : ℝ)).le
    nlinarith
  have hexp : exp 3 = (exp 1) ^ 3 := by
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 3
  unfold magnitude
  norm_num only [node, Nat.reduceAdd, Nat.cast_ofNat]
  rw [Real.exp_neg]
  apply (mul_inv_lt_iff₀ (Real.exp_pos _)).mpr
  nlinarith [Real.pi_lt_four]

/-- All actual first-order measures are below one half. -/
theorem magnitude_lt_half (k : ℕ) : magnitude k < 1 / 2 :=
  (magnitude_lt_quarter k).trans (by norm_num)

/-- The true objective at each trial point is three times its derivative magnitude. -/
theorem objective_value (k : ℕ) : objective (node k) = 3 * magnitude k := by
  simpa only [iteratedDeriv_zero, ite_true] using node_jets (j := 0) (by omega) k

/-- The actual quadratic Taylor model at every trial point has the exact concave scalar
formula. -/
theorem taylor_two (k : ℕ) (s : ℝ) :
    TaylorModel.eval objective 2 (node k) s =
      3 * magnitude k - magnitude k * s - magnitude k / 2 * s ^ 2 := by
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [node_jets (by omega), node_jets (by omega), node_jets (by omega)]
  norm_num
  ring

/-- The actual linear Taylor model at every trial point has its exact scalar formula. -/
theorem taylor_one (k : ℕ) (s : ℝ) :
    TaylorModel.eval objective 1 (node k) s = 3 * magnitude k - magnitude k * s := by
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [node_jets (by omega), node_jets (by omega)]
  norm_num
  ring

/-- The actual quadratic Taylor decrement is its exact positive-gradient and curvature
expression. -/
theorem decrement_two (k : ℕ) (s : ℝ) :
    TaylorModel.decrement objective 2 (node k) s =
      magnitude k * s + magnitude k / 2 * s ^ 2 := by
  rw [TaylorModel.decrement, taylor_two, taylor_two]
  ring

/-- The actual linear Taylor decrement is the derivative magnitude times the trial
direction. -/
theorem decrement_one (k : ℕ) (s : ℝ) :
    TaylorModel.decrement objective 1 (node k) s = magnitude k * s := by
  rw [TaylorModel.decrement, taylor_one, taylor_one]
  ring

/-- The unit-ball first-order Taylor criticality is the actual derivative magnitude. -/
theorem criticality_one (k : ℕ) :
    TaylorModel.criticality objective 1 (node k) 1 = magnitude k := by
  apply le_antisymm
  · change TaylorModel.jetCriticality (ftaylorSeries ℝ objective (node k)) _ _ ≤ _
    apply (TaylorModel.jetCriticality_le_iff _ _ zero_le_one).mpr
    intro s hs
    change TaylorModel.decrement objective 1 (node k) s ≤ _
    rw [decrement_one]
    exact mul_le_of_le_one_right (magnitude_pos k).le ((le_abs_self s).trans hs)
  · have h := TaylorModel.decrement_le_criticality objective 1 (x := node k)
      (s := (1 : ℝ)) (δ := 1) (by norm_num)
    simpa only [decrement_one, mul_one] using h

/-- The unit-ball second-order Taylor criticality is attained by the positive unit
direction and equals three halves of the derivative magnitude. -/
theorem criticality_two (k : ℕ) :
    TaylorModel.criticality objective 2 (node k) 1 = 3 / 2 * magnitude k := by
  apply le_antisymm
  · change TaylorModel.jetCriticality (ftaylorSeries ℝ objective (node k)) _ _ ≤ _
    apply (TaylorModel.jetCriticality_le_iff _ _ zero_le_one).mpr
    intro s hs
    change TaylorModel.decrement objective 2 (node k) s ≤ _
    rw [decrement_two]
    have hsa : s ≤ 1 := (le_abs_self s).trans hs
    have hs2 : s ^ 2 ≤ 1 := by
      have hh := pow_le_one₀ (abs_nonneg s) hs (n := 2)
      simpa only [sq_abs] using hh
    have h1 := mul_le_mul_of_nonneg_left hsa (magnitude_pos k).le
    have h2 := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ magnitude k / 2 from
        div_nonneg (magnitude_pos k).le (by norm_num))
    linarith
  · have h := TaylorModel.decrement_le_criticality objective 2 (x := node k)
      (s := (1 : ℝ)) (δ := 1) (by norm_num)
    rw [decrement_two] at h
    norm_num at h
    linarith

/-- The fixed true objective ratio of every actual unit trial. -/
noncomputable def ratio : ℝ := 2 * (1 - exp (-1))

/-- The actual objective ratio is greater than one, making every trial very successful. -/
theorem ratio_gt_one : 1 < ratio := by
  have he : 2 < exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
  have hi : exp (-1) < 1 / 2 := by
    rw [Real.exp_neg]
    exact (inv_lt_comm₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by norm_num; exact he)
  unfold ratio
  linarith

/-- Actual objective differences and actual quadratic Taylor decrements give the fixed
displayed acceptance ratio. -/
theorem actual_ratio (k : ℕ) :
    (objective (node k) - objective (node k + 1)) /
      TaylorModel.decrement objective 2 (node k) 1 = ratio := by
  rw [← node_succ, objective_value, objective_value, decrement_two, magnitude_succ]
  unfold ratio
  field_simp [(magnitude_pos k).ne']
  ring

end OracleSimulation.MinRateCounterexample
