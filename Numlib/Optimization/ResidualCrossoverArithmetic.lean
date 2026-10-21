import Numlib.Optimization.ResidualLeastSquares
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A crossing of active residual-cost orders

Two residual bands can have different dominant derivative orders. The sum of their maxima
need not fit the maximum of the separately summed geometric bounds. All data below are
fixed rational parameters, with strict primal and dual tolerances.
-/

noncomputable section
namespace Optimization.ResidualCrossover
open ResidualLeastSquares

/-- The fixed outer contraction factor. -/
def beta : ℝ := 4 / 5
/-- The fixed primal stopping tolerance. -/
def primal : ℝ := 799 / 1000
/-- The fixed two active dual tolerances. -/
def epsilon (j : ℕ) : ℝ := if j = 1 then 99 / 500 else 999 / 1000
/-- Distinct fixed exponents for the two derivative orders. -/
def exponent (j : ℕ) : ℝ := if j = 1 then 4 else 20
/-- The positive intermediate residual. -/
def middleResidual : ℝ := 7999 / 10000
/-- The positive residual at the terminal output. -/
def finalResidual : ℝ := 16 / 25
/-- The exact first derivative of the squared residual at the intermediate output. -/
def middleGradient : ℝ := 1583901 / 10000000
/-- The actual residual-scaled input vector to a call starting at residual `R`. -/
def inputTolerance (R : ℝ) (j : ℕ) : ℝ := beta * R * epsilon j

/-- The scalar data satisfy every strict domain condition of the two-call wrapper. -/
theorem parameter_bounds : 0 < beta ∧ beta < 1 ∧ 0 < primal ∧ primal < 1 ∧
    primal < middleResidual ∧ middleResidual < beta ∧ finalResidual < primal ∧
    ∀ j ∈ Finset.Icc 1 2, 0 < epsilon j ∧ epsilon j < 1 ∧ 1 < exponent j := by
  refine ⟨by norm_num [beta], by norm_num [beta], by norm_num [primal],
    by norm_num [primal], by norm_num [primal, middleResidual],
    by norm_num [middleResidual, beta], by norm_num [finalResidual, primal], ?_⟩
  intro j hj
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  interval_cases j <;> norm_num [epsilon, exponent]

/-- The intermediate first gap passes the first call's input tolerance and fails the
outer residual-scaled test at the returned residual. -/
theorem middle_gap_bounds : middleResidual * epsilon 1 < middleGradient ∧
    middleGradient ≤ inputTolerance 1 1 ∧
    middleGradient ≤ inputTolerance 1 2 / 2 := by
  norm_num [middleResidual, middleGradient, epsilon, inputTolerance, beta]

/-- The first call can genuinely pay 794 evaluations in either channel under its order-one
weight. No free calls or post-hoc increase of a coefficient are used. -/
theorem first_cost_le : (794 : ℝ) ≤
    (1 / 2 : ℝ) * toleranceWeight 2 (inputTolerance 1) exponent := by
  have hw := le_toleranceWeight (inputTolerance 1) exponent
    (by norm_num : 1 ∈ Finset.Icc 1 2)
  have hnum : (1588 : ℝ) ≤ inputTolerance 1 1 ^ (-exponent 1) := by
    norm_num [inputTolerance, beta, epsilon, exponent, Real.rpow_neg, Real.rpow_natCast]
  linarith

/-- The second call can pay 2461 evaluations in either channel under its order-two weight.
Its dominant order differs from the first call's. -/
theorem second_cost_le : (2461 : ℝ) ≤
    middleResidual ^ 2 / 2 * toleranceWeight 2 (inputTolerance middleResidual) exponent := by
  have hw := le_toleranceWeight (inputTolerance middleResidual) exponent
    (by norm_num : 2 ∈ Finset.Icc 1 2)
  have hnum : (2461 : ℝ) ≤ middleResidual ^ 2 / 2 *
      inputTolerance middleResidual 2 ^ (-exponent 2) := by
    norm_num [inputTolerance, beta, epsilon, exponent, middleResidual,
      Real.rpow_neg, Real.rpow_natCast]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ middleResidual ^ 2 / 2)
  exact hnum.trans hm

/-- The exact printed geometric prefactor, before any initialization query. -/
def printedBound : ℝ := 1 / 2 * orderMaximum 2 (fun j =>
  beta ^ (1 - 2 * exponent j) / (beta ^ (1 - exponent j) - 1) *
    primal ^ (1 - exponent j) * epsilon j ^ (-exponent j))

/-- Each separately summed order lies below 6382, while the actual two-call function
cost sum is 3255. The printed maximum is therefore too small even without initialization. -/
theorem printedBound_lt_inner_cost : printedBound < 794 + 2461 := by
  have hb : orderMaximum 2 (fun j =>
      beta ^ (1 - 2 * exponent j) / (beta ^ (1 - exponent j) - 1) *
        primal ^ (1 - exponent j) * epsilon j ^ (-exponent j)) ≤ 6382 := by
    apply orderMaximum_le (by norm_num)
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    interval_cases j <;>
      norm_num [beta, exponent, primal, epsilon, Real.rpow_neg, Real.rpow_natCast]
  unfold printedBound
  linarith


/-- The first exact cubic Taylor-model change in scalar coordinates. -/
def firstCubic (u : ℝ) : ℝ := -u + u ^ 2 / 4 + |u| ^ 3 / 6

/-- The second exact cubic Taylor-model change with its warm-start parameter. -/
def secondCubic (u : ℝ) : ℝ := middleGradient * u + middleGradient / 12 * |u| ^ 3

/-- The first actual cubic model has a global minimizer at the unit step. -/
theorem firstCubic_min (u : ℝ) : firstCubic 1 ≤ firstCubic u := by
  by_cases hu : 0 ≤ u
  · have hp := mul_nonneg (sq_nonneg (u - 1)) (by linarith : 0 ≤ 2 * u + 7)
    simp only [firstCubic, abs_of_nonneg hu, abs_one]
    nlinarith
  · have hu' := le_of_not_ge hu
    have hn := pow_nonneg (abs_nonneg u) 3
    simp only [firstCubic, abs_one]
    nlinarith [sq_nonneg u]

/-- The second actual cubic model has a global minimizer at the step minus two. -/
theorem secondCubic_min (u : ℝ) : secondCubic (-2) ≤ secondCubic u := by
  have hg : 0 < middleGradient := by norm_num [middleGradient]
  by_cases hu : u ≤ 0
  · have hp := mul_nonneg (sq_nonneg (u + 2)) (by linarith : 0 ≤ 4 - u)
    have hs : (-2 : ℝ) + |(-2 : ℝ)| ^ 3 / 12 ≤ u + |u| ^ 3 / 12 := by
      rw [abs_of_nonpos hu]
      norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hs hg.le
    unfold secondCubic
    nlinarith
  · have hu' := le_of_not_ge hu
    have hn := pow_nonneg (abs_nonneg u) 3
    unfold secondCubic
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [mul_nonneg hg.le hu', mul_nonneg hg.le hn]

/-- Both actual unregularized-prediction ratios are very successful, and their fixed
warm-start parameters obey the prescribed very-successful update intervals. -/
theorem acceptance_and_updates :
    (1 / 5 : ℝ) ≤ (1 / 2 - middleResidual ^ 2 / 2) / (3 / 4) ∧
    (1 / 5 : ℝ) ≤ (middleResidual ^ 2 / 2 - finalResidual ^ 2 / 2) /
      (2 * middleGradient) ∧
    max (1 / 1000 : ℝ) (1 / 100) ≤ middleGradient / 2 ∧
    middleGradient / 2 ≤ 1 ∧
    max (1 / 1000 : ℝ) (middleGradient / 200) ≤ middleGradient / 2 := by
  norm_num [middleResidual, finalResidual, middleGradient]

/-- Neither starting point has passed its input first-order stopping test. -/
theorem starting_tests_fail : inputTolerance 1 1 < 1 ∧
    inputTolerance middleResidual 1 < middleGradient := by
  norm_num [inputTolerance, beta, middleResidual, middleGradient, epsilon]

/-- All requested input tolerances for both calls satisfy the strict source domain. -/
theorem input_tolerance_bounds {R : ℝ} (hR : R = 1 ∨ R = middleResidual)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 2) :
    0 < inputTolerance R j ∧ inputTolerance R j < 1 := by
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  rcases hR with rfl | rfl <;> interval_cases j <;>
    norm_num [inputTolerance, beta, middleResidual, epsilon]

end Optimization.ResidualCrossover
