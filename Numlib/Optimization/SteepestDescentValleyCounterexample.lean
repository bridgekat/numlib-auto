import Numlib.Optimization.SteepestDescentValleyScalar
import Numlib.Optimization.ExactLineSearch

/-!
# A finite valley step is not a global ray minimizer

The actual valley with tolerance one tenth and one hundred cells has a prescribed first
successor which fails global exact line minimization. A later point on its first
negative-gradient ray has a strictly smaller actual objective value. This separates the
source's first-local-minimum argument from the global `LineSearch.IsExact` interface.
No assertion about first local minima is needed for this counterexample.
-/

noncomputable section
open Set

namespace Optimization.SteepestDescentValley

/-- Exact reciprocal-square finite parameters for the global-ray counterexample. -/
def counterexampleParameters : Parameters where
  eps := 1 / 10
  count := 100
  eps_pos := by norm_num
  eps_le_one := by norm_num
  count_pos := by norm_num
  scaled_count_lower := by norm_num
  scaled_count_upper := by norm_num

set_option maxHeartbeats 800000 in
-- Evaluate the one hundred exact rational summands.
/-- Exact horizontal endpoint of the one-hundred-cell chain. -/
theorem counterexample_nodeX : nodeX counterexampleParameters 100 = 301 / 20 := by
  norm_num [nodeX, cellLength, counterexampleParameters, Finset.sum_range_succ]

set_option maxHeartbeats 800000 in
-- Evaluate the one hundred exact alternating rational summands.
/-- Exact vertical endpoint of the same chain. -/
theorem counterexample_nodeY : nodeY counterexampleParameters 100 = 1 / 20 := by
  norm_num [nodeY, cellSign, cellLength, counterexampleParameters, Finset.sum_range_succ]

set_option maxHeartbeats 800000 in
-- Evaluate the one hundred exact squared rational summands.
/-- Exact terminal scalar objective value, from the actual finite sum of squared lengths. -/
theorem counterexample_nodeValue : nodeValue counterexampleParameters 100 = 33033 / 20000 := by
  norm_num [nodeValue, cellLength, counterexampleParameters, Finset.sum_range_succ]

/-- The first ray meets an exterior plateau far later in the same finite construction. -/
def counterexampleTrial : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![301 / 20, 301 / 20]

/-- Exact objective value at the first prescribed successor. -/
theorem counterexample_first_value :
    euclideanObjective counterexampleParameters (nodePoint counterexampleParameters 1) =
      (15879601 / 4000000) / Real.sqrt 2 := by
  have hk : 1 ≤ counterexampleParameters.count := by norm_num [counterexampleParameters]
  have hv := scalarObjective_node_jets counterexampleParameters hk (j := 0) (by omega)
  rw [euclideanObjective, euclideanMovingProfile]
  simp only [nodePoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    scalarWidth_node _ hk, scalarMidpoint_node _ hk, iteratedDeriv_zero] at *
  rw [hv]
  have he : nodeY counterexampleParameters 1 - nodeMidpoint counterexampleParameters 1 =
      cellLength counterexampleParameters 1 / 2 := by
    norm_num [nodeMidpoint, nodeY, cellSign, cellLength, counterexampleParameters,
      Finset.sum_range_succ]
  rw [he, profile_core (by
    have := (cellLength_pos counterexampleParameters hk).le
    linarith) le_rfl]
  norm_num [objectiveJet, nodeValue, cellLength, counterexampleParameters, Finset.sum_range_succ]

/-- Exact objective value at the later trial point on the first ray. -/
theorem counterexample_trial_value :
    euclideanObjective counterexampleParameters counterexampleTrial =
      (34633 / 20000) / Real.sqrt 2 := by
  have hk : 100 ≤ counterexampleParameters.count := by norm_num [counterexampleParameters]
  have hv := scalarObjective_node_jets counterexampleParameters hk (j := 0) (by omega)
  have hw := scalarWidth_node counterexampleParameters hk
  have hm := scalarMidpoint_node counterexampleParameters hk
  change scalarObjective counterexampleParameters (nodeX counterexampleParameters 100) =
    nodeValue counterexampleParameters 100 at hv
  rw [counterexample_nodeX] at hv hw hm
  have hmval : nodeMidpoint counterexampleParameters 100 = 1 / 10 := by
    rw [nodeMidpoint, counterexample_nodeY]
    norm_num [cellSign, cellLength, counterexampleParameters]
  rw [hmval] at hm
  have hlen : cellLength counterexampleParameters 100 = 1 / 10 := by
    norm_num [cellLength, counterexampleParameters]
  rw [hlen] at hw
  rw [euclideanObjective, euclideanMovingProfile]
  change (scalarObjective counterexampleParameters (301 / 20) +
    profile (scalarWidth counterexampleParameters (301 / 20))
      (301 / 20 - scalarMidpoint counterexampleParameters (301 / 20))) / Real.sqrt 2 = _
  rw [hv, hw, hm, profile_upper_plateau (by norm_num) (by norm_num), counterexample_nodeValue]
  norm_num

/-- The later point has strictly smaller actual objective value than the first successor. -/
theorem counterexample_trial_lt_first :
    euclideanObjective counterexampleParameters counterexampleTrial <
      euclideanObjective counterexampleParameters (nodePoint counterexampleParameters 1) := by
  rw [counterexample_trial_value, counterexample_first_value]
  exact (div_lt_div_iff_of_pos_right (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
    (by norm_num)

/-- The later trial is on the initial actual negative-gradient ray at a positive parameter. -/
theorem counterexample_trial_on_ray :
    nodePoint counterexampleParameters 0 + ((301 / 4 : ℝ) * Real.sqrt 2) •
      (-gradient (euclideanObjective counterexampleParameters)
        (nodePoint counterexampleParameters 0)) =
        counterexampleTrial := by
  rw [gradient_euclideanObjective_node _ (by norm_num [counterexampleParameters])]
  ext i
  fin_cases i <;>
    simp [nodePoint, nodeGradient, counterexampleTrial, nodeX, nodeY, cellSign, cellLength,
      counterexampleParameters, smul_eq_mul]
  all_goals field_simp
  all_goals ring

/-- The actual prescribed first step fails global exact ray minimization. This is a
machine-checked counterexample for the complete finite objective, not a scalar gap analogy. -/
theorem counterexample_not_global_exact :
    ¬ LineSearch.IsExact (euclideanObjective counterexampleParameters)
      (nodePoint counterexampleParameters 0)
      (-gradient (euclideanObjective counterexampleParameters)
        (nodePoint counterexampleParameters 0))
      (Real.sqrt 2) := by
  intro h
  have hh := h.le_trial (a := (301 / 4 : ℝ) * Real.sqrt 2) (by positivity)
  rw [counterexample_trial_on_ray] at hh
  have hfirst := nodePoint_succ counterexampleParameters (k := 0)
    (by norm_num [counterexampleParameters])
  have he : nodePoint counterexampleParameters 0 + Real.sqrt 2 •
      (-gradient (euclideanObjective counterexampleParameters)
        (nodePoint counterexampleParameters 0)) =
        nodePoint counterexampleParameters 1 := by
    simpa only [smul_neg, ← sub_eq_add_neg] using hfirst.symm
  rw [he] at hh
  exact (not_le_of_gt counterexample_trial_lt_first) hh

end Optimization.SteepestDescentValley
