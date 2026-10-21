import NumlibSurface.CartisGouldToint.Chapter14.Section03
import Numlib.Optimization.ResidualCrossoverRun

/-!
# Chapter 14, Section 3: a crossing of active INNER cost orders

The nonspecific INNER contract permits different active orders to dominate different calls.
A complete polynomial least-squares example satisfies every per-call contract but exceeds
the single maximum of geometric coefficients printed in Theorem 14.3.4. The selected INNER
has genuine exact cubic-model steps and legal accepted parameter updates, with explicitly
paid repeated queries before either step. It is an extension of a regularization method,
not the literal cached query schedule of Algorithm 12.2.2. No neighboring theorem or
existential asymptotic complexity result is inferred false.
-/

noncomputable section
namespace CartisGouldToint.Chapter14.Section03.LENCrossover
open Set Metric Optimization ResidualLeastSquares
open ResidualCrossoverJets ResidualCrossover

/-- The exact function-channel budget printed in Theorem 14.3.4, specialized to the fixed
coefficient one, the actual initial residual, and the two fixed exponents and tolerances. -/
def printedFunctionBudget : ℝ :=
  (1 / 2 : ℝ) * ‖residual (trace.point 0)‖ * orderMaximum 2 (fun j =>
    beta ^ (1 - 2 * exponent j) / (beta ^ (1 - exponent j) - 1) *
      primal ^ (1 - exponent j) * epsilon j ^ (-exponent j))

/-- The actual initial residual is one, so the source budget is exactly the checked
scalar geometric expression, with no omitted initialization or rounding adjustment. -/
theorem printedFunctionBudget_eq : printedFunctionBudget = printedBound := by
  change (1 / 2 : ℝ) * ‖residual (point 0)‖ * _ = _
  rw [residual_norm_zero, mul_one]
  rfl

/-- A complete literal LENq-SC run refutes the printed geometric prefactor. The actual
objective is a polynomial squared residual on a closed convex Euclidean simple set, with
all source bounded and anchored-Lipschitz jets on a full open convex neighborhood. Both
complete paid INNER calls use the same exponents and coefficients. The genuine first
stopping index is two, and its actual value-query total exceeds the printed bound even
before the initial residual query is added. -/
theorem literal_len_geometric_prefactor_counterexample :
    ∃ L B : ℕ → ℝ,
      IsClosed feasible ∧ feasible.Nonempty ∧ Convex ℝ feasible ∧
      Section02.SmoothBoundedJetsOnLevelSet objective feasible (point 0) 2 false
        neighborhood L B ∧
      algorithm_14_3_1 feasible residual 2 primal beta epsilon exponent
        (fun _ => 1) innerStep innerTerminal trace ∧
      Stops feasible residual 2 primal epsilon trace 2 ∧
      (∀ k < 2, ¬Stops feasible residual 2 primal epsilon trace k) ∧
      printedFunctionBudget < (evaluations trace .function 2 : ℝ) ∧
      printedFunctionBudget < (totalEvaluations trace .function 2 : ℝ) := by
  obtain ⟨L, B, hL, hB, hj⟩ := exists_anchoredBoundedJets_sublevel (point 0)
  have hs : Section02.SmoothBoundedJetsOnLevelSet objective feasible (point 0) 2 false
      neighborhood L B := {
    toHasAnchoredBoundedJets := hj
    initial_feasible := by simpa only [point_zero] using zero_mem_feasible
    feasible_subset := closedBall_subset_ball (by norm_num : (3 : ℝ) < 4)
    lipschitz_one_le := fun j _ _ => hL j
    bound_one_le := fun j _ _ => hB j }
  refine ⟨L, B, isClosed_feasible, ⟨0, zero_mem_feasible⟩, convex_feasible, hs,
    ⟨execution, ?_, ?_⟩, first_stop.1, first_stop.2, ?_, ?_⟩
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    interval_cases j <;> norm_num [epsilon]
  · change 0 < beta ∧ beta < min 1 (‖residual (point 0)‖)⁻¹
    rw [residual_norm_zero]
    norm_num [beta]
  · rw [printedFunctionBudget_eq]
    exact inner_cost_violation
  · rw [printedFunctionBudget_eq]
    exact total_cost_violation

end CartisGouldToint.Chapter14.Section03.LENCrossover
