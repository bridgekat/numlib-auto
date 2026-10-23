import Numlib.Optimization.Regularization.Inexact.RunStepPowers
import Numlib.Optimization.TrustRegion.Inexact.Complexity

/-!
# Actual objective decrease of accepted inexact regularization trials

The computed prediction is positive and dominates the regularization penalty.
The true objective ratio and accepted point update therefore give actual
objective decrease. Rejected trials and accuracy-only iterations preserve the
objective, with no decrease condition placed in the execution data.
-/

namespace InexactRegularization
open InexactTrustRegion EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Every actual accepted trial decreases the true objective by at least its
acceptance fraction times the minimum regularization penalty. -/
theorem function_decrease_ge_penalty (h : Run f P ε D N) {k : ℕ} (hk : k < N)
    (ht : k ∈ D.trials) (haccepted : P.eta1 ≤ D.ratio k) :
    P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) * ‖D.step k‖ ^ (p + 1) ≤
      f (D.point k) - f (D.point (k + 1)) := by
  have htrace := h.toModelTrace
  have hden := htrace.toOracleTrace.denominator_pos hk ht
  have hpen := (penalty_lt_decrement (htrace.reference_improvement k hk ht)
    (htrace.comparison k hk ht)).le
  have hratio := haccepted
  rw [h.ratio k hk ht] at hratio
  have hacc := (le_div_iff₀ hden).mp hratio
  have hmin := h.updates.min_le hk.le
  have hη := P.eta1_pos
  have hp : 0 ≤ ‖D.step k‖ ^ (p + 1) := by positivity
  have hscale := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmin
      (Nat.cast_nonneg (p + 1).factorial)) hp) hη.le
  have hprediction := mul_le_mul_of_nonneg_left hpen hη.le
  rw [h.point_trial k hk ht, ite_eq_left haccepted]
  convert hscale.trans (hprediction.trans hacc) using 1
  ring

/-- Every iteration outside the actual accepted trial set leaves the objective unchanged. -/
theorem objective_eq_of_not_successful (h : Run f P ε D N) {k : ℕ} (hk : k < N)
    (hnot : k ∉ successfulSet D.trials D.ratio P.eta1) :
    f (D.point (k + 1)) = f (D.point k) := by
  by_cases ht : k ∈ D.trials
  · rw [h.point_trial k hk ht, ite_eq_right (fun ha => hnot ⟨ht, ha⟩)]
  · rw [h.point_inactive k hk ht]

end Run
end InexactRegularization
