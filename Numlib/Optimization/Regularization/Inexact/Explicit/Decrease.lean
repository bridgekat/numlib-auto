import Numlib.Optimization.Regularization.Inexact.Explicit.Run
import Numlib.Optimization.TrustRegion.Inexact.FunctionValues

/-!
# True objective decrease of accepted EDA regularization trials

Both approximate function errors are bounded by the actual computed decrement.
The quarter-margin restriction then leaves half the acceptance factor in true
objective decrease. Actual model comparison and parameter updates give its
factorial-normalized norm-power floor.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- An accepted approximate-objective ratio gives half its acceptance factor
as true decrease, after both actual relative objective errors are accounted for. -/
theorem function_decrease_ge_computed (h : Run f P ε D N) {k : ℕ} (hk : k < N)
    (ht : k ∈ D.trials) (haccepted : P.eta1 ≤ D.ratio k) :
    P.eta1 / 2 * TaylorModel.jetDecrement (D.jet k) p (D.step k) ≤
      f (D.point k) - f (D.point (k + 1)) := by
  have hd := h.toFunctionTrace.toOracleTrace.denominator_pos hk ht
  have ha := haccepted
  rw [h.ratio k hk ht] at ha
  have hh := true_decrease_of_inexact_values hd P.function_acceptance_margin
    (D.functionStart k) (D.functionTrial k)
    ((h.error_initial k hk ht).trans (h.relative_request k hk ht))
    ((h.error_trial k hk ht).trans (h.relative_request k hk ht)) ha
  simpa only [h.point_trial k hk ht, ite_eq_left haccepted] using hh

/-- Actual reference improvement and model comparison turn accepted true
function decrease into its parameter-floor norm-power bound. -/
theorem function_decrease_ge_penalty (h : Run f P ε D N) {k : ℕ} (hk : k < N)
    (ht : k ∈ D.trials) (haccepted : P.eta1 ≤ D.ratio k) :
    P.eta1 * P.sigmaMin / (2 * ((p + 1).factorial : ℝ)) * ‖D.step k‖ ^ (p + 1) ≤
      f (D.point k) - f (D.point (k + 1)) := by
  have hm := (penalty_lt_decrement
    (h.toFunctionTrace.toOracleTrace.reference_improvement k hk ht)
    (h.step_two k hk ((h.trial_rule k hk).mp ht).1).comparison).le
  have hσ := h.updates.min_le hk.le
  apply le_trans _ (h.function_decrease_ge_computed hk ht haccepted)
  have hcoef : 0 ≤ P.eta1 / 2 := (half_pos P.eta1_pos).le
  have hh := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hσ (Nat.cast_nonneg _)) (by positivity)).trans hm) hcoef
  convert hh using 1
  ring

/-- Every inactive or rejected iteration leaves the actual objective point
unchanged; only accepted actual trials consume objective decrease. -/
theorem objective_eq_of_not_successful (h : Run f P ε D N) {k : ℕ} (hk : k < N)
    (hnot : ¬(k ∈ D.trials ∧ P.eta1 ≤ D.ratio k)) :
    f (D.point (k + 1)) = f (D.point k) := by
  by_cases ht : k ∈ D.trials
  · have ha : ¬P.eta1 ≤ D.ratio k := fun ha => hnot ⟨ht, ha⟩
    rw [h.point_trial k hk ht, ite_eq_right ha]
  · rw [h.point_inactive k hk ht]

end Run
end InexactRegularization.Explicit
