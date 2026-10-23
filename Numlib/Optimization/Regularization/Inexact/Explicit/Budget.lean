import Numlib.Optimization.Regularization.Inexact.Explicit.Decrease
import Numlib.Optimization.Regularization.Inexact.Explicit.Constants
import Numlib.Optimization.TrustRegion.Inexact.Complexity

/-!
# Successful-trial objective budgets for actual inexact regularization

The exact finite minimum of the positive order coefficients gives one common
objective decrease at each successful trial whose next point is not yet
approximately optimal. A finite lower objective bound then bounds successful
trials, with one extra trial allowed to first attain the target.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Some order's fixed coefficient times its fractional accuracy power bounds
an actual successful step from below. -/
theorem exists_root_step_lower_of_cap (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    (hmargin : P.theta < P.zeta / 2)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) (haccepted : P.eta1 ≤ D.ratio k)
    (hnot : ¬StopsAt P ε D (k + 1)) :
    ∃ a, rootStepCoefficient P L M S (modelOrder a) *
      (ε a) ^ rootStepExponent p q (modelOrder a) ≤ ‖D.step k‖ := by
  obtain ⟨_, _, a, ha⟩ := h.step_lower_of_cap hf hmargin hL hM hlip hparam hjet
    hk ht haccepted hnot
  refine ⟨a, ?_⟩
  by_cases hq : q ≤ 2
  · simpa only [rootStepCoefficient, rootStepExponent, ite_eq_left hq] using ha
  · simpa only [rootStepCoefficient, rootStepExponent, ite_eq_right hq] using ha

/-- Every actual successful trial before next-iterate approximate optimality
consumes the fixed common coefficient times the source minimum accuracy power. -/
theorem function_decrease_uniform (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    (hmargin : P.theta < P.zeta / 2)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) (haccepted : P.eta1 ≤ D.ratio k)
    (hnot : ¬StopsAt P ε D (k + 1)) :
    commonDecreaseCoefficient P L M S * accuracyFactor P.toSettings ε ≤
      f (D.point k) - f (D.point (k + 1)) := by
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  obtain ⟨a, ha⟩ := h.exists_root_step_lower_of_cap hf hmargin hL hM hlip hparam hjet
    hk ht haccepted hnot
  have hroot := rootStepCoefficient_pos P hmargin hL hM hS (modelOrder a)
  have hpow := pow_lower_of_root_step (n := p + 1) hroot.le (h.accuracy_pos a).le ha
  have hbase : 0 ≤ P.eta1 * P.sigmaMin / (2 * ((p + 1).factorial : ℝ)) := by
    exact div_nonneg (mul_nonneg P.eta1_pos.le P.sigmaMin_pos.le) (by positivity)
  have hscale := mul_le_mul_of_nonneg_left hpow hbase
  have hcommon := mul_le_mul (commonDecreaseCoefficient_le P L M S a)
    (accuracyFactor_le P.toSettings ε a) (accuracyFactor_pos P.toSettings h.accuracy_pos).le
    (show 0 ≤ orderDecreaseCoefficient P L M S a from by
      unfold orderDecreaseCoefficient
      positivity)
  have hdecrease := h.function_decrease_ge_penalty hk ht haccepted
  apply hcommon.trans
  apply le_trans _ hdecrease
  convert hscale using 1
  unfold orderDecreaseCoefficient evaluationExponent
  ring

/-- A lower objective bound controls all successful trials in a prefix whose
endpoint also precedes the true approximate-optimality target. -/
theorem successful_card_le_of_no_target_endpoint (h : Run f P ε D N)
    (hf : ContDiff ℝ p f) (hmargin : P.theta < P.zeta / 2) {L M S flow : ℝ} (hL : 1 ≤
      L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : flow ≤ f (D.point N)) (hnot : ∀ k ≤ N, ¬StopsAt P ε D k) :
    ((successfulIterations (successfulSet D.trials D.ratio P.eta1) N).card : ℝ) ≤
      (f (D.point 0) - flow) / (commonDecreaseCoefficient P L M S * accuracyFactor
        P.toSettings ε) := by
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  apply card_successful_le_gap_div (S := successfulSet D.trials D.ratio P.eta1)
    (f := fun i => f (D.point i)) (k := N)
    (mul_pos (commonDecreaseCoefficient_pos P hmargin hL hM hS)
      (accuracyFactor_pos P.toSettings h.accuracy_pos)) hlow
  · intro i hi hsuccess
    exact h.function_decrease_uniform hf hmargin hL hM hlip hparam hjet hi hsuccess.1 hsuccess.2
      (hnot (i + 1) (by omega))
  · intro i hi hsuccess
    exact (h.objective_eq_of_not_successful hi hsuccess).le

/-- At most one extra success can first attain the target. Its objective
value and all later target checks need no assumed decrease floor. -/
theorem successful_card_le (h : Run f P ε D N)
    (hf : ContDiff ℝ p f) (hmargin : P.theta < P.zeta / 2) {L M S flow : ℝ} (hL : 1 ≤
      L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬StopsAt P ε D k) :
    ((successfulIterations (successfulSet D.trials D.ratio P.eta1) N).card : ℝ) ≤
      (f (D.point 0) - flow) / (commonDecreaseCoefficient P L M S * accuracyFactor
        P.toSettings ε) + 1 := by
  classical
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  have hden : 0 < commonDecreaseCoefficient P L M S * accuracyFactor P.toSettings ε :=
    mul_pos (commonDecreaseCoefficient_pos P hmargin hL hM hS) (accuracyFactor_pos
      P.toSettings h.accuracy_pos)
  cases N with
  | zero =>
    simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]
    exact le_add_of_le_of_nonneg (div_nonneg (sub_nonneg.mpr (hlow _)) hden.le) zero_le_one
  | succ n =>
    have hc := (h.restrict (Nat.le_succ n)).successful_card_le_of_no_target_endpoint hf hmargin
      hL hM hlip (fun k hk => hparam k (hk.trans (Nat.le_succ n)))
      (fun k hk => hjet k (hk.trans (Nat.le_succ n))) (hlow _)
      (fun k hk => hnot k (by omega))
    have hcard : (successfulIterations (successfulSet D.trials D.ratio P.eta1) (n + 1)).card ≤
        (successfulIterations (successfulSet D.trials D.ratio P.eta1) n).card + 1 := by
      rw [card_successful_succ]
      split_ifs <;> omega
    have hcast : ((successfulIterations (successfulSet D.trials D.ratio P.eta1) (n + 1)).card :
        ℝ) ≤ (successfulIterations (successfulSet D.trials D.ratio P.eta1) n).card + 1 := by
      exact_mod_cast hcard
    linarith

end Run
end InexactRegularization.Explicit
