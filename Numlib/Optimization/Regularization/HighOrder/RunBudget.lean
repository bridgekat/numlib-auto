import Numlib.Optimization.Regularization.HighOrder.ComplexityConstants
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# Objective budgets for exact high-order regularization executions

Actual computed model tests and derived radius floors bound accepted steps.
A true finite minimum of positive order coefficients gives a uniform objective
budget. The first target-reaching success is counted without assuming that it
satisfies the decrease floor used before the target.
-/

namespace HighOrderRegularization
open InexactTrustRegion HighOrderStep EvaluationComplexity
open InexactRegularization (rootStepExponent evaluationExponent pow_lower_of_root_step)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- An actual accepted step before the next target satisfies one source
fractional accuracy rate, with its fixed positive coefficient. -/
theorem exists_root_step_lower (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hnot : ¬TargetAt f P ε D (k + 1)) :
    ∃ a, rootStepCoefficient P L (parameterCap P L) (modelOrder a) *
      (ε a) ^ rootStepExponent p q (modelOrder a) ≤ ‖D.step k‖ := by
  let S := parameterCap P L
  let κ := regularizationRadiusCoefficient P.zeta P.theta L L S q
  have hS : 0 ≤ S := (parameterCap_pos P L).le
  have hκ := regularizationRadiusCoefficient_mem P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one hL hL hS q
  have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
  obtain ⟨a, ha⟩ := h.criticality_obstruction hf hL (hlip p hp le_rfl) hk haccepted hnot
  have hj : 1 ≤ modelOrder a := by unfold modelOrder; omega
  have hjq : modelOrder a ≤ q := by unfold modelOrder; omega
  have hδupdate : D.radius (k + 1) = D.solvedRadius k := by
    rw [h.radius_update k hk, ite_eq_left haccepted]
  have hunit : q ≤ 2 → D.radius (k + 1) a = 1 := by
    intro hq2
    rw [hδupdate]
    exact (h.step_two k hk.le (h.continues k hk)).unit_radius a (hjq.trans hq2)
  have hfloor : ‖D.step k‖ ≤ 1 → κ * ε a ≤ D.radius (k + 1) a := by
    intro hs
    rw [hδupdate]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (h.accuracy_pos a).le).trans
      (h.solved_radius_floor hf hL hlip hk.le (h.continues k hk) hs a)
  have hh := lower_of_obstruction hj hjq P.order_le P.theta_pos P.theta_lt_one
    (by linarith : 1 ≤ L + S) hκ.1.le hκ.2 (min_le_right _ _)
    (h.accuracy_pos a).le (h.accuracy_le_one a) (h.radius_mem (by omega) a).1
    (norm_nonneg _) hunit hfloor ha
  refine ⟨a, ?_⟩
  by_cases hq2 : q ≤ 2
  · simpa only [rootStepCoefficient, rootStepExponent, ite_eq_left hq2] using hh
  · simpa only [rootStepCoefficient, rootStepExponent, ite_eq_right hq2] using hh

/-- Every actual successful trial before the next target consumes the fixed
common objective coefficient times the exact minimum source accuracy power. -/
theorem function_decrease_uniform (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hnot : ¬TargetAt f P ε D (k + 1)) :
    commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε ≤
      f (D.point k) - f (D.point (k + 1)) := by
  have hS := (parameterCap_pos P L).le
  obtain ⟨a, ha⟩ := h.exists_root_step_lower hf hL hlip hk haccepted hnot
  have hroot := rootStepCoefficient_pos P hL hS (modelOrder a)
  have hpow := pow_lower_of_root_step (n := p + 1) hroot.le (h.accuracy_pos a).le ha
  have hbase : 0 ≤ P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) := by
    exact div_nonneg (mul_nonneg P.eta1_pos.le P.sigmaMin_pos.le) (Nat.cast_nonneg _)
  have hscale := mul_le_mul_of_nonneg_left hpow hbase
  have hcommon := mul_le_mul (commonDecreaseCoefficient_le P L (parameterCap P L) a)
    (accuracyFactor_le P ε a) (accuracyFactor_pos P h.accuracy_pos).le
    (show 0 ≤ orderDecreaseCoefficient P L (parameterCap P L) a from by
      unfold orderDecreaseCoefficient
      positivity)
  apply hcommon.trans
  apply le_trans _ (h.modelTrace.successful_decrease hk haccepted).le
  convert hscale using 1
  unfold orderDecreaseCoefficient evaluationExponent
  ring

/-- A lower objective bound controls every success in a prefix whose endpoint
also precedes the target, using only actual objective decreases and updates. -/
theorem successful_card_le_of_no_target_endpoint (h : Run f P ε D N)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : flow ≤ f (D.point N)) (hnot : ∀ k ≤ N, ¬TargetAt f P ε D k) :
    ((successfulIterations {i | P.eta1 ≤ D.ratio i} N).card : ℝ) ≤
      (f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε) := by
  apply card_successful_le_gap_div (S := {i | P.eta1 ≤ D.ratio i})
    (f := fun i => f (D.point i)) (k := N)
    (mul_pos (commonDecreaseCoefficient_pos P hL (parameterCap_pos P L).le)
      (accuracyFactor_pos P h.accuracy_pos)) hlow
  · intro i hi hsuccess
    exact h.function_decrease_uniform hf hL hlip hi hsuccess (hnot (i + 1) (by omega))
  · intro i hi hsuccess
    change ¬P.eta1 ≤ D.ratio i at hsuccess
    have hx : D.point (i + 1) = D.point i := by
      rw [h.modelTrace.point_update i hi, ite_eq_right hsuccess]
    exact hx ▸ le_rfl

/-- At most one extra success first reaches the target, retaining initialized
and endpoint derivative evaluation counts. -/
theorem successful_card_le (h : Run f P ε D N)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬TargetAt f P ε D k) :
    ((successfulIterations {i | P.eta1 ≤ D.ratio i} N).card : ℝ) ≤
      (f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε) + 1 := by
  have hden : 0 < commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε :=
    mul_pos (commonDecreaseCoefficient_pos P hL (parameterCap_pos P L).le)
      (accuracyFactor_pos P h.accuracy_pos)
  cases N with
  | zero =>
    simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]
    exact le_add_of_le_of_nonneg (div_nonneg (sub_nonneg.mpr (hlow _)) hden.le) zero_le_one
  | succ n =>
    have hc := (h.restrict (Nat.le_succ n)).successful_card_le_of_no_target_endpoint hf
      hL hlip (hlow _) (fun k hk => hnot k (by omega))
    have hcard : (successfulIterations {i | P.eta1 ≤ D.ratio i} (n + 1)).card ≤
        (successfulIterations {i | P.eta1 ≤ D.ratio i} n).card + 1 := by
      rw [card_successful_succ]
      split_ifs <;> omega
    have hcast : ((successfulIterations {i | P.eta1 ≤ D.ratio i} (n + 1)).card : ℝ) ≤
        (successfulIterations {i | P.eta1 ≤ D.ratio i} n).card + 1 := by exact_mod_cast hcard
    linarith

end Run
end HighOrderRegularization
