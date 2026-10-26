import Numlib.Optimization.Regularization.Inexact.Explicit.Budget
import Numlib.Optimization.Regularization.Inexact.Explicit.CurrentBudget

/-!
# Corrected model and function decreases for explicit accuracy

The sharp regularization rates require an effective stopping margin and a
nonstopping next iterate. An unconditional all-trial alternative derives the
coarser current-check rate. Both give model and true function decreases from
actual comparisons, relative objective errors and operational radius floors.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- With a positive effective stopping margin, the actual computed decrement
has both sharp source rates and the corrected uniform coefficient. -/
theorem computed_decrement_uniform_effective_margin (h : Run f P ε D N)
    (hf : ContDiff ℝ p f) (hmargin : P.theta < P.zeta / 2)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) (ha : P.eta1 ≤ D.ratio k)
    (hnot : ¬StopsAt P ε D (k + 1)) :
    (2 * commonDecreaseCoefficient P L M S / P.eta1) * accuracyFactor P.toSettings ε ≤
      TaylorModel.jetDecrement (D.jet k) p (D.step k) := by
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  obtain ⟨a, hb⟩ := h.exists_root_step_lower_of_cap hf hmargin hL hM hlip hparam hjet
    hk ht ha hnot
  have hr := rootStepCoefficient_pos P hmargin hL hM hS (modelOrder a)
  have hp := pow_lower_of_root_step (n := p + 1) hr.le (h.accuracy_pos a).le hb
  have hη := P.eta1_pos
  have hσ := P.sigmaMin_pos
  have hc := mul_le_mul (commonDecreaseCoefficient_le P L M S a)
    (accuracyFactor_le P.toSettings ε a)
    (accuracyFactor_pos P.toSettings h.accuracy_pos).le
    (show 0 ≤ orderDecreaseCoefficient P L M S a by
      unfold orderDecreaseCoefficient; positivity)
  have hm := (penalty_lt_decrement
    (h.toFunctionTrace.toOracleTrace.reference_improvement k hk ht)
    (h.step_two k hk ((h.trial_rule k hk).mp ht).1).comparison).le
  have hmin := h.updates.min_le hk.le
  have hpen := (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hmin (Nat.cast_nonneg (p + 1).factorial))
    (pow_nonneg (norm_nonneg (D.step k)) (p + 1))).trans hm
  have hscale := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ P.eta1 * P.sigmaMin / (2 * ((p + 1).factorial : ℝ)) by positivity)
  have hh : commonDecreaseCoefficient P L M S * accuracyFactor P.toSettings ε ≤
      P.eta1 / 2 * TaylorModel.jetDecrement (D.jet k) p (D.step k) := by
    apply hc.trans
    apply le_trans _ (mul_le_mul_of_nonneg_left hpen (half_pos hη).le)
    convert hscale using 1
    · unfold orderDecreaseCoefficient evaluationExponent
      ring
    · ring
  have hd : (commonDecreaseCoefficient P L M S * accuracyFactor P.toSettings ε) /
      (P.eta1 / 2) ≤ TaylorModel.jetDecrement (D.jet k) p (D.step k) :=
    (div_le_iff₀ (half_pos hη)).2 (by convert hh using 1; ring)
  convert hd using 1
  ring

/-- The same effective-margin coefficient bounds the computed model decrease
and the true objective drop, including both approximate function-value errors. -/
theorem model_function_decrease_effective_margin (h : Run f P ε D N)
    (hf : ContDiff ℝ p f) (hmargin : P.theta < P.zeta / 2)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) (ha : P.eta1 ≤ D.ratio k)
    (hnot : ¬StopsAt P ε D (k + 1)) :
    let c := 2 * commonDecreaseCoefficient P L M S / P.eta1
    0 < c ∧ c * accuracyFactor P.toSettings ε ≤
      TaylorModel.jetDecrement (D.jet k) p (D.step k) ∧
      P.eta1 / 2 * c * accuracyFactor P.toSettings ε ≤
        f (D.point k) - f (D.point (k + 1)) := by
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  have hc := commonDecreaseCoefficient_pos P hmargin hL hM hS
  refine ⟨div_pos (mul_pos (by norm_num) hc) P.eta1_pos,
    h.computed_decrement_uniform_effective_margin hf hmargin hL hM hlip hparam hjet
      hk ht ha hnot, ?_⟩
  convert h.function_decrease_uniform hf hmargin hL hM hlip hparam hjet hk ht ha hnot using 1
  field_simp [P.eta1_pos.ne']

/-- Every literal trial obeys a fixed current-check model floor, with no
additional stopping margin. Accepted trials also obey the corresponding true
function floor. The rate is explicitly the coarser epsilon-min power q+1. -/
theorem model_function_decrease_current (h : Run f P ε D N)
    (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) :
    let M := executionTensorCap P.toSettings L
    let S := executionParameterCap P.toSettings L
    let c := currentReferenceCoefficient P M S
    0 < c ∧ c * (minimumAccuracy P.order_pos ε) ^ (q + 1) ≤
      TaylorModel.jetDecrement (D.jet k) p (D.step k) ∧
      (P.eta1 ≤ D.ratio k → P.eta1 / 2 * c *
        (minimumAccuracy P.order_pos ε) ^ (q + 1) ≤
          f (D.point k) - f (D.point (k + 1))) := by
  have hM := one_le_executionTensorCap P.toSettings hL
  obtain ⟨hparam, hjet⟩ := h.actual_caps hf hL hlip
  refine ⟨currentReferenceCoefficient_pos P hM,
    h.computed_decrement_lower_current hM hparam
      (fun k hk i hi hip => hjet k hk i (by omega) hip) hk ht, ?_⟩
  intro ha
  simpa only [currentDecreaseCoefficient, mul_assoc] using
    h.function_decrease_uniform_current hM hparam
      (fun k hk i hi hip => hjet k hk i (by omega) hip) hk ht ha

end Run
end InexactRegularization.Explicit
