import Numlib.Optimization.Regularization.HighOrder.CriticalityTermination
import Numlib.Optimization.Regularization.HighOrder.RunTarget
import Numlib.Optimization.HighOrder.CriticalityRadius

/-!
# Full evaluation complexity of exact high-order adaptive regularization

Positive constants are fixed before accuracies and execution arrays. Actual
consistent prefixes reach true all-order criticality with the two source rates,
including unit-radius certification in orders one and two. Function calls
count every trial plus initialization; derivative calls count successful point
updates plus initialization. The safe radius coefficient only repairs proof
constants and does not change the algorithm or source accuracy exponents.
-/

namespace HighOrderRegularization
open InexactTrustRegion EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual exact ARqp executions attain true approximate optimality within
uniform initialized function and derivative evaluation budgets. All constants
precede every accuracy vector and computed execution. -/
theorem evaluation_complexity {p q : ℕ} (f : E → ℝ) (P : Settings p q) (x₀ : E)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x, flow ≤ f x) :
    ∃ κs > 0, ∃ κa > 0, ∃ κc > 0,
      ∀ (ε : Fin q → ℝ) (D : ExecutionData E q), D.point 0 = x₀ →
      (∀ N, (∀ k < N, ¬TargetAt f P ε D k) → Run f P ε D N) →
      ∃ (K : ℕ) (δ : Fin q → ℝ), Run f P ε D K ∧ TargetAt f P ε D K ∧
        (∀ k < K, ¬TargetAt f P ε D k) ∧ OptimalityAt f ε (D.point K) δ ∧
        (q ≤ 2 → ∀ a, TaylorModel.criticality f (modelOrder a) (D.point K) 1 ≤
          ε a / (modelOrder a).factorial) ∧
        ((K + 1 : ℕ) : ℝ) ≤ κa * (f x₀ - flow) / accuracyFactor P ε + κc ∧
        (((successfulIterations {i | P.eta1 ≤ D.ratio i} K).card + 1 : ℕ) : ℝ) ≤
          κs * (f x₀ - flow) / accuracyFactor P ε + 2 := by
  let c := commonDecreaseCoefficient P L (parameterCap P L)
  let κs := 1 / c
  let κa := trialCountFactor P / c
  let κc := trialCountFactor P + |trialCountOffset P L| + 2
  have hc : 0 < c := commonDecreaseCoefficient_pos P hL (parameterCap_pos P L).le
  have hfac : 0 < trialCountFactor P := zero_lt_one.trans_le (one_le_trialCountFactor P)
  refine ⟨κs, div_pos zero_lt_one hc, κa, div_pos hfac hc, κc, by
    dsimp [κc]; positivity, ?_⟩
  intro ε D hinit hprefix
  obtain ⟨K, htarget, hrun, hfirst⟩ := exists_target hprefix hf hL hlip hlow
  obtain ⟨δ, hopt, _⟩ := hrun.target_optimality hf.contDiffAt htarget
  have ht := hrun.iterations_le hf hL hlip hlow hfirst
  have hs := hrun.successful_card_le hf hL hlip hlow hfirst
  rw [hinit] at ht hs
  have hrate := accuracyFactor_pos P hrun.accuracy_pos
  have hgap : 0 ≤ (f x₀ - flow) / (c * accuracyFactor P ε) :=
    div_nonneg (sub_nonneg.mpr (hlow _)) (mul_pos hc hrate).le
  have hea : κa * (f x₀ - flow) / accuracyFactor P ε =
      trialCountFactor P * ((f x₀ - flow) / (c * accuracyFactor P ε)) := by
    dsimp only [κa]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hes : κs * (f x₀ - flow) / accuracyFactor P ε =
      (f x₀ - flow) / (c * accuracyFactor P ε) := by
    dsimp only [κs]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    ring
  refine ⟨K, δ, hrun, htarget, hfirst, hopt, ?_, ?_, ?_⟩
  · intro hq2 a
    have hj : 1 ≤ modelOrder a := by unfold modelOrder; omega
    have hj2 : modelOrder a ≤ 2 := by unfold modelOrder; omega
    exact TaylorModel.criticality_unit_le_of_radius f (D.point K) hj hj2
      (hopt.1 a).1 (hopt.1 a).2 (hopt.2 a)
  · rw [hea]
    dsimp only [κc]
    norm_num only [Nat.cast_add, Nat.cast_one]
    change (K : ℝ) ≤ trialCountFactor P *
      ((f x₀ - flow) / (c * accuracyFactor P ε) + 1) + trialCountOffset P L at ht
    nlinarith [le_abs_self (trialCountOffset P L)]
  · rw [hes]
    norm_num only [Nat.cast_add, Nat.cast_one]
    change _ ≤ (f x₀ - flow) /
      (commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε) + 2
    linarith

end HighOrderRegularization
