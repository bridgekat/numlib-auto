import Numlib.Optimization.Regularization.HighOrder.RunBudget

/-!
# Total iteration budgets for exact high-order regularization

Primitive three-case parameter updates bound unsuccessful trials in terms of
successful trials and one fixed logarithmic initialization term. Combining this
with the actual objective budget bounds every prefix before its first target.
-/

namespace HighOrderRegularization
open EvaluationComplexity

/-- The fixed multiplicative cost of unsuccessful regularization trials. -/
noncomputable def trialCountFactor {p q : ℕ} (P : Settings p q) : ℝ :=
  1 + |Real.log P.gamma1| / Real.log P.gamma2

/-- The trial-count factor is at least one. -/
theorem one_le_trialCountFactor {p q : ℕ} (P : Settings p q) : 1 ≤ trialCountFactor P := by
  exact le_add_of_nonneg_right (div_nonneg (abs_nonneg _) (Real.log_pos P.one_lt_gamma2).le)

/-- The fixed parameter-cap initialization term in the total iteration budget. -/
noncomputable def trialCountOffset {p q : ℕ} (P : Settings p q) (L : ℝ) : ℝ :=
  Real.log (parameterCap P L / P.sigmaInitial) / Real.log P.gamma2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual finite executions before the first target obey the total trial
budget derived from successful decreases and operational parameter updates. -/
theorem Run.iterations_le {p q : ℕ} {f : E → ℝ} {P : Settings p q}
    {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}
    (h : Run f P ε D N) (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x, flow ≤ f x) (hnot : ∀ k < N, ¬TargetAt f P ε D k) :
    (N : ℝ) ≤ trialCountFactor P * ((f (D.point 0) - flow) /
      (commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε) + 1) +
        trialCountOffset P L := by
  have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
  have ht := iteration_bound_of_parameter_upper
    (S := {i | P.eta1 ≤ D.ratio i}) (fun i hi => h.modelTrace.updates.pos hi)
    P.gamma1_pos P.gamma1_lt_one P.one_lt_gamma2
    (h.parameter_le hf hL (hlip p hp le_rfl) le_rfl)
    (fun i hi hs => h.modelTrace.updates.successful_ge hi hs)
    (fun i hi hu => h.modelTrace.updates.unsuccessful_ge hi hu)
  rw [h.initial_parameter] at ht
  have hs := h.successful_card_le hf hL hlip hlow hnot
  have hfac : 0 ≤ trialCountFactor P := zero_le_one.trans (one_le_trialCountFactor P)
  have hh := mul_le_mul_of_nonneg_right hs hfac
  change (N : ℝ) ≤ (successfulIterations {i | P.eta1 ≤ D.ratio i} N).card *
    trialCountFactor P + trialCountOffset P L at ht
  exact ht.trans (by nlinarith)

end HighOrderRegularization
