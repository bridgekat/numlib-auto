import Numlib.Optimization.Regularization.Convex.DerivativeTransfer
import Numlib.Optimization.Regularization.HighOrder.Complexity

/-!
# Genuine constrained third-order successful-step budgets

The complete actual constrained stopping tests force a large step at some
order. The true factorial-normalized regularization penalty converts that step
to a uniform objective reduction. Both constants and exponents use actual
first, second and third derivative measures.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization EvaluationComplexity

/-- The true decrease coefficient at each constrained derivative order. -/
noncomputable def derivativeDecreaseCoefficient {p : ℕ}
    (P : DerivativeSettings p 2) (L : ℝ) (j : Fin 3) : ℝ :=
  P.eta1 * P.sigmaMin / (p + 1).factorial * derivativeStepThreshold P L j ^
    (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ))

/-- The positive minimum decrease coefficient is fixed before all accuracies. -/
noncomputable def derivativeBudgetCoefficient {p : ℕ}
    (P : DerivativeSettings p 2) (L : ℝ) : ℝ :=
  min (derivativeDecreaseCoefficient P L 0)
    (min (derivativeDecreaseCoefficient P L 1) (derivativeDecreaseCoefficient P L 2))

/-- The exact source threshold is strictly positive at every enabled order. -/
theorem derivativeStepThreshold_pos {p : ℕ} {q : Fin 3}
    (P : DerivativeSettings p q) {L : ℝ} (hL : 0 ≤ L) (j : Fin 3) :
    0 < derivativeStepThreshold P L j := by
  have hc : 0 < parameterCap P.toSettings L :=
    (P.sigmaMin_pos.trans_le P.sigmaMin_le_initial).trans_le (le_max_left _ _)
  unfold derivativeStepThreshold
  exact div_pos (mul_pos (by positivity) (sub_pos.mpr (P.fractions_lt_one j)))
    (add_pos_of_nonneg_of_pos hL hc)

/-- Each true factorial-normalized decrease coefficient is positive. -/
theorem derivativeDecreaseCoefficient_pos {p : ℕ}
    (P : DerivativeSettings p 2) {L : ℝ} (hL : 0 ≤ L) (j : Fin 3) :
    0 < derivativeDecreaseCoefficient P L j :=
  mul_pos (div_pos (mul_pos P.eta1_pos P.sigmaMin_pos) (by positivity))
    (Real.rpow_pos_of_pos (derivativeStepThreshold_pos P hL j) _)

/-- The common true decrease coefficient is positive. -/
theorem derivativeBudgetCoefficient_pos {p : ℕ}
    (P : DerivativeSettings p 2) {L : ℝ} (hL : 0 ≤ L) :
    0 < derivativeBudgetCoefficient P L :=
  lt_min (derivativeDecreaseCoefficient_pos P hL 0)
    (lt_min (derivativeDecreaseCoefficient_pos P hL 1)
      (derivativeDecreaseCoefficient_pos P hL 2))

/-- The common coefficient does not exceed any of the three actual-order coefficients. -/
theorem derivativeBudgetCoefficient_le {p : ℕ}
    (P : DerivativeSettings p 2) (L : ℝ) (j : Fin 3) :
    derivativeBudgetCoefficient P L ≤ derivativeDecreaseCoefficient P L j := by
  fin_cases j
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {p : ℕ} {f : E → ℝ} {C S : Set E} {P : DerivativeSettings p 2}
  {ε : Fin 3 → ℝ} {D : Data E} {N : ℕ}

/-- The actual finite-order accuracy budget is positive. -/
theorem DerivativeRun.accuracy_factor_pos (h : DerivativeRun f C P ε D N) :
    0 < finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) :=
  lt_min (Real.rpow_pos_of_pos (h.accuracy_pos 0) _)
    (lt_min (Real.rpow_pos_of_pos (h.accuracy_pos 1) _)
      (Real.rpow_pos_of_pos (h.accuracy_pos 2) _))

/-- The actual minimum accuracy power does not exceed its selected-order component. -/
theorem derivativeAccuracyFactor_le (p : ℕ) (ε : Fin 3 → ℝ) (j : Fin 3) :
    finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) ≤
      ε j ^ (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)) := by
  fin_cases j
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- Every accepted endpoint that still fails a literal true derivative test
consumes the common positive objective budget with the genuine(p+1)! factor. -/
theorem DerivativeRun.nonterminal_decrease (h : DerivativeRun f C P ε D N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i + 1 < N) (hs : P.eta1 ≤ D.ratio i) :
    derivativeBudgetCoefficient P L * finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) ≤
      f (D.point i) - f (D.point (i + 1)) := by
  obtain ⟨j,hj,ht⟩ := h.exists_large_step hS hCS hC hf hL hlip hi hs
  have horder := P.enabled_order
  have hm : 0 < p - j.val := by have := j.isLt; omega
  have hb := h.modelTrace.decrease_of_step_lower (by omega) hs hm
    (derivativeStepThreshold_pos P hL j).le (h.accuracy_pos j).le ht.le
  exact (mul_le_mul (derivativeBudgetCoefficient_le P L j)
    (derivativeAccuracyFactor_le p ε j) h.accuracy_factor_pos.le
    (derivativeDecreaseCoefficient_pos P hL j).le).trans hb

end ConvexRegularization
