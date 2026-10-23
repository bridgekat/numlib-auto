import Numlib.Optimization.Regularization.Convex.LeastSquares.Run
import Numlib.Optimization.LeastSquares.LowerBudget

/-!
# Exact dyadic budgets for genuine constrained least-norm executions

The actual constrained scaled-model decrease transfers to normalized
criticality and then to the scalar dyadic residual budget. The same exact
constants as the first-order unconstrained analysis apply; only the genuine
constrained criticality replaces the gradient norm.
-/

namespace ConvexLeastSquares
open Set TaylorModel HighOrderRegularization LeastSquares ConvexRegularization
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] {p : ℕ} {r : E → F} {ℓ L β : ℝ} {C S : Set E}
  {P : Settings p} {ε₀ ε₁ : ℝ} {D : Data E} {N : ℕ}

/-- Every true normalized constrained measure on an actual iterate is nonnegative. -/
theorem Run.measure_nonneg (h : Run r ℓ C P ε₀ ε₁ D N) (hclosed : IsClosed C)
    {i : ℕ} (hi : i ≤ N) : 0 ≤ firstMeasure r ℓ C (D.point i) :=
  div_nonneg (constrainedCriticality_nonneg _ 1 hclosed (h.mem hi) zero_le_one)
    (Real.rpow_nonneg (norm_nonneg _) _)

/-- The actual accepted objective decrease gives the correctly normalized
residual-power decrease, including a zero endpoint residual. -/
theorem Run.residual_power_decrease (h : Run r ℓ C P ε₀ ε₁ D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (powerObjective r ℓ) S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
        iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : P.eta1 ≤ D.ratio i) :
    firstDecreaseCoefficient P L * ℓ * firstMeasure r ℓ C (D.point (i + 1)) ^
      (((p + 1 : ℕ) : ℝ) / p) * ‖r (D.point (i + 1))‖ ^
        ((ℓ - 1) * (((p + 1 : ℕ) : ℝ) / p)) ≤
      ‖r (D.point i)‖ ^ ℓ - ‖r (D.point (i + 1))‖ ^ ℓ := by
  have hdrop := h.scaledRun.successful_decrease hclosed hS hCS hC hf hL hlip hi hs
  exact residual_decrease_of_power (by linarith [h.residual_order])
    (firstDecreaseCoefficient_pos P hL).le
    (constrainedCriticality_nonneg _ 1 hclosed (h.mem (by omega)) zero_le_one)
    (by have := P.order_pos; positivity) hdrop

/-- A successful nonterminal endpoint consumes the exact common first-order
dyadic residual budget, with all constants independent of both accuracies. -/
theorem Run.successful_root_decrease (h : Run r ℓ C P ε₀ ε₁ D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (powerObjective r ℓ) S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
        iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ) (hι : 0 ≤ cascadingExponent p ℓ a 1)
    {i : ℕ} (hi : i + 1 < N) (hs : P.eta1 ≤ D.ratio i) :
    lowerDecreaseCoefficient false p ℓ a P.sigmaInitial P.sigmaMin P.eta1 P.eta2
      P.gamma3 L P.theta 1 β * lowerAccuracyFactor false p a ε₀ ε₁ 1 /
      lowerDenominator false p ℓ a ‖r (D.point 0)‖ ≤
      ‖r (D.point i)‖ ^ (1 / (2 : ℝ) ^ a) -
        ‖r (D.point (i + 1))‖ ^ (1 / (2 : ℝ) ^ a) := by
  let K := firstDecreaseCoefficient P L
  let c := lowerDecreaseCoefficient false p ℓ a P.sigmaInitial P.sigmaMin P.eta1 P.eta2
    P.gamma3 L P.theta 1 β
  let A := lowerAccuracyFactor false p a ε₀ ε₁ 1
  let B := lowerDenominator false p ℓ a ‖r (D.point 0)‖
  have hK : 0 < K := firstDecreaseCoefficient_pos P hL
  have hA : 0 < A := lowerAccuracyFactor_pos false p a h.accuracy_global_pos
    h.accuracy_first_pos zero_lt_one
  have hB : 0 < B := lowerDenominator_pos false p ℓ a _
  obtain ⟨hc₀, hc₁, _⟩ := lowerDecreaseCoefficient_bounds false p ℓ a
    P.sigmaInitial P.sigmaMin P.eta1 P.eta2 P.gamma3 L P.theta 1 β
  obtain ⟨hAcc₀, hAcc₁, _⟩ := lowerAccuracyFactor_bounds false p a ε₀ ε₁ 1
  obtain ⟨hB₀, hB₁, _⟩ := lowerDenominator_bounds false p ℓ a ‖r (D.point 0)‖
  have hx : 0 < ‖r (D.point i)‖ := h.accuracy_global_pos.trans (h.residual_gt (by omega))
  have hb := h.residual_step_le (show i < N by omega)
  have hq : 0 < (1 : ℝ) / 2 ^ a := by positivity
  by_cases hrel : β * ‖r (D.point i)‖ < ‖r (D.point (i + 1))‖
  · have ht := cascading_decrease_of_power (i := a) (p := p) (j := 1) (ℓ := ℓ)
      (κ := K) (u := firstMeasure r ℓ C (D.point (i + 1))) hx (norm_nonneg _) hb hβ hrel.le
      (show 1 ≤ ℓ by linarith [h.residual_order]) hK.le
      (h.measure_nonneg hclosed (show i + 1 ≤ N by omega)) P.order_pos (by
        simpa only [Nat.add_sub_cancel, mul_div_assoc] using
          h.residual_power_decrease hclosed hS hCS hC hf hL hlip (by omega) hs)
    apply budget_le_of_measure hA.le hB (cascadingConstant_pos hK hβ p a 1).le hc₁
      hAcc₁ h.accuracy_first_pos.le (h.measure_gt hi).le (by positivity)
      (Real.rpow_pos_of_pos hx _) _ (by simpa only [Nat.add_sub_cancel] using ht)
    exact (Real.rpow_le_rpow (norm_nonneg _) (h.residual_le_initial (by omega)) hι).trans hB₁
  · have hh := Real.relative_cascading_decrease (norm_nonneg _) hb hβ.le hβ1
      (not_lt.mp hrel) hq
    apply budget_le_of_measure hA.le hB hh.1.le hc₀ hAcc₀ h.accuracy_global_pos.le
      (h.residual_gt hi).le hq.le zero_lt_one hB₀
    simpa only [div_one] using hh.2.2.trans hh.2.1

end ConvexLeastSquares
