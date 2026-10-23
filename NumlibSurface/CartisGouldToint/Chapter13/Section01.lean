import Numlib.Analysis.Calculus.TaylorModel
import Numlib.Optimization.HighOrder.ModelDecrease
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Positive model decrease for ARqpIDA

Approximate Taylor polynomials are finite polynomials of the actual approximate derivative
tensors. The model-comparison conditions of Step 2 imply both the penalty lower bound and
strict positivity of the acceptance ratio denominator.
-/

namespace CartisGouldToint

/-- The approximate Taylor model formed from a sequence of approximate derivative tensors. -/
noncomputable def inexactTaylorModel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (s : E) : ℝ :=
  TaylorModel.ofJet A p s

/-- Lemma 13.1.13: a trial step that improves on a strictly improving comparison step yields
at least the regularization penalty in the approximate Taylor decrement. That decrement is
strictly positive, so the denominator of equation (13.1.58) is nonzero. The two model comparisons
are the operational conditions (13.1.54) and (13.1.55) of Step 2. -/
theorem lemma_13_1_13 {n : ℕ}
    (A : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (p : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (d s : EuclideanSpace ℝ (Fin n))
    (hd : ModelDecrease.penalized (inexactTaylorModel A p) p σ d <
      ModelDecrease.penalized (inexactTaylorModel A p) p σ 0)
    (hs : ModelDecrease.penalized (inexactTaylorModel A p) p σ s ≤
      ModelDecrease.penalized (inexactTaylorModel A p) p σ d) :
    σ / ((p + 1).factorial : ℝ) * ‖s‖ ^ (p + 1) ≤
        inexactTaylorModel A p 0 - inexactTaylorModel A p s ∧
      0 < inexactTaylorModel A p 0 - inexactTaylorModel A p s ∧
      inexactTaylorModel A p 0 - inexactTaylorModel A p s ≠ 0 := by
  have hpos := ModelDecrease.decrement_pos (inexactTaylorModel A p) p hσ d s hd hs
  exact ⟨ModelDecrease.penalty_le_decrement _ _ _ _ (hs.trans hd.le),
    hpos, ne_of_gt hpos⟩

end CartisGouldToint
