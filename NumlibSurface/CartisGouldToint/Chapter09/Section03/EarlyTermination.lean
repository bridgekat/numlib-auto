import NumlibSurface.CartisGouldToint.Chapter09.Section03
import Numlib.Optimization.WeightedPowerDerivatives

/-!
# Chapter 9: invariant early regularization stopping

The Hessian test is relative to the SPD metric. The source's ordinary Euclidean eigenvalue
transcription is recorded separately as wrong in the parent plan. This criterion and its
sufficient scalar tests use the generalized, coordinate-invariant Hessian bound instead.
-/

noncomputable section
namespace CartisGouldToint.Chapter09.Section03
open scoped InnerProductSpace
open Chapter08.Section01 Chapter08.Section02

/-- Positive tolerances for the gradient and generalized-curvature stopping tests. -/
structure EarlyTerminationTolerances where
  theta1 : ℝ
  theta2 : ℝ
  theta1_pos : 0 < theta1
  theta2_pos : 0 < theta2

/-- The invariant form of the three early stopping tests (9.3.14), using the actual model,
its actual gradient in the inverse metric, and its actual bilinear Hessian relative to `M`. -/
def regularizationEarlyTermination {n : ℕ} (a : EarlyTerminationTolerances)
    (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (sigma r : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  regularizedModel g H M sigma r s ≤ 0 ∧
    weightedNorm M⁻¹ (gradient (regularizedModel g H M sigma r) s) ≤
      a.theta1 / 2 * weightedNorm M s ^ 2 ∧
    ∀ d, -(a.theta2 * weightedNorm M s) * weightedNorm M d ^ 2 ≤
      fderiv ℝ (fderiv ℝ (regularizedModel g H M sigma r)) s d d

/-- Unfold the stopping criterion into its three concrete model tests. -/
@[simp] theorem regularizationEarlyTermination_iff {n : ℕ} (a : EarlyTerminationTolerances)
    (g s : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ) (sigma r : ℝ) :
    regularizationEarlyTermination a g H M sigma r s ↔
      regularizedModel g H M sigma r s ≤ 0 ∧
      weightedNorm M⁻¹ (gradient (regularizedModel g H M sigma r) s) ≤
        a.theta1 / 2 * weightedNorm M s ^ 2 ∧
      ∀ d, -(a.theta2 * weightedNorm M s) * weightedNorm M d ^ 2 ≤
        fderiv ℝ (fderiv ℝ (regularizedModel g H M sigma r)) s d d := Iff.rfl

/-- Separate objective, gradient and generalized-Hessian certificates introduce early stopping. -/
theorem regularizationEarlyTermination.of_bounds {n : ℕ} {a : EarlyTerminationTolerances}
    {g s : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ} {sigma r : ℝ}
    (hf : regularizedModel g H M sigma r s ≤ 0)
    (hg : weightedNorm M⁻¹ (gradient (regularizedModel g H M sigma r) s) ≤
      a.theta1 / 2 * weightedNorm M s ^ 2)
    (hH : ∀ d, -(a.theta2 * weightedNorm M s) * weightedNorm M d ^ 2 ≤
      fderiv ℝ (fderiv ℝ (regularizedModel g H M sigma r)) s d d) :
    regularizationEarlyTermination a g H M sigma r s := ⟨hf, hg, hH⟩

/-- Early stopping certifies a nonpositive actual model value. -/
theorem regularizationEarlyTermination.objective_nonpos {n : ℕ} {a : EarlyTerminationTolerances}
    {g s : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ} {sigma r : ℝ}
    (h : regularizationEarlyTermination a g H M sigma r s) :
    regularizedModel g H M sigma r s ≤ 0 := h.1

/-- Early stopping certifies the actual inverse-metric gradient norm. -/
theorem regularizationEarlyTermination.gradient_bound {n : ℕ} {a : EarlyTerminationTolerances}
    {g s : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ} {sigma r : ℝ}
    (h : regularizationEarlyTermination a g H M sigma r s) :
    weightedNorm M⁻¹ (gradient (regularizedModel g H M sigma r) s) ≤
      a.theta1 / 2 * weightedNorm M s ^ 2 := h.2.1

/-- Early stopping bounds every actual Hessian direction relative to its metric norm. -/
theorem regularizationEarlyTermination.hessian_bound {n : ℕ} {a : EarlyTerminationTolerances}
    {g s : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ} {sigma r : ℝ}
    (h : regularizationEarlyTermination a g H M sigma r s) (d : EuclideanSpace ℝ (Fin n)) :
    -(a.theta2 * weightedNorm M s) * weightedNorm M d ^ 2 ≤
      fderiv ℝ (fderiv ℝ (regularizedModel g H M sigma r)) s d d := h.2.2 d

end CartisGouldToint.Chapter09.Section03
