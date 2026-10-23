import NumlibSurface.CartisGouldToint.Chapter04.Section01
import Numlib.Optimization.HighOrder.ModelDecrease
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Taylor decrease for composite regularization

The generalized composite Taylor model approximates the smooth maps `f` and `c` while keeping
`h` intact. A nonincreasing step for its regularization gives the full decrement estimate of
Lemma 14.1.5, irrespective of whether `h` is differentiable.
-/

namespace CartisGouldToint

/-- The generalized Taylor model `T_{w,p}` of the composite objective `w = f + h ∘ c`. -/
noncomputable def compositeTaylorModel {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x s : E) : ℝ :=
  taylorModel f p x s + h (taylorModel c p x s)

/-- At zero displacement the composite Taylor model equals the true composite objective. -/
@[simp] theorem compositeTaylorModel_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x : E) :
    compositeTaylorModel f c h p x 0 = f x + h (c x) := by
  simp [compositeTaylorModel]

/-- Lemma 14.1.5: the composite Taylor decrement at an ARqpC model-improving step is at least
the norm-power regularization penalty. The single hypothesis is the model comparison (14.1.11)
made when choosing the step, with the model given explicitly by equation (14.1.5). -/
theorem lemma_14_1_5 {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (p : ℕ) (σ : ℝ)
    (x s : EuclideanSpace ℝ (Fin n))
    (hs : ModelDecrease.penalized (compositeTaylorModel f c h p x) p σ s ≤
      ModelDecrease.penalized (compositeTaylorModel f c h p x) p σ 0) :
    σ / ((p + 1).factorial : ℝ) * ‖s‖ ^ (p + 1) ≤
      compositeTaylorModel f c h p x 0 - compositeTaylorModel f c h p x s :=
  ModelDecrease.penalty_le_decrement _ _ _ _ hs

end CartisGouldToint
