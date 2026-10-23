import NumlibSurface.CartisGouldToint.Chapter04.Section01
import Numlib.Optimization.HighOrder.ModelDecrease
import Numlib.Optimization.Composite.Optimality
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Taylor decrease for composite regularization

The generalized composite Taylor model approximates the smooth maps `f` and `c` while keeping
`h` intact. A nonincreasing step for its regularization gives the full decrement estimate of
Lemma 14.1.5, irrespective of whether `h` is differentiable.

Lemma 14.1.1 derives global minimality of the first-order model at zero and vanishing
actual composite criticality. Its source assumptions on subadditivity and `h(0)` are
unnecessary: Lipschitz continuity and convexity of `h` suffice.
-/

namespace CartisGouldToint

/-- The generalized Taylor model `T_{w,p}` of the composite objective `w = f + h ∘ c`. -/
noncomputable def compositeTaylorModel {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x s : E) : ℝ :=
  Composite.taylorModel f c h p x s

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

namespace CartisGouldToint

/-- The composite criticality measure (14.1.6), the largest decrease of the actual
composite Taylor model over the closed displacement ball. -/
noncomputable def compositeCriticality {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x : E) (δ : ℝ) : ℝ :=
  Composite.criticality f c h p x δ

/-- **Lemma 14.1.1 (convex-composite first-order necessary optimality).**
A true global minimum of `f + h ∘ c` globally minimizes its first-order composite model
at zero and has zero first-order composite criticality at every positive radius.
The source's subadditivity and zero-value assumptions on `h` can be omitted; Lipschitz
continuity controls the genuine derivative remainders directly. -/
theorem lemma_14_1_1 {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin n)) {K : NNReal}
    (hf : ContDiff ℝ 1 f) (hc : ContDiff ℝ 1 c)
    (hh : LipschitzWith K h) (hconv : ConvexOn ℝ Set.univ h)
    (hmin : IsMinOn (fun z => f z + h (c z)) Set.univ x) :
    IsMinOn (compositeTaylorModel f c h 1 x) Set.univ 0 ∧
      ∀ δ : ℝ, 0 < δ → compositeCriticality f c h 1 x δ = 0 := by
  have hm := Composite.taylorModel_one_isMinOn_of_isMinOn
    (hf.differentiable (by norm_num) x) (hc.differentiable (by norm_num) x) hh hconv hmin
  exact ⟨hm, fun _ hδ => Composite.criticality_eq_zero_of_model_min f c h 1 x hδ.le hm⟩

end CartisGouldToint
