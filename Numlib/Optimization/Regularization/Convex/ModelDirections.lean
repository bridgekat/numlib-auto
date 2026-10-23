import Numlib.Optimization.Constrained.RestrictedCriticality
import Numlib.Optimization.Constrained.FirstOrderModel
import Numlib.Optimization.Regularization.HighOrder.Parameter

/-!
# Actual model-restricted feasible direction hierarchies

The zero, first and second restrictions in the constrained regularization
algorithm use actual feasibility at x + s and actual model derivatives at s.
Their unit-ball derivative measures are genuine extrema of those derivatives.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The three actual model direction sets M⁰,M¹,M² in(6.2.1)-(6.2.2). -/
noncomputable def modelRestrictedDirections (f : E → ℝ) (p : ℕ) (C : Set E)
    (x : E) (σ : ℝ) (s : E) (a b : ℝ) : Fin 3 → Set E :=
  ![feasibleDisplacements C (x + s),
    firstRestrictedDirections (model f p x σ) (feasibleDisplacements C (x + s)) s a,
    secondRestrictedDirections (model f p x σ) (feasibleDisplacements C (x + s)) s a b]

/-- M⁰ is exactly the actual feasible endpoint displacement set. -/
@[simp] theorem modelRestrictedDirections_zero (f : E → ℝ) (p : ℕ) (C : Set E)
    (x : E) (σ : ℝ) (s : E) (a b : ℝ) :
    modelRestrictedDirections f p C x σ s a b 0 = feasibleDisplacements C (x + s) := rfl

/-- M¹ imposes the true model first-derivative restriction. -/
@[simp] theorem modelRestrictedDirections_one (f : E → ℝ) (p : ℕ) (C : Set E)
    (x : E) (σ : ℝ) (s : E) (a b : ℝ) :
    modelRestrictedDirections f p C x σ s a b 1 =
      firstRestrictedDirections (model f p x σ) (feasibleDisplacements C (x + s)) s a := rfl

/-- M² imposes both actual lower model derivative restrictions. -/
@[simp] theorem modelRestrictedDirections_two (f : E → ℝ) (p : ℕ) (C : Set E)
    (x : E) (σ : ℝ) (s : E) (a b : ℝ) :
    modelRestrictedDirections f p C x σ s a b 2 =
      secondRestrictedDirections (model f p x σ) (feasibleDisplacements C (x + s)) s a b := rfl

/-- Actual feasibility and nonnegative model tolerances retain the zero
vector in every level, including both disabled higher-order levels. -/
theorem zero_mem_modelRestrictedDirections {f : E → ℝ} {p : ℕ} {C : Set E}
    {x s : E} {σ a b : ℝ} (hxs : x + s ∈ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (j : Fin 3) :
    (0 : E) ∈ modelRestrictedDirections f p C x σ s a b j := by
  have hz : (0 : E) ∈ feasibleDisplacements C (x + s) := by simpa using hxs
  fin_cases j
  · exact hz
  · exact zero_mem_firstRestrictedDirections hz ha
  · exact zero_mem_secondRestrictedDirections hz ha hb

/-- Closed source feasibility implies closedness of every actual model direction level. -/
theorem isClosed_modelRestrictedDirections {f : E → ℝ} {p : ℕ} {C : Set E}
    {x s : E} {σ a b : ℝ} (hC : IsClosed C) (j : Fin 3) :
    IsClosed (modelRestrictedDirections f p C x σ s a b j) := by
  have hc : IsClosed (feasibleDisplacements C (x + s)) :=
    hC.preimage (continuous_const.add continuous_id)
  fin_cases j
  · exact hc
  · exact isClosed_firstRestrictedDirections hc
  · exact isClosed_secondRestrictedDirections hc

/-- The actual model derivative measures(6.2.3)-(6.2.5), indexed by orders one to three. -/
noncomputable def modelDerivativeCriticality (f : E → ℝ) (p : ℕ) (C : Set E)
    (x : E) (σ : ℝ) (s : E) (a b : ℝ) (j : Fin 3) : ℝ :=
  tensorCriticality (iteratedFDeriv ℝ (j.val+1) (model f p x σ) s)
    (modelRestrictedDirections f p C x σ s a b j)

/-- Every actual model derivative measure is nonnegative at a feasible trial. -/
theorem modelDerivativeCriticality_nonneg {f : E → ℝ} {p : ℕ} {C : Set E}
    {x s : E} {σ a b : ℝ} (hxs : x + s ∈ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (j : Fin 3) :
    0 ≤ modelDerivativeCriticality f p C x σ s a b j :=
  tensorCriticality_nonneg (by omega) _ (zero_mem_modelRestrictedDirections hxs ha hb j)

/-- The first model measure agrees exactly with the genuine constrained model
criticality on the translated source feasible set. -/
theorem modelDerivativeCriticality_zero (f : E → ℝ) (p : ℕ) (C : Set E)
    (x : E) (σ : ℝ) (s : E) (a b : ℝ) :
    modelDerivativeCriticality f p C x σ s a b 0 =
      constrainedCriticality (model f p x σ) 1 (feasibleDisplacements C x) s 1 := by
  rw [←tensorCriticality_one,feasibleDisplacements_translate]
  rfl

end ConvexRegularization
