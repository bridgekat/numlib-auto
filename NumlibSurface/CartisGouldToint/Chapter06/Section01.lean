import Numlib.Optimization.Constrained.RestrictedCriticality

/-!
# Actual first- to third-order constrained derivative measures

The actual feasible displacement sets carry the genuine first- and
second-derivative restrictions. The three signed measures are minus the minima
of the appropriate derivative diagonals on their restricted unit balls.
The missing leading minus signs in the supplied displays(6.1.5) and(6.1.9)
are restored, consistently with the algorithm's model measures(6.2.3)-(6.2.5).
-/

namespace CartisGouldToint
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The source constrained measures(6.1.5), (6.1.7), and(6.1.9), indexed by
orders one through three. The actual direction restrictions use tau times the
requested lower-order tolerances; every measure uses the Euclidean unit ball. -/
noncomputable def constrainedCriticality (f : E → ℝ) (C : Set E) (x : E)
    (τ₁ τ₂ α₁ α₂ : ℝ) : Fin 3 → ℝ :=
  ![TaylorModel.constrainedCriticality f 1 C x 1,
    TaylorModel.tensorCriticality (iteratedFDeriv ℝ 2 f x)
      (TaylorModel.firstRestrictedDirections f (TaylorModel.feasibleDisplacements C x)
        x (τ₁ * α₁)),
    TaylorModel.tensorCriticality (iteratedFDeriv ℝ 3 f x)
      (TaylorModel.secondRestrictedDirections f (TaylorModel.feasibleDisplacements C x)
        x (τ₁ * α₁) (τ₂ * α₂))]

/-- Order one is exactly the actual constrained linear Taylor decrement. -/
@[simp] theorem constrainedCriticality_one (f : E → ℝ) (C : Set E) (x : E)
    (τ₁ τ₂ α₁ α₂ : ℝ) : constrainedCriticality f C x τ₁ τ₂ α₁ α₂ 0 =
      TaylorModel.constrainedCriticality f 1 C x 1 := rfl

/-- Order two uses the actual Hessian on directions with small actual first derivative. -/
@[simp] theorem constrainedCriticality_two (f : E → ℝ) (C : Set E) (x : E)
    (τ₁ τ₂ α₁ α₂ : ℝ) : constrainedCriticality f C x τ₁ τ₂ α₁ α₂ 1 =
      TaylorModel.tensorCriticality (iteratedFDeriv ℝ 2 f x)
        (TaylorModel.firstRestrictedDirections f (TaylorModel.feasibleDisplacements C x)
          x (τ₁ * α₁)) := rfl

/-- Order three uses the actual cubic derivative on both genuine lower derivative restrictions. -/
@[simp] theorem constrainedCriticality_three (f : E → ℝ) (C : Set E) (x : E)
    (τ₁ τ₂ α₁ α₂ : ℝ) : constrainedCriticality f C x τ₁ τ₂ α₁ α₂ 2 =
      TaylorModel.tensorCriticality (iteratedFDeriv ℝ 3 f x)
        (TaylorModel.secondRestrictedDirections f (TaylorModel.feasibleDisplacements C x)
          x (τ₁ * α₁) (τ₂ * α₂)) := rfl

/-- Every source constrained measure is nonnegative at a feasible point when
its lower derivative tolerances are nonnegative, including zero tolerances. -/
theorem constrainedCriticality_nonneg (f : E → ℝ) {C : Set E} {x : E} (hx : x ∈ C)
    {τ₁ τ₂ α₁ α₂ : ℝ} (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) (j : Fin 3) :
    0 ≤ constrainedCriticality f C x τ₁ τ₂ α₁ α₂ j := by
  have hz : (0 : E) ∈ TaylorModel.feasibleDisplacements C x := by simpa using hx
  fin_cases j
  · change 0 ≤ TaylorModel.constrainedCriticality f 1 C x 1
    rw [←TaylorModel.tensorCriticality_one]
    exact TaylorModel.tensorCriticality_nonneg (by decide) _ hz
  · change 0 ≤ TaylorModel.tensorCriticality (iteratedFDeriv ℝ 2 f x)
      (TaylorModel.firstRestrictedDirections f (TaylorModel.feasibleDisplacements C x)
        x (τ₁ * α₁))
    exact TaylorModel.tensorCriticality_nonneg (by decide) _
      (TaylorModel.zero_mem_firstRestrictedDirections hz (mul_nonneg hτ₁ hα₁))
  · change 0 ≤ TaylorModel.tensorCriticality (iteratedFDeriv ℝ 3 f x)
      (TaylorModel.secondRestrictedDirections f (TaylorModel.feasibleDisplacements C x)
        x (τ₁ * α₁) (τ₂ * α₂))
    exact TaylorModel.tensorCriticality_nonneg (by decide) _
      (TaylorModel.zero_mem_secondRestrictedDirections hz
        (mul_nonneg hτ₁ hα₁) (mul_nonneg hτ₂ hα₂))

end CartisGouldToint
