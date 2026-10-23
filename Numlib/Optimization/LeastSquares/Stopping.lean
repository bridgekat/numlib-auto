import Numlib.Optimization.LeastSquares.Measures

/-!
# Actual normalized residual-power stopping predicates

The literal finite-third-order test contains its printed nonempty-direction
guard. The repaired predicate removes only that guard and retains the global
residual test and every normalized actual derivative test.
-/

namespace LeastSquares
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
/-- Literal finite-third-order ARpLE stopping, including the printed nonempty-direction guard. -/
def literalFiniteStop (r : E → F) (ℓ : ℝ) (x : E) (μ : ℝ) (M : Set E)
    (ε₀ ε₁ ε₂ ε₃ : ℝ) : Prop :=
  ‖r x‖ ≤ ε₀ ∨ (firstMeasure r ℓ x ≤ ε₁ ∧
    (ε₂ < secondMeasure r ℓ x μ ∨ (-ε₂ ≤ secondMeasure r ℓ x μ ∧ M.Nonempty ∧
      ∀ v ∈ M, thirdMeasure r ℓ x v ≤ ε₃ ∧
        directionalSecondMeasure r ℓ x v ≤ ε₂)))

/-- Repaired finite-third-order ARpLE stopping removes only the nonempty-direction guard. -/
def finiteStop (r : E → F) (ℓ : ℝ) (x : E) (μ : ℝ) (M : Set E)
    (ε₀ ε₁ ε₂ ε₃ : ℝ) : Prop :=
  ‖r x‖ ≤ ε₀ ∨ (firstMeasure r ℓ x ≤ ε₁ ∧
    (ε₂ < secondMeasure r ℓ x μ ∨ (-ε₂ ≤ secondMeasure r ℓ x μ ∧
      ∀ v ∈ M, thirdMeasure r ℓ x v ≤ ε₃ ∧
        directionalSecondMeasure r ℓ x v ≤ ε₂)))

/-- Every literal stopping point satisfies the repaired true derivative tests. -/
theorem finiteStop_of_literal {r : E → F} {ℓ : ℝ} {x : E} {μ ε₀ ε₁ ε₂ ε₃ : ℝ}
    {M : Set E} (h : literalFiniteStop r ℓ x μ M ε₀ ε₁ ε₂ ε₃) :
    finiteStop r ℓ x μ M ε₀ ε₁ ε₂ ε₃ := by
  rcases h with hr | ⟨hfirst, hsecond | ⟨hsecond, _, hthird⟩⟩
  · exact Or.inl hr
  · exact Or.inr ⟨hfirst, Or.inl hsecond⟩
  · exact Or.inr ⟨hfirst, Or.inr ⟨hsecond, hthird⟩⟩

/-- The source and repaired stopping predicates agree whenever the inherited set is nonempty. -/
theorem literalFiniteStop_iff_of_nonempty {r : E → F} {ℓ : ℝ} {x : E}
    {μ ε₀ ε₁ ε₂ ε₃ : ℝ} {M : Set E} (hM : M.Nonempty) :
    literalFiniteStop r ℓ x μ M ε₀ ε₁ ε₂ ε₃ ↔
      finiteStop r ℓ x μ M ε₀ ε₁ ε₂ ε₃ := by
  simp only [literalFiniteStop, finiteStop, hM, true_and]
end LeastSquares