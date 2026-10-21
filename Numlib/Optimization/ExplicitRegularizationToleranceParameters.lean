import Numlib.Optimization.ExplicitRegularization
import Numlib.Optimization.InexactRegularizationRun

/-!
# Varying tolerances with fixed explicit-accuracy controls

Tolerance replacement retains every implicit control and both endpoint-error allowances.
This lets complexity constants be chosen before the requested tolerance vector.
-/

namespace Optimization.ExplicitRegularization

/-- Replace the requested tolerances alone, retaining all algorithm controls and the two
inequalities that pay for endpoint errors in acceptance and very successful trials. -/
def Parameters.withTolerances (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) : Parameters where
  toImplicitParameters := P.toImplicitParameters.withTolerances ε hpos hlt
  step_acceptance := P.step_acceptance
  step_success := P.step_success

/-- The implicit projection is exactly the implicit tolerance replacement. -/
@[simp] theorem Parameters.withTolerances_toImplicitParameters (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).toImplicitParameters =
      P.toImplicitParameters.withTolerances ε hpos hlt := rfl

/-- Tolerance replacement supplies precisely the requested vector. -/
@[simp] theorem Parameters.withTolerances_epsilon (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).epsilon = ε := rfl

/-- The fixed model degree is unchanged. -/
@[simp] theorem Parameters.withTolerances_p (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).p = P.p := rfl

/-- The fixed tested order is unchanged. -/
@[simp] theorem Parameters.withTolerances_q (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).q = P.q := rfl

/-- All regularization update controls are unchanged. -/
@[simp] theorem Parameters.withTolerances_updates (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).toImplicitParameters.toParameters.toRegularizationParameters =
      P.toImplicitParameters.toParameters.toRegularizationParameters := rfl

end Optimization.ExplicitRegularization
