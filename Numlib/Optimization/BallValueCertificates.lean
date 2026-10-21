import Mathlib.Analysis.Normed.Module.Basic

/-!
# Feasible radial trial points

Radially rescaling any boundary point produces a feasible trial point on another ball,
which can be used to certify upper bounds on its minimum value.
-/

namespace Optimization
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  {t : E} {δ ε : ℝ}

/-- A positive-radius boundary point rescales to any nonnegative target radius. -/
theorem norm_rescale_boundary (hδ : 0 ≤ δ) (hε : 0 < ε) (ht : ‖t‖ = ε) :
    ‖(δ / ε) • t‖ = δ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hδ hε.le), ht,
    div_mul_cancel₀ _ hε.ne']

end Optimization
