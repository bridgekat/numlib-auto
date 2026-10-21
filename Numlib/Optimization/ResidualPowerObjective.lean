import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Powers of residual norms

The objective is defined for real exponents. Zero residuals are handled before division in
criticality tests. Smoothness is proved through the squared norm and never through the norm
at zero.
-/

noncomputable section
namespace Optimization

variable {E F : Type*} [NormedAddCommGroup F]

/-- The real-power least-norm objective associated with a residual map. -/
def residualPowerObjective (r : E → F) (ell : ℝ) (x : E) : ℝ := ‖r x‖ ^ ell / ell

/-- A nonnegative denominator gives a nonnegative objective. -/
theorem residualPowerObjective_nonneg (r : E → F) {ell : ℝ} (hell : 0 ≤ ell) (x : E) :
    0 ≤ residualPowerObjective r ell x := div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hell

/-- A positive power vanishes at every zero residual. -/
theorem residualPowerObjective_eq_zero {r : E → F} {ell : ℝ} (hell : 0 < ell) {x : E}
    (hx : r x = 0) : residualPowerObjective r ell x = 0 := by
  simp [residualPowerObjective, hx, Real.zero_rpow hell.ne']

/-- Every zero residual is a global minimum of the actual objective. -/
theorem isMinOn_residualPowerObjective_of_zero {r : E → F} {ell : ℝ} (hell : 0 < ell)
    {x : E} (hx : r x = 0) : IsMinOn (residualPowerObjective r ell) Set.univ x := by
  intro y _
  rw [residualPowerObjective_eq_zero hell hx]
  exact residualPowerObjective_nonneg r hell.le y

/-- Squared norm factorization, valid also at zero. -/
theorem residualPowerObjective_eq_sq_norm_rpow (r : E → F) (ell : ℝ) (x : E) :
    residualPowerObjective r ell x = (‖r x‖ ^ 2) ^ (ell / 2) / ell := by
  rw [residualPowerObjective, ← Real.rpow_natCast_mul (norm_nonneg _)]
  congr 2
  push_cast
  ring

section Smooth
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ F]
  {r : E → F} {p : ℕ}

/-- Even natural powers inherit every order of residual smoothness. -/
theorem contDiff_residualPowerObjective_even (hr : ContDiff ℝ p r) (k : ℕ) :
    ContDiff ℝ p (residualPowerObjective r (2 * (k : ℝ))) := by
  have h : ContDiff ℝ p (fun x => (‖r x‖ ^ 2) ^ k / (2 * (k : ℝ))) :=
    (((contDiff_norm_sq ℝ).comp hr).pow k).div_const _
  convert h using 1
  funext x
  rw [residualPowerObjective_eq_sq_norm_rpow]
  simp

/-- Exponents at least twice the derivative order are smooth through the squared norm. -/
theorem contDiff_residualPowerObjective_of_two_mul_le (hr : ContDiff ℝ p r) {ell : ℝ}
    (hell : 2 * (p : ℝ) ≤ ell) : ContDiff ℝ p (residualPowerObjective r ell) := by
  have h : ContDiff ℝ p (fun x => (‖r x‖ ^ 2) ^ (ell / 2) / ell) :=
    ((Real.contDiff_rpow_const_of_le (by linarith : (p : ℝ) ≤ ell / 2)).comp
      ((contDiff_norm_sq ℝ).comp hr)).div_const ell
  convert h using 1
  funext x
  exact residualPowerObjective_eq_sq_norm_rpow r ell x

end Smooth
end Optimization
