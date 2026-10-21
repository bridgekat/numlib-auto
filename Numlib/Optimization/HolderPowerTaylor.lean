import Numlib.Analysis.SpecialFunctions.RealPowerFactorial
import Numlib.Analysis.Calculus.SymmetricDerivativeNorm
import Numlib.Optimization.RegularizedTaylorCurvature

/-!
# Hölder derivatives and real-power Taylor regularization

Actual continuously differentiable objectives carry their highest derivative's diagonal
Hölder bound. Symmetry identifies this with the operator bound needed by the sharp Taylor
remainder. Finite-product factorials normalize all value, gradient and Hessian estimates.
-/

noncomputable section
namespace Optimization
open RegularizedTaylorModel
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Continuous finite smoothness together with diagonal Hölder control of its highest
actual derivative. Exponent zero controls oscillation and adds no continuity assertion. -/
structure HolderDerivative (f : E → ℝ) (p : ℕ) (H β : ℝ) : Prop where
  smooth : ContDiff ℝ p f
  constant_nonneg : 0 ≤ H
  exponent_nonneg : 0 ≤ β
  exponent_le_one : β ≤ 1
  bound : ∀ x y, (iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y).diagonalNorm ≤
    H * ‖x - y‖ ^ β

variable {f : E → ℝ} {p : ℕ} {H β : ℝ}

/-- Symmetry converts diagonal Hölder control into the same operator-norm bound. -/
theorem HolderDerivative.norm_sub_le (hf : HolderDerivative f p H β) (hp : 1 ≤ p)
    (x y : E) : ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ H * ‖x - y‖ ^ β := by
  rw [← diagonalNorm_iteratedFDeriv_sub_eq_norm hf.smooth.contDiffAt hf.smooth.contDiffAt
    (by omega : 0 < p)]
  exact hf.bound x y

/-- Every actual Taylor derivative has the sharp shifted-factorial Hölder remainder. -/
theorem HolderDerivative.norm_iteratedFDeriv_sub_taylorModel_le
    (hf : HolderDerivative f p H β) (hp : 1 ≤ p) {j : ℕ} (hj : j ≤ p) (x s : E) :
    ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (taylorModel f p x) s‖ ≤
      H / Real.powerFactorial ((p : ℝ) + β - j) * ‖s‖ ^ ((p : ℝ) + β - j) := by
  have he : ((p - j : ℕ) : ℝ) + β = (p : ℝ) + β - j := by
    rw [Nat.cast_sub hj]
    ring
  rw [← he, Real.powerFactorial_nat_add hf.exponent_nonneg hf.exponent_le_one]
  apply norm_iteratedFDeriv_sub_taylorModel_le_holder hj hf.exponent_nonneg
    (fun _ _ => hf.smooth.contDiffAt)
  intro t _
  simpa only [add_sub_cancel_left] using hf.norm_sub_le hp (x + t • s) x

/-- The value remainder uses the finite-product factorial at the total smoothness exponent. -/
theorem HolderDerivative.norm_sub_taylorModel_le (hf : HolderDerivative f p H β)
    (hp : 1 ≤ p) (x s : E) :
    ‖f (x + s) - taylorModel f p x s‖ ≤
      H / Real.powerFactorial ((p : ℝ) + β) * ‖s‖ ^ ((p : ℝ) + β) := by
  simpa only [Nat.cast_zero, sub_zero, norm_iteratedFDeriv_zero_sub] using
    hf.norm_iteratedFDeriv_sub_taylorModel_le hp (Nat.zero_le p) x s

/-- The actual first derivative has the shifted-factorial Taylor remainder. -/
theorem HolderDerivative.norm_fderiv_sub_taylorModel_le (hf : HolderDerivative f p H β)
    (hp : 1 ≤ p) (x s : E) :
    ‖fderiv ℝ f (x + s) - fderiv ℝ (taylorModel f p x) s‖ ≤
      H / Real.powerFactorial ((p : ℝ) + β - 1) * ‖s‖ ^ ((p : ℝ) + β - 1) := by
  have h := hf.norm_iteratedFDeriv_sub_taylorModel_le hp hp x s
  rw [norm_iteratedFDeriv_sub_eq_fderiv_sub, norm_iteratedFDeriv_zero_sub] at h
  simpa only [Nat.cast_one] using h

/-- The actual Hessian has the shifted-factorial Taylor remainder. -/
theorem HolderDerivative.norm_hessian_sub_taylorModel_le (hf : HolderDerivative f p H β)
    (hp : 2 ≤ p) (x s : E) :
    ‖fderiv ℝ (fderiv ℝ f) (x + s) - fderiv ℝ (fderiv ℝ (taylorModel f p x)) s‖ ≤
      H / Real.powerFactorial ((p : ℝ) + β - 2) * ‖s‖ ^ ((p : ℝ) + β - 2) := by
  have h := hf.norm_iteratedFDeriv_sub_taylorModel_le (by omega) hp x s
  rw [norm_iteratedFDeriv_sub_eq_fderiv_sub, norm_iteratedFDeriv_sub_eq_fderiv_sub,
    norm_iteratedFDeriv_zero_sub] at h
  exact h

/-- Actual model residuals control the trial gradient, with the exact real-power coefficient. -/
theorem HolderDerivative.trial_fderiv_bound (hf : HolderDerivative f p H β)
    (hp : 1 ≤ p) {r sigma theta : ℝ} (hr : 1 < r) (hsigma : 0 ≤ sigma) (x s : E)
    (hm : ‖fderiv ℝ (regularizedModel f p x sigma (Real.powerFactorial r) r) s‖ ≤
      theta * ‖s‖ ^ (r - 1)) :
    ‖fderiv ℝ f (x + s)‖ ≤
      H / Real.powerFactorial ((p : ℝ) + β - 1) * ‖s‖ ^ ((p : ℝ) + β - 1) +
        (sigma / Real.powerFactorial (r - 1) + theta) * ‖s‖ ^ (r - 1) := by
  have h := fderiv_step_lower_bound hsigma (Real.powerFactorial_pos (by linarith : 0 ≤ r))
    hr (hf.norm_fderiv_sub_taylorModel_le hp x s) hm
  rwa [Real.div_powerFactorial_mul hr.le] at h

/-- Actual model curvature controls the objective in every direction, with the exact
second derivative coefficient of the real-power regularizer. -/
theorem HolderDerivative.trial_curvature_bound (hf : HolderDerivative f p H β)
    (hp : 2 ≤ p) {r sigma theta : ℝ} (hr : 2 < r) (hsigma : 0 ≤ sigma) (x s u : E)
    (hm : -(theta * ‖s‖ ^ (r - 2)) * ‖u‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (regularizedModel f p x sigma (Real.powerFactorial r) r)) s u u) :
    -(H / Real.powerFactorial ((p : ℝ) + β - 2) * ‖s‖ ^ ((p : ℝ) + β - 2) +
      (sigma / Real.powerFactorial (r - 2) + theta) * ‖s‖ ^ (r - 2)) * ‖u‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ f) (x + s) u u := by
  have h := curvature_step_lower_bound hsigma (Real.powerFactorial_pos (by linarith : 0 ≤ r))
    hr (hf.norm_hessian_sub_taylorModel_le hp x s) hm
  rwa [Real.div_powerFactorial_mul_mul hr.le] at h

end Optimization
