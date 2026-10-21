import Numlib.Analysis.Calculus.NormRpowHessian
import Numlib.Optimization.TaylorModelRemainder

/-!
# Curvature transfer for regularized Taylor models

The model Hessian is the Taylor Hessian plus the genuine Hessian of the radial
regularizer. Operator remainder bounds and model lower curvature bounds therefore
transfer to the objective in arbitrary directions.
-/

open scoped ContDiff

namespace Optimization.RegularizedTaylorModel

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sharp operator bound for the genuine Hessian of a radial power. -/
theorem hessian_norm_power_bound {r : ℝ} (hr : 2 < r) (s : E) :
    ‖fderiv ℝ (fderiv ℝ (fun z : E ↦ ‖z‖ ^ r)) s‖ ≤
      r * (r - 1) * ‖s‖ ^ (r - 2) := by
  rw [fderiv_fderiv_norm_rpow hr]
  exact norm_normRpowHessian_le hr s

/-- The model Hessian decomposes into Taylor and radial Hessians at every step. -/
theorem hessian_regularizedModel (f : E → ℝ) (p : ℕ) (x s : E)
    (sigma c : ℝ) {r : ℝ} (hr : 2 < r) :
    fderiv ℝ (fderiv ℝ (regularizedModel f p x sigma c r)) s =
      fderiv ℝ (fderiv ℝ (taylorModel f p x)) s + (sigma / c) • normRpowHessian r s := by
  have hT : Differentiable ℝ (fderiv ℝ (taylorModel f p x)) :=
    ((contDiff_taylorModel f p x 2).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)
  have heq : fderiv ℝ (regularizedModel f p x sigma c r) =
      fun z ↦ fderiv ℝ (taylorModel f p x) z +
        (sigma / c) • fderiv ℝ (fun y : E ↦ ‖y‖ ^ r) z := by
    funext z
    exact fderiv_regularizedModel f p x z sigma c (by linarith)
  rw [heq]
  exact ((hT s).hasFDerivAt.add
    ((hasFDerivAt_fderiv_norm_rpow hr s).const_smul (sigma / c))).fderiv

/-- A Hessian remainder and a model lower curvature bound transfer to the objective.
All directions are allowed, including subspaces, by applying this result only there. -/
theorem curvature_step_lower_bound {f : E → ℝ} {p : ℕ} {x s u : E}
    {sigma c r R theta : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 < c) (hr : 2 < r)
    (hrem : ‖fderiv ℝ (fderiv ℝ f) (x + s) -
      fderiv ℝ (fderiv ℝ (taylorModel f p x)) s‖ ≤ R)
    (hmodel : -(theta * ‖s‖ ^ (r - 2)) * ‖u‖ ^ (2 : ℕ) ≤
      fderiv ℝ (fderiv ℝ (regularizedModel f p x sigma c r)) s u u) :
    -(R + (sigma / c * r * (r - 1) + theta) * ‖s‖ ^ (r - 2)) *
      ‖u‖ ^ (2 : ℕ) ≤ fderiv ℝ (fderiv ℝ f) (x + s) u u := by
  have hR := (ContinuousLinearMap.abs_apply_self_le
    (fderiv ℝ (fderiv ℝ f) (x + s) -
      fderiv ℝ (fderiv ℝ (taylorModel f p x)) s) u).trans
        (mul_le_mul_of_nonneg_right hrem (sq_nonneg ‖u‖))
  have hrad := abs_normRpowHessian_apply_self_le hr s u
  have hrad' : (sigma / c) * normRpowHessian r s u u ≤
      sigma / c * (r * (r - 1) * ‖s‖ ^ (r - 2) * ‖u‖ ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hrad) (div_nonneg hsigma hc.le)
  rw [hessian_regularizedModel _ _ _ _ _ _ hr] at hmodel
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul] at hR hmodel
  have hR' := (abs_le.mp hR).1
  nlinarith [hrad']

/-- Sharp Hölder control of the genuine, curried Hessian Taylor remainder. -/
theorem norm_hessian_sub_taylorModel_le_holder {f : E → ℝ} {p : ℕ} {x s : E} {H beta : ℝ}
    (hp : 2 ≤ p) (hbeta : 0 ≤ beta)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ p f (x + t • s))
    (hH : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ p f (x + t • s) - iteratedFDeriv ℝ p f x‖ ≤ H * ‖t • s‖ ^ beta) :
    ‖fderiv ℝ (fderiv ℝ f) (x + s) -
        fderiv ℝ (fderiv ℝ (taylorModel f p x)) s‖ ≤
      H / (∏ i ∈ Finset.range (p - 2), (((i + 1 : ℕ) : ℝ) + beta)) *
        ‖s‖ ^ (((p - 2 : ℕ) : ℝ) + beta) := by
  have h := norm_iteratedFDeriv_sub_taylorModel_le_holder (j := 2) hp hbeta hf hH
  rw [norm_iteratedFDeriv_sub_eq_fderiv_sub, norm_iteratedFDeriv_sub_eq_fderiv_sub,
    norm_iteratedFDeriv_zero_sub] at h
  exact h

/-- The cubic regularizer contributes at most `sigma * ‖s‖` to the Hessian norm. -/
theorem hessian_cubic_regularizer_bound (sigma : ℝ) (hsigma : 0 ≤ sigma) (s : E) :
    ‖fderiv ℝ (fderiv ℝ (fun z : E ↦ sigma / 6 * ‖z‖ ^ (3 : ℝ))) s‖ ≤ sigma * ‖s‖ := by
  have he : fderiv ℝ (fun z : E ↦ sigma / 6 * ‖z‖ ^ (3 : ℝ)) =
      fun z ↦ (sigma / 6) • fderiv ℝ (fun y : E ↦ ‖y‖ ^ (3 : ℝ)) z := by
    funext z
    convert! fderiv_const_smul (differentiable_norm_rpow (by norm_num : (1 : ℝ) < 3) z)
        (sigma / 6) using 1
  rw [he]
  change ‖fderiv ℝ ((sigma / 6) • fderiv ℝ (fun y : E ↦ ‖y‖ ^ (3 : ℝ))) s‖ ≤ _
  rw [((hasFDerivAt_fderiv_norm_rpow (by norm_num : (2 : ℝ) < 3) s).const_smul
    (sigma / 6)).fderiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ sigma / 6 * (3 * (3 - 1) * ‖s‖ ^ ((3 : ℝ) - 2)) :=
      mul_le_mul_of_nonneg_left (norm_normRpowHessian_le (by norm_num) s) (by positivity)
    _ = _ := by norm_num; ring

/-- The cubic model curvature condition gives an objective Hessian lower bound. -/
theorem cubic_curvature_step_lower_bound {f : E → ℝ} {x s u : E} {sigma L theta : ℝ}
    (hsigma : 0 ≤ sigma)
    (hrem : ‖fderiv ℝ (fderiv ℝ f) (x + s) -
      fderiv ℝ (fderiv ℝ (taylorModel f 2 x)) s‖ ≤ L * ‖s‖)
    (hmodel : -(theta * ‖s‖) * ‖u‖ ^ (2 : ℕ) ≤
      fderiv ℝ (fderiv ℝ (regularizedModel f 2 x sigma 6 3)) s u u) :
    -((L + sigma + theta) * ‖s‖) * ‖u‖ ^ (2 : ℕ) ≤
      fderiv ℝ (fderiv ℝ f) (x + s) u u := by
  have h := curvature_step_lower_bound (u := u) (theta := theta) hsigma (by norm_num : (0 : ℝ) < 6)
    (by norm_num : (2 : ℝ) < 3) hrem (by norm_num at *; exact hmodel)
  convert h using 1
  norm_num
  ring

/-- A quadratic Taylor model has the objective Hessian at the expansion point. -/
theorem hessian_taylorModel_two {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (s : E) :
    fderiv ℝ (fderiv ℝ (taylorModel f 2 x)) s = fderiv ℝ (fderiv ℝ f) x := by
  have he : fderiv ℝ (taylorModel f 2 x) = taylorModel (fderiv ℝ f) 1 x := by
    funext z
    exact fderiv_taylorModel_eq_taylorModel_fderiv hf z
  rw [he, fderiv_taylorModel_eq_taylorModel_fderiv (p := 0)
    (hf.fderiv_right (by norm_num)) s]
  simp

/-- With a genuine objective Hessian Lipschitz bound, approximate model curvature
implies the cubic objective curvature estimate. -/
theorem cubic_curvature_step_lower_bound_of_lipschitz {f : E → ℝ} {x s u : E}
    {sigma L theta : ℝ} (hsigma : 0 ≤ sigma) (hf : ContDiffAt ℝ 2 f x)
    (hL : ‖fderiv ℝ (fderiv ℝ f) (x + s) - fderiv ℝ (fderiv ℝ f) x‖ ≤ L * ‖s‖)
    (hmodel : -(theta * ‖s‖) * ‖u‖ ^ (2 : ℕ) ≤
      fderiv ℝ (fderiv ℝ (regularizedModel f 2 x sigma 6 3)) s u u) :
    -((L + sigma + theta) * ‖s‖) * ‖u‖ ^ (2 : ℕ) ≤
      fderiv ℝ (fderiv ℝ f) (x + s) u u := by
  apply cubic_curvature_step_lower_bound hsigma _ hmodel
  simpa only [hessian_taylorModel_two hf s] using hL

/-- Negative curvature of magnitude `epsilon` in a unit direction forces a cubic step
of length at least `epsilon / (L + sigmaMax + theta)`. -/
theorem cubic_step_norm_lower_bound_of_negative_curvature {f : E → ℝ} {x s u : E}
    {sigma sigmaMax L theta epsilon : ℝ} (hsigma : 0 ≤ sigma)
    (hsigmaMax : sigma ≤ sigmaMax) (hden : 0 < L + sigmaMax + theta)
    (hf : ContDiffAt ℝ 2 f x)
    (hL : ‖fderiv ℝ (fderiv ℝ f) (x + s) - fderiv ℝ (fderiv ℝ f) x‖ ≤ L * ‖s‖)
    (hu : ‖u‖ = 1)
    (hmodel : -(theta * ‖s‖) ≤
      fderiv ℝ (fderiv ℝ (regularizedModel f 2 x sigma 6 3)) s u u)
    (hneg : fderiv ℝ (fderiv ℝ f) (x + s) u u ≤ -epsilon) :
    epsilon / (L + sigmaMax + theta) ≤ ‖s‖ := by
  have h := cubic_curvature_step_lower_bound_of_lipschitz hsigma hf hL
    (u := u) (theta := theta) (by simpa [hu] using hmodel)
  rw [hu] at h
  simp only [one_pow, mul_one] at h
  rw [div_le_iff₀ hden]
  have hm := mul_le_mul_of_nonneg_right hsigmaMax (norm_nonneg s)
  nlinarith

end Optimization.RegularizedTaylorModel
