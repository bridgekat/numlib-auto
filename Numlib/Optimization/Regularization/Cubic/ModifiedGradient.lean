import Numlib.Optimization.Regularization.Cubic.Gradient

/-!
# Modified quadratic stationarity for cubic regularization

The alternative step test bounds the actual derivative of the quadratic Taylor
polynomial by a multiple of the current cubic penalty parameter. The sharp true
Hessian Lipschitz error and the operational parameter bound then yield the modified
step-length estimate. Exact cubic stationarity satisfies the alternative test.
-/

namespace CubicRegularization
open TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The modified first-order step condition on the actual quadratic Taylor polynomial. -/
def ModifiedFirstOrderStationary (f : E → ℝ) (x s : E) (σ θ : ℝ) : Prop :=
  ‖fderiv ℝ (eval f 2 x) s‖ ≤ θ * σ / 2 * ‖s‖ ^ 2

/-- The modified step condition uses the genuine quadratic-model derivative. -/
theorem modifiedFirstOrderStationary_iff {f : E → ℝ} {x s : E} {σ θ : ℝ}
    (hf : ContDiffAt ℝ 2 f x) :
    ModifiedFirstOrderStationary f x s σ θ ↔
      ‖quadraticDerivative f x s‖ ≤ θ * σ / 2 * ‖s‖ ^ 2 := by
  rw [ModifiedFirstOrderStationary, (hasFDerivAt_eval_two hf s).fderiv]

/-- Exact first-order stationarity of the actual cubic model satisfies the modified
step test for every multiplier at least one, including the zero step. -/
theorem modifiedFirstOrderStationary_of_stationary {f : E → ℝ} {x s : E} {σ θ : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hσ : 0 ≤ σ) (hθ : 1 ≤ θ)
    (hstat : fderiv ℝ (model f x σ) s = 0) :
    ModifiedFirstOrderStationary f x s σ θ := by
  apply (modifiedFirstOrderStationary_iff hf).2
  have he : quadraticDerivative f x s = -((σ / 2 * ‖s‖) • innerSL ℝ s) := by
    rw [fderiv_model hf] at hstat
    exact eq_neg_of_add_eq_zero_left hstat
  rw [he, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity), innerSL_apply_norm]
  have hh := mul_le_mul_of_nonneg_right hθ (by positivity : 0 ≤ σ * ‖s‖ ^ 2)
  nlinarith

/-- The modified step test controls the actual derivative at the trial point. -/
theorem trial_derivative_le_of_modified {f : E → ℝ} {L θ σ : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (x s : E) (hstat : ModifiedFirstOrderStationary f x s σ θ) :
    ‖fderiv ℝ f (x + s)‖ ≤ (L + θ * σ) / 2 * ‖s‖ ^ 2 := by
  have hs := (modifiedFirstOrderStationary_iff hf.contDiffAt).1 hstat
  have he := norm_fderiv_sub_quadraticDerivative_le hf hlip x s
  have ht := norm_add_le (fderiv ℝ f (x + s) - quadraticDerivative f x s)
    (quadraticDerivative f x s)
  rw [sub_add_cancel] at ht
  linarith

/-- The genuine AR2 parameter trace supplies the uniform modified step bound. -/
theorem ModelTrace.step_length_lower_of_modified {f : E → ℝ} {x s : ℕ → E}
    {σ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ : ℝ} {N : ℕ}
    (h : ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L) (hθ : 0 < θ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hstat : ModifiedFirstOrderStationary f (x i) (s i) (σ i) θ) :
    2 / (L + θ * max (σ 0) (γ₃ * L / (1 - η₂))) * ‖fderiv ℝ f (x i + s i)‖ ≤
      ‖s i‖ ^ 2 := by
  have hmax := h.parameter_le hf hL hlip (i := i) (by omega)
  have hmaxpos : 0 < max (σ 0) (γ₃ * L / (1 - η₂)) :=
    h.updates.pos (Nat.zero_le N) |>.trans_le (le_max_left _ _)
  have hden : 0 < L + θ * max (σ 0) (γ₃ * L / (1 - η₂)) := by positivity
  have hb := trial_derivative_le_of_modified hf hlip (x i) (s i) hstat
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmax hθ.le) (sq_nonneg ‖s i‖)]
end CubicRegularization
