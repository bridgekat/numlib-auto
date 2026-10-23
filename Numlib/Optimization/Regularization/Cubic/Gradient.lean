import Numlib.Optimization.Regularization.Cubic.Parameter
import Numlib.Analysis.Calculus.TaylorModel.SecondOrder
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Cubic-model derivatives and step-length bounds

The gradient bound is imposed on the actual cubic model. Its derivative is
proved from finite second-order Schwarz symmetry and the norm-power derivative,
including zero steps. The sharp Taylor gradient error controls the trial gradient.
-/

namespace CubicRegularization

open TaylorModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Derivative of the genuine cubic regularization model. -/
theorem hasFDerivAt_model {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (σ : ℝ) (s : E) :
    HasFDerivAt (model f x σ)
      (quadraticDerivative f x s + (σ / 2 * ‖s‖) • innerSL ℝ s) s := by
  have hn := (hasFDerivAt_norm_rpow s (p := 3) (by norm_num)).const_mul (σ / 6)
  have hd := (hasFDerivAt_eval_two hf s).add hn
  have heq : (fun y => eval f 2 x y + σ / 6 * ‖y‖ ^ (3 : ℝ)) = model f x σ := by
    ext y
    norm_num [model, ModelDecrease.penalized, Real.rpow_natCast]
  change HasFDerivAt (fun y => eval f 2 x y + σ / 6 * ‖y‖ ^ (3 : ℝ)) _ s at hd
  rw [heq] at hd
  convert hd using 1
  ext v
  norm_num [add_apply, smul_apply, Real.rpow_one, smul_eq_mul]
  ring

/-- The actual Fréchet derivative has the explicit cubic-gradient formula. -/
theorem fderiv_model {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (σ : ℝ) (s : E) :
    fderiv ℝ (model f x σ) s =
      quadraticDerivative f x s + (σ / 2 * ‖s‖) • innerSL ℝ s :=
  (hasFDerivAt_model hf σ s).fderiv

/-- First-order model stationarity and a sharp Hessian Lipschitz bound control
the derivative at the actual trial point. -/
theorem trial_derivative_le {f : E → ℝ} {L θ σ : ℝ}
    (hf : ContDiff ℝ 2 f) (hσ : 0 ≤ σ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (x s : E) (hstat : ‖fderiv ℝ (model f x σ) s‖ ≤ θ / 2 * ‖s‖ ^ 2) :
    ‖fderiv ℝ f (x + s)‖ ≤ (L + θ + σ) / 2 * ‖s‖ ^ 2 := by
  let R := (σ / 2 * ‖s‖) • innerSL ℝ s
  have hR : ‖R‖ = σ / 2 * ‖s‖ ^ 2 := by
    dsimp [R]
    rw [norm_smul, Real.norm_of_nonneg (by positivity), innerSL_apply_norm]
    ring
  have hid : fderiv ℝ f (x + s) =
      (fderiv ℝ f (x + s) - quadraticDerivative f x s) +
        fderiv ℝ (model f x σ) s - R := by
    rw [fderiv_model hf.contDiffAt]
    dsimp [R]
    abel
  have ht : ‖fderiv ℝ f (x + s)‖ ≤
      ‖fderiv ℝ f (x + s) - quadraticDerivative f x s‖ +
        ‖fderiv ℝ (model f x σ) s‖ + ‖R‖ := by
    calc
      _ = ‖(fderiv ℝ f (x + s) - quadraticDerivative f x s) +
          fderiv ℝ (model f x σ) s - R‖ := congrArg norm hid
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have he := norm_fderiv_sub_quadraticDerivative_le hf hlip x s
  rw [hR] at ht
  linarith

/-- Uniform parameter bounds convert first-order stationarity of the actual
cubic model into a lower bound on the trial step length. -/
theorem ModelTrace.step_length_lower {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ : ℝ} {N : ℕ}
    (h : ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L) (hθ : 0 ≤ θ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N)
    (hstat : ‖fderiv ℝ (model f (x i) (σ i)) (s i)‖ ≤ θ / 2 * ‖s i‖ ^ 2) :
    2 / (L + θ + max (σ 0) (γ₃ * L / (1 - η₂))) *
      ‖fderiv ℝ f (x i + s i)‖ ≤ ‖s i‖ ^ 2 := by
  have hσ := h.updates.pos (show i ≤ N by omega)
  have hmax := h.parameter_le hf hL hlip (i := i) (by omega)
  have hmaxpos : 0 < max (σ 0) (γ₃ * L / (1 - η₂)) :=
    h.updates.pos (Nat.zero_le N) |>.trans_le (le_max_left _ _)
  have hden : 0 < L + θ + max (σ 0) (γ₃ * L / (1 - η₂)) := by positivity
  have hb := trial_derivative_le hf hσ.le hlip (x i) (s i) hstat
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_right hmax (sq_nonneg ‖s i‖)]

end CubicRegularization
