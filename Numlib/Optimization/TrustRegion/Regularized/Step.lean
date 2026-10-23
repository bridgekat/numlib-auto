import Numlib.Optimization.TrustRegion.Regularized.Model
import Numlib.Analysis.Calculus.TaylorModel.SecondOrder
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Interior regularized trust-region steps

The derivative of the actual regularized quadratic model is the quadratic
Taylor derivative plus the Riesz functional of the regularization shift.
The sharp Taylor gradient error gives the trial-gradient estimate and a scalar
quadratic inequality yields a uniform interior-step lower bound.
-/

namespace RegularizedTrustRegion
open TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine derivative of the quadratically regularized Taylor model. -/
theorem hasFDerivAt_model {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (ε : ℝ) (s : E) :
    HasFDerivAt (model f x ε) (quadraticDerivative f x s + ε • innerSL ℝ s) s := by
  have hn := (hasStrictFDerivAt_norm_sq s).hasFDerivAt.const_mul (ε / 2)
  have hd := (hasFDerivAt_eval_two hf s).add hn
  change HasFDerivAt (model f x ε) _ s at hd
  convert hd using 1
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The actual regularized model derivative has the explicit shift formula. -/
theorem fderiv_model {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (ε : ℝ) (s : E) :
    fderiv ℝ (model f x ε) s = quadraticDerivative f x s + ε • innerSL ℝ s :=
  (hasFDerivAt_model hf ε s).fderiv

/-- Actual model stationarity controls the trial derivative, with the regularization
weight multiplying the step norm and the sharp Taylor error multiplying its square. -/
theorem trial_derivative_le {f : E → ℝ} {L θ ε : ℝ}
    (hf : ContDiff ℝ 2 f) (hε : 0 ≤ ε)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (x s : E)
    (hstat : ‖fderiv ℝ (model f x ε) s‖ ≤ θ / 2 * ‖s‖ ^ 2) :
    ‖fderiv ℝ f (x + s)‖ ≤ (L + θ) / 2 * ‖s‖ ^ 2 + ε * ‖s‖ := by
  let R := ε • innerSL ℝ s
  have hR : ‖R‖ = ε * ‖s‖ := by
    simp only [R, norm_smul, Real.norm_of_nonneg hε, innerSL_apply_norm]
  have hid : fderiv ℝ f (x + s) =
      (fderiv ℝ f (x + s) - quadraticDerivative f x s) +
        fderiv ℝ (model f x ε) s - R := by
    rw [fderiv_model hf.contDiffAt]
    dsimp [R]
    abel
  have ht : ‖fderiv ℝ f (x + s)‖ ≤
      ‖fderiv ℝ f (x + s) - quadraticDerivative f x s‖ +
        ‖fderiv ℝ (model f x ε) s‖ + ‖R‖ := by
    calc
      _ = ‖(fderiv ℝ f (x + s) - quadraticDerivative f x s) +
          fderiv ℝ (model f x ε) s - R‖ := congrArg norm hid
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have he := norm_fderiv_sub_quadraticDerivative_le hf hlip x s
  rw [hR] at ht
  linarith

/-- A quadratic upper bound gives the source's minimum-form step lower bound,
including zero gradient and zero quadratic coefficient. -/
theorem min_step_lower {G t ε C : ℝ} (ht : 0 ≤ t)
    (hε : 0 < ε) (hC : 0 ≤ C) (hbound : G ≤ C / 2 * t ^ 2 + ε * t) :
    (Real.sqrt (1 + 2 * C))⁻¹ * min ε (G * ε⁻¹) ≤ t := by
  let R := Real.sqrt (1 + 2 * C)
  have hR : 1 ≤ R := by simpa [R] using Real.one_le_sqrt.mpr (by linarith : 1 ≤ 1 + 2*C)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hRsq : R ^ 2 = 1 + 2 * C := Real.sq_sqrt (by positivity)
  have hcoef : C / 2 ≤ R * (R - 1) := by
    nlinarith [mul_nonneg (show 0 ≤ 3 * R - 1 by linarith) (show 0 ≤ R - 1 by linarith)]
  have hmin : min ε (G * ε⁻¹) ≤ R * t := by
    by_cases hb : ε ≤ R * t
    · exact (min_le_left _ _).trans hb
    · have hb' : R * t ≤ ε := (lt_of_not_ge hb).le
      have h1 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
      have h2 := mul_le_mul_of_nonneg_right hb'
        (show 0 ≤ (R - 1) * t by positivity)
      have hGle : G ≤ (R * t) * ε := by nlinarith
      apply (min_le_right _ _).trans
      rw [← div_eq_mul_inv]
      exact (div_le_iff₀ hε).mpr hGle
  change R⁻¹ * min ε (G * ε⁻¹) ≤ t
  calc
    _ ≤ R⁻¹ * (R * t) := mul_le_mul_of_nonneg_left hmin (inv_nonneg.mpr hRpos.le)
    _ = t := by rw [← mul_assoc, inv_mul_cancel₀ hRpos.ne', one_mul]

/-- A genuine stationary interior-model step has the minimum-form lower bound
in terms of the actual derivative at the trial point. -/
theorem interior_step_lower {f : E → ℝ} {L θ ε : ℝ}
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L) (hθ : 0 ≤ θ) (hε : 0 < ε)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (x s : E)
    (hstat : ‖fderiv ℝ (model f x ε) s‖ ≤ θ / 2 * ‖s‖ ^ 2) :
    (Real.sqrt (1 + 2 * (L + θ)))⁻¹ *
      min ε (‖fderiv ℝ f (x + s)‖ * ε⁻¹) ≤ ‖s‖ :=
  min_step_lower (norm_nonneg _) hε (add_nonneg hL hθ)
    (trial_derivative_le hf hε.le hlip x s hstat)

end RegularizedTrustRegion
