import Numlib.Optimization.CubicModelMinimizer
import Numlib.Optimization.CubicSecondOrder

/-!
# Exact sharp cubic traces

Constant regularization parameters and actual global model minima give a reusable
second-order adaptive cubic trace when every objective acceptance ratio is very successful.
-/
noncomputable section
namespace Optimization.CubicRegularization
/-- Fixed positive AR2 parameters used for the sharp gradient and curvature witnesses. -/
def sharpParameters : ParameterUpdates.RegularizationParameters where
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 1
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := by norm_num

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact global model minimizers with very successful objective ratios give a lawful
second-order cubic run at a constant regularization parameter. -/
theorem secondOrderRun_of_global_minimizers
    (p : ParameterUpdates.RegularizationParameters) {θ₁ θ₂ σ : ℝ}
    (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hσ : p.sigmaMin ≤ σ)
    {f : E → ℝ} {x s : ℕ → E} (hf : ContDiff ℝ 2 f)
    (hmin : ∀ k, IsMinOn (cubicModel f (x k) σ) Set.univ (s k))
    (hratio : ∀ k, p.eta2 ≤ ratio f (x k) (s k) σ)
    (hstep : ∀ k, x (k + 1) = x k + s k) :
    SecondOrderRun p θ₁ θ₂ f x s (fun _ => σ) := by
  have hσpos : 0 < σ := p.sigmaMin_pos.trans_le hσ
  constructor
  · constructor
    · constructor
      · constructor
        · exact hσ
        · intro k
          rw [ite_eq_left (hratio k)]
          exact ⟨max_le hσ (mul_le_of_le_one_left hσpos.le p.gamma1_lt_one.le), le_rfl⟩
      · intro k
        exact decrease_or_eq_zero_of_isMinOn_cubicModel hf.contDiffAt hσpos (hmin k)
      · intro k
        rw [ite_eq_left (p.eta_le.trans (hratio k))]
        exact hstep k
    · intro k
      rw [fderiv_eq_zero_of_isMinOn_cubicModel (hmin k), norm_zero]
      positivity
  · intro k u
    have hh := hessian_nonneg_of_isMinOn_cubicModel (hmin k) u
    have hn : -(θ₂ * ‖s k‖) * ‖u‖ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg hθ₂ (norm_nonneg _))) (sq_nonneg _)
    exact hn.trans hh

end Optimization.CubicRegularization
