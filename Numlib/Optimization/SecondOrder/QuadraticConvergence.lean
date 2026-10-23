import Numlib.Optimization.SecondOrder.ShiftedNewton

/-!
# Step lengths under quadratic gradient convergence

A global Lipschitz bound on the actual gradient bounds the true Riesz Hessian.
A bounded nonnegative shift and relative residual bound then make the current
gradient norm no larger than a fixed multiple of the step length. Quadratic
convergence transfers this control to the square root of the next gradient norm.
-/

namespace ShiftedNewton
open SecondOrderTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lipschitz continuity of the actual gradient bounds the actual Riesz Hessian,
with the same constant, at every point. -/
theorem norm_hessian_le_of_gradient_lipschitz {f : E → ℝ} {H : ℝ} (hH : 0 ≤ H)
    (hlip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ H * ‖y - z‖) (x : E) :
    ‖hessian f x‖ ≤ H := by
  have hder : LipschitzWith ⟨H, hH⟩ (fderiv ℝ f) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_eq_norm, dist_eq_norm, ← toDual_gradient, ← toDual_gradient,
      ← map_sub, (InnerProductSpace.toDual ℝ E).norm_map]
    exact hlip y z
  have hb := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hder
  rw [norm_hessian, ← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  exact hb

/-- A relatively small Newton residual and a bounded nonnegative multiplier
bound the current actual gradient by the step length. -/
theorem Step.gradient_mul_le {f : E → ℝ} {x s r : E} {ℓ κg κs H B : ℝ}
    (h : Step f x s r ℓ κg κs) (hH : ‖hessian f x‖ ≤ H) (hℓ : ℓ ≤ B) :
    (1 - κg) * ‖gradient f x‖ ≤ (H + B) * ‖s‖ := by
  have hid : gradient f x = r - (hessian f x s + ℓ • s) := by
    calc
      _ = r - (-gradient f x + r) := by abel
      _ = _ := by rw [h.equation]
  have hb : ‖gradient f x‖ ≤ ‖r‖ + (H + B) * ‖s‖ := by
    calc
      _ = ‖r - (hessian f x s + ℓ • s)‖ := congrArg norm hid
      _ ≤ ‖r‖ + ‖hessian f x s + ℓ • s‖ := norm_sub_le _ _
      _ ≤ ‖r‖ + (‖hessian f x s‖ + ‖ℓ • s‖) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ _ := by
        rw [norm_smul, Real.norm_of_nonneg h.multiplier_nonneg]
        have ht := (hessian f x).le_opNorm s
        nlinarith [mul_le_mul_of_nonneg_right hH (norm_nonneg s),
          mul_le_mul_of_nonneg_right hℓ (norm_nonneg s)]
  nlinarith [h.residual_relative]

/-- Quadratic decrease of the actual gradient norm forces a square-root lower
bound on the step, with the explicit coefficient from bounded shifted Hessians. -/
theorem Step.step_lower_of_quadratic {f : E → ℝ} {x s r : E}
    {ℓ κg κs H B C : ℝ} (h : Step f x s r ℓ κg κs)
    (hH : 0 ≤ H) (hB : 0 < B) (hC : 0 < C)
    (hhess : ‖hessian f x‖ ≤ H) (hℓ : ℓ ≤ B)
    (hnext : ‖gradient f (x + s)‖ ≤ C * ‖gradient f x‖ ^ 2) :
    0 < (1 - κg) / ((H + B) * Real.sqrt C) ∧
      (1 - κg) / ((H + B) * Real.sqrt C) *
        Real.sqrt ‖gradient f (x + s)‖ ≤ ‖s‖ := by
  have hκ : 0 < 1 - κg := by linarith [h.relative_lt_one]
  have hden : 0 < (H + B) * Real.sqrt C := by positivity
  have hsqrt : Real.sqrt ‖gradient f (x + s)‖ ≤ Real.sqrt C * ‖gradient f x‖ := by
    have h1 := Real.sq_sqrt (norm_nonneg (gradient f (x + s)))
    have h2 := Real.sq_sqrt hC.le
    have hnorm := norm_nonneg (gradient f x)
    have hnonneg : 0 ≤ Real.sqrt C * ‖gradient f x‖ := by positivity
    nlinarith [Real.sqrt_nonneg ‖gradient f (x + s)‖]
  have hbound := h.gradient_mul_le hhess hℓ
  have hb : (1 - κg) * Real.sqrt ‖gradient f (x + s)‖ ≤
      ((H + B) * Real.sqrt C) * ‖s‖ := by
    have hb1 := mul_le_mul_of_nonneg_left hsqrt hκ.le
    have hb2 := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg C)
    nlinarith
  refine ⟨div_pos hκ hden, ?_⟩
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hb)

/-- An accepted inexact shifted-Newton trace with quadratic gradient convergence
has a common positive square-root step coefficient at every iteration. -/
theorem Trace.step_lower_of_quadratic {f : E → ℝ} {x s r : ℕ → E}
    {ℓ : ℕ → ℝ} {κg κs H B C : ℝ} {N : ℕ}
    (h : Trace f x s r ℓ κg κs N) (hH : 0 ≤ H) (hB : 0 < B) (hC : 0 < C)
    (hlip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ H * ‖y - z‖)
    (hℓ : ∀ i < N, ℓ i ≤ B)
    (hnext : ∀ i < N, ‖gradient f (x (i + 1))‖ ≤ C * ‖gradient f (x i)‖ ^ 2) :
    0 < (1 - κg) / ((H + B) * Real.sqrt C) ∧
      ∀ i < N, (1 - κg) / ((H + B) * Real.sqrt C) *
        Real.sqrt ‖gradient f (x (i + 1))‖ ≤ ‖s i‖ := by
  have hκ : 0 < 1 - κg := by linarith [h.relative_lt_one]
  refine ⟨by positivity, ?_⟩
  intro i hi
  have hn := hnext i hi
  rw [h.point_update i hi] at hn ⊢
  exact ((h.step i hi).step_lower_of_quadratic hH hB hC
    (norm_hessian_le_of_gradient_lipschitz hH hlip (x i)) (hℓ i hi) hn).2

end ShiftedNewton
