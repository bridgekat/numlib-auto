import Numlib.Optimization.Constrained.TargetMerit
import Numlib.Analysis.SpecialFunctions.Sqrt.Bounds
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Exact Euclidean target-reset geometry

The augmented residual uses the genuine Euclidean product norm. Reset and
reflection formulas yield exact residual identities, positive target gaps and
the fixed reset decrease directly from the actual old residual disk.
-/

namespace Constrained.TwoPhase
variable {E F : Type*} [NormedAddCommGroup F] {f : E → ℝ} {c : E → F}

/-- The actual constraint/objective residual in a Euclidean product space. -/
noncomputable def residual (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    WithLp 2 (F × ℝ) := WithLp.toLp 2 (c x, f x - t)

/-- The augmented residual has exactly the Euclidean sum-of-squares norm. -/
theorem residual_norm_sq (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    ‖residual f c t x‖ ^ 2 = ‖c x‖ ^ 2 + (f x - t) ^ 2 := by
  simpa only [residual, WithLp.toLp_fst, WithLp.toLp_snd, Prod.fst, Prod.snd,
    Real.norm_eq_abs, sq_abs] using
    WithLp.prod_norm_sq_eq_of_L2 (residual f c t x)

/-- The actual residual norm is the square root of its genuine squared components. -/
theorem residual_norm (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    ‖residual f c t x‖ = Real.sqrt (‖c x‖ ^ 2 + (f x - t) ^ 2) := by
  rw [←residual_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Constraint infeasibility never exceeds the actual augmented residual norm. -/
theorem constraint_norm_le_residual (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    ‖c x‖ ≤ ‖residual f c t x‖ := by
  have hh := residual_norm_sq f c t x
  nlinarith [sq_nonneg (f x - t), norm_nonneg (c x), norm_nonneg (residual f c t x)]

/-- Absolute objective-target gap never exceeds the actual residual norm. -/
theorem abs_gap_le_residual (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    |f x - t| ≤ ‖residual f c t x‖ := by
  have hh := residual_norm_sq f c t x
  nlinarith [sq_nonneg ‖c x‖, abs_nonneg (f x - t), sq_abs (f x - t),
    norm_nonneg (residual f c t x)]

/-- The literal target reset fixes the new residual norm at the primal tolerance. -/
noncomputable def resetTarget (f : E → ℝ) (c : E → F) (ε : ℝ) (x : E) : ℝ :=
  f x - Real.sqrt (ε ^ 2 - ‖c x‖ ^ 2)

/-- The reflection target changes only the sign of the objective-target residual. -/
def reflectTarget (f : E → ℝ) (t : ℝ) (x : E) : ℝ := 2 * f x - t

/-- Every reset has nonnegative objective-target gap. -/
theorem reset_gap_nonneg (f : E → ℝ) (c : E → F) (ε : ℝ) (x : E) :
    0 ≤ f x - resetTarget f c ε x := by
  simpa only [resetTarget, sub_sub_cancel] using Real.sqrt_nonneg (ε ^ 2 - ‖c x‖ ^ 2)

/-- If constraint infeasibility is at most the positive tolerance, the target
reset gives exactly the requested augmented residual norm. -/
theorem residual_reset {ε : ℝ} (hε : 0 ≤ ε) {x : E} (hc : ‖c x‖ ≤ ε) :
    ‖residual f c (resetTarget f c ε x) x‖ = ε := by
  have hs : 0 ≤ ε ^ 2 - ‖c x‖ ^ 2 := by nlinarith [norm_nonneg (c x)]
  have hh := residual_norm_sq f c (resetTarget f c ε x) x
  rw [resetTarget, sub_sub_cancel, Real.sq_sqrt hs] at hh
  dsimp only [resetTarget]
  nlinarith [norm_nonneg (residual f c (f x - Real.sqrt (ε ^ 2 - ‖c x‖ ^ 2)) x)]

/-- Reflection preserves the actual residual norm exactly. -/
theorem residual_reflect (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    ‖residual f c (reflectTarget f t x) x‖ = ‖residual f c t x‖ := by
  have h₁ := residual_norm_sq f c (reflectTarget f t x) x
  have h₂ := residual_norm_sq f c t x
  dsimp [reflectTarget] at h₁
  dsimp only [reflectTarget]
  nlinarith [norm_nonneg (residual f c (2 * f x - t) x),
    norm_nonneg (residual f c t x)]

/-- Reflecting an overshot target gives a positive new objective-target gap. -/
theorem reflect_gap_pos {t : ℝ} {x : E} (h : f x < t) :
    0 < f x - reflectTarget f t x := by dsimp [reflectTarget]; linarith

/-- Reflection strictly decreases an overshot target. -/
theorem reflect_lt {t : ℝ} {x : E} (h : f x < t) : reflectTarget f t x < t := by
  dsimp [reflectTarget]
  linarith

/-- The genuine old residual disk gives the precise reset target decrease. -/
theorem reset_decrease {ε θ t : ℝ} (hε : 0 ≤ ε) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {x : E} (hr : ‖residual f c t x‖ ≤ θ * ε) :
    (1 - θ) * ε ≤ t - resetTarget f c ε x := by
  have hs : (f x - t) ^ 2 + ‖c x‖ ^ 2 ≤ (θ * ε) ^ 2 := by
    have hh := residual_norm_sq f c t x
    nlinarith [norm_nonneg (residual f c t x), mul_nonneg hθ hε]
  have hh := Real.sub_le_neg_add_sqrt_of_sq_add_sq_le
    (r := θ * ε) (R := ε) (x := f x - t) (y := ‖c x‖)
    (mul_nonneg hθ hε) (mul_le_of_le_one_left hε hθ1) hs
  dsimp [resetTarget]
  linarith

/-- The actual target merit equals one half of the Euclidean residual norm squared. -/
theorem targetMerit_eq_residual (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    targetMerit f c t x = ‖residual f c t x‖ ^ 2 / 2 := by
  rw [residual_norm_sq, targetMerit]
  ring

/-- Actual merit nonincrease is exactly residual-norm nonincrease. -/
theorem residual_le_of_merit_le {t : ℝ} {x y : E}
    (h : targetMerit f c t y ≤ targetMerit f c t x) :
    ‖residual f c t y‖ ≤ ‖residual f c t x‖ := by
  rw [targetMerit_eq_residual, targetMerit_eq_residual] at h
  nlinarith [norm_nonneg (residual f c t x), norm_nonneg (residual f c t y)]

end Constrained.TwoPhase
