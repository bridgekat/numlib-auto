import Numlib.Optimization.TargetLeastSquares
import Numlib.Analysis.SpecialFunctions.SqrtDifference

/-!
# Target updates for equality-constrained least squares

Resetting a scalar target places the residual on a prescribed Euclidean sphere. Reflecting
it preserves the residual. These algebraic facts do not depend on the inner minimizer.
-/

noncomputable section
namespace Optimization.TwoPhaseTargets

variable {E F : Type} [NormedAddCommGroup F]

/-- The Euclidean norm of a constraint residual with an appended objective residual. -/
def residualNorm (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) : ℝ :=
  Real.sqrt (‖c x‖ ^ 2 + (f x - t) ^ 2)

/-- A target residual norm is nonnegative. -/
theorem residualNorm_nonneg (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    0 ≤ residualNorm f c t x := Real.sqrt_nonneg _

/-- Squaring the augmented norm recovers the constraint and objective residual squares. -/
@[simp] theorem residualNorm_sq (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    residualNorm f c t x ^ 2 = ‖c x‖ ^ 2 + (f x - t) ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The actual scalar-target least-squares objective is half the squared augmented norm. -/
theorem objective_eq_half_sq (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    TargetLeastSquares.objective f c t x = residualNorm f c t x ^ 2 / 2 := by
  rw [residualNorm_sq]
  rfl

/-- The augmented norm bounds its constraint component. -/
theorem norm_constraint_le (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    ‖c x‖ ≤ residualNorm f c t x := by
  have hs := residualNorm_sq f c t x
  have hn := residualNorm_nonneg f c t x
  nlinarith [sq_nonneg (f x - t), norm_nonneg (c x)]

/-- The augmented norm bounds the absolute objective-target gap. -/
theorem abs_gap_le (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    |f x - t| ≤ residualNorm f c t x := by
  have hs := residualNorm_sq f c t x
  have hn := residualNorm_nonneg f c t x
  nlinarith [sq_nonneg ‖c x‖, sq_abs (f x - t), abs_nonneg (f x - t)]

/-- Resetting the target chooses the nonnegative objective residual on the sphere. -/
def resetTarget (f : E → ℝ) (c : E → F) (epsilon : ℝ) (x : E) : ℝ :=
  f x - Real.sqrt (epsilon ^ 2 - ‖c x‖ ^ 2)

/-- Reflection reverses the sign of the scalar residual. -/
def reflectTarget (f : E → ℝ) (t : ℝ) (x : E) : ℝ := 2 * f x - t

/-- A reset has nonnegative scalar residual. -/
theorem reset_gap_nonneg (f : E → ℝ) (c : E → F) (epsilon : ℝ) (x : E) :
    0 ≤ f x - resetTarget f c epsilon x := by
  simp only [resetTarget, sub_sub_cancel]
  exact Real.sqrt_nonneg _

/-- A reset reaches the prescribed radius whenever the constraint component fits. -/
theorem residualNorm_reset {f : E → ℝ} {c : E → F} {epsilon : ℝ} {x : E}
    (he : 0 ≤ epsilon) (hc : ‖c x‖ ≤ epsilon) :
    residualNorm f c (resetTarget f c epsilon x) x = epsilon := by
  have hh : 0 ≤ epsilon ^ 2 - ‖c x‖ ^ 2 := by nlinarith [norm_nonneg (c x)]
  unfold residualNorm resetTarget
  simp only [sub_sub_cancel]
  rw [Real.sq_sqrt hh]
  rw [show ‖c x‖ ^ 2 + (epsilon ^ 2 - ‖c x‖ ^ 2) = epsilon ^ 2 by ring]
  exact Real.sqrt_sq he

/-- Reflection leaves the actual augmented residual norm unchanged. -/
@[simp] theorem residualNorm_reflect (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    residualNorm f c (reflectTarget f t x) x = residualNorm f c t x := by
  unfold residualNorm reflectTarget
  congr 1
  ring

/-- Reflection after crossing the target produces a positive scalar gap. -/
theorem reflect_gap_pos {f : E → ℝ} {t : ℝ} {x : E} (h : f x < t) :
    0 < f x - reflectTarget f t x := by unfold reflectTarget; linarith

/-- A reflection after crossing the target strictly decreases it. -/
theorem reflectTarget_lt {f : E → ℝ} {t : ℝ} {x : E} (h : f x < t) :
    reflectTarget f t x < t := by unfold reflectTarget; linarith

/-- A small old residual pays the difference of radii when the target is reset. -/
theorem reset_decrease {f : E → ℝ} {c : E → F} {epsilon theta t : ℝ} {x : E}
    (he : 0 ≤ epsilon) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (hr : residualNorm f c t x ≤ theta * epsilon) :
    (1 - theta) * epsilon ≤ t - resetTarget f c epsilon x := by
  have hrad : 0 ≤ theta * epsilon := mul_nonneg ht0 he
  have hle : theta * epsilon ≤ epsilon := by nlinarith
  have hdisk : (f x - t) ^ 2 + ‖c x‖ ^ 2 ≤ (theta * epsilon) ^ 2 := by
    have hs := residualNorm_sq f c t x
    nlinarith [residualNorm_nonneg f c t x]
  have hd := Real.sub_add_sqrt_sq_sub_sq_ge_sub hrad hle hdisk
  unfold resetTarget
  nlinarith

/-- A nonnegative scalar gap and bounded residual put the target in the objective interval. -/
theorem target_mem_interval {f : E → ℝ} {c : E → F} {t epsilon low up : ℝ} {x : E}
    (he : epsilon ≤ 1) (hl : low ≤ f x) (hu : f x ≤ up)
    (hg : 0 ≤ f x - t) (hr : residualNorm f c t x ≤ epsilon) :
    t ∈ Set.Icc (low - 1) up := by
  have hg' := (le_abs_self (f x - t)).trans ((abs_gap_le f c t x).trans hr)
  constructor <;> linarith

end Optimization.TwoPhaseTargets
