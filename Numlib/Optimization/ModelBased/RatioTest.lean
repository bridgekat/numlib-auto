import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The ratio test of model-based methods

Trust-region and adaptive-regularization methods compare the achieved reduction of the objective
with the reduction `pred > 0` predicted by a model ([cartis2022evaluation], (2.3.6), (2.4.3),
(3.3.7), (4.1.15), (12.2.4), …):
`ρ = (f(x) - f(x + s)) / pred`, and the trial point `x + s` is accepted iff `ρ ≥ η₁`. The predicted
decrease is a Taylor decrement in the AR/TR methods, `‖s‖³` in iRN, an inexact decrement in
Chapter 13; nothing about it is assumed here.

* `Optimization.reductionRatio f x s pred` and `Optimization.acceptStep η₁ f x s pred`.
* `Optimization.le_reductionRatio_iff`, `Optimization.sub_le_of_le_reductionRatio`: a successful
  iteration decreases `f` by at least `η₁ pred`.
* `Optimization.abs_reductionRatio_sub_one`, `Optimization.le_reductionRatio_of_abs_sub_le`: if the
  model value `f(x) - pred` predicts `f(x + s)` up to `c pred`, then `ρ ≥ 1 - c` (so the iteration
  is very successful when `c ≤ 1 - η₂`).
-/

namespace Optimization

variable {E : Type*} [Add E]

/-- The reduction ratio `ρ = (f(x) - f(x + s)) / pred` of the achieved to the predicted
reduction. -/
noncomputable def reductionRatio (f : E → ℝ) (x s : E) (pred : ℝ) : ℝ :=
  (f x - f (x + s)) / pred

/-- The accepted iterate: `x + s` if `η₁ ≤ ρ` (successful iteration), `x` otherwise. -/
noncomputable def acceptStep (η₁ : ℝ) (f : E → ℝ) (x s : E) (pred : ℝ) : E :=
  if η₁ ≤ reductionRatio f x s pred then x + s else x

variable {f : E → ℝ} {x s : E} {pred η c : ℝ}

theorem reductionRatio_def : reductionRatio f x s pred = (f x - f (x + s)) / pred := rfl

theorem acceptStep_of_le (h : η ≤ reductionRatio f x s pred) : acceptStep η f x s pred = x + s := by
  simp [acceptStep, h]

theorem acceptStep_of_lt (h : reductionRatio f x s pred < η) : acceptStep η f x s pred = x := by
  simp [acceptStep, not_le.2 h]

/-- For a positive predicted decrease, `η ≤ ρ` iff the achieved decrease is at least
`η pred`. -/
theorem le_reductionRatio_iff (hpred : 0 < pred) :
    η ≤ reductionRatio f x s pred ↔ η * pred ≤ f x - f (x + s) :=
  le_div_iff₀ hpred

/-- For a positive predicted decrease, `ρ < η` iff the achieved decrease is less than
`η pred`. -/
theorem reductionRatio_lt_iff (hpred : 0 < pred) :
    reductionRatio f x s pred < η ↔ f x - f (x + s) < η * pred :=
  div_lt_iff₀ hpred

/-- A successful iteration (`η ≤ ρ`, `pred > 0`) decreases `f` by at least `η pred`. -/
theorem sub_le_of_le_reductionRatio (hpred : 0 < pred) (h : η ≤ reductionRatio f x s pred) :
    η * pred ≤ f x - f (x + s) :=
  (le_reductionRatio_iff hpred).1 h

/-- `|ρ - 1| = |f(x + s) - (f(x) - pred)| / |pred|`: the ratio is close to one iff the model value
`f(x) - pred` predicts `f(x + s)` well relative to `pred`. -/
theorem abs_reductionRatio_sub_one (hpred : pred ≠ 0) :
    |reductionRatio f x s pred - 1| = |f (x + s) - (f x - pred)| / |pred| := by
  rw [reductionRatio, div_sub_one hpred, abs_div, ← abs_neg (f x - f (x + s) - pred)]
  congr 2
  ring

/-- If `|f(x + s) - (f(x) - pred)| ≤ c pred` with `pred > 0`, then `|ρ - 1| ≤ c`. -/
theorem abs_reductionRatio_sub_one_le (hpred : 0 < pred)
    (h : |f (x + s) - (f x - pred)| ≤ c * pred) : |reductionRatio f x s pred - 1| ≤ c := by
  rw [abs_reductionRatio_sub_one hpred.ne', abs_of_pos hpred, div_le_iff₀ hpred]
  exact h

/-- If `|f(x + s) - (f(x) - pred)| ≤ c pred` with `pred > 0`, then `1 - c ≤ ρ`. With
`c ≤ 1 - η₂` the iteration is very successful (`η₂ ≤ ρ`). -/
theorem le_reductionRatio_of_abs_sub_le (hpred : 0 < pred)
    (h : |f (x + s) - (f x - pred)| ≤ c * pred) : 1 - c ≤ reductionRatio f x s pred := by
  have := abs_reductionRatio_sub_one_le hpred h
  linarith [neg_abs_le (reductionRatio f x s pred - 1)]

/-- If the model value `f(x) - pred` overestimates `f(x + s)` and `pred > 0`, then `ρ ≥ 1`. -/
theorem one_le_reductionRatio (hpred : 0 < pred) (h : f (x + s) ≤ f x - pred) :
    1 ≤ reductionRatio f x s pred := by
  rw [le_reductionRatio_iff hpred]
  linarith

end Optimization
