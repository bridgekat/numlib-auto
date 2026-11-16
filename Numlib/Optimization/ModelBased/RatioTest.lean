/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The ratio test of model-based methods

Trust-region and adaptive-regularization methods compare the achieved reduction of the objective $f$
with the reduction $\mathrm{pred} > 0$ that a model predicts, as in (2.3.6), (2.4.3), (3.3.7),
(4.1.15) and (12.2.4) of [cartis2022evaluation]. The **reduction ratio** is
$$\rho = \frac{f(x) - f(x + s)}{\mathrm{pred}},$$
and the trial point $x + s$ is accepted if and only if $\rho \ge \eta_1$. In the
adaptive-regularization and trust-region methods the predicted decrease is a Taylor decrement, in
the iRN method of [cartis2022evaluation] it is $\|s\|^3$, and in Chapter 13 of
[cartis2022evaluation] it is an inexact decrement. This file assumes nothing about it.

## Main definitions

* `Optimization.reductionRatio`: the reduction ratio $\rho = (f(x) - f(x + s)) / \mathrm{pred}$.
* `Optimization.acceptStep`: the next iterate, $x + s$ if $\eta_1 \le \rho$ and $x$ otherwise.

## Main results

* `Optimization.le_reductionRatio_iff`: for $\mathrm{pred} > 0$, $\eta \le \rho$ if and only if
  $f(x) - f(x + s) \ge \eta \, \mathrm{pred}$.
* `Optimization.sub_le_of_le_reductionRatio`: a successful iteration decreases $f$ by at least
  $\eta_1 \, \mathrm{pred}$.
* `Optimization.abs_reductionRatio_sub_one`: $|\rho - 1| = |f(x + s) - (f(x) - \mathrm{pred})| /
  |\mathrm{pred}|$.
* `Optimization.le_reductionRatio_of_abs_sub_le`: if the model value $f(x) - \mathrm{pred}$ predicts
  $f(x + s)$ up to $c \, \mathrm{pred}$, then $\rho \ge 1 - c$, so the iteration is very successful
  when $c \le 1 - \eta_2$.

## Implementation notes

* The domain $E$ needs only an addition. For $\mathrm{pred} = 0$, the ratio is $0$, because division
  by zero gives $0$ in Lean.
-/

namespace Optimization

variable {E : Type*} [Add E]

/-- The **reduction ratio** of the achieved to the predicted reduction:
$$\rho = \frac{f(x) - f(x + s)}{\mathrm{pred}}.$$
It is $0$ when $\mathrm{pred} = 0$. -/
noncomputable def reductionRatio (f : E → ℝ) (x s : E) (pred : ℝ) : ℝ :=
  (f x - f (x + s)) / pred

/-- The **accepted iterate** of the ratio test with threshold $\eta_1$: it is $x + s$ if
$\eta_1 \le \rho$ (a successful iteration), and $x$ otherwise. Here $\rho$ is
`Optimization.reductionRatio f x s pred`. -/
noncomputable def acceptStep (η₁ : ℝ) (f : E → ℝ) (x s : E) (pred : ℝ) : E :=
  if η₁ ≤ reductionRatio f x s pred then x + s else x

variable {f : E → ℝ} {x s : E} {pred η c : ℝ}

/-- The reduction ratio is $\rho = (f(x) - f(x + s)) / \mathrm{pred}$. -/
theorem reductionRatio_def : reductionRatio f x s pred = (f x - f (x + s)) / pred := rfl

/-- If $\eta \le \rho$, then the ratio test with threshold $\eta$ accepts the trial point $x + s$.
-/
theorem acceptStep_of_le (h : η ≤ reductionRatio f x s pred) : acceptStep η f x s pred = x + s := by
  simp [acceptStep, h]

/-- If $\rho < \eta$, then the ratio test with threshold $\eta$ keeps the point $x$. -/
theorem acceptStep_of_lt (h : reductionRatio f x s pred < η) : acceptStep η f x s pred = x := by
  simp [acceptStep, not_le.2 h]

/-- If $\mathrm{pred} > 0$, then $\eta \le \rho$ if and only if the achieved decrease is at least
$\eta \, \mathrm{pred}$:
$$\eta \le \rho \iff \eta \, \mathrm{pred} \le f(x) - f(x + s).$$
-/
theorem le_reductionRatio_iff (hpred : 0 < pred) :
    η ≤ reductionRatio f x s pred ↔ η * pred ≤ f x - f (x + s) :=
  le_div_iff₀ hpred

/-- If $\mathrm{pred} > 0$, then $\rho < \eta$ if and only if the achieved decrease is less than
$\eta \, \mathrm{pred}$:
$$\rho < \eta \iff f(x) - f(x + s) < \eta \, \mathrm{pred}.$$
-/
theorem reductionRatio_lt_iff (hpred : 0 < pred) :
    reductionRatio f x s pred < η ↔ f x - f (x + s) < η * pred :=
  div_lt_iff₀ hpred

/-- A successful iteration decreases the objective by at least $\eta$ times the predicted decrease.
Let $\mathrm{pred} > 0$ and $\eta \le \rho$. Then
$$f(x) - f(x + s) \ge \eta \, \mathrm{pred}.$$
-/
theorem sub_le_of_le_reductionRatio (hpred : 0 < pred) (h : η ≤ reductionRatio f x s pred) :
    η * pred ≤ f x - f (x + s) :=
  (le_reductionRatio_iff hpred).1 h

/-- If $\mathrm{pred} \neq 0$, then
$$|\rho - 1| = \frac{|f(x + s) - (f(x) - \mathrm{pred})|}{|\mathrm{pred}|}.$$
Thus the ratio is close to $1$ if and only if the model value $f(x) - \mathrm{pred}$ predicts
$f(x + s)$ well relative to $\mathrm{pred}$. -/
theorem abs_reductionRatio_sub_one (hpred : pred ≠ 0) :
    |reductionRatio f x s pred - 1| = |f (x + s) - (f x - pred)| / |pred| := by
  rw [reductionRatio, div_sub_one hpred, abs_div, ← abs_neg (f x - f (x + s) - pred)]
  congr 2
  ring

/-- Let $\mathrm{pred} > 0$ and $|f(x + s) - (f(x) - \mathrm{pred})| \le c \, \mathrm{pred}$. Then
$|\rho - 1| \le c$. -/
theorem abs_reductionRatio_sub_one_le (hpred : 0 < pred)
    (h : |f (x + s) - (f x - pred)| ≤ c * pred) : |reductionRatio f x s pred - 1| ≤ c := by
  rw [abs_reductionRatio_sub_one hpred.ne', abs_of_pos hpred, div_le_iff₀ hpred]
  exact h

/-- If the model value $f(x) - \mathrm{pred}$ predicts $f(x + s)$ up to $c$ times the predicted
decrease, then the ratio is at least $1 - c$. Let $\mathrm{pred} > 0$ and
$$|f(x + s) - (f(x) - \mathrm{pred})| \le c \, \mathrm{pred}.$$
Then $\rho \ge 1 - c$.

With $c \le 1 - \eta_2$, it follows that $\rho \ge \eta_2$, so the iteration is very successful. -/
theorem le_reductionRatio_of_abs_sub_le (hpred : 0 < pred)
    (h : |f (x + s) - (f x - pred)| ≤ c * pred) : 1 - c ≤ reductionRatio f x s pred := by
  have := abs_reductionRatio_sub_one_le hpred h
  linarith [neg_abs_le (reductionRatio f x s pred - 1)]

/-- If $\mathrm{pred} > 0$ and the model value $f(x) - \mathrm{pred}$ is at least $f(x + s)$, then
$\rho \ge 1$. -/
theorem one_le_reductionRatio (hpred : 0 < pred) (h : f (x + s) ≤ f x - pred) :
    1 ≤ reductionRatio f x s pred := by
  rw [le_reductionRatio_iff hpred]
  linarith

end Optimization
