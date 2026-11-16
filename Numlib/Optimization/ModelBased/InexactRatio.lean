/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Ratio tests with inexact data

The dynamic-accuracy methods of Chapter 13 of [cartis2022evaluation] (§13.1 and §13.3, with the
ratios (13.1.16), (13.1.58), (13.3.10) and (13.3.19)) compare the achieved decrease with the
predicted decrease through the ratio $\rho = (a - b)/\bar\Delta$. Here $\bar\Delta > 0$ is an
inexact Taylor decrement, and $a$ and $b$ are values of the objective at $x$ and $x + s$. These
values are exact in the IDA framework, $a = f(x)$ and $b = f(x + s)$, and inexact in the EDA
framework. Write $f_x = f(x)$ and $f_{xs} = f(x + s)$ for the exact values and $\Delta_T$ for the
exact Taylor decrement at $x$ along $s$.

The lemmas of this file are statements about real numbers. The exact quantities $f_x$, $f_{xs}$ and
$\Delta_T$ enter only through the error terms $|a - f_x|$, $|b - f_{xs}|$,
$|f_{xs} - (f_x - \Delta_T)|$ and $|\Delta_T - \bar\Delta|$, so the same lemmas serve every
algorithm of Chapter 13.

## Main results

* `Optimization.abs_div_sub_one_le_of_inexact`: $|\rho - 1|$ is at most the sum of the two value
  errors, the Taylor remainder $|f_{xs} - (f_x - \Delta_T)|$ and the decrement error
  $|\Delta_T - \bar\Delta|$, divided by $\bar\Delta$.
* `Optimization.le_div_of_inexact_error_le`: if that sum is at most $(1 - \eta)\bar\Delta$, then
  $\rho \ge \eta$ (the very-successful criterion).
* `Optimization.sub_ge_of_inexact_ratio`: on an accepted step with value errors at most
  $\kappa_s \bar\Delta$ and $\kappa_s \le \eta_1/4$, the true decrease $f_x - f_{xs}$ is at least
  $\eta_1 \bar\Delta/2$.

## Implementation notes

* The quantities are real variables: `fx`, `fxs`, `ΔT` and `Δbar` stand for $f_x$, $f_{xs}$,
  $\Delta_T$ and $\bar\Delta$.
* In the IDA framework the ratio of the source is `Optimization.reductionRatio f x s Δbar`, which
  equals $(a - b)/\bar\Delta$ with $a = f(x)$ and $b = f(x + s)$ by
  `Optimization.reductionRatio_def`. If moreover $\bar\Delta = \Delta_T$, the first lemma is the
  exact estimate behind `Optimization.le_reductionRatio_of_abs_sub_le`.
-/

namespace Optimization

variable {a b fx fxs ΔT Δbar η η₁ κs : ℝ}

/-- The **error decomposition of the inexact ratio**. Let $a, b, f_x, f_{xs}, \Delta_T, \bar\Delta
\in \mathbb{R}$ with $\bar\Delta > 0$. Then
$$\left|\frac{a - b}{\bar\Delta} - 1\right| \le \frac{|a - f_x| + |f_{xs} - (f_x - \Delta_T)| +
  |\Delta_T - \bar\Delta| + |b - f_{xs}|}{\bar\Delta}.$$

When $\Delta_T$ is the exact Taylor decrement at $x$ along $s$, $f_x - \Delta_T$ is the value of
the Taylor polynomial at $s$, so the second term is the Taylor remainder. The third term is the
error of the inexact decrement. The first and the last terms are the errors of the function
values, and they vanish in the IDA framework. -/
theorem abs_div_sub_one_le_of_inexact (hΔ : 0 < Δbar) :
    |(a - b) / Δbar - 1| ≤
      (|a - fx| + |fxs - (fx - ΔT)| + |ΔT - Δbar| + |b - fxs|) / Δbar := by
  have hsplit : (a - b) / Δbar - 1 =
      ((a - fx) - (fxs - (fx - ΔT)) + (ΔT - Δbar) - (b - fxs)) / Δbar := by
    field_simp
    ring
  rw [hsplit, abs_div, abs_of_pos hΔ]
  gcongr
  calc |(a - fx) - (fxs - (fx - ΔT)) + (ΔT - Δbar) - (b - fxs)|
      ≤ |(a - fx) - (fxs - (fx - ΔT)) + (ΔT - Δbar)| + |b - fxs| := abs_sub _ _
    _ ≤ |(a - fx) - (fxs - (fx - ΔT))| + |ΔT - Δbar| + |b - fxs| := by
        gcongr; exact abs_add_le _ _
    _ ≤ |a - fx| + |fxs - (fx - ΔT)| + |ΔT - Δbar| + |b - fxs| := by
        gcongr; exact abs_sub _ _

/-- The **very-successful criterion for the inexact ratio**. Let $a, b, f_x, f_{xs}, \Delta_T,
\bar\Delta, \eta \in \mathbb{R}$ with $\bar\Delta > 0$, and suppose that the total error is
small:
$$|a - f_x| + |f_{xs} - (f_x - \Delta_T)| + |\Delta_T - \bar\Delta| + |b - f_{xs}| \le (1 -
  \eta)\bar\Delta.$$
Then $\eta \le (a - b)/\bar\Delta$. -/
theorem le_div_of_inexact_error_le (hΔ : 0 < Δbar)
    (herr : |a - fx| + |fxs - (fx - ΔT)| + |ΔT - Δbar| + |b - fxs| ≤ (1 - η) * Δbar) :
    η ≤ (a - b) / Δbar := by
  have h1 := abs_div_sub_one_le_of_inexact (a := a) (b := b) (fx := fx) (fxs := fxs) (ΔT := ΔT) hΔ
  have h2 : (|a - fx| + |fxs - (fx - ΔT)| + |ΔT - Δbar| + |b - fxs|) / Δbar ≤ 1 - η := by
    rwa [div_le_iff₀ hΔ]
  have := neg_abs_le ((a - b) / Δbar - 1)
  linarith

/-- The true decrease on an accepted step with inexact values, sharp form. Let $\bar\Delta > 0$,
$|a - f_x| \le \kappa_s \bar\Delta$, $|b - f_{xs}| \le \kappa_s \bar\Delta$ and
$\eta_1 \le (a - b)/\bar\Delta$. Then $f_x - f_{xs} \ge (\eta_1 - 2\kappa_s)\bar\Delta$. -/
theorem sub_ge_sub_mul_of_inexact_ratio (hΔ : 0 < Δbar) (ha : |a - fx| ≤ κs * Δbar)
    (hb : |b - fxs| ≤ κs * Δbar) (hρ : η₁ ≤ (a - b) / Δbar) :
    (η₁ - 2 * κs) * Δbar ≤ fx - fxs := by
  rw [le_div_iff₀ hΔ] at hρ
  have := le_abs_self (a - fx)
  have := neg_abs_le (b - fxs)
  nlinarith [abs_sub_comm a fx]

/-- The **true decrease on accepted steps with inexact values**. Let $a, b, f_x, f_{xs}, \bar\Delta,
\eta_1, \kappa_s \in \mathbb{R}$ with $\bar\Delta > 0$, $|a - f_x| \le \kappa_s \bar\Delta$,
$|b - f_{xs}| \le \kappa_s \bar\Delta$, $\eta_1 \le (a - b)/\bar\Delta$ and
$\kappa_s \le \eta_1/4$. Then
$$f_x - f_{xs} \ge \frac{\eta_1}{2}\bar\Delta.$$
This is the estimate in the proofs of Lemmas 13.3.2 and 13.3.7 of [cartis2022evaluation]. -/
theorem sub_ge_of_inexact_ratio (hΔ : 0 < Δbar) (ha : |a - fx| ≤ κs * Δbar)
    (hb : |b - fxs| ≤ κs * Δbar) (hρ : η₁ ≤ (a - b) / Δbar) (hκ : κs ≤ η₁ / 4) :
    η₁ / 2 * Δbar ≤ fx - fxs := by
  have := sub_ge_sub_mul_of_inexact_ratio hΔ ha hb hρ
  nlinarith

end Optimization
