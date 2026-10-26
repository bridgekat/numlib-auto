import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Ratio tests with inexact data

In the dynamic-accuracy methods of [cartis2022evaluation] (§13.1, §13.3: (13.1.16), (13.1.58),
(13.3.10), (13.3.19)) the ratio of achieved to predicted decrease is
`ρ = (a - b) / Δbar`, where `Δbar > 0` is an *inexact* Taylor decrement and `a, b` are the values
of the objective at `x` and `x + s`, exact (IDA framework, `a = f x`, `b = f (x + s)`) or inexact
(EDA framework). The lemmas below are statements about real numbers: the exact values
`fx = f x`, `fxs = f (x + s)` and the exact decrement `ΔT` enter only through the error terms, so
the same lemmas serve every algorithm of Chapter 13.

* `Optimization.abs_div_sub_one_le_of_inexact`: `|ρ - 1|` is bounded by the sum of the value
  errors, the Taylor remainder `|fxs - (fx - ΔT)|` and the decrement error `|ΔT - Δbar|`, divided
  by `Δbar`.
* `Optimization.le_div_of_inexact_error_le`: if that sum is at most `(1 - η) Δbar` then `η ≤ ρ`
  (the very-successful criterion).
* `Optimization.sub_ge_of_inexact_ratio`: on an accepted step with value errors at most
  `κs Δbar`, `κs ≤ η₁ / 4`, the true decrease is at least `η₁ Δbar / 2`.

In the IDA framework the book's ratio is `Optimization.reductionRatio f x s Δbar`, which is
`(a - b) / Δbar` with `a = f x`, `b = f (x + s)` by `Optimization.reductionRatio_def`. With
moreover `Δbar = ΔT` the first lemma is the exact estimate behind
`Optimization.le_reductionRatio_of_abs_sub_le`.
-/

namespace Optimization

variable {a b fx fxs ΔT Δbar η η₁ κs : ℝ}

/-- **Error decomposition of the inexact ratio.** For `Δbar > 0`,
`|(a - b) / Δbar - 1| ≤ (|a - fx| + |fxs - (fx - ΔT)| + |ΔT - Δbar| + |b - fxs|) / Δbar`. When
`ΔT` is the exact Taylor decrement at `x`, `fx - ΔT` is the Taylor polynomial at `s`, so the
second term is the Taylor remainder; the third is the error of the inexact decrement, and the first
and last are the errors of the function values (zero in the IDA framework). -/
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

/-- **Very-successful criterion for the inexact ratio.** If `Δbar > 0` and the total error
`|a - fx| + |fxs - (fx - ΔT)| + |ΔT - Δbar| + |b - fxs|` is at most `(1 - η) Δbar`, then
`η ≤ (a - b) / Δbar`. -/
theorem le_div_of_inexact_error_le (hΔ : 0 < Δbar)
    (herr : |a - fx| + |fxs - (fx - ΔT)| + |ΔT - Δbar| + |b - fxs| ≤ (1 - η) * Δbar) :
    η ≤ (a - b) / Δbar := by
  have h1 := abs_div_sub_one_le_of_inexact (a := a) (b := b) (fx := fx) (fxs := fxs) (ΔT := ΔT) hΔ
  have h2 : (|a - fx| + |fxs - (fx - ΔT)| + |ΔT - Δbar| + |b - fxs|) / Δbar ≤ 1 - η := by
    rwa [div_le_iff₀ hΔ]
  have := neg_abs_le ((a - b) / Δbar - 1)
  linarith

/-- True decrease on an accepted step with inexact values, sharp form: if `Δbar > 0`, the value
errors are at most `κs Δbar` and `η₁ ≤ (a - b) / Δbar`, then `fx - fxs ≥ (η₁ - 2 κs) Δbar`. -/
theorem sub_ge_sub_mul_of_inexact_ratio (hΔ : 0 < Δbar) (ha : |a - fx| ≤ κs * Δbar)
    (hb : |b - fxs| ≤ κs * Δbar) (hρ : η₁ ≤ (a - b) / Δbar) :
    (η₁ - 2 * κs) * Δbar ≤ fx - fxs := by
  rw [le_div_iff₀ hΔ] at hρ
  have := le_abs_self (a - fx)
  have := neg_abs_le (b - fxs)
  nlinarith [abs_sub_comm a fx]

/-- **True decrease on accepted steps with inexact values** ([cartis2022evaluation], proofs of
Lemmas 13.3.2, 13.3.7): if `Δbar > 0`, `|a - fx| ≤ κs Δbar`, `|b - fxs| ≤ κs Δbar`,
`η₁ ≤ (a - b) / Δbar` and `κs ≤ η₁ / 4`, then `fx - fxs ≥ η₁ Δbar / 2`. -/
theorem sub_ge_of_inexact_ratio (hΔ : 0 < Δbar) (ha : |a - fx| ≤ κs * Δbar)
    (hb : |b - fxs| ≤ κs * Δbar) (hρ : η₁ ≤ (a - b) / Δbar) (hκ : κs ≤ η₁ / 4) :
    η₁ / 2 * Δbar ≤ fx - fxs := by
  have := sub_ge_sub_mul_of_inexact_ratio hΔ ha hb hρ
  nlinarith

end Optimization
