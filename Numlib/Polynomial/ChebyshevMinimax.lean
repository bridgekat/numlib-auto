/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.RingTheory.Polynomial.Chebyshev`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Chebyshev min–max on an interval

`min {max_{t ∈ [a,b]} |p t| : deg p ≤ m, p γ = 1} = 1 / |T_m(1 + 2(a - γ)/(b - a))|` for
`γ ∉ [a, b]` (Saad Thm 6.25 / Saad-eig Thm 4.8; Rivlin Thm 1.10), its special case `γ = 0`,
and the growth estimates that turn it into geometric rates (Saad (6.128)).
Mathlib supplies `Polynomial.Chebyshev.T` and the extremal inequality
`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`.
-/

open Polynomial Polynomial.Chebyshev

namespace Polynomial.Chebyshev

/-- Closed form `T_m x = ½ ((x + √(x²-1))^m + (x - √(x²-1))^m)` for `x ≥ 1`. -/
theorem eval_T_eq_half_add_pow {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    (T ℝ m).eval x =
      ((x + Real.sqrt (x ^ 2 - 1)) ^ m + (x - Real.sqrt (x ^ 2 - 1)) ^ m) / 2 := by
  sorry

/-- `½ (x + √(x²-1))^m ≤ T_m x` for `x ≥ 1`. -/
theorem half_pow_le_eval_T {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    (x + Real.sqrt (x ^ 2 - 1)) ^ m / 2 ≤ (T ℝ m).eval x := by
  sorry

theorem one_le_eval_T {x : ℝ} (hx : 1 ≤ x) (m : ℕ) : 1 ≤ (T ℝ m).eval x := by
  sorry

/-- The shifted Chebyshev polynomial `t ↦ T_m((b + a - 2t)/(b - a)) / T_m((b + a - 2γ)/(b - a))`,
normalized to `1` at `γ`. -/
noncomputable def shifted (m : ℕ) (a b γ : ℝ) : ℝ[X] :=
  Polynomial.C (1 / (T ℝ m).eval ((b + a - 2 * γ) / (b - a))) *
    (T ℝ m).comp (Polynomial.C ((b + a) / (b - a)) - Polynomial.C (2 / (b - a)) * X)

theorem shifted_degree_le (m : ℕ) (a b γ : ℝ) : (shifted m a b γ).degree ≤ m := by
  sorry

theorem shifted_eval_self (m : ℕ) {a b γ : ℝ} (hab : a < b) (hγ : γ ∉ Set.Icc a b) :
    (shifted m a b γ).eval γ = 1 := by
  sorry

/-- Lower bound (general normalization point `γ ∉ [a, b]`): every polynomial of degree `≤ m`
with `p γ = 1` has sup over `[a, b]` at least `1 / |T_m((b + a - 2γ)/(b - a))|`. -/
theorem one_div_eval_T_le_sSup_abs_eval (m : ℕ) {a b γ : ℝ} (hab : a < b)
    (hγ : γ ∉ Set.Icc a b) (p : ℝ[X]) (hp : p.degree ≤ m) (hpγ : p.eval γ = 1) :
    1 / |(T ℝ m).eval ((b + a - 2 * γ) / (b - a))| ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc a b) := by
  sorry

/-- The bound is attained by `shifted m a b γ`. -/
theorem sSup_abs_eval_shifted (m : ℕ) {a b γ : ℝ} (hab : a < b) (hγ : γ ∉ Set.Icc a b) :
    sSup ((fun t => |(shifted m a b γ).eval t|) '' Set.Icc a b) =
      1 / |(T ℝ m).eval ((b + a - 2 * γ) / (b - a))| := by
  sorry

/-- Special case `γ = 0`, `0 < a < b` (Saad Thm 6.29's ingredient):
`min_{deg p ≤ m, p 0 = 1} max_{[a,b]} |p| = 1 / T_m((b + a)/(b - a))`. -/
theorem one_div_eval_T_le_sSup_abs_eval_of_eval_zero (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (p : ℝ[X]) (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    1 / (T ℝ m).eval ((b + a) / (b - a)) ≤ sSup ((fun t => |p.eval t|) '' Set.Icc a b) := by
  sorry

/-- `1 / T_m((κ + 1)/(κ - 1)) ≤ 2 ((√κ - 1)/(√κ + 1))^m` for `κ > 1` (Saad (6.128)). -/
theorem one_div_eval_T_le_two_mul_pow {κ : ℝ} (hκ : 1 < κ) (m : ℕ) :
    1 / (T ℝ m).eval ((κ + 1) / (κ - 1)) ≤
      2 * ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ m := by
  sorry

end Polynomial.Chebyshev
