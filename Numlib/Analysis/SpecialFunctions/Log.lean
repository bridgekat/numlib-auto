/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Limits of logarithms of `m`-th roots

`tendsto_one_div_mul_log_of_tendsto_rpow_one_div`: if `a m ^ (1 / m) → ρ > 0` for a nonnegative
sequence, then `(1 / m) log (a m) → log ρ`. This is the step from a root-test limit such as
Gelfand's formula `‖Gᵐ‖ ^ (1 / m) → ρ(G)` to the corresponding logarithmic convergence rate
`-(1 / m) log ‖Gᵐ‖ → -log ρ(G)`.

`Real.abs_log_le_of_mul_le`: `|log b| ≤ |log u| + |log v|` for `u v ≤ b ≤ 1`, `u, v ∈ (0, 1]`.
-/

open Filter Topology

/-- If `a m ^ (1 / m) → ρ > 0` for a nonnegative sequence, then `(1 / m) log (a m) → log ρ`: the
continuity of `log` at a positive point, with `log (a ^ (1 / m)) = (1 / m) log a` also at
`a = 0`. -/
theorem tendsto_one_div_mul_log_of_tendsto_rpow_one_div {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    {ρ : ℝ} (hρ : 0 < ρ) (h : Tendsto (fun m : ℕ => a m ^ (1 / m : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun m : ℕ => (1 / m : ℝ) * Real.log (a m)) atTop (𝓝 (Real.log ρ)) := by
  refine ((Real.continuousAt_log hρ.ne').tendsto.comp h).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  simp only [Function.comp_apply]
  rcases (ha m).eq_or_lt with h0 | h0
  · rw [← h0, Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.2 (by omega))), Real.log_zero,
      mul_zero]
  · rw [Real.log_rpow h0]

/-- `|log b| ≤ |log u| + |log v|` for `0 < u v ≤ b ≤ 1` with `u, v ∈ (0, 1]`. -/
theorem Real.abs_log_le_of_mul_le {b u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1)
    (hv1 : v ≤ 1) (hb : u * v ≤ b) (hb1 : b ≤ 1) : |Real.log b| ≤ |Real.log u| + |Real.log v| := by
  have hb0 : 0 < b := lt_of_lt_of_le (mul_pos hu hv) hb
  rw [abs_of_nonpos (Real.log_nonpos hb0.le hb1), abs_of_nonpos (Real.log_nonpos hu.le hu1),
    abs_of_nonpos (Real.log_nonpos hv.le hv1)]
  have := Real.log_le_log (mul_pos hu hv) hb
  rw [Real.log_mul hu.ne' hv.ne'] at this
  linarith
