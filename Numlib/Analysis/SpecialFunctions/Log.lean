/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Limits and bounds for logarithms

This file collects three facts about the real logarithm. First, if a nonnegative sequence satisfies
$a_m^{1/m} \to \rho > 0$, then $\frac{1}{m} \log a_m \to \log \rho$. This is the step from a
root-test limit, such as Gelfand's formula $\|G^m\|^{1/m} \to \rho(G)$, to the corresponding
logarithmic convergence rate $-\frac{1}{m} \log \|G^m\| \to -\log \rho(G)$. Second,
$|\log b| \le |\log u| + |\log v|$ when $0 < u, v \le 1$ and $uv \le b \le 1$. Third, for
$0 < \beta < 1$, the iteration count $\lceil \log(a/r) / \log \beta \rceil$ is at most
$1 + r/(a\,|\log \beta|)$.

## Main results

* `tendsto_one_div_mul_log_of_tendsto_rpow_one_div`: if $a_m \ge 0$ and $a_m^{1/m} \to \rho > 0$,
  then $\frac{1}{m} \log a_m \to \log \rho$.
* `Real.abs_log_le_of_mul_le`: $|\log b| \le |\log u| + |\log v|$ for $u, v \in (0, 1]$ and
  $uv \le b \le 1$.
* `Real.natCeil_log_div_log_le`: $\lceil \log(a/r) / \log \beta \rceil \le 1 + r/(a\,|\log \beta|)$
  for $a > 0$, $r \ge 0$ and $\beta \in (0, 1)$.
-/

open Filter Topology

/-- Let $(a_m)_{m \ge 0}$ be a sequence of nonnegative real numbers, and let $\rho > 0$. If
$a_m^{1/m} \to \rho$ as $m \to \infty$, then
$$\frac{1}{m} \log a_m \to \log \rho \qquad (m \to \infty).$$

The proof uses the continuity of $\log$ at the positive point $\rho$ and the identity
$\log(a^{1/m}) = \frac{1}{m} \log a$. With the Lean convention $\log 0 = 0$, this identity holds
also at $a = 0$. -/
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

/-- Let $u, v, b$ be real numbers with $0 < u \le 1$, $0 < v \le 1$ and $uv \le b \le 1$. Then
$$|\log b| \le |\log u| + |\log v|.$$
-/
theorem Real.abs_log_le_of_mul_le {b u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1)
    (hv1 : v ≤ 1) (hb : u * v ≤ b) (hb1 : b ≤ 1) : |Real.log b| ≤ |Real.log u| + |Real.log v| := by
  have hb0 : 0 < b := lt_of_lt_of_le (mul_pos hu hv) hb
  rw [abs_of_nonpos (Real.log_nonpos hb0.le hb1), abs_of_nonpos (Real.log_nonpos hu.le hu1),
    abs_of_nonpos (Real.log_nonpos hv.le hv1)]
  have := Real.log_le_log (mul_pos hu hv) hb
  rw [Real.log_mul hu.ne' hv.ne'] at this
  linarith

/-- Let $a > 0$, $r \ge 0$ and $0 < \beta < 1$. Then
$$\left\lceil \frac{\log(a/r)}{\log \beta} \right\rceil \le 1 + \frac{r}{a\,|\log \beta|}.$$
Thus an iteration count of the form $\lceil \log(a/r) / \log \beta \rceil$ is $O(r/a)$.

The ceiling is the natural-number ceiling `Nat.ceil`, which is $0$ for a nonpositive argument.
With the Lean conventions $a/0 = 0$ and $\log 0 = 0$, the case $r = 0$ is included, and the left
side is then $0$. -/
theorem Real.natCeil_log_div_log_le {a r β₁ : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) :
    (⌈Real.log (a / r) / Real.log β₁⌉₊ : ℝ) ≤ 1 + r / (a * |Real.log β₁|) := by
  have hl : Real.log β₁ < 0 := Real.log_neg hβ₁0 hβ₁1
  have habs : |Real.log β₁| = -Real.log β₁ := abs_of_neg hl
  have hkey : -Real.log (a / r) ≤ r / a := by
    rcases hr.eq_or_lt with rfl | hr0
    · simp
    · rw [← Real.log_inv, inv_div]
      have := Real.log_le_sub_one_of_pos (div_pos hr0 ha)
      linarith
  have hx : Real.log (a / r) / Real.log β₁ ≤ r / (a * |Real.log β₁|) :=
    calc Real.log (a / r) / Real.log β₁ = -Real.log (a / r) / -Real.log β₁ :=
          (neg_div_neg_eq _ _).symm
      _ ≤ r / a / -Real.log β₁ := div_le_div_of_nonneg_right hkey (by linarith)
      _ = r / (a * |Real.log β₁|) := by rw [habs, div_div]
  have hnn : 0 ≤ r / (a * |Real.log β₁|) := by positivity
  by_cases hx0 : 0 ≤ Real.log (a / r) / Real.log β₁
  · have := Nat.ceil_lt_add_one hx0
    linarith
  · rw [Nat.ceil_eq_zero.2 (not_le.1 hx0).le]
    push_cast
    linarith
