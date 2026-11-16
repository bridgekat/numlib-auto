/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.MeanInequalitiesPow` for the power-sum inequality and
`Mathlib.Analysis.SpecialFunctions.Pow.Real` for the elementary bound.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Elementary inequalities for real powers

This file collects elementary inequalities for the real power $t \mapsto t^r$ on $[0, \infty)$. For
$r \ge 1$ the power is convex, which compares the $\ell^1$ norm and the $\ell^r$ norm of a finite
family: $(\sum_i a_i)^r \le n^r \sum_i a_i^r$ for $n$ nonnegative terms. This crude comparison is
the form that the $p$-Laplacian energy and the $W^{1,p}$ gradient norms use. For
$0 \le \alpha \le 1$ the power $u \mapsto u^\alpha$ is concave and lies below each of its tangent
lines, which is the weighted inequality of arithmetic and geometric means. The file also gives the
bound $(1 + t)^r \le 2^r (1 + t^r)$, a crude Young inequality $a^{p-1} b \le a^p + b^p$, and the
summability of the product of two square-summable families.

## Main results

* `Real.sum_rpow_le_card_rpow_mul_sum`: $(\sum_{i \in s} a_i)^r \le |s|^r \sum_{i \in s} a_i^r$ for
  nonnegative $a_i$ and $r \ge 1$.
* `Real.one_add_rpow_le`: $(1 + t)^p \le 2^p (1 + t^p)$ for $t \ge 0$ and $p \ge 0$.
* `Real.summable_mul_of_summable_sq`: the product of two square-summable real families is summable.
* `Real.rpow_le_tangent`: for $0 \le \alpha \le 1$, $s > 0$ and $u \ge 0$, $u^\alpha \le \alpha
  s^{\alpha - 1} u + (1 - \alpha) s^\alpha$.
* `Real.rpow_sub_one_mul_le_add`: $a^{p-1} b \le a^p + b^p$ for $a, b \ge 0$ and $p \ge 1$.
-/

namespace Real

/-- Let $s$ be a finite index set, let $a_i \ge 0$ for $i \in s$, and let $r \ge 1$ be real. Then
$$\Bigl(\sum_{i \in s} a_i\Bigr)^r \le |s|^r \sum_{i \in s} a_i^r.$$

This is the convexity of $t \mapsto t^r$ with uniform weights,
`Real.rpow_arith_mean_le_arith_mean_rpow`. The factor $|s|^r$ is cruder than the sharp factor
$|s|^{r-1}$. If $s$ is empty, both sides are $0$. -/
theorem sum_rpow_le_card_rpow_mul_sum {ι : Type*} (s : Finset ι) {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) {r : ℝ} (hr : 1 ≤ r) :
    (∑ i ∈ s, a i) ^ r ≤ (s.card : ℝ) ^ r * ∑ i ∈ s, a i ^ r := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs
    simp [Real.zero_rpow (zero_lt_one.trans_le hr).ne']
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hmean := Real.rpow_arith_mean_le_arith_mean_rpow (s := s) (fun _ ↦ (s.card : ℝ)⁻¹) a
    (fun _ _ ↦ by positivity) (by simp [Finset.sum_const, hn.ne']) ha hr
  have hsum : ∑ i ∈ s, (s.card : ℝ)⁻¹ * a i = (s.card : ℝ)⁻¹ * ∑ i ∈ s, a i := by
    rw [Finset.mul_sum]
  have hsum' : ∑ i ∈ s, (s.card : ℝ)⁻¹ * a i ^ r = (s.card : ℝ)⁻¹ * ∑ i ∈ s, a i ^ r := by
    rw [Finset.mul_sum]
  rw [hsum, hsum', Real.mul_rpow (by positivity) (Finset.sum_nonneg ha),
    Real.inv_rpow hn.le] at hmean
  have hle : (s.card : ℝ)⁻¹ * ∑ i ∈ s, a i ^ r ≤ ∑ i ∈ s, a i ^ r := by
    have h1 : (s.card : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hs.card_pos)
    have h2 : 0 ≤ ∑ i ∈ s, a i ^ r := Finset.sum_nonneg fun i hi ↦ Real.rpow_nonneg (ha i hi) r
    nlinarith
  calc (∑ i ∈ s, a i) ^ r
      = (s.card : ℝ) ^ r * (((s.card : ℝ) ^ r)⁻¹ * (∑ i ∈ s, a i) ^ r) := by
        field_simp
    _ ≤ (s.card : ℝ) ^ r * ∑ i ∈ s, a i ^ r := by
        gcongr
        exact hmean.trans hle

/-- Let $t \ge 0$ and $p \ge 0$ be real. Then
$$(1 + t)^p \le 2^p (1 + t^p).$$
-/
theorem one_add_rpow_le {t p : ℝ} (ht : 0 ≤ t) (hp : 0 ≤ p) :
    (1 + t) ^ p ≤ 2 ^ p * (1 + t ^ p) := by
  have h1 : 1 + t ≤ 2 * max 1 t := by
    have := le_max_left 1 t
    have := le_max_right 1 t
    linarith
  calc (1 + t) ^ p ≤ (2 * max 1 t) ^ p := Real.rpow_le_rpow (by positivity) h1 hp
    _ = 2 ^ p * (max 1 t) ^ p := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 2 ^ p * (1 + t ^ p) := by
      gcongr
      rcases le_total 1 t with h | h
      · rw [max_eq_right h]
        linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1) p]
      · rw [max_eq_left h, Real.one_rpow]
        linarith [Real.rpow_nonneg ht p]

/-- Let $f$ and $g$ be real families such that $\sum_k f_k^2$ and $\sum_k g_k^2$ are summable. Then
$\sum_k f_k g_k$ is summable.

The proof uses $|f_k g_k| \le (f_k^2 + g_k^2) / 2$. This is the case $p = q = 2$ of
`Real.summable_mul_of_Lp_Lq_of_nonneg` without the sign conditions. -/
theorem summable_mul_of_summable_sq {ι : Type*} {f g : ι → ℝ} (hf : Summable fun k => f k ^ 2)
    (hg : Summable fun k => g k ^ 2) : Summable fun k => f k * g k := by
  refine Summable.of_abs (Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    ((hf.add hg).div_const 2))
  rw [abs_mul]
  nlinarith [sq_nonneg (|f k| - |g k|), abs_nonneg (f k), abs_nonneg (g k), sq_abs (f k),
    sq_abs (g k)]

/-- The concave power lies below its tangent line. Let $0 \le \alpha \le 1$, $s > 0$ and $u \ge 0$.
Then
$$u^\alpha \le \alpha s^{\alpha - 1} u + (1 - \alpha) s^\alpha.$$

The right side is the tangent line of $u \mapsto u^\alpha$ at $u = s$. The inequality is the
weighted inequality of arithmetic and geometric means, and it replaces Jensen's inequality in
estimates of Hölder type. -/
theorem rpow_le_tangent {u s α : ℝ} (hu : 0 ≤ u) (hs : 0 < s) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : u ^ α ≤ α * s ^ (α - 1) * u + (1 - α) * s ^ α := by
  have h := Real.geom_mean_le_arith_mean2_weighted hα0 (by linarith : (0 : ℝ) ≤ 1 - α)
    (div_nonneg hu hs.le) zero_le_one (by ring)
  rw [Real.one_rpow, mul_one, mul_one, Real.div_rpow hu hs.le] at h
  have hsα : (0 : ℝ) < s ^ α := Real.rpow_pos_of_pos hs α
  have hmul := mul_le_mul_of_nonneg_right h hsα.le
  rw [div_mul_cancel₀ _ hsα.ne'] at hmul
  refine hmul.trans_eq ?_
  rw [Real.rpow_sub hs, Real.rpow_one]
  field_simp

end Real

/-- A crude **Young inequality**. Let $a, b \ge 0$ and $p \ge 1$ be real. Then
$$a^{p-1} b \le a^p + b^p.$$

The powers are real powers, so $a^0 = 1$ also for $a = 0$, and at $p = 1$ the inequality is
$b \le a + b$. -/
theorem Real.rpow_sub_one_mul_le_add {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    a ^ (p - 1) * b ≤ a ^ p + b ^ p := by
  rcases le_total a b with hab | hab
  · calc a ^ (p - 1) * b ≤ b ^ (p - 1) * b :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha hab (by linarith)) hb
      _ = b ^ p := by
          rw [← Real.rpow_add_one' hb (by linarith), sub_add_cancel]
      _ ≤ a ^ p + b ^ p := le_add_of_nonneg_left (Real.rpow_nonneg ha _)
  · calc a ^ (p - 1) * b ≤ a ^ (p - 1) * a :=
          mul_le_mul_of_nonneg_left hab (Real.rpow_nonneg ha _)
      _ = a ^ p := by
          rw [← Real.rpow_add_one' ha (by linarith), sub_add_cancel]
      _ ≤ a ^ p + b ^ p := le_add_of_nonneg_right (Real.rpow_nonneg hb _)
