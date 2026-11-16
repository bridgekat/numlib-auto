/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.Normalize` and
`Mathlib.Analysis.InnerProductSpace.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Perturbing a direction and a rank-one projection

This module proves two stability facts that the perturbation analysis of a Householder reflector
$x \mapsto x - 2 \langle w, x \rangle w$ uses. First, the directions $a / \|a\|$ and $b / \|b\|$ of
two nearby vectors are close: $\|b / \|b\| - a / \|a\|\| \le 2 \|b - a\| / \|a\|$ for $a \neq 0$.
Second, for two vectors $a$ and $b$ of norm at most $1$, the rank-one maps
$x \mapsto \langle a, x \rangle a$ and $x \mapsto \langle b, x \rangle b$ differ by at most
$2 \|b - a\|$ in operator norm. The module also records the scaling identities $\|t e\| = |t|$ and
$\langle e, t e \rangle = t$ of a unit vector $e$.

## Main results

* `NormedSpace.norm_normalize_le_one`: $\|x / \|x\|\| \le 1$ for every $x$, including $x = 0$.
* `NormedSpace.norm_normalize_sub_normalize_le`: $\|b / \|b\| - a / \|a\|\| \le 2 \|b - a\| / \|a\|$
  for $a \neq 0$.
* `norm_inner_smul_sub_inner_smul_le`: $\|\langle b, x \rangle b - \langle a, x \rangle a\| \le 2
  \|b - a\| \|x\|$ for $\|a\|, \|b\| \le 1$.

## Implementation notes

* The direction of $x$ is Mathlib's `NormedSpace.normalize x`, which is $\|x\|^{-1} x$. It is $0$ at
  $x = 0$, because Lean sets $0^{-1} = 0$.
-/

open scoped RealInnerProductSpace

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let $E$ be a real normed space. For every $x \in E$, the normalized vector $\|x\|^{-1} x$ has
norm at most $1$: the norm is $1$ for $x \neq 0$, and the vector is $0$ for $x = 0$. -/
theorem norm_normalize_le_one (x : E) : ‖normalize x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (norm_normalize hx).le

/-- Let $E$ be a real normed space, and let $a, b \in E$ with $a \neq 0$. Then the directions of $a$
and $b$ satisfy
$$\left\| \frac{b}{\|b\|} - \frac{a}{\|a\|} \right\| \le \frac{2 \|b - a\|}{\|a\|}.$$
The bound also holds for $b = 0$, where the direction of $b$ is $0$. -/
theorem norm_normalize_sub_normalize_le {a : E} (ha : a ≠ 0) (b : E) :
    ‖normalize b - normalize a‖ ≤ 2 * ‖b - a‖ / ‖a‖ := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [le_div_iff₀ hpos]
  have key : ‖a‖ • (normalize b - normalize a) = (b - a) + (‖a‖ - ‖b‖) • normalize b := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  have h1 : |‖a‖ - ‖b‖| ≤ ‖b - a‖ := by
    rw [norm_sub_rev]
    exact abs_norm_sub_norm_le a b
  have h2 : |‖a‖ - ‖b‖| * ‖normalize b‖ ≤ ‖b - a‖ :=
    (mul_le_of_le_one_right (abs_nonneg _) (norm_normalize_le_one b)).trans h1
  calc ‖normalize b - normalize a‖ * ‖a‖ = ‖‖a‖ • (normalize b - normalize a)‖ := by
        rw [norm_smul, norm_norm, mul_comm]
    _ ≤ ‖b - a‖ + |‖a‖ - ‖b‖| * ‖normalize b‖ := by
        rw [key]
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 2 * ‖b - a‖ := by linarith

end NormedSpace

/-- Let $E$ be a real inner product space, and let $a, b \in E$ with $\|a\| \le 1$ and
$\|b\| \le 1$. Then for every $x \in E$,
$$\|\langle b, x \rangle b - \langle a, x \rangle a\| \le 2 \|b - a\| \|x\|,$$
so the rank-one maps $x \mapsto \langle a, x \rangle a$ and $x \mapsto \langle b, x \rangle b$
differ by at most $2 \|b - a\|$ in operator norm. -/
theorem norm_inner_smul_sub_inner_smul_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a b : E} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (x : E) :
    ‖⟪b, x⟫ • b - ⟪a, x⟫ • a‖ ≤ 2 * ‖b - a‖ * ‖x‖ := by
  have hsplit : ⟪b, x⟫ • b - ⟪a, x⟫ • a = ⟪b - a, x⟫ • b + ⟪a, x⟫ • (b - a) := by
    rw [inner_sub_left, sub_smul, smul_sub]
    abel
  have h1 : |⟪b - a, x⟫| * ‖b‖ ≤ ‖b - a‖ * ‖x‖ :=
    (mul_le_mul (abs_real_inner_le_norm _ _) hb (norm_nonneg _) (by positivity)).trans_eq
      (mul_one _)
  have h2 : |⟪a, x⟫| * ‖b - a‖ ≤ ‖x‖ * ‖b - a‖ :=
    mul_le_mul_of_nonneg_right ((abs_real_inner_le_norm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg x) ha)) (norm_nonneg _)
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  linarith

/-! ### Unit vectors -/

/-- Let $E$ be a real normed space and let $e \in E$ with $\|e\| = 1$. Then $\|t e\| = |t|$ for
every $t \in \mathbb{R}$. -/
theorem norm_smul_of_norm_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {e : E}
    (he : ‖e‖ = 1) (t : ℝ) : ‖t • e‖ = |t| := by
  rw [norm_smul, he, mul_one, Real.norm_eq_abs]

/-- Let $E$ be a real inner product space and let $e \in E$ with $\|e\| = 1$. Then
$\langle e, t e \rangle = t$ for every $t \in \mathbb{R}$. -/
theorem inner_smul_self_of_norm_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {e : E} (he : ‖e‖ = 1) (t : ℝ) : ⟪e, t • e⟫ = t := by
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
