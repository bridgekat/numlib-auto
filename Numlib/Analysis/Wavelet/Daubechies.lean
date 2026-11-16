/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# The Daubechies D4 scaling function

This file constructs the continuous function $\varphi : \mathbb{R} \to \mathbb{R}$ such that
$\varphi(x) = 0$ outside $[0, 3]$, $\varphi(1) = (1 + \sqrt{3})/2$, $\varphi(2) = (1 - \sqrt{3})/2$,
and
$$\varphi(x) = \tfrac{1 + \sqrt{3}}{4} \varphi(2x) + \tfrac{3 + \sqrt{3}}{4} \varphi(2x - 1) +
  \tfrac{3 - \sqrt{3}}{4} \varphi(2x - 2) + \tfrac{1 - \sqrt{3}}{4} \varphi(2x - 3)$$
for all $x$. It also proves that the support of $\varphi$ is exactly $[0, 3]$. This is the first
Daubechies scaling function after the Haar function. It is the fixed point of the **cascade
operator** of the four-tap mask $\bigl(\frac{1 + \sqrt{3}}{4}, \frac{3 + \sqrt{3}}{4}, \frac{3 -
\sqrt{3}}{4}, \frac{1 - \sqrt{3}}{4}\bigr)$. The mask, the normalization and the support are those
of [han2009theoretical], §4.5, (4.5.5)–(4.5.7); the construction is due to Daubechies (1988).

## Main definitions

* `Daubechies.cascade`: the cascade operator $T$ of the D4 mask.
* `Daubechies.IsApprox`: the invariants of the cascade iteration.
* `Daubechies.approx0`: the piecewise-linear starting function of the iteration.
* `Daubechies.approxSeq`, `Daubechies.delta`: the cascade iterates and their increments.
* `Daubechies.scalingFun`: the D4 scaling function $\varphi$, the uniform limit of the iterates.

## Main results

* `Daubechies.cascade_bound`: on the plane $v_0 + v_1 + v_2 = 0$, the cascade operator contracts by
  the factor $\sqrt{3}/2$ in a suitable norm.
* `Daubechies.scalingFun_continuous`: $\varphi$ is continuous.
* `Daubechies.scalingFun_isApprox`: $\varphi$ vanishes outside $[0, 3]$, takes the values
  $(1 \pm \sqrt{3})/2$ at $1$ and $2$, and satisfies the partition of unity $\varphi(x) +
  \varphi(x + 1) + \varphi(x + 2) = 1$ on $[0, 1]$.
* `Daubechies.scalingFun_refine`: $\varphi$ satisfies the four-term refinement equation.
* `Daubechies.scalingFun_one_half`, `Daubechies.scalingFun_three_halves`,
  `Daubechies.scalingFun_five_halves`: the values $(2 + \sqrt{3})/4$, $0$ and $(2 - \sqrt{3})/4$ of
  $\varphi$ at $1/2$, $3/2$ and $5/2$.
* `Daubechies.scalingFun_support`: the closure of the support of $\varphi$ is $[0, 3]$.
* `Daubechies.exists_scalingFun`: the existence theorem, in the form in which the properties are
  usually quoted.

## Proof outline

Existence is proved by iterating the cascade operator $T$ from a piecewise-linear function that
already has the right values at the integers, and by showing that the iterates converge uniformly.
The operator $T$ is not a contraction for the supremum norm, because the mask has
$\sum_k |p_k| = (3 + \sqrt{3})/2 > 1$. The standard remedy is a bound on the joint spectral radius
of the two matrices that drive the iteration. For this mask the bound is explicit and elementary.
Write $w(y) = (h(y), h(y + 1), h(y + 2))$ for $y \in [0, 1]$. A function $h$ that vanishes outside
$[0, 3]$ satisfies $w(y) = T_0\, w(2y)$ on $[0, 1/2]$ and $w(y) = T_1\, w(2y - 1)$ on $[1/2, 1]$,
for two explicit $3 \times 3$ matrices whose columns each sum to $1$. Both matrices fix the
direction $(1, 1, 1)$, so the relevant action is on the plane $\{v : v_0 + v_1 + v_2 = 0\}$. The
difference of two consecutive iterates lies in this plane, because the iteration preserves the
partition of unity. On this plane, in the norm $N(v) = \max\{|v_0|, 2|v_2|\}$, both $T_0$ and $T_1$
have operator norm at most $\sqrt{3}/2 < 1$: the bound for $T_0$ is exactly $\sqrt{3}/2$, and the
bound for $T_1$ is $(5 + \sqrt{3})/8$. So the increments of the iteration decay geometrically.

The equality of the support with $[0, 3]$ needs a second idea. Pair $w(y)$ with a covector $u$ and
run the two relations backwards. Then $\langle w(y), u \rangle$ on a dyadic interval
$[m/2^n, (m + 1)/2^n]$ equals $\langle w(z), u' \rangle$ on all of $[0, 1]$, where $u'$ is the image
of $u$ under a product of the two transposed matrices. Both transposes are injective, and
$w(0), w(1/2), w(1)$ span $\mathbb{R}^3$, so $u' \neq 0$ makes $\langle w(z), u' \rangle$ nonzero
somewhere. With $u$ a coordinate covector, this shows that $\varphi$ cannot vanish identically on
any nondegenerate subinterval of $[0, 3]$.
-/

noncomputable section

open Set

namespace Daubechies

/-! ### Arithmetic of $\sqrt{3}$ -/

private theorem sqrt3_mul_self : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

private theorem one_lt_sqrt3 : (1 : ℝ) < √3 := by
  nlinarith [sqrt3_mul_self, Real.sqrt_nonneg 3]

private theorem sqrt3_lt_two : √3 < 2 := by
  nlinarith [sqrt3_mul_self, Real.sqrt_nonneg 3]

/-! ### The cascade operator -/

/-- The **cascade operator** of the Daubechies D4 mask: for $f : \mathbb{R} \to \mathbb{R}$,
$$(Tf)(x) = \tfrac{1 + \sqrt{3}}{4} f(2x) + \tfrac{3 + \sqrt{3}}{4} f(2x - 1) + \tfrac{3 -
  \sqrt{3}}{4} f(2x - 2) + \tfrac{1 - \sqrt{3}}{4} f(2x - 3).$$
The scaling function is its fixed point. -/
def cascade (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 + √3) / 4 * f (2 * x) + (3 + √3) / 4 * f (2 * x - 1) + (3 - √3) / 4 * f (2 * x - 2)
    + (1 - √3) / 4 * f (2 * x - 3)

/-- The defining formula of `Daubechies.cascade`: $(Tf)(x) = \frac{1 + \sqrt{3}}{4} f(2x) +
\frac{3 + \sqrt{3}}{4} f(2x - 1) + \frac{3 - \sqrt{3}}{4} f(2x - 2) + \frac{1 - \sqrt{3}}{4}
f(2x - 3)$. -/
theorem cascade_apply (f : ℝ → ℝ) (x : ℝ) :
    cascade f x = (1 + √3) / 4 * f (2 * x) + (3 + √3) / 4 * f (2 * x - 1)
      + (3 - √3) / 4 * f (2 * x - 2) + (1 - √3) / 4 * f (2 * x - 3) := rfl

/-- The cascade operator commutes with subtraction: $T(f - g) = Tf - Tg$.

This linearity makes the increments of the iteration satisfy the same recurrence as the
iterates. -/
theorem cascade_sub (f g : ℝ → ℝ) :
    cascade (fun x => f x - g x) = fun x => cascade f x - cascade g x := by
  funext x
  simp only [cascade_apply]
  ring

/-- If $f$ is continuous, then $Tf$ is continuous, since it is a finite linear combination of
dilates of $f$. -/
theorem cascade_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (cascade f) := by
  change Continuous fun x => cascade f x
  simp only [cascade_apply]
  fun_prop

/-! ### The two-scale relations -/

section Relations

variable {f : ℝ → ℝ} (hle : ∀ x : ℝ, x ≤ 0 → f x = 0) (hge : ∀ x : ℝ, 3 ≤ x → f x = 0)

include hle hge

/-- Let $f : \mathbb{R} \to \mathbb{R}$ vanish on $(-\infty, 0]$ and on $[3, \infty)$, and let
$0 \le x \le 1/2$. Then
$$(Tf)(x) = \tfrac{1 + \sqrt{3}}{4} f(2x),$$
$$(Tf)(x + 1) = \tfrac{1 + \sqrt{3}}{4} f(2x + 2) + \tfrac{3 + \sqrt{3}}{4} f(2x + 1) +
  \tfrac{3 - \sqrt{3}}{4} f(2x),$$
$$(Tf)(x + 2) = \tfrac{3 - \sqrt{3}}{4} f(2x + 2) + \tfrac{1 - \sqrt{3}}{4} f(2x + 1).$$
So the values of $Tf$ at $x, x + 1, x + 2$ are a fixed matrix $T_0$ applied to the values of $f$
at $2x, 2x + 1, 2x + 2$. -/
theorem cascade_left {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    cascade f x = (1 + √3) / 4 * f (2 * x) ∧
      cascade f (x + 1) = (1 + √3) / 4 * f (2 * x + 2) + (3 + √3) / 4 * f (2 * x + 1)
        + (3 - √3) / 4 * f (2 * x) ∧
      cascade f (x + 2) = (3 - √3) / 4 * f (2 * x + 2) + (1 - √3) / 4 * f (2 * x + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cascade_apply, hle (2 * x - 1) (by linarith), hle (2 * x - 2) (by linarith),
      hle (2 * x - 3) (by linarith)]
    ring
  · have e0 : f (2 * (x + 1)) = f (2 * x + 2) := by congr 1; ring
    have e1 : f (2 * (x + 1) - 1) = f (2 * x + 1) := by congr 1; ring
    have e2 : f (2 * (x + 1) - 2) = f (2 * x) := by congr 1; ring
    have e3 : f (2 * (x + 1) - 3) = f (2 * x - 1) := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, e3, hle (2 * x - 1) (by linarith)]
    ring
  · have e0 : f (2 * (x + 2)) = f (2 * x + 4) := by congr 1; ring
    have e1 : f (2 * (x + 2) - 1) = f (2 * x + 3) := by congr 1; ring
    have e2 : f (2 * (x + 2) - 2) = f (2 * x + 2) := by congr 1; ring
    have e3 : f (2 * (x + 2) - 3) = f (2 * x + 1) := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, e3, hge (2 * x + 4) (by linarith),
      hge (2 * x + 3) (by linarith)]
    ring

/-- Let $f : \mathbb{R} \to \mathbb{R}$ vanish on $(-\infty, 0]$ and on $[3, \infty)$, and let
$1/2 \le x \le 1$. Then
$$(Tf)(x) = \tfrac{1 + \sqrt{3}}{4} f(2x) + \tfrac{3 + \sqrt{3}}{4} f(2x - 1),$$
$$(Tf)(x + 1) = \tfrac{3 + \sqrt{3}}{4} f(2x + 1) + \tfrac{3 - \sqrt{3}}{4} f(2x) + \tfrac{1 -
  \sqrt{3}}{4} f(2x - 1),$$
$$(Tf)(x + 2) = \tfrac{1 - \sqrt{3}}{4} f(2x + 1).$$
So the values of $Tf$ at $x, x + 1, x + 2$ are a fixed matrix $T_1$ applied to the values of $f$
at $2x - 1, 2x, 2x + 1$. -/
theorem cascade_right {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    cascade f x = (1 + √3) / 4 * f (2 * x) + (3 + √3) / 4 * f (2 * x - 1) ∧
      cascade f (x + 1) = (3 + √3) / 4 * f (2 * x + 1) + (3 - √3) / 4 * f (2 * x)
        + (1 - √3) / 4 * f (2 * x - 1) ∧
      cascade f (x + 2) = (1 - √3) / 4 * f (2 * x + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cascade_apply, hle (2 * x - 2) (by linarith), hle (2 * x - 3) (by linarith)]
    ring
  · have e0 : f (2 * (x + 1)) = f (2 * x + 2) := by congr 1; ring
    have e1 : f (2 * (x + 1) - 1) = f (2 * x + 1) := by congr 1; ring
    have e2 : f (2 * (x + 1) - 2) = f (2 * x) := by congr 1; ring
    have e3 : f (2 * (x + 1) - 3) = f (2 * x - 1) := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, e3, hge (2 * x + 2) (by linarith)]
    ring
  · have e0 : f (2 * (x + 2)) = f (2 * x + 4) := by congr 1; ring
    have e1 : f (2 * (x + 2) - 1) = f (2 * x + 3) := by congr 1; ring
    have e2 : f (2 * (x + 2) - 2) = f (2 * x + 2) := by congr 1; ring
    have e3 : f (2 * (x + 2) - 3) = f (2 * x + 1) := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, e3, hge (2 * x + 4) (by linarith),
      hge (2 * x + 3) (by linarith), hge (2 * x + 2) (by linarith)]
    ring

end Relations

/-! ### The invariants of the iteration -/

/-- The invariants of the cascade iteration: a function $f : \mathbb{R} \to \mathbb{R}$ satisfies
`Daubechies.IsApprox` if it is continuous, vanishes on $(-\infty, 0]$ and on $[3, \infty)$,
takes the values $f(1) = (1 + \sqrt{3})/2$ and $f(2) = (1 - \sqrt{3})/2$, and satisfies the
partition of unity $f(x) + f(x + 1) + f(x + 2) = 1$ for $x \in [0, 1]$. -/
structure IsApprox (f : ℝ → ℝ) : Prop where
  /-- The function $f$ is continuous. -/
  continuous : Continuous f
  /-- The function $f$ vanishes on $(-\infty, 0]$. -/
  zero_of_le : ∀ x : ℝ, x ≤ 0 → f x = 0
  /-- The function $f$ vanishes on $[3, \infty)$. -/
  zero_of_ge : ∀ x : ℝ, 3 ≤ x → f x = 0
  /-- The value at $1$ is $f(1) = (1 + \sqrt{3})/2$. -/
  val_one : f 1 = (1 + √3) / 2
  /-- The value at $2$ is $f(2) = (1 - \sqrt{3})/2$. -/
  val_two : f 2 = (1 - √3) / 2
  /-- The partition of unity: $f(x) + f(x + 1) + f(x + 2) = 1$ for $x \in [0, 1]$. -/
  sum_eq_one : ∀ x ∈ Icc (0 : ℝ) 1, f x + f (x + 1) + f (x + 2) = 1

namespace IsApprox

variable {f : ℝ → ℝ} (h : IsApprox f)
include h

/-- A function with the invariants satisfies $f(0) = 0$. -/
theorem val_zero : f 0 = 0 := h.zero_of_le 0 le_rfl

/-- A function with the invariants satisfies $f(3) = 0$. -/
theorem val_three : f 3 = 0 := h.zero_of_ge 3 le_rfl

/-- A function with the invariants satisfies $f(x) = 0$ for $x < 0$ and for $x > 3$. -/
theorem eq_zero_of_lt_or_gt {x : ℝ} (hx : x < 0 ∨ 3 < x) : f x = 0 := by
  rcases hx with hx | hx
  · exact h.zero_of_le x hx.le
  · exact h.zero_of_ge x hx.le

/-- If $f$ has the invariants of `Daubechies.IsApprox`, then so has $Tf$. -/
theorem cascade : IsApprox (Daubechies.cascade f) := by
  refine ⟨cascade_continuous h.continuous, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [cascade_apply, h.zero_of_le (2 * x) (by linarith), h.zero_of_le (2 * x - 1) (by linarith),
      h.zero_of_le (2 * x - 2) (by linarith), h.zero_of_le (2 * x - 3) (by linarith)]
    ring
  · intro x hx
    rw [cascade_apply, h.zero_of_ge (2 * x) (by linarith), h.zero_of_ge (2 * x - 1) (by linarith),
      h.zero_of_ge (2 * x - 2) (by linarith), h.zero_of_ge (2 * x - 3) (by linarith)]
    ring
  · have e0 : f (2 * (1 : ℝ)) = f 2 := by congr 1; ring
    have e1 : f (2 * (1 : ℝ) - 1) = f 1 := by congr 1; ring
    have e2 : f (2 * (1 : ℝ) - 2) = f 0 := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, h.val_one, h.val_two, h.val_zero,
      h.zero_of_le (2 * (1 : ℝ) - 3) (by norm_num)]
    ring
  · have e0 : f (2 * (2 : ℝ)) = f 4 := by congr 1; ring
    have e1 : f (2 * (2 : ℝ) - 1) = f 3 := by congr 1; ring
    have e2 : f (2 * (2 : ℝ) - 2) = f 2 := by congr 1; ring
    have e3 : f (2 * (2 : ℝ) - 3) = f 1 := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, e3, h.val_one, h.val_two, h.val_three,
      h.zero_of_ge (4 : ℝ) (by norm_num)]
    ring
  · rintro x ⟨hx0, hx1⟩
    rcases le_total x (1 / 2) with hh | hh
    · obtain ⟨e1, e2, e3⟩ := cascade_left h.zero_of_le h.zero_of_ge hx0 hh
      rw [e1, e2, e3]
      linear_combination h.sum_eq_one (2 * x) ⟨by linarith, by linarith⟩
    · obtain ⟨e1, e2, e3⟩ := cascade_right h.zero_of_le h.zero_of_ge hh hx1
      have hs := h.sum_eq_one (2 * x - 1) ⟨by linarith, by linarith⟩
      have c1 : f (2 * x - 1 + 1) = f (2 * x) := by congr 1; ring
      have c2 : f (2 * x - 1 + 2) = f (2 * x + 1) := by congr 1; ring
      rw [c1, c2] at hs
      rw [e1, e2, e3]
      linear_combination hs

end IsApprox

/-! ### The contraction estimate -/

/-- **The joint spectral radius bound for the D4 mask.** Let $h : \mathbb{R} \to \mathbb{R}$ vanish
on $(-\infty, 0]$ and on $[3, \infty)$, and let $h(y) + h(y + 1) + h(y + 2) = 0$ for
$y \in [0, 1]$. Let $B \in \mathbb{R}$ with $|h(y)| \le B$ and $2|h(y + 2)| \le B$ for
$y \in [0, 1]$. Then for every $x \in [0, 1]$,
$$|(Th)(x)| \le \tfrac{\sqrt{3}}{2} B \quad\text{and}\quad 2\,|(Th)(x + 2)| \le
  \tfrac{\sqrt{3}}{2} B.$$

This estimate makes the cascade iteration converge; the essential fact is $\sqrt{3}/2 < 1$. -/
theorem cascade_bound {h : ℝ → ℝ} (hle : ∀ x : ℝ, x ≤ 0 → h x = 0)
    (hge : ∀ x : ℝ, 3 ≤ x → h x = 0) (hsum : ∀ x ∈ Icc (0 : ℝ) 1, h x + h (x + 1) + h (x + 2) = 0)
    {B : ℝ} (hb1 : ∀ x ∈ Icc (0 : ℝ) 1, |h x| ≤ B) (hb2 : ∀ x ∈ Icc (0 : ℝ) 1, 2 * |h (x + 2)| ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |cascade h x| ≤ √3 / 2 * B ∧ 2 * |cascade h (x + 2)| ≤ √3 / 2 * B := by
  obtain ⟨hx0, hx1⟩ := hx
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb1 0 ⟨le_rfl, by norm_num⟩)
  have hs1 := one_lt_sqrt3
  have hs2 := sqrt3_lt_two
  rcases le_total x (1 / 2) with hh | hh
  · have hmem : (2 * x) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    obtain ⟨e1, -, e3⟩ := cascade_left hle hge hx0 hh
    have ha : |h (2 * x)| ≤ B := hb1 _ hmem
    have hc : |h (2 * x + 2)| ≤ B / 2 := by
      have hb' : 2 * |h (2 * x + 2)| ≤ B := hb2 _ hmem
      linarith
    constructor
    · rw [e1, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (1 + √3) / 4)]
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (by linarith : (0 : ℝ) ≤ 1 + √3),
        mul_nonneg hB (by linarith : (0 : ℝ) ≤ √3 - 1)]
    · have key : cascade h (x + 2) = 1 / 2 * h (2 * x + 2) + (√3 - 1) / 4 * h (2 * x) := by
        rw [e3]
        linear_combination ((1 - √3) / 4) * hsum (2 * x) hmem
      rw [key]
      have habs : |1 / 2 * h (2 * x + 2) + (√3 - 1) / 4 * h (2 * x)|
          ≤ 1 / 2 * |h (2 * x + 2)| + (√3 - 1) / 4 * |h (2 * x)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ (√3 - 1) / 4)]
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (by linarith : (0 : ℝ) ≤ √3 - 1)]
  · have hmem : (2 * x - 1) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    obtain ⟨e1, -, e3⟩ := cascade_right hle hge hh hx1
    have ha : |h (2 * x - 1)| ≤ B := hb1 _ hmem
    have hc : |h (2 * x + 1)| ≤ B / 2 := by
      have hb' : 2 * |h (2 * x - 1 + 2)| ≤ B := hb2 _ hmem
      have he : h (2 * x - 1 + 2) = h (2 * x + 1) := by congr 1; ring
      rw [he] at hb'
      linarith
    have hsum' : h (2 * x - 1) + h (2 * x) + h (2 * x + 1) = 0 := by
      have hz := hsum (2 * x - 1) hmem
      have c1 : h (2 * x - 1 + 1) = h (2 * x) := by congr 1; ring
      have c2 : h (2 * x - 1 + 2) = h (2 * x + 1) := by congr 1; ring
      rw [c1, c2] at hz
      exact hz
    constructor
    · have key : cascade h x = 1 / 2 * h (2 * x - 1) + -((1 + √3) / 4) * h (2 * x + 1) := by
        rw [e1]
        linear_combination ((1 + √3) / 4) * hsum'
      rw [key]
      have habs : |1 / 2 * h (2 * x - 1) + -((1 + √3) / 4) * h (2 * x + 1)|
          ≤ 1 / 2 * |h (2 * x - 1)| + (1 + √3) / 4 * |h (2 * x + 1)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
          abs_of_nonpos (by linarith : -((1 + √3) / 4) ≤ 0)]
        linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (by linarith : (0 : ℝ) ≤ 1 + √3),
        sqrt3_mul_self, mul_nonneg hB (by nlinarith [sqrt3_mul_self] : (0 : ℝ) ≤ 3 * √3 - 5)]
    · rw [e3, abs_mul, abs_of_nonpos (by linarith : (1 - √3) / 4 ≤ 0)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (by linarith : (0 : ℝ) ≤ √3 - 1),
        abs_nonneg (h (2 * x + 1))]

/-! ### The starting function of the iteration -/

/-- The unit **hat function** $\operatorname{hat}(t) = \max\{0, 1 - |t|\}$, which is supported on
$[-1, 1]$. -/
def hat (t : ℝ) : ℝ := max 0 (1 - |t|)

/-- The hat function is continuous. -/
theorem hat_continuous : Continuous hat := by
  change Continuous fun t => max 0 (1 - |t|)
  fun_prop

/-- If $|t| \ge 1$, then $\operatorname{hat}(t) = 0$. -/
theorem hat_of_one_le {t : ℝ} (ht : 1 ≤ |t|) : hat t = 0 := max_eq_left (by linarith)

/-- If $|t| \le 1$, then $\operatorname{hat}(t) = 1 - |t|$. -/
theorem hat_of_le_one {t : ℝ} (ht : |t| ≤ 1) : hat t = 1 - |t| := max_eq_right (by linarith)

/-- The starting function of the cascade iteration:
$$f_0(x) = \tfrac{1 + \sqrt{3}}{2} \operatorname{hat}(x - 1) + \tfrac{1 - \sqrt{3}}{2}
  \operatorname{hat}(x - 2).$$
It is the piecewise-linear function with knots at $0, 1, 2, 3$ and the values $0$,
$(1 + \sqrt{3})/2$, $(1 - \sqrt{3})/2$, $0$ there. -/
def approx0 (x : ℝ) : ℝ := (1 + √3) / 2 * hat (x - 1) + (1 - √3) / 2 * hat (x - 2)

/-- The defining formula of `Daubechies.approx0`: $f_0(x) = \frac{1 + \sqrt{3}}{2}
\operatorname{hat}(x - 1) + \frac{1 - \sqrt{3}}{2} \operatorname{hat}(x - 2)$. -/
theorem approx0_apply (x : ℝ) :
    approx0 x = (1 + √3) / 2 * hat (x - 1) + (1 - √3) / 2 * hat (x - 2) := rfl

/-- The starting function $f_0$ has all the invariants of `Daubechies.IsApprox`, the partition of
unity included. This is the reason for placing its two hat functions at $1$ and $2$ with the
prescribed heights. -/
theorem approx0_isApprox : IsApprox approx0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Continuous fun x => (1 + √3) / 2 * hat (x - 1) + (1 - √3) / 2 * hat (x - 2)
    exact ((hat_continuous.comp (continuous_id.sub continuous_const)).const_mul _).add
      ((hat_continuous.comp (continuous_id.sub continuous_const)).const_mul _)
  · intro x hx
    rw [approx0_apply, hat_of_one_le (t := x - 1) (by rw [abs_of_nonpos (by linarith)]; linarith),
      hat_of_one_le (t := x - 2) (by rw [abs_of_nonpos (by linarith)]; linarith)]
    ring
  · intro x hx
    rw [approx0_apply, hat_of_one_le (t := x - 1) (by rw [abs_of_nonneg (by linarith)]; linarith),
      hat_of_one_le (t := x - 2) (by rw [abs_of_nonneg (by linarith)]; linarith)]
    ring
  · have e1 : hat ((1 : ℝ) - 1) = 1 := by
      rw [show (1 : ℝ) - 1 = 0 by norm_num, hat_of_le_one (t := 0) (by norm_num)]
      norm_num
    have e2 : hat ((1 : ℝ) - 2) = 0 := by
      refine hat_of_one_le (t := (1 : ℝ) - 2) ?_
      rw [show (1 : ℝ) - 2 = -1 by norm_num]
      norm_num
    rw [approx0_apply, e1, e2]
    ring
  · have e1 : hat ((2 : ℝ) - 1) = 0 := by
      refine hat_of_one_le (t := (2 : ℝ) - 1) ?_
      rw [show (2 : ℝ) - 1 = 1 by norm_num]
      norm_num
    have e2 : hat ((2 : ℝ) - 2) = 1 := by
      rw [show (2 : ℝ) - 2 = 0 by norm_num, hat_of_le_one (t := 0) (by norm_num)]
      norm_num
    rw [approx0_apply, e1, e2]
    ring
  · rintro x ⟨hx0, hx1⟩
    have a1 : hat (x - 1) = x := by
      rw [hat_of_le_one (t := x - 1) (by rw [abs_of_nonpos (by linarith)]; linarith),
        abs_of_nonpos (by linarith : x - 1 ≤ 0)]
      ring
    have a2 : hat (x - 2) = 0 :=
      hat_of_one_le (t := x - 2) (by rw [abs_of_nonpos (by linarith)]; linarith)
    have b1 : hat (x + 1 - 1) = 1 - x := by
      have e : x + 1 - 1 = x := by ring
      rw [e, hat_of_le_one (t := x) (by rw [abs_of_nonneg hx0]; linarith), abs_of_nonneg hx0]
    have b2 : hat (x + 1 - 2) = x := by
      have e : x + 1 - 2 = x - 1 := by ring
      rw [e, a1]
    have c1 : hat (x + 2 - 1) = 0 := by
      have e : x + 2 - 1 = x + 1 := by ring
      rw [e]
      exact hat_of_one_le (t := x + 1) (by rw [abs_of_nonneg (by linarith)]; linarith)
    have c2 : hat (x + 2 - 2) = 1 - x := by
      have e : x + 2 - 2 = x := by ring
      rw [e, hat_of_le_one (t := x) (by rw [abs_of_nonneg hx0]; linarith), abs_of_nonneg hx0]
    rw [approx0_apply, approx0_apply, approx0_apply, a1, a2, b1, b2, c1, c2]
    ring

/-! ### The cascade iterates and their increments -/

/-- The cascade iterates: $f_0$ is the starting function `Daubechies.approx0`, and
$f_{n+1} = T f_n$. -/
def approxSeq : ℕ → ℝ → ℝ
  | 0 => approx0
  | n + 1 => cascade (approxSeq n)

/-- Every cascade iterate $f_n$ has the invariants of `Daubechies.IsApprox`. -/
theorem approxSeq_isApprox : ∀ n : ℕ, IsApprox (approxSeq n)
  | 0 => approx0_isApprox
  | n + 1 => (approxSeq_isApprox n).cascade

/-- The increment $\delta_n = f_{n+1} - f_n$ of the cascade iteration. -/
def delta (n : ℕ) (x : ℝ) : ℝ := approxSeq (n + 1) x - approxSeq n x

/-- The defining formula of `Daubechies.delta`: $\delta_n(x) = f_{n+1}(x) - f_n(x)$. -/
theorem delta_apply (n : ℕ) (x : ℝ) : delta n x = approxSeq (n + 1) x - approxSeq n x := rfl

/-- The increments satisfy the cascade recurrence: $\delta_{n+1} = T \delta_n$.

This follows from the linearity of $T$, and it turns the contraction estimate
`Daubechies.cascade_bound` into geometric decay. -/
theorem delta_succ (n : ℕ) : delta (n + 1) = cascade (delta n) := by
  have h : delta n = fun x => approxSeq (n + 1) x - approxSeq n x := rfl
  rw [h, cascade_sub]
  rfl

/-- Every increment $\delta_n$ is continuous. -/
theorem delta_continuous (n : ℕ) : Continuous (delta n) :=
  ((approxSeq_isApprox (n + 1)).continuous).sub ((approxSeq_isApprox n).continuous)

/-- Every increment $\delta_n$ vanishes on $(-\infty, 0]$. -/
theorem delta_zero_of_le (n : ℕ) (x : ℝ) (hx : x ≤ 0) : delta n x = 0 := by
  rw [delta_apply, (approxSeq_isApprox (n + 1)).zero_of_le x hx,
    (approxSeq_isApprox n).zero_of_le x hx, sub_zero]

/-- Every increment $\delta_n$ vanishes on $[3, \infty)$. -/
theorem delta_zero_of_ge (n : ℕ) (x : ℝ) (hx : 3 ≤ x) : delta n x = 0 := by
  rw [delta_apply, (approxSeq_isApprox (n + 1)).zero_of_ge x hx,
    (approxSeq_isApprox n).zero_of_ge x hx, sub_zero]

/-- The increments lie in the plane $v_0 + v_1 + v_2 = 0$: for $x \in [0, 1]$,
$$\delta_n(x) + \delta_n(x + 1) + \delta_n(x + 2) = 0.$$

This holds because both iterates satisfy the partition of unity. The two cascade matrices
contract on this plane. -/
theorem delta_sum (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    delta n x + delta n (x + 1) + delta n (x + 2) = 0 := by
  have h1 := (approxSeq_isApprox (n + 1)).sum_eq_one x hx
  have h2 := (approxSeq_isApprox n).sum_eq_one x hx
  simp only [delta_apply]
  linarith

/-- Every increment vanishes at $1$: $\delta_n(1) = 0$. -/
theorem delta_val_one (n : ℕ) : delta n 1 = 0 := by
  rw [delta_apply, (approxSeq_isApprox (n + 1)).val_one, (approxSeq_isApprox n).val_one, sub_self]

/-- Every increment vanishes at $2$: $\delta_n(2) = 0$. -/
theorem delta_val_two (n : ℕ) : delta n 2 = 0 := by
  rw [delta_apply, (approxSeq_isApprox (n + 1)).val_two, (approxSeq_isApprox n).val_two, sub_self]

/-! ### Geometric decay of the increments -/

private theorem delta_bound_step {B : ℝ}
    (h0 : ∀ x ∈ Icc (0 : ℝ) 1, |delta 0 x| ≤ B)
    (h0' : ∀ x ∈ Icc (0 : ℝ) 1, 2 * |delta 0 (x + 2)| ≤ B) (n : ℕ) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      |delta n x| ≤ (√3 / 2) ^ n * B ∧ 2 * |delta n (x + 2)| ≤ (√3 / 2) ^ n * B := by
  induction n with
  | zero =>
    intro x hx
    simpa using ⟨h0 x hx, h0' x hx⟩
  | succ n ih =>
    intro x hx
    have hb1 : ∀ y ∈ Icc (0 : ℝ) 1, |delta n y| ≤ (√3 / 2) ^ n * B := fun y hy => (ih y hy).1
    have hb2 : ∀ y ∈ Icc (0 : ℝ) 1, 2 * |delta n (y + 2)| ≤ (√3 / 2) ^ n * B :=
      fun y hy => (ih y hy).2
    have hkey := cascade_bound (delta_zero_of_le n) (delta_zero_of_ge n)
      (fun y hy => delta_sum n hy) hb1 hb2 hx
    rw [delta_succ]
    constructor
    · refine hkey.1.trans (le_of_eq ?_)
      ring
    · refine hkey.2.trans (le_of_eq ?_)
      ring

private theorem exists_delta_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (x : ℝ), |delta n x| ≤ (√3 / 2) ^ n * B := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 3) isCompact_Icc
    (f := delta 0) (delta_continuous 0).continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, by norm_num⟩)
  have h0 : ∀ x ∈ Icc (0 : ℝ) 1, |delta 0 x| ≤ 2 * C := by
    rintro x ⟨hx0, hx1⟩
    have := hC x ⟨hx0, by linarith⟩
    rw [Real.norm_eq_abs] at this
    linarith
  have h0' : ∀ x ∈ Icc (0 : ℝ) 1, 2 * |delta 0 (x + 2)| ≤ 2 * C := by
    rintro x ⟨hx0, hx1⟩
    have := hC (x + 2) ⟨by linarith, by linarith⟩
    rw [Real.norm_eq_abs] at this
    linarith
  refine ⟨3 * C, by linarith, fun n x => ?_⟩
  have hmain := delta_bound_step h0 h0' n
  have hpow : 0 ≤ (√3 / 2) ^ n := by positivity
  rcases le_or_gt x 0 with hx | hx
  · rw [delta_zero_of_le n x hx, abs_zero]
    have : 0 ≤ (√3 / 2) ^ n * (3 * C) := by positivity
    linarith
  rcases le_or_gt 3 x with hx3 | hx3
  · rw [delta_zero_of_ge n x hx3, abs_zero]
    have : 0 ≤ (√3 / 2) ^ n * (3 * C) := by positivity
    linarith
  rcases le_or_gt x 1 with h1 | h1
  · have := (hmain x ⟨hx.le, h1⟩).1
    nlinarith [mul_nonneg hpow hC0]
  rcases le_or_gt x 2 with h2 | h2
  · have hmem : x - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hs := delta_sum n hmem
    have c1 : delta n (x - 1 + 1) = delta n x := by congr 1; ring
    have c2 : delta n (x - 1 + 2) = delta n (x + 1) := by congr 1; ring
    rw [c1, c2] at hs
    have hA := (hmain (x - 1) hmem).1
    have hB2 := (hmain (x - 1) hmem).2
    rw [c2] at hB2
    have habs : |delta n x| ≤ |delta n (x - 1)| + |delta n (x + 1)| := by
      have e : delta n x = -delta n (x - 1) + -delta n (x + 1) := by linarith
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_neg]
    nlinarith [abs_nonneg (delta n (x - 1)), abs_nonneg (delta n (x + 1))]
  · have hmem : x - 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hB2 := (hmain (x - 2) hmem).2
    have c3 : delta n (x - 2 + 2) = delta n x := by congr 1; ring
    rw [c3] at hB2
    nlinarith [abs_nonneg (delta n x), mul_nonneg hpow hC0]

/-! ### The limit -/

private theorem sqrt3_div_two_lt_one : √3 / 2 < 1 := by linarith [sqrt3_lt_two]

private theorem sqrt3_div_two_nonneg : (0 : ℝ) ≤ √3 / 2 := by positivity

/-- The **Daubechies D4 scaling function**
$$\varphi(x) = f_0(x) + \sum_{n \ge 0} \delta_n(x),$$
the limit of the cascade iterates $f_n$.

The sum is Mathlib's `tsum`. It converges for every $x$, and uniformly in $x$, because the
increments decay geometrically. -/
def scalingFun (x : ℝ) : ℝ := approx0 x + ∑' n : ℕ, delta n x

/-- The defining formula of `Daubechies.scalingFun`: $\varphi(x) = f_0(x) + \sum_{n \ge 0}
\delta_n(x)$. -/
theorem scalingFun_apply (x : ℝ) : scalingFun x = approx0 x + ∑' n : ℕ, delta n x := rfl

private theorem summable_delta_bound {B : ℝ} : Summable (fun n : ℕ => (√3 / 2) ^ n * B) :=
  ((summable_geometric_of_lt_one sqrt3_div_two_nonneg sqrt3_div_two_lt_one)).mul_right B

private theorem summable_delta (x : ℝ) : Summable (fun n : ℕ => delta n x) := by
  obtain ⟨B, -, hB⟩ := exists_delta_bound
  exact Summable.of_norm_bounded summable_delta_bound (fun n => by
    rw [Real.norm_eq_abs]; exact hB n x)

/-- For every $x \in \mathbb{R}$, the cascade iterates satisfy $f_N(x) \to \varphi(x)$ as
$N \to \infty$.

The partial sum $\sum_{n < N} \delta_n$ telescopes to $f_N - f_0$. -/
theorem approxSeq_tendsto (x : ℝ) :
    Filter.Tendsto (fun N : ℕ => approxSeq N x) Filter.atTop (nhds (scalingFun x)) := by
  have hsum := (summable_delta x).hasSum.tendsto_sum_nat
  have he : ∀ N : ℕ, approx0 x + ∑ n ∈ Finset.range N, delta n x = approxSeq N x := by
    intro N
    have := Finset.sum_range_sub (fun n : ℕ => approxSeq n x) N
    simp only [← delta_apply] at this
    rw [this]
    change approx0 x + (approxSeq N x - approxSeq 0 x) = approxSeq N x
    have h0 : approxSeq 0 x = approx0 x := rfl
    rw [h0]
    ring
  have hconst : Filter.Tendsto (fun _ : ℕ => approx0 x) Filter.atTop (nhds (approx0 x)) :=
    tendsto_const_nhds
  have h2 := hconst.add hsum
  rw [scalingFun_apply]
  simpa only [he] using h2

/-- The scaling function $\varphi$ is continuous.

The increments are bounded by a geometric series, so the cascade iterates converge uniformly. -/
theorem scalingFun_continuous : Continuous scalingFun := by
  obtain ⟨B, -, hB⟩ := exists_delta_bound
  refine (approx0_isApprox.continuous).add (continuous_tsum delta_continuous
    (u := fun n : ℕ => (√3 / 2) ^ n * B) summable_delta_bound (fun n x => ?_))
  rw [Real.norm_eq_abs]
  exact hB n x

/-- The scaling function $\varphi$ has all the invariants of `Daubechies.IsApprox`: it is
continuous, vanishes on $(-\infty, 0]$ and on $[3, \infty)$, takes the values
$(1 \pm \sqrt{3})/2$ at $1$ and $2$, and satisfies the partition of unity on $[0, 1]$. -/
theorem scalingFun_isApprox : IsApprox scalingFun := by
  refine ⟨scalingFun_continuous, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have : ∀ n : ℕ, delta n x = 0 := fun n => delta_zero_of_le n x hx
    simp only [scalingFun, this, tsum_zero, add_zero]
    exact approx0_isApprox.zero_of_le x hx
  · intro x hx
    have : ∀ n : ℕ, delta n x = 0 := fun n => delta_zero_of_ge n x hx
    simp only [scalingFun, this, tsum_zero, add_zero]
    exact approx0_isApprox.zero_of_ge x hx
  · simp only [scalingFun, delta_val_one, tsum_zero, add_zero]
    exact approx0_isApprox.val_one
  · simp only [scalingFun, delta_val_two, tsum_zero, add_zero]
    exact approx0_isApprox.val_two
  · intro x hx
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    refine tendsto_nhds_unique ?_ hconst
    have := ((approxSeq_tendsto x).add (approxSeq_tendsto (x + 1))).add
      (approxSeq_tendsto (x + 2))
    refine this.congr (fun N => ?_)
    exact (approxSeq_isApprox N).sum_eq_one x hx

/-- The scaling function satisfies the four-term D4 refinement equation: for every
$x \in \mathbb{R}$,
$$\varphi(x) = \tfrac{1 + \sqrt{3}}{4} \varphi(2x) + \tfrac{3 + \sqrt{3}}{4} \varphi(2x - 1) +
  \tfrac{3 - \sqrt{3}}{4} \varphi(2x - 2) + \tfrac{1 - \sqrt{3}}{4} \varphi(2x - 3).$$
-/
theorem scalingFun_refine (x : ℝ) :
    scalingFun x = (1 + √3) / 4 * scalingFun (2 * x) + (3 + √3) / 4 * scalingFun (2 * x - 1)
      + (3 - √3) / 4 * scalingFun (2 * x - 2) + (1 - √3) / 4 * scalingFun (2 * x - 3) := by
  have hlim : Filter.Tendsto (fun N : ℕ => cascade (approxSeq N) x) Filter.atTop
      (nhds (cascade scalingFun x)) := by
    simp only [cascade_apply]
    exact ((((approxSeq_tendsto (2 * x)).const_mul _).add
      ((approxSeq_tendsto (2 * x - 1)).const_mul _)).add
      ((approxSeq_tendsto (2 * x - 2)).const_mul _)).add
      ((approxSeq_tendsto (2 * x - 3)).const_mul _)
  have hlim2 : Filter.Tendsto (fun N : ℕ => cascade (approxSeq N) x) Filter.atTop
      (nhds (scalingFun x)) := (approxSeq_tendsto x).comp (Filter.tendsto_add_atTop_nat 1)
  rw [← cascade_apply]
  exact tendsto_nhds_unique hlim2 hlim

/-! ### Values at the first dyadic points -/

/-- The scaling function is a fixed point of the cascade operator: $T\varphi = \varphi$. -/
theorem cascade_scalingFun (x : ℝ) : cascade scalingFun x = scalingFun x :=
  (scalingFun_refine x).symm

/-- The value at $1/2$: $\varphi(1/2) = (2 + \sqrt{3})/4$.

In the refinement equation at $1/2$, the terms $\varphi(-1)$ and $\varphi(-2)$ vanish and
$\varphi(0) = 0$, so only $\frac{1 + \sqrt{3}}{4} \varphi(1)$ remains. -/
theorem scalingFun_one_half : scalingFun (1 / 2) = (2 + √3) / 4 := by
  have h := scalingFun_refine (1 / 2)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num,
    show (1 : ℝ) - 2 = -1 by norm_num, show (1 : ℝ) - 3 = -2 by norm_num,
    scalingFun_isApprox.val_one, scalingFun_isApprox.val_zero,
    scalingFun_isApprox.zero_of_le (-1) (by norm_num),
    scalingFun_isApprox.zero_of_le (-2) (by norm_num)] at h
  rw [h]
  linear_combination sqrt3_mul_self / 8

/-- The value at $3/2$: $\varphi(3/2) = 0$, from the refinement equation at $3/2$. -/
theorem scalingFun_three_halves : scalingFun (3 / 2) = 0 := by
  have h := scalingFun_refine (3 / 2)
  rw [show (2 : ℝ) * (3 / 2) = 3 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num,
    show (3 : ℝ) - 2 = 1 by norm_num, show (3 : ℝ) - 3 = 0 by norm_num,
    scalingFun_isApprox.val_one, scalingFun_isApprox.val_two, scalingFun_isApprox.val_zero,
    scalingFun_isApprox.val_three] at h
  rw [h]
  linear_combination (-1 / 4 : ℝ) * sqrt3_mul_self

/-- The value at $5/2$: $\varphi(5/2) = (2 - \sqrt{3})/4$, from the refinement equation at $5/2$.

With `Daubechies.scalingFun_one_half` and `Daubechies.scalingFun_three_halves`, these are the
three half-integer values that the span argument behind `Daubechies.scalingFun_support` needs. -/
theorem scalingFun_five_halves : scalingFun (5 / 2) = (2 - √3) / 4 := by
  have h := scalingFun_refine (5 / 2)
  rw [show (2 : ℝ) * (5 / 2) = 5 by norm_num, show (5 : ℝ) - 1 = 4 by norm_num,
    show (5 : ℝ) - 2 = 3 by norm_num, show (5 : ℝ) - 3 = 2 by norm_num,
    scalingFun_isApprox.val_two, scalingFun_isApprox.val_three,
    scalingFun_isApprox.zero_of_ge 4 (by norm_num),
    scalingFun_isApprox.zero_of_ge 5 (by norm_num)] at h
  rw [h]
  linear_combination sqrt3_mul_self / 8

/-! ### Pairing against a covector -/

/-- The pairing $u_0 \varphi(y) + u_1 \varphi(y + 1) + u_2 \varphi(y + 2)$ of the vector
$(\varphi(y), \varphi(y + 1), \varphi(y + 2))$ with a covector $(u_0, u_1, u_2)$. -/
private def pairing (u₀ u₁ u₂ y : ℝ) : ℝ :=
  u₀ * scalingFun y + u₁ * scalingFun (y + 1) + u₂ * scalingFun (y + 2)

private theorem pairing_apply (u₀ u₁ u₂ y : ℝ) :
    pairing u₀ u₁ u₂ y = u₀ * scalingFun y + u₁ * scalingFun (y + 1)
      + u₂ * scalingFun (y + 2) := rfl

private theorem refine_left {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    scalingFun x = (1 + √3) / 4 * scalingFun (2 * x) ∧
      scalingFun (x + 1) = (1 + √3) / 4 * scalingFun (2 * x + 2)
        + (3 + √3) / 4 * scalingFun (2 * x + 1) + (3 - √3) / 4 * scalingFun (2 * x) ∧
      scalingFun (x + 2) = (3 - √3) / 4 * scalingFun (2 * x + 2)
        + (1 - √3) / 4 * scalingFun (2 * x + 1) := by
  obtain ⟨e1, e2, e3⟩ := cascade_left scalingFun_isApprox.zero_of_le
    scalingFun_isApprox.zero_of_ge hx0 hx1
  rw [cascade_scalingFun] at e1 e2 e3
  exact ⟨e1, e2, e3⟩

private theorem refine_right {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    scalingFun x = (1 + √3) / 4 * scalingFun (2 * x)
        + (3 + √3) / 4 * scalingFun (2 * x - 1) ∧
      scalingFun (x + 1) = (3 + √3) / 4 * scalingFun (2 * x + 1)
        + (3 - √3) / 4 * scalingFun (2 * x) + (1 - √3) / 4 * scalingFun (2 * x - 1) ∧
      scalingFun (x + 2) = (1 - √3) / 4 * scalingFun (2 * x + 1) := by
  obtain ⟨e1, e2, e3⟩ := cascade_right scalingFun_isApprox.zero_of_le
    scalingFun_isApprox.zero_of_ge hx0 hx1
  rw [cascade_scalingFun] at e1 e2 e3
  exact ⟨e1, e2, e3⟩

private theorem pairing_left (u₀ u₁ u₂ : ℝ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    pairing u₀ u₁ u₂ y = pairing ((1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁)
      ((3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂) ((1 + √3) / 4 * u₁ + (3 - √3) / 4 * u₂) (2 * y) := by
  obtain ⟨e1, e2, e3⟩ := refine_left hy0 hy1
  rw [pairing_apply, pairing_apply, e1, e2, e3]
  ring

private theorem pairing_right (u₀ u₁ u₂ : ℝ) {y : ℝ} (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 1) :
    pairing u₀ u₁ u₂ y = pairing ((3 + √3) / 4 * u₀ + (1 - √3) / 4 * u₁)
      ((1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁) ((3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂)
      (2 * y - 1) := by
  obtain ⟨e1, e2, e3⟩ := refine_right hy0 hy1
  have c1 : scalingFun (2 * y - 1 + 1) = scalingFun (2 * y) := by congr 1; ring
  have c2 : scalingFun (2 * y - 1 + 2) = scalingFun (2 * y + 1) := by congr 1; ring
  rw [pairing_apply, pairing_apply, e1, e2, e3, c1, c2]
  ring

/-! ### Injectivity of the transposes, and the span of $w(0), w(1/2), w(1)$ -/

private theorem covector_left_eq_zero {u₀ u₁ u₂ : ℝ}
    (e1 : (1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁ = 0)
    (e2 : (3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂ = 0)
    (e3 : (1 + √3) / 4 * u₁ + (3 - √3) / 4 * u₂ = 0) : u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0 := by
  have hs := one_lt_sqrt3
  have hs2 := sqrt3_lt_two
  have h2 : -(1 / 2 : ℝ) * u₂ = 0 := by
    linear_combination ((1 + √3) / 4) * e2 - ((3 + √3) / 4) * e3
  have hu2 : u₂ = 0 := by linarith
  have hu1 : u₁ = 0 :=
    (mul_eq_zero_iff_right (b := (3 + √3) / 4) (by intro hc; nlinarith)).1
      (by linear_combination e2 - ((1 - √3) / 4) * hu2)
  have hu0 : u₀ = 0 :=
    (mul_eq_zero_iff_right (b := (1 + √3) / 4) (by intro hc; nlinarith)).1
      (by linear_combination e1 - ((3 - √3) / 4) * hu1)
  exact ⟨hu0, hu1, hu2⟩

private theorem covector_right_eq_zero {u₀ u₁ u₂ : ℝ}
    (e1 : (3 + √3) / 4 * u₀ + (1 - √3) / 4 * u₁ = 0)
    (e2 : (1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁ = 0)
    (e3 : (3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂ = 0) : u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0 := by
  have hs := one_lt_sqrt3
  have hs2 := sqrt3_lt_two
  have h2 : -(1 / 2 : ℝ) * u₁ = 0 := by
    linear_combination ((1 + √3) / 4) * e1 - ((3 + √3) / 4) * e2
  have hu1 : u₁ = 0 := by linarith
  have hu0 : u₀ = 0 :=
    (mul_eq_zero_iff_right (b := (3 + √3) / 4) (by intro hc; nlinarith)).1
      (by linear_combination e1 - ((1 - √3) / 4) * hu1)
  have hu2 : u₂ = 0 :=
    (mul_eq_zero_iff_right (b := (1 - √3) / 4) (by intro hc; nlinarith)).1
      (by linear_combination e3 - ((3 + √3) / 4) * hu1)
  exact ⟨hu0, hu1, hu2⟩

private theorem covector_eq_zero {u₀ u₁ u₂ : ℝ} (h0 : pairing u₀ u₁ u₂ 0 = 0)
    (hh : pairing u₀ u₁ u₂ (1 / 2) = 0) (h1 : pairing u₀ u₁ u₂ 1 = 0) :
    u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0 := by
  have hs := one_lt_sqrt3
  have hs2 := sqrt3_lt_two
  rw [pairing_apply, show (0 : ℝ) + 1 = 1 by norm_num, show (0 : ℝ) + 2 = 2 by norm_num,
    scalingFun_isApprox.val_zero, scalingFun_isApprox.val_one,
    scalingFun_isApprox.val_two] at h0
  rw [pairing_apply, show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num,
    show (1 : ℝ) / 2 + 2 = 5 / 2 by norm_num, scalingFun_one_half, scalingFun_three_halves,
    scalingFun_five_halves] at hh
  rw [pairing_apply, show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) + 2 = 3 by norm_num,
    scalingFun_isApprox.val_one, scalingFun_isApprox.val_two,
    scalingFun_isApprox.val_three] at h1
  have key : (4 - 2 * √3) * u₂ = 0 := by
    linear_combination (1 - √3) * h0 - (1 + √3) * h1 + 4 * hh + ((u₀ - u₂) / 2) * sqrt3_mul_self
  have hu2 : u₂ = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (by intro hc; linarith)
    · exact h
  have hu1 : u₁ = 0 :=
    (mul_eq_zero_iff_right (b := (1 + √3) / 2) (by intro hc; nlinarith)).1
      (by linear_combination h0 - ((1 - √3) / 2) * hu2)
  have hu0 : u₀ = 0 :=
    (mul_eq_zero_iff_right (b := (1 + √3) / 2) (by intro hc; nlinarith)).1
      (by linear_combination h1 - ((1 - √3) / 2) * hu1)
  exact ⟨hu0, hu1, hu2⟩

/-! ### No covector pairing vanishes on a dyadic interval -/

private theorem pairing_dyadic : ∀ (n m : ℕ), m < 2 ^ n → ∀ u₀ u₁ u₂ : ℝ,
    (∀ y : ℝ, (m : ℝ) ≤ y * 2 ^ n → y * 2 ^ n ≤ (m : ℝ) + 1 → pairing u₀ u₁ u₂ y = 0) →
    u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0 := by
  intro n
  induction n with
  | zero =>
    intro m hm u₀ u₁ u₂ h
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    refine covector_eq_zero (h 0 ?_ ?_) (h (1 / 2) ?_ ?_) (h 1 ?_ ?_) <;> norm_num
  | succ n ih =>
    intro m hm u₀ u₁ u₂ h
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    have hsplit : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rcases le_or_gt (m + 1) (2 ^ n) with hcase | hcase
    · have hmn : m < 2 ^ n := by omega
      have hmr : (m : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hcase
      obtain ⟨a0, a1, a2⟩ := ih m hmn ((1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁)
        ((3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂) ((1 + √3) / 4 * u₁ + (3 - √3) / 4 * u₂)
        (by
          intro z hz1 hz2
          have hz0 : 0 ≤ z := by nlinarith
          have hzle : z ≤ 1 := by nlinarith
          have hkey := pairing_left u₀ u₁ u₂ (y := z / 2) (by linarith) (by linarith)
          rw [show (2 : ℝ) * (z / 2) = z by ring] at hkey
          rw [← hkey]
          refine h (z / 2) ?_ ?_
          · rw [hsplit]; nlinarith
          · rw [hsplit]; nlinarith)
      exact covector_left_eq_zero a0 a1 a2
    · have hmn : m - 2 ^ n < 2 ^ n := by omega
      have hmr : ((m - 2 ^ n : ℕ) : ℝ) + 1 ≤ 2 ^ n := by
        have hnat : (m - 2 ^ n) + 1 ≤ 2 ^ n := by
          omega
        exact_mod_cast hnat
      have hcast : (m : ℝ) = ((m - 2 ^ n : ℕ) : ℝ) + 2 ^ n := by
        have hnat : m = (m - 2 ^ n) + 2 ^ n := by omega
        rw [show ((m : ℕ) : ℝ) = (((m - 2 ^ n) + 2 ^ n : ℕ) : ℝ) by rw [← hnat]]
        push_cast
        ring
      obtain ⟨a0, a1, a2⟩ := ih (m - 2 ^ n) hmn ((3 + √3) / 4 * u₀ + (1 - √3) / 4 * u₁)
        ((1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁) ((3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂)
        (by
          intro z hz1 hz2
          have hz0 : 0 ≤ z := by nlinarith
          have hzle : z ≤ 1 := by nlinarith
          have hkey := pairing_right u₀ u₁ u₂ (y := (z + 1) / 2) (by linarith) (by linarith)
          rw [show (2 : ℝ) * ((z + 1) / 2) - 1 = z by ring] at hkey
          rw [← hkey]
          refine h ((z + 1) / 2) ?_ ?_
          · rw [hsplit, hcast]; nlinarith
          · rw [hsplit, hcast]; nlinarith)
      exact covector_right_eq_zero a0 a1 a2

private theorem exists_pairing_ne_zero {u₀ u₁ u₂ : ℝ} (hu : ¬(u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0))
    {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    ∃ y ∈ Icc a b, pairing u₀ u₁ u₂ y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hba : 0 < b - a := by linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / (b - a)) (by norm_num : (1 : ℝ) < 2)
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hn' : 2 < (b - a) * 2 ^ n := by
    rw [div_lt_iff₀ hba] at hn
    linarith
  have hmle : a * 2 ^ n ≤ ((⌈a * 2 ^ n⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hmlt : ((⌈a * 2 ^ n⌉₊ : ℕ) : ℝ) < a * 2 ^ n + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hmn : ⌈a * 2 ^ n⌉₊ < 2 ^ n := by
    have h1 : ((⌈a * 2 ^ n⌉₊ : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast h1
  refine hu (pairing_dyadic n ⌈a * 2 ^ n⌉₊ hmn u₀ u₁ u₂ ?_)
  intro y hy1 hy2
  refine hcon y ⟨?_, ?_⟩
  · nlinarith
  · nlinarith

/-! ### The support -/

private theorem exists_ne_zero {p q : ℝ} (hpq : p < q) (hp : 0 ≤ p) (hq : q ≤ 3) :
    ∃ y ∈ Icc p q, scalingFun y ≠ 0 := by
  have hr0 : (0 : ℝ) ≤ (p + q) / 2 := by linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ⌊(p + q) / 2⌋₊ = k := ⟨_, rfl⟩
  have hjle : (k : ℝ) ≤ (p + q) / 2 := hk ▸ Nat.floor_le hr0
  have hjlt : (p + q) / 2 < (k : ℝ) + 1 := hk ▸ Nat.lt_floor_add_one _
  have hj3 : k < 3 := by
    by_contra hc
    push Not at hc
    have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hc
    linarith
  obtain ⟨a, b, hab, ha0, hb1, hpa, hbq⟩ :
      ∃ a b : ℝ, a < b ∧ 0 ≤ a ∧ b ≤ 1 ∧ p ≤ a + (k : ℝ) ∧ b + (k : ℝ) ≤ q := by
    refine ⟨max p (k : ℝ) - (k : ℝ), min q ((k : ℝ) + 1) - (k : ℝ), ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : max p (k : ℝ) ≤ (p + q) / 2 := max_le (by linarith) hjle
      have h2 : (p + q) / 2 < min q ((k : ℝ) + 1) := lt_min (by linarith) hjlt
      linarith
    · have := le_max_right p (k : ℝ); linarith
    · have := min_le_right q ((k : ℝ) + 1); linarith
    · have := le_max_left p (k : ℝ); linarith
    · have := min_le_left q ((k : ℝ) + 1); linarith
  interval_cases k
  · norm_num at hpa hbq
    obtain ⟨y, hy, hne⟩ := exists_pairing_ne_zero (u₀ := 1) (u₁ := 0) (u₂ := 0)
      (by simp) hab ha0 hb1
    have hp0 : pairing 1 0 0 y = scalingFun y := by rw [pairing_apply]; ring
    rw [hp0] at hne
    exact ⟨y, ⟨by linarith [hy.1], by linarith [hy.2]⟩, hne⟩
  · norm_num at hpa hbq
    obtain ⟨y, hy, hne⟩ := exists_pairing_ne_zero (u₀ := 0) (u₁ := 1) (u₂ := 0)
      (by simp) hab ha0 hb1
    have hp0 : pairing 0 1 0 y = scalingFun (y + 1) := by rw [pairing_apply]; ring
    rw [hp0] at hne
    exact ⟨y + 1, ⟨by linarith [hy.1], by linarith [hy.2]⟩, hne⟩
  · norm_num at hpa hbq
    obtain ⟨y, hy, hne⟩ := exists_pairing_ne_zero (u₀ := 0) (u₁ := 0) (u₂ := 1)
      (by simp) hab ha0 hb1
    have hp0 : pairing 0 0 1 y = scalingFun (y + 2) := by rw [pairing_apply]; ring
    rw [hp0] at hne
    exact ⟨y + 2, ⟨by linarith [hy.1], by linarith [hy.2]⟩, hne⟩

/-- **The support of the Daubechies D4 scaling function is exactly $[0, 3]$**: the closure of
$\{x : \varphi(x) \neq 0\}$ is $[0, 3]$.

The inclusion in $[0, 3]$ holds by construction. The reverse inclusion needs that $\varphi$
cannot vanish identically on a nondegenerate subinterval of $[0, 3]$. -/
theorem scalingFun_support : closure (Function.support scalingFun) = Icc 0 3 := by
  refine Subset.antisymm (closure_minimal (fun x hx => ?_) isClosed_Icc) ?_
  · by_contra hc
    simp only [mem_Icc, not_and_or, not_le] at hc
    refine hx (scalingFun_isApprox.eq_zero_of_lt_or_gt ?_)
    rcases hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr hc
  · rintro x ⟨hx0, hx3⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hd : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
    have hd2 : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
    have hd1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
    rcases lt_or_ge x 3 with hlt | hge
    · obtain ⟨y, hy, hne⟩ := exists_ne_zero (p := x) (q := min (x + min (ε / 2) 1) 3)
        (lt_min (by linarith) hlt) hx0 (min_le_right _ _)
      refine ⟨y, hne, ?_⟩
      have h1 := hy.1
      have h2 := hy.2.trans (min_le_left (x + min (ε / 2) 1) 3)
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    · have hx3' : x = 3 := le_antisymm hx3 hge
      subst hx3'
      obtain ⟨y, hy, hne⟩ := exists_ne_zero (p := 3 - min (ε / 2) 1) (q := 3)
        (by linarith) (by linarith) le_rfl
      refine ⟨y, hne, ?_⟩
      have h1 := hy.1
      have h2 := hy.2
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith

/-! ### The existence theorem -/

/-- **Existence of the Daubechies D4 scaling function.** There is a continuous function
$\varphi : \mathbb{R} \to \mathbb{R}$ such that $\varphi(x) = 0$ for $x < 0$ and for $x > 3$,
the closure of the support of $\varphi$ is exactly $[0, 3]$, $\varphi$ satisfies the four-term
scaling equation
$$\varphi(x) = \tfrac{1 + \sqrt{3}}{4} \varphi(2x) + \tfrac{3 + \sqrt{3}}{4} \varphi(2x - 1) +
  \tfrac{3 - \sqrt{3}}{4} \varphi(2x - 2) + \tfrac{1 - \sqrt{3}}{4} \varphi(2x - 3)$$
for all $x \in \mathbb{R}$, and $\varphi$ is normalized by $\varphi(1) = (1 + \sqrt{3})/2$ and
$\varphi(2) = (1 - \sqrt{3})/2$. -/
theorem exists_scalingFun :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ (∀ x : ℝ, x < 0 ∨ 3 < x → φ x = 0) ∧
      closure (Function.support φ) = Icc 0 3 ∧
      (∀ x : ℝ, φ x = (1 + √3) / 4 * φ (2 * x) + (3 + √3) / 4 * φ (2 * x - 1)
        + (3 - √3) / 4 * φ (2 * x - 2) + (1 - √3) / 4 * φ (2 * x - 3)) ∧
      φ 1 = (1 + √3) / 2 ∧ φ 2 = (1 - √3) / 2 :=
  ⟨scalingFun, scalingFun_continuous, fun _ hx => scalingFun_isApprox.eq_zero_of_lt_or_gt hx,
    scalingFun_support, scalingFun_refine, scalingFun_isApprox.val_one,
    scalingFun_isApprox.val_two⟩

end Daubechies
