/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Polynomial.Roots`, beside `Polynomial.nthRoots`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Sqrt

/-!
# Counting the real roots of explicit polynomials

For a real number $c$, the polynomial $X^2 - c$ has two real roots, counted with multiplicity, when
$c \ge 0$, and none when $c < 0$. Mathlib's `Mathlib.Algebra.Polynomial.Roots` bounds the number of
roots of $X^n - a$ (`Polynomial.card_nthRoots`) and says when $X^2 - a$ has no roots
(`Polynomial.nthRoots_two_eq_zero_iff`). Over $\mathbb{R}$ this module gives the exact count.
Counting the real roots of a polynomial with a parameter is the standard example of an ill-posed
problem ([quarteroni2000numerical], Example 2.1), whose biquadratic polynomial factors into two such
quadratics.

## Main results

* `Polynomial.card_roots_X_sq_sub_C`: the number of real roots of $X^2 - c$, counted with
  multiplicity, is $2$ if $c \ge 0$ and $0$ if $c < 0$.
-/

open Polynomial

namespace Polynomial

/-- The **real roots of $X^2 - c$**. Let $c \in \mathbb{R}$. The number of real roots of $X^2 - c$,
counted with multiplicity, is
$$\begin{cases} 2 & \text{if } c \ge 0, \\ 0 & \text{if } c < 0. \end{cases}$$

For $c > 0$ the roots are $\pm\sqrt{c}$, and for $c = 0$ the root $0$ is double. -/
theorem card_roots_X_sq_sub_C (c : ℝ) :
    Multiset.card (X ^ 2 - C c : ℝ[X]).roots = if 0 ≤ c then 2 else 0 := by
  split_ifs with hc
  · have h : (X ^ 2 - C c : ℝ[X]) = (X - C √c) * (X - C (-√c)) := by
      conv_lhs => rw [← Real.sq_sqrt hc, C_pow]
      rw [C_neg]; ring
    rw [h, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
      roots_X_sub_C]
    simp
  · rw [Multiset.card_eq_zero]
    refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    rw [mem_roots (X_pow_sub_C_ne_zero two_pos c), IsRoot.def] at hx
    simp at hx
    nlinarith [sq_nonneg x]

end Polynomial
