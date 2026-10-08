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

Mathlib's `Mathlib/Algebra/Polynomial/Roots.lean` bounds the number of roots of `X ^ n - C a`
(`Polynomial.card_nthRoots`) and says when `X ^ 2 - C a` has none
(`Polynomial.nthRoots_two_eq_zero_iff`); over `ℝ` the count is exact:

* `Polynomial.card_roots_X_sq_sub_C`: the real roots of `X ^ 2 - C c`, counted with multiplicity,
  are two (`±√c`, a double root `0` at `c = 0`) when `0 ≤ c`, and none when `c < 0`.

Counting real roots of a parametrized polynomial is the standard example of an ill-posed problem
([quarteroni2000numerical] Example 2.1), whose biquadratic factors into two such quadratics.
-/

open Polynomial

namespace Polynomial

/-- **The real roots of `X ^ 2 - C c`**, counted with multiplicity: two (`±√c`, a double root `0`
at `c = 0`) when `0 ≤ c`, none when `c < 0`. -/
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
