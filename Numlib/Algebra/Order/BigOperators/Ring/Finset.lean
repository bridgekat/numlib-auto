/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Order.BigOperators.Ring.Finset`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The Weierstrass product inequality

Let $b_i$, $i \in s$, be finitely many elements of $[0, 1]$ in an ordered commutative ring. The
Weierstrass product inequality $1 - \sum_i b_i \le \prod_i (1 - b_i)$ bounds a product of factors
$1 - b_i$ from below. It keeps the product away from $0$ while $\sum_i b_i$ is small.

## Main results

* `Finset.one_sub_sum_le_prod_one_sub`: if $0 \le b_i \le 1$ for all $i \in s$, then $1 - \sum_{i
  \in s} b_i \le \prod_{i \in s} (1 - b_i)$.
-/

namespace Finset

/-- The **Weierstrass product inequality**. Let $R$ be a strictly ordered commutative ring with a
linear order, let $s$ be a finite subset of an index type $\iota$, and let
$b \colon \iota \to R$ satisfy $0 \le b_i \le 1$ for all $i \in s$. Then
$$1 - \sum_{i \in s} b_i \le \prod_{i \in s} (1 - b_i).$$
-/
theorem one_sub_sum_le_prod_one_sub {ι R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (s : Finset ι) (b : ι → R) (hb0 : ∀ i ∈ s, 0 ≤ b i)
    (hb1 : ∀ i ∈ s, b i ≤ 1) : 1 - ∑ i ∈ s, b i ≤ ∏ i ∈ s, (1 - b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have ih' := ih (fun i hi => hb0 i (mem_insert_of_mem hi))
      (fun i hi => hb1 i (mem_insert_of_mem hi))
    have hS : 0 ≤ ∑ i ∈ s, b i := sum_nonneg fun i hi => hb0 i (mem_insert_of_mem hi)
    have h0 := hb0 a (mem_insert_self a s)
    have h1 := hb1 a (mem_insert_self a s)
    nlinarith [ih', h0, h1]

end Finset
