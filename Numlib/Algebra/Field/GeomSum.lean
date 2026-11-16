/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Field.GeomSum`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Field.GeomSum

/-!
# Geometric sums of roots of unity

Let $x$ be an element of a division ring with $x^n = 1$. This module shows that the geometric sum
$\sum_{i < n} x^i$ equals $n$ if $x = 1$ and $0$ otherwise. This is the orthogonality relation of
the characters of a finite cyclic group.

## Main results

* `geom_sum_eq_ite_of_pow_eq_one`: if $x^n = 1$, then $\sum_{i < n} x^i$ is $n$ for $x = 1$ and $0$
  for $x \neq 1$.

## Implementation notes

* Mathlib's `IsPrimitiveRoot.geom_sum_eq_zero` sums the powers of a primitive root of unity. The
  result here needs only $x^n = 1$.
-/

/-- The **geometric sum of an $n$-th root of unity**. Let $\alpha$ be a division ring, let
$x \in \alpha$ and $n \in \mathbb{N}$, and suppose that $x^n = 1$. Then
$$\sum_{i=0}^{n-1} x^i = \begin{cases} n & \text{if } x = 1, \\ 0 & \text{if } x \neq 1.
  \end{cases}$$
-/
theorem geom_sum_eq_ite_of_pow_eq_one {α : Type*} [DivisionRing α] [DecidableEq α] {x : α}
    {n : ℕ} (h : x ^ n = 1) :
    ∑ i ∈ Finset.range n, x ^ i = if x = 1 then (n : α) else 0 := by
  rcases eq_or_ne x 1 with rfl | hx
  · simp
  · rw [ite_eq_right hx, geom_sum_eq hx, h, sub_self, zero_div]
