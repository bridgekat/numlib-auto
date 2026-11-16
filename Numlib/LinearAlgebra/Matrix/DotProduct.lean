/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.DotProduct`, beside
`Matrix.conjTranspose_mul_self_eq_zero`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# A column with a vanishing Gram diagonal entry

Let $R$ be a star-ordered ring without zero divisors, and let $A$ be an $m \times n$ matrix over
$R$. The diagonal entry $(A^H A)_{jj} = \sum_k \overline{a_{kj}} a_{kj}$ of the Gram matrix is a sum
of nonnegative terms. So it vanishes only if column $j$ of $A$ is zero.

## Main results

* `Matrix.apply_eq_zero_of_conjTranspose_mul_self_apply_self_eq_zero`: if $(A^H A)_{jj} = 0$, then
  $a_{kj} = 0$ for every $k$.

## Implementation notes

* The result is the entrywise form of Mathlib's `Matrix.conjTranspose_mul_self_eq_zero`.
-/

namespace Matrix

variable {m n R : Type*} [Fintype m] [PartialOrder R] [NonUnitalRing R] [StarRing R]
  [StarOrderedRing R] [NoZeroDivisors R]

/-- Let $R$ be a star-ordered ring without zero divisors and let $A$ be an $m \times n$ matrix over
$R$. If the diagonal entry $(A^H A)_{jj}$ of the Gram matrix vanishes, then column $j$ of $A$ is
zero: $a_{kj} = 0$ for every row $k$. -/
theorem apply_eq_zero_of_conjTranspose_mul_self_apply_self_eq_zero {A : Matrix m n R} {j : n}
    (h : (Aᴴ * A) j j = 0) (k : m) : A k j = 0 := by
  have h0 : star (fun k => A k j) ⬝ᵥ (fun k => A k j) = 0 := by
    rw [← h, Matrix.mul_apply]
    rfl
  exact congrFun (dotProduct_star_self_eq_zero.1 h0) k

end Matrix
