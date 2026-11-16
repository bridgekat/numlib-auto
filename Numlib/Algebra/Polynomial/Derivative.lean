/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Polynomial.Derivative`, beside `Polynomial.coeff_iterate_derivative`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Derivative

/-!
# The top iterated derivative of a polynomial

Let $p = \sum_i p_i X^i$ be a polynomial over a commutative semiring. If $\deg p \le k$, then the
$k$-th derivative of $p$ is the constant $k! \, p_k$. For $k = \deg p$ this constant is $k!$ times
the leading coefficient of $p$, and so it is $k!$ for a monic polynomial. These constants appear in
every interpolation error formula and in the Rodrigues formulas for the classical orthogonal
polynomials.

## Main results

* `Polynomial.iterate_derivative_eq_C_of_natDegree_le`: if $\deg p \le k$, then
  $p^{(k)} = k! \, p_k$.
* `Polynomial.iterate_derivative_eq_C_of_natDegree_eq`: if $\deg p = k$, then $p^{(k)}$ is $k!$
  times the leading coefficient of $p$.
-/

open Nat

namespace Polynomial

variable {R : Type*} [CommSemiring R] {p : R[X]} {k : ℕ}

/-- Let $R$ be a commutative semiring and let $p = \sum_i p_i X^i \in R[X]$ have degree at most $k$.
Then the $k$-th derivative of $p$ is the constant polynomial
$$p^{(k)} = k! \, p_k.$$

The degree is `Polynomial.natDegree`, so the zero polynomial has degree $0$. -/
theorem iterate_derivative_eq_C_of_natDegree_le (hp : p.natDegree ≤ k) :
    derivative^[k] p = C ((k.factorial : R) * p.coeff k) := by
  have h0 : (derivative^[k] p).natDegree = 0 :=
    Nat.le_zero.mp ((natDegree_iterate_derivative p k).trans (by omega))
  rw [eq_C_of_natDegree_eq_zero h0, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul]

/-- Let $R$ be a commutative semiring and let $p \in R[X]$ have degree $k$. Then the $k$-th
derivative of $p$ is the constant polynomial
$$p^{(k)} = k! \, \operatorname{lc}(p),$$
where $\operatorname{lc}(p)$ is the leading coefficient of $p$.

The degree is `Polynomial.natDegree`, so the zero polynomial has degree $0$. -/
theorem iterate_derivative_eq_C_of_natDegree_eq (hp : p.natDegree = k) :
    derivative^[k] p = C ((k ! : R) * p.leadingCoeff) := by
  rw [iterate_derivative_eq_C_of_natDegree_le hp.le, leadingCoeff, hp]

end Polynomial
