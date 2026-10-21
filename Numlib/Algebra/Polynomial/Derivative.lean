/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Polynomial.Derivative`, beside `Polynomial.coeff_iterate_derivative`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Iterated derivatives of polynomials

The `k`-th derivative of a polynomial of degree at most `k` is the constant `k! · p_k`
(`Polynomial.iterate_derivative_eq_C_of_natDegree_le`); at `k = natDegree p` it is
`k! · leadingCoeff p` (`Polynomial.iterate_derivative_eq_C_of_natDegree_eq`), which is `k!` for a
monic polynomial. These are the constants of every interpolation error formula and of the
Rodrigues formulas for the classical orthogonal polynomials. Evaluation of the iterated
derivatives of an affine polynomial is given by `Polynomial.eval_iterate_derivative_affine`.
-/

open Nat

namespace Polynomial

variable {R : Type*} [CommSemiring R] {p : R[X]} {k : ℕ}

/-- The top iterated derivative of a polynomial of degree at most `k` is the constant
`k! · (coefficient of X^k)`. -/
theorem iterate_derivative_eq_C_of_natDegree_le (hp : p.natDegree ≤ k) :
    derivative^[k] p = C ((k.factorial : R) * p.coeff k) := by
  have h0 : (derivative^[k] p).natDegree = 0 :=
    Nat.le_zero.mp ((natDegree_iterate_derivative p k).trans (by omega))
  rw [eq_C_of_natDegree_eq_zero h0, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul]

/-- The `natDegree`-th derivative of a polynomial is the constant `k! · leadingCoeff p`. -/
theorem iterate_derivative_eq_C_of_natDegree_eq (hp : p.natDegree = k) :
    derivative^[k] p = C ((k ! : R) * p.leadingCoeff) := by
  rw [iterate_derivative_eq_C_of_natDegree_le hp.le, leadingCoeff, hp]

/-- The iterated derivatives of an affine polynomial have the expected three branches. -/
theorem eval_iterate_derivative_affine (a b t : R) (j : ℕ) :
    (derivative^[j] (C a + C b * X)).eval t =
      if j = 0 then a + b * t else if j = 1 then b else 0 := by
  cases j with
  | zero => simp
  | succ j =>
    rw [Function.iterate_succ_apply]
    simp only [derivative_add, derivative_C, derivative_mul, derivative_X, zero_mul,
      zero_add, mul_one]
    cases j with
    | zero => simp
    | succ j =>
      rw [Function.iterate_succ_apply]
      simp

end Polynomial
