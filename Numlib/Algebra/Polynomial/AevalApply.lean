/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Polynomial.AlgebraMap`, beside `Polynomial.aeval_algHom_apply`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomials in an endomorphism, applied to a vector

The evaluation `p(T) v` of a polynomial in an endomorphism `T` of a module distributes over the ring
operations on `p` (`Module.End.aeval_mul_apply`, `Module.End.aeval_apply_add`, …) and commutes with
`T` (`Module.End.aeval_apply_apply`); these are the rewriting steps of every polynomial recurrence
of a Krylov method (`φ_{j+1} = φ_j − α_j X π_j`, …).
-/

open Polynomial

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (T : Module.End R M)

/-- `(p q)(T) v = p(T) (q(T) v)`. -/
theorem aeval_mul_apply (p q : R[X]) (v : M) : aeval T (p * q) v = aeval T p (aeval T q v) := by
  rw [map_mul]; rfl

/-- `p(T)` commutes with `T`: `p(T) (T v) = T (p(T) v)`. -/
theorem aeval_apply_apply (p : R[X]) (v : M) : aeval T p (T v) = T (aeval T p v) := by
  have hmul : aeval T (p * X) = aeval T (X * p) := by rw [mul_comm]
  have := congrArg (fun f : Module.End R M => f v) hmul
  simpa only [map_mul, aeval_X, Module.End.mul_apply] using this

/-- Evaluation is additive in the polynomial: `(p + q)(T) v = p(T) v + q(T) v`. -/
theorem aeval_apply_add (p q : R[X]) (v : M) :
    aeval T (p + q) v = aeval T p v + aeval T q v := by
  rw [map_add]; rfl

/-- Evaluation is subtractive in the polynomial: `(p - q)(T) v = p(T) v - q(T) v`. -/
theorem aeval_apply_sub (p q : R[X]) (v : M) :
    aeval T (p - q) v = aeval T p v - aeval T q v := by
  rw [map_sub]; rfl

/-- A constant factor becomes a scalar: `(c p)(T) v = c • p(T) v`. -/
theorem aeval_apply_C_mul (c : R) (p : R[X]) (v : M) :
    aeval T (C c * p) v = c • aeval T p v := by
  rw [map_mul, aeval_C]
  simp [Module.End.mul_apply, Module.algebraMap_end_apply]

/-- A factor of `X` becomes an application of `T`: `(X p)(T) v = T (p(T) v)`. -/
theorem aeval_apply_X_mul (p : R[X]) (v : M) : aeval T (X * p) v = T (aeval T p v) := by
  rw [aeval_mul_apply, aeval_X]

/-- The evaluation of `p - c X q`: `p(T) v - c • T (q(T) v)`. -/
theorem aeval_sub_C_mul_X_mul (c : R) (p q : R[X]) (v : M) :
    aeval T (p - C c * (X * q)) v = aeval T p v - c • T (aeval T q v) := by
  rw [aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]

/-- The evaluation of `p + c q`: `p(T) v + c • q(T) v`. -/
theorem aeval_add_C_mul (c : R) (p q : R[X]) (v : M) :
    aeval T (p + C c * q) v = aeval T p v + c • aeval T q v := by
  rw [aeval_apply_add, aeval_apply_C_mul]

end Module.End
