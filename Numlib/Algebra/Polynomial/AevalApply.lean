/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $T$ be an endomorphism of a module $M$ over a commutative ring $R$. For a polynomial
$p \in R[X]$ and a vector $v \in M$, the vector $p(T) v$ distributes over the ring operations on
$p$, and $p(T)$ commutes with $T$. These identities are the rewriting steps of every polynomial
recurrence of a Krylov method, such as $\varphi_{j+1} = \varphi_j - \alpha_j X \pi_j$.

## Main results

* `Module.End.aeval_mul_apply`: $(pq)(T) v = p(T)(q(T) v)$.
* `Module.End.aeval_apply_apply`: $p(T)(Tv) = T(p(T) v)$.
* `Module.End.aeval_sub_C_mul_X_mul`: $(p - cXq)(T) v = p(T) v - c \, T(q(T) v)$.
-/

open Polynomial

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (T : Module.End R M)

/-- Let $T$ be an endomorphism of an $R$-module $M$, let $p, q \in R[X]$ and $v \in M$. Then
$(pq)(T) v = p(T)(q(T) v)$. -/
theorem aeval_mul_apply (p q : R[X]) (v : M) : aeval T (p * q) v = aeval T p (aeval T q v) := by
  rw [map_mul]; rfl

/-- Let $T$ be an endomorphism of an $R$-module $M$, let $p \in R[X]$ and $v \in M$. Then $p(T)$
commutes with $T$: $p(T)(Tv) = T(p(T) v)$. -/
theorem aeval_apply_apply (p : R[X]) (v : M) : aeval T p (T v) = T (aeval T p v) := by
  have hmul : aeval T (p * X) = aeval T (X * p) := by rw [mul_comm]
  have := congrArg (fun f : Module.End R M => f v) hmul
  simpa only [map_mul, aeval_X, Module.End.mul_apply] using this

/-- Evaluation is additive in the polynomial: $(p + q)(T) v = p(T) v + q(T) v$. -/
theorem aeval_apply_add (p q : R[X]) (v : M) :
    aeval T (p + q) v = aeval T p v + aeval T q v := by
  rw [map_add]; rfl

/-- Evaluation is subtractive in the polynomial: $(p - q)(T) v = p(T) v - q(T) v$. -/
theorem aeval_apply_sub (p q : R[X]) (v : M) :
    aeval T (p - q) v = aeval T p v - aeval T q v := by
  rw [map_sub]; rfl

/-- A constant factor becomes a scalar: for $c \in R$, $(cp)(T) v = c \, p(T) v$. -/
theorem aeval_apply_C_mul (c : R) (p : R[X]) (v : M) :
    aeval T (C c * p) v = c • aeval T p v := by
  rw [map_mul, aeval_C]
  simp [Module.End.mul_apply, Module.algebraMap_end_apply]

/-- A factor $X$ becomes an application of $T$: $(Xp)(T) v = T(p(T) v)$. -/
theorem aeval_apply_X_mul (p : R[X]) (v : M) : aeval T (X * p) v = T (aeval T p v) := by
  rw [aeval_mul_apply, aeval_X]

/-- For $c \in R$ and $p, q \in R[X]$, $(p - cXq)(T) v = p(T) v - c \, T(q(T) v)$. -/
theorem aeval_sub_C_mul_X_mul (c : R) (p q : R[X]) (v : M) :
    aeval T (p - C c * (X * q)) v = aeval T p v - c • T (aeval T q v) := by
  rw [aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]

/-- For $c \in R$ and $p, q \in R[X]$, $(p + cq)(T) v = p(T) v + c \, q(T) v$. -/
theorem aeval_add_C_mul (c : R) (p q : R[X]) (v : M) :
    aeval T (p + C c * q) v = aeval T p v + c • aeval T q v := by
  rw [aeval_apply_add, aeval_apply_C_mul]

end Module.End
