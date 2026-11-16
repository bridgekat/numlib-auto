/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Restriction of scalars commutes with powers

Let $M$ be an additive commutative monoid with a topology, and a module over two semirings $A$ and
$R$, with compatible scalar actions. A continuous $A$-linear endomorphism $f$ of $M$ is also a
continuous $R$-linear endomorphism, its restriction of scalars. This file proves that restriction of
scalars commutes with taking powers. Hence a bound on the powers of a complex operator is a bound on
the powers of the underlying real operator.

## Main results

* `ContinuousLinearMap.restrictScalars_pow`: the restriction of scalars of $f^n$ is the $n$-th power
  of the restriction of scalars of $f$.
-/

namespace ContinuousLinearMap

variable {A M R : Type*} [Semiring A] [Semiring R] [AddCommMonoid M] [Module A M] [Module R M]
  [TopologicalSpace M] [LinearMap.CompatibleSMul M M R A]

/-- **Restriction of scalars commutes with powers.** Let $M$ be a module over the semirings $A$ and
$R$ with a topology, such that $A$-linear maps $M \to M$ are $R$-linear. For a continuous
$A$-linear map $f : M \to M$ and $n \in \mathbb{N}$, the restriction of scalars of $f^n$ to $R$
is the $n$-th power of the restriction of scalars of $f$ to $R$.

The compatibility of the two actions is the hypothesis `LinearMap.CompatibleSMul M M R A`. No
continuity of addition or of scalar multiplication on $M$ is assumed. -/
theorem restrictScalars_pow (f : M →L[A] M) (n : ℕ) :
    (f ^ n).restrictScalars R = f.restrictScalars R ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl

end ContinuousLinearMap
