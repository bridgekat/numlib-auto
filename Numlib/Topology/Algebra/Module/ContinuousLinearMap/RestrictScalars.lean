/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Restriction of scalars commutes with powers

`ContinuousLinearMap.restrictScalars_pow`: restricting the scalars of a continuous endomorphism
commutes with taking powers, so a bound on the powers of a complex operator is one on the powers
of the underlying real operator.
-/

namespace ContinuousLinearMap

variable {A M R : Type*} [Semiring A] [Semiring R] [AddCommMonoid M] [Module A M] [Module R M]
  [TopologicalSpace M] [LinearMap.CompatibleSMul M M R A]

/-- **Restricting scalars commutes with powers** of a continuous endomorphism. -/
theorem restrictScalars_pow (f : M →L[A] M) (n : ℕ) :
    (f ^ n).restrictScalars R = f.restrictScalars R ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl

end ContinuousLinearMap
