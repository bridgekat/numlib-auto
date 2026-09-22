/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.AddTorsor.AffineMap`, beside
`ContinuousAffineMap.contDiff`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# The derivative of a rigid motion

An affine isometry equivalence `T : E ≃ᵃⁱ[ℝ] F` of normed spaces — a rigid motion — is its
linear part followed by the translation by `T 0`
(`AffineIsometryEquiv.apply_eq_linearIsometryEquiv_add`), so it is differentiable with derivative
its linear part (`AffineIsometryEquiv.hasFDerivAt`), and the linear part of its inverse is the
inverse of its linear part (`AffineIsometryEquiv.linearIsometryEquiv_symm`).

Mathlib has `ContinuousAffineMap.contDiff` but no `hasFDerivAt` for an affine map; these three
facts are what the change of variables along a rigid motion of `ℝ^N` needs (the graph charts of
`Numlib/Analysis/Sobolev/Boundary/`).
-/

namespace AffineIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The linear part of the inverse of a rigid motion is the inverse of its linear part. -/
theorem linearIsometryEquiv_symm (T : E ≃ᵃⁱ[ℝ] F) :
    T.symm.linearIsometryEquiv = T.linearIsometryEquiv.symm := rfl

/-- A rigid motion is its linear part followed by a translation. -/
theorem apply_eq_linearIsometryEquiv_add (T : E ≃ᵃⁱ[ℝ] F) (x : E) :
    T x = T.linearIsometryEquiv x + T 0 := by
  have := T.map_vadd (0 : E) x
  rwa [vadd_eq_add, add_zero, vadd_eq_add] at this

/-- A rigid motion `T x = T.linear x + T 0` has derivative its linear part. -/
theorem hasFDerivAt (T : E ≃ᵃⁱ[ℝ] F) (z : E) :
    HasFDerivAt T (T.linearIsometryEquiv.toContinuousLinearEquiv : E →L[ℝ] F) z := by
  have h : (T : E → F) = fun z ↦ T.linearIsometryEquiv z + T 0 :=
    funext (apply_eq_linearIsometryEquiv_add T)
  rw [h]
  exact T.linearIsometryEquiv.toContinuousLinearEquiv.hasFDerivAt.add_const (T 0)

end AffineIsometryEquiv
