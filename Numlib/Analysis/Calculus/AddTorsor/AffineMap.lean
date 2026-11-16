/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

A rigid motion here is an affine isometry equivalence $T : E \to F$ between real normed spaces.
Write $\vec T$ for its linear part, a linear isometry equivalence. Then $T$ is $\vec T$ followed by
the translation by $T(0)$, that is $T(x) = \vec T x + T(0)$. Hence $T$ is differentiable at every
point with derivative $\vec T$. Moreover, the linear part of $T^{-1}$ is $\vec T^{-1}$.

Mathlib has `ContinuousAffineMap.contDiff`, but no statement of the derivative of an affine map.
These three facts are what a change of variables along a rigid motion of $\mathbb{R}^N$ needs, as in
the boundary charts of `Numlib.Analysis.Sobolev.Boundary.GraphMeasure`.

## Main results

* `AffineIsometryEquiv.linearIsometryEquiv_symm`: the linear part of $T^{-1}$ is $\vec T^{-1}$.
* `AffineIsometryEquiv.apply_eq_linearIsometryEquiv_add`: $T(x) = \vec T x + T(0)$.
* `AffineIsometryEquiv.hasFDerivAt`: $T$ has the derivative $\vec T$ at every point.

## Implementation notes

* A rigid motion is a term `T` of type `E ≃ᵃⁱ[ℝ] F`. Its linear part $\vec T$ is
  `T.linearIsometryEquiv`.
-/

namespace AffineIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Let $T : E \to F$ be an affine isometry equivalence of real normed spaces. The linear part of
the inverse $T^{-1}$ is the inverse $\vec T^{-1}$ of the linear part of $T$. -/
theorem linearIsometryEquiv_symm (T : E ≃ᵃⁱ[ℝ] F) :
    T.symm.linearIsometryEquiv = T.linearIsometryEquiv.symm := rfl

/-- Let $T : E \to F$ be an affine isometry equivalence of real normed spaces, with linear part
$\vec T$. Then for every $x \in E$,
$$T(x) = \vec T x + T(0).$$

The linear part $\vec T$ is `T.linearIsometryEquiv`. -/
theorem apply_eq_linearIsometryEquiv_add (T : E ≃ᵃⁱ[ℝ] F) (x : E) :
    T x = T.linearIsometryEquiv x + T 0 := by
  have := T.map_vadd (0 : E) x
  rwa [vadd_eq_add, add_zero, vadd_eq_add] at this

/-- Let $T : E \to F$ be an affine isometry equivalence of real normed spaces, with linear part
$\vec T$. Then at every point $z \in E$, $T$ is Fréchet differentiable with derivative $\vec T$.

The derivative is `T.linearIsometryEquiv` as a continuous linear map `E →L[ℝ] F`. The proof uses
`AffineIsometryEquiv.apply_eq_linearIsometryEquiv_add`. -/
theorem hasFDerivAt (T : E ≃ᵃⁱ[ℝ] F) (z : E) :
    HasFDerivAt T (T.linearIsometryEquiv.toContinuousLinearEquiv : E →L[ℝ] F) z := by
  have h : (T : E → F) = fun z ↦ T.linearIsometryEquiv z + T 0 :=
    funext (apply_eq_linearIsometryEquiv_add T)
  rw [h]
  exact T.linearIsometryEquiv.toContinuousLinearEquiv.hasFDerivAt.add_const (T 0)

end AffineIsometryEquiv
