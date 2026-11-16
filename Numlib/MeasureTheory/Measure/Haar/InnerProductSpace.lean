/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace`, beside
`LinearIsometryEquiv.measurePreserving`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Rigid motions preserve Lebesgue measure

Let $E$ and $F$ be finite-dimensional real inner product spaces with their Lebesgue measures. An
affine isometric equivalence $T \colon E \to F$ is a linear isometry followed by a translation, so
it preserves the Lebesgue measure. Hence it leaves integrals and integrals over sets unchanged.
Mathlib has the linear case, `LinearIsometryEquiv.measurePreserving`.

## Main results

* `AffineIsometryEquiv.measurePreserving`: $T$ maps the Lebesgue measure of $E$ to the Lebesgue
  measure of $F$.
* `AffineIsometryEquiv.integral_comp`: $\int_E f(Tx) \, dx = \int_F f(y) \, dy$.
* `AffineIsometryEquiv.setIntegral_comp`: $\int_{T^{-1}(s)} f(Tx) \, dx = \int_s f(y) \, dy$.

## Implementation notes

* The Lebesgue measure of a finite-dimensional real inner product space is `volume`, the Haar
  measure that gives measure $1$ to the parallelepiped of an orthonormal basis.
-/

open MeasureTheory

namespace AffineIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **A rigid motion preserves Lebesgue measure.** Let $E$ and $F$ be finite-dimensional real inner
product spaces with their Borel $\sigma$-algebras, and let $T \colon E \to F$ be an affine
isometric equivalence. Then $T$ is measure preserving from the Lebesgue measure of $E$ to the
Lebesgue measure of $F$.

The proof writes $Tx = Lx + T(0)$ with $L$ the linear part of $T$, a linear isometric
equivalence. -/
theorem measurePreserving (T : E ≃ᵃⁱ[ℝ] F) : MeasurePreserving T volume volume := by
  have h : (T : E → F) = fun x ↦ T.linearIsometryEquiv x + T 0 := by
    funext x
    have := T.map_vadd (0 : E) x
    rwa [vadd_eq_add, add_zero, vadd_eq_add] at this
  rw [h]
  exact (measurePreserving_add_right volume (T 0)).comp T.linearIsometryEquiv.measurePreserving

/-- Let $E$ and $F$ be finite-dimensional real inner product spaces, let $T \colon E \to F$ be an
affine isometric equivalence, and let $f \colon F \to G$ with $G$ a real normed space. Then
$$\int_E f(Tx) \, dx = \int_F f(y) \, dy.$$
-/
theorem integral_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E ≃ᵃⁱ[ℝ] F) (f : F → G) : ∫ x, f (T x) = ∫ y, f y :=
  T.measurePreserving.integral_comp T.toHomeomorph.measurableEmbedding f

/-- Let $E$ and $F$ be finite-dimensional real inner product spaces, let $T \colon E \to F$ be an
affine isometric equivalence, let $f \colon F \to G$ with $G$ a real normed space, and let
$s \subseteq F$. Then
$$\int_{T^{-1}(s)} f(Tx) \, dx = \int_s f(y) \, dy.$$
-/
theorem setIntegral_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E ≃ᵃⁱ[ℝ] F) (f : F → G) (s : Set F) :
    ∫ x in T ⁻¹' s, f (T x) = ∫ y in s, f y :=
  T.measurePreserving.setIntegral_preimage_emb T.toHomeomorph.measurableEmbedding f s

end AffineIsometryEquiv
