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

An affine isometry equivalence `T : E ≃ᵃⁱ[ℝ] F` of finite-dimensional real inner product spaces
preserves the volume (`AffineIsometryEquiv.measurePreserving`), being a linear isometry followed
by a translation, and therefore leaves integrals and set integrals invariant
(`AffineIsometryEquiv.integral_comp`, `AffineIsometryEquiv.setIntegral_comp`). Mathlib has the
linear statement `LinearIsometryEquiv.measurePreserving`.
-/

open MeasureTheory

namespace AffineIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **A rigid motion preserves Lebesgue measure**: `T x = T.linear x + T 0` is a linear isometry
followed by a translation. -/
theorem measurePreserving (T : E ≃ᵃⁱ[ℝ] F) : MeasurePreserving T volume volume := by
  have h : (T : E → F) = fun x ↦ T.linearIsometryEquiv x + T 0 := by
    funext x
    have := T.map_vadd (0 : E) x
    rwa [vadd_eq_add, add_zero, vadd_eq_add] at this
  rw [h]
  exact (measurePreserving_add_right volume (T 0)).comp T.linearIsometryEquiv.measurePreserving

/-- Integrals are invariant under a rigid motion: `∫ f (T x) = ∫ f`. -/
theorem integral_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E ≃ᵃⁱ[ℝ] F) (f : F → G) : ∫ x, f (T x) = ∫ y, f y :=
  T.measurePreserving.integral_comp T.toHomeomorph.measurableEmbedding f

/-- Set integrals are invariant under a rigid motion: `∫_{T ⁻¹' s} f (T x) = ∫_s f`. -/
theorem setIntegral_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E ≃ᵃⁱ[ℝ] F) (f : F → G) (s : Set F) :
    ∫ x in T ⁻¹' s, f (T x) = ∫ y in s, f y :=
  T.measurePreserving.setIntegral_preimage_emb T.toHomeomorph.measurableEmbedding f s

end AffineIsometryEquiv
