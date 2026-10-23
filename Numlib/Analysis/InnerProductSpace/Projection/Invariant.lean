import Numlib.Analysis.InnerProductSpace.Projection.Compression

/-!
# Projection of symmetric operators onto invariant subspaces

The genuine orthogonal projection intertwines a symmetric operator and its
compression whenever the subspace is invariant.
-/

namespace compression
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
/-- A symmetric operator commutes with projection onto an invariant compression space. -/
theorem apply_orthogonalProjectionOnto (A : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (hK : ∀ v ∈ K, A v ∈ K) (x : E) :
    compression A K (K.orthogonalProjectionOnto x) = K.orthogonalProjectionOnto (A x) := by
  apply ext_inner_right 𝕜
  intro z
  rw [compression.inner_apply]
  change inner 𝕜 (A (K.starProjection x)) (z : E) =
    inner 𝕜 (K.starProjection (A x)) (z : E)
  rw [hA]
  have hp : inner 𝕜 (K.starProjection x) (A (z : E)) = inner 𝕜 x (A (z : E)) := by
    have hh := K.starProjection_inner_eq_zero x (A (z : E)) (hK z z.property)
    rw [inner_sub_left, sub_eq_zero] at hh
    exact hh.symm
  rw [hp, ← hA]
  have hh := K.starProjection_inner_eq_zero (A x) (z : E) z.property
  rw [inner_sub_left, sub_eq_zero] at hh
  exact hh
end compression
