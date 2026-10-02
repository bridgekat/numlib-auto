/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Projection onto the span of some vectors of an orthonormal basis

In the coordinates of an orthonormal basis `b`, the orthogonal projection `P` onto
`span (b '' s)` keeps the coordinates indexed by `s` and sets the others to `0`
(`OrthonormalBasis.repr_starProjection_span_image`). Hence `‖P x‖²` and `‖x − P x‖²` are the sums
of the squared coordinates in and outside `s` (`OrthonormalBasis.norm_sq_starProjection_span_image`,
`OrthonormalBasis.norm_sq_sub_starProjection_span_image`), which is how the angle between a vector
and an invariant subspace spanned by eigenvectors is read off the eigenvector coordinates.
-/

namespace OrthonormalBasis

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type*}
  [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)

/-- Parseval's identity in the coordinates of an orthonormal basis:
`∑ i, ‖b.repr x i‖² = ‖x‖²`. -/
@[deprecated "use `OrthonormalBasis.sum_sq_norm_inner_right` and `repr_apply_apply`"
  (since := "2026-09-30")]
theorem sum_sq_norm_repr (x : E) : ∑ i, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simpa only [b.repr_apply_apply] using b.sum_sq_norm_inner_right x

variable [FiniteDimensional 𝕜 E] (s : Set ι) [DecidablePred (· ∈ s)]

/-- The coordinates of the orthogonal projection onto the span of some vectors of an orthonormal
basis: those coordinates are kept, the others are set to `0`. -/
theorem repr_starProjection_span_image (x : E) (j : ι) :
    b.repr ((Submodule.span 𝕜 (b '' s)).starProjection x) j = if j ∈ s then b.repr x j else 0 := by
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  split_ifs with hj
  · rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (Submodule.subset_span (Set.mem_image_of_mem b hj))]
  · have key : ∀ z ∈ Submodule.span 𝕜 (b '' s), inner 𝕜 (b j) z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨l, hl, rfl⟩ := hz
        exact b.orthonormal.2 fun h => hj (by subst h; exact hl)
      | zero => exact inner_zero_right _
      | add z w _ _ hz hw => rw [inner_add_right, hz, hw, add_zero]
      | smul c z _ hz => rw [inner_smul_right, hz, mul_zero]
    exact key _ (Submodule.starProjection_apply_mem _ x)

/-- `‖P x‖² = ∑_{j ∈ s} |x_j|²` for the orthogonal projection `P` onto `span (b '' s)`. -/
theorem norm_sq_starProjection_span_image (x : E) :
    ‖(Submodule.span 𝕜 (b '' s)).starProjection x‖ ^ 2 =
      ∑ j, if j ∈ s then ‖b.repr x j‖ ^ 2 else 0 := by
  rw [← b.sum_sq_norm_inner_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← b.repr_apply_apply, repr_starProjection_span_image b s]
  split_ifs <;> simp

/-- `‖x - P x‖² = ∑_{j ∉ s} |x_j|²` for the orthogonal projection `P` onto `span (b '' s)`. -/
theorem norm_sq_sub_starProjection_span_image (x : E) :
    ‖x - (Submodule.span 𝕜 (b '' s)).starProjection x‖ ^ 2 =
      ∑ j, if j ∈ s then 0 else ‖b.repr x j‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← b.repr_apply_apply, map_sub, PiLp.sub_apply, repr_starProjection_span_image b s]
  split_ifs <;> simp

end OrthonormalBasis
