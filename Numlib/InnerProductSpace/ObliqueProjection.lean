/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Projection`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Oblique projectors

Projectors `P` (`P ∘ P = P`) onto `K` and orthogonal to `L` (`ker P = Lᗮ`): uniqueness from
range and kernel, existence iff `K ⊓ Lᗮ = ⊥` (Saad §1.12, (1.39)–(1.41)), the matrix form
`P = V (Wᴴ V)⁻¹ Wᴴ` from bases `V` of `K` and `W` of `L` (Saad (1.44)), the norm characterization
of orthogonal projectors (Saad Thm 1.36), and Kato's lemma `‖P‖ = ‖1 - P‖` (Szyld 2006;
Atkinson–Han Rem 9.2.2, Xu–Zikatanov).
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap

/-- A projector is determined by its range and its kernel. -/
theorem IsIdempotentElem.ext_of_range_eq_of_ker_eq {P Q : E →ₗ[𝕜] E} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) (hr : LinearMap.range P = LinearMap.range Q)
    (hk : LinearMap.ker P = LinearMap.ker Q) : P = Q := by
  sorry

/-- Saad (1.41): `P x` is the unique element of `K` with `x - P x ⟂ L`, for a projector `P` with
range `K` and kernel `Lᗮ`. -/
theorem IsIdempotentElem.apply_eq_iff {P : E →ₗ[𝕜] E} (hP : IsIdempotentElem P)
    {K L : Submodule 𝕜 E} (hr : LinearMap.range P = K) (hk : LinearMap.ker P = Lᗮ) (x y : E) :
    P x = y ↔ y ∈ K ∧ x - y ∈ Lᗮ := by
  sorry

/-- Saad §1.12.1: a projector onto `K` orthogonal to `L` exists (uniquely) iff `K ⊓ Lᗮ = ⊥`,
for finite-dimensional `K`, `L` of equal dimension. -/
theorem existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot {K L : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) (hKL : K ⊓ Lᗮ = ⊥) :
    ∃! P : E →ₗ[𝕜] E, IsIdempotentElem P ∧ LinearMap.range P = K ∧ LinearMap.ker P = Lᗮ := by
  sorry

section Bases

instance finiteDimensional_span_range {ι : Type*} [Finite ι] (V : ι → E) :
    FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range V)) :=
  Module.Finite.span_of_finite 𝕜 (Set.finite_range V)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (𝕜)

/-- The Gram-type matrix `Wᴴ V = (⟪W i, V j⟫)` of two families. -/
noncomputable def crossGram (V W : ι → E) : Matrix ι ι 𝕜 :=
  Matrix.of fun i j => inner 𝕜 (W i) (V j)

/-- Saad (1.44): the projector `V (Wᴴ V)⁻¹ Wᴴ` onto `span V` orthogonally to `span W`
(as a linear map; junk when `Wᴴ V` is singular). -/
noncomputable def obliqueProjectionOfBases (V W : ι → E) : E →ₗ[𝕜] E where
  toFun x := ∑ j, (crossGram 𝕜 V W)⁻¹.mulVec (fun i => inner 𝕜 (W i) x) j • V j
  map_add' := by sorry
  map_smul' := by sorry

variable {𝕜}

variable (V W : ι → E) (hVW : IsUnit (crossGram 𝕜 V W))
include hVW

theorem obliqueProjectionOfBases_isIdempotentElem :
    IsIdempotentElem (obliqueProjectionOfBases 𝕜 V W) := by
  sorry

theorem range_obliqueProjectionOfBases :
    LinearMap.range (obliqueProjectionOfBases 𝕜 V W) = Submodule.span 𝕜 (Set.range V) := by
  sorry

theorem ker_obliqueProjectionOfBases :
    LinearMap.ker (obliqueProjectionOfBases 𝕜 V W) = (Submodule.span 𝕜 (Set.range W))ᗮ := by
  sorry

theorem sub_obliqueProjectionOfBases_apply_mem_orthogonal (x : E) :
    x - obliqueProjectionOfBases 𝕜 V W x ∈ (Submodule.span 𝕜 (Set.range W))ᗮ := by
  sorry

omit hVW in
/-- With `W = V` orthonormal, `V (Vᴴ V)⁻¹ Vᴴ = V Vᴴ` is the orthogonal projection. -/
theorem obliqueProjectionOfBases_self_eq_starProjection (hV : Orthonormal 𝕜 V) :
    obliqueProjectionOfBases 𝕜 V V =
      ((Submodule.span 𝕜 (Set.range V)).starProjection : E →ₗ[𝕜] E) := by
  sorry

end Bases

end LinearMap

namespace ContinuousLinearMap

variable [CompleteSpace E]

/-- Saad Thm 1.36 / Atkinson–Han Ex 3.6.7: a nonzero projector has norm `≥ 1`, with equality iff
it is orthogonal (self-adjoint). -/
theorem IsIdempotentElem.norm_eq_one_iff_isSymmetric {P : E →L[𝕜] E} (hP : IsIdempotentElem P)
    (h0 : P ≠ 0) : ‖P‖ = 1 ↔ (P : E →ₗ[𝕜] E).IsSymmetric := by
  sorry

/-- Kato's lemma: for a bounded projector `P ≠ 0, 1` on a Hilbert space, `‖P‖ = ‖1 - P‖`
(Szyld, *The many proofs of an identity on the norm of oblique projections*, 2006). -/
theorem IsIdempotentElem.norm_one_sub_eq {P : E →L[𝕜] E} (hP : IsIdempotentElem P) (h0 : P ≠ 0)
    (h1 : P ≠ 1) : ‖1 - P‖ = ‖P‖ := by
  sorry

end ContinuousLinearMap
