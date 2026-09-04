/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Uniqueness of orthonormal bases of a flag

An orthonormal family `u` with `span {u_0, …, u_j} = span {f_0, …, f_j}` for every `j` agrees with
the Gram–Schmidt orthonormalization of `f` up to unimodular scalars, and equals it under the
sign normalization `re ⟪u_j, f_j⟫ > 0`. This is the "same method, different implementation"
principle behind classical/modified Gram–Schmidt Arnoldi, Householder Arnoldi (up to signs),
and the Lanczos/CG identifications (Saad §6.3.2, P-6.1(f); Choi; Fong–Saunders).
-/

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `⟪gramSchmidtNormed f j, f j⟫ = ‖gramSchmidt f j‖ ≥ 0`. -/
theorem inner_gramSchmidtNormed_self (f : ℕ → E) (j : ℕ) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f j) (f j) = (‖gramSchmidt 𝕜 f j‖ : 𝕜) := by
  sorry

/-- Flag uniqueness: an orthonormal family spanning the same flag as `f` differs from
`gramSchmidtNormed 𝕜 f` by unimodular scalars. -/
theorem exists_norm_eq_one_smul_gramSchmidtNormed {f u : ℕ → E} (hu : Orthonormal 𝕜 u)
    (hspan : ∀ j, Submodule.span 𝕜 (u '' Set.Iic j) = Submodule.span 𝕜 (f '' Set.Iic j))
    (j : ℕ) : ∃ ε : 𝕜, ‖ε‖ = 1 ∧ u j = ε • gramSchmidtNormed 𝕜 f j := by
  sorry

/-- With the sign normalization `re ⟪u_j, f_j⟫ > 0`, the orthonormal basis of the flag is
Gram–Schmidt itself. -/
theorem eq_gramSchmidtNormed_of_re_inner_pos {f u : ℕ → E} (hu : Orthonormal 𝕜 u)
    (hspan : ∀ j, Submodule.span 𝕜 (u '' Set.Iic j) = Submodule.span 𝕜 (f '' Set.Iic j))
    (j : ℕ) (hpos : 0 < RCLike.re (inner 𝕜 (u j) (f j))) : u j = gramSchmidtNormed 𝕜 f j := by
  sorry

/-- The `j`-th Gram–Schmidt vector is the component of `f j` orthogonal to the span of the
previous ones: `f j - gramSchmidt f j ∈ span {f i | i < j}` … -/
theorem sub_gramSchmidt_mem_span (f : ℕ → E) (j : ℕ) :
    f j - gramSchmidt 𝕜 f j ∈ Submodule.span 𝕜 (f '' Set.Iio j) := by
  sorry

/-- … and `gramSchmidt f j ⟂ span {f i | i < j}`. -/
theorem gramSchmidt_mem_orthogonal (f : ℕ → E) (j : ℕ) :
    gramSchmidt 𝕜 f j ∈ (Submodule.span 𝕜 (f '' Set.Iio j))ᗮ := by
  sorry

end InnerProductSpace
