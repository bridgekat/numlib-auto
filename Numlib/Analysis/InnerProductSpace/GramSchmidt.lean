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

open scoped ComplexOrder

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The `j`-th Gram–Schmidt vector is the component of `f j` orthogonal to the span of the
previous ones: `f j - gramSchmidt f j ∈ span {f i | i < j}` … -/
theorem sub_gramSchmidt_mem_span (f : ℕ → E) (j : ℕ) :
    f j - gramSchmidt 𝕜 f j ∈ Submodule.span 𝕜 (f '' Set.Iio j) := by
  rw [gramSchmidt_def, sub_sub_cancel, ← span_gramSchmidt_Iio 𝕜 f j]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hle : (𝕜 ∙ gramSchmidt 𝕜 f i) ≤ Submodule.span 𝕜 (gramSchmidt 𝕜 f '' Set.Iio j) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩
  exact hle (Submodule.starProjection_apply_mem _ (f j))

/-- … and `gramSchmidt f j ⟂ span {f i | i < j}`. -/
theorem gramSchmidt_mem_orthogonal (f : ℕ → E) (j : ℕ) :
    gramSchmidt 𝕜 f j ∈ (Submodule.span 𝕜 (f '' Set.Iio j))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  have hle : Submodule.span 𝕜 (f '' Set.Iio j) ≤
      LinearMap.ker ((innerSL 𝕜 (gramSchmidt 𝕜 f j) : E →L[𝕜] 𝕜) : E →ₗ[𝕜] 𝕜) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact gramSchmidt_inv_triangular 𝕜 f hi
  exact hle hu

/-- `⟪gramSchmidt f j, f j⟫ = ‖gramSchmidt f j‖²`: the Gram–Schmidt vector is the orthogonal
component of `f j`. -/
private theorem inner_gramSchmidt_self (f : ℕ → E) (j : ℕ) :
    inner 𝕜 (gramSchmidt 𝕜 f j) (f j) = ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' 𝕜 f j]
  rw [inner_add_right, inner_sum, inner_self_eq_norm_sq_to_K]
  convert add_zero _
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [inner_smul_right, gramSchmidt_orthogonal 𝕜 f (Finset.mem_Iio.1 hi).ne', mul_zero]

/-- `⟪gramSchmidtNormed f j, f j⟫ = ‖gramSchmidt f j‖ ≥ 0`. -/
theorem inner_gramSchmidtNormed_self (f : ℕ → E) (j : ℕ) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f j) (f j) = (‖gramSchmidt 𝕜 f j‖ : 𝕜) := by
  rw [gramSchmidtNormed, inner_smul_left, inner_gramSchmidt_self, RCLike.conj_inv,
    RCLike.conj_ofReal]
  rcases eq_or_ne ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) 0 with h | h
  · simp [h]
  · rw [sq, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- Flag uniqueness: an orthonormal family spanning the same flag as `f` differs from
`gramSchmidtNormed 𝕜 f` by unimodular scalars. -/
theorem exists_norm_eq_one_smul_gramSchmidtNormed {f u : ℕ → E} (hu : Orthonormal 𝕜 u)
    (hspan : ∀ j, Submodule.span 𝕜 (u '' Set.Iic j) = Submodule.span 𝕜 (f '' Set.Iic j))
    (j : ℕ) : ∃ ε : 𝕜, ‖ε‖ = 1 ∧ u j = ε • gramSchmidtNormed 𝕜 f j := by
  have hIio : Submodule.span 𝕜 (u '' Set.Iio j) = Submodule.span 𝕜 (f '' Set.Iio j) := by
    cases j with
    | zero => simp
    | succ k =>
      rw [show Set.Iio (k + 1) = Set.Iic k from Set.ext fun _ => Nat.lt_succ_iff]
      exact hspan k
  have huperp : u j ∈ (Submodule.span 𝕜 (f '' Set.Iio j))ᗮ := by
    rw [← hIio, Submodule.mem_orthogonal']
    intro w hw
    have hle : Submodule.span 𝕜 (u '' Set.Iio j) ≤
        LinearMap.ker ((innerSL 𝕜 (u j) : E →L[𝕜] 𝕜) : E →ₗ[𝕜] 𝕜) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact hu.2 (Nat.ne_of_gt hi)
    exact hle hw
  have hmem : u j ∈ Submodule.span 𝕜 (f '' Set.Iic j) := by
    rw [← hspan j]
    exact Submodule.subset_span ⟨j, Set.mem_Iic.2 le_rfl, rfl⟩
  rw [show Set.Iic j = insert j (Set.Iio j) from (Set.Iio_insert (a := j)).symm,
    Set.image_insert_eq,
    Submodule.span_insert] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hs : u j - c • gramSchmidt 𝕜 f j ∈ Submodule.span 𝕜 (f '' Set.Iio j) := by
    have hrw : u j - c • gramSchmidt 𝕜 f j = c • (f j - gramSchmidt 𝕜 f j) + z := by
      rw [← hyz]; module
    rw [hrw]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (sub_gramSchmidt_mem_span f j)) hz
  have hsperp : u j - c • gramSchmidt 𝕜 f j ∈ (Submodule.span 𝕜 (f '' Set.Iio j))ᗮ :=
    Submodule.sub_mem _ huperp (Submodule.smul_mem _ _ (gramSchmidt_mem_orthogonal f j))
  have huj : u j = c • gramSchmidt 𝕜 f j := by
    rw [← sub_eq_zero]
    exact inner_self_eq_zero.1
      ((Submodule.mem_orthogonal' _ _).1 hsperp _ hs)
  have hnorm : ‖u j‖ = 1 := hu.1 j
  have hg : gramSchmidt 𝕜 f j ≠ 0 := by
    intro h
    rw [huj, h, smul_zero, norm_zero] at hnorm
    norm_num at hnorm
  have hgn : ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) ≠ 0 := by
    simpa using norm_ne_zero_iff.2 hg
  refine ⟨c * (‖gramSchmidt 𝕜 f j‖ : 𝕜), ?_, ?_⟩
  · rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    rw [huj, norm_smul] at hnorm
    exact hnorm
  · rw [huj, gramSchmidtNormed, smul_smul, mul_assoc, mul_inv_cancel₀ hgn, mul_one]

/-- A unimodular scalar whose product with a nonnegative real is positive is `1`. -/
private theorem eq_one_of_norm_eq_one_of_mul_ofReal_pos {w : 𝕜} (hw : ‖w‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hpos : 0 < w * (r : 𝕜)) : w = 1 := by
  rw [mul_comm, RCLike.pos_iff, RCLike.re_ofReal_mul, RCLike.im_ofReal_mul] at hpos
  obtain ⟨h1, h2⟩ := hpos
  have hr0 : r ≠ 0 := by rintro rfl; simp at h1
  have hrpos : 0 < r := hr.lt_of_ne (Ne.symm hr0)
  have him : RCLike.im w = 0 := (mul_eq_zero.1 h2).resolve_left hr0
  have hre : 0 < RCLike.re w := by nlinarith
  have hsq : RCLike.re w * RCLike.re w + RCLike.im w * RCLike.im w = 1 := by
    rw [← RCLike.norm_sq_eq_def, hw]; norm_num
  refine RCLike.ext ?_ ?_
  · rw [RCLike.one_re]; nlinarith
  · rw [RCLike.one_im, him]

/-- With the sign normalization `⟪u_j, f_j⟫ > 0`, the orthonormal basis of the flag is
Gram–Schmidt itself.

The hypothesis is positivity of `⟪u_j, f_j⟫` in `𝕜` (`RCLike` order, i.e. the inner product is a
positive real), not merely of its real part: over `ℂ` a unimodular factor `ε` with `re ε > 0` is
not forced to be `1`, so the `re`-only version of this statement is false. Over `ℝ` the two
hypotheses agree. -/
theorem eq_gramSchmidtNormed_of_re_inner_pos {f u : ℕ → E} (hu : Orthonormal 𝕜 u)
    (hspan : ∀ j, Submodule.span 𝕜 (u '' Set.Iic j) = Submodule.span 𝕜 (f '' Set.Iic j))
    (j : ℕ) (hpos : 0 < inner 𝕜 (u j) (f j)) : u j = gramSchmidtNormed 𝕜 f j := by
  obtain ⟨ε, hε, hue⟩ := exists_norm_eq_one_smul_gramSchmidtNormed hu hspan j
  rw [hue, inner_smul_left, inner_gramSchmidtNormed_self] at hpos
  have hconj : (starRingEnd 𝕜) ε = 1 :=
    eq_one_of_norm_eq_one_of_mul_ofReal_pos (by rwa [RCLike.norm_conj]) (norm_nonneg _) hpos
  have hε1 : ε = 1 := by
    have := congrArg (starRingEnd 𝕜) hconj
    rwa [RCLike.conj_conj, map_one] at this
  rw [hue, hε1, one_smul]

end InnerProductSpace
