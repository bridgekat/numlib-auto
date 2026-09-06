/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.CStarAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin

/-!
# The spectral norm of a Hermitian matrix

The bridge from the *spectrum* of a Hermitian matrix to its *spectral norm*, the `ℓ²` operator
norm carried by Mathlib's scoped `Matrix.Norms.L2Operator` instances: `‖A‖₂` is the largest
modulus of an eigenvalue, and for an invertible `A` the norm of the inverse is the reciprocal of
the smallest.  Together they compute the spectral condition number `κ₂(A) = λmax / λmin` of a
positive definite matrix, the form in which the conditioning of a discretized differential operator
is usually stated.

The two halves of the norm identity are the two halves of Rayleigh's principle: the quadratic form
of a symmetric operator is enclosed by its extreme eigenvalues, and the enclosure is attained at an
eigenvector.  Mathlib's `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` turns the enclosure
into a norm bound and `ContinuousLinearMap.rayleighQuotient_le_norm` turns the attainment into the
reverse bound, so no diagonalization is needed.

## Main results

* `Matrix.IsHermitian.l2_opNorm_eq`: `‖A‖₂ = M` when every eigenvalue has modulus at most `M` and
  some eigenvalue has modulus exactly `M`.
* `Matrix.hasEigenvalue_toEuclideanLin_inv_iff`: the eigenvalues of `A⁻¹` are the reciprocals of
  the eigenvalues of an invertible `A`.
* `Matrix.IsHermitian.l2_opNorm_inv_eq`: `‖A⁻¹‖₂ = m⁻¹` when every eigenvalue has modulus at least
  `m > 0` and some eigenvalue has modulus exactly `m`.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- The eigenvalues of a Hermitian matrix are real. -/
theorem IsHermitian.ofReal_re_of_hasEigenvalue (hA : A.IsHermitian) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (toEuclideanLin A) μ) : ((RCLike.re μ : ℝ) : 𝕜) = μ :=
  RCLike.conj_eq_iff_re.mp
    ((isSymmetric_toEuclideanLin_iff.mpr hA).conj_eigenvalue_eq_self hμ)

/-- For a real eigenvalue the real part commutes with inversion. -/
private theorem re_inv_of_ofReal_re (hμ : ((RCLike.re μ : ℝ) : 𝕜) = μ) :
    RCLike.re μ⁻¹ = (RCLike.re μ)⁻¹ := by
  rw [← hμ, ← RCLike.ofReal_inv, RCLike.ofReal_re, RCLike.ofReal_re]

/-- **The spectral norm of a Hermitian matrix is the largest modulus of an eigenvalue.**  The
hypotheses say exactly that: every eigenvalue has modulus at most `M`, and `M` is attained. -/
theorem IsHermitian.l2_opNorm_eq (hA : A.IsHermitian) {M : ℝ}
    (hle : ∀ μ : 𝕜, Module.End.HasEigenvalue (toEuclideanLin A) μ → |RCLike.re μ| ≤ M)
    (hmem : ∃ μ : 𝕜, Module.End.HasEigenvalue (toEuclideanLin A) μ ∧ |RCLike.re μ| = M) :
    ‖A‖ = M := by
  obtain ⟨μ₀, hμ₀, hμ₀M⟩ := hmem
  have hM0 : 0 ≤ M := hμ₀M ▸ abs_nonneg _
  have hsymm : (toEuclideanLin A).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  set T : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n :=
    LinearMap.toContinuousLinearMap (toEuclideanLin A) with hT
  have hTsymm : (T : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n).IsSymmetric := hsymm
  have hbdd : (T : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n).IsSymmetricBoundedBy (-M) M :=
    (LinearMap.IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue hTsymm _ _).mpr
      fun μ hμ => abs_le.mp (hle μ hμ)
  rw [l2_opNorm_eq_norm_toEuclideanLin, ← hT]
  refine le_antisymm ?_ ?_
  · rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hTsymm]
    refine ciSup_le fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] using hM0
    · have h := hbdd.rayleigh_mem_Icc hx
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, abs_le]
      exact ⟨h.1, h.2⟩
  · obtain ⟨x, hx, hx0⟩ := hμ₀.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hx
    have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx0) 2
    have hrq : T.rayleighQuotient x = RCLike.re μ₀ := by
      have hxx : T x = μ₀ • x := hx
      have hnorm : RCLike.re (inner 𝕜 (T x) x) = RCLike.re μ₀ * ‖x‖ ^ 2 := by
        rw [hxx, inner_smul_left, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im,
          inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re, RCLike.ofReal_im]
        ring
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, hnorm,
        mul_div_assoc, div_self hx2.ne', mul_one]
    rw [← hμ₀M, ← hrq]
    exact T.rayleighQuotient_le_norm x

/-- **The eigenvalues of the inverse are the reciprocals of the eigenvalues.**  Stated for an
invertible `A`, for which `0` is an eigenvalue of neither side, so `μ` needs no side condition. -/
theorem hasEigenvalue_toEuclideanLin_inv_iff (hA : IsUnit A) (μ : 𝕜) :
    Module.End.HasEigenvalue (toEuclideanLin A⁻¹) μ ↔
      Module.End.HasEigenvalue (toEuclideanLin A) μ⁻¹ := by
  obtain ⟨u, rfl⟩ := hA
  rw [hasEigenvalue_toEuclideanLin_iff, hasEigenvalue_toEuclideanLin_iff, ← coe_units_inv,
    ← spectrum.map_inv u, Set.mem_inv]

/-- **The spectral norm of the inverse of a Hermitian matrix is the reciprocal of the smallest
modulus of an eigenvalue.**  Every eigenvalue is assumed of modulus at least `m > 0`, and `m` is
assumed attained; positivity of `m` is what makes `A` invertible. -/
theorem IsHermitian.l2_opNorm_inv_eq (hA : A.IsHermitian) {m : ℝ} (hm : 0 < m)
    (hle : ∀ μ : 𝕜, Module.End.HasEigenvalue (toEuclideanLin A) μ → m ≤ |RCLike.re μ|)
    (hmem : ∃ μ : 𝕜, Module.End.HasEigenvalue (toEuclideanLin A) μ ∧ |RCLike.re μ| = m) :
    ‖A⁻¹‖ = m⁻¹ := by
  have hzero : ¬ Module.End.HasEigenvalue (toEuclideanLin A) 0 := fun h => by
    have h0 : m ≤ |RCLike.re (0 : 𝕜)| := hle 0 h
    simp only [map_zero, abs_zero] at h0
    exact absurd h0 (not_le.mpr hm)
  have hAunit : IsUnit A := by
    by_contra hnot
    exact hzero ((Matrix.hasEigenvalue_toEuclideanLin_iff A 0).mpr
      (spectrum.zero_mem (R := 𝕜) hnot))
  refine hA.inv.l2_opNorm_eq ?_ ?_
  · intro ν hν
    have hν' := (Matrix.hasEigenvalue_toEuclideanLin_inv_iff hAunit ν).mp hν
    have hν0 : ν ≠ 0 := by rintro rfl; exact hzero (by simpa using hν')
    have hre : RCLike.re ν = (RCLike.re ν⁻¹)⁻¹ := by
      rw [re_inv_of_ofReal_re (hA.inv.ofReal_re_of_hasEigenvalue hν), inv_inv]
    rw [hre, abs_inv]
    exact inv_anti₀ hm (hle _ hν')
  · obtain ⟨μ₀, hμ₀, hμ₀m⟩ := hmem
    have hμ₀0 : μ₀ ≠ 0 := by rintro rfl; exact hzero hμ₀
    refine ⟨μ₀⁻¹, (Matrix.hasEigenvalue_toEuclideanLin_inv_iff hAunit _).mpr (by rwa [inv_inv]), ?_⟩
    rw [re_inv_of_ofReal_re (hA.ofReal_re_of_hasEigenvalue hμ₀), abs_inv, hμ₀m]

end Matrix
