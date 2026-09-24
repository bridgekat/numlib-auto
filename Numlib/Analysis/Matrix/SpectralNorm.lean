/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.CStarAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Rank

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
* `IsSelfAdjoint.norm_pow` and `Matrix.IsHermitian.l2_opNorm_pow`: `‖Aᵐ‖₂ = ‖A‖₂ᵐ` for a Hermitian
  matrix, the C⋆-identity `‖A²‖ = ‖A‖²` iterated, with `Matrix.IsHermitian.l2_opNorm_pow_rpow`
  for the root form `‖Aᵐ‖₂ ^ (1 / m) = ‖A‖₂`.
* `Matrix.l2_opNorm_eq_complexSpectralRadius_of_isHermitian`: the spectral norm of a real
  symmetric matrix is its spectral radius.
* `Matrix.l2_opNorm_submatrix_le`: a submatrix, for injective row and column selections, has the
  smaller spectral norm, through `Matrix.submatrix_mulVec_eq_comp_mulVec_extend` and the `ℓ^p`
  facts `PiLp.norm_toLp_comp_le`, `PiLp.norm_toLp_extend`; the induced `p`-norm version is
  `Matrix.lpOpNorm_submatrix_le` in `Numlib/Analysis/Matrix/OperatorNorm`.
* `Matrix.l2_opNorm_fromBlocks_le`: Kahan's bound on the spectral norm of a `2 × 2` block matrix
  by the norms of its blocks, the largest eigenvalue of `[μ γ; γ δ]` ([golub2013matrix]
  Lemma 10.3.1), with its Hermitian-shaped case `Matrix.l2_opNorm_fromBlocks_le_of_isHermitian`.
-/

open scoped Matrix.Norms.L2Operator

section CStarRing

variable {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]

/-- In a C⋆-ring, `‖xⁿ‖₊ = ‖x‖₊ⁿ` for a self-adjoint `x` and every `n ≠ 0`: the identity
`IsSelfAdjoint.nnnorm_pow_two_pow` for powers of two, then `‖x‖ ^ 2ᵏ = ‖xⁿ x ^ (2ᵏ - n)‖ ≤ ‖xⁿ‖
‖x‖ ^ (2ᵏ - n)` for `n < 2ᵏ`. (The exponent `0` needs `‖1‖ = 1`, which a C⋆-ring may lack.) -/
theorem IsSelfAdjoint.nnnorm_pow {x : E} (hx : IsSelfAdjoint x) {n : ℕ} (hn : n ≠ 0) :
    ‖x ^ n‖₊ = ‖x‖₊ ^ n := by
  refine le_antisymm (nnnorm_pow_le' x (Nat.pos_of_ne_zero hn)) ?_
  obtain ⟨j, hj, hj0⟩ : ∃ j, 2 ^ n = n + j ∧ j ≠ 0 :=
    ⟨2 ^ n - n, by have := n.lt_two_pow_self; omega, by have := n.lt_two_pow_self; omega⟩
  rcases eq_or_ne ‖x‖₊ 0 with h0 | h0
  · rw [h0, zero_pow hn]
    exact zero_le
  have h := hx.nnnorm_pow_two_pow n
  rw [hj, pow_add, pow_add] at h
  have hle : ‖x‖₊ ^ n * ‖x‖₊ ^ j ≤ ‖x ^ n‖₊ * ‖x‖₊ ^ j := by
    rw [← h]
    exact (nnnorm_mul_le _ _).trans (by gcongr; exact nnnorm_pow_le' x (Nat.pos_of_ne_zero hj0))
  exact le_of_mul_le_mul_right hle (pos_iff_ne_zero.2 (pow_ne_zero _ h0))

/-- In a C⋆-ring, `‖xⁿ‖ = ‖x‖ⁿ` for a self-adjoint `x` and every `n ≠ 0`. -/
theorem IsSelfAdjoint.norm_pow {x : E} (hx : IsSelfAdjoint x) {n : ℕ} (hn : n ≠ 0) :
    ‖x ^ n‖ = ‖x‖ ^ n :=
  congr($(hx.nnnorm_pow hn))

end CStarRing

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- The eigenvalues of a Hermitian matrix are real. -/
theorem IsHermitian.ofReal_re_of_hasEigenvalue (hA : A.IsHermitian) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (toEuclideanLin A) μ) : ((RCLike.re μ : ℝ) : 𝕜) = μ :=
  RCLike.conj_eq_iff_re.mp
    ((isSymmetric_toEuclideanLin_iff.mpr hA).conj_eigenvalue_eq_self hμ)

/-- For a real eigenvalue the real part commutes with inversion. -/
private theorem re_inv_of_ofReal_re {μ : 𝕜} (hμ : ((RCLike.re μ : ℝ) : 𝕜) = μ) :
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

/-- **The spectral norm of a power of a Hermitian matrix is the power of the spectral norm**:
`‖Aᵐ‖₂ = ‖A‖₂ᵐ` for `m ≠ 0`. This is the C⋆-identity `IsSelfAdjoint.norm_pow` in the
C⋆-ring `Matrix n n 𝕜` with the `ℓ²` operator norm; the exponent `0` is excluded because
`‖1‖₂ = 0 ≠ 1` when `n` is empty. -/
theorem IsHermitian.l2_opNorm_pow (hA : A.IsHermitian) {m : ℕ} (hm : m ≠ 0) :
    ‖A ^ m‖ = ‖A‖ ^ m :=
  hA.isSelfAdjoint.norm_pow hm

/-- The root form of `Matrix.IsHermitian.l2_opNorm_pow`: `‖Aᵐ‖₂ ^ (1 / m) = ‖A‖₂` for `m ≠ 0`,
so that the Gelfand sequence of a Hermitian matrix is constant. -/
theorem IsHermitian.l2_opNorm_pow_rpow (hA : A.IsHermitian) {m : ℕ} (hm : m ≠ 0) :
    ‖A ^ m‖ ^ (1 / m : ℝ) = ‖A‖ := by
  rw [hA.l2_opNorm_pow hm, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    mul_one_div_cancel (Nat.cast_ne_zero.2 hm), Real.rpow_one]

/-- **The spectral norm of a real symmetric matrix is its spectral radius**:
`‖A‖₂ = ρ(A)` for `A : Matrix n n ℝ` with `Aᵀ = A`, the spectral radius being the complex one
(`Matrix.complexSpectralRadius`). Complexification preserves the norm
(`Matrix.l2_opNorm_complexify`) and Hermitian-ness, and in the C⋆-algebra `Matrix n n ℂ` the norm
of a self-adjoint element is its spectral radius
(`IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm`). With
`Matrix.IsHermitian.l2_opNorm_pow` this gives `‖Aᵐ‖₂ = ρ(A)ᵐ` for every `m`, the symmetric case
of [quarteroni2000numerical] (4.5). -/
theorem l2_opNorm_eq_complexSpectralRadius_of_isHermitian {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : ‖A‖ = (complexSpectralRadius A).toReal := by
  rw [← l2_opNorm_complexify, complexSpectralRadius]
  exact (IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm
    ((isHermitian_complexify_iff A).mpr hA).isSelfAdjoint).symm

/-- The `ℓ²` operator norm of a symmetric matrix whose quadratic form is enclosed in `[-M, M]` is
at most `M`: one half of `Matrix.IsHermitian.l2_opNorm_eq`, through Rayleigh quotients
(`ContinuousLinearMap.norm_le_of_isSymmetricBoundedBy`). -/
theorem norm_toEuclideanCLM_le_of_isSymmetricBoundedBy {A : Matrix n n ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : (toEuclideanLin A).IsSymmetricBoundedBy (-M) M) :
    ‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ M := by
  rw [l2_opNorm_toEuclideanCLM, l2_opNorm_eq_norm_toEuclideanLin]
  exact ContinuousLinearMap.norm_le_of_isSymmetricBoundedBy hM hb

/-! ### Submatrices -/

section Submatrix

/-- **A submatrix has a smaller spectral norm**, for injective row and column selections:
`‖A.submatrix f g‖₂ ≤ ‖A‖₂` ([golub2013matrix] (2.3.13) at `p = 2`). Apply `A` to the vector
extended by zero along `g` (`PiLp.norm_toLp_extend`) and drop the coordinates outside the range
of `f` (`PiLp.norm_toLp_comp_le`). -/
theorem l2_opNorm_submatrix_le {m m' n' : Type*} [Fintype m] [Fintype m'] [Fintype n']
    [DecidableEq n'] (B : Matrix m n 𝕜) {f : m' → m} (hf : Function.Injective f) {g : n' → n}
    (hg : Function.Injective g) : ‖B.submatrix f g‖ ≤ ‖B‖ := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have key : ‖(WithLp.toLp 2 (B.submatrix f g *ᵥ WithLp.ofLp x) : EuclideanSpace 𝕜 m')‖
      ≤ ‖B‖ * ‖x‖ := by
    rw [submatrix_mulVec_eq_comp_mulVec_extend B f hg]
    calc ‖(WithLp.toLp 2 ((B *ᵥ Function.extend g (WithLp.ofLp x) 0) ∘ f) : EuclideanSpace 𝕜 m')‖
        ≤ ‖(WithLp.toLp 2 (B *ᵥ Function.extend g (WithLp.ofLp x) 0) : EuclideanSpace 𝕜 m)‖ :=
          PiLp.norm_toLp_comp_le 2 hf _
      _ ≤ ‖B‖ * ‖(WithLp.toLp 2 (Function.extend g (WithLp.ofLp x) 0) : EuclideanSpace 𝕜 n)‖ :=
          l2_opNorm_mulVec B (WithLp.toLp 2 (Function.extend g (WithLp.ofLp x) 0))
      _ = ‖B‖ * ‖x‖ := by rw [PiLp.norm_toLp_extend 2 hg]
  exact key

end Submatrix

/-! ### Block matrices -/

section Blocks

/-- The largest eigenvalue `λ = (μ + δ + √((μ - δ)² + 4γ²)) / 2` of the symmetric matrix
`[μ γ; γ δ]` with nonnegative entries bounds its quadratic action:
`(μ a + γ b)² + (γ a + δ b)² ≤ λ² (a² + b²)`. -/
private theorem sq_add_sq_le_of_blockBound {μ γ δ a b : ℝ} (hμ : 0 ≤ μ) (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) :
    (μ * a + γ * b) ^ 2 + (γ * a + δ * b) ^ 2
      ≤ ((μ + δ + √((μ - δ) ^ 2 + 4 * γ ^ 2)) / 2) ^ 2 * (a ^ 2 + b ^ 2) := by
  set s := √((μ - δ) ^ 2 + 4 * γ ^ 2) with hs_def
  set l := (μ + δ + s) / 2 with hl
  have hs2 : s ^ 2 = (μ - δ) ^ 2 + 4 * γ ^ 2 := Real.sq_sqrt (by positivity)
  have hsabs : |δ - μ| ≤ s := Real.abs_le_sqrt (by nlinarith [sq_abs (δ - μ)])
  have hlμ : 0 ≤ l - μ := by rw [hl]; linarith [neg_abs_le (δ - μ)]
  have hlδ : 0 ≤ l - δ := by rw [hl]; linarith [le_abs_self (δ - μ)]
  have hchar' : l ^ 2 - (μ + δ) * l + μ * δ - γ ^ 2 = 0 := by
    rw [hl]; linear_combination hs2 / 4
  have hchar : (l - μ) * (l - δ) = γ ^ 2 := by linear_combination hchar'
  set P := √(l - μ)
  set R := √(l - δ)
  have hP : P ^ 2 = l - μ := Real.sq_sqrt hlμ
  have hR : R ^ 2 = l - δ := Real.sq_sqrt hlδ
  have hPR : P * R = γ := by
    rw [← Real.sqrt_mul hlμ, hchar, Real.sqrt_sq hγ]
  have key : l ^ 2 * (a ^ 2 + b ^ 2) - ((μ * a + γ * b) ^ 2 + (γ * a + δ * b) ^ 2)
      = (μ + δ) * (P * a - R * b) ^ 2 := by
    linear_combination (a ^ 2 + b ^ 2) * hchar' - (μ + δ) * a ^ 2 * hP - (μ + δ) * b ^ 2 * hR
      + 2 * (μ + δ) * a * b * hPR
  nlinarith [mul_nonneg (add_nonneg hμ hδ) (sq_nonneg (P * a - R * b))]

/-- The squared `ℓ²` norm of a vector on a sum type is the sum of the squared norms of its two
parts. -/
private theorem norm_toLp_sumElim_sq {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂] (u : m₁ → 𝕜)
    (w : m₂ → 𝕜) :
    ‖(WithLp.toLp 2 (Sum.elim u w) : EuclideanSpace 𝕜 (m₁ ⊕ m₂))‖ ^ 2
      = ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 m₁)‖ ^ 2
        + ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 m₂)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr]

/-- **The spectral norm of a `2 × 2` block matrix from the norms of its blocks**: if `‖E‖₂ ≤ μ`,
`‖C‖₂ ≤ γ`, `‖C'‖₂ ≤ γ` and `‖D‖₂ ≤ δ`, then `‖[E C; C' D]‖₂ ≤ λ`, the largest eigenvalue
`(μ + δ + √((μ - δ)² + 4γ²)) / 2` of `[μ γ; γ δ]` (Kahan's lemma, [golub2013matrix] Lemma 10.3.1,
stated there for a Hermitian matrix `C' = Cᴴ`; no symmetry is needed). Blockwise,
`‖M z‖² ≤ (μ ‖x‖ + γ ‖y‖)² + (γ ‖x‖ + δ ‖y‖)² ≤ λ² ‖z‖²` for `z = (x, y)`. -/
theorem l2_opNorm_fromBlocks_le {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Fintype n₁]
    [Fintype n₂] [DecidableEq n₁] [DecidableEq n₂] {E : Matrix m₁ n₁ 𝕜} {C : Matrix m₁ n₂ 𝕜}
    {C' : Matrix m₂ n₁ 𝕜} {D : Matrix m₂ n₂ 𝕜} {μ γ δ : ℝ} (hE : ‖E‖ ≤ μ) (hC : ‖C‖ ≤ γ)
    (hC' : ‖C'‖ ≤ γ) (hD : ‖D‖ ≤ δ) :
    ‖fromBlocks E C C' D‖ ≤ (μ + δ + √((μ - δ) ^ 2 + 4 * γ ^ 2)) / 2 := by
  have hμ : 0 ≤ μ := (norm_nonneg _).trans hE
  have hγ : 0 ≤ γ := (norm_nonneg _).trans hC
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hD
  have hl : 0 ≤ (μ + δ + √((μ - δ) ^ 2 + 4 * γ ^ 2)) / 2 := by positivity
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hl fun z => ?_
  set x : n₁ → 𝕜 := fun i => WithLp.ofLp z (Sum.inl i)
  set y : n₂ → 𝕜 := fun i => WithLp.ofLp z (Sum.inr i)
  have hz : WithLp.ofLp z = Sum.elim x y := by
    funext i; cases i <;> rfl
  have hnz : ‖z‖ ^ 2 = ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n₁)‖ ^ 2
      + ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 n₂)‖ ^ 2 := by
    rw [← norm_toLp_sumElim_sq, ← hz, WithLp.toLp_ofLp]
  -- the two block rows
  have h1 : ‖(WithLp.toLp 2 (E *ᵥ x + C *ᵥ y) : EuclideanSpace 𝕜 m₁)‖
      ≤ μ * ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n₁)‖
        + γ * ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 n₂)‖ := by
    rw [WithLp.toLp_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (l2_opNorm_mulVec E (WithLp.toLp 2 x)).trans
        (mul_le_mul_of_nonneg_right hE (norm_nonneg _))
    · exact (l2_opNorm_mulVec C (WithLp.toLp 2 y)).trans
        (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  have h2 : ‖(WithLp.toLp 2 (C' *ᵥ x + D *ᵥ y) : EuclideanSpace 𝕜 m₂)‖
      ≤ γ * ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n₁)‖
        + δ * ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 n₂)‖ := by
    rw [WithLp.toLp_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (l2_opNorm_mulVec C' (WithLp.toLp 2 x)).trans
        (mul_le_mul_of_nonneg_right hC' (norm_nonneg _))
    · exact (l2_opNorm_mulVec D (WithLp.toLp 2 y)).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have hMz : ‖(WithLp.toLp 2 (fromBlocks E C C' D *ᵥ WithLp.ofLp z)
      : EuclideanSpace 𝕜 (m₁ ⊕ m₂))‖ ^ 2
      ≤ ((μ + δ + √((μ - δ) ^ 2 + 4 * γ ^ 2)) / 2 * ‖z‖) ^ 2 := by
    rw [hz, fromBlocks_mulVec, norm_toLp_sumElim_sq, mul_pow, hnz]
    refine le_trans ?_ (sq_add_sq_le_of_blockBound hμ hγ hδ)
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2)
      (pow_le_pow_left₀ (norm_nonneg _) h2 2)
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hMz

/-- **Kahan's lemma for a Hermitian-shaped block matrix** ([golub2013matrix] Lemma 10.3.1): for
`M = [E C; Cᴴ D]` with `‖E‖₂ ≤ μ`, `‖C‖₂ ≤ γ`, `‖D‖₂ ≤ δ`,
`‖M‖₂ ≤ (μ + δ + √((μ - δ)² + 4γ²)) / 2`. The case `C' = Cᴴ` of
`Matrix.l2_opNorm_fromBlocks_le`, since `‖Cᴴ‖₂ = ‖C‖₂`; the Hermitian-ness of `E` and `D` is not
needed. -/
theorem l2_opNorm_fromBlocks_le_of_isHermitian {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂] {E : Matrix m₁ m₁ 𝕜} {C : Matrix m₁ m₂ 𝕜}
    {D : Matrix m₂ m₂ 𝕜}
    {μ γ δ : ℝ} (hE : ‖E‖ ≤ μ) (hC : ‖C‖ ≤ γ) (hD : ‖D‖ ≤ δ) :
    ‖fromBlocks E C Cᴴ D‖ ≤ (μ + δ + √((μ - δ) ^ 2 + 4 * γ ^ 2)) / 2 :=
  l2_opNorm_fromBlocks_le hE hC (by rwa [l2_opNorm_conjTranspose]) hD

end Blocks

end Matrix
