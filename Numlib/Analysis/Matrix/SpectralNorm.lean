/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

This file relates the spectrum of a Hermitian matrix $A \in \mathbb{K}^{n \times n}$,
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, to its spectral norm $\|A\|_2$, the operator norm for the
Euclidean norm. The spectral norm is the largest modulus of an eigenvalue, and for an invertible $A$
the norm $\|A^{-1}\|_2$ is the reciprocal of the smallest modulus of an eigenvalue. Together these
give the spectral condition number $\kappa_2(A) = \lambda_{\max} / \lambda_{\min}$ of a positive
definite matrix, the form in which the conditioning of a discretized differential operator is
usually stated. The file also proves $\|A^m\|_2 = \|A\|_2^m$ for Hermitian $A$, and that the
spectral norm of a real symmetric matrix is its spectral radius.

The file then gives three groups of bounds for general matrices: a submatrix has at most the
spectral norm of the matrix, the rank-one matrix $u w^T$ has spectral norm $\|u\|_2 \|w\|_2$, and
Kahan's lemma bounds the spectral norm of a $2 \times 2$ block matrix by the largest eigenvalue of
the $2 \times 2$ matrix of the norms of its blocks ([golub2013matrix], Lemma 10.3.1).

## Main results

* `IsSelfAdjoint.norm_pow`: in a C⋆-ring, $\|x^n\| = \|x\|^n$ for self-adjoint $x$ and $n \ne 0$.
* `Matrix.IsHermitian.l2_opNorm_eq`: $\|A\|_2 = M$ if every eigenvalue has modulus at most $M$ and
  some eigenvalue has modulus $M$.
* `Matrix.hasEigenvalue_toEuclideanLin_inv_iff`: the eigenvalues of $A^{-1}$ are the reciprocals of
  the eigenvalues of an invertible $A$.
* `Matrix.IsHermitian.l2_opNorm_inv_eq`: $\|A^{-1}\|_2 = 1/m$ if every eigenvalue has modulus at
  least $m > 0$ and some eigenvalue has modulus $m$.
* `Matrix.IsHermitian.l2_opNorm_pow`: $\|A^m\|_2 = \|A\|_2^m$ for Hermitian $A$ and $m \ne 0$, with
  the root form `Matrix.IsHermitian.l2_opNorm_pow_rpow`.
* `Matrix.l2_opNorm_eq_complexSpectralRadius_of_isHermitian`: the spectral norm of a real symmetric
  matrix is its spectral radius.
* `Matrix.norm_toLp_submatrix_mulVec_le`: selecting rows and columns preserves an operator bound in
  the $\ell^p$ norms.
* `Matrix.l2_opNorm_submatrix_le`: a submatrix has at most the spectral norm of the matrix, and
  `Matrix.l2_opNorm_submatrix_equiv`: reindexing does not change it.
* `Matrix.l2_opNorm_vecMulVec`: $\|u w^T\|_2 = \|u\|_2 \|w\|_2$.
* `Matrix.l2_opNorm_fromBlocks_le`: Kahan's bound on the spectral norm of a $2 \times 2$ block
  matrix, with the case `Matrix.l2_opNorm_fromBlocks_conjTranspose_le` of a block matrix of
  Hermitian shape.

## Proof outline

The two halves of the norm identity are the two halves of Rayleigh's principle. The quadratic form
of a symmetric operator lies between its extreme eigenvalues, and it attains them at eigenvectors.
Mathlib's `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` turns the enclosure into an upper
bound on the norm, and `ContinuousLinearMap.rayleighQuotient_le_norm` turns the attainment into the
lower bound, so no diagonalization is needed.

## Implementation notes

* The spectral norm $\|A\|_2$ is the norm of the scoped instance `Matrix.Norms.L2Operator`. The
  eigenvalues of $A$ are the eigenvalues of the operator `Matrix.toEuclideanLin A`, and a modulus
  $|\mu|$ is written `|RCLike.re μ|`, which is the same for a real eigenvalue.
* The induced $p$-norm version of `Matrix.l2_opNorm_submatrix_le` is `Matrix.lpOpNorm_submatrix_le`
  in `Numlib.Analysis.Matrix.OperatorNorm`.
-/

open scoped Matrix.Norms.L2Operator

section CStarRing

variable {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]

/-- Let $E$ be a C⋆-ring, let $x \in E$ be self-adjoint, and let $n \ne 0$ be a natural number. Then
$\|x^n\|_+ = \|x\|_+^n$ for the nonnegative norm.

The proof uses `IsSelfAdjoint.nnnorm_pow_two_pow` for powers of two, and then $\|x\|^{2^k} =
\|x^n x^{2^k - n}\| \le \|x^n\| \|x\|^{2^k - n}$ for $n < 2^k$. The exponent $n = 0$ is excluded
because it needs $\|1\| = 1$, which a C⋆-ring can fail to have. -/
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

/-- Let $E$ be a C⋆-ring, let $x \in E$ be self-adjoint, and let $n \ne 0$ be a natural number. Then
$$\|x^n\| = \|x\|^n.$$

This is `IsSelfAdjoint.nnnorm_pow` for the real norm. -/
theorem IsSelfAdjoint.norm_pow {x : E} (hx : IsSelfAdjoint x) {n : ℕ} (hn : n ≠ 0) :
    ‖x ^ n‖ = ‖x‖ ^ n :=
  congr($(hx.nnnorm_pow hn))

end CStarRing

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- The eigenvalues of a Hermitian matrix are real. Let $A \in \mathbb{K}^{n \times n}$ be Hermitian
and let $\mu \in \mathbb{K}$ be an eigenvalue of $A$. Then $\mu = \operatorname{Re} \mu$.

An eigenvalue of $A$ is an eigenvalue of the operator `Matrix.toEuclideanLin A`. -/
theorem IsHermitian.ofReal_re_of_hasEigenvalue (hA : A.IsHermitian) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (toEuclideanLin A) μ) : ((RCLike.re μ : ℝ) : 𝕜) = μ :=
  RCLike.conj_eq_iff_re.mp
    ((isSymmetric_toEuclideanLin_iff.mpr hA).conj_eigenvalue_eq_self hμ)

/-- For a $\mu \in \mathbb{K}$ that is real, $\operatorname{Re}(\mu^{-1}) = (\operatorname{Re}
\mu)^{-1}$. -/
private theorem re_inv_of_ofReal_re {μ : 𝕜} (hμ : ((RCLike.re μ : ℝ) : 𝕜) = μ) :
    RCLike.re μ⁻¹ = (RCLike.re μ)⁻¹ := by
  rw [← hμ, ← RCLike.ofReal_inv, RCLike.ofReal_re, RCLike.ofReal_re]

/-- The spectral norm of a Hermitian matrix is the largest modulus of an eigenvalue. Let
$A \in \mathbb{K}^{n \times n}$ be Hermitian and let $M \in \mathbb{R}$. Suppose that every
eigenvalue $\mu$ of $A$ satisfies $|\mu| \le M$, and that some eigenvalue $\mu$ of $A$ satisfies
$|\mu| = M$. Then
$$\|A\|_2 = M.$$

The eigenvalues are those of the operator `Matrix.toEuclideanLin A`, and $|\mu|$ is written
`|RCLike.re μ|`, which is the modulus because $\mu$ is real
(`Matrix.IsHermitian.ofReal_re_of_hasEigenvalue`). The upper bound comes from
`ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` and the lower bound from
`ContinuousLinearMap.rayleighQuotient_le_norm` at an eigenvector. -/
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

/-- The eigenvalues of the inverse are the reciprocals of the eigenvalues. Let
$A \in \mathbb{K}^{n \times n}$ be invertible and let $\mu \in \mathbb{K}$. Then $\mu$ is an
eigenvalue of $A^{-1}$ if and only if $\mu^{-1}$ is an eigenvalue of $A$.

Since $A$ is invertible, $0$ is an eigenvalue of neither $A$ nor $A^{-1}$, so the statement
needs no condition on $\mu$. In Lean, $\mu^{-1}$ is $0$ at $\mu = 0$, and both sides are then
false. -/
theorem hasEigenvalue_toEuclideanLin_inv_iff (hA : IsUnit A) (μ : 𝕜) :
    Module.End.HasEigenvalue (toEuclideanLin A⁻¹) μ ↔
      Module.End.HasEigenvalue (toEuclideanLin A) μ⁻¹ := by
  obtain ⟨u, rfl⟩ := hA
  rw [hasEigenvalue_toEuclideanLin_iff, hasEigenvalue_toEuclideanLin_iff, ← coe_units_inv,
    ← spectrum.map_inv u, Set.mem_inv]

/-- The spectral norm of the inverse of a Hermitian matrix is the reciprocal of the smallest modulus
of an eigenvalue. Let $A \in \mathbb{K}^{n \times n}$ be Hermitian and let $m > 0$. Suppose that
every eigenvalue $\mu$ of $A$ satisfies $|\mu| \ge m$, and that some eigenvalue $\mu$ of $A$
satisfies $|\mu| = m$. Then
$$\|A^{-1}\|_2 = m^{-1}.$$

The condition $m > 0$ makes $A$ invertible. The eigenvalues and the modulus are encoded as in
`Matrix.IsHermitian.l2_opNorm_eq`. -/
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

/-- The spectral norm of a power of a Hermitian matrix is the power of the spectral norm. Let
$A \in \mathbb{K}^{n \times n}$ be Hermitian and let $m \ne 0$ be a natural number. Then
$$\|A^m\|_2 = \|A\|_2^m.$$

This is the C⋆-identity `IsSelfAdjoint.norm_pow` in the C⋆-ring of $n \times n$ matrices with
the spectral norm. The exponent $m = 0$ is excluded because $\|I\|_2 = 0 \ne 1$ when $n = 0$. -/
theorem IsHermitian.l2_opNorm_pow (hA : A.IsHermitian) {m : ℕ} (hm : m ≠ 0) :
    ‖A ^ m‖ = ‖A‖ ^ m :=
  hA.isSelfAdjoint.norm_pow hm

/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian and let $m \ne 0$ be a natural number. Then
$$\|A^m\|_2^{1/m} = \|A\|_2,$$
so the sequence $\|A^m\|_2^{1/m}$ of Gelfand's formula is constant for a Hermitian matrix.

This is the root form of `Matrix.IsHermitian.l2_opNorm_pow`. -/
theorem IsHermitian.l2_opNorm_pow_rpow (hA : A.IsHermitian) {m : ℕ} (hm : m ≠ 0) :
    ‖A ^ m‖ ^ (1 / m : ℝ) = ‖A‖ := by
  rw [hA.l2_opNorm_pow hm, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    mul_one_div_cancel (Nat.cast_ne_zero.2 hm), Real.rpow_one]

/-- The spectral norm of a real symmetric matrix is its spectral radius. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric. Then
$$\|A\|_2 = \rho(A),$$
where $\rho(A)$ is the spectral radius of $A$ as a complex matrix.

The spectral radius is `Matrix.complexSpectralRadius`, a value in $[0, \infty]$, read as a real
number. Complexification preserves the norm (`Matrix.l2_opNorm_complexify`) and the Hermitian
property, and in the C⋆-algebra of complex $n \times n$ matrices the norm of a self-adjoint
element is its spectral radius (`IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm`). Together
with `Matrix.IsHermitian.l2_opNorm_pow` this gives $\|A^m\|_2 = \rho(A)^m$ for every $m$, the
symmetric case of [quarteroni2000numerical], (4.5). -/
theorem l2_opNorm_eq_complexSpectralRadius_of_isHermitian {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : ‖A‖ = (complexSpectralRadius A).toReal := by
  rw [← l2_opNorm_complexify, complexSpectralRadius]
  exact (IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm
    ((isHermitian_complexify_iff A).mpr hA).isSelfAdjoint).symm

/-- Let $A \in \mathbb{R}^{n \times n}$ and let $M \ge 0$. Suppose that the operator of $A$ is
symmetric and that its quadratic form satisfies $-M \|x\|^2 \le x^T A x \le M \|x\|^2$ for all
$x$. Then the operator norm of $A$ on $\mathbb{R}^n$ with the Euclidean norm is at most $M$.

The hypothesis is `LinearMap.IsSymmetricBoundedBy (-M) M` for `Matrix.toEuclideanLin A`, and the
conclusion is stated for `Matrix.toEuclideanCLM A`. This is one half of
`Matrix.IsHermitian.l2_opNorm_eq`, through Rayleigh quotients
(`ContinuousLinearMap.norm_le_of_isSymmetricBoundedBy`). -/
theorem norm_toEuclideanCLM_le_of_isSymmetricBoundedBy {A : Matrix n n ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : (toEuclideanLin A).IsSymmetricBoundedBy (-M) M) :
    ‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ M := by
  rw [l2_opNorm_toEuclideanCLM, l2_opNorm_eq_norm_toEuclideanLin]
  exact ContinuousLinearMap.norm_le_of_isSymmetricBoundedBy hM hb

/-! ### Submatrices -/

section Submatrix

omit [DecidableEq n] in
/-- Selecting rows and columns preserves an operator bound in the $\ell^p$ norm. Let
$1 \le p \le \infty$, let $B \in \mathbb{K}^{m \times n}$, and let $C \in \mathbb{R}$ satisfy
$\|B y\|_p \le C \|y\|_p$ for all $y \in \mathbb{K}^n$. Let $f : m' \to m$ and $g : n' \to n$ be
injective, and let $B[f, g]$ be the submatrix with entries $B_{f(i), g(j)}$. Then
$\|B[f, g] x\|_p \le C \|x\|_p$ for all $x \in \mathbb{K}^{n'}$.

The proof applies $B$ to $x$ extended by zero along $g$ (`PiLp.norm_toLp_extend`) and drops the
coordinates outside the range of $f$ (`PiLp.norm_toLp_comp_le`). The submatrix is
`B.submatrix f g`. The result is used by `Matrix.l2_opNorm_submatrix_le` and by its induced
$p$-norm version `Matrix.lpOpNorm_submatrix_le`. -/
theorem norm_toLp_submatrix_mulVec_le (p : ENNReal) [Fact (1 ≤ p)] {m m' n' : Type*} [Fintype m]
    [Fintype m'] [Fintype n'] {B : Matrix m n 𝕜} {f : m' → m}
    (hf : Function.Injective f) {g : n' → n} (hg : Function.Injective g) {C : ℝ}
    (hB : ∀ y : n → 𝕜, ‖(WithLp.toLp p (B *ᵥ y) : PiLp p fun _ : m => 𝕜)‖
      ≤ C * ‖(WithLp.toLp p y : PiLp p fun _ : n => 𝕜)‖) (x : n' → 𝕜) :
    ‖(WithLp.toLp p (B.submatrix f g *ᵥ x) : PiLp p fun _ : m' => 𝕜)‖
      ≤ C * ‖(WithLp.toLp p x : PiLp p fun _ : n' => 𝕜)‖ := by
  classical
  rw [submatrix_mulVec_eq_comp_mulVec_extend B f hg]
  calc ‖(WithLp.toLp p ((B *ᵥ Function.extend g x 0) ∘ f) : PiLp p fun _ : m' => 𝕜)‖
      ≤ ‖(WithLp.toLp p (B *ᵥ Function.extend g x 0) : PiLp p fun _ : m => 𝕜)‖ :=
        PiLp.norm_toLp_comp_le p hf _
    _ ≤ C * ‖(WithLp.toLp p (Function.extend g x 0) : PiLp p fun _ : n => 𝕜)‖ := hB _
    _ = C * ‖(WithLp.toLp p x : PiLp p fun _ : n' => 𝕜)‖ := by rw [PiLp.norm_toLp_extend p hg]

/-- A submatrix has at most the spectral norm of the matrix. Let $B \in \mathbb{K}^{m \times n}$,
and let $f : m' \to m$ and $g : n' \to n$ be injective. Then the submatrix $B[f, g]$ with
entries $B_{f(i), g(j)}$ satisfies
$$\|B[f, g]\|_2 \le \|B\|_2.$$

This is [golub2013matrix], (2.3.13), at $p = 2$. The submatrix is `B.submatrix f g`, and the
proof is `Matrix.norm_toLp_submatrix_mulVec_le`. -/
theorem l2_opNorm_submatrix_le {m m' n' : Type*} [Fintype m] [Fintype m'] [Fintype n']
    [DecidableEq n'] (B : Matrix m n 𝕜) {f : m' → m} (hf : Function.Injective f) {g : n' → n}
    (hg : Function.Injective g) : ‖B.submatrix f g‖ ≤ ‖B‖ := by
  rw [l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x =>
    norm_toLp_submatrix_mulVec_le 2 hf hg (C := ‖B‖)
      (fun y => l2_opNorm_mulVec B (WithLp.toLp 2 y)) (WithLp.ofLp x)

/-- Reindexing does not change the spectral norm: for $B \in \mathbb{K}^{m \times n}$ and bijections
$e : m' \to m$ and $f : n' \to n$, the matrix with entries $B_{e(i), f(j)}$ has the spectral
norm $\|B\|_2$. -/
theorem l2_opNorm_submatrix_equiv {m m' n' : Type*} [Fintype m] [Fintype m'] [Fintype n']
    [DecidableEq n'] (B : Matrix m n 𝕜) (e : m' ≃ m) (f : n' ≃ n) : ‖B.submatrix e f‖ = ‖B‖ := by
  refine le_antisymm (l2_opNorm_submatrix_le B e.injective f.injective) ?_
  have h := l2_opNorm_submatrix_le (B.submatrix e f) e.symm.injective f.symm.injective
  rwa [submatrix_submatrix, e.self_comp_symm, f.self_comp_symm, submatrix_id_id] at h

end Submatrix

/-! ### Rank-one matrices and bilinear forms -/

section RankOne

/-- The spectral norm of a rank-one matrix: for $u \in \mathbb{K}^m$ and $w \in \mathbb{K}^n$,
$$\|u w^T\|_2 = \|u\|_2 \|w\|_2.$$

The matrix $u w^T$ is `Matrix.vecMulVec u w`, without complex conjugation. Its operator is
$z \mapsto \langle \bar w, z \rangle u$, of norm at most $\|\bar w\| \|u\|$ by the
Cauchy–Schwarz inequality, with equality at $z = \bar w$. -/
theorem l2_opNorm_vecMulVec {m : Type*} [Fintype m] (u : m → 𝕜) (w : n → 𝕜) :
    ‖vecMulVec u w‖ = ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 m)‖ *
      ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 n)‖ := by
  have hW : ‖(WithLp.toLp 2 (star w) : EuclideanSpace 𝕜 n)‖ =
      ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 n)‖ := by
    simp [EuclideanSpace.norm_eq]
  have happ : ∀ z : EuclideanSpace 𝕜 n,
      (WithLp.toLp 2 (vecMulVec u w *ᵥ WithLp.ofLp z) : EuclideanSpace 𝕜 m)
        = inner 𝕜 (WithLp.toLp 2 (star w) : EuclideanSpace 𝕜 n) z •
          (WithLp.toLp 2 u : EuclideanSpace 𝕜 m) := by
    intro z
    rw [vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul, WithLp.toLp_smul,
      EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_star, dotProduct_comm]
  refine le_antisymm ?_ ?_
  · rw [l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    change ‖(WithLp.toLp 2 (vecMulVec u w *ᵥ WithLp.ofLp z) : EuclideanSpace 𝕜 m)‖ ≤ _
    rw [happ, norm_smul, ← hW]
    calc ‖inner 𝕜 (WithLp.toLp 2 (star w) : EuclideanSpace 𝕜 n) z‖ *
          ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 m)‖
        ≤ ‖(WithLp.toLp 2 (star w) : EuclideanSpace 𝕜 n)‖ * ‖z‖ *
          ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 m)‖ :=
          mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
      _ = _ := by ring
  · set W : EuclideanSpace 𝕜 n := WithLp.toLp 2 (star w)
    have h := l2_opNorm_mulVec (vecMulVec u w) W
    change ‖(WithLp.toLp 2 (vecMulVec u w *ᵥ WithLp.ofLp W) : EuclideanSpace 𝕜 m)‖ ≤ _ at h
    rw [happ, inner_self_eq_norm_sq_to_K, norm_smul, norm_pow, RCLike.norm_ofReal,
      abs_norm] at h
    rw [← hW]
    rcases eq_or_ne ‖W‖ 0 with h0 | h0
    · rw [h0, mul_zero]
      exact norm_nonneg _
    · have hpos : 0 < ‖W‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith [norm_nonneg (vecMulVec u w), norm_nonneg (WithLp.toLp 2 u : EuclideanSpace 𝕜 m)]

/-- For $M \in \mathbb{R}^{m \times n}$, $x \in \mathbb{R}^m$ and $y \in \mathbb{R}^n$,
$x^T M y \le \|M\|_2 \|x\|_2 \|y\|_2$. -/
theorem dotProduct_mulVec_le_l2_opNorm {m : Type*} [Fintype m] (M : Matrix m n ℝ) (x : m → ℝ)
    (y : n → ℝ) :
    x ⬝ᵥ (M *ᵥ y) ≤ ‖M‖ * (‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖ *
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖) := by
  have h1 : x ⬝ᵥ (M *ᵥ y)
      = inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ m) (WithLp.toLp 2 (M *ᵥ y)) := by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  have h2 : ‖(WithLp.toLp 2 (M *ᵥ y) : EuclideanSpace ℝ m)‖
      ≤ ‖M‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖ :=
    l2_opNorm_mulVec M (WithLp.toLp 2 y)
  rw [h1]
  calc _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖ *
        ‖(WithLp.toLp 2 (M *ᵥ y) : EuclideanSpace ℝ m)‖ := real_inner_le_norm _ _
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖ *
        (‖M‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = _ := by ring

omit [DecidableEq n] in
/-- The **Cauchy–Schwarz inequality** for a positive semidefinite real quadratic form: for a
positive semidefinite $T \in \mathbb{R}^{n \times n}$ and $x, y \in \mathbb{R}^n$,
$$(x^T T y)^2 \le (x^T T x)(y^T T y).$$
-/
theorem PosSemidef.sq_dotProduct_mulVec_le {T : Matrix n n ℝ} (hT : T.PosSemidef) (x y : n → ℝ) :
    (x ⬝ᵥ (T *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (T *ᵥ x)) * (y ⬝ᵥ (T *ᵥ y)) := by
  have hTt : Tᵀ = T := by
    have := hT.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hsymm : y ⬝ᵥ (T *ᵥ x) = x ⬝ᵥ (T *ᵥ y) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hTt, dotProduct_comm]
  have h := discrim_le_zero (a := y ⬝ᵥ (T *ᵥ y)) (b := 2 * (x ⬝ᵥ (T *ᵥ y)))
    (c := x ⬝ᵥ (T *ᵥ x)) fun t => by
      have := hT.dotProduct_mulVec_nonneg (x + t • y)
      simp only [star_trivial, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, hsymm] at this
      linarith
  rw [discrim] at h
  nlinarith [h]

end RankOne

/-! ### Block matrices -/

section Blocks

/-- Let $\mu, \gamma, \delta \ge 0$ and let $\lambda = (\mu + \delta + \sqrt{(\mu - \delta)^2 + 4
\gamma^2}) / 2$, the largest eigenvalue of $\begin{bmatrix} \mu & \gamma \\ \gamma & \delta
\end{bmatrix}$; then $(\mu a + \gamma b)^2 + (\gamma a + \delta b)^2 \le \lambda^2 (a^2 + b^2)$
for all real $a, b$. -/
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

/-- The spectral norm of a $2 \times 2$ block matrix, bounded by the norms of its blocks (**Kahan's
lemma**). Let $E \in \mathbb{K}^{m_1 \times n_1}$, $C \in \mathbb{K}^{m_1 \times n_2}$,
$C' \in \mathbb{K}^{m_2 \times n_1}$ and $D \in \mathbb{K}^{m_2 \times n_2}$, and let
$\mu, \gamma, \delta \in \mathbb{R}$ satisfy $\|E\|_2 \le \mu$, $\|C\|_2 \le \gamma$,
$\|C'\|_2 \le \gamma$ and $\|D\|_2 \le \delta$. Then
$$\left\| \begin{bmatrix} E & C \\ C' & D \end{bmatrix} \right\|_2 \le \frac{\mu + \delta +
  \sqrt{(\mu - \delta)^2 + 4 \gamma^2}}{2},$$
and the right side is the largest eigenvalue of $\begin{bmatrix} \mu & \gamma \\ \gamma & \delta
\end{bmatrix}$.

[golub2013matrix], Lemma 10.3.1, states this for a Hermitian matrix, with $C' = C^H$. The proof
needs no symmetry. For $z = (x, y)$ the proof bounds the image blockwise: $\|M z\|^2 \le (\mu
\|x\| + \gamma \|y\|)^2 + (\gamma \|x\| + \delta \|y\|)^2 \le \lambda^2 \|z\|^2$. -/
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
    rw [← EuclideanSpace.norm_toLp_sumElim_sq, ← hz, WithLp.toLp_ofLp]
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
    rw [hz, fromBlocks_mulVec, EuclideanSpace.norm_toLp_sumElim_sq, mul_pow, hnz]
    refine le_trans ?_ (sq_add_sq_le_of_blockBound hμ hγ hδ)
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2)
      (pow_le_pow_left₀ (norm_nonneg _) h2 2)
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hMz

/-- **Kahan's lemma** for a block matrix of Hermitian shape ([golub2013matrix], Lemma 10.3.1). Let
$E \in \mathbb{K}^{m_1 \times m_1}$, $C \in \mathbb{K}^{m_1 \times m_2}$ and
$D \in \mathbb{K}^{m_2 \times m_2}$, and let $\mu, \gamma, \delta \in \mathbb{R}$ satisfy
$\|E\|_2 \le \mu$, $\|C\|_2 \le \gamma$ and $\|D\|_2 \le \delta$. Then
$$\left\| \begin{bmatrix} E & C \\ C^H & D \end{bmatrix} \right\|_2 \le \frac{\mu + \delta +
  \sqrt{(\mu - \delta)^2 + 4 \gamma^2}}{2}.$$

This is the case $C' = C^H$ of `Matrix.l2_opNorm_fromBlocks_le`, because $\|C^H\|_2 = \|C\|_2$.
The matrices $E$ and $D$ need not be Hermitian. -/
theorem l2_opNorm_fromBlocks_conjTranspose_le {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂] {E : Matrix m₁ m₁ 𝕜} {C : Matrix m₁ m₂ 𝕜}
    {D : Matrix m₂ m₂ 𝕜}
    {μ γ δ : ℝ} (hE : ‖E‖ ≤ μ) (hC : ‖C‖ ≤ γ) (hD : ‖D‖ ≤ δ) :
    ‖fromBlocks E C Cᴴ D‖ ≤ (μ + δ + √((μ - δ) ^ 2 + 4 * γ ^ 2)) / 2 :=
  l2_opNorm_fromBlocks_le hE hC (by rwa [l2_opNorm_conjTranspose]) hD

end Blocks

end Matrix
