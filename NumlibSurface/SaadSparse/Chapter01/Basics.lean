/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Numlib.Analysis.Matrix.OperatorNorm
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Sections 1.1–1.6: Matrices, eigenvalues, types of matrices, norms and subspaces

This module formalizes §1.1–1.6 of [saad2003iterative]: square matrices and their determinants,
eigenvalues and the spectrum, the standard classes of matrices, inner products and vector norms,
matrix norms, and subspaces with the range and the kernel. For $A \in \mathbb{C}^{n \times n}$, a
scalar $\lambda$ is an eigenvalue when $Au = \lambda u$ for some $u \neq 0$, and the set of
eigenvalues is the spectrum $\sigma(A)$. The module proves that $A$ is nonsingular exactly when it
is invertible, that the trace and the determinant are the sum and the product of the eigenvalues,
that unitary matrices preserve the inner product, the Cauchy–Schwarz inequality, the formulas for
$\|A\|_\infty$, $\|A\|_1$, $\|A\|_2$ and $\|A\|_F$, that the spectral radius is not a norm, and the
decomposition $\mathbb{C}^n = \operatorname{Ran}(A) \oplus \operatorname{Null}(A^H)$.

Almost all of these sections is Mathlib restated in the notation of the book, so the module is thin.
The proofs use Mathlib and the backbone module `Numlib.Analysis.Matrix.OperatorNorm`.

## Main definitions

* Definition 1.1, `SaadSparse.Chapter01.definition_1_1`: $\lambda$ is an eigenvalue of $A$, that is
  $Au = \lambda u$ for some $u \neq 0$, if and only if $\lambda$ is in Mathlib's spectrum of $A$.

## Main results

* Proposition 1.2, `SaadSparse.Chapter01.proposition_1_2`: $\det A \neq 0$ if and only if $A$ has a
  two-sided inverse.
* §1.2, `SaadSparse.Chapter01.trace_eq_sum_eigenvalues`: the trace and the determinant of a complex
  matrix are the sum and the product of its eigenvalues, counted with algebraic multiplicity.
* Proposition 1.3, `SaadSparse.Chapter01.proposition_1_3`: $\sigma(A^H) = \overline{\sigma(A)}$, and
  an eigenvector of $A^H$ for $\bar\mu$ is a left eigenvector of $A$ for $\mu$.
* Proposition 1.4, `SaadSparse.Chapter01.proposition_1_4`: a unitary matrix preserves the Euclidean
  inner product and the Euclidean norm.
* Equation (1.2), `SaadSparse.Chapter01.equation_1_2`: the Cauchy–Schwarz inequality
  $|(x, y)| \le \|x\| \|y\|$.
* Equations (1.4)–(1.5), `SaadSparse.Chapter01.equation_1_5`: $(Ax, y) = (x, A^H y)$.
* Equations (1.13)–(1.14), `SaadSparse.Chapter01.equation_1_14`: $\|A\|_\infty$ is the largest
  absolute row sum, and $\|A\|_1 = \|A^T\|_\infty$.
* Equation (1.15), `SaadSparse.Chapter01.equation_1_15`: $\|A\|_2^2 = \rho(A^H A) = \rho(A A^H)$.
* Equation (1.15), `SaadSparse.Chapter01.spectralRadius_eq_l2_opNNNorm_of_isHermitian`: for a
  Hermitian matrix, $\rho(A) = \|A\|_2$.
* Equations (1.12) and (1.16), `SaadSparse.Chapter01.equation_1_16`: $\|A\|_F^2 = \sum_{i,j}
  |a_{ij}|^2 = \operatorname{tr}(A^H A) = \operatorname{tr}(A A^H)$.
* Example 1.1, `SaadSparse.Chapter01.example_1_1`: the spectral radius vanishes on a nonzero matrix
  and is not subadditive, so it is not a matrix norm.
* Equation (1.18), `SaadSparse.Chapter01.equation_1_18`: $\mathbb{C}^n = \operatorname{Ran}(A)
  \oplus \operatorname{Null}(A^H)$, and the same with $A$ and $A^H$ exchanged.

## Conventions

* The book calls a matrix *orthogonal* when $Q^H Q$ is diagonal, not necessarily the identity. No
  other source uses this notion. The library uses the standard notion of a unitary matrix,
  `Matrix.unitaryGroup`, which is what Proposition 1.4 is about.

## Implementation notes

* The following items of the book have no declaration of their own, because a Mathlib or backbone
  declaration is the statement: the definitions of §1.1 and §1.3 (`Matrix.transpose`,
  `Matrix.conjTranspose`, `Matrix.IsSymm`, `Matrix.IsHermitian`, `IsStarNormal`, `Matrix.IsDiag`,
  `Matrix.BlockTriangular`, `Matrix.unitaryGroup`, and `Matrix.IsTridiagonal` and
  `Matrix.IsUpperHessenberg` of `Numlib.LinearAlgebra.Matrix.Hessenberg`); the properties of the
  determinant in §1.2; the axioms of inner products and norms in §1.4 (`InnerProductSpace`, `Norm`);
  the $p$-norms (1.6) (`PiLp`); and all of §1.6 (`Submodule.span`, `LinearMap.range`,
  `LinearMap.ker`, `IsCompl` and `Module.End.eigenspace`; an eigenspace is invariant by
  `Module.End.mem_eigenspace_iff`).
* The matrix norms of §1.5 are Mathlib's scoped instances, one for each norm, opened for each
  declaration. The instances `Matrix.Norms.Operator`, `Matrix.Norms.L2Operator` and
  `Matrix.Norms.Frobenius` give the norms $\|\cdot\|_\infty$, $\|\cdot\|_2$ and $\|\cdot\|_F$.
* The other induced norms $\|\cdot\|_p$ of (1.7) are `Matrix.lpOpNorm p`, the operator norm of
  `Matrix.lpCLM p A` on `PiLp p`. The column-sum formula (1.13) for $\|\cdot\|_1$ is
  `Matrix.lpOpNorm_one_eq_sup_sum_norm`. The remark of §1.5 that a consistent norm dominates the
  spectral radius is `Matrix.complexSpectralRadius_le_lpOpNorm`. §1.13.2 defines the condition
  number $\kappa_p(A) = \|A\|_p \|A^{-1}\|_p$ (`Matrix.condNumberLp`) from these norms.

## Deviations from the source

* **Propositions 1.2 and 1.4, Equations (1.2) and (1.5)** (generalization). The book uses complex
  scalars. The declarations also cover real scalars. See `SaadSparse.Chapter01.proposition_1_2`,
  `SaadSparse.Chapter01.proposition_1_4`, `SaadSparse.Chapter01.equation_1_2` and
  `SaadSparse.Chapter01.equation_1_5`.
* **§1.2, trace as a sum of eigenvalues** (generalization). The theorem also identifies the
  determinant as the product of the same eigenvalues. See
  `SaadSparse.Chapter01.trace_eq_sum_eigenvalues`.
* **Proposition 1.3** (generalization). The book gives one implication for the eigenvalues. The
  theorem identifies the two spectra by conjugation. See `SaadSparse.Chapter01.proposition_1_3`.
* **Equations (1.12)–(1.16), the norm formulas** (reading). The book states the formulas for
  rectangular matrices. The surface declarations use square matrices. See
  `SaadSparse.Chapter01.equation_1_14`, `SaadSparse.Chapter01.equation_1_15` and
  `SaadSparse.Chapter01.equation_1_16`.
* **Equation (1.18)** (typo). The book prints $\mathbb{C}^n = \operatorname{Ran}(A) \oplus
  \operatorname{Null}(A^T)$ in a complex setting, where $A^H$ is meant. See
  `SaadSparse.Chapter01.equation_1_18`.
* **Equation (1.18)** (reading). The book uses rectangular matrices. The declaration uses square
  matrices. See `SaadSparse.Chapter01.equation_1_18`.
-/

open Matrix Finset Polynomial

open scoped SaadSparse ENNReal NNReal

namespace SaadSparse.Chapter01

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ### §1.1–1.2 Matrices, determinants and eigenvalues -/

/-- **Proposition 1.2** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. Then $\det A \neq 0$ if and only if there is a
matrix $B$ with $AB = I$ and $BA = I$.

**Generalization.** The book works over $\mathbb{C}$ by default. The determinant and inverse
criterion also holds over $\mathbb{R}$.

The inverse is then `A⁻¹`, by `Matrix.nonsing_inv_mul` and `Matrix.mul_nonsing_inv`. -/
theorem proposition_1_2 (A : Matrix (Fin n) (Fin n) 𝕜) :
    A.det ≠ 0 ↔ ∃ B, A * B = 1 ∧ B * A = 1 := by
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det, isUnit_iff_exists]

/-- **Section 1.2** of [saad2003iterative], trace and determinant. Let
$A \in \mathbb{C}^{n \times n}$. The trace of $A$ is the sum, and the determinant of $A$ is the
product, of the roots of the characteristic polynomial of $A$, counted with multiplicity:
$$\operatorname{tr} A = \sum_i \lambda_i, \qquad \det A = \prod_i \lambda_i.$$

**Generalization.** The source states the trace formula in this passage. The theorem adds the
determinant formula, which follows by taking the constant term of the characteristic polynomial.

The roots are `A.charpoly.roots`, a multiset that counts each eigenvalue with its algebraic
multiplicity. -/
theorem trace_eq_sum_eigenvalues (A : Matrix (Fin n) (Fin n) ℂ) :
    A.trace = A.charpoly.roots.sum ∧ A.det = A.charpoly.roots.prod :=
  ⟨A.trace_eq_sum_roots_charpoly, A.det_eq_prod_roots_charpoly⟩

/-- **Definition 1.1** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$. A scalar
$\lambda \in \mathbb{C}$ is an **eigenvalue** of $A$ if $Au = \lambda u$ for some nonzero
$u \in \mathbb{C}^n$, and such a $u$ is an **eigenvector** of $A$ associated with $\lambda$. The
set of eigenvalues is the **spectrum** $\sigma(A)$. The theorem states that $\lambda$ is an
eigenvalue in this sense if and only if $\lambda$ lies in the spectrum of $A$ in the sense of
Mathlib, `spectrum ℂ A`.

The book's $\sigma(A)$ is Mathlib's `spectrum ℂ A`. The statement "$u$ is an eigenvector of $A$
for $\lambda$" is `u ≠ 0` together with `u ∈ Module.End.eigenspace (Matrix.toEuclideanLin A) λ`,
which `Module.End.mem_eigenspace_iff` unfolds to $Au = \lambda u$. The rest of the library uses
`spectrum ℂ A` for the set of eigenvalues. -/
theorem definition_1_1 (A : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    (∃ u : EuclideanSpace ℂ (Fin n), u ≠ 0 ∧ (A ⬝ u) = l • u) ↔ l ∈ spectrum ℂ A := by
  rw [← Matrix.hasEigenvalue_toEuclideanLin_iff]
  constructor
  · rintro ⟨u, hu, h⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (x := u) ⟨Module.End.mem_eigenspace_iff.2 h, hu⟩
  · intro h
    obtain ⟨u, hmem, hu⟩ := h.exists_hasEigenvector
    exact ⟨u, hu, Module.End.mem_eigenspace_iff.1 hmem⟩

/-- **Proposition 1.3** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$. Then the
spectrum of $A^H$ is the complex conjugate of the spectrum of $A$,
$\sigma(A^H) = \{\bar\mu : \mu \in \sigma(A)\}$. Moreover, for every $\mu \in \mathbb{C}$ and
$v \in \mathbb{C}^n$, if $A^H v = \bar\mu v$, then $v$ is a **left eigenvector** of $A$ for
$\mu$:
$$v^H A = \mu v^H.$$

**Generalization.** The book says that each eigenvalue of $A$ gives a conjugate eigenvalue of
$A^H$. The theorem also gives the converse, since $(A^H)^H = A$.

The spectra correspond under conjugation because the characteristic polynomial of $A^H$ is the
conjugate of the characteristic polynomial of $A$. The row vector $v^H A$ is `star v ᵥ* A`. -/
theorem proposition_1_3 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ Aᴴ = star '' spectrum ℂ A ∧
      ∀ (μ : ℂ) (v : Fin n → ℂ), Aᴴ *ᵥ v = star μ • v → star v ᵥ* A = μ • star v := by
  have hunit : ∀ M : Matrix (Fin n) (Fin n) ℂ, IsUnit Mᴴ ↔ IsUnit M := by
    intro M
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    simp [isUnit_iff_ne_zero]
  have halg : ∀ μ : ℂ,
      (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (star μ))ᴴ =
        algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ := by
    intro μ
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.algebraMap_eq_diagonal, h, eq_comm]
  have hspec : ∀ μ : ℂ, μ ∈ spectrum ℂ Aᴴ ↔ star μ ∈ spectrum ℂ A := by
    intro μ
    simp only [spectrum.mem_iff, not_iff_not]
    rw [← hunit (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (star μ) - A),
      Matrix.conjTranspose_sub, halg μ]
  refine ⟨Set.ext fun μ => ?_, fun μ v hv => ?_⟩
  · rw [hspec μ, Set.mem_image]
    exact ⟨fun h => ⟨star μ, h, star_star μ⟩, fun ⟨ν, hν, h⟩ => by
      rw [← h, star_star]; exact hν⟩
  · have h := congrArg star hv
    rwa [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, star_smul, star_star] at h

/-! ### §1.3 Types of matrices: unitary matrices -/

/-- **Proposition 1.4** of [saad2003iterative], with its corollary. Let
$Q \in \mathbb{K}^{n \times n}$ be unitary, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$.
Then for all $x, y \in \mathbb{K}^n$,
$$(Qx, Qy) = (x, y) \quad \text{and} \quad \|Qx\|_2 = \|x\|_2.$$

**Generalization.** The book gives the complex identity and deduces preservation of the norm.
The theorem covers those facts over both scalar fields.

A unitary matrix is an element of `Matrix.unitaryGroup (Fin n) 𝕜`. The book's inner product
$(x, y)$ is `inner 𝕜 y x`. -/
theorem proposition_1_4 {Q : Matrix (Fin n) (Fin n) 𝕜}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 (Q ⬝ y) (Q ⬝ x) = inner 𝕜 y x ∧ ‖Q ⬝ x‖ = ‖x‖ :=
  ⟨Matrix.inner_toLp_mulVec_of_mem_unitaryGroup hQ _ _,
    Matrix.norm_toLp_mulVec_of_mem_unitaryGroup hQ _⟩

/-! ### §1.4 Inner products and vector norms -/

/-- **Equation (1.2)** of [saad2003iterative] (Cauchy–Schwarz inequality). Let $E$ be an inner
product space over $\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. Then for
all $x, y \in E$,
$$|(x, y)| \le \|x\| \|y\|.$$

**Generalization.** The book states the inequality for complex inner products. This theorem
also covers real inner products, with the same induced norm. -/
theorem equation_1_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ‖(inner 𝕜 y x : 𝕜)‖ ≤ ‖x‖ * ‖y‖ := by
  rw [mul_comm]
  exact norm_inner_le_norm (𝕜 := 𝕜) y x

/-- **Equations (1.4)–(1.5)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. For the Euclidean inner product $(x, y) = y^H x$
and all $x, y \in \mathbb{K}^n$,
$$(Ax, y) = (x, A^H y).$$

**Generalization.** The book states the identity for complex matrices. The declaration includes
real matrices, for which the conjugate transpose is the transpose.

The formula $(x, y) = y^H x$ is `EuclideanSpace.inner_eq_star_dotProduct`. The book's $(x, y)$
is `inner 𝕜 y x`. -/
theorem equation_1_5 (A : Matrix (Fin n) (Fin n) 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 y (A ⬝ x) = inner 𝕜 (Aᴴ ⬝ y) x := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_inner_left _ _ _).symm

/-! ### §1.5 Matrix norms -/

section MatrixNorms

open scoped Matrix.Norms.Operator

/-- **Equations (1.13)–(1.14)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. The norm $\|A\|_\infty$ induced by the vector
$\infty$-norm is the largest absolute row sum, and the induced norm $\|A\|_1$ equals
$\|A^T\|_\infty$:
$$\|A\|_\infty = \max_i \sum_j |a_{ij}|, \qquad \|A\|_1 = \|A^T\|_\infty.$$
Together, $\|A\|_1$ is the largest absolute column sum. For $n = 0$ the maximum is $0$.

**Reading.** The book states both formulas for rectangular matrices. The declaration specializes
them to square matrices and takes an empty maximum to be zero.

The norm $\|\cdot\|_\infty$ is the scoped instance `Matrix.Norms.Operator`, and $\|\cdot\|_1$ is
`Matrix.lpOpNorm 1`. The proof uses the column-sum formula
`Matrix.lpOpNorm_one_eq_sup_sum_norm`. -/
theorem equation_1_14 (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A‖ = ↑(univ.sup fun i => ∑ j, ‖A i j‖₊) ∧ Matrix.lpOpNorm 1 A = ‖Aᵀ‖ := by
  refine ⟨Matrix.linfty_opNorm_def A, ?_⟩
  rw [Matrix.lpOpNorm_one_eq_sup_sum_norm, Matrix.linfty_opNorm_def]
  rfl

end MatrixNorms

section L2

open scoped Matrix.Norms.L2Operator

/-- **Equation (1.15)** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$. Then
$$\rho(A^H A) = \|A\|_2^2 = \rho(A A^H).$$
The square roots of the eigenvalues of $A^H A$ are the singular values of $A$, so $\|A\|_2$ is
the largest singular value of $A$.

**Reading.** The book allows distinct row and column dimensions. The declaration uses a square
matrix, so both products have the same dimension.

The norm $\|\cdot\|_2$ is the scoped instance `Matrix.Norms.L2Operator`, and $\rho$ is Mathlib's
`spectralRadius ℂ`, with values in $[0, \infty]$. The matrices $A^H A$ and $A A^H$ are
self-adjoint, so their spectral radii are their norms, and the C*-identity turns these norms
into $\|A\|_2^2$. -/
theorem equation_1_15 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius ℂ (Aᴴ * A) = (‖A‖₊ : ℝ≥0∞) ^ 2 ∧
      spectralRadius ℂ (A * Aᴴ) = (‖A‖₊ : ℝ≥0∞) ^ 2 := by
  have hself : ∀ B : Matrix (Fin n) (Fin n) ℂ, IsSelfAdjoint (Bᴴ * B) := fun B => by
    rw [IsSelfAdjoint, star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hmul : ‖A * Aᴴ‖₊ = ‖A‖₊ * ‖A‖₊ := by
    have h := Matrix.l2_opNNNorm_conjTranspose_mul_self Aᴴ
    rwa [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNNNorm_conjTranspose] at h
  refine ⟨?_, ?_⟩
  · rw [IsSelfAdjoint.spectralRadius_eq_nnnorm (hself A),
      Matrix.l2_opNNNorm_conjTranspose_mul_self, sq]
    norm_cast
  · have h := IsSelfAdjoint.spectralRadius_eq_nnnorm (hself Aᴴ)
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [h, hmul, sq]
    norm_cast

/-- **Equation (1.15)** of [saad2003iterative], the Hermitian case. Let
$A \in \mathbb{C}^{n \times n}$ be Hermitian. Then $\rho(A) = \|A\|_2$. -/
theorem spectralRadius_eq_l2_opNNNorm_of_isHermitian {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) : spectralRadius ℂ A = (‖A‖₊ : ℝ≥0∞) :=
  IsSelfAdjoint.spectralRadius_eq_nnnorm hA

end L2

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Equations (1.12) and (1.16)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. The Frobenius norm satisfies
$$\|A\|_F^2 = \sum_{i,j} |a_{ij}|^2, \qquad \|A\|_F^2 = \operatorname{tr}(A^H A) =
  \operatorname{tr}(A A^H).$$

**Reading.** The source defines and evaluates the Frobenius norm for rectangular matrices. The
declaration states those identities for square matrices.

The norm $\|\cdot\|_F$ is the scoped instance `Matrix.Norms.Frobenius`, and the two trace
identities are stated in $\mathbb{K}$. The Frobenius norm is consistent (Problem P-1.5) by
`Matrix.frobenius_norm_mul`. -/
theorem equation_1_16 (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 ∧
      ((‖A‖ : 𝕜)) ^ 2 = (Aᴴ * A).trace ∧ ((‖A‖ : 𝕜)) ^ 2 = (A * Aᴴ).trace := by
  have hsq : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    norm_num
  have hcast : ((‖A‖ : 𝕜)) ^ 2 = ∑ i, ∑ j, ((‖A i j‖ : 𝕜)) ^ 2 := by
    rw [← RCLike.ofReal_pow, hsq]
    push_cast
    rfl
  have key : ∀ B : Matrix (Fin n) (Fin n) 𝕜,
      (Bᴴ * B).trace = ∑ i, ∑ j, ((‖B j i‖ : 𝕜)) ^ 2 := by
    intro B
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [← starRingEnd_apply, RCLike.conj_mul]
  refine ⟨hsq, ?_, ?_⟩
  · rw [key A, hcast]
    exact Finset.sum_comm
  · have h := key Aᴴ
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [h, hcast]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [Matrix.conjTranspose_apply, norm_star]

end Frobenius

/-- **Example 1.1** of [saad2003iterative]. The spectral radius is not a matrix norm. Let
$$A = \begin{bmatrix} 0 & 1 \\ 0 & 0 \end{bmatrix}.$$
Then $A \neq 0$ and $\rho(A) = 0$. Moreover $\rho(A^T) = 0$, while $\rho(A + A^T) = 1$, so
$\rho$ is not subadditive.

This is why every convergence statement of Chapter 4 is about $\rho$ and not about a norm. The
spectral radius of a real matrix is `Matrix.complexSpectralRadius`. -/
theorem example_1_1 :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 ∧
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).complexSpectralRadius = 0 ∧
      (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).complexSpectralRadius = 0 ∧
      ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) +
        !![0, 0; 1, 0]).complexSpectralRadius = 1 := by
  have hnil : ∀ B : Matrix (Fin 2) (Fin 2) ℝ, B ^ 2 = 0 → B.complexSpectralRadius = 0 := by
    intro B hB
    have h := Matrix.complexSpectralRadius_pow_le B (k := 2) two_ne_zero
    rw [hB, Matrix.complexSpectralRadius_zero, le_zero_iff] at h
    exact pow_eq_zero_iff two_ne_zero |>.mp h
  refine ⟨?_, hnil _ ?_, hnil _ ?_, ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 1
    norm_num at this
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · have hsum : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) + !![0, 0; 1, 0] = !![0, 1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hc : Matrix.complexify (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
        (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hroot : ∀ μ : ℂ, μ ∈ spectrum ℂ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ↔
        μ ^ 2 = 1 := by
      intro μ
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def,
        Matrix.charpoly_fin_two, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      constructor
      · intro h
        linear_combination h
      · intro h
        linear_combination h
    have hnorm : ∀ μ : ℂ, μ ^ 2 = 1 → ‖μ‖₊ = 1 := by
      intro μ hμ
      have h2 : ‖μ‖ ^ 2 = 1 ^ 2 := by rw [← norm_pow, hμ, norm_one, one_pow]
      have h3 : ‖μ‖ = 1 := (pow_left_inj₀ (norm_nonneg μ) zero_le_one two_ne_zero).mp h2
      exact NNReal.eq (by rw [coe_nnnorm, NNReal.coe_one]; exact h3)
    rw [hsum, Matrix.complexSpectralRadius, hc, spectralRadius_eq_of_unital]
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
    · rw [hnorm μ ((hroot μ).mp hμ)]
      simp
    · have h1 : (1 : ℂ) ∈ spectrum ℂ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) :=
        (hroot 1).mpr (one_pow 2)
      calc (1 : ℝ≥0∞) = ((‖(1 : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) := by simp
        _ ≤ _ := le_iSup₂ (f := fun μ (_ : μ ∈ _) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞)) (1 : ℂ) h1

/-! ### §1.6 Subspaces, range and kernel -/

/-- **Equation (1.18)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. Then $\mathbb{K}^n$ is the direct sum of the range
of $A$ and the kernel of $A^H$, and also of the range of $A^H$ and the kernel of $A$:
$$\mathbb{K}^n = \operatorname{Ran}(A) \oplus \operatorname{Null}(A^H) = \operatorname{Ran}(A^H)
  \oplus \operatorname{Null}(A).$$

**Typo.** The book prints $\operatorname{Null}(A^T)$ in a complex setting, where $A^H$ is meant.

**Reading.** The book gives the two decompositions in the row and column ambient spaces of a
rectangular matrix. The declaration uses square matrices, so these spaces have the same dimension.

The direct sums are `IsCompl` of subspaces. The kernel of the adjoint is the orthogonal
complement of the range, and a subspace and its orthogonal complement are complementary. -/
theorem equation_1_18 (A : Matrix (Fin n) (Fin n) 𝕜) :
    IsCompl (LinearMap.range (toEuclideanLin A)) (LinearMap.ker (toEuclideanLin Aᴴ)) ∧
      IsCompl (LinearMap.range (toEuclideanLin Aᴴ)) (LinearMap.ker (toEuclideanLin A)) := by
  have key : ∀ B : Matrix (Fin n) (Fin n) 𝕜,
      IsCompl (LinearMap.range (toEuclideanLin B)) (LinearMap.ker (toEuclideanLin Bᴴ)) := by
    intro B
    have h : (LinearMap.range (toEuclideanLin B))ᗮ = LinearMap.ker (toEuclideanLin Bᴴ) := by
      rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      exact LinearMap.orthogonal_range _
    exact h ▸ Submodule.isCompl_orthogonal _
  refine ⟨key A, ?_⟩
  have := key Aᴴ
  rwa [Matrix.conjTranspose_conjTranspose] at this

end SaadSparse.Chapter01
