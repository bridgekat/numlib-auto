/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Jordan
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Basics

/-!
# Quarteroni, Sacco and Saleri, Section 1.7: Eigenvalues and eigenvectors

This module formalizes §1.7 of [quarteroni2000numerical]. A number $\lambda \in \mathbb{C}$ is an
eigenvalue of $A \in \mathbb{C}^{n \times n}$ if $Ax = \lambda x$ for some $x \neq 0$, and the set
$\sigma(A)$ of the eigenvalues is the spectrum of $A$. The eigenvalues are the roots of the
characteristic polynomial $p_A(\lambda) = \det(A - \lambda I)$, so that $\det A$ and
$\operatorname{tr} A$ are the product and the sum of the eigenvalues. The module states these facts,
the relation between the spectra of $A$, $A^T$ and $A^H$, the Cayley–Hamilton theorem, and the
conjugate pairs of eigenvalues of a real matrix. It defines the spectral radius $\rho(A) =
\max_{\lambda \in \sigma(A)} |\lambda|$ (1.7) and proves its rules under conjugate transposition,
scalar multiplication and powers. It also treats the spectra of block triangular and triangular
matrices, the algebraic and the geometric multiplicity of an eigenvalue, defective matrices, and
invariant subspaces (Definition 1.13).

The proofs use Mathlib's spectrum and characteristic polynomial, and the backbone modules
`Numlib.LinearAlgebra.Matrix.Complexify` (the spectrum of a real matrix),
`Numlib.Analysis.Normed.Algebra.SpectralRadius` and `Numlib.LinearAlgebra.Matrix.Jordan`
(eigenspaces and multiplicities).

## Main definitions

* §1.7, `QuarteroniSaccoSaleri.Chapter01.IsDefective`: a matrix is defective if some eigenvalue has
  a geometric multiplicity smaller than its algebraic multiplicity.
* Definition 1.13, `QuarteroniSaccoSaleri.Chapter01.definition_1_13`: a subspace is invariant under
  $A$ if $A$ maps it into itself; every eigenspace of $A$ is invariant.

## Main results

* §1.7, `QuarteroniSaccoSaleri.Chapter01.mem_spectrum_iff_exists_mulVec_eq_smul`: $\lambda$ is an
  eigenvalue of $A$ if and only if $Ax = \lambda x$ for some $x \neq 0$.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.vecMul_eq_smul_iff_conjTranspose_mulVec`: left eigenvectors
  of $A$ are eigenvectors of $A^H$, and the Rayleigh quotient of an eigenvector is its eigenvalue.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.mem_spectrum_iff_isRoot_charpoly`: the eigenvalues are the
  roots of the characteristic polynomial, which has degree $n$ and $n$ roots.
* Equation (1.6), `QuarteroniSaccoSaleri.Chapter01.equation_1_6`: $\det A$ is the product and
  $\operatorname{tr} A$ is the sum of the eigenvalues.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.spectrum_transpose`: $\sigma(A^T) = \sigma(A)$ and
  $\sigma(A^H) = \overline{\sigma(A)}$.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.star_mem_spectrum_complexify_iff`: the eigenvalues of a
  real matrix occur in conjugate pairs with equal algebraic multiplicity.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.cayleyHamilton`: the Cayley–Hamilton theorem $p_A(A) = 0$.
* Equation (1.7), `QuarteroniSaccoSaleri.Chapter01.equation_1_7`: the spectral radius is the maximum
  of $|\lambda|$ over the eigenvalues.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.spectralRadius_conjTranspose`:
  $\rho(A^H) = \rho(A^T) = \rho(A)$.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.spectralRadius_smul`: $\rho(\alpha A) = |\alpha| \rho(A)$.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.spectralRadius_pow`: $\rho(A^k) = \rho(A)^k$.
* Exercise 8 of Chapter 1, `QuarteroniSaccoSaleri.Chapter01.exercise_1_8`:
  $\sigma(P(A)) = P(\sigma(A))$ for a polynomial $P$.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.spectrum_of_blockTriangular`: the spectrum of a block
  triangular matrix is the union of the spectra of its diagonal blocks.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.spectrum_of_isTriangular`: the eigenvalues of a triangular
  matrix are its diagonal entries.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.finrank_eigenspace_eq`: the eigenspace of $\lambda$ is
  $\ker(A - \lambda I)$, of dimension $n - \operatorname{rank}(A - \lambda I)$.
* §1.7, `QuarteroniSaccoSaleri.Chapter01.finrank_eigenspace_le_rootMultiplicity`: the geometric
  multiplicity of an eigenvalue is at most its algebraic multiplicity.

## Conventions

* Matrices are `Matrix (Fin n) (Fin n) ℂ`, or `Matrix (Fin n) (Fin n) ℝ` where the book says "real
  entries". The book's standing assumption $n \ge 1$ is the hypothesis `[NeZero n]` of the
  statements that need a nonempty spectrum.
* The spectrum $\sigma(A)$ is Mathlib's `spectrum ℂ A`, the set of $\mu$ such that $\mu I - A$ is
  not invertible. An eigenvector for $\mu$ is a vector $x \neq 0$ with `A *ᵥ x = μ • x`, and the
  eigenspace is `Module.End.eigenspace A.mulVecLin μ`.
* The book's characteristic polynomial $\det(A - \lambda I)$ differs from Mathlib's `A.charpoly`,
  which is $\det(\lambda I - A)$, by the sign $(-1)^n$. The roots agree.
* The algebraic multiplicity of $\mu$ is `A.charpoly.rootMultiplicity μ`, and the geometric
  multiplicity is the dimension of the eigenspace.
* The book's $x^H A x$ is `star x ⬝ᵥ (A *ᵥ x)`, and its $y^H A$ is `star y ᵥ* A`.

## Implementation notes

* The spectral radius of a complex matrix is Mathlib's `spectralRadius ℂ A`, with values in
  $[0, \infty]$. The spectral radius of a real matrix is the backbone's
  `Matrix.complexSpectralRadius A`, the spectral radius of `Matrix.complexify A`, because the real
  spectrum `spectrum ℝ A` does not contain the nonreal eigenvalues that the book counts.

## Deviations from the source

* **The characteristic polynomial** (reading). Lean uses $\det(\lambda I-A)$. The book uses
  $\det(A-\lambda I)$. The factor $(-1)^n$ leaves the roots and their multiplicities unchanged.
* **Real matrices** (reading and generalization). The eigenvector characterization can be
  applied to the complexification of a real matrix. The scaling and power laws are stated
  separately for the resulting complex spectral radius of real matrices.
* **Exercise 8** (generalization). Spectral mapping is stated for arbitrary polynomial degree.
-/

open Finset Matrix Polynomial
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter01

variable {n : ℕ}

/-! ### Eigenvalues, eigenvectors, the Rayleigh quotient -/

/-- **Section 1.7** of [quarteroni2000numerical], the definition of an eigenvalue. Let
$A \in \mathbb{C}^{n \times n}$ and $\lambda \in \mathbb{C}$. Then $\lambda$ is an
**eigenvalue** of $A$, that is, $\lambda$ belongs to the **spectrum** $\sigma(A)$, if and only
if there is a vector $x \in \mathbb{C}^n$ with $x \neq 0$ and $Ax = \lambda x$. Such an $x$ is
an **eigenvector** of $A$ for $\lambda$.

The spectrum is Mathlib's `spectrum ℂ A`. The proof is the backbone theorem
`Matrix.mem_spectrum_iff_exists_mulVec_eq_smul`.

**Reading.** For a real matrix, apply the criterion to `Matrix.complexify` to retain all complex
eigenvalues. -/
theorem mem_spectrum_iff_exists_mulVec_eq_smul (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ A ↔ ∃ x : Fin n → ℂ, x ≠ 0 ∧ A *ᵥ x = μ • x :=
  Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A μ

/-- **Section 1.7** of [quarteroni2000numerical], left eigenvectors and the Rayleigh quotient. Let
$A \in \mathbb{C}^{n \times n}$, $\lambda \in \mathbb{C}$ and $y \in \mathbb{C}^n$. Then $y$
satisfies $y^H A = \lambda y^H$ (it is a **left eigenvector** of $A$ for $\lambda$ when
$y \neq 0$) if and only if $A^H y = \bar\lambda y$, that is, if and only if $y$ is an
eigenvector of $A^H$ for $\bar\lambda$. Moreover, if $x \neq 0$ and $Ax = \lambda x$, then the
Rayleigh quotient recovers the eigenvalue:
$$\lambda = \frac{x^H A x}{x^H x}.$$
-/
theorem vecMul_eq_smul_iff_conjTranspose_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (y : Fin n → ℂ) :
    (star y ᵥ* A = μ • star y ↔ Aᴴ *ᵥ y = star μ • y) ∧
      ∀ x : Fin n → ℂ, x ≠ 0 → A *ᵥ x = μ • x → (star x ⬝ᵥ (A *ᵥ x)) / (star x ⬝ᵥ x) = μ := by
  refine ⟨?_, fun x hx hAx => ?_⟩
  · have h1 : star (Aᴴ *ᵥ y) = star y ᵥ* A := by rw [star_mulVec, conjTranspose_conjTranspose]
    have h2 : star (star μ • y) = μ • star y := by rw [star_smul, star_star]
    rw [← h1, ← h2, star_inj]
  · have h0 : star x ⬝ᵥ x ≠ 0 := by
      open scoped ComplexOrder in
      exact fun h => hx (dotProduct_star_self_eq_zero.1 h)
    rw [hAx, dotProduct_smul, smul_eq_mul, mul_div_cancel_right₀ _ h0]

/-! ### The characteristic equation -/

/-- **Section 1.7** of [quarteroni2000numerical], the characteristic equation. Let
$A \in \mathbb{C}^{n \times n}$ and $\mu \in \mathbb{C}$. Then $\mu \in \sigma(A)$ if and only
if $\mu$ is a root of the **characteristic polynomial** $p_A$ of $A$, if and only if
$\det(A - \mu I) = 0$. The polynomial $p_A$ has degree $n$ and exactly $n$ roots counted with
multiplicity.

The book defines $p_A(\lambda) = \det(A - \lambda I)$. Mathlib's `A.charpoly` is
$\det(\lambda I - A)$, which differs by the sign $(-1)^n$ and has the same roots. The proof uses
`Matrix.mem_spectrum_iff_isRoot_charpoly`.

**Reading.** Uses the monic characteristic polynomial with the opposite determinant order. Roots and
their multiplicities are unchanged.
-/
theorem mem_spectrum_iff_isRoot_charpoly (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    (μ ∈ spectrum ℂ A ↔ A.charpoly.IsRoot μ) ∧ (μ ∈ spectrum ℂ A ↔ (A - μ • 1).det = 0) ∧
      A.charpoly.natDegree = n ∧ A.charpoly.roots.card = n := by
  refine ⟨Matrix.mem_spectrum_iff_isRoot_charpoly, ?_, ?_, ?_⟩
  · rw [Matrix.mem_spectrum_iff_exists_mulVec_eq_smul, ← Matrix.exists_mulVec_eq_zero_iff]
    simp only [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
  · rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  · rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots, charpoly_natDegree_eq_dim,
      Fintype.card_fin]

/-- **Equation (1.6)** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$, with
eigenvalues $\lambda_1, \dots, \lambda_n$ counted with their algebraic multiplicity. Then
$$\det A = \prod_{i=1}^n \lambda_i, \qquad \operatorname{tr} A = \sum_{i=1}^n \lambda_i.$$
Consequently $A$ is singular if and only if $0$ is an eigenvalue of $A$.

The eigenvalues with multiplicity are the multiset `A.charpoly.roots`. The proof uses
`Matrix.det_eq_prod_roots_charpoly` and `Matrix.trace_eq_sum_roots_charpoly`. The last clause is
the equivalence of conditions (1) and (6) of `QuarteroniSaccoSaleri.Chapter01.nonsingular_tfae`. -/
theorem equation_1_6 (A : Matrix (Fin n) (Fin n) ℂ) :
    A.det = A.charpoly.roots.prod ∧ A.trace = A.charpoly.roots.sum ∧
      (¬ IsUnit A ↔ (0 : ℂ) ∈ spectrum ℂ A) :=
  ⟨det_eq_prod_roots_charpoly A, trace_eq_sum_roots_charpoly A,
    ((nonsingular_tfae A).out 1 6).not.trans not_not⟩

/-- **Section 1.7** of [quarteroni2000numerical], the spectra of $A^T$ and $A^H$. Let
$A \in \mathbb{C}^{n \times n}$. Then $\sigma(A^T) = \sigma(A)$, because
$\det(A^T - \lambda I) = \det(A - \lambda I)$. Moreover $\sigma(A^H) = \{\bar\lambda : \lambda
\in \sigma(A)\}$, so that $\lambda$ is an eigenvalue of $A$ if and only if $\bar\lambda$ is an
eigenvalue of $A^H$.

The proof uses `Matrix.spectrum_transpose` and `spectrum.map_star`. -/
theorem spectrum_transpose (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ Aᵀ = spectrum ℂ A ∧ spectrum ℂ Aᴴ = star '' spectrum ℂ A ∧
      ∀ μ : ℂ, star μ ∈ spectrum ℂ Aᴴ ↔ μ ∈ spectrum ℂ A := by
  have h : spectrum ℂ Aᴴ = star '' spectrum ℂ A := by
    rw [← star_eq_conjTranspose, spectrum.map_star, Set.image_star]
  exact ⟨Matrix.spectrum_transpose A, h, fun μ => by rw [h, Set.image_star, Set.star_mem_star]⟩

/-- **Section 1.7** of [quarteroni2000numerical], real matrices. Let $A \in \mathbb{R}^{n \times n}$
and $\mu \in \mathbb{C}$. Since $p_A$ has real coefficients, the eigenvalues of $A$ occur in
conjugate pairs: $\bar\mu \in \sigma(A)$ if and only if $\mu \in \sigma(A)$. Moreover, $\bar\mu$
and $\mu$ have the same algebraic multiplicity.

Here $\sigma(A)$ is the spectrum of `Matrix.complexify A`, the matrix $A$ regarded as a complex
matrix. The proof uses the backbone theorems `Matrix.star_mem_spectrum_complexify_iff` and
`Matrix.rootMultiplicity_charpoly_complexify_star`. -/
theorem star_mem_spectrum_complexify_iff (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) :
    (star μ ∈ spectrum ℂ (complexify A) ↔ μ ∈ spectrum ℂ (complexify A)) ∧
      (complexify A).charpoly.rootMultiplicity (star μ) =
        (complexify A).charpoly.rootMultiplicity μ :=
  ⟨Matrix.star_mem_spectrum_complexify_iff A μ, rootMultiplicity_charpoly_complexify_star A μ⟩

/-- **Section 1.7** of [quarteroni2000numerical] (the Cayley–Hamilton theorem). Every matrix
$A \in \mathbb{C}^{n \times n}$ annihilates its characteristic polynomial: $p_A(A) = 0$.

The proof is Mathlib's `Matrix.aeval_self_charpoly`. -/
theorem cayleyHamilton (A : Matrix (Fin n) (Fin n) ℂ) : aeval A A.charpoly = 0 :=
  aeval_self_charpoly A

/-! ### The spectral radius, (1.7) -/

section SpectralRadius

open scoped Matrix.Norms.L2Operator

/-- **Equation (1.7)** of [quarteroni2000numerical]. Let $n \ge 1$, $A \in \mathbb{C}^{n \times n}$
and $B \in \mathbb{R}^{n \times n}$. The **spectral radius** of $A$ is
$$\rho(A) = \max_{\lambda \in \sigma(A)} |\lambda|.$$
That is, $\rho(A)$ is the supremum of $|\lambda|$ over $\lambda \in \sigma(A)$, the supremum is
attained at some eigenvalue, and $\rho(A)$ is finite. The spectral radius of the real matrix $B$
is the spectral radius of $B$ regarded as a complex matrix.

The spectral radius is Mathlib's `spectralRadius ℂ A`, with values in $[0, \infty]$. For a real
matrix it is the backbone's `Matrix.complexSpectralRadius B`, because `spectrum ℝ B` does not
contain the nonreal eigenvalues. The attainment uses
`spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty`. -/
theorem equation_1_7 [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℝ) :
    spectralRadius ℂ A = ⨆ μ ∈ spectrum ℂ A, (‖μ‖₊ : ℝ≥0∞) ∧
      (∃ μ ∈ spectrum ℂ A, (‖μ‖₊ : ℝ≥0∞) = spectralRadius ℂ A) ∧ spectralRadius ℂ A ≠ ⊤ ∧
      B.complexSpectralRadius = spectralRadius ℂ (complexify B) := by
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact ⟨spectralRadius_eq_of_unital A, spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A), spectrum.spectralRadius_ne_top A,
    rfl⟩

end SpectralRadius

/-- **Section 1.7** of [quarteroni2000numerical]. For $A \in \mathbb{C}^{n \times n}$,
$$\rho(A^H) = \rho(A), \qquad \rho(A^T) = \rho(A).$$

The first identity holds because $\lambda \in \sigma(A)$ if and only if
$\bar\lambda \in \sigma(A^H)$, and $|\bar\lambda| = |\lambda|$. The second holds because
$\sigma(A^T) = \sigma(A)$. -/
theorem spectralRadius_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius ℂ Aᴴ = spectralRadius ℂ A ∧ spectralRadius ℂ Aᵀ = spectralRadius ℂ A :=
  ⟨by rw [← star_eq_conjTranspose, spectralRadius_star],
    by rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital,
      (Chapter01.spectrum_transpose A).1]⟩

/-- **Section 1.7** of [quarteroni2000numerical]. For $\alpha \in \mathbb{C}$ and
$A \in \mathbb{C}^{n \times n}$, $\rho(\alpha A) = |\alpha| \rho(A)$. For $c \in \mathbb{R}$ and
$B \in \mathbb{R}^{n \times n}$, the same identity $\rho(cB) = |c| \rho(B)$ holds for the
spectral radius of $B$ regarded as a complex matrix.

The proof uses the backbone theorems `spectralRadius_smul` and
`Matrix.complexSpectralRadius_smul`.

**Reading.** The scaling formula is also stated for real matrices using complexification.
-/
theorem spectralRadius_smul (α : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    spectralRadius ℂ (α • A) = ‖α‖₊ * spectralRadius ℂ A ∧
      (c • B).complexSpectralRadius = ‖c‖₊ * B.complexSpectralRadius :=
  ⟨_root_.spectralRadius_smul α A, complexSpectralRadius_smul c B⟩

/-- **Section 1.7** of [quarteroni2000numerical]. Let $n \ge 1$, $A \in \mathbb{C}^{n \times n}$,
$B \in \mathbb{R}^{n \times n}$ and $k \in \mathbb{N}$. Then
$$\rho(A^k) = \rho(A)^k, \qquad \rho(B^k) = \rho(B)^k,$$
where $\rho(B)$ is the spectral radius of $B$ regarded as a complex matrix.

This is the spectral mapping theorem for powers. The proof uses the backbone theorem
`spectralRadius_pow_of_nonempty`.

**Reading.** The formula also applies to real matrices by complexification.
-/
theorem spectralRadius_pow [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) :
    spectralRadius ℂ (A ^ k) = spectralRadius ℂ A ^ k ∧
      (B ^ k).complexSpectralRadius = B.complexSpectralRadius ^ k := by
  refine ⟨spectralRadius_pow_of_nonempty
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A) k, ?_⟩
  rw [complexSpectralRadius, complexSpectralRadius, complexify_pow]
  exact spectralRadius_pow_of_nonempty
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (complexify B)) k

/-- **Exercise 8 of Chapter 1** of [quarteroni2000numerical]. Let $n \ge 1$,
$A \in \mathbb{C}^{n \times n}$, and let $P(x) = \sum_k c_k x^k$ be a polynomial with complex
coefficients. Then the eigenvalues of $P(A) = \sum_k c_k A^k$ are the values of $P$ at the
eigenvalues of $A$:
$$\sigma(P(A)) = \{P(\lambda) : \lambda \in \sigma(A)\}.$$
In particular $\rho(A^2) = \rho(A)^2$.

The proof uses Mathlib's `spectrum.map_polynomial_aeval_of_nonempty`.

**Generalization.** The book writes a polynomial through degree $n$, the matrix order. The
formal statement allows arbitrary polynomial degree. -/
theorem exercise_1_8 [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (P : ℂ[X]) :
    spectrum ℂ (aeval A P) = (fun μ => P.eval μ) '' spectrum ℂ A ∧
      spectralRadius ℂ (A ^ 2) = spectralRadius ℂ A ^ 2 :=
  ⟨spectrum.map_polynomial_aeval_of_nonempty A P
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A),
    (Chapter01.spectralRadius_pow A 0 2).1⟩

/-! ### Block triangular matrices -/

/-- **Section 1.7** of [quarteroni2000numerical], block triangular matrices. Let
$A \in \mathbb{C}^{n \times n}$ be block upper triangular with diagonal blocks
$A_{11}, \dots, A_{kk}$. Then the characteristic polynomial of $A$ is the product of the
characteristic polynomials of the diagonal blocks,
$$p_A = p_{A_{11}} \cdots p_{A_{kk}},$$
and the spectrum of $A$ is the union of the spectra of the diagonal blocks.

The block structure is `Matrix.BlockTriangular A b` for a map $b$ from the indices to a linearly
ordered type, which assigns each index to its block; the diagonal block of index $k$ is
`A.toSquareBlock b k`, and the blocks range over the image of $b$. The proof uses
`Matrix.BlockTriangular.charpoly`. -/
theorem spectrum_of_blockTriangular {α : Type*} [LinearOrder α] {A : Matrix (Fin n) (Fin n) ℂ}
    {b : Fin n → α} (hA : A.BlockTriangular b) :
    A.charpoly = ∏ k ∈ univ.image b, (A.toSquareBlock b k).charpoly ∧
      spectrum ℂ A = ⋃ k ∈ univ.image b, spectrum ℂ (A.toSquareBlock b k) := by
  refine ⟨hA.charpoly, Set.ext fun μ => ?_⟩
  simp only [Set.mem_iUnion, Matrix.mem_spectrum_iff_isRoot_charpoly, hA.charpoly, isRoot_prod,
    exists_prop]

/-- **Section 1.7** of [quarteroni2000numerical], triangular matrices. Let
$U, L \in \mathbb{C}^{n \times n}$. If $U$ is upper triangular, then
$\sigma(U) = \{u_{11}, \dots, u_{nn}\}$. If $L$ is lower triangular, then
$\sigma(L) = \{l_{11}, \dots, l_{nn}\}$.

The proof uses `Matrix.charpoly_of_isUpperTriangular`, and the transpose for the lower
triangular case. -/
theorem spectrum_of_isTriangular (U L : Matrix (Fin n) (Fin n) ℂ) :
    (U.IsUpperTriangular → spectrum ℂ U = Set.range fun i => U i i) ∧
      (L.IsLowerTriangular → spectrum ℂ L = Set.range fun i => L i i) := by
  have key : ∀ T : Matrix (Fin n) (Fin n) ℂ, T.IsUpperTriangular →
      spectrum ℂ T = Set.range fun i => T i i := fun T hT => by
    ext μ
    simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_of_isUpperTriangular T hT,
      IsRoot.def, eval_prod, Finset.prod_eq_zero_iff, mem_univ, true_and, eval_sub, eval_X,
      eval_C, sub_eq_zero, Set.mem_range]
    exact exists_congr fun i => eq_comm
  refine ⟨key U, fun hL => ?_⟩
  have hLt : Lᵀ.IsUpperTriangular := fun _ _ hij => hL (OrderDual.toDual_lt_toDual.2 hij)
  rw [← Matrix.spectrum_transpose, key Lᵀ hLt]
  rfl

/-! ### Geometric and algebraic multiplicity, defective matrices -/

/-- **Section 1.7** of [quarteroni2000numerical], the eigenspace and the geometric multiplicity. Let
$A \in \mathbb{C}^{n \times n}$ and $\mu \in \mathbb{C}$. The **eigenspace** of $\mu$, the set
of the eigenvectors for $\mu$ together with the null vector, is $\ker(A - \mu I)$. Its
dimension, the **geometric multiplicity** of $\mu$, is
$$\dim \ker(A - \mu I) = n - \operatorname{rank}(A - \mu I).$$

The eigenspace is `Module.End.eigenspace A.mulVecLin μ`. The proof uses the backbone theorems
`Matrix.eigenspace_mulVecLin_eq_ker` and `Matrix.rank_add_finrank_ker_mulVecLin` (rank–nullity). -/
theorem finrank_eigenspace_eq (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.End.eigenspace A.mulVecLin μ = LinearMap.ker (A - μ • 1).mulVecLin ∧
      Module.finrank ℂ (Module.End.eigenspace A.mulVecLin μ) = n - (A - μ • 1).rank := by
  refine ⟨eigenspace_mulVecLin_eq_ker A μ, ?_⟩
  have h := rank_add_finrank_ker_mulVecLin (A - μ • 1)
  rw [Fintype.card_fin] at h
  rw [eigenspace_mulVecLin_eq_ker]
  omega

/-- **Section 1.7** of [quarteroni2000numerical], the two multiplicities. Let
$A \in \mathbb{C}^{n \times n}$ and $\mu \in \mathbb{C}$. The geometric multiplicity of $\mu$ is
at most its **algebraic multiplicity**, the multiplicity of $\mu$ as a root of the
characteristic polynomial.

The algebraic multiplicity is `A.charpoly.rootMultiplicity μ`. The proof is the backbone theorem
`Matrix.finrank_eigenspace_le_rootMultiplicity_charpoly`. -/
theorem finrank_eigenspace_le_rootMultiplicity (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace A.mulVecLin μ) ≤ A.charpoly.rootMultiplicity μ :=
  finrank_eigenspace_le_rootMultiplicity_charpoly A μ

/-- **Section 1.7** of [quarteroni2000numerical], defective matrices. An eigenvalue of
$A \in \mathbb{C}^{n \times n}$ is **defective** if its geometric multiplicity is strictly less
than its algebraic multiplicity. The matrix $A$ is **defective** if it has at least one
defective eigenvalue. -/
def IsDefective (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ μ ∈ spectrum ℂ A,
    Module.finrank ℂ (Module.End.eigenspace A.mulVecLin μ) < A.charpoly.rootMultiplicity μ

/-- **Definition 1.13** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$ and let
$S$ be a subspace of $\mathbb{C}^n$. Then $S$ is **invariant** with respect to $A$,
$AS \subseteq S$, if and only if $Ax \in S$ for every $x \in S$. Moreover, for every
$\mu \in \mathbb{C}$ the eigenspace of $\mu$ is invariant with respect to $A$, because
$Ax = \mu x$ implies $A(Ax) = \mu (Ax)$.

The image $AS$ is `S.map A.mulVecLin`. -/
theorem definition_1_13 (A : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) (μ : ℂ) :
    (S.map A.mulVecLin ≤ S ↔ ∀ x ∈ S, A *ᵥ x ∈ S) ∧
      (Module.End.eigenspace A.mulVecLin μ).map A.mulVecLin ≤
        Module.End.eigenspace A.mulVecLin μ := by
  refine ⟨Submodule.map_le_iff_le_comap, Submodule.map_le_iff_le_comap.2 fun x hx => ?_⟩
  rw [Module.End.mem_eigenspace_iff] at hx
  rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff, hx, map_smul, hx]

end QuarteroniSaccoSaleri.Chapter01
