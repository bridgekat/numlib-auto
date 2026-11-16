/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Numlib.Eigen.MinMax
import Numlib.Eigen.Normal
import Numlib.Eigen.NumericalRange
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 1.9: Normal and Hermitian matrices

This module formalizes §1.9 of [saad2003iterative]: normal matrices with the field of values and the
numerical radius (§1.9.1), and Hermitian matrices with the min–max theorems (§1.9.2). A matrix
$A \in \mathbb{C}^{n \times n}$ is normal when $A^H A = A A^H$. The Rayleigh quotient of $A$ at
$x \neq 0$ is $\mu(x) = (Ax, x)/(x, x)$; the field of values $F(A)$ is the set of these quotients,
and the numerical radius is $\nu(A) = \max_{x \neq 0} |\mu(x)|$.

The module proves that a normal triangular matrix is diagonal, that a matrix is normal exactly when
it is unitarily similar to a diagonal matrix, and exactly when its eigenvectors are eigenvectors of
$A^H$. It proves that $F(A)$ is convex and contains the convex hull of the spectrum, with equality
for a normal matrix, the chain $\rho(A) \le \nu(A) \le \|A\|_2$, and the power inequality
$\nu(A^k) \le \nu(A)^k$. For a Hermitian matrix it proves that the eigenvalues are real, the
spectral theorem, and the min–max characterizations of the eigenvalues
$\lambda_1 \ge \dots \ge \lambda_n$ by Rayleigh quotients. The proofs specialize the backbone
modules `Numlib.Eigen.Normal`, `Numlib.Eigen.NumericalRange` and `Numlib.Eigen.MinMax`, and
Mathlib's `Matrix.IsHermitian.spectral_theorem`.

## Main definitions

* §1.9.1, `SaadSparse.Chapter01.normalEigenBasis`: an orthonormal basis of eigenvectors of a normal
  matrix.
* §1.9.1, `SaadSparse.Chapter01.normalEigenvalues`: the eigenvalues of a normal matrix, in the order
  of this basis.
* Equation (1.33), `SaadSparse.Chapter01.rayleigh`: the complex Rayleigh quotient
  $\mu(x) = (Ax, x)/(x, x)$.
* §1.9.1, `SaadSparse.Chapter01.fieldOfValues`: the field of values, the set of Rayleigh quotients
  at nonzero vectors.
* §1.9.1, `SaadSparse.Chapter01.numericalRadius`: the numerical radius
  $\nu(A) = \max_{x \neq 0} |\mu(x)|$.
* §1.9.2, `SaadSparse.Chapter01.eigenvaluesDesc`: the eigenvalues
  $\lambda_1 \ge \dots \ge \lambda_n$ of a Hermitian matrix in decreasing order.
* §1.9.2, `SaadSparse.Chapter01.eigenvectorBasisDesc`: an orthonormal basis of eigenvectors
  $q_1, \dots, q_n$ of a Hermitian matrix in the same order.

## Main results

* Lemma 1.13, `SaadSparse.Chapter01.lemma_1_13`: a normal upper triangular matrix is diagonal.
* Theorem 1.14, `SaadSparse.Chapter01.theorem_1_14`: a matrix is normal if and only if it is
  unitarily similar to a diagonal matrix.
* Lemma 1.15, `SaadSparse.Chapter01.lemma_1_15`: a matrix is normal if and only if each of its
  eigenvectors is an eigenvector of $A^H$.
* Corollary 1.16, `SaadSparse.Chapter01.corollary_1_16`: a normal matrix with real spectrum is
  Hermitian.
* §1.9.1, `SaadSparse.Chapter01.norm_rayleigh_le`: $|\mu(x)| \le \|A\|_2$.
* §1.9.1, `SaadSparse.Chapter01.numericalRadius_le_l2_opNorm`: $\nu(A) \le \|A\|_2$.
* Proposition 1.18, `SaadSparse.Chapter01.proposition_1_18_convex`: the field of values is convex
  (Toeplitz–Hausdorff theorem).
* Proposition 1.18, `SaadSparse.Chapter01.spectrum_subset_fieldOfValues`: the spectrum is contained
  in the field of values.
* Proposition 1.18, `SaadSparse.Chapter01.proposition_1_18`: the field of values is convex and
  contains the convex hull of the spectrum.
* §1.9.1, `SaadSparse.Chapter01.spectralRadius_le_numericalRadius`: $\rho(A) \le \nu(A)$.
* Equation (1.36), `SaadSparse.Chapter01.equation_1_36`: $\nu(A^k) \le \nu(A)^k$ for $k \ge 1$.
* Equation (1.34), `SaadSparse.Chapter01.equation_1_34`: the Rayleigh quotient of a normal matrix is
  a convex combination of its eigenvalues.
* Theorem 1.17, `SaadSparse.Chapter01.theorem_1_17`: the field of values of a normal matrix is the
  convex hull of its spectrum.
* Theorem 1.19, `SaadSparse.Chapter01.theorem_1_19`: the eigenvalues of a Hermitian matrix are real.
* Theorem 1.20, `SaadSparse.Chapter01.theorem_1_20`: a Hermitian matrix is unitarily similar to a
  real diagonal matrix.
* §1.9.2, `SaadSparse.Chapter01.inner_self_isReal_iff_isHermitian`: a complex matrix has real
  $(Ax, x)$ for all $x$ if and only if it is Hermitian.
* Theorem 1.21, `SaadSparse.Chapter01.theorem_1_21`: the Courant–Fischer min–max principle (1.37)
  and the max–min form (1.39).
* Equation (1.38), `SaadSparse.Chapter01.equation_1_38`: $\lambda_1$ is the largest value of the
  Rayleigh quotient.
* Equation (1.40), `SaadSparse.Chapter01.equation_1_40`: $\lambda_n$ is the smallest value of the
  Rayleigh quotient.
* Theorem 1.22, `SaadSparse.Chapter01.theorem_1_22`: $\lambda_k$ is the largest value of the
  Rayleigh quotient on the vectors orthogonal to $q_1, \dots, q_{k-1}$, attained at $q_k$ (1.41).

## Conventions

* The book's inner product $(x, y)$ is `inner 𝕜 y x`. So the Rayleigh quotient (1.33)
  $\mu(x) = (Ax, x)/(x, x)$ is `SaadSparse.Chapter01.rayleigh`, which is `inner ℂ x (A ⬝ x)` divided
  by `inner ℂ x x`.
* The book indexes the eigenvalues of a Hermitian matrix in decreasing order
  $\lambda_1 \ge \dots \ge \lambda_n$. This is `SaadSparse.Chapter01.eigenvaluesDesc`, with
  $0$-based indices: the book's $\lambda_k$ is `eigenvaluesDesc hA (k - 1)`. Mathlib's
  `Matrix.IsHermitian.eigenvalues` is in no particular order, while the backbone's
  `LinearMap.IsSymmetric.eigenvalues` is already decreasing.

## Implementation notes

* Lemma 1.15 is the pair `LinearMap.IsStarNormal.eigenspace_adjoint` and
  `LinearMap.isStarNormal_of_adjoint_apply_eq_smul`, and Theorem 1.14 is
  `Matrix.IsStarNormal.spectral_theorem`, whose orthonormal eigenbasis
  `LinearMap.IsStarNormal.eigenvectorBasis` is `SaadSparse.Chapter01.normalEigenBasis`.
* The backbone's `LinearMap.rayleighQuotient` is the real part of `SaadSparse.Chapter01.rayleigh`,
  which is all that a Hermitian matrix needs. The min–max theorems are stated with it.
* `SaadSparse.Chapter01.fieldOfValues` is definitionally the backbone's `LinearMap.numericalRange`
  of `Matrix.toEuclideanLin A`. The convexity in Proposition 1.18, the Toeplitz–Hausdorff theorem
  that the book states without proof, is the backbone's `LinearMap.convex_numericalRange`.
* The power inequality (1.36), Berger's inequality, which the book attributes to the literature, is
  proved over the backbone's `LinearMap.norm_inner_pow_le`.
-/

open Matrix Finset Module.End Polynomial

open scoped SaadSparse ComplexConjugate ENNReal

namespace SaadSparse.Chapter01

variable {n : ℕ}

/-! ### §1.9.1 Normal matrices -/

section Lemma113

variable {A : Matrix (Fin n) (Fin n) ℂ}

private theorem blockTriangular_smul {a : ℂ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.BlockTriangular id) : (a • M).BlockTriangular id :=
  fun _ _ h => by rw [Matrix.smul_apply, hM h, smul_zero]

private theorem blockTriangular_pow (hA : A.BlockTriangular id) (k : ℕ) :
    (A ^ k).BlockTriangular id := by
  induction k with
  | zero => simpa using Matrix.blockTriangular_one
  | succ k ih => rw [pow_succ]; exact ih.mul hA

private theorem blockTriangular_aeval (hA : A.BlockTriangular id) (p : ℂ[X]) :
    (aeval A p).BlockTriangular id := by
  induction p using Polynomial.induction_on with
  | C a =>
      rw [aeval_C, Algebra.algebraMap_eq_smul_one]
      exact blockTriangular_smul Matrix.blockTriangular_one
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial k a _ =>
      rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul]
      exact blockTriangular_smul (blockTriangular_pow hA _)

/-- **Lemma 1.13** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$ be normal and upper
triangular. Then $A$ is diagonal.

Upper triangular is `Matrix.BlockTriangular A id`. The conjugate transpose of a normal matrix is
a polynomial in it (Problem P-1.19, the backbone's
`Matrix.IsStarNormal.exists_aeval_eq_conjTranspose`), so $A^H$ is upper triangular as well, and
a matrix that is upper triangular together with its conjugate transpose is diagonal. -/
theorem lemma_1_13 (hA : IsStarNormal A) (hT : A.BlockTriangular id) : Matrix.IsDiag A := by
  obtain ⟨q, hq⟩ := Matrix.IsStarNormal.exists_aeval_eq_conjTranspose hA
  have hH : Aᴴ.BlockTriangular id := hq ▸ blockTriangular_aeval hT q
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · have hji := hH h
    rw [Matrix.conjTranspose_apply, star_eq_zero] at hji
    exact hji
  · exact hT h

end Lemma113

/-- **Theorem 1.14** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$. Then $A$ is normal
if and only if there are a unitary $Q \in \mathbb{C}^{n \times n}$ and $d \in \mathbb{C}^n$ with
$$Q^H A Q = \operatorname{diag}(d).$$

The proof is the backbone's `Matrix.IsStarNormal.spectral_theorem`. -/
theorem theorem_1_14 {A : Matrix (Fin n) (Fin n) ℂ} :
    IsStarNormal A ↔
      ∃ Q ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ d : Fin n → ℂ, Qᴴ * A * Q = Matrix.diagonal d :=
  Matrix.IsStarNormal.spectral_theorem

section EigenBasis

variable {A : Matrix (Fin n) (Fin n) ℂ}

/-- **Theorem 1.14** of [saad2003iterative], in the form that the section uses: for a normal
$A \in \mathbb{C}^{n \times n}$, an orthonormal basis $q_1, \dots, q_n$ of $\mathbb{C}^n$ that
consists of eigenvectors of $A$.

This is the backbone's `LinearMap.IsStarNormal.eigenvectorBasis` for `Matrix.toEuclideanLin A`. -/
noncomputable abbrev normalEigenBasis (hA : IsStarNormal A) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  LinearMap.IsStarNormal.eigenvectorBasis (Matrix.isStarNormal_toEuclideanLin_iff.2 hA)
    finrank_euclideanSpace_fin

/-- The eigenvalues $\lambda_1, \dots, \lambda_n$ of a normal matrix $A$, with $\lambda_k$ the
eigenvalue of the eigenvector $q_k$ of `SaadSparse.Chapter01.normalEigenBasis`. -/
noncomputable abbrev normalEigenvalues (hA : IsStarNormal A) : Fin n → ℂ :=
  LinearMap.IsStarNormal.eigenvalues (Matrix.isStarNormal_toEuclideanLin_iff.2 hA)
    finrank_euclideanSpace_fin

/-- For a normal matrix $A$, each vector $q_k$ of `SaadSparse.Chapter01.normalEigenBasis` is an
eigenvector: $A q_k = \lambda_k q_k$, with $\lambda_k$ given by
`SaadSparse.Chapter01.normalEigenvalues`. -/
theorem apply_normalEigenBasis (hA : IsStarNormal A) (k : Fin n) :
    (A ⬝ normalEigenBasis hA k) = normalEigenvalues hA k • normalEigenBasis hA k :=
  LinearMap.IsStarNormal.apply_eigenvectorBasis _ _ k

/-- For a normal matrix $A$, each $\lambda_k$ of `SaadSparse.Chapter01.normalEigenvalues` is in the
spectrum of $A$. -/
theorem normalEigenvalues_mem_spectrum (hA : IsStarNormal A) (k : Fin n) :
    normalEigenvalues hA k ∈ spectrum ℂ A := by
  rw [← Matrix.hasEigenvalue_toEuclideanLin_iff]
  exact hasEigenvalue_of_hasEigenvector
    ⟨mem_eigenspace_iff.2 (apply_normalEigenBasis hA k),
      (normalEigenBasis hA).toBasis.ne_zero k⟩

/-- For a normal matrix $A$, the conjugate transpose acts on the eigenbasis by the conjugate
eigenvalues: $A^H q_k = \bar\lambda_k q_k$. This is the easy half of Lemma 1.15 in coordinates. -/
theorem conjTranspose_apply_normalEigenBasis (hA : IsStarNormal A) (k : Fin n) :
    (Aᴴ ⬝ normalEigenBasis hA k) = conj (normalEigenvalues hA k) • normalEigenBasis hA k := by
  have hT := Matrix.isStarNormal_toEuclideanLin_iff.2 hA
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  refine mem_eigenspace_iff.1 ?_
  rw [LinearMap.IsStarNormal.eigenspace_adjoint hT]
  exact mem_eigenspace_iff.2 (apply_normalEigenBasis hA k)

/-- For a normal matrix $A$, the coordinate of $Ax$ along an eigenvector is the eigenvalue times the
coordinate of $x$: $(Ax, q_k) = \lambda_k (x, q_k)$ for every $x \in \mathbb{C}^n$. -/
theorem inner_normalEigenBasis_apply (hA : IsStarNormal A) (k : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (normalEigenBasis hA k) (A ⬝ x) =
      normalEigenvalues hA k * inner ℂ (normalEigenBasis hA k) x := by
  have h := LinearMap.adjoint_inner_left (toEuclideanLin A) x (normalEigenBasis hA k)
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_apply_normalEigenBasis hA k,
    inner_smul_left, RingHomCompTriple.comp_apply, RingHom.id_apply] at h
  exact h.symm

end EigenBasis

/-- **Lemma 1.15** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$. Then $A$ is normal
if and only if every eigenvector of $A$ is an eigenvector of $A^H$: for all $\mu \in \mathbb{C}$
and $v \in \mathbb{C}^n$ with $Av = \mu v$, there is $\nu \in \mathbb{C}$ with $A^H v = \nu v$.

The forward direction is the backbone's `LinearMap.IsStarNormal.eigenspace_adjoint`. The
converse is the more difficult `LinearMap.isStarNormal_of_adjoint_apply_eq_smul`. -/
theorem lemma_1_15 {A : Matrix (Fin n) (Fin n) ℂ} :
    IsStarNormal A ↔
      ∀ (μ : ℂ) (v : EuclideanSpace ℂ (Fin n)), (A ⬝ v) = μ • v → ∃ ν : ℂ, (Aᴴ ⬝ v) = ν • v := by
  rw [← Matrix.isStarNormal_toEuclideanLin_iff]
  constructor
  · intro hT μ v hv
    refine ⟨conj μ, ?_⟩
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    refine mem_eigenspace_iff.1 ?_
    rw [LinearMap.IsStarNormal.eigenspace_adjoint hT]
    exact mem_eigenspace_iff.2 hv
  · intro h
    refine LinearMap.isStarNormal_of_adjoint_apply_eq_smul fun μ v hv => ?_
    obtain ⟨ν, hν⟩ := h μ v hv
    exact ⟨ν, by rwa [Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at hν⟩

/-- **Corollary 1.16** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$ be normal, with
all its eigenvalues real. Then $A$ is Hermitian.

The converse is Theorem 1.19, `SaadSparse.Chapter01.theorem_1_19`. -/
theorem corollary_1_16 {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A)
    (hreal : spectrum ℂ A ⊆ Set.range ((↑) : ℝ → ℂ)) : A.IsHermitian := by
  obtain ⟨Q, hQ, d, hd⟩ := theorem_1_14.mp hA
  have hspec : Set.range d = spectrum ℂ A := by
    rw [← spectrum_diagonal d, ← hd, ← Matrix.star_eq_conjTranspose]
    exact Unitary.spectrum_star_left_conjugate
      (U := (⟨Q, hQ⟩ : unitary (Matrix (Fin n) (Fin n) ℂ)))
  have hdiag : Matrix.diagonal (star d) = Matrix.diagonal d := by
    refine congrArg Matrix.diagonal (funext fun j => ?_)
    obtain ⟨r, hr⟩ := hreal (hspec ▸ Set.mem_range_self j)
    rw [Pi.star_apply, ← hr, RCLike.star_def, Complex.conj_ofReal]
  have hstar' : Q * star Q = 1 := (Unitary.mem_iff.1 hQ).2
  have hA' : A = Q * Matrix.diagonal d * Qᴴ := by
    rw [← hd, ← Matrix.star_eq_conjTranspose]
    calc A = Q * star Q * A * (Q * star Q) := by rw [hstar', Matrix.one_mul, Matrix.mul_one]
      _ = Q * (star Q * A * Q) * star Q := by simp only [Matrix.mul_assoc]
  change Aᴴ = A
  conv_lhs => rw [hA']
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, ← Matrix.mul_assoc,
    hdiag, ← hA']

/-! ### §1.9.1 The field of values and the numerical radius -/

section FieldOfValues

open scoped Matrix.Norms.L2Operator

variable {A : Matrix (Fin n) (Fin n) ℂ}

/-- **Equation (1.33)** of [saad2003iterative]. The **Rayleigh quotient** of
$A \in \mathbb{C}^{n \times n}$ at $x \in \mathbb{C}^n$ is the complex number
$$\mu(x) = \frac{(Ax, x)}{(x, x)}.$$
At $x = 0$ its value is $0$, since division by $0$ gives $0$.

The backbone's `LinearMap.rayleighQuotient` is the real part of $\mu(x)$. -/
noncomputable def rayleigh (A : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) : ℂ :=
  inner ℂ x (A ⬝ x) / inner ℂ x x

/-- **Section 1.9.1** of [saad2003iterative], field of values. The **field of values** of
$A \in \mathbb{C}^{n \times n}$ is the set of its Rayleigh quotients at nonzero vectors:
$$F(A) = \{\mu(x) : x \in \mathbb{C}^n, \ x \neq 0\}.$$
-/
def fieldOfValues (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ x : EuclideanSpace ℂ (Fin n), x ≠ 0 ∧ rayleigh A x = z}

/-- **Section 1.9.1** of [saad2003iterative], numerical radius. The **numerical radius** of
$A \in \mathbb{C}^{n \times n}$ is
$$\nu(A) = \max_{x \neq 0} |\mu(x)|.$$

The supremum in the definition runs over every $x$, including $x = 0$, and this gives the same
number: $\mu(0) = 0$, and every value $|\mu(x)|$ is nonnegative, so $x = 0$ cannot raise the
supremum. For $n = 0$ the value is $0$. -/
noncomputable def numericalRadius (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ⨆ x : EuclideanSpace ℂ (Fin n), ‖rayleigh A x‖

/-- For $A \in \mathbb{C}^{n \times n}$ and $x \in \mathbb{C}^n$, $\|Ax\|_2 \le \|A\|_2 \|x\|_2$,
where $\|A\|_2$ is the operator norm `Matrix.Norms.L2Operator`. -/
theorem norm_toEuclideanLin_le (A : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    ‖(A ⬝ x)‖ ≤ ‖A‖ * ‖x‖ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).le_opNorm x

/-- **Section 1.9.1** of [saad2003iterative], bound by the $2$-norm. Let
$A \in \mathbb{C}^{n \times n}$. Then every value of the Rayleigh quotient satisfies
$|\mu(x)| \le \|A\|_2$, for every $x \in \mathbb{C}^n$. -/
theorem norm_rayleigh_le (A : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    ‖rayleigh A x‖ ≤ ‖A‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [rayleigh]
  · have hxx : ‖(inner ℂ x x : ℂ)‖ = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg x)]
    have hpos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    rw [rayleigh, norm_div, hxx, div_le_iff₀ hpos]
    calc ‖(inner ℂ x (A ⬝ x) : ℂ)‖ ≤ ‖x‖ * ‖(A ⬝ x)‖ := norm_inner_le_norm (𝕜 := ℂ) x _
      _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by gcongr; exact norm_toEuclideanLin_le A x
      _ = ‖A‖ * ‖x‖ ^ 2 := by ring

private theorem bddAbove_rayleigh (A : Matrix (Fin n) (Fin n) ℂ) :
    BddAbove (Set.range fun x : EuclideanSpace ℂ (Fin n) => ‖rayleigh A x‖) :=
  ⟨‖A‖, by rintro _ ⟨x, rfl⟩; exact norm_rayleigh_le A x⟩

/-- For $A \in \mathbb{C}^{n \times n}$ and every $x \in \mathbb{C}^n$, $|\mu(x)| \le \nu(A)$. -/
theorem norm_rayleigh_le_numericalRadius (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ‖rayleigh A x‖ ≤ numericalRadius A :=
  le_ciSup (bddAbove_rayleigh A) x

/-- **Section 1.9.1** of [saad2003iterative], upper bound of the numerical radius. Let
$A \in \mathbb{C}^{n \times n}$. Then $\nu(A) \le \|A\|_2$. This is the second half of the chain
$\rho(A) \le \nu(A) \le \|A\|_2$. -/
theorem numericalRadius_le_l2_opNorm (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRadius A ≤ ‖A‖ :=
  ciSup_le fun x => norm_rayleigh_le A x

/-- **Section 1.9.1** of [saad2003iterative], field of values. For $A \in \mathbb{C}^{n \times n}$,
the field of values $F(A)$ is the backbone's `LinearMap.numericalRange` of the operator
$x \mapsto Ax$ on $\mathbb{C}^n$. -/
theorem fieldOfValues_eq_numericalRange (A : Matrix (Fin n) (Fin n) ℂ) :
    fieldOfValues A = (Matrix.toEuclideanLin A).numericalRange := rfl

/-- **Proposition 1.18** of [saad2003iterative], convexity. Let $A \in \mathbb{C}^{n \times n}$.
Then the field of values $F(A)$ is convex.

This is the Toeplitz–Hausdorff theorem, which the book states without proof. It is the
backbone's `LinearMap.convex_numericalRange`. -/
theorem proposition_1_18_convex (A : Matrix (Fin n) (Fin n) ℂ) : Convex ℝ (fieldOfValues A) :=
  LinearMap.convex_numericalRange _

/-- **Proposition 1.18** of [saad2003iterative], containment of the spectrum. Let
$A \in \mathbb{C}^{n \times n}$. Then $\sigma(A) \subseteq F(A)$.

An eigenvalue of $A$ is the Rayleigh quotient of $A$ at any of its eigenvectors. -/
theorem spectrum_subset_fieldOfValues (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ fieldOfValues A := by
  intro μ hμ
  obtain ⟨v, hv, hv0⟩ :=
    Module.End.HasEigenvalue.exists_hasEigenvector
      ((Matrix.hasEigenvalue_toEuclideanLin_iff A μ).2 hμ)
  refine ⟨v, hv0, ?_⟩
  have hvv : (inner ℂ v v : ℂ) ≠ 0 := fun h => hv0 (inner_self_eq_zero.1 h)
  rw [rayleigh, mem_eigenspace_iff.1 hv, inner_smul_right, mul_div_assoc, div_self hvv, mul_one]

/-- **Proposition 1.18** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$. Then the field
of values $F(A)$ is convex and contains the convex hull of the spectrum of $A$:
$$\operatorname{conv} \sigma(A) \subseteq F(A).$$

The third sentence of the proposition in the book, that the two sets are equal for a normal
matrix, is `SaadSparse.Chapter01.theorem_1_17`. -/
theorem proposition_1_18 (A : Matrix (Fin n) (Fin n) ℂ) :
    Convex ℝ (fieldOfValues A) ∧ convexHull ℝ (spectrum ℂ A) ⊆ fieldOfValues A :=
  ⟨proposition_1_18_convex A,
    convexHull_min (spectrum_subset_fieldOfValues A) (proposition_1_18_convex A)⟩

/-- **Section 1.9.1** of [saad2003iterative], lower bound of the numerical radius. Let
$A \in \mathbb{C}^{n \times n}$. Then $\rho(A) \le \nu(A)$. This is the first half of the chain
$\rho(A) \le \nu(A) \le \|A\|_2$.

The spectral radius is Mathlib's `spectralRadius ℂ A`, with values in $[0, \infty]$. -/
theorem spectralRadius_le_numericalRadius (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius ℂ A ≤ ENNReal.ofReal (numericalRadius A) := by
  rw [spectralRadius_eq_of_unital]
  refine iSup₂_le fun μ hμ => ?_
  obtain ⟨x, _, hx⟩ := spectrum_subset_fieldOfValues A hμ
  rw [← enorm_eq_nnnorm, ← ofReal_norm, ← hx]
  exact ENNReal.ofReal_le_ofReal (norm_rayleigh_le_numericalRadius A x)

/-- For $x \in \mathbb{C}^n$, $(x, x) = \|x\|_2^2$ as a complex number. -/
private theorem inner_self_ofReal (x : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ x x : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; rfl

/-- **Section 1.9.1** of [saad2003iterative]. For $A \in \mathbb{C}^{n \times n}$, $\nu(A) \ge 0$,
since $\mu(0) = 0$. -/
theorem numericalRadius_nonneg (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ numericalRadius A := by
  simpa [rayleigh] using norm_rayleigh_le_numericalRadius A 0

/-- **Section 1.9.1** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$. Then for every
$x \in \mathbb{C}^n$,
$$|(Ax, x)| \le \nu(A) \|x\|_2^2.$$
-/
theorem norm_inner_le_numericalRadius (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖(inner ℂ x (A ⬝ x) : ℂ)‖ ≤ numericalRadius A * ‖x‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
    have h := norm_rayleigh_le_numericalRadius A x
    rw [rayleigh, norm_div, inner_self_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx2.le, div_le_iff₀ hx2] at h
    exact h

/-- **Equation (1.36)** of [saad2003iterative] (power inequality for the numerical radius). Let
$A \in \mathbb{C}^{n \times n}$ and $k \ge 1$. Then
$$\nu(A^k) \le \nu(A)^k.$$

The book attributes this inequality to the literature and does not prove it. It is Berger's
inequality, and it is a real theorem: the numerical radius is not submultiplicative, since
$\nu(AB) \le \nu(A) \nu(B)$ is false in general. The backbone proof,
`LinearMap.norm_inner_pow_le`, is Pearcy's: it averages the resolvents $(I - \omega^j z A)^{-1}$
over the $k$-th roots of unity $\omega^j$, and needs no unitary dilation. -/
theorem equation_1_36 (A : Matrix (Fin n) (Fin n) ℂ) {k : ℕ} (hk : 0 < k) :
    numericalRadius (A ^ k) ≤ numericalRadius A ^ k := by
  have hnn := numericalRadius_nonneg A
  have hbound := LinearMap.norm_inner_pow_le (T := Matrix.toEuclideanLin A) hnn
    (norm_inner_le_numericalRadius A) hk
  refine ciSup_le fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [rayleigh, inner_zero_left, zero_div, norm_zero]
    positivity
  · have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
    have h := hbound x
    rw [← Matrix.toEuclideanLin_pow] at h
    rw [rayleigh, norm_div, inner_self_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx2.le, div_le_iff₀ hx2]
    exact h

end FieldOfValues

/-! ### §1.9.1 The Rayleigh quotient of a normal matrix -/

section Normal

variable {A : Matrix (Fin n) (Fin n) ℂ}

/-- The squared eigenbasis coordinates of a vector, the weights of (1.34). -/
private noncomputable def coordSq (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n))
    (k : Fin n) : ℝ := ‖(inner ℂ (normalEigenBasis hA k) x : ℂ)‖ ^ 2

private theorem coordSq_def (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
    coordSq hA x k = ‖(inner ℂ (normalEigenBasis hA k) x : ℂ)‖ ^ 2 := rfl

private theorem coordSq_nonneg (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
    0 ≤ coordSq hA x k := sq_nonneg _

private theorem coordSq_cast (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
    ((coordSq hA x k : ℝ) : ℂ) =
      inner ℂ x (normalEigenBasis hA k) * inner ℂ (normalEigenBasis hA k) x := by
  rw [coordSq_def, ← inner_conj_symm x (normalEigenBasis hA k), RCLike.conj_mul]
  norm_cast

private theorem sum_coordSq (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n)) :
    ((∑ k, coordSq hA x k : ℝ) : ℂ) = inner ℂ x x := by
  rw [← (normalEigenBasis hA).sum_inner_mul_inner x x]
  push_cast
  exact Finset.sum_congr rfl fun k _ => coordSq_cast hA x k

private theorem sum_coordSq_pos (hA : IsStarNormal A) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ≠ 0) : 0 < ∑ k, coordSq hA x k := by
  rcases (Finset.sum_nonneg fun k (_ : k ∈ univ) => coordSq_nonneg hA x k).lt_or_eq with h | h
  · exact h
  · refine absurd (inner_self_eq_zero (𝕜 := ℂ).1 ?_) hx
    rw [← sum_coordSq hA x, ← h]
    simp

private theorem inner_apply_eq_sum (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ x (A ⬝ x) : ℂ) =
      ∑ k, ((coordSq hA x k : ℝ) : ℂ) * normalEigenvalues hA k := by
  rw [← (normalEigenBasis hA).sum_inner_mul_inner x (A ⬝ x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_normalEigenBasis_apply hA k x, coordSq_cast hA x k]
  ring

/-- **Equation (1.34)** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$ be normal, with
eigenvalues $\lambda_1, \dots, \lambda_n$ and orthonormal eigenvectors $q_1, \dots, q_n$, and
let $x \in \mathbb{C}^n$ be nonzero. Then there are real numbers $\beta_1, \dots, \beta_n \ge 0$
with $\sum_k \beta_k = 1$ and
$$\mu(x) = \sum_{k=1}^n \beta_k \lambda_k.$$

The weights are $\beta_k = |(x, q_k)|^2 / \|x\|_2^2$, read off the expansion of $x$ in the
eigenbasis `SaadSparse.Chapter01.normalEigenBasis`. -/
theorem equation_1_34 (hA : IsStarNormal A) {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0) :
    ∃ β : Fin n → ℝ, (∀ k, 0 ≤ β k) ∧ ∑ k, β k = 1 ∧
      rayleigh A x = ∑ k, (β k : ℂ) * normalEigenvalues hA k := by
  have hpos := sum_coordSq_pos hA hx
  refine ⟨fun k => coordSq hA x k / ∑ j, coordSq hA x j,
    fun k => div_nonneg (coordSq_nonneg hA x k) hpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hpos.ne']
  · rw [rayleigh, inner_apply_eq_sum hA x, ← sum_coordSq hA x, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring

private theorem spectrum_subset_range_normalEigenvalues (hA : IsStarNormal A) :
    spectrum ℂ A ⊆ Set.range (normalEigenvalues hA) := by
  intro μ hμ
  obtain ⟨v, hv, hv0⟩ := Module.End.HasEigenvalue.exists_hasEigenvector
    ((Matrix.hasEigenvalue_toEuclideanLin_iff A μ).2 hμ)
  by_contra hcon
  have hall : ∀ k, (inner ℂ (normalEigenBasis hA k) v : ℂ) = 0 := by
    intro k
    have h1 : (inner ℂ (normalEigenBasis hA k) (A ⬝ v) : ℂ) =
        μ * inner ℂ (normalEigenBasis hA k) v := by
      rw [mem_eigenspace_iff.1 hv, inner_smul_right]
    rw [inner_normalEigenBasis_apply hA k v] at h1
    have h2 : (normalEigenvalues hA k - μ) * inner ℂ (normalEigenBasis hA k) v = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 fun hc => hcon ⟨k, hc⟩)
  exact hv0 (((normalEigenBasis hA).sum_repr' v).symm.trans
    (Finset.sum_eq_zero fun k _ => by rw [hall k, zero_smul]))

private theorem convexCombination_mem_fieldOfValues (hA : IsStarNormal A) {β : Fin n → ℝ}
    (hβ0 : ∀ k, 0 ≤ β k) (hβ1 : ∑ k, β k = 1) :
    (∑ k, (β k : ℂ) * normalEigenvalues hA k) ∈ fieldOfValues A := by
  classical
  set x : EuclideanSpace ℂ (Fin n) :=
    ∑ k, ((Real.sqrt (β k) : ℝ) : ℂ) • normalEigenBasis hA k with hxdef
  have hinner : ∀ k, (inner ℂ (normalEigenBasis hA k) x : ℂ) = ((Real.sqrt (β k) : ℝ) : ℂ) := by
    intro k
    have hortho := orthonormal_iff_ite.1 (normalEigenBasis hA).orthonormal
    rw [hxdef, inner_sum, Finset.sum_eq_single k]
    · rw [inner_smul_right, hortho k k]
      simp
    · intro j _ hj
      rw [inner_smul_right, hortho k j]
      simp [Ne.symm hj]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have hcoord : ∀ k, coordSq hA x k = β k := by
    intro k
    rw [coordSq_def, hinner k, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hβ0 k)]
  have hsum : ∑ k, coordSq hA x k = 1 := by simp only [hcoord]; exact hβ1
  have hx0 : x ≠ 0 := by
    intro hc
    rw [hc] at hsum
    simp [coordSq_def] at hsum
  refine ⟨x, hx0, ?_⟩
  rw [rayleigh, inner_apply_eq_sum hA x, ← sum_coordSq hA x, hsum]
  simp only [hcoord, Complex.ofReal_one, div_one]

/-- **Theorem 1.17** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$ be normal. Then the
field of values of $A$ is the convex hull of its spectrum:
$$F(A) = \operatorname{conv} \sigma(A).$$

The inclusion from left to right is (1.34). The reverse inclusion holds because every convex
combination of eigenvalues is the Rayleigh quotient at a suitable combination of the
eigenvectors. The book deduces the statement from the Toeplitz–Hausdorff theorem, which this
argument does not need. -/
theorem theorem_1_17 {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) :
    fieldOfValues A = convexHull ℝ (spectrum ℂ A) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx0, rfl⟩
    obtain ⟨β, hβ0, hβ1, hβ⟩ := equation_1_34 hA hx0
    rw [hβ]
    refine (convex_convexHull ℝ (spectrum ℂ A)).sum_mem (fun k _ => hβ0 k) hβ1 fun k _ => ?_
    exact subset_convexHull ℝ _ (normalEigenvalues_mem_spectrum hA k)
  · refine convexHull_min ?_ ?_
    · intro μ hμ
      obtain ⟨k, rfl⟩ := spectrum_subset_range_normalEigenvalues hA hμ
      have h := convexCombination_mem_fieldOfValues hA
        (β := fun j => if j = k then (1 : ℝ) else 0)
        (fun j => by by_cases hj : j = k <;> simp [hj]) (by simp)
      have hsum : ∑ j, (((if j = k then (1 : ℝ) else 0) : ℝ) : ℂ) * normalEigenvalues hA j =
          normalEigenvalues hA k := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb
          simp [hb]
        · intro hk
          exact absurd (Finset.mem_univ k) hk
      rwa [hsum] at h
    · rintro z ⟨x, hx0, rfl⟩ w ⟨y, hy0, rfl⟩ a b ha hb hab
      obtain ⟨β, hβ0, hβ1, hβ⟩ := equation_1_34 hA hx0
      obtain ⟨γ, hγ0, hγ1, hγ⟩ := equation_1_34 hA hy0
      have hmem := convexCombination_mem_fieldOfValues hA
        (β := fun k => a * β k + b * γ k)
        (fun k => by have := hβ0 k; have := hγ0 k; positivity)
        (by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hβ1, hγ1,
              mul_one, mul_one, hab])
      have hcalc : ∑ k, ((a * β k + b * γ k : ℝ) : ℂ) * normalEigenvalues hA k =
          a • rayleigh A x + b • rayleigh A y := by
        rw [hβ, hγ, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Complex.real_smul]
        push_cast
        ring
      rwa [hcalc] at hmem

end Normal

/-! ### §1.9.2 Hermitian matrices -/

section Hermitian

variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}

/-- **Theorem 1.19** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be Hermitian, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. Then every eigenvalue of $A$ is real: the spectrum
of $A$ over $\mathbb{K}$ is contained in $\mathbb{R}$. -/
theorem theorem_1_19 (hA : A.IsHermitian) : spectrum 𝕜 A ⊆ Set.range ((↑) : ℝ → 𝕜) := by
  rw [hA.spectrum_eq_image_range]
  rintro _ ⟨r, _, rfl⟩
  exact ⟨_, rfl⟩

/-- **Theorem 1.20** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be Hermitian, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. Then there are a unitary
$Q \in \mathbb{K}^{n \times n}$ and a real vector $d \in \mathbb{R}^n$ with
$$Q^H A Q = \operatorname{diag}(d).$$
So $A$ has an orthonormal basis of eigenvectors.

The proof uses Mathlib's `Matrix.IsHermitian.spectral_theorem` and
`Matrix.IsHermitian.eigenvectorUnitary`. -/
theorem theorem_1_20 (hA : A.IsHermitian) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin n) 𝕜, ∃ d : Fin n → ℝ,
      Qᴴ * A * Q = Matrix.diagonal (RCLike.ofReal ∘ d) := by
  refine ⟨hA.eigenvectorUnitary, (hA.eigenvectorUnitary).2, hA.eigenvalues, ?_⟩
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rwa [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] at h

/-- **Section 1.9.2** of [saad2003iterative], with its converse (Problem P-1.15). Let
$A \in \mathbb{C}^{n \times n}$. Then $(Ax, x)$ is real for every $x \in \mathbb{C}^n$ if and
only if $A$ is Hermitian.

Over $\mathbb{R}$ the direction from real values to symmetry fails, because $(Ax, x)$ is real
for every real matrix $A$. This is why the "positive definite" of the book in §1.11 does not
force symmetry. -/
theorem inner_self_isReal_iff_isHermitian {A : Matrix (Fin n) (Fin n) ℂ} :
    (∀ x : EuclideanSpace ℂ (Fin n), (inner ℂ x (A ⬝ x) : ℂ).im = 0) ↔ A.IsHermitian := by
  constructor
  · intro h
    have hzero : ∀ x : EuclideanSpace ℂ (Fin n),
        (inner ℂ ((toEuclideanLin A - toEuclideanLin Aᴴ) x) x : ℂ) = 0 := by
      intro x
      have him : (inner ℂ ((toEuclideanLin A) x) x : ℂ).im = 0 := by
        have h1 : (inner ℂ ((toEuclideanLin A) x) x : ℂ) =
            (starRingEnd ℂ) (inner ℂ x ((toEuclideanLin A) x)) := (inner_conj_symm _ _).symm
        rw [h1, Complex.conj_im, neg_eq_zero]
        exact h x
      rw [LinearMap.sub_apply, inner_sub_left, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        LinearMap.adjoint_inner_left, ← inner_conj_symm x (toEuclideanLin A x),
        Complex.conj_eq_iff_im.mpr him, sub_self]
    have hsub := (inner_map_self_eq_zero _).1 hzero
    rw [sub_eq_zero] at hsub
    have hAeq : toEuclideanLin Aᴴ = toEuclideanLin A := hsub.symm
    exact Matrix.toEuclideanLin.injective hAeq
  · intro hA x
    have hsym : (toEuclideanLin A).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    have h : conj (inner ℂ x (A ⬝ x) : ℂ) = inner ℂ x (A ⬝ x) := by
      rw [inner_conj_symm]
      exact hsym x x
    exact Complex.conj_eq_iff_im.mp h

/-- **Section 1.9.2** of [saad2003iterative], ordered eigenvalues. For a Hermitian
$A \in \mathbb{K}^{n \times n}$, the eigenvalues $\lambda_1 \ge \lambda_2 \ge \dots \ge
\lambda_n$ of $A$, in the decreasing order of the book, counted with multiplicity.

The indices are $0$-based: the book's $\lambda_k$ is `eigenvaluesDesc hA (k - 1)`. This is the
backbone's `LinearMap.IsSymmetric.eigenvalues` for `Matrix.toEuclideanLin A`. Mathlib's
`Matrix.IsHermitian.eigenvalues` is in no particular order. -/
noncomputable abbrev eigenvaluesDesc (hA : A.IsHermitian) : Fin n → ℝ :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin

/-- **Section 1.9.2** of [saad2003iterative], ordered eigenvectors. For a Hermitian
$A \in \mathbb{K}^{n \times n}$, an orthonormal basis $q_1, \dots, q_n$ of eigenvectors of $A$,
where $q_k$ belongs to the eigenvalue $\lambda_k$ of `SaadSparse.Chapter01.eigenvaluesDesc`. -/
noncomputable abbrev eigenvectorBasisDesc (hA : A.IsHermitian) :
    OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace_fin

/-- For a Hermitian matrix, the eigenvalues $\lambda_1, \dots, \lambda_n$ of
`SaadSparse.Chapter01.eigenvaluesDesc` are decreasing. -/
theorem eigenvaluesDesc_antitone (hA : A.IsHermitian) : Antitone (eigenvaluesDesc hA) :=
  LinearMap.IsSymmetric.eigenvalues_antitone _ _

/-- **Theorem 1.21** of [saad2003iterative] (Courant–Fischer min–max principle), equations (1.37)
and (1.39). Let $A \in \mathbb{K}^{n \times n}$ be Hermitian, with eigenvalues
$\lambda_1 \ge \dots \ge \lambda_n$, and let $1 \le k \le n$. Then
$$\lambda_k = \min_{\dim S = n - k + 1} \ \max_{x \in S, \, x \neq 0} \frac{(Ax, x)}{(x, x)} =
  \max_{\dim S = k} \ \min_{x \in S, \, x \neq 0} \frac{(Ax, x)}{(x, x)},$$
where $S$ ranges over the subspaces of $\mathbb{K}^n$ of the given dimension.

The index is $0$-based in Lean: for `k : Fin n`, the subspaces have dimension `n - k` and
`k + 1`. The minima and maxima are the infimum and the supremum, and the Rayleigh quotient is
the real number `LinearMap.rayleighQuotient`. The proof specializes the backbone's
`LinearMap.IsSymmetric.eigenvalues_eq_iInf_iSup` and
`LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf`. -/
theorem theorem_1_21 (hA : A.IsHermitian) (k : Fin n) :
    eigenvaluesDesc hA k =
        ⨅ S : {S : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) // Module.finrank 𝕜 S = n - (k : ℕ)},
          ⨆ x : {x : EuclideanSpace 𝕜 (Fin n) // x ∈ (S : Submodule 𝕜 _) ∧ x ≠ 0},
            (toEuclideanLin A).rayleighQuotient (x : EuclideanSpace 𝕜 (Fin n)) ∧
      eigenvaluesDesc hA k =
        ⨆ S : {S : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) // Module.finrank 𝕜 S = (k : ℕ) + 1},
          ⨅ x : {x : EuclideanSpace 𝕜 (Fin n) // x ∈ (S : Submodule 𝕜 _) ∧ x ≠ 0},
            (toEuclideanLin A).rayleighQuotient (x : EuclideanSpace 𝕜 (Fin n)) :=
  ⟨LinearMap.IsSymmetric.eigenvalues_eq_iInf_iSup _ _ k,
    LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf _ _ k⟩

/-- **Equation (1.38)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be Hermitian
with $n \ge 1$. Then the largest eigenvalue $\lambda_1$ of $A$ is the greatest value of the
Rayleigh quotient:
$$\lambda_1 = \max_{x \neq 0} \frac{(Ax, x)}{(x, x)}.$$

The dimension is written $n = m + 1$. -/
theorem equation_1_38 {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜} (hA : A.IsHermitian) :
    IsGreatest {c : ℝ | ∃ x : EuclideanSpace 𝕜 (Fin (m + 1)), x ≠ 0 ∧
      (toEuclideanLin A).rayleighQuotient x = c} (eigenvaluesDesc hA 0) := by
  have h := LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace_fin 0
  simpa using h

/-- **Equation (1.40)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be Hermitian
with $n \ge 1$. Then the smallest eigenvalue $\lambda_n$ of $A$ is the least value of the
Rayleigh quotient:
$$\lambda_n = \min_{x \neq 0} \frac{(Ax, x)}{(x, x)}.$$

The dimension is written $n = m + 1$. -/
theorem equation_1_40 {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜} (hA : A.IsHermitian) :
    IsLeast {c : ℝ | ∃ x : EuclideanSpace 𝕜 (Fin (m + 1)), x ≠ 0 ∧
      (toEuclideanLin A).rayleighQuotient x = c} (eigenvaluesDesc hA (Fin.last m)) := by
  set hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  refine ⟨⟨hT.eigenvectorBasis finrank_euclideanSpace_fin (Fin.last m),
    hT.eigenvectorBasis_ne_zero finrank_euclideanSpace_fin _,
    hT.rayleighQuotient_eigenvectorBasis finrank_euclideanSpace_fin _⟩, ?_⟩
  rintro c ⟨x, hx0, rfl⟩
  exact hT.le_rayleighQuotient_of_forall finrank_euclideanSpace_fin
    (fun i => hT.eigenvalues_antitone finrank_euclideanSpace_fin (Fin.le_last i)) hx0

/-- **Theorem 1.22** of [saad2003iterative], equation (1.41). Let $A \in \mathbb{K}^{n \times n}$ be
Hermitian, with eigenvalues $\lambda_1 \ge \dots \ge \lambda_n$ and corresponding orthonormal
eigenvectors $q_1, \dots, q_n$, and let $1 \le k \le n$. Then $\mu(q_k) = \lambda_k$, and
$\lambda_k$ is the greatest value of the Rayleigh quotient on the nonzero vectors orthogonal to
$q_1, \dots, q_{k-1}$:
$$\lambda_k = \max \left\{ \frac{(Ax, x)}{(x, x)} : x \neq 0, \ (x, q_j) = 0 \text{ for } j < k
  \right\}.$$

The index is $0$-based in Lean. The eigenvectors are
`SaadSparse.Chapter01.eigenvectorBasisDesc`. The proof is the backbone's
`LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal`. -/
theorem theorem_1_22 (hA : A.IsHermitian) (k : Fin n) :
    (toEuclideanLin A).rayleighQuotient (eigenvectorBasisDesc hA k) = eigenvaluesDesc hA k ∧
      IsGreatest {c : ℝ | ∃ x : EuclideanSpace 𝕜 (Fin n), x ≠ 0 ∧
        (∀ j < k, inner 𝕜 (eigenvectorBasisDesc hA j) x = 0) ∧
        (toEuclideanLin A).rayleighQuotient x = c} (eigenvaluesDesc hA k) :=
  ⟨LinearMap.IsSymmetric.rayleighQuotient_eigenvectorBasis _ _ k,
    LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal _ _ k⟩

end Hermitian

end SaadSparse.Chapter01
