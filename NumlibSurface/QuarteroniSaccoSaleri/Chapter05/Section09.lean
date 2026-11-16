/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.GeneralizedSchur
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section05

/-!
# Quarteroni, Sacco and Saleri, Section 5.9: The generalized eigenvalue problem

This module formalizes Section 5.9 of [quarteroni2000numerical], the generalized eigenvalue problem
$Ax = \lambda Bx$ for a matrix pencil $(A, B)$ of square matrices. The spectrum of the pencil is
$\sigma(A, B) = \{\mu : \det(A - \mu B) = 0\}$. The pencil is regular when $\det(A - zB)$ is not
identically zero; then $\sigma(A, B)$ is the set of roots of the characteristic polynomial
$p(z) = \det(A - zB)$, and the eigenvalue $\infty$ has multiplicity $n - \deg p$. The module proves
the reduction to a standard eigenvalue problem when $B$ is nonsingular, the generalized Schur
decomposition (Property 5.10) and its real form, and the simultaneous diagonalization of a
symmetric-definite pencil (Theorem 5.7). The proofs specialize `Numlib.Eigen.Pencil` and
`Numlib.LinearAlgebra.Matrix.GeneralizedSchur`.

## Main definitions

* Section 5.9, `QuarteroniSaccoSaleri.Chapter05.pencilSpectrum`: the spectrum
  $\sigma(A, B) = \{\mu : \det(A - \mu B) = 0\}$ of a pencil.
* Section 5.9, `QuarteroniSaccoSaleri.Chapter05.isRegularPencil`: the pencil is regular if
  $\det(A - zB) \neq 0$ for some $z \in \mathbb{C}$.

## Main results

* Equation (5.58), `QuarteroniSaccoSaleri.Chapter05.equation_5_58`: $\mu \in \sigma(A, B)$ if and
  only if $Ax = \mu Bx$ for some $x \neq 0$.
* Equation (5.58), `QuarteroniSaccoSaleri.Chapter05.pencilSpectrum_one`: $\sigma(A, I) = \sigma(A)$.
* Section 5.9, `QuarteroniSaccoSaleri.Chapter05.isRegularPencil_iff`: regularity agrees with the
  backbone definition `Matrix.IsRegularPencil`.
* Section 5.9, `QuarteroniSaccoSaleri.Chapter05.pencilCharpoly`: the spectrum of a regular pencil is
  the set of roots of $p$, and $\infty$ has multiplicity $n - \deg p$.
* Example 5.14, `QuarteroniSaccoSaleri.Chapter05.example_5_14_conj`,
  `QuarteroniSaccoSaleri.Chapter05.example_5_14_infty` and
  `QuarteroniSaccoSaleri.Chapter05.example_5_14_singular`: a symmetric pencil with eigenvalues
  $\pm i$, a regular pencil with the eigenvalue $\infty$, and a singular pencil.
* Section 5.9.1, `QuarteroniSaccoSaleri.Chapter05.pencilSpectrum_eq_spectrum_of_isUnit`: the pencil
  has $n$ finite eigenvalues if and only if $B$ is nonsingular, and then $\sigma(A, B) = \sigma(C)$
  for $BC = A$.
* Property 5.10, `QuarteroniSaccoSaleri.Chapter05.property_5_10`: the generalized Schur
  decomposition $U^H A Z = T$, $U^H B Z = S$ of a regular pencil.
* Section 5.9.1, `QuarteroniSaccoSaleri.Chapter05.generalizedRealSchur_of_isUnit` and
  `QuarteroniSaccoSaleri.Chapter05.generalizedRealSchur`: the generalized real Schur form, first for
  a nonsingular $B$, then for every real pair.
* Theorem 5.7, `QuarteroniSaccoSaleri.Chapter05.theorem_5_7`, with
  `QuarteroniSaccoSaleri.Chapter05.pencilSpectrum_complexify_of_conj` and
  `QuarteroniSaccoSaleri.Chapter05.theorem_5_7_eigenvectors`: a symmetric-definite pencil has real
  eigenvalues and linearly independent eigenvectors, and $A$ and $B$ are simultaneously
  diagonalizable.

## Conventions

* The pencil $(A, B)$ is the pair of matrices. Its spectrum is defined for matrices over any field,
  so that the real pencil of Theorem 5.7 has both a real and a complex spectrum. It is the
  backbone's `Matrix.pencilSpectrum` by definition.
* The characteristic polynomial $p(z) = \det(A - zB)$ is `Matrix.pencilPoly A B`, and the
  multiplicity $n - \deg p$ of the eigenvalue $\infty$ is `Matrix.pencilInftyMultiplicity A B`.
* The book's $U^H$ is `Uᴴ`, its $X^T$ is `Xᵀ`, and a positive definite $B$ is `Matrix.PosDef`. A
  real matrix acts on complex vectors through `Matrix.complexify`.

## Deviations from the source

* **Example 5.14, first pencil** (typo). The source prints $p(z) = z^2 + 1$; the characteristic
  polynomial is $\det(A - zB) = -(z^2 + 1)$, with the same roots. See
  `QuarteroniSaccoSaleri.Chapter05.example_5_14_conj`.
* **Generalized real Schur form, after Property 5.10** (generalization). The source states it for a
  regular pencil; it holds for every pair of real matrices. See
  `QuarteroniSaccoSaleri.Chapter05.generalizedRealSchur`.

## Not formalized

* **Section 5.9.1, the QZ iteration.** The source describes it without a theorem.
* **Section 5.9.2, the QR–Cholesky algorithm.** The source describes it without a theorem.
* **Section 5.9.2, the stability of the QR–Cholesky algorithm.** After the Cholesky factorization
  $B = H^T H$ and $C = H^{-T} A H^{-1}$, the symmetric QR iteration on $C$ returns approximate
  eigenvalues $\hat\lambda$ of the symmetric-definite pencil $(A, B)$. The source claims, citing
  Golub and Van Loan (cited as GL89, p. 464) without proof, that
  $\hat\lambda \in \sigma(H^{-T} A H^{-1} + E)$ with $\|E\|_2 \simeq u \|A\|_2 \|B^{-1}\|_2$. This
  is a relation $\simeq$, not an inequality, so it is not a statement as printed. Moreover the
  printed bound is wrong: the forward error of a triangular solve is the condition number times the
  backward error, so the two solves contribute a factor $\kappa(\hat H) = \kappa(B)^{1/2}$ in
  addition to the factor $\|B^{-1}\|_2 = \|\hat H^{-1}\|_2^2$ that the source records. A correct
  statement must carry $\kappa(\hat H)$, or assume $\|B\|_2 \approx 1$, which is the normalization
  under which the printed bound is right. The backbone has the rounding analysis of the computed
  Cholesky factor (`FloatingPoint.RoundsCholesky`, `FloatingPoint.exists_roundsCholesky_eq_add`) and
  of the computed two-sided triangular solve $\hat C = fl(\hat H^{-T} A \hat H^{-1})$
  (`FloatingPoint.RoundsTwoSidedSolve`,
  `FloatingPoint.frobenius_norm_sub_le_of_roundsTwoSidedSolve`, with the bound $\|\hat C - \hat
  H^{-T} A \hat H^{-1}\|_F \le \frac{2\theta}{(1 - \theta)^2} \|\hat H^{-1}\|_F^2 \|A\|_F$ for
  $\theta = \gamma_n \|\hat H^{-1}\|_F \|\hat H\|_F$). The backward stability of the symmetric QR
  iteration with shifts and deflation on $\hat C$, $\hat\lambda \in \sigma(\hat C + E_2)$, is not
  available.
-/

open Finset Matrix Polynomial

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### The pencil, its spectrum, and regularity -/

/-- **Section 5.9** of [quarteroni2000numerical], the spectrum of a pencil. Let
$A, B \in K^{n \times n}$ over a field $K$. For $z \in K$, $A - zB$ is the **matrix pencil**
$(A, B)$, and its **spectrum** is the set of its eigenvalues $$\sigma(A, B) = \{\mu \in K :
\det(A - \mu B) = 0\}.$$

The source takes $K = \mathbb{C}$. This is the backbone's `Matrix.pencilSpectrum A B` by
definition. -/
def pencilSpectrum {K : Type*} [Field K] (A B : Matrix (Fin n) (Fin n) K) : Set K :=
  {μ | (A - μ • B).det = 0}

/-- **Equation (5.58)** of [quarteroni2000numerical], the generalized eigenvalue problem. Let
$A, B \in K^{n \times n}$ over a field $K$, and let $\mu \in K$. Then $\mu \in \sigma(A, B)$ if
and only if there is a vector $x \in K^n$, $x \neq 0$, with $$Ax = \mu Bx.$$ Such a pair
$(\mu, x)$ is an eigenvalue and eigenvector of the pencil.

The proof specializes `Matrix.mem_pencilSpectrum_iff_exists`. The pair is a
`Matrix.HasPencilEigenvector` of the backbone. -/
theorem equation_5_58 {K : Type*} [Field K] (A B : Matrix (Fin n) (Fin n) K) (μ : K) :
    μ ∈ pencilSpectrum A B ↔ ∃ x : Fin n → K, x ≠ 0 ∧ A *ᵥ x = μ • (B *ᵥ x) :=
  Matrix.mem_pencilSpectrum_iff_exists A B μ

/-- **Equation (5.58)** of [quarteroni2000numerical], the standard problem as a special case. For
$A \in K^{n \times n}$ over a field $K$, setting $B = I_n$ in (5.58) gives the standard
eigenvalue problem: $\sigma(A, I) = \sigma(A)$.

The proof specializes `Matrix.pencilSpectrum_one`. -/
theorem pencilSpectrum_one {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K) :
    pencilSpectrum A 1 = spectrum K A :=
  Matrix.pencilSpectrum_one A

/-- **Section 5.9** of [quarteroni2000numerical], regular pencils. Let
$A, B \in \mathbb{C}^{n \times n}$. The pencil $(A, B)$ is **regular** if $\det(A - zB)$ is not
identically zero, that is, $\det(A - zB) \neq 0$ for some $z \in \mathbb{C}$. Otherwise it is
**singular**. -/
def isRegularPencil (A B : Matrix (Fin n) (Fin n) ℂ) : Prop := ∃ z : ℂ, (A - z • B).det ≠ 0

/-- Let $A, B \in \mathbb{C}^{n \times n}$. The pencil $(A, B)$ is regular in the sense of Section
5.9 of [quarteroni2000numerical] if and only if it is regular in the sense of the backbone
`Matrix.IsRegularPencil`, that is, the polynomial $p(z) = \det(A - zB)$
(`Matrix.pencilPoly A B`) is not the zero polynomial.

A nonzero polynomial over the infinite field $\mathbb{C}$ has a point where it does not vanish,
and $p(z) = \det(A - zB)$ by `Matrix.pencilPoly_eval`. -/
theorem isRegularPencil_iff (A B : Matrix (Fin n) (Fin n) ℂ) :
    isRegularPencil A B ↔ Matrix.IsRegularPencil A B := by
  simp only [isRegularPencil, Matrix.IsRegularPencil, ← Matrix.pencilPoly_eval]
  constructor
  · rintro ⟨z, hz⟩ h
    exact hz (by rw [h, eval_zero])
  · intro h
    by_contra hc
    refine h (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
    have hall : ∀ z : ℂ, (Matrix.pencilPoly A B).IsRoot z := fun z => by
      by_contra hz
      exact hc ⟨z, hz⟩
    rw [show {x | (Matrix.pencilPoly A B).IsRoot x} = Set.univ from Set.eq_univ_of_forall hall]
    exact Set.infinite_univ

/-- **Section 5.9** of [quarteroni2000numerical], the characteristic polynomial of a regular pencil
and the eigenvalue $\infty$. Let $(A, B)$ be a regular pencil of matrices in
$\mathbb{C}^{n \times n}$, and let $p$ be its characteristic polynomial. Then
$p(z) = \det(A - zB)$ for every $z \in \mathbb{C}$, $\mu \in \sigma(A, B)$ if and only if
$p(\mu) = 0$, $\deg p \le n$, and the multiplicity of the eigenvalue $\infty$ is $n - \deg p$.
So if $\deg p = n$ all eigenvalues are finite, and if $k = \deg p < n$ the eigenvalue $\infty$
has multiplicity $n - k$.

The polynomial $p$ is `Matrix.pencilPoly A B`, and the multiplicity of $\infty$ is
`Matrix.pencilInftyMultiplicity A B`. The four facts hold without the regularity hypothesis,
which the proof does not use. The proof specializes `Matrix.pencilPoly_eval`,
`Matrix.mem_pencilSpectrum_iff_isRoot` and `Matrix.natDegree_pencilPoly_le`. -/
theorem pencilCharpoly {A B : Matrix (Fin n) (Fin n) ℂ} (_h : isRegularPencil A B) :
    (∀ z, (Matrix.pencilPoly A B).eval z = (A - z • B).det) ∧
      (∀ μ, μ ∈ pencilSpectrum A B ↔ (Matrix.pencilPoly A B).IsRoot μ) ∧
      (Matrix.pencilPoly A B).natDegree ≤ n ∧
      Matrix.pencilInftyMultiplicity A B = n - (Matrix.pencilPoly A B).natDegree :=
  ⟨Matrix.pencilPoly_eval A B, Matrix.mem_pencilSpectrum_iff_isRoot A B,
    by simpa using Matrix.natDegree_pencilPoly_le A B,
    by rw [Matrix.pencilInftyMultiplicity, Fintype.card_fin]⟩

/-! ### Example 5.14 -/

/-- **Example 5.14** of [quarteroni2000numerical], first pencil. For $$A = \begin{bmatrix} -1 & 0 \\
0 & 1 \end{bmatrix}, \qquad B = \begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix},$$ the
characteristic polynomial is $p(z) = \det(A - zB) = -(z^2 + 1)$, and $\sigma(A, B) = \{i, -i\}$.
So a symmetric pencil, unlike a symmetric matrix, can have complex conjugate eigenvalues.

**Typo.** The source prints $p(z) = z^2 + 1$, which differs from $\det(A - zB)$ by the sign and
has the same roots. -/
theorem example_5_14_conj :
    Matrix.pencilPoly (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 1; 1, 0] = -(X ^ 2 + 1) ∧
      pencilSpectrum (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 1; 1, 0] =
        {Complex.I, -Complex.I} := by
  refine ⟨?_, ?_⟩
  · simp [Matrix.pencilPoly, Matrix.det_fin_two]
    ring
  · ext μ
    simp only [pencilSpectrum, Set.mem_ofPred_eq, Matrix.det_fin_two, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
    rw [← sq_eq_sq_iff_eq_or_eq_neg, Complex.I_sq]
    constructor <;> intro h <;> linear_combination -h

/-- **Example 5.14** of [quarteroni2000numerical], second pencil. For $$A = \begin{bmatrix} -1 & 0
\\ 0 & 0 \end{bmatrix}, \qquad B = \begin{bmatrix} 0 & 0 \\ 0 & 1 \end{bmatrix},$$ the
characteristic polynomial is $p(z) = z$. So the pencil is regular with $\deg p = 1 < 2$, its
finite spectrum is $\sigma(A, B) = \{0\}$, and $\infty$ is an eigenvalue of multiplicity $1$. In
the notation of the source, $\sigma(A, B) = \{0, \infty\}$. -/
theorem example_5_14_infty :
    Matrix.pencilPoly (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1] = X ∧
      isRegularPencil (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1] ∧
      pencilSpectrum (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1] = {0} ∧
      Matrix.pencilInftyMultiplicity (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1]
        = 1 := by
  have hp : Matrix.pencilPoly (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1] = X := by
    simp [Matrix.pencilPoly, Matrix.det_fin_two]
  refine ⟨hp, (isRegularPencil_iff _ _).mpr (by rw [Matrix.IsRegularPencil, hp]; exact X_ne_zero),
    ?_, ?_⟩
  · ext μ
    rw [pencilSpectrum, Set.mem_ofPred_eq, ← Matrix.pencilPoly_eval, hp, eval_X]
    rfl
  · rw [Matrix.pencilInftyMultiplicity, hp, natDegree_X, Fintype.card_fin]

/-- **Example 5.14** of [quarteroni2000numerical], third pencil. For $$A = \begin{bmatrix} 1 & 2 \\
0 & 0 \end{bmatrix}, \qquad B = \begin{bmatrix} 1 & 0 \\ 0 & 0 \end{bmatrix},$$ the
characteristic polynomial is $p(z) = 0$. So the pencil is singular, and
$\sigma(A, B) = \mathbb{C}$.

The proof uses `Matrix.pencilSpectrum_eq_univ_of_not_isRegularPencil`. -/
theorem example_5_14_singular :
    Matrix.pencilPoly (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![1, 0; 0, 0] = 0 ∧
      ¬ isRegularPencil (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![1, 0; 0, 0] ∧
      pencilSpectrum (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![1, 0; 0, 0] = Set.univ := by
  have hp : Matrix.pencilPoly (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![1, 0; 0, 0] = 0 := by
    simp [Matrix.pencilPoly, Matrix.det_fin_two]
  have hreg : ¬ Matrix.IsRegularPencil (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![1, 0; 0, 0] :=
    fun h => h hp
  exact ⟨hp, fun h => hreg ((isRegularPencil_iff _ _).mp h),
    Matrix.pencilSpectrum_eq_univ_of_not_isRegularPencil hreg⟩

/-! ### Section 5.9.1: reduction to a standard problem, and the generalized Schur form -/

/-- **Section 5.9.1** of [quarteroni2000numerical], reduction to a standard problem. Let
$A, B \in \mathbb{C}^{n \times n}$. The pencil $(A, B)$ has $n$ finite eigenvalues, that is, its
characteristic polynomial has degree $n$, if and only if $B$ is nonsingular. If $B$ is
nonsingular, then for every $C$ with $BC = A$, problem (5.58) is equivalent to the standard
eigenvalue problem $Cx = \lambda x$: $$\sigma(A, B) = \sigma(C).$$

The proof specializes `Matrix.natDegree_pencilPoly_eq_card_iff` and
`Matrix.pencilSpectrum_eq_spectrum_of_isUnit`. -/
theorem pencilSpectrum_eq_spectrum_of_isUnit (A B : Matrix (Fin n) (Fin n) ℂ) :
    ((Matrix.pencilPoly A B).natDegree = n ↔ IsUnit B) ∧
      (IsUnit B → ∀ C, B * C = A → pencilSpectrum A B = spectrum ℂ C) := by
  refine ⟨?_, fun hB C hC => ?_⟩
  · have h := Matrix.natDegree_pencilPoly_eq_card_iff A B
    rw [Fintype.card_fin] at h
    rw [h, isUnit_iff_isUnit_det]
  · have hC' : C = B⁻¹ * A := by
      rw [← hC, ← Matrix.mul_assoc, nonsing_inv_mul B ((isUnit_iff_isUnit_det B).mp hB),
        Matrix.one_mul]
    rw [hC']
    exact Matrix.pencilSpectrum_eq_spectrum_of_isUnit A hB

/-- **Property 5.10** of [quarteroni2000numerical] (generalized Schur decomposition). Let $(A, B)$
be a regular pencil of matrices in $\mathbb{C}^{n \times n}$. Then there are unitary matrices
$U, Z \in \mathbb{C}^{n \times n}$ such that $$U^H A Z = T \quad \text{and} \quad U^H B Z = S$$
are upper triangular. The eigenvalues of $(A, B)$ are $\lambda_i = t_{ii} / s_{ii}$ if
$s_{ii} \neq 0$ and $\lambda_i = \infty$ if $s_{ii} = 0$: precisely, $$\sigma(A, B) = \{t_{ii} /
s_{ii} : s_{ii} \neq 0\},$$ and $t_{ii} \neq 0$ for every $i$ with $s_{ii} = 0$.

The proof specializes `Matrix.exists_unitary_pencil_isUpperTriangular` (a Schur form and a QR
factorization), `Matrix.pencilSpectrum_eq_of_isUpperTriangular` and
`Matrix.pencilSpectrum_mul_mul_of_isUnit`. A diagonal position with $t_{ii} = s_{ii} = 0$ would
make every $\mu$ an eigenvalue, but the spectrum of a regular pencil is finite. -/
theorem property_5_10 {A B : Matrix (Fin n) (Fin n) ℂ} (hreg : isRegularPencil A B) :
    ∃ U ∈ unitaryGroup (Fin n) ℂ, ∃ Z ∈ unitaryGroup (Fin n) ℂ,
      (Uᴴ * A * Z).IsUpperTriangular ∧ (Uᴴ * B * Z).IsUpperTriangular ∧
        pencilSpectrum A B =
          {μ | ∃ i, (Uᴴ * B * Z) i i ≠ 0 ∧ μ = (Uᴴ * A * Z) i i / (Uᴴ * B * Z) i i} ∧
        ∀ i, (Uᴴ * B * Z) i i = 0 → (Uᴴ * A * Z) i i ≠ 0 := by
  have hreg' := (isRegularPencil_iff A B).mp hreg
  obtain ⟨U, hU, Z, hZ, hT, hS⟩ := Matrix.exists_unitary_pencil_isUpperTriangular hreg'
  rw [star_eq_conjTranspose] at hT hS
  have hUs : IsUnit Uᴴ := ⟨Unitary.toUnits ⟨Uᴴ, Unitary.star_mem hU⟩, rfl⟩
  have hZu : IsUnit Z := ⟨Unitary.toUnits ⟨Z, hZ⟩, rfl⟩
  have hσ : pencilSpectrum A B = {μ | ∃ i, (Uᴴ * A * Z) i i = μ * (Uᴴ * B * Z) i i} := by
    rw [pencilSpectrum, ← Matrix.pencilSpectrum_eq_of_isUpperTriangular hT hS,
      Matrix.pencilSpectrum_mul_mul_of_isUnit A B hUs hZu]
    rfl
  have hinf : ∀ i, (Uᴴ * B * Z) i i = 0 → (Uᴴ * A * Z) i i ≠ 0 := by
    intro i hSi hTi
    have huniv : pencilSpectrum A B = Set.univ := by
      rw [hσ]
      exact Set.eq_univ_of_forall fun μ => ⟨i, by rw [hSi, hTi, mul_zero]⟩
    have hfin : (pencilSpectrum A B).Finite := hreg'.finite_pencilSpectrum
    rw [huniv] at hfin
    exact Set.infinite_univ hfin
  refine ⟨U, hU, Z, hZ, hT, hS, ?_, hinf⟩
  rw [hσ]
  ext μ
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi⟩
    have hSi : (Uᴴ * B * Z) i i ≠ 0 := fun h => hinf i h (by rw [hi, h, mul_zero])
    exact ⟨i, hSi, by rw [hi, mul_div_cancel_right₀ _ hSi]⟩
  · rintro ⟨i, hSi, rfl⟩
    exact ⟨i, by rw [div_mul_cancel₀ _ hSi]⟩

/-! ### Section 5.9.2: symmetric-definite pencils -/

/-- Let $A, B, X \in \mathbb{R}^{n \times n}$ with $X$ nonsingular, and let
$\lambda_1, \dots, \lambda_n \in \mathbb{R}$ with $X^T A X = \operatorname{diag}(\lambda_1,
\dots, \lambda_n)$ and $X^T B X = I$. Then the complex spectrum of the pencil $(A, B)$ is
$\{\lambda_1, \dots, \lambda_n\} \subset \mathbb{C}$. This is the clause of Theorem 5.7 of
[quarteroni2000numerical] that the eigenvalues are real.

The matrices act on $\mathbb{C}^n$ through `Matrix.complexify`. The proof uses
`Matrix.pencilSpectrum_mul_mul_of_isUnit` and `Matrix.pencilSpectrum_diagonal` for the
complexified matrices. -/
theorem pencilSpectrum_complexify_of_conj {A B X : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hX : IsUnit X) (hA : Xᵀ * A * X = diagonal lam) (hB : Xᵀ * B * X = 1) :
    pencilSpectrum (complexify A) (complexify B) = Set.range fun i => (lam i : ℂ) := by
  have hX' : IsUnit (complexify X) := (isUnit_complexify_iff X).mpr hX
  have hXt : IsUnit (complexify X)ᵀ := (isUnit_transpose _).mpr hX'
  change Matrix.pencilSpectrum (complexify A) (complexify B) = _
  rw [← Matrix.pencilSpectrum_mul_mul_of_isUnit (complexify A) (complexify B) hXt hX',
    ← complexify_transpose, ← complexify_mul, ← complexify_mul, ← complexify_mul,
    ← complexify_mul, hA, hB, complexify_one, complexify, diagonal_map Complex.ofReal_zero,
    ← diagonal_one, Matrix.pencilSpectrum_diagonal]
  ext μ
  simp [eq_comm]

/-- **Theorem 5.7** of [quarteroni2000numerical]. Let $A, B \in \mathbb{R}^{n \times n}$ be
symmetric, with $B$ positive definite, so that $(A, B)$ is a symmetric-definite pencil. Then $A$
and $B$ can be simultaneously diagonalized: there are a nonsingular
$X \in \mathbb{R}^{n \times n}$ and real numbers $\lambda_1, \dots, \lambda_n$ with $$X^T A X =
\Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_n), \qquad X^T B X = I_n.$$ The
$\lambda_i$ are the eigenvalues of the pencil: both its real spectrum and its complex spectrum
are $\{\lambda_1, \dots, \lambda_n\}$. In particular all eigenvalues of the pencil are real.

The clause that the eigenvectors are linearly independent is
`QuarteroniSaccoSaleri.Chapter05.theorem_5_7_eigenvectors`. The proof specializes
`Matrix.exists_simultaneous_diagonalization` over $\mathbb{R}$, with any $W$ such that
$W^T B W = I$ in place of the inverse of the Cholesky factor $H$ of $B$ that the source uses,
and `QuarteroniSaccoSaleri.Chapter05.pencilSpectrum_complexify_of_conj` for the complex
spectrum. -/
theorem theorem_5_7 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.PosDef) :
    ∃ (X : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ), IsUnit X ∧
      Xᵀ * A * X = diagonal lam ∧ Xᵀ * B * X = 1 ∧
      pencilSpectrum A B = Set.range lam ∧
      pencilSpectrum (complexify A) (complexify B) = Set.range fun i => (lam i : ℂ) := by
  obtain ⟨X, lam, hX, hBX, hAX, hσ⟩ :=
    Matrix.exists_simultaneous_diagonalization (isHermitian_iff_isSymm.mpr hA) hB
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hBX hAX
  simp only [RCLike.ofReal_real_eq_id, id] at hAX hσ
  exact ⟨X, lam, hX, hAX, hBX, hσ, pencilSpectrum_complexify_of_conj hX hAX hBX⟩

/-- **Theorem 5.7** of [quarteroni2000numerical], the eigenvectors. Let
$A, B, X \in \mathbb{R}^{n \times n}$ with $X$ nonsingular, and let
$\lambda_1, \dots, \lambda_n \in \mathbb{R}$ with $X^T A X = \operatorname{diag}(\lambda_1,
\dots, \lambda_n)$ and $X^T B X = I$. Then the columns $x_i$ of $X$ are eigenvectors of the
pencil, $$A x_i = \lambda_i B x_i \quad \text{for all } i,$$ and they are linearly independent.

The proof specializes `Matrix.hasPencilEigenvector_col_of_conj_eq_diagonal` and
`Matrix.linearIndependent_cols_iff_isUnit`. -/
theorem theorem_5_7_eigenvectors {A B X : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hX : IsUnit X) (hA : Xᵀ * A * X = diagonal lam) (hB : Xᵀ * B * X = 1) :
    (∀ i, A *ᵥ X.col i = lam i • (B *ᵥ X.col i)) ∧ LinearIndependent ℝ X.col := by
  refine ⟨fun i => ?_, linearIndependent_col_iff_isUnit.mpr hX⟩
  have hB' : star X * B * X = 1 := by
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hA' : star X * A * X = diagonal lam := by
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  exact (Matrix.hasPencilEigenvector_col_of_conj_eq_diagonal hX hB' hA' i).2

/-- **Section 5.9.1** of [quarteroni2000numerical], the generalized real Schur form for a
nonsingular $B$. Let $A, B \in \mathbb{R}^{n \times n}$ with $B$ nonsingular. Then there are
orthogonal matrices $\tilde U, \tilde Z \in \mathbb{R}^{n \times n}$ such that
$\tilde T = \tilde U^T A \tilde Z$ is upper quasi-triangular and
$\tilde S = \tilde U^T B \tilde Z$ is upper triangular. Here upper quasi-triangular means block
upper triangular with diagonal blocks of order $1$ or $2$.

The source states this form after Property 5.10, without proof and with a reference to Golub and
Van Loan (cited as GL89, §7.7). As in the description of the QZ iteration in the source, which
applies the QR algorithm to $A B^{-1}$, the proof assumes that $B$ is nonsingular. It takes
$\tilde Z$ from the real Schur form of $B^{-1} A$ (Property 5.8), so that
$\tilde Z^T B^{-1} A \tilde Z = T$ is upper quasi-triangular, and $\tilde U$ from a QR
factorization $B \tilde Z = \tilde U R$ (Definition 3.1). Then $\tilde U^T B \tilde Z = R$ is
upper triangular, and $\tilde U^T A \tilde Z = RT$ is upper quasi-triangular. The
quasi-triangular shape is that of Property 5.8: `Matrix.BlockTriangular p` for a monotone
`p : Fin n → ℕ` whose fibres have at most two elements. -/
theorem generalizedRealSchur_of_isUnit {A B : Matrix (Fin n) (Fin n) ℝ} (hB : IsUnit B.det) :
    ∃ U ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ, ∃ p : Fin n → ℕ,
      Monotone p ∧ (∀ k, #{i | p i = k} ≤ 2) ∧
        (Uᵀ * A * Z).BlockTriangular p ∧ (Uᵀ * B * Z).IsUpperTriangular := by
  obtain ⟨Z, hZ, p, hmono, hcard, htri, -⟩ := property_5_8 (B⁻¹ * A)
  obtain ⟨U, hU, R, hR, -, hBZ⟩ :=
    (Chapter03.definition_3_1_iff (B * Z)).1.1 (Chapter03.definition_3_1_iff (B * Z)).2
  have hZZ : Z * Zᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ ℝ).1 hZ
  have hUU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' _ ℝ).1 hU
  have hkey : Uᵀ * B * Z = R := by
    rw [Matrix.mul_assoc, hBZ, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hRtri : R.IsUpperTriangular := fun i j hij => hR i j hij
  refine ⟨U, hU, Z, hZ, p, hmono, hcard, ?_, by rw [hkey]; exact hRtri⟩
  have hAZ : R * (Zᵀ * (B⁻¹ * A) * Z) = Uᵀ * A * Z := by
    rw [← hkey]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Z Zᵀ, hZZ, Matrix.one_mul, ← Matrix.mul_assoc B B⁻¹,
      Matrix.mul_nonsing_inv B hB, Matrix.one_mul]
  rw [← hAZ]
  refine Matrix.BlockTriangular.mul (fun i j hij => hRtri ?_) htri
  by_contra hji
  exact absurd (hmono (not_lt.1 hji)) (not_le.2 hij)

/-- **Section 5.9.1** of [quarteroni2000numerical], the generalized real Schur form. Let
$A, B \in \mathbb{R}^{n \times n}$. Then there are orthogonal matrices
$\tilde U, \tilde Z \in \mathbb{R}^{n \times n}$ such that $\tilde T = \tilde U^T A \tilde Z$ is
upper quasi-triangular (block upper triangular with diagonal blocks of order $1$ or $2$) and
$\tilde S = \tilde U^T B \tilde Z$ is upper triangular.

**Generalization.** The source states this form after Property 5.10 for a regular pencil,
without proof and with a reference to Golub and Van Loan (cited as GL89, §7.7). It holds with no
hypothesis on the pencil.

The quasi-triangular shape is that of Property 5.8: `Matrix.BlockTriangular p` for a monotone
`p : Fin n → ℕ` whose fibres have at most two elements. The proof specializes
`Matrix.exists_orthogonal_pencil_isQuasiUpperTriangular`, which applies
`QuarteroniSaccoSaleri.Chapter05.generalizedRealSchur_of_isUnit` to $(A, B + \varepsilon I)$ and
takes the limit $\varepsilon \to 0$ in the compact orthogonal group. -/
theorem generalizedRealSchur (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ, ∃ p : Fin n → ℕ,
      Monotone p ∧ (∀ k, #{i | p i = k} ≤ 2) ∧
        (Uᵀ * A * Z).BlockTriangular p ∧ (Uᵀ * B * Z).IsUpperTriangular := by
  obtain ⟨U, hU, Z, hZ, ⟨p, hp, hcard, hA⟩, hB⟩ :=
    Matrix.exists_orthogonal_pencil_isQuasiUpperTriangular A B
  exact ⟨U, hU, Z, hZ, p, hp, hcard, hA, hB⟩

end QuarteroniSaccoSaleri.Chapter05
