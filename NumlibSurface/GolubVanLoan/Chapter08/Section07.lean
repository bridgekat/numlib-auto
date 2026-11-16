/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Numlib.Eigen.Pencil
import Numlib.Eigen.SymmetricPencil
import Numlib.LinearAlgebra.Matrix.SVD
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter04.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter06.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section03
import NumlibSurface.GolubVanLoan.Chapter08.Section01

/-!
# Golub and Van Loan, Section 8.7: Generalized eigenvalue problems with symmetry

This module formalizes §8.7 of [golub2013matrix], the generalized eigenvalue problem
$Ax = \lambda Bx$ with symmetry. For a symmetric-definite pencil $A - \lambda B$, with $A$ symmetric
and $B$ positive definite, it proves that congruence preserves the eigenvalues, that $A$ and $B$ can
be diagonalized by one congruence (Theorem 8.7.1, Corollary 8.7.2), and a corrected form of the
perturbation bound of Theorem 8.7.3 in terms of the Crawford number (8.7.4). It states Algorithm
8.7.1, which reduces the pencil to a symmetric eigenvalue problem through the Cholesky factorization
of $B$, and the generalized Rayleigh quotient (8.7.5)–(8.7.8). For $A \in \mathbb{R}^{m_1 \times n}$
and $B \in \mathbb{R}^{m_2 \times n}$ it treats the generalized singular value decomposition (GSVD)
$U_1^T A X = D_A$, $U_2^T B X = D_B$: Theorem 8.7.4, the relations between its columns, Algorithm
8.7.2, and the $2 \times 2$ step of the Kogbetliantz approach. Last, it treats the quadratic
eigenvalue problem $(\lambda^2 M + \lambda C + K) x = 0$ of (8.7.12): the scalar equation
(8.7.13)–(8.7.14), the linearizations (8.7.15)–(8.7.16), the real parts of the eigenvalues in the
damped and the gyroscopic cases, and palindromic problems (8.7.17)–(8.7.18).

The proofs specialize the backbone modules `Numlib.Eigen.Pencil` (the eigenvalues of a pencil),
`Numlib.Eigen.SymmetricPencil` (the sorted eigenvalues of a symmetric-definite pencil and the
Crawford number) and `Numlib.LinearAlgebra.Matrix.SVD`. The algorithms call the programs of Chapters
3–5 of the library.

## Main definitions

* Equation (8.7.4), `GolubVanLoan.Chapter08.crawfordNumber`: the Crawford number $c(A, B) =
  \min_{\|x\|_2 = 1} \sqrt{(x^T A x)^2 + (x^T B x)^2}$.
* Algorithm 8.7.1, `GolubVanLoan.Chapter08.algorithm_8_7_1`: the symmetric-definite problem through
  the Cholesky factorization $B = GG^T$ and the Schur decomposition of $G^{-1} A G^{-T}$.
* Equation (8.7.5), `GolubVanLoan.Chapter08.generalizedRayleighQuotientIteration`: the generalized
  Rayleigh quotient iteration.
* Algorithm 8.7.2, `GolubVanLoan.Chapter08.algorithm_8_7_2`: the GSVD of a tall pair through a QR
  factorization and a CS decomposition.

## Main results

* §8.7.1, `GolubVanLoan.Chapter08.pencil_congruence`: for nonsingular $X$,
  $\lambda(X^T A X, X^T B X) = \lambda(A, B)$.
* Theorem 8.7.1, `GolubVanLoan.Chapter08.theorem_8_7_1`: if some $C(\mu) = \mu A + (1 - \mu) B$ with
  $\mu \in [0, 1]$ is positive semidefinite with $\operatorname{null}(C(\mu)) =
  \operatorname{null}(A) \cap \operatorname{null}(B)$, then one congruence diagonalizes $A$ and $B$.
* Corollary 8.7.2, `GolubVanLoan.Chapter08.corollary_8_7_2`: a symmetric-definite pencil is
  diagonalized by a congruence whose columns are eigenvectors.
* Theorem 8.7.3, `GolubVanLoan.Chapter08.theorem_8_7_3`: the corrected perturbation bound $\sin
  |\arctan \lambda_i - \arctan \mu_i| \le \epsilon / c(A, B)$.
* Theorem 8.7.3, `GolubVanLoan.Chapter08.theorem_8_7_3_counterexample`: the bound as printed fails
  for a $1 \times 1$ pencil.
* Algorithm 8.7.1, `GolubVanLoan.Chapter08.algorithm_8_7_1_spec`: in exact arithmetic the output
  $(X, a)$ satisfies $X^T A X = \operatorname{diag}(a)$ and $X^T B X = I$.
* §8.7.2, `GolubVanLoan.Chapter08.pencil_eq_cholesky_spectrum`: $\lambda(A, B)$ is the spectrum of
  $G^{-1} A G^{-T}$ and the set of the numbers $a_i$ that Algorithm 8.7.1 returns.
* Equation (8.7.5), `GolubVanLoan.Chapter08.generalizedRayleighQuotientIteration_succ`: the
  iteration is Rayleigh quotient iteration on $B^{-1} A$.
* Equation (8.7.7), `GolubVanLoan.Chapter08.equation_8_7_7`: $x^T A x / x^T B x$ minimizes
  $\|Ax - \lambda Bx\|_{B^{-1}}$.
* Equation (8.7.8), `GolubVanLoan.Chapter08.equation_8_7_8`: generalized orthogonal iteration is
  orthogonal iteration on $B^{-1} A$.
* Theorem 8.7.4, `GolubVanLoan.Chapter08.theorem_8_7_4`: the GSVD of a tall pair exists.
* §8.7.4, `GolubVanLoan.Chapter08.gsvd_columns_and_pencil`: the column relations of a GSVD and the
  eigenvalues of $A^T A - \lambda B^T B$.
* Algorithm 8.7.2, `GolubVanLoan.Chapter08.algorithm_8_7_2_spec`: in exact arithmetic the algorithm
  computes a GSVD.
* §8.7.5, `GolubVanLoan.Chapter08.gsvd_subspace_via_rq`: an RQ factorization of $V^T R$ gives
  orthonormal bases of the spans of the leading columns of $X$.
* §8.7.7, `GolubVanLoan.Chapter08.kogbetliantz_twoByTwo`: the $2 \times 2$ step of the Kogbetliantz
  approach.
* Equations (8.7.13)–(8.7.14), `GolubVanLoan.Chapter08.equation_8_7_13`: an eigenpair of the
  quadratic problem gives the scalar equation $m\lambda^2 + c\lambda + k = 0$.
* Equations (8.7.15)–(8.7.16), `GolubVanLoan.Chapter08.equation_8_7_15`: the two linearizations of
  the quadratic problem.
* §8.7.9, `GolubVanLoan.Chapter08.qep_re_nonpos`: with $M$, $C$ positive definite and $K$ positive
  semidefinite, every eigenvalue has nonpositive real part.
* §8.7.9, `GolubVanLoan.Chapter08.gyroscopic_eigenvalues_imaginary`: the eigenvalues of a gyroscopic
  problem with $K$ positive semidefinite are purely imaginary.
* §8.7.9, `GolubVanLoan.Chapter08.gyroscopic_counterexample`: without $K \succeq 0$ an eigenvalue
  can have nonzero real part.
* §8.7.9, `GolubVanLoan.Chapter08.palindromic_reciprocal`: the eigenvalues of a palindromic problem
  come in pairs $\lambda$, $1/\lambda$.
* Equation (8.7.18), `GolubVanLoan.Chapter08.equation_8_7_18`: a solution of the linearization
  (8.7.17) gives an eigenvector $y + z$ of the palindromic problem.

## Conventions

* $\lambda(A, B)$ is `Matrix.pencilSpectrum A B`, the set $\{\lambda : \det(A - \lambda B) = 0\}$. A
  symmetric-definite pencil has $A$ symmetric (`Matrix.IsSymm`) and $B$ positive definite
  (`Matrix.PosDef`). Its eigenvalues $\lambda_1 \ge \dots \ge \lambda_n$ are
  `Matrix.pencilEigenvalues`, with 0-based indices.
* A nonsingular matrix $X$ is `IsUnit X.det` or `IsUnit X`, and an orthogonal matrix is a member of
  `Matrix.orthogonalGroup`. The rectangular diagonal matrices $D_A$ and $D_B$ of a GSVD are
  `Matrix.rectDiagonal`.
* The quadratic eigenvalue problem is stated over $\mathbb{C}$, where $\lambda$ and $x$ live. A real
  symmetric (skew-symmetric, positive definite) matrix is in particular a complex Hermitian
  (skew-Hermitian, positive definite) matrix, so the hypotheses on $M$, $C$ and $K$ are stated in
  the complex Hermitian form.

## Implementation notes

* Algorithms 8.7.1 and 8.7.2 are programs generic in a monad `M` and a rounding hook `rnd`, as in
  the algorithm conventions of `NumlibSurface.GolubVanLoan`. They call the programs of Chapters 3–5:
  the Cholesky factorization (Algorithm 4.2.1), forward and back substitution (Algorithms 3.1.1 and
  3.1.2), and modified Gram–Schmidt (Algorithm 5.2.6). A triangular solve with a matrix right-hand
  side runs column by column.
* The two steps that have no exact program, the symmetric Schur decomposition and the CS
  decomposition, are monadic parameters of the programs, and the exact-semantics theorems assume
  their specifications (convention 5 of the library).
* Equation (8.7.8) is stated with the orthogonal iteration
  `GolubVanLoan.Chapter07.orthogonalIteration` of Chapter 7.
* Theorem 8.7.4 restates Theorem 6.1.1 of Chapter 6 (`GolubVanLoan.Chapter06.theorem_6_1_1`), whose
  number $p = \max(r - m_2, 0)$ is $0$ when $B$ has at least as many rows as columns.

## Deviations from the source

* **Equation (8.7.4)** (correction). The source's display of the Crawford number has no square root.
  The definition takes the square root, which the ratio $\epsilon / c(A, B)$ of Theorem 8.7.3 needs.
  See `GolubVanLoan.Chapter08.crawfordNumber`.
* **Theorem 8.7.3** (correction). The printed bound $|\arctan \lambda_i - \arctan \mu_i| \le
  \arctan(\epsilon / c(A, B))$ is false. The library proves $\sin |\arctan \lambda_i - \arctan
  \mu_i| \le \epsilon / c(A, B)$ and assumes that $B + E_B$ is positive definite. See
  `GolubVanLoan.Chapter08.theorem_8_7_3` and `GolubVanLoan.Chapter08.theorem_8_7_3_counterexample`.
* **Algorithm 8.7.1** (typo). The source cites Algorithm 4.2.2 for the Cholesky factorization. The
  intended algorithm is Algorithm 4.2.1. See `GolubVanLoan.Chapter08.algorithm_8_7_1`.
* **Algorithm 8.7.2** (typo). The source writes the hypothesis as $\operatorname{null}(A) \cap
  \operatorname{null}(B) = \emptyset$. The intended hypothesis is $\operatorname{null}(A) \cap
  \operatorname{null}(B) = \{0\}$. See `GolubVanLoan.Chapter08.algorithm_8_7_2_spec`.
* **§8.7.7** (typo). The source prints $U_1^T F = (U_2^T G) \Sigma$. The correct identity is
  $U_1^T F = \Sigma (U_2^T G)$. See `GolubVanLoan.Chapter08.kogbetliantz_twoByTwo`.
* **§8.7.9, gyroscopic systems** (correction). The source says that the eigenvalues are purely
  imaginary. This holds only when $K$ is positive semidefinite, which the library assumes. See
  `GolubVanLoan.Chapter08.gyroscopic_eigenvalues_imaginary` and
  `GolubVanLoan.Chapter08.gyroscopic_counterexample`.

## Not formalized

* The overdamping theorem of §8.7.9, which the source quotes from Duffin and Veselić.
* The characterization of the generalized singular values as stationary values.
* The product SVD and the restricted SVD of §8.7.8.
* The accuracy discussion of §8.7.6.
-/

open Matrix

namespace GolubVanLoan.Chapter08

variable {n : ℕ}

/-! ### §8.7.1 Mathematical background -/

/-- **§8.7.1** of [golub2013matrix], invariance under congruence. Let
$A, B, X \in \mathbb{R}^{n \times n}$ with $X$ nonsingular. Then $A - \lambda B$ is singular if
and only if $X^T A X - \lambda X^T B X$ is singular, that is,
$$\lambda(X^T A X, X^T B X) = \lambda(A, B).$$

No symmetry is assumed. The sets are `Matrix.pencilSpectrum`. -/
theorem pencil_congruence (A B : Matrix (Fin n) (Fin n) ℝ) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsUnit X.det) : pencilSpectrum (Xᵀ * A * X) (Xᵀ * B * X) = pencilSpectrum A B := by
  have hXu : IsUnit X := (isUnit_iff_isUnit_det X).2 hX
  have hXt : IsUnit Xᵀ := (isUnit_iff_isUnit_det Xᵀ).2 (by rw [det_transpose]; exact hX)
  exact pencilSpectrum_mul_mul_of_isUnit A B hXt hXu

/-- **Theorem 8.7.1** of [golub2013matrix]. Let $A, B \in \mathbb{R}^{n \times n}$ be symmetric, and
let $C(\mu) = \mu A + (1 - \mu) B$ as in (8.7.3). If some $\mu \in [0, 1]$ makes $C(\mu)$
positive semidefinite with
$$\operatorname{null}(C(\mu)) = \operatorname{null}(A) \cap \operatorname{null}(B),$$
then there is a nonsingular $X \in \mathbb{R}^{n \times n}$ such that $X^T A X$ and $X^T B X$
are both diagonal.

The null space condition is stated pointwise: $C(\mu) x = 0$ if and only if $Ax = 0$ and
$Bx = 0$. -/
theorem theorem_8_7_1 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.IsSymm) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hC : (μ • A + (1 - μ) • B).PosSemidef)
    (hker : ∀ x, (μ • A + (1 - μ) • B) *ᵥ x = 0 ↔ A *ᵥ x = 0 ∧ B *ᵥ x = 0) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ, IsUnit X ∧ ∃ a b : Fin n → ℝ,
      Xᵀ * A * X = diagonal a ∧ Xᵀ * B * X = diagonal b := by
  obtain ⟨X, hX, a, b, ha, hb⟩ := exists_isUnit_conj_diagonal_of_posSemidef_combination (𝕜 := ℝ)
    (isHermitian_iff_isSymm.2 hA) (isHermitian_iff_isSymm.2 hB) hμ (by simpa using hC)
    (by simpa using hker)
  refine ⟨X, hX, a, b, ?_, ?_⟩
  · simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using ha
  · simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hb

/-- **Corollary 8.7.2** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric and
$B \in \mathbb{R}^{n \times n}$ positive definite. Then there is a nonsingular
$X = [x_1 | \cdots | x_n]$ and vectors $a, b \in \mathbb{R}^n$ with
$$X^T A X = \operatorname{diag}(a_1, \dots, a_n), \qquad X^T B X = \operatorname{diag}(b_1,
  \dots, b_n),$$
and $A x_i = \lambda_i B x_i$ with $\lambda_i = a_i / b_i$ for every $i$. -/
theorem corollary_8_7_2 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.PosDef) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ, IsUnit X ∧ ∃ a b : Fin n → ℝ,
      Xᵀ * A * X = diagonal a ∧ Xᵀ * B * X = diagonal b ∧
        ∀ i, A *ᵥ X.col i = (a i / b i) • (B *ᵥ X.col i) := by
  obtain ⟨M, d, hM, hMB, hMA, -⟩ := exists_simultaneous_diagonalization (𝕜 := ℝ)
    (isHermitian_iff_isSymm.2 hA) hB
  have hMA' : star M * A * M = diagonal d := by simpa using hMA
  refine ⟨M, hM, d, 1, ?_, ?_, fun i => ?_⟩
  · simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hMA'
  · simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hMB
  · have h := (hasPencilEigenvector_col_of_conj_eq_diagonal hM hMB hMA' i).2
    simpa using h

/-- **Equation (8.7.4)** of [golub2013matrix] (the Crawford number). For
$A, B \in \mathbb{R}^{n \times n}$, the **Crawford number** is
$$c(A, B) = \min_{\|x\|_2 = 1} \sqrt{(x^T A x)^2 + (x^T B x)^2}.$$

**Correction.** The source's display has no square root. With the square root, $c(A, B)$ scales
like the matrices, which the ratio $\epsilon / c(A, B)$ of Theorem 8.7.3 needs.

The definition is the backbone's `Matrix.crawfordNumber`, an infimum over the unit sphere. It is
$0$ for $n = 0$, where the sphere is empty. -/
noncomputable def crawfordNumber (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.crawfordNumber A B

/-- **Theorem 8.7.3** of [golub2013matrix], corrected. Let $A - \lambda B$ be symmetric-definite,
with $A \in \mathbb{R}^{n \times n}$ symmetric and $B$ positive definite, and with eigenvalues
$\lambda_1 \ge \dots \ge \lambda_n$. Let $E_A, E_B \in \mathbb{R}^{n \times n}$ be such that
$A + E_A$ is symmetric and $B + E_B$ is positive definite, and let $\mu_1 \ge \dots \ge \mu_n$
be the eigenvalues of $(A + E_A) - \lambda (B + E_B)$. If
$$\epsilon = \sqrt{\|E_A\|_2^2 + \|E_B\|_2^2} < c(A, B),$$
then for every $i$
$$\sin |\arctan \lambda_i - \arctan \mu_i| \le \frac{\epsilon}{c(A, B)}.$$

**Correction.** The source prints the bound $|\arctan \lambda_i - \arctan \mu_i| \le
\arctan(\epsilon / c(A, B))$, which is false: see
`GolubVanLoan.Chapter08.theorem_8_7_3_counterexample`. The statement here bounds the sine of the
angle by $\epsilon / c(A, B)$, and it assumes that $B + E_B$ is positive definite. The Crawford
number is the corrected (8.7.4), with the square root.

The eigenvalues are `Matrix.pencilEigenvalues`, sorted decreasingly and indexed from 0. The norm
$\|\cdot\|_2$ is `Matrix.lpOpNorm 2`. -/
theorem theorem_8_7_3 {A B EA EB : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.PosDef)
    (hA' : (A + EA).IsSymm) (hB' : (B + EB).PosDef)
    (hε : Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) < crawfordNumber A B) (i : Fin n) :
    Real.sin |Real.arctan (pencilEigenvalues (isHermitian_iff_isSymm.2 hA) hB
          (Fin.cast (Fintype.card_fin n).symm i)) -
        Real.arctan (pencilEigenvalues (isHermitian_iff_isSymm.2 hA') hB'
          (Fin.cast (Fintype.card_fin n).symm i))| ≤
      Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) / crawfordNumber A B :=
  sin_abs_arctan_pencilEigenvalues_sub_le _ hB _ hB' hε _

/-- **Theorem 8.7.3** of [golub2013matrix], counterexample to the printed bound. Let $n = 1$,
$A = 0$, $B = 1$, $E_A = \sqrt{3}/4$ and $E_B = -1/4$. Then $\|E_A\|_2^2 + \|E_B\|_2^2 = 1/4$,
so $\epsilon = 1/2 < 1 = c(A, B)$. Moreover $\lambda(A, B) = \{0\}$ and
$\lambda(A + E_A, B + E_B) = \{1/\sqrt{3}\}$, and
$$|\arctan 0 - \arctan(1/\sqrt{3})| = \pi/6 > \arctan(\epsilon / c(A, B)).$$
So the bound as printed in the source fails. -/
theorem theorem_8_7_3_counterexample :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let B : Matrix (Fin 1) (Fin 1) ℝ := 1
    let EA : Matrix (Fin 1) (Fin 1) ℝ := !![Real.sqrt 3 / 4]
    let EB : Matrix (Fin 1) (Fin 1) ℝ := !![-1 / 4]
    lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2 = 1 / 4 ∧ crawfordNumber A B = 1 ∧
      pencilSpectrum A B = {0} ∧ pencilSpectrum (A + EA) (B + EB) = {(Real.sqrt 3)⁻¹} ∧
      ¬ |Real.arctan 0 - Real.arctan (Real.sqrt 3)⁻¹| ≤
        Real.arctan (Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) / crawfordNumber A B) := by
  intro A B EA EB
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3p : 0 < Real.sqrt 3 := by positivity
  -- the norm of a `1 × 1` matrix
  have hnorm : ∀ t : ℝ, lpOpNorm 2 (!![t] : Matrix (Fin 1) (Fin 1) ℝ) = |t| := fun t => by
    have hd : (!![t] : Matrix (Fin 1) (Fin 1) ℝ) = diagonal fun _ => t := by
      ext i j; fin_cases i; fin_cases j; rfl
    rw [hd, lpOpNorm_diagonal, ciSup_const, Real.norm_eq_abs]
  have hε : lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2 = 1 / 4 := by
    simp only [EA, EB, hnorm, sq_abs, div_pow, hs3]
    norm_num
  have hc : crawfordNumber A B = 1 := by
    have hne : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
      (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
    have hterm : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
        Real.sqrt (reQuadForm A x ^ 2 + reQuadForm B x ^ 2) = 1 := fun x => by
      have hx : ‖(x : EuclideanSpace ℝ (Fin 1))‖ = 1 := by simp
      have h1 : reQuadForm B x = 1 := by
        simp only [reQuadForm, B, one_mulVec, star_trivial, RCLike.re_to_real]
        rw [dotProduct_self_eq_norm_sq, WithLp.toLp_ofLp, hx, one_pow]
      have h0 : reQuadForm A x = 0 := by simp [reQuadForm, A]
      rw [h0, h1]
      norm_num
    rw [crawfordNumber, Matrix.crawfordNumber, iInf_congr hterm, ciInf_const]
  have hspec1 : pencilSpectrum A B = {0} := by
    ext μ
    simp [mem_pencilSpectrum_iff_det, A, B]
  have hspec2 : pencilSpectrum (A + EA) (B + EB) = {(Real.sqrt 3)⁻¹} := by
    ext μ
    simp only [mem_pencilSpectrum_iff_det, A, B, EA, EB, det_fin_one, Set.mem_singleton_iff]
    simp only [zero_add, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, one_apply_eq,
      of_apply, cons_val', empty_val', cons_val_fin_one, smul_eq_mul]
    constructor
    · intro h
      field_simp
      nlinarith [hs3]
    · rintro rfl
      field_simp
      nlinarith [hs3]
  refine ⟨hε, hc, hspec1, hspec2, ?_⟩
  rw [hε, hc, div_one, show Real.sqrt (1 / 4) = 1 / 2 by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num,
    Real.arctan_zero, zero_sub, abs_neg, Real.arctan_inv_sqrt_three,
    abs_of_pos (by positivity), not_le, ← Real.arctan_inv_sqrt_three]
  refine Real.arctan_lt_arctan_iff.2 ?_
  rw [one_div, inv_lt_inv₀ (by norm_num) hs3p]
  nlinarith [hs3]

/-! ### §8.7.2 Methods for the symmetric-definite problem -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The column-by-column triangular solve of Algorithms 8.7.1 and 8.7.2: column $j$ of $Y$ is
replaced by `solve` applied to that column. -/
private def solveCols (solve : (Fin n → ℝ) → M (Fin n → ℝ)) (Y : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (Z : Matrix (Fin n) (Fin n) ℝ) j => do
    let z ← solve (Y.col j)
    pure (Z.updateCol j z)) Y

/-- **Algorithm 8.7.1** of [golub2013matrix] (symmetric-definite $Ax = \lambda Bx$). "Given
$A = A^T$ and $B = B^T$ positive definite, the following algorithm computes a nonsingular $X$
such that $X^T A X = \operatorname{diag}(a_1, \dots, a_n)$ and $X^T B X = I_n$."
```
Compute the Cholesky factorization B = GGᵀ using Algorithm 4.2.1.
Compute C = G⁻¹AG⁻ᵀ.
Use the symmetric QR algorithm to compute the Schur decomposition QᵀCQ = diag(a₁, …, a_n).
Set X = G⁻ᵀQ.
```
The program takes $G$ as the lower triangle of the output of Algorithm 4.2.1. It computes
$Y = G^{-1} A$ and then $C = G^{-1} Y^T$ by forward substitution (Algorithm 3.1.1), which gives
$G^{-1} A G^{-T}$ because $A$ is symmetric. It computes $X$ from $G^T X = Q$ by back
substitution (Algorithm 3.1.2). It returns $X$ and $a$.

**Typo.** The source cites Algorithm 4.2.2 for the Cholesky factorization. The intended
algorithm is Algorithm 4.2.1.

The symmetric Schur decomposition is the monadic parameter `schur` (convention 5 of the
library), which returns $Q$ and $a$: Algorithm 8.3.3 returns a diagonal matrix only up to its
deflation perturbation, so it is not an exact program. The triangular solves run column by
column. -/
noncomputable def algorithm_8_7_1
    (schur : Matrix (Fin n) (Fin n) ℝ → M (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)))
    (A B : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) := do
  let F ← Chapter04.algorithm_4_2_1 rnd B
  let G := F - F.strictUpper
  let Y ← solveCols (Chapter03.algorithm_3_1_1 rnd G) A
  let C ← solveCols (Chapter03.algorithm_3_1_1 rnd G) Yᵀ
  let Qa ← schur C
  let X ← solveCols (Chapter03.algorithm_3_1_2 rnd Gᵀ) Qa.1
  pure (X, Qa.2)

end Programs

/-- In exact arithmetic, the column solves return the matrix whose column $j$ is `solve` applied to
column $j$ of $Y$. -/
private theorem solveCols_id (solve : (Fin n → ℝ) → Id (Fin n → ℝ))
    (Y : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (solveCols solve Y) = of fun i j => Id.run (solve (Y.col j)) i := by
  have key : ∀ (l : List (Fin n)) (Z : Matrix (Fin n) (Fin n) ℝ), l.Nodup →
      l.foldl (fun Z j => Z.updateCol j (Id.run (solve (Y.col j)))) Z =
        of fun i j => if j ∈ l then Id.run (solve (Y.col j)) i else Z i j := by
    intro l
    induction l with
    | nil => intro Z _; ext i j; simp
    | cons a l ih =>
      intro Z hl
      rw [List.foldl_cons, ih _ (List.nodup_cons.1 hl).2]
      ext i j
      simp only [of_apply, updateCol_apply, List.mem_cons]
      by_cases hja : j = a
      · subst hja; simp [(List.nodup_cons.1 hl).1]
      · simp [hja]
  unfold solveCols
  rw [show (fun (Z : Matrix (Fin n) (Fin n) ℝ) j =>
      (do let z ← solve (Y.col j); pure (Z.updateCol j z) : Id _)) =
      fun Z j => pure (Z.updateCol j (Id.run (solve (Y.col j)))) from rfl, List.foldlM_pure,
    key _ _ (List.nodup_finRange n)]
  ext i j
  simp

/-- If `solve b` solves $Gx = b$ for every $b$, then the column solves of $Y$ return $X$ with
$GX = Y$. -/
private theorem mul_solveCols {G : Matrix (Fin n) (Fin n) ℝ}
    {solve : (Fin n → ℝ) → Id (Fin n → ℝ)} (h : ∀ b, G *ᵥ Id.run (solve b) = b)
    (Y : Matrix (Fin n) (Fin n) ℝ) : G * Id.run (solveCols solve Y) = Y := by
  ext i j
  have := congrFun (h (Y.col j)) i
  rw [solveCols_id]
  simpa [Matrix.mul_apply, mulVec, dotProduct] using this

/-- **Algorithm 8.7.1** of [golub2013matrix], exact semantics. Suppose that, for every symmetric
$C \in \mathbb{R}^{n \times n}$, the Schur step returns an orthogonal $Q$ and a vector $a$ with
$Q^T C Q = \operatorname{diag}(a)$. Let $A \in \mathbb{R}^{n \times n}$ be symmetric and
$B \in \mathbb{R}^{n \times n}$ positive definite. Then in exact arithmetic the output $(X, a)$
of Algorithm 8.7.1 satisfies
$$X^T A X = \operatorname{diag}(a), \qquad X^T B X = I.$$

The Cholesky step gives $G = $ `Matrix.cholesky B`, lower triangular with positive diagonal and
$B = GG^T$. The solves give $GY = A$, $GC = Y^T$ and $G^T X = Q$, so $A = GCG^T$,
$X^T A X = Q^T C Q$ and $X^T B X = Q^T Q$. -/
theorem algorithm_8_7_1_spec
    (schur : Matrix (Fin n) (Fin n) ℝ → Id (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)))
    (hschur : ∀ C : Matrix (Fin n) (Fin n) ℝ, C.IsSymm →
      (Id.run (schur C)).1 ∈ orthogonalGroup (Fin n) ℝ ∧
        (Id.run (schur C)).1ᵀ * C * (Id.run (schur C)).1 = diagonal (Id.run (schur C)).2)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.PosDef) :
    (Id.run (algorithm_8_7_1 pure schur A B)).1ᵀ * A * (Id.run (algorithm_8_7_1 pure schur A B)).1 =
        diagonal (Id.run (algorithm_8_7_1 pure schur A B)).2 ∧
      (Id.run (algorithm_8_7_1 pure schur A B)).1ᵀ * B *
        (Id.run (algorithm_8_7_1 pure schur A B)).1 = 1 := by
  obtain ⟨hFG, hBG⟩ := Chapter04.algorithm_4_2_1_spec hB
  set F := Id.run (Chapter04.algorithm_4_2_1 pure B)
  set G := F - F.strictUpper with hGdef
  have hGl : G.IsLowerTriangular := by rw [hFG]; exact isLowerTriangular_cholesky B
  have hGd : ∀ i, G i i ≠ 0 := fun i => by
    have := (isCholesky_cholesky hB).diag_pos i
    rw [hFG]
    simpa using this.ne'
  have hGu : IsUnit G := by
    rw [isUnit_iff_isUnit_det, det_of_isLowerTriangular G hGl]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hGd i)
  have hGtu : Gᵀ.IsUpperTriangular := hGl.transpose_isUpperTriangular
  set Y := Id.run (solveCols (Chapter03.algorithm_3_1_1 pure G) A)
  set C := Id.run (solveCols (Chapter03.algorithm_3_1_1 pure G) Yᵀ)
  set Qa := Id.run (schur C)
  set X := Id.run (solveCols (Chapter03.algorithm_3_1_2 pure Gᵀ) Qa.1)
  have hrun : Id.run (algorithm_8_7_1 pure schur A B) = (X, Qa.2) := rfl
  rw [hrun]
  have hY : G * Y = A := mul_solveCols (fun b => Chapter03.algorithm_3_1_1_spec hGl hGd b) A
  have hC : G * C = Yᵀ := mul_solveCols (fun b => Chapter03.algorithm_3_1_1_spec hGl hGd b) Yᵀ
  have hX : Gᵀ * X = Qa.1 := mul_solveCols (fun b => Chapter03.algorithm_3_1_2_spec hGtu
    (fun i => by simpa using hGd i) b) Qa.1
  have hAGC : A = G * C * Gᵀ := by
    rw [hC, ← transpose_mul, hY, hA.eq]
  have hCs : C.IsSymm := by
    have h1 : G * Cᵀ * Gᵀ = G * C * Gᵀ := by
      rw [← hAGC]
      conv_rhs => rw [← hA.eq, hAGC]
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    have h2 := hGu.mul_left_cancel (by simpa only [Matrix.mul_assoc] using h1)
    exact ((isUnit_transpose G).2 hGu).mul_right_cancel h2
  obtain ⟨hQ, hQC⟩ := hschur C hCs
  have hQQ : Qa.1ᵀ * Qa.1 = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  refine ⟨?_, ?_⟩
  · rw [hAGC, show Xᵀ * (G * C * Gᵀ) * X = (Gᵀ * X)ᵀ * C * (Gᵀ * X) by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc], hX, hQC]
  · rw [hBG, show Xᵀ * (G * Gᵀ) * X = (Gᵀ * X)ᵀ * (Gᵀ * X) by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc], hX, hQQ]

/-- **§8.7.2** of [golub2013matrix], the identity after Algorithm 8.7.1. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $B \in \mathbb{R}^{n \times n}$ positive
definite, with Cholesky factor $G$, so that $B = GG^T$. Then
$$\lambda(A, B) = \lambda(A, GG^T) = \lambda(G^{-1} A G^{-T}, I) = \lambda(C),$$
that is, $\lambda(A, B)$ is the spectrum of $C = G^{-1} A G^{-T}$. If, in addition, the Schur
step returns for every symmetric $C$ an orthogonal $Q$ and a vector $a$ with
$Q^T C Q = \operatorname{diag}(a)$, then $\lambda(A, B) = \{a_1, \dots, a_n\}$ for the output
$(X, a)$ of Algorithm 8.7.1 in exact arithmetic.

The factor $G$ is `Matrix.cholesky B`. The first identity is
`GolubVanLoan.Chapter08.pencil_congruence` with $X = G^{-T}$. The hypothesis on the Schur step
is also present for the first identity, which does not use it. -/
theorem pencil_eq_cholesky_spectrum
    (schur : Matrix (Fin n) (Fin n) ℝ → Id (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)))
    (hschur : ∀ C : Matrix (Fin n) (Fin n) ℝ, C.IsSymm →
      (Id.run (schur C)).1 ∈ orthogonalGroup (Fin n) ℝ ∧
        (Id.run (schur C)).1ᵀ * C * (Id.run (schur C)).1 = diagonal (Id.run (schur C)).2)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.PosDef) :
    pencilSpectrum A B = spectrum ℝ ((cholesky B)⁻¹ * A * ((cholesky B)⁻¹)ᵀ) ∧
      pencilSpectrum A B = Set.range (Id.run (algorithm_8_7_1 pure schur A B)).2 := by
  obtain ⟨hFG, hBG⟩ := Chapter04.algorithm_4_2_1_spec hB
  rw [hFG] at hBG
  set G := cholesky B
  have hGd : IsUnit G.det := by
    have h := congrArg det hBG
    rw [det_mul, det_transpose] at h
    exact isUnit_iff_ne_zero.2 fun h0 => hB.det_pos.ne' (by rw [h, h0, zero_mul])
  refine ⟨?_, ?_⟩
  · have hXd : IsUnit (G⁻¹)ᵀ.det := by
      rw [det_transpose]; exact isUnit_nonsing_inv_det G hGd
    rw [← pencil_congruence A B hXd, transpose_transpose, hBG,
      show G⁻¹ * (G * Gᵀ) * G⁻¹ᵀ = (G⁻¹ * G) * (G⁻¹ * G)ᵀ by
        simp only [transpose_mul, Matrix.mul_assoc],
      nonsing_inv_mul _ hGd, transpose_one, Matrix.mul_one, pencilSpectrum_one]
  · obtain ⟨h1, h2⟩ := algorithm_8_7_1_spec schur hschur hA hB
    set X := (Id.run (algorithm_8_7_1 pure schur A B)).1
    have hXd : IsUnit X.det := by
      have h := congrArg det h2
      rw [det_mul, det_mul, det_transpose, det_one] at h
      exact IsUnit.of_mul_eq_one (B.det * X.det) (by rw [← h]; ring)
    rw [← pencil_congruence A B hXd, h1, h2, pencilSpectrum_one, spectrum_diagonal]

/-! ### §8.7.2 The generalized Rayleigh quotient -/

/-- **Equation (8.7.5)** of [golub2013matrix] (generalized Rayleigh quotient iteration). For
$A, B \in \mathbb{R}^{n \times n}$ and a start vector $x_0$, the iteration is
$$\mu_k = \frac{x_k^T A x_k}{x_k^T B x_k}, \qquad (A - \mu_k B) z_{k+1} = B x_k, \qquad
  x_{k+1} = \frac{z_{k+1}}{\|z_{k+1}\|_2}.$$

The solve uses the Lean inverse `Matrix.inv`, which is total: if $A - \mu_k B$ is singular, then
$z_{k+1} = 0$ and $x_{k+1} = 0$. If $x_k^T B x_k = 0$, then $\mu_k = 0$, and if $z_{k+1} = 0$,
then $x_{k+1} = 0$. -/
noncomputable def generalizedRayleighQuotientIteration (A B : Matrix (Fin n) (Fin n) ℝ)
    (x₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₀
  | k + 1 =>
    let x := generalizedRayleighQuotientIteration A B x₀ k
    let z := (A - ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) • B)⁻¹ *ᵥ (B *ᵥ x)
    ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))‖⁻¹ • z

/-- **Equation (8.7.5)** of [golub2013matrix], as Rayleigh quotient iteration on $B^{-1} A$. Let $B$
be nonsingular. Then each step of the generalized Rayleigh quotient iteration solves
$$(B^{-1} A - \mu_k I) z_{k+1} = x_k, \qquad \mu_k = \frac{x_k^T A x_k}{x_k^T B x_k},$$
and sets $x_{k+1} = z_{k+1} / \|z_{k+1}\|_2$. This is inverse iteration (7.6.1) on $B^{-1} A$
with the generalized Rayleigh quotient $\mu_k$ as shift. -/
theorem generalizedRayleighQuotientIteration_succ {A B : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsUnit B.det) (x₀ : Fin n → ℝ) (k : ℕ) :
    let x := generalizedRayleighQuotientIteration A B x₀ k
    let z := (B⁻¹ * A - ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) • 1)⁻¹ *ᵥ x
    generalizedRayleighQuotientIteration A B x₀ (k + 1) =
      ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))‖⁻¹ • z := by
  intro x z
  have key : ∀ μ : ℝ, (A - μ • B)⁻¹ *ᵥ (B *ᵥ x) = (B⁻¹ * A - μ • 1)⁻¹ *ᵥ x := fun μ => by
    have e : A - μ • B = B * (B⁻¹ * A - μ • 1) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, mul_nonsing_inv B hB, Matrix.one_mul,
        Matrix.mul_smul, Matrix.mul_one]
    rw [e, Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul B hB,
      Matrix.mul_one]
  change ‖(WithLp.toLp 2 ((A - ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) • B)⁻¹ *ᵥ (B *ᵥ x)) :
      EuclideanSpace ℝ (Fin n))‖⁻¹ • ((A - ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) • B)⁻¹ *ᵥ (B *ᵥ x)) = _
  rw [key]

/-- **Equations (8.7.6)–(8.7.7)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$, let
$B \in \mathbb{R}^{n \times n}$ be positive definite, and let $x \neq 0$. For the norm
$\|z\|_{B^{-1}}^2 = z^T B^{-1} z$, the number
$$\lambda = \frac{x^T A x}{x^T B x}$$
minimizes $f(\lambda) = \|Ax - \lambda Bx\|_{B^{-1}}$ over $\lambda \in \mathbb{R}$.

The matrix $A$ need not be symmetric. -/
theorem equation_8_7_7 (A : Matrix (Fin n) (Fin n) ℝ) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosDef) {x : Fin n → ℝ} (hx : x ≠ 0) :
    IsMinOn (fun μ : ℝ => Real.sqrt ((A *ᵥ x - μ • B *ᵥ x) ⬝ᵥ B⁻¹ *ᵥ (A *ᵥ x - μ • B *ᵥ x)))
      Set.univ ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) :=
  fun _ hμ => Real.sqrt_le_sqrt (isMinOn_pencil_residual (A := A) hB hx hμ)

/-- **Equation (8.7.8)** of [golub2013matrix] (generalized orthogonal iteration). Let
$A, B \in \mathbb{R}^{n \times n}$ with $B$ nonsingular, and let
$Q_k \in \mathbb{R}^{n \times p}$ and $R_k \in \mathbb{R}^{p \times p}$ for $k \ge 0$ be
arbitrary sequences. The iteration (8.7.8) solves $B Z_k = A Q_{k-1}$ and takes a thin QR
factorization $Z_k = Q_k R_k$ for $k \ge 1$. The source says that it "is mathematically
equivalent to (7.3.6) with $A$ replaced by $B^{-1} A$". Precisely:

* there are $Z_k$ that satisfy (8.7.8) if and only if, for every $k \ge 1$, $Q_k R_k$ is a thin
  QR factorization of $B^{-1} A Q_{k-1}$;
* if $Q_0^T Q_0 = I_p$ and these factorizations hold, then $(Q_k)$ is an orthogonal iteration
  (7.3.6) for $B^{-1} A$.

The thin QR factorizations are `Matrix.IsThinQR`, which includes that $R_k$ is upper triangular,
and the orthogonal iteration is `GolubVanLoan.Chapter07.orthogonalIteration`. -/
theorem equation_8_7_8 {p : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hB : IsUnit B.det)
    (Q : ℕ → Matrix (Fin n) (Fin p) ℝ) (R : ℕ → Matrix (Fin p) (Fin p) ℝ) :
    ((∃ Z : ℕ → Matrix (Fin n) (Fin p) ℝ, ∀ k,
        B * Z (k + 1) = A * Q k ∧ IsThinQR (Z (k + 1)) (Q (k + 1)) (R (k + 1))) ↔
      ∀ k, IsThinQR (B⁻¹ * A * Q k) (Q (k + 1)) (R (k + 1))) ∧
    ((Q 0)ᵀ * Q 0 = 1 → (∀ k, IsThinQR (B⁻¹ * A * Q k) (Q (k + 1)) (R (k + 1))) →
      Chapter07.orthogonalIteration (B⁻¹ * A) Q) := by
  refine ⟨⟨fun ⟨Z, hZ⟩ k => ?_, fun h => ⟨fun k => B⁻¹ * A * Q (k - 1), fun k => ⟨?_, ?_⟩⟩⟩,
    fun h0 h => ⟨by rwa [conjTranspose_eq_transpose_of_trivial], fun k => ⟨R (k + 1), h k⟩⟩⟩
  · obtain ⟨h1, h2⟩ := hZ k
    have hZk : Z (k + 1) = B⁻¹ * A * Q k := by
      rw [Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hB, Matrix.one_mul]
    rwa [hZk] at h2
  · simp only [Nat.add_sub_cancel]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hB, Matrix.one_mul]
  · simpa only [Nat.add_sub_cancel] using h k

/-! ### §8.7.4 The generalized singular value problem -/

/-- **Theorem 8.7.4** of [golub2013matrix] (GSVD, tall rectangular version). "If
$A \in \mathbb{R}^{m_1 \times n}$ and $B \in \mathbb{R}^{m_2 \times n}$ have at least as many
rows as columns, then there exists an orthogonal matrix $U_1 \in \mathbb{R}^{m_1 \times m_1}$,
an orthogonal matrix $U_2 \in \mathbb{R}^{m_2 \times m_2}$, and a nonsingular matrix
$X \in \mathbb{R}^{n \times n}$ such that
$$U_1^T A X = \operatorname{diag}(\alpha_1, \dots, \alpha_n), \qquad U_2^T B X =
  \operatorname{diag}(\beta_1, \dots, \beta_n)."$$

The diagonal matrices are the rectangular diagonal matrices `Matrix.rectDiagonal α` and
`Matrix.rectDiagonal β`. The proof uses Theorem 6.1.1 of Chapter 6,
`GolubVanLoan.Chapter06.theorem_6_1_1`, where $p = \max(r - m_2, 0) = 0$ because $r =
\operatorname{rank} \begin{bmatrix} A \\ B \end{bmatrix} \le n \le m_2$. -/
theorem theorem_8_7_4 {m₁ m₂ : ℕ} (hm₁ : n ≤ m₁) (hm₂ : n ≤ m₂) (A : Matrix (Fin m₁) (Fin n) ℝ)
    (B : Matrix (Fin m₂) (Fin n) ℝ) :
    ∃ (U₁ : Matrix (Fin m₁) (Fin m₁) ℝ) (U₂ : Matrix (Fin m₂) (Fin m₂) ℝ)
      (X : Matrix (Fin n) (Fin n) ℝ) (α β : ℕ → ℝ),
      U₁ ∈ orthogonalGroup (Fin m₁) ℝ ∧ U₂ ∈ orthogonalGroup (Fin m₂) ℝ ∧ IsUnit X.det ∧
      U₁ᵀ * A * X = rectDiagonal α ∧ U₂ᵀ * B * X = rectDiagonal β := by
  obtain ⟨U₁, U₂, X, α, β, hU₁, hU₂, hX, hA, hB, -, -⟩ := Chapter06.theorem_6_1_1 hm₁ A B
  have hp : (fromRows A B).rank - m₂ = 0 :=
    Nat.sub_eq_zero_of_le (((rank_le_card_width _).trans_eq (Fintype.card_fin n)).trans hm₂)
  refine ⟨U₁, U₂, X, α, β, hU₁, hU₂, (isUnit_iff_isUnit_det X).1 hX, hA, ?_⟩
  rwa [hp, shiftedRectDiagonal_zero] at hB

/-- **§8.7.4** of [golub2013matrix], the consequences of a GSVD. Let
$A \in \mathbb{R}^{m_1 \times n}$ and $B \in \mathbb{R}^{m_2 \times n}$ with $m_1, m_2 \ge n$,
and let $U_1$, $U_2$ be orthogonal and $X = [x_1 | \cdots | x_n]$ nonsingular with
$U_1^T A X = D_A = \operatorname{diag}(\alpha)$ and
$U_2^T B X = D_B = \operatorname{diag}(\beta)$. Let $u_k$ and $v_k$ be the columns of $U_1$ and
$U_2$. Then:

* $A x_k = \alpha_k u_k$ and $B x_k = \beta_k v_k$ for every $k$;
* $X^T (A^T A - \lambda B^T B) X = \operatorname{diag}(\alpha_k^2 - \lambda \beta_k^2)$ for
  every $\lambda \in \mathbb{R}$;
* if $\beta_k \neq 0$, then $x_k$ is an eigenvector of the pencil $A^T A - \lambda B^T B$ with
  eigenvalue $(\alpha_k / \beta_k)^2$;
* if $\beta_k \neq 0$ for all $k$, then $\lambda(A^T A, B^T B) = \{(\alpha_k / \beta_k)^2 : k =
  1, \dots, n\}$, the squares of the generalized singular values
  $\sigma(A, B) = \{\alpha_k / \beta_k\}$.

The eigenvector condition is `Matrix.HasPencilEigenvector`. -/
theorem gsvd_columns_and_pencil {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} (hm₁ : n ≤ m₁) (hm₂ : n ≤ m₂)
    {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ} {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hU₁ : U₁ ∈ orthogonalGroup (Fin m₁) ℝ)
    (hU₂ : U₂ ∈ orthogonalGroup (Fin m₂) ℝ) (hX : IsUnit X.det) {α β : ℕ → ℝ}
    (hA : U₁ᵀ * A * X = rectDiagonal α) (hB : U₂ᵀ * B * X = rectDiagonal β) :
    (∀ k : Fin n, A *ᵥ X.col k = α k • U₁.col (Fin.castLE hm₁ k) ∧
      B *ᵥ X.col k = β k • U₂.col (Fin.castLE hm₂ k)) ∧
    (∀ l : ℝ, Xᵀ * (Aᵀ * A - l • (Bᵀ * B)) * X =
      diagonal fun k : Fin n => α k ^ 2 - l * β k ^ 2) ∧
    (∀ k : Fin n, β k ≠ 0 →
      HasPencilEigenvector (Aᵀ * A) (Bᵀ * B) ((α k / β k) ^ 2) (X.col k)) ∧
    ((∀ k : Fin n, β k ≠ 0) →
      pencilSpectrum (Aᵀ * A) (Bᵀ * B) = Set.range fun k : Fin n => (α k / β k) ^ 2) := by
  have hstar : ∀ {m : ℕ} (U : Matrix (Fin m) (Fin m) ℝ), star U = Uᵀ := fun U => by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hA' : star U₁ * A * X = rectDiagonal α := by rwa [hstar]
  have hB' : star U₂ * B * X = rectDiagonal β := by rwa [hstar]
  -- the Gram matrices, by `Matrix.conjTranspose_mul_gram_mul_of_star_mul_mul_eq_rectDiagonal`
  have hgram : ∀ {m : ℕ} (hm : n ≤ m) {M : Matrix (Fin m) (Fin n) ℝ}
      {U : Matrix (Fin m) (Fin m) ℝ} {γ : ℕ → ℝ}, U ∈ orthogonalGroup (Fin m) ℝ →
      star U * M * X = rectDiagonal γ →
      Xᴴ * (Mᴴ * M) * X = diagonal fun k : Fin n => γ k ^ 2 := fun {m} hm {M U γ} hU h => by
    rw [conjTranspose_mul_gram_mul_of_star_mul_mul_eq_rectDiagonal hm hU h]
    congr 1
    funext k
    rw [star_trivial, sq]
  have hgA := hgram hm₁ hU₁ hA'
  have hgB := hgram hm₂ hU₂ hB'
  simp only [conjTranspose_eq_transpose_of_trivial] at hgA hgB
  have hpen : ∀ l : ℝ, Xᵀ * (Aᵀ * A - l • (Bᵀ * B)) * X =
      diagonal fun k : Fin n => α k ^ 2 - l * β k ^ 2 := fun l => by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hgA, hgB]
    ext i j
    by_cases h : i = j <;> simp [h]
  have hXu : IsUnit X := (isUnit_iff_isUnit_det X).2 hX
  have hgA' : Xᴴ * (Aᵀ * A) * X = diagonal fun k : Fin n => α k ^ 2 := by
    rwa [conjTranspose_eq_transpose_of_trivial]
  have hgB' : Xᴴ * (Bᵀ * B) * X = diagonal fun k : Fin n => β k ^ 2 := by
    rwa [conjTranspose_eq_transpose_of_trivial]
  refine ⟨fun k => ⟨mulVec_col_eq_smul_col_of_mul_eq_mul_rectDiagonal hm₁
      (mul_eq_mul_of_star_mul_mul_eq hU₁ hA') k,
    mulVec_col_eq_smul_col_of_mul_eq_mul_rectDiagonal hm₂
      (mul_eq_mul_of_star_mul_mul_eq hU₂ hB') k⟩, hpen, fun k hk => ?_, fun hβ => ?_⟩
  · rw [div_pow]
    exact hasPencilEigenvector_col_of_conj_diagonal hXu hgA' hgB' (pow_ne_zero 2 hk)
  · rw [pencilSpectrum_eq_range_of_conj_diagonal hXu hgA' hgB' fun k => pow_ne_zero 2 (hβ k)]
    simp only [div_pow]

/-! ### §8.7.5 Computing the GSVD -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 8.7.2** of [golub2013matrix] (GSVD, tall full-rank version). For
$A \in \mathbb{R}^{m_1 \times n}$ and $B \in \mathbb{R}^{m_2 \times n}$ with
$\operatorname{null}(A) \cap \operatorname{null}(B) = \{0\}$, the algorithm does the following.

* Compute the QR factorization $\begin{bmatrix} A \\ B \end{bmatrix} = \begin{bmatrix} Q_1 \\
  Q_2 \end{bmatrix} R$.
* Compute the CS decomposition $U_1^T Q_1 V = D_A = \operatorname{diag}(\alpha_1, \dots,
  \alpha_n)$, $U_2^T Q_2 V = D_B = \operatorname{diag}(\beta_1, \dots, \beta_n)$.
* Solve $RX = V$ for $X$.

The program returns $(U_1, U_2, X, \alpha, \beta)$. The QR factorization is modified
Gram–Schmidt (Algorithm 5.2.6) on the stacked $(m_1 + m_2) \times n$ matrix, and $RX = V$ is
solved by back substitution (Algorithm 3.1.2) column by column. The source gives no algorithm
for the CS decomposition, so it is the monadic parameter `cs` (convention 5 of the library),
which returns $(U_1, U_2, V, \alpha, \beta)$. -/
noncomputable def algorithm_8_7_2 {m₁ m₂ : ℕ}
    (cs : Matrix (Fin m₁) (Fin n) ℝ → Matrix (Fin m₂) (Fin n) ℝ →
      M (Matrix (Fin m₁) (Fin m₁) ℝ × Matrix (Fin m₂) (Fin m₂) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        (ℕ → ℝ) × (ℕ → ℝ)))
    (A : Matrix (Fin m₁) (Fin n) ℝ) (B : Matrix (Fin m₂) (Fin n) ℝ) :
    M (Matrix (Fin m₁) (Fin m₁) ℝ × Matrix (Fin m₂) (Fin m₂) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      (ℕ → ℝ) × (ℕ → ℝ)) := do
  let QR ← Chapter05.algorithm_5_2_6 rnd ((fromRows A B).submatrix finSumFinEquiv.symm id)
  let out ← cs (QR.1.submatrix (Fin.castAdd m₂) id) (QR.1.submatrix (Fin.natAdd m₁) id)
  let X ← solveCols (Chapter03.algorithm_3_1_2 rnd QR.2) out.2.2.1
  pure (out.1, out.2.1, X, out.2.2.2.1, out.2.2.2.2)

end Programs

/-- **Algorithm 8.7.2** of [golub2013matrix], exact semantics. Suppose that, for every
$Q_1 \in \mathbb{R}^{m_1 \times n}$ and $Q_2 \in \mathbb{R}^{m_2 \times n}$ with
$Q_1^T Q_1 + Q_2^T Q_2 = I$, the CS step returns orthogonal $U_1$, $U_2$, $V$ and vectors
$\alpha$, $\beta$ with $U_1^T Q_1 V = \operatorname{diag}(\alpha)$ and
$U_2^T Q_2 V = \operatorname{diag}(\beta)$. Let $A \in \mathbb{R}^{m_1 \times n}$ and
$B \in \mathbb{R}^{m_2 \times n}$ satisfy $\operatorname{null}(A) \cap \operatorname{null}(B) =
\{0\}$. Then in exact arithmetic the output $(U_1, U_2, X, \alpha, \beta)$ satisfies: $U_1$ and
$U_2$ are orthogonal, $X$ is nonsingular, and
$$U_1^T A X = \operatorname{diag}(\alpha), \qquad U_2^T B X = \operatorname{diag}(\beta),$$
which is a GSVD as in Theorem 8.7.4.

**Typo.** The source writes the hypothesis as $\operatorname{null}(A) \cap
\operatorname{null}(B) = \emptyset$. The intended hypothesis, stated here, is
$\operatorname{null}(A) \cap \operatorname{null}(B) = \{0\}$.

The hypothesis on the CS step is a thin CS decomposition; Theorem 2.5.2 of Chapter 2 gives one
when $m_1, m_2 \ge n$. The stacked matrix has full column rank, so Algorithm 5.2.6 computes a
thin QR factorization with positive diagonal, and $AX = Q_1 RX = Q_1 V$. -/
theorem algorithm_8_7_2_spec {m₁ m₂ : ℕ}
    (cs : Matrix (Fin m₁) (Fin n) ℝ → Matrix (Fin m₂) (Fin n) ℝ →
      Id (Matrix (Fin m₁) (Fin m₁) ℝ × Matrix (Fin m₂) (Fin m₂) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        (ℕ → ℝ) × (ℕ → ℝ)))
    (hcs : ∀ (Q₁ : Matrix (Fin m₁) (Fin n) ℝ) (Q₂ : Matrix (Fin m₂) (Fin n) ℝ),
      Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1 →
        (Id.run (cs Q₁ Q₂)).1 ∈ orthogonalGroup (Fin m₁) ℝ ∧
        (Id.run (cs Q₁ Q₂)).2.1 ∈ orthogonalGroup (Fin m₂) ℝ ∧
        (Id.run (cs Q₁ Q₂)).2.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧
        (Id.run (cs Q₁ Q₂)).1ᵀ * Q₁ * (Id.run (cs Q₁ Q₂)).2.2.1 =
          rectDiagonal (Id.run (cs Q₁ Q₂)).2.2.2.1 ∧
        (Id.run (cs Q₁ Q₂)).2.1ᵀ * Q₂ * (Id.run (cs Q₁ Q₂)).2.2.1 =
          rectDiagonal (Id.run (cs Q₁ Q₂)).2.2.2.2)
    {A : Matrix (Fin m₁) (Fin n) ℝ} {B : Matrix (Fin m₂) (Fin n) ℝ}
    (hAB : ∀ x, A *ᵥ x = 0 → B *ᵥ x = 0 → x = 0) :
    (Id.run (algorithm_8_7_2 pure cs A B)).1 ∈ orthogonalGroup (Fin m₁) ℝ ∧
      (Id.run (algorithm_8_7_2 pure cs A B)).2.1 ∈ orthogonalGroup (Fin m₂) ℝ ∧
      IsUnit (Id.run (algorithm_8_7_2 pure cs A B)).2.2.1 ∧
      (Id.run (algorithm_8_7_2 pure cs A B)).1ᵀ * A *
          (Id.run (algorithm_8_7_2 pure cs A B)).2.2.1 =
        rectDiagonal (Id.run (algorithm_8_7_2 pure cs A B)).2.2.2.1 ∧
      (Id.run (algorithm_8_7_2 pure cs A B)).2.1ᵀ * B *
          (Id.run (algorithm_8_7_2 pure cs A B)).2.2.1 =
        rectDiagonal (Id.run (algorithm_8_7_2 pure cs A B)).2.2.2.2 := by
  set S := (fromRows A B).submatrix finSumFinEquiv.symm id with hS
  have hSA : ∀ x i, (S *ᵥ x) (Fin.castAdd m₂ i) = (A *ᵥ x) i := fun x i => by
    simp [S, mulVec, dotProduct]
  have hSB : ∀ x i, (S *ᵥ x) (Fin.natAdd m₁ i) = (B *ᵥ x) i := fun x i => by
    simp [S, mulVec, dotProduct]
  have hind : LinearIndependent ℝ Sᵀ := by
    refine mulVec_injective_iff.1 fun x y hxy => ?_
    rw [← sub_eq_zero] at hxy ⊢
    rw [← mulVec_sub] at hxy
    refine hAB _ (funext fun i => ?_) (funext fun i => ?_)
    · rw [← hSA, hxy, Pi.zero_apply, Pi.zero_apply]
    · rw [← hSB, hxy, Pi.zero_apply, Pi.zero_apply]
  obtain ⟨hQR, hRd⟩ := Chapter05.algorithm_5_2_6_spec S hind
  set QR := Id.run (Chapter05.algorithm_5_2_6 pure S)
  set Q₁ := QR.1.submatrix (Fin.castAdd m₂) id
  set Q₂ := QR.1.submatrix (Fin.natAdd m₁) id
  set out := Id.run (cs Q₁ Q₂)
  set X := Id.run (solveCols (Chapter03.algorithm_3_1_2 pure QR.2) out.2.2.1)
  have hrun : Id.run (algorithm_8_7_2 pure cs A B) =
      (out.1, out.2.1, X, out.2.2.2.1, out.2.2.2.2) := rfl
  rw [hrun]
  have hA1 : A = Q₁ * QR.2 := by
    ext i j
    have := congrFun (congrFun hQR.mul_eq (Fin.castAdd m₂ i)) j
    simp only [S, submatrix_apply, id, finSumFinEquiv_symm_apply_castAdd, fromRows_apply_inl,
      Matrix.mul_apply] at this
    simp only [Q₁, Matrix.mul_apply, submatrix_apply, id]
    exact this.symm
  have hB1 : B = Q₂ * QR.2 := by
    ext i j
    have := congrFun (congrFun hQR.mul_eq (Fin.natAdd m₁ i)) j
    simp only [S, submatrix_apply, id, finSumFinEquiv_symm_apply_natAdd, fromRows_apply_inr,
      Matrix.mul_apply] at this
    simp only [Q₂, Matrix.mul_apply, submatrix_apply, id]
    exact this.symm
  have hQQ : Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1 := by
    ext i j
    have := congrFun (congrFun hQR.conjTranspose_mul_self i) j
    simp only [Matrix.mul_apply, conjTranspose_apply, star_trivial, Fin.sum_univ_add] at this
    simpa [Q₁, Q₂, Matrix.mul_apply] using this
  obtain ⟨hU1, hU2, hV, hDA, hDB⟩ := hcs Q₁ Q₂ hQQ
  have hRX : QR.2 * X = out.2.2.1 := mul_solveCols (fun b =>
    Chapter03.algorithm_3_1_2_spec hQR.isUpperTriangular (fun i => (hRd i).ne') b) _
  have hVd : IsUnit out.2.2.1.det :=
    isUnit_det_of_left_inverse ((mem_orthogonalGroup_iff' _ ℝ).1 hV)
  refine ⟨hU1, hU2, (isUnit_iff_isUnit_det X).2 (isUnit_of_mul_isUnit_right
    (by rw [← det_mul, hRX]; exact hVd)), ?_, ?_⟩
  · rw [hA1, show out.1ᵀ * (Q₁ * QR.2) * X = out.1ᵀ * Q₁ * (QR.2 * X) by
      simp only [Matrix.mul_assoc], hRX, hDA]
  · rw [hB1, show out.2.1ᵀ * (Q₂ * QR.2) * X = out.2.1ᵀ * Q₂ * (QR.2 * X) by
      simp only [Matrix.mul_assoc], hRX, hDB]

/-- **§8.7.5** of [golub2013matrix], the subspaces after Algorithm 8.7.2. Let
$R, V, Z, T \in \mathbb{R}^{n \times n}$ with $V$ and $Z$ orthogonal and $T$ upper triangular
and nonsingular, and suppose that $T Z^T = V^T R$. Then $Z T^{-1} = R^{-1} V$, and for
$X = R^{-1} V$ and every $k \le n$,
$$\operatorname{span}\{x_1, \dots, x_k\} = \operatorname{span}\{z_1, \dots, z_k\}.$$

The source assumes that $R$ is nonsingular. The statement does not need this hypothesis, because
$V^T R = T Z^T$ is then nonsingular. -/
theorem gsvd_subspace_via_rq {R V Z T : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (hT : T.IsUpperTriangular) (hTu : IsUnit T.det) (hTZ : T * Zᵀ = Vᵀ * R) :
    Z * T⁻¹ = R⁻¹ * V ∧ ∀ (k : ℕ) (hk : k ≤ n),
      Submodule.span ℝ (Set.range fun i : Fin k => (R⁻¹ * V).col (Fin.castLE hk i)) =
        Submodule.span ℝ (Set.range fun i : Fin k => Z.col (Fin.castLE hk i)) := by
  have hZZ : Z * Zᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hZ
  have hVV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hV
  have hX : Z * T⁻¹ = R⁻¹ * V := by
    have h1 : (T * Zᵀ)⁻¹ = Z * T⁻¹ := by
      rw [Matrix.mul_inv_rev, inv_eq_left_inv (show Z * Zᵀ = 1 from hZZ)]
    have h2 : (Vᵀ * R)⁻¹ = R⁻¹ * V := by
      rw [Matrix.mul_inv_rev, inv_eq_right_inv (show Vᵀ * V = 1 from
        (mem_orthogonalGroup_iff' _ ℝ).1 hV)]
    rw [← h1, hTZ, h2]
  refine ⟨hX, fun k hk => ?_⟩
  rw [← hX]
  have hTi : T⁻¹.IsUpperTriangular := by
    have : Invertible T := invertibleOfIsUnitDet T hTu
    exact blockTriangular_inv_of_blockTriangular hT
  have hZe : Z = Z * T⁻¹ * T := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hTu, Matrix.mul_one]
  -- a column of `M * U` with `U` upper triangular is a combination of the first columns of `M`
  have key : ∀ (M U : Matrix (Fin n) (Fin n) ℝ), U.IsUpperTriangular → ∀ i : Fin k,
      (M * U).col (Fin.castLE hk i) ∈
        Submodule.span ℝ (Set.range fun i : Fin k => M.col (Fin.castLE hk i)) := by
    intro M U hU i
    have hcol : (M * U).col (Fin.castLE hk i) = ∑ j : Fin n, U j (Fin.castLE hk i) • M.col j := by
      ext r
      simp [col_apply, Matrix.mul_apply, Finset.sum_apply, mul_comm]
    rw [hcol]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · have h0 : U j (Fin.castLE hk i) = 0 := hU (Fin.lt_def.2 (by simp; omega))
      rw [h0, zero_smul]
      exact zero_mem _
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact key Z T⁻¹ hTi i
  · rintro _ ⟨i, rfl⟩
    have := key (Z * T⁻¹) T hT i
    rwa [← hZe] at this

/-! ### §8.7.7 The Kogbetliantz approach -/

/-- **§8.7.7** of [golub2013matrix], the $2 \times 2$ GSVD step. Let
$F, G, U_1, U_2 \in \mathbb{R}^{2 \times 2}$ with $G$ nonsingular and $U_2$ orthogonal, and
suppose that $U_1^T (F G^{-1}) U_2 = \Sigma = \operatorname{diag}(\sigma_1, \sigma_2)$. Then:

* $U_1^T F = \Sigma (U_2^T G)$;
* if $Z$ is orthogonal and $U_2^T G Z$ is upper triangular, then
  $U_1^T F Z = \Sigma (U_2^T G Z)$, and $U_1^T F Z$ is upper triangular;
* $X = G^{-1} U_2$ satisfies $U_1^T F X = \Sigma$ and $U_2^T G X = I$, a GSVD of $(F, G)$ with
  generalized singular values $\sigma_1$, $\sigma_2$.

**Typo.** The source prints $U_1^T F = (U_2^T G) \Sigma$. The correct identity has $\Sigma$ on
the left.

The source takes $U_1^T (F G^{-1}) U_2 = \Sigma$ to be an SVD. Only the orthogonality of $U_2$
is used, so $U_1$ is not assumed orthogonal. -/
theorem kogbetliantz_twoByTwo {F G U₁ U₂ : Matrix (Fin 2) (Fin 2) ℝ} (hG : IsUnit G.det)
    (hU₂ : U₂ ∈ orthogonalGroup (Fin 2) ℝ)
    {σ : Fin 2 → ℝ} (hSig : U₁ᵀ * (F * G⁻¹) * U₂ = diagonal σ) :
    U₁ᵀ * F = diagonal σ * (U₂ᵀ * G) ∧
      (∀ Z ∈ orthogonalGroup (Fin 2) ℝ, (U₂ᵀ * G * Z).IsUpperTriangular →
        U₁ᵀ * F * Z = diagonal σ * (U₂ᵀ * G * Z) ∧ (U₁ᵀ * F * Z).IsUpperTriangular) ∧
      U₁ᵀ * F * (G⁻¹ * U₂) = diagonal σ ∧ U₂ᵀ * G * (G⁻¹ * U₂) = 1 := by
  have hU₂' : U₂ * U₂ᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hU₂
  have hU₂'' : U₂ᵀ * U₂ = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hU₂
  have h1 : U₁ᵀ * F = diagonal σ * (U₂ᵀ * G) := by
    rw [← hSig]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U₂, hU₂', Matrix.one_mul, nonsing_inv_mul _ hG, Matrix.mul_one]
  refine ⟨h1, fun Z _ hZ => ?_, ?_, ?_⟩
  · have h2 : U₁ᵀ * F * Z = diagonal σ * (U₂ᵀ * G * Z) := by
      rw [h1]
      simp only [Matrix.mul_assoc]
    exact ⟨h2, h2 ▸ (blockTriangular_diagonal σ).mul hZ⟩
  · rw [← hSig]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc G, mul_nonsing_inv _ hG, Matrix.one_mul, hU₂'']

/-! ### §8.7.9 The quadratic eigenvalue problem -/

/-- **Equations (8.7.13)–(8.7.14)** of [golub2013matrix]. Let $M, C, K \in \mathbb{C}^{n \times n}$,
$\lambda \in \mathbb{C}$ and $x \in \mathbb{C}^n$ with $(\lambda^2 M + \lambda C + K) x = 0$.
With $m = x^H M x$, $c = x^H C x$ and $k = x^H K x$,
$$m \lambda^2 + c \lambda + k = 0, \qquad (2m\lambda + c)^2 = c^2 - 4mk.$$
For $m \neq 0$ the second identity is the quadratic formula (8.7.14). -/
theorem equation_8_7_13 (M C K : Matrix (Fin n) (Fin n) ℂ) {l : ℂ} {x : Fin n → ℂ}
    (h : (l ^ 2 • M + l • C + K) *ᵥ x = 0) :
    (star x ⬝ᵥ M *ᵥ x) * l ^ 2 + (star x ⬝ᵥ C *ᵥ x) * l + star x ⬝ᵥ K *ᵥ x = 0 ∧
      (2 * (star x ⬝ᵥ M *ᵥ x) * l + star x ⬝ᵥ C *ᵥ x) ^ 2 =
        (star x ⬝ᵥ C *ᵥ x) ^ 2 - 4 * (star x ⬝ᵥ M *ᵥ x) * (star x ⬝ᵥ K *ᵥ x) := by
  have h1 : (star x ⬝ᵥ M *ᵥ x) * l ^ 2 + (star x ⬝ᵥ C *ᵥ x) * l + star x ⬝ᵥ K *ᵥ x = 0 := by
    have := congrArg (star x ⬝ᵥ ·) h
    simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
      dotProduct_zero] at this
    linear_combination this
  exact ⟨h1, by linear_combination 4 * (star x ⬝ᵥ M *ᵥ x) * h1⟩

/-- A $2 \times 2$ block equation $\begin{bmatrix} A_1 & B_1 \\ C_1 & D_1 \end{bmatrix}
\begin{bmatrix} x \\ u \end{bmatrix} = \lambda \begin{bmatrix} A_2 & B_2 \\ C_2 & D_2
\end{bmatrix} \begin{bmatrix} x \\ u \end{bmatrix}$ holds if and only if both block rows hold. -/
private theorem fromBlocks_eq_smul_iff {m : ℕ}
    (A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : Matrix (Fin m) (Fin m) ℂ) (l : ℂ) (x u : Fin m → ℂ) :
    fromBlocks A₁ B₁ C₁ D₁ *ᵥ Sum.elim x u = l • (fromBlocks A₂ B₂ C₂ D₂ *ᵥ Sum.elim x u) ↔
      A₁ *ᵥ x + B₁ *ᵥ u = l • (A₂ *ᵥ x + B₂ *ᵥ u) ∧
        C₁ *ᵥ x + D₁ *ᵥ u = l • (C₂ *ᵥ x + D₂ *ᵥ u) := by
  simp only [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, funext_iff, Sum.forall,
    Sum.elim_inl, Sum.elim_inr, Pi.smul_apply]

/-- **Equations (8.7.15)–(8.7.16)** of [golub2013matrix] (linearizations). Let
$M, C, K, N \in \mathbb{C}^{n \times n}$ with $N$ nonsingular, and let $\lambda \in \mathbb{C}$.
For every $x \in \mathbb{C}^n$, $(\lambda^2 M + \lambda C + K) x = 0$ if and only if
$$\begin{bmatrix} 0 & N \\ K & C \end{bmatrix} \begin{bmatrix} x \\ \lambda x \end{bmatrix} =
  \lambda \begin{bmatrix} N & 0 \\ 0 & -M \end{bmatrix} \begin{bmatrix} x \\ \lambda x
  \end{bmatrix} \quad (8.7.15),$$
and if and only if
$$\begin{bmatrix} -K & 0 \\ 0 & N \end{bmatrix} \begin{bmatrix} x \\ \lambda x \end{bmatrix} =
  \lambda \begin{bmatrix} C & M \\ N & 0 \end{bmatrix} \begin{bmatrix} x \\ \lambda x
  \end{bmatrix} \quad (8.7.16).$$
Moreover, every solution $(x, u)$ of either linearization has $u = \lambda x$, so an eigenvector
of a linearization has $x \neq 0$.

Block matrices are `Matrix.fromBlocks`, and the vector $(x, u)$ is `Sum.elim x u`. -/
theorem equation_8_7_15 (M C K : Matrix (Fin n) (Fin n) ℂ) {N : Matrix (Fin n) (Fin n) ℂ}
    (hN : IsUnit N) (l : ℂ) :
    (∀ x : Fin n → ℂ, (l ^ 2 • M + l • C + K) *ᵥ x = 0 ↔
      fromBlocks 0 N K C *ᵥ Sum.elim x (l • x) =
        l • (fromBlocks N 0 0 (-M) *ᵥ Sum.elim x (l • x))) ∧
    (∀ x : Fin n → ℂ, (l ^ 2 • M + l • C + K) *ᵥ x = 0 ↔
      fromBlocks (-K) 0 0 N *ᵥ Sum.elim x (l • x) =
        l • (fromBlocks C M N 0 *ᵥ Sum.elim x (l • x))) ∧
    (∀ x u : Fin n → ℂ, fromBlocks 0 N K C *ᵥ Sum.elim x u =
      l • (fromBlocks N 0 0 (-M) *ᵥ Sum.elim x u) → u = l • x) ∧
    (∀ x u : Fin n → ℂ, fromBlocks (-K) 0 0 N *ᵥ Sum.elim x u =
      l • (fromBlocks C M N 0 *ᵥ Sum.elim x u) → u = l • x) := by
  have hinj := (Matrix.mulVec_injective_iff_isUnit).2 hN
  have hNrow : ∀ x u : Fin n → ℂ, N *ᵥ u = l • (N *ᵥ x) → u = l • x := fun x u h =>
    hinj (by rw [h, mulVec_smul])
  have hQ : ∀ x : Fin n → ℂ,
      (l ^ 2 • M + l • C + K) *ᵥ x = l ^ 2 • (M *ᵥ x) + l • (C *ᵥ x) + K *ᵥ x := fun x => by
    rw [add_mulVec, add_mulVec, smul_mulVec, smul_mulVec]
  refine ⟨fun x => ?_, fun x => ?_, fun x u h => ?_, fun x u h => ?_⟩
  · rw [fromBlocks_eq_smul_iff, hQ]
    simp only [zero_mulVec, zero_add, add_zero, mulVec_smul, neg_mulVec, funext_iff,
      Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
      implies_true, true_and]
    exact forall_congr' fun i =>
      ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  · rw [fromBlocks_eq_smul_iff, hQ]
    simp only [zero_mulVec, zero_add, add_zero, mulVec_smul, neg_mulVec, funext_iff,
      Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
      implies_true, and_true]
    exact forall_congr' fun i =>
      ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  · rw [fromBlocks_eq_smul_iff] at h
    simp only [zero_mulVec, zero_add, add_zero] at h
    exact hNrow x u h.1
  · rw [fromBlocks_eq_smul_iff] at h
    simp only [zero_mulVec, zero_add, add_zero] at h
    exact hNrow x u h.2

open scoped ComplexOrder in
/-- **§8.7.9** of [golub2013matrix], damped systems. Let $M, C, K \in \mathbb{C}^{n \times n}$ with
$M$ and $C$ positive definite and $K$ positive semidefinite. If $x \neq 0$ and
$(\lambda^2 M + \lambda C + K) x = 0$, then $\operatorname{Re} \lambda \le 0$.

The source takes $M$, $C$ and $K$ real symmetric. The statement uses the complex Hermitian forms
of these hypotheses. -/
theorem qep_re_nonpos {M C K : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) (hC : C.PosDef)
    (hK : K.PosSemidef) {l : ℂ} {x : Fin n → ℂ} (hx : x ≠ 0)
    (h : (l ^ 2 • M + l • C + K) *ᵥ x = 0) : l.re ≤ 0 := by
  have h1 := (equation_8_7_13 M C K h).1
  have hm := hM.dotProduct_mulVec_pos hx
  have hc := hC.dotProduct_mulVec_pos hx
  have hk := hK.dotProduct_mulVec_nonneg x
  rw [Complex.lt_def] at hm hc
  rw [Complex.le_def] at hk
  simp only [Complex.zero_re, Complex.zero_im] at hm hc hk
  have hre := congrArg Complex.re h1
  have him := congrArg Complex.im h1
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sq,
    Complex.zero_re, Complex.zero_im, ← hm.2, ← hc.2, ← hk.2] at hre him
  by_contra hpos
  push Not at hpos
  have hb : l.im = 0 := by
    have : l.im * (2 * (star x ⬝ᵥ M *ᵥ x).re * l.re + (star x ⬝ᵥ C *ᵥ x).re) = 0 := by
      linear_combination him
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · nlinarith
  rw [hb] at hre
  nlinarith [mul_pos hm.1 (mul_pos hpos hpos), mul_pos hc.1 hpos]

open scoped ComplexOrder in
/-- **§8.7.9** of [golub2013matrix], gyroscopic systems, corrected. Let
$M, C, K \in \mathbb{C}^{n \times n}$ with $M$ positive definite, $C$ skew-Hermitian
($C^H = -C$) and $K$ positive semidefinite. Then:

* if $x \neq 0$ and $(\lambda^2 M + \lambda C + K) x = 0$, then $\lambda$ is purely imaginary,
  $\operatorname{Re} \lambda = 0$;
* for all $\lambda$, $u$ and $x$,
$$\begin{bmatrix} 0 & -K \\ M & 0 \end{bmatrix} \begin{bmatrix} u \\ x \end{bmatrix} = \lambda
  \begin{bmatrix} M & C \\ 0 & M \end{bmatrix} \begin{bmatrix} u \\ x \end{bmatrix}$$
holds if and only if $u = \lambda x$ and $(\lambda^2 M + \lambda C + K) x = 0$.

**Correction.** The source states that the eigenvalues are purely imaginary for $M$ symmetric
positive definite, $C$ skew-symmetric and $K$ symmetric. This requires $K$ to be positive
semidefinite, which the statement assumes; see
`GolubVanLoan.Chapter08.gyroscopic_counterexample`. -/
theorem gyroscopic_eigenvalues_imaginary {M C K : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef)
    (hC : Cᴴ = -C) (hK : K.PosSemidef) :
    (∀ {l : ℂ} {x : Fin n → ℂ}, x ≠ 0 → (l ^ 2 • M + l • C + K) *ᵥ x = 0 → l.re = 0) ∧
      ∀ (l : ℂ) (u x : Fin n → ℂ), fromBlocks 0 (-K) M 0 *ᵥ Sum.elim u x =
          l • (fromBlocks M C 0 M *ᵥ Sum.elim u x) ↔
        u = l • x ∧ (l ^ 2 • M + l • C + K) *ᵥ x = 0 := by
  refine ⟨fun {l x} hx h => ?_, fun l u x => ?_⟩
  · have h1 := (equation_8_7_13 M C K h).1
    have hm := hM.dotProduct_mulVec_pos hx
    have hk := hK.dotProduct_mulVec_nonneg x
    -- `xᴴ C x` is purely imaginary
    have hc : (star x ⬝ᵥ C *ᵥ x).re = 0 := by
      have hIC : (Complex.I • C)ᴴ = Complex.I • C := by
        rw [conjTranspose_smul, hC, Complex.star_def, Complex.conj_I, smul_neg, neg_smul, neg_neg]
      have := star_dotProduct_mulVec_self_of_conjTranspose_eq hIC x
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul, star_mul', Complex.star_def,
        Complex.conj_I] at this
      have him := congrArg Complex.im this
      simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im] at him
      linarith
    rw [Complex.lt_def] at hm
    rw [Complex.le_def] at hk
    simp only [Complex.zero_re, Complex.zero_im] at hm hk
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sq,
      Complex.zero_re, Complex.zero_im, ← hm.2, ← hk.2, hc] at hre him
    by_contra ha
    have hb : (star x ⬝ᵥ C *ᵥ x).im = -(2 * (star x ⬝ᵥ M *ᵥ x).re * l.im) := by
      have : l.re * (2 * (star x ⬝ᵥ M *ᵥ x).re * l.im + (star x ⬝ᵥ C *ᵥ x).im) = 0 := by
        linear_combination him
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 ha
      · linarith
    rw [hb] at hre
    have hsq : 0 < l.re * l.re := mul_self_pos.2 ha
    nlinarith [mul_pos hm.1 hsq, mul_nonneg hm.1.le (mul_self_nonneg l.im)]
  · have hinj := (Matrix.mulVec_injective_iff_isUnit).2 hM.isUnit
    rw [fromBlocks_eq_smul_iff]
    simp only [zero_mulVec, zero_add, add_zero, neg_mulVec]
    constructor
    · rintro ⟨h1, h2⟩
      have hu : u = l • x := hinj (by rw [h2, mulVec_smul])
      refine ⟨hu, ?_⟩
      rw [hu, mulVec_smul] at h1
      rw [add_mulVec, add_mulVec, smul_mulVec, smul_mulVec]
      ext i
      have := congrFun h1 i
      simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      linear_combination -this
    · rintro ⟨rfl, h⟩
      refine ⟨?_, by rw [mulVec_smul]⟩
      rw [add_mulVec, add_mulVec, smul_mulVec, smul_mulVec] at h
      rw [mulVec_smul]
      ext i
      have := congrFun h i
      simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      linear_combination -this

open scoped ComplexOrder in
/-- **§8.7.9** of [golub2013matrix], counterexample for gyroscopic systems. Let $n = 1$, $M = 1$,
$C = 0$ and $K = -1$. Then $M$ is positive definite, $C^H = -C$ and $K$ is Hermitian, and there
are $\lambda$ and $x \neq 0$ with $(\lambda^2 M + \lambda C + K) x = 0$ and
$\operatorname{Re} \lambda \neq 0$ (for example $\lambda = 1$). So the gyroscopic claim of the
source needs $K \succeq 0$. -/
theorem gyroscopic_counterexample :
    let M : Matrix (Fin 1) (Fin 1) ℂ := 1
    let C : Matrix (Fin 1) (Fin 1) ℂ := 0
    let K : Matrix (Fin 1) (Fin 1) ℂ := -1
    M.PosDef ∧ Cᴴ = -C ∧ K.IsHermitian ∧
      ∃ (l : ℂ) (x : Fin 1 → ℂ), x ≠ 0 ∧ (l ^ 2 • M + l • C + K) *ᵥ x = 0 ∧ l.re ≠ 0 := by
  intro M C K
  refine ⟨PosDef.one, by simp [C], by simp [K, IsHermitian], 1, 1, one_ne_zero, ?_, by simp⟩
  simp [M, C, K]

/-- **§8.7.9** of [golub2013matrix], palindromic problems. Let $M, C \in \mathbb{C}^{n \times n}$
with $C^T = C$, and let $Q(\lambda) = \lambda^2 M + \lambda C + M^T$. For $\lambda \neq 0$,
$Q(\lambda)$ is singular if and only if $Q(1/\lambda)$ is singular.

The transpose is the plain transpose, not the conjugate transpose. -/
theorem palindromic_reciprocal {M C : Matrix (Fin n) (Fin n) ℂ} (hC : Cᵀ = C) {l : ℂ}
    (hl : l ≠ 0) :
    (l ^ 2 • M + l • C + Mᵀ).det = 0 ↔ (l⁻¹ ^ 2 • M + l⁻¹ • C + Mᵀ).det = 0 := by
  have key : l⁻¹ ^ 2 • M + l⁻¹ • C + Mᵀ = l⁻¹ ^ 2 • (l ^ 2 • M + l • C + Mᵀ)ᵀ := by
    rw [transpose_add, transpose_add, transpose_smul, transpose_smul, transpose_transpose, hC,
      smul_add, smul_add, smul_smul, smul_smul]
    have h1 : l⁻¹ ^ 2 * l ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl, one_pow]
    have h2 : l⁻¹ ^ 2 * l = l⁻¹ := by field_simp
    rw [h1, h2, one_smul]
    abel
  rw [key, det_smul, det_transpose, mul_eq_zero, or_iff_right (pow_ne_zero _ (pow_ne_zero _
    (inv_ne_zero hl)))]

/-- **Equations (8.7.17)–(8.7.18)** of [golub2013matrix]. Let $M, C \in \mathbb{C}^{n \times n}$,
$\lambda \in \mathbb{C}$ and $y, z \in \mathbb{C}^n$. If
$$\begin{bmatrix} M^T & M^T \\ C - M & M^T \end{bmatrix} \begin{bmatrix} y \\ z \end{bmatrix} =
  \lambda \begin{bmatrix} -M & M^T - C \\ -M & -M \end{bmatrix} \begin{bmatrix} y \\ z
  \end{bmatrix},$$
then $(\lambda^2 M + \lambda C + M^T)(y + z) = 0$. -/
theorem equation_8_7_18 {M C : Matrix (Fin n) (Fin n) ℂ} {l : ℂ} {y z : Fin n → ℂ}
    (h : fromBlocks Mᵀ Mᵀ (C - M) Mᵀ *ᵥ Sum.elim y z =
      l • (fromBlocks (-M) (Mᵀ - C) (-M) (-M) *ᵥ Sum.elim y z)) :
    (l ^ 2 • M + l • C + Mᵀ) *ᵥ (y + z) = 0 := by
  rw [fromBlocks_eq_smul_iff] at h
  obtain ⟨h1, h2⟩ := h
  ext i
  have e1 := congrFun h1 i
  have e2 := congrFun h2 i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_mulVec, neg_mulVec, Pi.sub_apply,
    Pi.neg_apply] at e1 e2
  simp only [add_mulVec, smul_mulVec, mulVec_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  linear_combination e1 + l * e2

end GolubVanLoan.Chapter08
