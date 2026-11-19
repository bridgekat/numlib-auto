/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.GeneralizedSchur
import Mathlib.Data.Matrix.Composition
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter07.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section05

/-!
# Golub and Van Loan, Section 7.7: The generalized eigenvalue problem

This module formalizes §7.7 of [golub2013matrix]. For $A, B \in \mathbb{C}^{n \times n}$, the
eigenvalues of the pencil $A - \lambda B$ are the elements of $\lambda(A, B) = \{\lambda \in
\mathbb{C} : \det(A - \lambda B) = 0\}$. §7.7.1 shows that there are $n$ eigenvalues exactly when
$B$ has full rank, that $\lambda(A, B)$ can be finite, empty or all of $\mathbb{C}$ when $B$ is
singular, and that equivalent pencils $Q^{-1} A Z - \lambda Q^{-1} B Z$ have the same eigenvalues
(7.7.2). The generalized Schur decomposition (Theorem 7.7.1) makes $Q^H A Z$ and $Q^H B Z$ upper
triangular with unitary $Q$ and $Z$, and the eigenvalues are the ratios of the diagonal entries. Its
real form (Theorem 7.7.2) makes $Q^T A Z$ upper quasi-triangular and $Q^T B Z$ upper triangular with
orthogonal $Q$ and $Z$.

The QZ algorithm computes the real form. Algorithm 7.7.1 reduces $(A, B)$ to Hessenberg–triangular
form. A zero subdiagonal entry of $A$ decouples the pencil (§7.7.5), and a zero diagonal entry of
$B$ can be chased down to deflate it. The QZ step (Algorithm 7.7.2) is a Francis double-shift step
on $AB^{-1}$ that never forms $AB^{-1}$, and the QZ algorithm (Algorithm 7.7.3) repeats deflation,
zero chasing and QZ steps. The module also treats generalized inverse iteration and deflating
subspaces (§7.7.8), and the linearization of a polynomial eigenvalue problem ((7.7.3)–(7.7.6)). The
proofs specialize the backbone modules `Numlib.Eigen.Pencil` and
`Numlib.LinearAlgebra.Matrix.GeneralizedSchur`, and the QR algorithm of §7.5.

## Main definitions

* Algorithm 7.7.1, `GolubVanLoan.Chapter07.algorithm_7_7_1`: the Hessenberg–triangular reduction.
* §7.7.5, `GolubVanLoan.Chapter07.qzZeroChase`: the zero chase that moves a zero diagonal entry of
  $B$ to the bottom of a block and zeroes the last subdiagonal entry of $A$.
* Algorithm 7.7.2, `GolubVanLoan.Chapter07.algorithm_7_7_2`: the QZ step, with its shift vector
  `GolubVanLoan.Chapter07.qzShiftVector` and loop body `GolubVanLoan.Chapter07.qzStep`.
* Algorithm 7.7.3, `GolubVanLoan.Chapter07.algorithm_7_7_3`: the QZ algorithm, with one pass
  `GolubVanLoan.Chapter07.qzPass` and the deflation sweep `GolubVanLoan.Chapter07.qzDeflate`.
* (7.7.5), `GolubVanLoan.Chapter07.cubicPencil`: the companion pencil of a cubic matrix polynomial.
* (7.7.6), `GolubVanLoan.Chapter07.linearizationS`, `GolubVanLoan.Chapter07.linearizationDiag`,
  `GolubVanLoan.Chapter07.linearizationT` and `GolubVanLoan.Chapter07.linearizationPencil`: the
  factors $S(\lambda)$, $\operatorname{diag}(P(\lambda), I)$, $T(\lambda)$ and the pencil
  $L(\lambda)$ of the linearization.

## Main results

* §7.7.1, `GolubVanLoan.Chapter07.pencilSpectrum_card`: $\det(A - \lambda B)$ has degree $n$ if and
  only if $\operatorname{rank} B = n$.
* §7.7.1, `GolubVanLoan.Chapter07.pencil_examples`: three pencils with a finite, an empty and the
  full spectrum.
* §7.7.1, `GolubVanLoan.Chapter07.pencilSpectrum_inv`: $1/\lambda \in \lambda(B, A)$ for
  $0 \neq \lambda \in \lambda(A, B)$, and $\lambda(A, B) = \lambda(B^{-1} A)$ for nonsingular $B$.
* (7.7.2), `GolubVanLoan.Chapter07.equation_7_7_2`: equivalent pencils have the same eigenvalues and
  corresponding eigenvectors.
* Theorem 7.7.1, `GolubVanLoan.Chapter07.theorem_7_7_1` and
  `GolubVanLoan.Chapter07.theorem_7_7_1_spectrum`: the generalized Schur decomposition and the
  eigenvalues that it shows.
* Theorem 7.7.2, `GolubVanLoan.Chapter07.theorem_7_7_2`: the generalized real Schur decomposition.
* §7.7.4, `GolubVanLoan.Chapter07.exists_hessenbergTriangular`: the Hessenberg–triangular form
  exists.
* Algorithm 7.7.1, `GolubVanLoan.Chapter07.algorithm_7_7_1_spec`: the reduction computes a
  Hessenberg–triangular form.
* §7.7.5, `GolubVanLoan.Chapter07.pencil_decouple`: a block upper triangular pencil decouples.
* §7.7.5, `GolubVanLoan.Chapter07.qzZeroChase_spec`: the zero chase moves a zero of $B$'s diagonal
  to the end of the block and zeroes the last subdiagonal entry of $A$ there.
* Algorithm 7.7.2, `GolubVanLoan.Chapter07.algorithm_7_7_2_spec`: the QZ step is a Francis step on
  $AB^{-1}$.
* Algorithm 7.7.2, `GolubVanLoan.Chapter07.algorithm_7_7_2_window`: the QZ step on a diagonal block
  is a Francis step on $A_{22} B_{22}^{-1}$.
* Algorithm 7.7.3, `GolubVanLoan.Chapter07.qzPass_isQZPass`: each pass of the QZ algorithm is a
  deflation followed by a zero chase or a QZ step.
* Algorithm 7.7.3, `GolubVanLoan.Chapter07.algorithm_7_7_3_spec`: the QZ algorithm computes a
  generalized real Schur form of a small perturbation of the pencil when it finishes.
* §7.7.8, `GolubVanLoan.Chapter07.generalizedInverseIteration_eq`: generalized inverse iteration is
  inverse iteration for $B^{-1} A$.
* §7.7.8, `GolubVanLoan.Chapter07.deflatingSubspace_of_generalizedSchur`: the leading columns of $Z$
  in a generalized Schur form span deflating subspaces.
* (7.7.3)–(7.7.5), `GolubVanLoan.Chapter07.equation_7_7_5`: a cubic eigenvalue problem and its
  companion pencil have the same eigenvalues.
* (7.7.6), `GolubVanLoan.Chapter07.equation_7_7_6`: $S(\lambda) \operatorname{diag}(P(\lambda), I)
  T(\lambda) = L(\lambda)$ with constant nonzero determinants of $S(\lambda)$ and $T(\lambda)$.

## Conventions

* $\lambda(A, B)$ is the backbone's `Matrix.pencilSpectrum A B` $= \{z : \det(A - zB) = 0\}$, an
  eigenvector of the pencil is `Matrix.HasPencilEigenvector`, and $\det(A - \lambda B)$ as a
  polynomial in $\lambda$ is `Matrix.pencilPoly A B`.
* The theory of §7.7.1–7.7.2 and §7.7.8–7.7.9 is over `Matrix (Fin n) (Fin n) ℂ`. The real Schur
  form and the algorithms are over `Matrix (Fin n) (Fin n) ℝ`.
* Indices are 0-based. A block partition is `Matrix.fromBlocks`. The source's "diagonal block
  $A_{22}$" of the QZ algorithm is the block of consecutive indices $p, \dots, r$.

## Implementation notes

* Algorithms 7.7.1–7.7.3 and the zero chase are programs in the algorithm conventions of
  `NumlibSurface.GolubVanLoan`, with a rounding hook. They call the programs of Chapter 5:
  Householder QR (`GolubVanLoan.Chapter05.algorithm_5_2_1`), `GolubVanLoan.Chapter05.houseOn`,
  `GolubVanLoan.Chapter05.householderApplyLeft`, `GolubVanLoan.Chapter05.householderApplyRight`,
  `GolubVanLoan.Chapter05.algorithm_5_1_3` (the source's `givens`),
  `GolubVanLoan.Chapter05.givensApplyLeft` and `GolubVanLoan.Chapter05.givensApplyRight`.
* The arrays are carried in `GolubVanLoan.Chapter07.QZArrays`: $A$, $B$ and the accumulated $Q$ and
  $Z$. The QZ step and the zero chase act on a block $p, \dots, r$ of consecutive indices of the
  whole arrays; this is the source's update by $\operatorname{diag}(I_p, \cdot, I_q)$. A Householder
  matrix that acts on a row is `house` on the reversed index list.
* The exact semantics of Algorithm 7.7.1 and of the zero chase use the invariant
  `GolubVanLoan.Chapter07.QZArrays.IsEquiv`, $(A, B) = (Q^T A_0 Z, Q^T B_0 Z)$ with orthogonal $Q$
  and $Z$.
* The exact semantics of the QZ step on a block (`GolubVanLoan.Chapter07.algorithm_7_7_2_block`)
  rests on a bulge-chasing invariant: the bulge of $A$ below the subdiagonal and of $B$ below the
  diagonal. On the whole pencil the step is a Francis step on $AB^{-1}$
  (`GolubVanLoan.Chapter07.algorithm_7_7_2_spec`), by the implicit Q theorem and the first column
  $(M - aI)(M - bI) e_1$ that `GolubVanLoan.Chapter07.qzShiftVector` computes
  (`GolubVanLoan.Chapter07.isFrancisStep_of_qz`). On a window it is a QZ step on the blocks $A_{22}$
  and $B_{22}$ (`GolubVanLoan.Chapter07.algorithm_7_7_2_window`,
  `GolubVanLoan.Chapter07.IsQZStepOn`).
* The exact semantics of the QZ algorithm (`GolubVanLoan.Chapter07.algorithm_7_7_3_spec`) is a
  statement with a perturbation. Its deflation sweep is the sweep of Algorithm 7.5.2
  (`GolubVanLoan.Chapter07.qzDeflate_pure_eq`, `GolubVanLoan.Chapter07.qrDeflate_spec`), while the
  zero chase and the QZ steps are exact equivalences. Each pass is the source's loop body
  (`GolubVanLoan.Chapter07.qzPass_isQZPass`, `GolubVanLoan.Chapter07.IsQZPass`): a deflation, then
  the zero chase (`GolubVanLoan.Chapter07.IsQZChasePass`) or a QZ step on the unreduced block
  (`GolubVanLoan.Chapter07.IsQZStepPass`).
* `GolubVanLoan.Chapter07.equation_7_7_6` states the linearization on the index type
  `Fin d × Fin n`, through `Matrix.comp` of block matrices.

## Deviations from the source

* **§7.7.1, the pencil eigenvalue count** (reading).
  `GolubVanLoan.Chapter07.pencilSpectrum_card` states degree of the determinant polynomial,
  which counts eigenvalues with multiplicity when the determinant polynomial is nonzero.
* **§7.7.5, the zero chase** (typo). The penultimate source diagram prints $BZ_{34}^T$ alongside
  $AZ_{34}$. `GolubVanLoan.Chapter07.qzZeroChase` applies the same right factor to both arrays.
* **Algorithm 7.7.2** (reading). `GolubVanLoan.Chapter07.algorithm_7_7_2` acts on a window and
  returns reflector lists. Its exact full-window theorem uses an order of at least three and
  compares with the Francis polynomial-factorization condition. The product on the left of the
  source's similarity relation is the updated $\bar A\bar B^{-1}$.
* **Algorithm 7.7.3** (reading). `GolubVanLoan.Chapter07.algorithm_7_7_3` always accumulates
  both orthogonal factors and returns a stop flag after bounded work. Its exact specification
  bounds threshold deflations of $A$ in Frobenius norm and gives quasi-triangular $T$ upon
  stopping.
* **Equations (7.7.5)–(7.7.6)** (reading). `GolubVanLoan.Chapter07.equation_7_7_5` corrects
  missing factors of $x$ in the elimination and proves the converse kernel relation.
  `GolubVanLoan.Chapter07.equation_7_7_6` establishes the factorization for all coefficients,
  including cases where the leading coefficient vanishes.
* **§7.7.8, generalized inverse iteration** (typo). The source prints the eigenvalue estimate as
  $\lambda^{(k)} = q^{(k)H} A q^{(k)} / q^{(k)H} A q^{(k)}$; the denominator is
  $q^{(k)H} B q^{(k)}$. See `GolubVanLoan.Chapter07.generalizedInverseIteration_eq`.

## Not formalized

* **The Kronecker canonical form.** The source mentions it but does not state it.
* **The 7-digit example.**
* **Stewart's chordal-metric bound and Wilkinson's remark on $t_{kk} = s_{kk} = 0$.** The bound is
  first order and quoted without proof.
* **The backward stability of QZ.** The source states it with $\approx$ and gives no derivation.
* **Flop counts.**
-/

open Matrix Polynomial

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.7.1 Background -/

/-- **§7.7.1** of [golub2013matrix]: "there are $n$ eigenvalues if and only if
$\operatorname{rank}(B) = n$". Let $A, B \in \mathbb{C}^{n \times n}$. The characteristic
polynomial $\det(A - \lambda B)$ has degree $n$ if and only if $\operatorname{rank} B = n$.

The polynomial is `Matrix.pencilPoly A B`, and its degree is `Polynomial.natDegree`.

**Reading.** The source’s count is a polynomial degree statement, hence a count with algebraic
multiplicity when the pencil determinant is nonzero. The left side is not the cardinality of
the set of distinct eigenvalues. -/
theorem pencilSpectrum_card (A B : Matrix (Fin n) (Fin n) ℂ) :
    (pencilPoly A B).natDegree = n ↔ B.rank = n := by
  have h := natDegree_pencilPoly_eq_card_iff A B
  rw [Fintype.card_fin] at h
  rw [h, ← isUnit_iff_isUnit_det]
  exact ⟨fun h => by rw [rank_of_isUnit B h, Fintype.card_fin], fun h =>
    isUnit_of_rank_eq_card (by rw [h, Fintype.card_fin])⟩

/-- **§7.7.1** of [golub2013matrix], the three pencils. When $B$ is singular, $\lambda(A, B)$ can be
finite, empty or all of $\mathbb{C}$: $$\lambda\left(\begin{bmatrix} 1 & 2 \\ 0 & 3
\end{bmatrix}, \begin{bmatrix} 1 & 0 \\ 0 & 0 \end{bmatrix}\right) = \{1\}, \quad
\lambda\left(\begin{bmatrix} 1 & 2 \\ 0 & 3 \end{bmatrix}, \begin{bmatrix} 0 & 1 \\ 0 & 0
\end{bmatrix}\right) = \emptyset, \quad \lambda\left(\begin{bmatrix} 1 & 2 \\ 0 & 0
\end{bmatrix}, \begin{bmatrix} 1 & 0 \\ 0 & 0 \end{bmatrix}\right) = \mathbb{C}.$$
-/
theorem pencil_examples :
    pencilSpectrum !![(1 : ℂ), 2; 0, 3] !![1, 0; 0, 0] = {1} ∧
      pencilSpectrum !![(1 : ℂ), 2; 0, 3] !![0, 1; 0, 0] = ∅ ∧
      pencilSpectrum !![(1 : ℂ), 2; 0, 0] !![1, 0; 0, 0] = Set.univ := by
  have ha : ∀ μ : ℂ, (!![(1 : ℂ), 2; 0, 3] - μ • !![1, 0; 0, 0]).det = 3 * (1 - μ) := fun μ => by
    rw [det_fin_two]
    simp
    ring
  have hb : ∀ μ : ℂ, (!![(1 : ℂ), 2; 0, 3] - μ • !![0, 1; 0, 0]).det = 3 := fun μ => by
    rw [det_fin_two]
    simp
  have hc : ∀ μ : ℂ, (!![(1 : ℂ), 2; 0, 0] - μ • !![1, 0; 0, 0]).det = 0 := fun μ => by
    rw [det_fin_two]
    simp
  refine ⟨?_, ?_, ?_⟩ <;> ext μ
  · rw [Set.mem_singleton_iff, mem_pencilSpectrum_iff_det, ha]
    constructor
    · intro h
      have h1 : (1 : ℂ) - μ = 0 := by
        rcases mul_eq_zero.1 h with h3 | h3
        · norm_num at h3
        · exact h3
      exact (sub_eq_zero.1 h1).symm
    · rintro rfl
      ring
  · rw [mem_pencilSpectrum_iff_det, hb]
    simp
  · rw [mem_pencilSpectrum_iff_det, hc]
    simp

/-- **§7.7.1** of [golub2013matrix]. Let $A, B \in \mathbb{C}^{n \times n}$. If
$\lambda \in \lambda(A, B)$ and $\lambda \neq 0$, then $1/\lambda \in \lambda(B, A)$. If $B$ is
nonsingular, then $$\lambda(A, B) = \lambda(B^{-1} A, I) = \lambda(B^{-1} A).$$
-/
theorem pencilSpectrum_inv (A B : Matrix (Fin n) (Fin n) ℂ) :
    (∀ μ : ℂ, μ ≠ 0 → μ ∈ pencilSpectrum A B → μ⁻¹ ∈ pencilSpectrum B A) ∧
      (IsUnit B → pencilSpectrum A B = pencilSpectrum (B⁻¹ * A) 1 ∧
        pencilSpectrum (B⁻¹ * A) 1 = spectrum ℂ (B⁻¹ * A)) :=
  ⟨fun _ hμ h => inv_mem_pencilSpectrum_swap hμ h, fun hB =>
    ⟨by rw [pencilSpectrum_one, pencilSpectrum_eq_spectrum_of_isUnit A hB],
      pencilSpectrum_one _⟩⟩

/-- **Equation (7.7.2)** of [golub2013matrix], equivalent pencils. Let
$A, B, Q, Z \in \mathbb{C}^{n \times n}$ with $Q$ and $Z$ nonsingular, and let
$A_1 = Q^{-1} A Z$ and $B_1 = Q^{-1} B Z$. Then $\lambda(A, B) = \lambda(A_1, B_1)$, and for
every $\lambda \in \mathbb{C}$ and $y \in \mathbb{C}^n$, $$A_1 y = \lambda B_1 y \iff Ax =
\lambda Bx, \qquad x = Zy.$$
-/
theorem equation_7_7_2 {A B Q Z : Matrix (Fin n) (Fin n) ℂ} (hQ : IsUnit Q) (hZ : IsUnit Z) :
    pencilSpectrum A B = pencilSpectrum (Q⁻¹ * A * Z) (Q⁻¹ * B * Z) ∧
      ∀ (μ : ℂ) (y : Fin n → ℂ),
        (Q⁻¹ * A * Z) *ᵥ y = μ • ((Q⁻¹ * B * Z) *ᵥ y) ↔ A *ᵥ (Z *ᵥ y) = μ • (B *ᵥ (Z *ᵥ y)) := by
  have hQd : IsUnit Q.det := (isUnit_iff_isUnit_det Q).1 hQ
  have hQi : IsUnit Q⁻¹ := (isUnit_nonsing_inv_iff).2 hQ
  refine ⟨(pencilSpectrum_mul_mul_of_isUnit A B hQi hZ).symm, fun μ y => ?_⟩
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, (Q⁻¹ * M * Z) *ᵥ y = Q⁻¹ *ᵥ (M *ᵥ (Z *ᵥ y)) :=
    fun M => by simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [key A, key B, ← mulVec_smul]
  constructor
  · intro h
    have h' := congrArg (Q *ᵥ ·) h
    simpa [mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hQd] using h'
  · intro h
    rw [h]

/-! ### §7.7.2 The generalized Schur decomposition -/

/-- **Theorem 7.7.1** of [golub2013matrix] (generalized Schur decomposition), existence. For
$A, B \in \mathbb{C}^{n \times n}$ there are unitary $Q$ and $Z$ such that $Q^H A Z = T$ and
$Q^H B Z = S$ are upper triangular.

The decomposition exists for every pair, whether the pencil is regular or not. The proof applies
the backbone's generalized Schur decomposition of
`Numlib.LinearAlgebra.Matrix.GeneralizedSchur`. -/
theorem theorem_7_7_1 (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Q ∈ unitaryGroup (Fin n) ℂ, ∃ Z ∈ unitaryGroup (Fin n) ℂ,
      (star Q * A * Z).IsUpperTriangular ∧ (star Q * B * Z).IsUpperTriangular :=
  exists_generalizedSchur A B

/-- **Theorem 7.7.1** of [golub2013matrix], the eigenvalues. Let
$A, B, Q, Z \in \mathbb{C}^{n \times n}$ with $Q$ and $Z$ unitary, and let $T = Q^H A Z$ and
$S = Q^H B Z$ be upper triangular. Then for every $\lambda \in \mathbb{C}$, $$\det(A - \lambda
B) = \det(Q Z^H) \prod_{i=1}^n (t_{ii} - \lambda s_{ii}).$$ If $t_{kk} = s_{kk} = 0$ for some
$k$, then $\lambda(A, B) = \mathbb{C}$. Otherwise $\lambda(A, B) = \{t_{ii} / s_{ii} : s_{ii}
\neq 0\}$. -/
theorem theorem_7_7_1_spectrum {A B Q Z : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (hZ : Z ∈ unitaryGroup (Fin n) ℂ)
    (hT : (star Q * A * Z).IsUpperTriangular) (hS : (star Q * B * Z).IsUpperTriangular) :
    (∀ μ : ℂ, (A - μ • B).det =
      (Q * star Z).det * ∏ i, ((star Q * A * Z) i i - μ * (star Q * B * Z) i i)) ∧
    ((∃ k, (star Q * A * Z) k k = 0 ∧ (star Q * B * Z) k k = 0) → pencilSpectrum A B = Set.univ) ∧
    ((¬ ∃ k, (star Q * A * Z) k k = 0 ∧ (star Q * B * Z) k k = 0) →
      pencilSpectrum A B =
        {μ | ∃ i, (star Q * B * Z) i i ≠ 0 ∧ μ = (star Q * A * Z) i i / (star Q * B * Z) i i}) := by
  set T := star Q * A * Z
  set S := star Q * B * Z
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hZZ : Z * star Z = 1 := mem_unitaryGroup_iff.1 hZ
  have hQu : IsUnit (star Q) := (isUnit_iff_isUnit_det _).2
    (isUnit_det_of_left_inverse hQQ)
  have hZu : IsUnit Z := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hZZ)
  have hspec : pencilSpectrum A B = {μ | ∃ i, T i i = μ * S i i} := by
    rw [← pencilSpectrum_eq_of_isUpperTriangular hT hS]
    exact (pencilSpectrum_mul_mul_of_isUnit A B hQu hZu).symm
  refine ⟨fun μ => ?_, fun ⟨k, hk1, hk2⟩ => ?_, fun hno => ?_⟩
  · have hdecomp : A - μ • B = Q * (T - μ • S) * star Z := by
      simp only [T, S, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hZZ, Matrix.mul_one]
    have hup : (T - μ • S).IsUpperTriangular := fun i j hij => by
      simp [Matrix.sub_apply, hT hij, hS hij]
    rw [hdecomp, det_mul, det_mul, det_of_isUpperTriangular hup, det_mul]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [hspec]
    exact Set.eq_univ_of_forall fun μ => ⟨k, by rw [hk1, hk2, mul_zero]⟩
  · rw [hspec]
    ext μ
    constructor
    · rintro ⟨i, hi⟩
      have hSi : S i i ≠ 0 := fun h0 => hno ⟨i, by rw [hi, h0, mul_zero], h0⟩
      exact ⟨i, hSi, by rw [hi, mul_div_cancel_right₀ _ hSi]⟩
    · rintro ⟨i, hSi, rfl⟩
      exact ⟨i, by rw [div_mul_cancel₀ _ hSi]⟩

/-- **Theorem 7.7.2** of [golub2013matrix] (generalized real Schur decomposition). For
$A, B \in \mathbb{R}^{n \times n}$ there are orthogonal $Q$ and $Z$ such that $Q^T A Z$ is upper
quasi-triangular and $Q^T B Z$ is upper triangular. -/
theorem theorem_7_7_2 (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ,
      (Qᵀ * A * Z).IsQuasiUpperTriangular ∧ (Qᵀ * B * Z).IsUpperTriangular :=
  exists_orthogonal_pencil_isQuasiUpperTriangular A B

/-! ### §7.7.4 Hessenberg–triangular form -/

/-- **§7.7.4** of [golub2013matrix], existence of the Hessenberg–triangular form. For
$A, B \in \mathbb{R}^{n \times n}$ there are orthogonal $Q$ and $Z$ such that $Q^T A Z$ is upper
Hessenberg and $Q^T B Z$ is upper triangular.

The proof applies Theorem 7.7.2, since an upper quasi-triangular matrix is upper Hessenberg. -/
theorem exists_hessenbergTriangular (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ,
      (Qᵀ * A * Z).IsUpperHessenberg ∧ (Qᵀ * B * Z).IsUpperTriangular := by
  obtain ⟨Q, hQ, Z, hZ, hA, hB⟩ := theorem_7_7_2 A B
  exact ⟨Q, hQ, Z, hZ, hA.isUpperHessenberg, hB⟩

/-- The working arrays of the QZ programs: the pencil $(A, B)$, which the programs overwrite with
$(Q^T A Z, Q^T B Z)$, and the accumulated orthogonal factors $Q$ and $Z$ (the source's "if $Q$
and $Z$ are desired"). -/
structure QZArrays (n : ℕ) where
  /-- The array that is overwritten by $Q^T A Z$. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The array that is overwritten by $Q^T B Z$. -/
  B : Matrix (Fin n) (Fin n) ℝ
  /-- The accumulated left factor $Q$. -/
  Q : Matrix (Fin n) (Fin n) ℝ
  /-- The accumulated right factor $Z$. -/
  Z : Matrix (Fin n) (Fin n) ℝ

section Programs

open GolubVanLoan.Chapter05

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One rotation pair of Algorithm 7.7.1 of [golub2013matrix], for the column $j$ and a row
$i \ge j + 2$, with $k = i - 1$ (0-based):
```
[c, s] = givens(A(i-1, j), A(i, j))
A(i-1:i, j:n) = [c s; -s c]ᵀ A(i-1:i, j:n)
B(i-1:i, i-1:n) = [c s; -s c]ᵀ B(i-1:i, i-1:n)
[c, s] = givens(-B(i, i), B(i, i-1))
B(1:i, i-1:i) = B(1:i, i-1:i) [c s; -s c]
A(1:n, i-1:i) = A(1:n, i-1:i) [c s; -s c]
```
The first rotation is accumulated into $Q$ and the second into $Z$, each by a multiplication on
the right that acts on all rows. The negation $-B(i, i)$ is exact. -/
noncomputable def hessTriStep (j i : Fin n) (st : QZArrays n) : M (QZArrays n) := do
  let k : Fin n := ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  let g ← algorithm_5_1_3 rnd (st.A k j) (st.A i j)
  let A ← givensApplyLeft rnd k i g.1 g.2 (indexFrom n j) st.A
  let B ← givensApplyLeft rnd k i g.1 g.2 (indexFrom n k) st.B
  let Q ← givensApplyRight rnd k i g.1 g.2 (List.finRange n) st.Q
  let h ← algorithm_5_1_3 rnd (-B i i) (B i k)
  let B ← givensApplyRight rnd k i h.1 h.2 ((List.finRange n).filter fun r => (r : ℕ) ≤ i) B
  let A ← givensApplyRight rnd k i h.1 h.2 (List.finRange n) A
  let Z ← givensApplyRight rnd k i h.1 h.2 (List.finRange n) st.Z
  pure ⟨A, B, Q, Z⟩

/-- **Algorithm 7.7.1** of [golub2013matrix] (Hessenberg–triangular reduction). Given $A$ and $B$ in
$\mathbb{R}^{n \times n}$, the algorithm overwrites $A$ with an upper Hessenberg matrix
$Q^T A Z$ and $B$ with an upper triangular matrix $Q^T B Z$, where $Q$ and $Z$ are orthogonal:
```
Compute the factorization B = QR using Algorithm 5.2.1
    and overwrite A with QᵀA and B with QᵀB.
for j = 1:n-2
    for i = n:-1:j+2
        (the rotation pair of hessTriStep)
    end
end
```
The program returns $(Q^T A Z, Q^T B Z, Q, Z)$ as a `GolubVanLoan.Chapter07.QZArrays`. Its exact
semantics is `GolubVanLoan.Chapter07.algorithm_7_7_1_spec`.

The product $Q^T A$ applies the reflector data of Algorithm 5.2.1, the stored vectors with the
returned $\beta$, to $A$ in order (`GolubVanLoan.Chapter05.householderApplyLeft` on the rows
from $j$ on and all columns); the reflectors are never rebuilt from the vectors. The product
$Q^T B = R$ is the upper triangular part of the overwritten array. $Q$ is accumulated from the
same data by `GolubVanLoan.Chapter05.backwardAccumulation` and then updated by every row
rotation; $Z$ starts at $I$ and is updated by every column rotation. The inner loop
$i = n{:}{-1}{:}j{+}2$ runs over the reversed index list with the guard $j + 2 \le i$. -/
noncomputable def algorithm_7_7_1 (A B : Matrix (Fin n) (Fin n) ℝ) : M (QZArrays n) := do
  let qr ← algorithm_5_2_1 rnd B
  let A ← (List.finRange n).foldlM (fun A j =>
    householderApplyLeft rnd (storedHouseholderVec qr.1 j) (qr.2 j) (indexFrom n j)
      (List.finRange n) A) A
  let Q ← backwardAccumulation rnd (storedReflectors qr.1 qr.2)
  (List.finRange n).foldlM (fun st (j : Fin n) =>
    (List.finRange n).reverse.foldlM (fun st (i : Fin n) =>
      if (j : ℕ) + 2 ≤ i then hessTriStep rnd j i st else pure st) st)
    ⟨A, upperPart qr.1, Q, 1⟩

end Programs

section Exact

open GolubVanLoan.Chapter05

/-- A loop invariant indexed by the position in the list: `List.foldl_induction` with the step
quantified over natural indices. -/
private theorem foldl_induction_getElem {α S : Type*} (l : List α) (f : S → α → S)
    (P : ℕ → S → Prop) (s : S) (h0 : P 0 s)
    (h : ∀ (p : ℕ) (hp : p < l.length) (s : S), P p s → P (p + 1) (f s l[p])) :
    P l.length (l.foldl f s) :=
  List.foldl_induction P h0 fun i s hs => h i i.2 s hs

end Exact

section HessTri

open GolubVanLoan.Chapter05

variable {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ}

/-- The invariant of the QZ programs for the initial pencil $(A_0, B_0)$: $Q$ and $Z$ are
orthogonal, $A = Q^T A_0 Z$ and $B = Q^T B_0 Z$. -/
def QZArrays.IsEquiv (A₀ B₀ : Matrix (Fin n) (Fin n) ℝ) (st : QZArrays n) : Prop :=
  st.Q ∈ orthogonalGroup (Fin n) ℝ ∧ st.Z ∈ orthogonalGroup (Fin n) ℝ ∧
    st.A = st.Qᵀ * A₀ * st.Z ∧ st.B = st.Qᵀ * B₀ * st.Z

/-- The columns $c < j$ of $A$ are upper Hessenberg, and column $j$ vanishes below the row $b$:
$a_{rc} = 0$ whenever $r > c + 1$ and either $c < j$, or $c = j$ and $r > b$. -/
def HessCols (A : Matrix (Fin n) (Fin n) ℝ) (j b : ℕ) : Prop :=
  ∀ r c : Fin n, (c : ℕ) + 1 < r → ((c : ℕ) < j ∨ ((c : ℕ) = j ∧ b < r)) → A r c = 0

/-- A row rotation applied to both arrays keeps the invariant
`GolubVanLoan.Chapter07.QZArrays.IsEquiv`. Let $i \neq k$, $c^2 + s^2 = 1$ and
$G = G(i, k, \theta)$ the Givens rotation with cosine $c$ and sine $s$. If $(A, B, Q, Z)$
satisfies the invariant, then so does $(G^T A, G^T B, QG, Z)$. -/
theorem QZArrays.IsEquiv.rot_left {st : QZArrays n} (h : st.IsEquiv A₀ B₀) {i k : Fin n}
    (hik : i ≠ k) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (⟨(givensRotation i k c s)ᵀ * st.A, (givensRotation i k c s)ᵀ * st.B,
      st.Q * givensRotation i k c s, st.Z⟩ : QZArrays n).IsEquiv A₀ B₀ := by
  obtain ⟨hQ, hZ, hA, hB⟩ := h
  refine ⟨Submonoid.mul_mem _ hQ (givensRotation_mem_orthogonalGroup hik hcs), hZ, ?_, ?_⟩ <;>
    simp only [hA, hB, transpose_mul, Matrix.mul_assoc]

/-- A column rotation applied to both arrays keeps the invariant
`GolubVanLoan.Chapter07.QZArrays.IsEquiv`. Let $i \neq k$, $c^2 + s^2 = 1$ and
$G = G(i, k, \theta)$ the Givens rotation with cosine $c$ and sine $s$. If $(A, B, Q, Z)$
satisfies the invariant, then so does $(AG, BG, Q, ZG)$. -/
theorem QZArrays.IsEquiv.rot_right {st : QZArrays n} (h : st.IsEquiv A₀ B₀) {i k : Fin n}
    (hik : i ≠ k) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (⟨st.A * givensRotation i k c s, st.B * givensRotation i k c s, st.Q,
      st.Z * givensRotation i k c s⟩ : QZArrays n).IsEquiv A₀ B₀ := by
  obtain ⟨hQ, hZ, hA, hB⟩ := h
  refine ⟨hQ, Submonoid.mul_mem _ hZ (givensRotation_mem_orthogonalGroup hik hcs), ?_, ?_⟩ <;>
    simp only [hA, hB, Matrix.mul_assoc]

/-- One rotation pair of Algorithm 7.7.1, in exact arithmetic. Let the state satisfy the invariant
`GolubVanLoan.Chapter07.QZArrays.IsEquiv`, let $B$ be upper triangular, let $j + 2 \le i$, and
let the columns of $A$ before $j$ be upper Hessenberg and column $j$ vanish below row $i$. Then
after the step the invariant holds, $B$ is upper triangular, and column $j$ of $A$ vanishes
below row $i - 1$. -/
theorem hessTriStep_spec {st : QZArrays n} (h : st.IsEquiv A₀ B₀)
    (hB : st.B.IsUpperTriangular) {j i : Fin n} (hji : (j : ℕ) + 2 ≤ i)
    (hA : HessCols st.A j i) :
    (Id.run (hessTriStep pure j i st)).IsEquiv A₀ B₀ ∧
      (Id.run (hessTriStep pure j i st)).B.IsUpperTriangular ∧
      HessCols (Id.run (hessTriStep pure j i st)).A j (i - 1) := by
  set k : Fin n := ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ with hk
  have hki : k ≠ i := fun e => by
    have := congrArg Fin.val e; simp [k] at this; omega
  have hkv : (k : ℕ) = i - 1 := rfl
  have hBv : ∀ r c : Fin n, (c : ℕ) < r → st.B r c = 0 := fun r c h => hB (Fin.lt_def.2 h)
  obtain ⟨c, s, hg, hcs, hz⟩ := givens_exact (st.A k j) (st.A i j)
  set A₁ := (givensRotation k i c s)ᵀ * st.A with hA₁
  set B₁ := (givensRotation k i c s)ᵀ * st.B with hB₁
  obtain ⟨c', s', hg', hcs', hz'⟩ := givens_exact (-B₁ i i) (B₁ i k)
  have hA1 : Id.run (givensApplyLeft pure k i c s (indexFrom n j) st.A) = A₁ := by
    refine givensApplyLeft_eq_mul hki c s (nodup_indexFrom n j) fun q hq => ?_
    rw [mem_indexFrom, not_le] at hq
    exact ⟨hA k q (by omega) (Or.inl hq), hA i q (by omega) (Or.inl hq)⟩
  have hB1 : Id.run (givensApplyLeft pure k i c s (indexFrom n k) st.B) = B₁ := by
    refine givensApplyLeft_eq_mul hki c s (nodup_indexFrom n k) fun q hq => ?_
    rw [mem_indexFrom, not_le] at hq
    exact ⟨hBv k q hq, hBv i q (by omega)⟩
  have hB2 : Id.run (givensApplyRight pure k i c' s'
      ((List.finRange n).filter fun r => (r : ℕ) ≤ i) B₁) = B₁ * givensRotation k i c' s' := by
    refine givensApplyRight_eq_mul hki c' s' ((List.nodup_finRange n).filter _) fun r hr => ?_
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, not_le] at hr
    have hrk : r ≠ k := fun e => by rw [e] at hr; omega
    have hri : r ≠ i := fun e => by rw [e] at hr; omega
    rw [hB₁, givensRotation_transpose_mul_apply hki, givensRotation_transpose_mul_apply hki]
    simp only [hrk, hri, ↓reduceIte]
    exact ⟨hBv r k (by omega), hBv r i hr⟩
  have hrun : Id.run (hessTriStep pure j i st) =
      ⟨A₁ * givensRotation k i c' s', B₁ * givensRotation k i c' s',
        st.Q * givensRotation k i c s, st.Z * givensRotation k i c' s'⟩ := by
    simp only [hessTriStep, Id.run_bind, Id.run_pure]
    rw [hg, hA1, hB1]
    simp only
    rw [hg', hB2, givensApplyRight_spec_of_forall_mem hki _ _ (List.nodup_finRange n)
      List.mem_finRange, givensApplyRight_spec_of_forall_mem hki _ _ (List.nodup_finRange n)
      List.mem_finRange, givensApplyRight_spec_of_forall_mem hki _ _ (List.nodup_finRange n)
      List.mem_finRange]
  rw [hrun]
  refine ⟨(h.rot_left hki hcs).rot_right hki hcs', ?_, ?_⟩
  · intro r p hpr
    have hpr' : (p : ℕ) < r := Fin.lt_def.1 hpr
    change (B₁ * givensRotation k i c' s') r p = 0
    have hB₁e : ∀ r' q, r' ≠ k → r' ≠ i → B₁ r' q = st.B r' q := fun r' q h1 h2 => by
      rw [hB₁, givensRotation_transpose_mul_apply hki]
      simp [h1, h2]
    rw [mul_givensRotation_apply hki]
    by_cases hpk : p = k
    · have hkr : (k : ℕ) < r := by rw [← hpk]; exact hpr'
      have hrk : r ≠ k := fun e => by rw [e] at hkr; omega
      simp only [hpk, ↓reduceIte]
      by_cases hri : r = i
      · rw [hri]
        linear_combination hz'
      · have hir : (i : ℕ) < r := by
          have : (r : ℕ) ≠ i := fun e => hri (Fin.ext e)
          omega
        rw [hB₁e r k hrk hri, hB₁e r i hrk hri, hBv r k hkr, hBv r i hir]
        ring
    · by_cases hpi : p = i
      · have hir : (i : ℕ) < r := by rw [← hpi]; exact hpr'
        have hrk : r ≠ k := fun e => by rw [e] at hir; omega
        have hri : r ≠ i := fun e => by rw [e] at hir; omega
        rw [hB₁e r k hrk hri, hB₁e r i hrk hri, hBv r k (by omega), hBv r i hir]
        simp [hpi, hki.symm]
      · simp only [hpk, hpi, ↓reduceIte]
        have hpk' : (p : ℕ) ≠ k := fun e => hpk (Fin.ext e)
        have hpi' : (p : ℕ) ≠ i := fun e => hpi (Fin.ext e)
        by_cases hrk : r = k
        · have h1 : st.B k p = 0 := hBv k p (by rw [← hrk]; exact hpr')
          have h2 : st.B i p = 0 := hBv i p (by
            have : (p : ℕ) < k := by rw [← hrk]; exact hpr'
            omega)
          rw [hrk, hB₁, givensRotation_transpose_mul_apply hki]
          simp [h1, h2]
        · by_cases hri : r = i
          · have h2 : st.B i p = 0 := hBv i p (by rw [← hri]; exact hpr')
            have h1 : st.B k p = 0 := hBv k p (by
              have : (p : ℕ) < i := by rw [← hri]; exact hpr'
              omega)
            rw [hri, hB₁, givensRotation_transpose_mul_apply hki]
            simp [h1, h2, hki.symm]
          · rw [hB₁e r p hrk hri]
            exact hBv r p hpr'
  · intro r q hqr hq
    change (A₁ * givensRotation k i c' s') r q = 0
    have hqk : q ≠ k := fun e => by rw [e] at hq; omega
    have hqi : q ≠ i := fun e => by rw [e] at hq; omega
    rw [mul_givensRotation_apply hki]
    simp only [hqk, hqi, ↓reduceIte, hA₁]
    rw [givensRotation_transpose_mul_apply hki]
    by_cases hrk : r = k
    · subst hrk
      have hq' : (q : ℕ) < j := by omega
      simp [hA _ q (by omega) (Or.inl hq'), hA i q (by omega) (Or.inl hq')]
    · by_cases hri : r = i
      · subst hri
        simp only [hrk, ↓reduceIte]
        rcases hq with hq' | ⟨hq', -⟩
        · simp [hA _ q (by omega) (Or.inl hq'), hA k q (by omega) (Or.inl hq')]
        · have hqj : q = j := Fin.ext hq'
          subst hqj
          linarith
      · simp only [hrk, hri, ↓reduceIte]
        refine hA r q hqr ?_
        rcases hq with hq' | ⟨hq', hr'⟩
        · exact Or.inl hq'
        · refine Or.inr ⟨hq', ?_⟩
          rcases lt_or_gt_of_ne (fun e : (r : ℕ) = i => hri (Fin.ext e)) with h1 | h1
          · exfalso; apply hrk; ext; simp [k]; omega
          · exact h1


/-- `GolubVanLoan.Chapter07.HessCols` is monotone in the row bound: if it holds for $b$, it holds
for every $b' \ge b$. -/
theorem HessCols.mono {A : Matrix (Fin n) (Fin n) ℝ} {j b b' : ℕ} (h : HessCols A j b)
    (hb : b ≤ b') : HessCols A j b' := fun r c hrc hc =>
  h r c hrc (hc.imp_right fun ⟨h1, h2⟩ => ⟨h1, lt_of_le_of_lt hb h2⟩)

/-- If the columns of $A$ before $j$ are upper Hessenberg and column $j$ vanishes below row $j + 1$,
then the columns before $j + 1$ are upper Hessenberg. -/
theorem HessCols.succ {A : Matrix (Fin n) (Fin n) ℝ} {j : ℕ} (h : HessCols A j (j + 1)) :
    HessCols A (j + 1) (n - 1) := fun r c hrc hc => by
  rcases hc with hc | ⟨-, hr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
    · exact h r c hrc (Or.inl hc)
    · exact h r c hrc (Or.inr ⟨hc, by omega⟩)
  · exact absurd r.isLt (by omega)

/-- The inner loop of Algorithm 7.7.1 for the column $j$, in exact arithmetic. If the state
satisfies the invariant `GolubVanLoan.Chapter07.QZArrays.IsEquiv`, $B$ is upper triangular and
the columns of $A$ before $j$ are upper Hessenberg, then after the loop the invariant holds, $B$
is upper triangular and the columns of $A$ before $j + 1$ are upper Hessenberg. -/
theorem hessTri_inner_spec {st : QZArrays n} (h : st.IsEquiv A₀ B₀)
    (hB : st.B.IsUpperTriangular) (j : Fin n) (hA : HessCols st.A j (n - 1)) :
    let st' := Id.run ((List.finRange n).reverse.foldlM (fun st (i : Fin n) =>
      if (j : ℕ) + 2 ≤ i then hessTriStep pure j i st else pure st) st)
    st'.IsEquiv A₀ B₀ ∧ st'.B.IsUpperTriangular ∧ HessCols st'.A (j + 1) (n - 1) := by
  intro st'
  have key := foldl_induction_getElem (List.finRange n).reverse
    (fun st (i : Fin n) => Id.run (if (j : ℕ) + 2 ≤ i then hessTriStep pure j i st else pure st))
    (fun q st => st.IsEquiv A₀ B₀ ∧ st.B.IsUpperTriangular ∧
      HessCols st.A j (max (n - 1 - q) (j + 1))) st
    ⟨h, hB, hA.mono (by omega)⟩ (by
      intro q hq s ⟨hs, hsB, hsA⟩
      have hq' : q < n := by simpa using hq
      have hval : (((List.finRange n).reverse)[q] : ℕ) = n - 1 - q := by
        simp [List.getElem_reverse]
      by_cases hji : (j : ℕ) + 2 ≤ ((List.finRange n).reverse)[q]
      · simp only [hji, ↓reduceIte]
        rw [hval] at hji
        have hmax : max (n - 1 - q) (j + 1) = ((List.finRange n).reverse)[q] := by
          rw [hval]; omega
        obtain ⟨h1, h2, h3⟩ := hessTriStep_spec hs hsB (by rw [hval]; exact hji) (hmax ▸ hsA)
        refine ⟨h1, h2, h3.mono ?_⟩
        rw [hval]
        omega
      · simp only [hji, ↓reduceIte, Id.run_pure]
        rw [hval] at hji
        exact ⟨hs, hsB, hsA.mono (by omega)⟩)
  have hst' : st' = List.foldl
      (fun st (i : Fin n) => Id.run (if (j : ℕ) + 2 ≤ i then hessTriStep pure j i st else pure st))
      st (List.finRange n).reverse := by
    simp only [st', List.idRun_foldlM]
  rw [hst']
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨h1, h2, HessCols.succ (h3.mono ?_)⟩
  simp only [List.length_reverse, List.length_finRange]
  omega

/-- **Algorithm 7.7.1** of [golub2013matrix], exact semantics. Let
$A, B \in \mathbb{R}^{n \times n}$ and let $(A', B', Q, Z)$ be the output of Algorithm 7.7.1 in
exact arithmetic. Then $Q$ and $Z$ are orthogonal, $$A' = Q^T A Z, \qquad B' = Q^T B Z,$$ $A'$
is upper Hessenberg and $B'$ is upper triangular.

Exact arithmetic is the hook `pure` in the monad `Id`. -/
theorem algorithm_7_7_1_spec (A B : Matrix (Fin n) (Fin n) ℝ) :
    (Id.run (algorithm_7_7_1 pure A B)).Q ∈ orthogonalGroup (Fin n) ℝ ∧
      (Id.run (algorithm_7_7_1 pure A B)).Z ∈ orthogonalGroup (Fin n) ℝ ∧
      (Id.run (algorithm_7_7_1 pure A B)).A =
        (Id.run (algorithm_7_7_1 pure A B)).Qᵀ * A * (Id.run (algorithm_7_7_1 pure A B)).Z ∧
      (Id.run (algorithm_7_7_1 pure A B)).B =
        (Id.run (algorithm_7_7_1 pure A B)).Qᵀ * B * (Id.run (algorithm_7_7_1 pure A B)).Z ∧
      (Id.run (algorithm_7_7_1 pure A B)).A.IsUpperHessenberg ∧
      (Id.run (algorithm_7_7_1 pure A B)).B.IsUpperTriangular := by
  set qr := Id.run (algorithm_5_2_1 pure B) with hqr
  have hQR := (algorithm_5_2_1_spec le_rfl B).1
  rw [← hqr] at hQR
  set Q₀ := factoredQ qr.2 qr.1 with hQ₀
  have hQ₀o : Q₀ ∈ orthogonalGroup (Fin n) ℝ := hQR.mem_unitaryGroup
  have hQ₀t : Q₀ᵀ * Q₀ = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hQ₀o
  have hA₁ : Id.run ((List.finRange n).foldlM (fun A j =>
      householderApplyLeft pure (storedHouseholderVec qr.1 j) (qr.2 j) (indexFrom n j)
        (List.finRange n) A) A) = Q₀ᵀ * A := by
    rw [List.idRun_foldlM]
    have hf : (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) =>
        Id.run (householderApplyLeft pure (storedHouseholderVec qr.1 j) (qr.2 j) (indexFrom n j)
          (List.finRange n) A)) = fun A j =>
          (1 - qr.2 j • vecMulVec (storedHouseholderVec qr.1 j) (storedHouseholderVec qr.1 j)) *
            A := by
      funext A j
      exact householderApplyLeft_spec_of_forall_mem (nodup_indexFrom n j) (List.nodup_finRange n)
        List.mem_finRange (fun i hi => storedHouseholderVec_eq_zero qr.1 j hi) _ A
    rw [hf, foldl_mul_eq_transpose_prod_mul _
      (fun j => transpose_one_sub_smul_vecMulVec _ _),
      hQ₀, factoredQ_eq_prod]
  have hQ : Id.run (backwardAccumulation pure (storedReflectors qr.1 qr.2)) = Q₀ :=
    backwardAccumulation_spec _
  have hR : upperPart qr.1 = Q₀ᵀ * B := by
    rw [← hQR.mul_eq, ← Matrix.mul_assoc, hQ₀t, Matrix.one_mul]
  set st₀ : QZArrays n := ⟨Q₀ᵀ * A, upperPart qr.1, Q₀, 1⟩ with hst₀
  have h0 : st₀.IsEquiv A B := ⟨hQ₀o, one_mem _, by simp [st₀], by simp [st₀, hR]⟩
  have h0B : st₀.B.IsUpperTriangular := fun i j hij => hQR.apply_eq_zero i j hij
  have hrun : Id.run (algorithm_7_7_1 pure A B) = List.foldl (fun st (j : Fin n) =>
      Id.run ((List.finRange n).reverse.foldlM (fun st (i : Fin n) =>
        if (j : ℕ) + 2 ≤ i then hessTriStep pure j i st else pure st) st)) st₀
        (List.finRange n) := by
    simp only [algorithm_7_7_1, Id.run_bind]
    rw [← hqr, hA₁, hQ, List.idRun_foldlM]
  have key := foldl_induction_getElem (List.finRange n) (fun st (j : Fin n) =>
      Id.run ((List.finRange n).reverse.foldlM (fun st (i : Fin n) =>
        if (j : ℕ) + 2 ≤ i then hessTriStep pure j i st else pure st) st))
    (fun p st => st.IsEquiv A B ∧ st.B.IsUpperTriangular ∧ HessCols st.A p (n - 1)) st₀
    ⟨h0, h0B, fun r c _ hc => by rcases hc with hc | ⟨hc, hr⟩ <;> omega⟩ (by
      intro p hp s ⟨hs, hsB, hsA⟩
      have hv : (((List.finRange n)[p]) : ℕ) = p := by simp
      obtain ⟨h1, h2, h3⟩ := hessTri_inner_spec hs hsB ((List.finRange n)[p])
        (by rw [hv]; exact hsA)
      have e : p + 1 = ((List.finRange n)[p] : ℕ) + 1 := by rw [hv]
      exact ⟨h1, h2, by rw [e]; exact h3⟩)
  rw [hrun]
  obtain ⟨⟨hQo, hZo, hAe, hBe⟩, hBt, hAh⟩ := key
  refine ⟨hQo, hZo, hAe, hBe, fun r c ⟨k, hck, hkr⟩ => hAh r c ?_ (Or.inl ?_), hBt⟩
  · have := Fin.lt_def.1 hck; have := Fin.lt_def.1 hkr; omega
  · simp

end HessTri

/-! ### §7.7.5 Deflation -/

/-- **§7.7.5** of [golub2013matrix], the first deflation. Let
$A_{11}, B_{11} \in \mathbb{C}^{p \times p}$, $A_{12}, B_{12} \in \mathbb{C}^{p \times q}$ and
$A_{22}, B_{22} \in \mathbb{C}^{q \times q}$. Then for every $\lambda \in \mathbb{C}$,
$$\det\left(\begin{bmatrix} A_{11} & A_{12} \\ 0 & A_{22} \end{bmatrix} - \lambda
\begin{bmatrix} B_{11} & B_{12} \\ 0 & B_{22} \end{bmatrix}\right) = \det(A_{11} - \lambda
B_{11}) \det(A_{22} - \lambda B_{22}),$$ and therefore the spectrum of the block pencil is
$\lambda(A_{11}, B_{11}) \cup \lambda(A_{22}, B_{22})$.

The source applies this when $a_{k+1,k} = 0$ in a Hessenberg–triangular pencil, which makes the
pencil block upper triangular. -/
theorem pencil_decouple {p q : ℕ} (A₁₁ B₁₁ : Matrix (Fin p) (Fin p) ℂ)
    (A₁₂ B₁₂ : Matrix (Fin p) (Fin q) ℂ) (A₂₂ B₂₂ : Matrix (Fin q) (Fin q) ℂ) :
    (∀ μ : ℂ, (fromBlocks A₁₁ A₁₂ 0 A₂₂ - μ • fromBlocks B₁₁ B₁₂ 0 B₂₂).det =
      (A₁₁ - μ • B₁₁).det * (A₂₂ - μ • B₂₂).det) ∧
    pencilSpectrum (fromBlocks A₁₁ A₁₂ 0 A₂₂) (fromBlocks B₁₁ B₁₂ 0 B₂₂) =
      pencilSpectrum A₁₁ B₁₁ ∪ pencilSpectrum A₂₂ B₂₂ := by
  have hdet : ∀ μ : ℂ, (fromBlocks A₁₁ A₁₂ 0 A₂₂ - μ • fromBlocks B₁₁ B₁₂ 0 B₂₂).det =
      (A₁₁ - μ • B₁₁).det * (A₂₂ - μ • B₂₂).det := fun μ => by
    rw [fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, smul_zero, neg_zero,
      add_zero, det_fromBlocks_zero₂₁]
    simp only [← sub_eq_add_neg]
  refine ⟨hdet, ?_⟩
  ext μ
  simp only [Set.mem_union, mem_pencilSpectrum_iff_det, hdet, mul_eq_zero]

section Programs

open GolubVanLoan.Chapter05

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- A column rotation in the columns $l, m$ that zeroes $a_{tl}$, a step of the zero chase:
$[c, s] = \mathtt{givens}(-a_{tm}, a_{tl})$, with the negation exact, and then
$A \leftarrow AG$, $B \leftarrow BG$ and $Z \leftarrow ZG$ for $G = G(l, m, \theta)$ on all
rows. It is the step of Algorithm 7.7.1 that restores $B$, used here to zero an entry of $A$. -/
noncomputable def qzColumnZero (l m t : Fin n) (st : QZArrays n) : M (QZArrays n) := do
  let g ← algorithm_5_1_3 rnd (-st.A t m) (st.A t l)
  let A ← givensApplyRight rnd l m g.1 g.2 (List.finRange n) st.A
  let B ← givensApplyRight rnd l m g.1 g.2 (List.finRange n) st.B
  let Z ← givensApplyRight rnd l m g.1 g.2 (List.finRange n) st.Z
  pure ⟨A, B, st.Q, Z⟩

/-- One step $j$ of the zero chase of §7.7.5 of [golub2013matrix]. The row rotation in the rows
$j, j + 1$ that zeroes $b_{j+1,j+1}$, $[c, s] = \mathtt{givens}(b_{j,j+1}, b_{j+1,j+1})$, is
applied to $A$ and $B$ on all columns and accumulated into $Q$. Then, if $j$ is not the first
index $p$ of the block, the column rotation in the columns $j - 1, j$ zeroes the fill-in
$a_{j+1,j-1}$. -/
noncomputable def qzZeroChaseStep (p : ℕ) (j j₁ : Fin n) (st : QZArrays n) : M (QZArrays n) := do
  let g ← algorithm_5_1_3 rnd (st.B j j₁) (st.B j₁ j₁)
  let A ← givensApplyLeft rnd j j₁ g.1 g.2 (List.finRange n) st.A
  let B ← givensApplyLeft rnd j j₁ g.1 g.2 (List.finRange n) st.B
  let Q ← givensApplyRight rnd j j₁ g.1 g.2 (List.finRange n) st.Q
  if p < (j : ℕ) then
    qzColumnZero rnd ⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ j j₁ ⟨A, B, Q, st.Z⟩
  else pure ⟨A, B, Q, st.Z⟩

/-- **§7.7.5** of [golub2013matrix], zero chasing: "if $b_{kk} = 0$ for some $k$, then it is
possible to introduce a zero in $A$'s $(n, n-1)$ position and thereby deflate. … The zero on
$B$'s diagonal can be 'pushed down' to the $(n, n)$ position". The program acts on the block of
consecutive indices $p, \dots, r$, with the zero of $B$'s diagonal at $k$. For
$j = k, \dots, r - 1$ it applies the row rotation in the rows $j, j + 1$ that zeroes
$b_{j+1,j+1}$ and, for $j > p$, the column rotation in the columns $j - 1, j$ that zeroes the
fill-in $a_{j+1,j-1}$. Finally, if $p < r$, the column rotation in the columns $r - 1, r$ zeroes
$a_{r,r-1}$. All rotations act on the whole arrays and are accumulated into $Q$ and $Z$. If
$r \ge n$, the program returns the state unchanged.

The source's display is the case $p = 0$, $r = n - 1$; Algorithm 7.7.3 runs the program on its
unreduced block. The exact semantics is `GolubVanLoan.Chapter07.qzZeroChase_spec`.

**Typo.** In the example’s penultimate diagram the source writes $BZ_{34}^T$ while applying
$Z_{34}$ on the right of $A$. Lean applies the same right rotation to both arrays, preserving
pencil equivalence. -/
noncomputable def qzZeroChase (p k r : ℕ) (st : QZArrays n) : M (QZArrays n) := do
  let st ← (List.finRange n).foldlM (fun st (j : Fin n) =>
    if h : k ≤ (j : ℕ) ∧ (j : ℕ) < r ∧ r < n then
      qzZeroChaseStep rnd p j ⟨(j : ℕ) + 1, by omega⟩ st
    else pure st) st
  if h : p < r ∧ r < n then
    qzColumnZero rnd ⟨r - 1, by omega⟩ ⟨r, h.2⟩ ⟨r, h.2⟩ st
  else pure st

end Programs

/-! ### §7.7.6 The QZ step -/

/-- The entry $(i, j)$ of a matrix at natural indices: `A i j` if $i, j < n$, and $0$ otherwise. The
QZ programs read the neighbours of the corners of a block with it. -/
def qzEntry (A : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) : ℝ :=
  if h : i < n ∧ j < n then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The state of the loop of the QZ step: the arrays, the reflector data applied so far on each
side, and the current $x, y, z$. -/
structure QZStepState (n : ℕ) where
  /-- The array that is overwritten by $Q^T A Z$. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The array that is overwritten by $Q^T B Z$. -/
  B : Matrix (Fin n) (Fin n) ℝ
  /-- The left reflector data, in the order of application. -/
  dQ : List ((Fin n → ℝ) × ℝ)
  /-- The right reflector data, in the order of application. -/
  dZ : List ((Fin n → ℝ) × ℝ)
  /-- The source's $x$. -/
  x : ℝ
  /-- The source's $y$. -/
  y : ℝ
  /-- The source's $z$. -/
  z : ℝ

section Programs

open GolubVanLoan.Chapter05

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The shift vector of the QZ step of [golub2013matrix] §7.7.6: "Let $M = AB^{-1}$ and compute
$(M - aI)(M - bI)e_1 = [x, y, z, 0, \dots, 0]^T$ where $a$ and $b$ are the eigenvalues of $M$'s
lower 2-by-2", on the block $p, \dots, r$. The source adds that "$v$ can be calculated in $O(1)$
flops": $M$ is upper Hessenberg, and the entries that are needed, in the leading $3 \times 2$
corner and the trailing $2 \times 2$ block, come from row forward substitutions $m_i B = a_i$
over at most three columns. In the local 1-based indices of a block of order $N$,
$$\begin{aligned} &m_{11} = a_{11}/b_{11}, \quad m_{21} = a_{21}/b_{11}, \quad m_{12} =
  (a_{12} - m_{11} b_{12})/b_{22}, \quad m_{22} = (a_{22} - m_{21} b_{12})/b_{22}, \\ &m_{32} =
  a_{32}/b_{22}, \quad e = m_{N-1,N-1}, \quad f = m_{N-1,N}, \quad g = m_{N,N-1}, \quad h =
  m_{NN}, \\ &s = e + h, \quad t = eh - fg, \\ &x = m_{11}^2 + m_{12} m_{21} - s m_{11} + t,
  \quad y = m_{21}(m_{11} + m_{22} - s), \quad z = m_{21} m_{32}. \end{aligned}$$
Here $a + b = s$ and $ab = t$. For a block of order $2$, $z = 0$. Every arithmetic operation is
rounded. -/
noncomputable def qzShiftVector (p r : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) : M (ℝ × ℝ × ℝ) := do
  let a := qzEntry A
  let b := qzEntry B
  let m₁₁ ← rnd (a p p / b p p)
  let m₂₁ ← rnd (a (p + 1) p / b p p)
  let m₁₂ ← rnd ((← rnd (a p (p + 1) - (← rnd (m₁₁ * b p (p + 1))))) / b (p + 1) (p + 1))
  let m₂₂ ← rnd ((← rnd (a (p + 1) (p + 1) - (← rnd (m₂₁ * b p (p + 1))))) / b (p + 1) (p + 1))
  let μ ← if p + 2 ≤ r then rnd (a (r - 1) (r - 2) / b (r - 2) (r - 2)) else pure 0
  let e ← if p + 2 ≤ r then do
      rnd ((← rnd (a (r - 1) (r - 1) - (← rnd (μ * b (r - 2) (r - 1))))) / b (r - 1) (r - 1))
    else pure m₁₁
  let f ← if p + 2 ≤ r then do
      rnd ((← rnd ((← rnd (a (r - 1) r - (← rnd (μ * b (r - 2) r)))) -
        (← rnd (e * b (r - 1) r)))) / b r r)
    else pure m₁₂
  let g ← rnd (a r (r - 1) / b (r - 1) (r - 1))
  let h ← rnd ((← rnd (a r r - (← rnd (g * b (r - 1) r)))) / b r r)
  let s ← rnd (e + h)
  let t ← rnd ((← rnd (e * h)) - (← rnd (f * g)))
  let x ← rnd ((← rnd ((← rnd ((← rnd (m₁₁ * m₁₁)) + (← rnd (m₁₂ * m₂₁)))) -
    (← rnd (s * m₁₁)))) + t)
  let y ← rnd (m₂₁ * (← rnd ((← rnd (m₁₁ + m₂₂)) - s)))
  let z ← if p + 2 ≤ r then do rnd (m₂₁ * (← rnd (a (p + 2) (p + 1) / b (p + 1) (p + 1))))
    else pure 0
  pure (x, y, z)

/-- The loop body of Algorithm 7.7.2 of [golub2013matrix] at the rows $j, j + 1, j + 2$ (the
source's $k, k + 1, k + 2$):
```
Find Householder Q_k so Q_k [x; y; z] = [*; 0; 0].
A = diag(I_{k-1}, Q_k, I_{n-k-2}) · A;  B = diag(I_{k-1}, Q_k, I_{n-k-2}) · B
Find Householder Z_{k1} so [b_{k+2,k} | b_{k+2,k+1} | b_{k+2,k+2}] Z_{k1} = [0 | 0 | *].
A = A · diag(I_{k-1}, Z_{k1}, I_{n-k-2});  B = B · diag(I_{k-1}, Z_{k1}, I_{n-k-2})
Find Householder Z_{k2} so [b_{k+1,k} | b_{k+1,k+1}] Z_{k2} = [0 | *].
A = A · diag(I_{k-1}, Z_{k2}, I_{n-k-1});  B = B · diag(I_{k-1}, Z_{k2}, I_{n-k-1})
x = a_{k+1,k};  y = a_{k+2,k};  if k < n - 2: z = a_{k+3,k}
```
The reflector $Q_k$ is `house` on the index list $[j, j+1, j+2]$. A Householder matrix that acts
on a row is `house` on the reversed list, $[j+2, j+1, j]$ or $[j+1, j]$, whose pivot is the last
entry. The reflectors act on the whole arrays and are recorded in the state. -/
noncomputable def qzStep (r : ℕ) (j j₁ j₂ : Fin n) (st : QZStepState n) : M (QZStepState n) := do
  let u : Fin n → ℝ := fun i =>
    if i = j then st.x else if i = j₁ then st.y else if i = j₂ then st.z else 0
  let q ← houseOn rnd [j, j₁, j₂] u
  let A ← householderApplyLeft rnd q.1 q.2 [j, j₁, j₂] (List.finRange n) st.A
  let B ← householderApplyLeft rnd q.1 q.2 [j, j₁, j₂] (List.finRange n) st.B
  let z₁ ← houseOn rnd [j₂, j₁, j] (B j₂)
  let A ← householderApplyRight rnd z₁.1 z₁.2 (List.finRange n) [j₂, j₁, j] A
  let B ← householderApplyRight rnd z₁.1 z₁.2 (List.finRange n) [j₂, j₁, j] B
  let z₂ ← houseOn rnd [j₁, j] (B j₁)
  let A ← householderApplyRight rnd z₂.1 z₂.2 (List.finRange n) [j₁, j] A
  let B ← householderApplyRight rnd z₂.1 z₂.2 (List.finRange n) [j₁, j] B
  pure ⟨A, B, st.dQ ++ [q], st.dZ ++ [z₁, z₂], A j₁ j, A j₂ j,
    if (j : ℕ) + 3 ≤ r then qzEntry A ((j : ℕ) + 3) j else st.z⟩

/-- **Algorithm 7.7.2** of [golub2013matrix] (the QZ step). "Given an unreduced upper Hessenberg
matrix $A \in \mathbb{R}^{n \times n}$ and a nonsingular upper triangular matrix
$B \in \mathbb{R}^{n \times n}$, the following algorithm overwrites $A$ with the upper
Hessenberg matrix $Q^T A Z$ and $B$ with the upper triangular matrix $Q^T B Z$ where $Q$ and $Z$
are orthogonal and $Q$ has the same first column as the orthogonal similarity transformation in
Algorithm 7.5.1 when it is applied to $AB^{-1}$." The program acts on the block of consecutive
indices $p, \dots, r$ with $p < r < n$. It computes the shift vector
(`GolubVanLoan.Chapter07.qzShiftVector`), runs the loop body `GolubVanLoan.Chapter07.qzStep` for
$k = 1{:}n{-}2$, and finishes with
```
Find Householder Q_{n-1} so Q_{n-1} [x; y] = [*; 0].
A = diag(I_{n-2}, Q_{n-1}) · A;  B = diag(I_{n-2}, Q_{n-1}) · B
Find Householder Z_{n-1} so [b_{n,n-1} | b_{nn}] Z_{n-1} = [0 | *].
A = A · diag(I_{n-2}, Z_{n-1});  B = B · diag(I_{n-2}, Z_{n-1})
```
It returns the arrays and the left and right reflector data, with $Q$ =
`GolubVanLoan.Chapter05.householderProduct dQ` and $Z$ =
`GolubVanLoan.Chapter05.householderProduct dZ`. If $p < r < n$ fails, it returns $(A, B)$ with
empty data.

The source's algorithm is the case $p = 0$, $r = n - 1$; Algorithm 7.7.3 runs the program on its
unreduced block $A_{22}$. Since the reflectors act on the whole arrays, the program on a block
performs the source's update $A = \operatorname{diag}(I_p, Q, I_q)^T A \operatorname{diag}(I_p,
Z, I_q)$ of Algorithm 7.7.3. The program has no hypotheses; the exact semantics are
`GolubVanLoan.Chapter07.algorithm_7_7_2_block`, `GolubVanLoan.Chapter07.algorithm_7_7_2_spec`
and `GolubVanLoan.Chapter07.algorithm_7_7_2_window`.

**Reading.** The source applies the step to a full unreduced pencil. Lean applies the same
reflectors on a window and returns the reflector lists; it returns the input with empty lists
when the window has fewer than two valid indices. -/
noncomputable def algorithm_7_7_2 (p r : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ) ×
      List ((Fin n → ℝ) × ℝ)) :=
  if hr : p < r ∧ r < n then do
    let v ← qzShiftVector rnd p r A B
    let st ← (List.finRange n).foldlM (fun st (j : Fin n) =>
      if h : p ≤ (j : ℕ) ∧ (j : ℕ) + 2 ≤ r then
        qzStep rnd r j ⟨(j : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 2, by omega⟩ st
      else pure st) (⟨A, B, [], [], v.1, v.2.1, v.2.2⟩ : QZStepState n)
    let r₁ : Fin n := ⟨r - 1, by omega⟩
    let r' : Fin n := ⟨r, hr.2⟩
    let q ← houseOn rnd [r₁, r'] (fun i => if i = r₁ then st.x else if i = r' then st.y else 0)
    let A ← householderApplyLeft rnd q.1 q.2 [r₁, r'] (List.finRange n) st.A
    let B ← householderApplyLeft rnd q.1 q.2 [r₁, r'] (List.finRange n) st.B
    let z ← houseOn rnd [r', r₁] (B r')
    let A ← householderApplyRight rnd z.1 z.2 (List.finRange n) [r', r₁] A
    let B ← householderApplyRight rnd z.1 z.2 (List.finRange n) [r', r₁] B
    pure (A, B, st.dQ ++ [q], st.dZ ++ [z])
  else pure (A, B, [], [])

end Programs

section ZeroChase

open GolubVanLoan.Chapter05

variable {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ}

/-- At indices `i j : Fin n`, `GolubVanLoan.Chapter07.qzEntry A i j` is the entry `A i j`. -/
theorem qzEntry_fin (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : qzEntry A i j = A i j := by
  simp [qzEntry]

/-- At natural indices $i, j < n$, `GolubVanLoan.Chapter07.qzEntry A i j` is the entry $a_{ij}$. -/
theorem qzEntry_of_lt (A : Matrix (Fin n) (Fin n) ℝ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    qzEntry A i j = A ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [qzEntry, hi, hj]

/-- At natural indices with $i \ge n$ or $j \ge n$, `GolubVanLoan.Chapter07.qzEntry A i j` is $0$.
-/
theorem qzEntry_of_not_lt (A : Matrix (Fin n) (Fin n) ℝ) {i j : ℕ} (h : ¬ (i < n ∧ j < n)) :
    qzEntry A i j = 0 := by
  simp only [qzEntry]
  split_ifs
  rfl

/-- The exact run of a column rotation of the zero chase. For $l \neq m$ there are $c, s$ with
$c^2 + s^2 = 1$ and $c\,a_{tl} - s\,a_{tm} = 0$ such that the step replaces $(A, B, Q, Z)$ by
$(AG, BG, Q, ZG)$, where $G = G(l, m, \theta)$ is
`GolubVanLoan.Chapter05.givensRotation l m c s`. -/
theorem qzColumnZero_run {l m : Fin n} (hlm : l ≠ m) (t : Fin n) (st : QZArrays n) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ s * -st.A t m + c * st.A t l = 0 ∧
      Id.run (qzColumnZero pure l m t st) = ⟨st.A * givensRotation l m c s,
        st.B * givensRotation l m c s, st.Q, st.Z * givensRotation l m c s⟩ := by
  obtain ⟨c, s, hg, hcs, hz⟩ := givens_exact (-st.A t m) (st.A t l)
  refine ⟨c, s, hcs, hz, ?_⟩
  simp only [qzColumnZero, Id.run_bind, Id.run_pure]
  rw [hg]
  simp only [givensApplyRight_spec_of_forall_mem hlm _ _ (List.nodup_finRange n)
    List.mem_finRange]

/-- One step $j$ of the zero chase, in exact arithmetic. Let $p \le j$ and let the state satisfy the
invariant `GolubVanLoan.Chapter07.QZArrays.IsEquiv`, with $A$ upper Hessenberg, $B$ upper
triangular, $b_{jj} = 0$, and $a_{p,p-1} = 0$ if $p > 0$. Then after the step the invariant
holds, $A$ is upper Hessenberg, $B$ is upper triangular, $b_{j+1,j+1} = 0$, $a_{p,p-1} = 0$
still holds if $p > 0$, and the entries $a_{rc}$ with $r > j + 1$ and $c \ge j + 1$ are
unchanged. -/
theorem qzZeroChaseStep_spec {p : ℕ} {j j₁ : Fin n} (hj : (j₁ : ℕ) = j + 1) (hpj : p ≤ j)
    {st : QZArrays n} (h : st.IsEquiv A₀ B₀) (hA : st.A.IsUpperHessenberg)
    (hB : st.B.IsUpperTriangular) (hBj : st.B j j = 0)
    (hp : 0 < p → qzEntry st.A p (p - 1) = 0) :
    (Id.run (qzZeroChaseStep pure p j j₁ st)).IsEquiv A₀ B₀ ∧
      (Id.run (qzZeroChaseStep pure p j j₁ st)).A.IsUpperHessenberg ∧
      (Id.run (qzZeroChaseStep pure p j j₁ st)).B.IsUpperTriangular ∧
      (Id.run (qzZeroChaseStep pure p j j₁ st)).B j₁ j₁ = 0 ∧
      (0 < p → qzEntry (Id.run (qzZeroChaseStep pure p j j₁ st)).A p (p - 1) = 0) ∧
      (∀ r c : Fin n, (j₁ : ℕ) < r → (j₁ : ℕ) ≤ c →
        (Id.run (qzZeroChaseStep pure p j j₁ st)).A r c = st.A r c) := by
  rw [isUpperHessenberg_iff_fin] at hA ⊢
  rw [isUpperTriangular_iff_fin] at hB ⊢
  have hjj : j ≠ j₁ := fun e => by rw [e] at hj; omega
  obtain ⟨c, s, hg, hcs, hz⟩ := givens_exact (st.B j j₁) (st.B j₁ j₁)
  set G := givensRotation j j₁ c s with hG
  set A₁ := Gᵀ * st.A with hA₁
  set B₁ := Gᵀ * st.B with hB₁
  have hA₁e : ∀ r q, A₁ r q = if r = j then c * st.A j q - s * st.A j₁ q
      else if r = j₁ then s * st.A j q + c * st.A j₁ q else st.A r q := fun r q =>
    givensRotation_transpose_mul_apply hjj c s st.A r q
  have hB₁e : ∀ r q, B₁ r q = if r = j then c * st.B j q - s * st.B j₁ q
      else if r = j₁ then s * st.B j q + c * st.B j₁ q else st.B r q := fun r q =>
    givensRotation_transpose_mul_apply hjj c s st.B r q
  have hst₁ : (⟨A₁, B₁, st.Q * G, st.Z⟩ : QZArrays n).IsEquiv A₀ B₀ := h.rot_left hjj hcs
  have hBjl : ∀ q : Fin n, (q : ℕ) ≤ j → st.B j q = 0 := fun q hq => by
    rcases Nat.lt_or_ge (q : ℕ) j with h1 | h1
    · exact hB j q h1
    · have : q = j := Fin.ext (by omega)
      rw [this, hBj]
  have hB₁t : ∀ r q : Fin n, (q : ℕ) < r → B₁ r q = 0 := by
    intro r q hqr
    rw [hB₁e]
    split_ifs with h1 h2
    · subst h1
      rw [hB r q hqr, hB j₁ q (by omega)]; ring
    · subst h2
      rw [hBjl q (by omega), hB r q hqr]; ring
    · exact hB r q hqr
  have hB₁jj : B₁ j j = 0 := by
    rw [hB₁e]; simp only [↓reduceIte]; rw [hBj, hB j₁ j (by omega)]; ring
  have hB₁j₁ : B₁ j₁ j₁ = 0 := by
    rw [hB₁e]; simp only [hjj.symm, ↓reduceIte]; linear_combination hz
  have hB₁jl : ∀ q : Fin n, (q : ℕ) ≤ j → B₁ j q = 0 := fun q hq => by
    rcases Nat.lt_or_ge (q : ℕ) j with h1 | h1
    · exact hB₁t j q h1
    · have : q = j := Fin.ext (by omega)
      rw [this, hB₁jj]
  have hA₁h : ∀ r q : Fin n, (q : ℕ) + 1 < r → ¬ ((r : ℕ) = j₁ ∧ (q : ℕ) + 1 = j) →
      A₁ r q = 0 := by
    intro r q hqr hne
    rw [hA₁e]
    split_ifs with h1 h2
    · subst h1
      rw [hA r q hqr, hA j₁ q (by omega)]; ring
    · subst h2
      rw [hA j q (by omega), hA r q hqr]; ring
    · exact hA r q hqr
  have hA₁out : ∀ r q : Fin n, r ≠ j → r ≠ j₁ → A₁ r q = st.A r q := fun r q h1 h2 => by
    rw [hA₁e]; simp [h1, h2]
  by_cases hpj' : p < (j : ℕ)
  · set l : Fin n := ⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ with hl
    have hlv : (l : ℕ) = j - 1 := rfl
    have hlj : l ≠ j := fun e => by have := congrArg Fin.val e; simp [l] at this; omega
    obtain ⟨c', s', hcs', hz', hcz⟩ :=
      qzColumnZero_run hlj j₁ (⟨A₁, B₁, st.Q * G, st.Z⟩ : QZArrays n)
    have hrun : Id.run (qzZeroChaseStep pure p j j₁ st) =
        ⟨A₁ * givensRotation l j c' s', B₁ * givensRotation l j c' s', st.Q * G,
          st.Z * givensRotation l j c' s'⟩ := by
      simp only [qzZeroChaseStep, Id.run_bind]
      rw [hg]
      simp only [givensApplyLeft_spec_of_forall_mem hjj _ _ (List.nodup_finRange n)
        List.mem_finRange, givensApplyRight_spec_of_forall_mem hjj _ _ (List.nodup_finRange n)
        List.mem_finRange, hpj', ↓reduceIte]
      exact hcz
    rw [hrun]
    have hH : ∀ (Y : Matrix (Fin n) (Fin n) ℝ) r q, (Y * givensRotation l j c' s') r q =
        if q = l then c' * Y r l - s' * Y r j else if q = j then s' * Y r l + c' * Y r j
          else Y r q := fun Y r q => mul_givensRotation_apply hlj c' s' Y r q
    refine ⟨hst₁.rot_right hlj hcs', ?_, ?_, ?_, ?_, ?_⟩
    · intro r q hqr
      change (A₁ * givensRotation l j c' s') r q = 0
      rw [hH]
      split_ifs with h1 h2
      · subst h1
        by_cases hr : r = j₁
        · subst hr
          linear_combination hz'
        · rw [hA₁h r l hqr (fun ⟨e, _⟩ => hr (Fin.ext e)),
            hA₁h r j (by omega) (fun ⟨_, e⟩ => by omega)]
          ring
      · subst h2
        rw [hA₁h r l (by omega) (fun ⟨_, e⟩ => by omega), hA₁h r q hqr (fun ⟨_, e⟩ => by omega)]
        ring
      · exact hA₁h r q hqr (fun ⟨_, e⟩ => h1 (Fin.ext (by omega)))
    · intro r q hqr
      change (B₁ * givensRotation l j c' s') r q = 0
      rw [hH]
      split_ifs with h1 h2
      · subst h1
        rcases Nat.lt_or_ge (j : ℕ) r with h3 | h3
        · rw [hB₁t r l (by omega), hB₁t r j h3]; ring
        · have : r = j := Fin.ext (by omega)
          rw [this, hB₁jl l (by omega), hB₁jj]; ring
      · subst h2
        rw [hB₁t r l (by omega), hB₁t r q hqr]; ring
      · exact hB₁t r q hqr
    · change (B₁ * givensRotation l j c' s') j₁ j₁ = 0
      rw [hH]
      have h1 : j₁ ≠ l := fun e => by rw [e] at hj; omega
      simp only [h1, hjj.symm, ↓reduceIte]
      exact hB₁j₁
    · intro hp0
      have hpn : p < n := by omega
      rw [qzEntry_of_lt _ hpn (by omega)]
      change (A₁ * givensRotation l j c' s') _ _ = 0
      rw [hH]
      have h1 : (⟨p - 1, by omega⟩ : Fin n) ≠ l := fun e => by
        have := congrArg Fin.val e; simp [l] at this; omega
      have h2 : (⟨p - 1, by omega⟩ : Fin n) ≠ j := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp only [h1, h2, ↓reduceIte]
      have h3 : (⟨p, hpn⟩ : Fin n) ≠ j := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      have h4 : (⟨p, hpn⟩ : Fin n) ≠ j₁ := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      rw [hA₁out _ _ h3 h4, ← qzEntry_of_lt st.A hpn (by omega)]
      exact hp hp0
    · intro r q hr hq
      change (A₁ * givensRotation l j c' s') r q = st.A r q
      have h1 : q ≠ l := fun e => by rw [e] at hq; omega
      have h2 : q ≠ j := fun e => by rw [e] at hq; omega
      have h3 : r ≠ j := fun e => by rw [e] at hr; omega
      have h4 : r ≠ j₁ := fun e => by rw [e] at hr; omega
      rw [hH]
      simp only [h1, h2, ↓reduceIte]
      exact hA₁out r q h3 h4
  · have hpj'' : (j : ℕ) = p := by omega
    have hrun : Id.run (qzZeroChaseStep pure p j j₁ st) = ⟨A₁, B₁, st.Q * G, st.Z⟩ := by
      simp only [qzZeroChaseStep, Id.run_bind]
      rw [hg]
      simp only [givensApplyLeft_spec_of_forall_mem hjj _ _ (List.nodup_finRange n)
        List.mem_finRange, givensApplyRight_spec_of_forall_mem hjj _ _ (List.nodup_finRange n)
        List.mem_finRange, hpj', ↓reduceIte, Id.run_pure]
      rfl
    rw [hrun]
    -- the entry `A(p, p - 1)` vanishes, so does the only candidate fill-in `(j₁, j - 1)`
    have hbd : ∀ q : Fin n, (q : ℕ) + 1 = j → st.A j q = 0 := fun q hq => by
      have := hp (by omega)
      rw [qzEntry_of_lt _ (by omega) (by omega)] at this
      rw [← this]
      congr 1 <;> ext <;> simp <;> omega
    refine ⟨hst₁, ?_, hB₁t, hB₁j₁, ?_, ?_⟩
    · intro r q hqr
      by_cases hbad : (r : ℕ) = j₁ ∧ (q : ℕ) + 1 = j
      · obtain ⟨e1, e2⟩ := hbad
        have hr : r = j₁ := Fin.ext e1
        change A₁ r q = 0
        rw [hr, hA₁e]
        simp only [hjj.symm, ↓reduceIte]
        rw [hbd q e2, hA j₁ q (by omega)]
        ring
      · exact hA₁h r q hqr hbad
    · intro hp0
      rw [qzEntry_of_lt _ (by omega) (by omega)]
      change A₁ _ _ = 0
      have h3 : (⟨p, by omega⟩ : Fin n) = j := Fin.ext hpj''.symm
      rw [hA₁e]
      simp only [h3, ↓reduceIte]
      rw [hbd _ (by simp; omega), hA j₁ _ (by simp; omega)]
      ring
    · intro r q hr _
      exact hA₁out r q (fun e => by rw [e] at hr; omega) (fun e => by rw [e] at hr; omega)

end ZeroChase

section ZeroChaseSpec

open GolubVanLoan.Chapter05

variable {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ}

/-- **§7.7.5** of [golub2013matrix], the exact semantics of the zero chase: "This zero-chasing
technique is perfectly general and can be used to zero $a_{n,n-1}$ regardless of where the zero
appears along $B$'s diagonal". Let $p \le k \le r < n$. Let the state satisfy the invariant
`GolubVanLoan.Chapter07.QZArrays.IsEquiv` for $(A_0, B_0)$, with $A$ upper Hessenberg and $B$
upper triangular, let $b_{kk} = 0$, and let the block $p, \dots, r$ be decoupled from the rest:
$a_{p,p-1} = 0$ if $p > 0$, and $a_{r+1,r} = 0$ if $r + 1 < n$. Then after the zero chase (in
exact arithmetic) the invariant holds, $A$ is upper Hessenberg, $B$ is upper triangular,
$b_{rr} = 0$, $a_{r,r-1} = 0$ if $p < r$, and the block is still decoupled.

With $p = 0$, $r = n - 1$ and $Q = Z = I$ at the start this is the source's display: the output
is $(Q^T A Z, Q^T B Z)$ with $(Q^T A Z)_{n,n-1} = 0$ and $(Q^T B Z)_{nn} = 0$. The entries at
natural indices are read with `GolubVanLoan.Chapter07.qzEntry`, which is $0$ out of range.

**Generalization.** The source presents deflation at the last position of the whole pencil.
This theorem also applies to a decoupled active window and explicitly certifies the
corresponding boundary and terminal zeros. -/
theorem qzZeroChase_spec {p k r : ℕ} (hpk : p ≤ k) (hkr : k ≤ r) (hr : r < n)
    {st : QZArrays n} (h : st.IsEquiv A₀ B₀) (hA : st.A.IsUpperHessenberg)
    (hB : st.B.IsUpperTriangular) (hk : qzEntry st.B k k = 0)
    (hp : 0 < p → qzEntry st.A p (p - 1) = 0) (hr₁ : qzEntry st.A (r + 1) r = 0) :
    (Id.run (qzZeroChase pure p k r st)).IsEquiv A₀ B₀ ∧
      (Id.run (qzZeroChase pure p k r st)).A.IsUpperHessenberg ∧
      (Id.run (qzZeroChase pure p k r st)).B.IsUpperTriangular ∧
      qzEntry (Id.run (qzZeroChase pure p k r st)).B r r = 0 ∧
      (p < r → qzEntry (Id.run (qzZeroChase pure p k r st)).A r (r - 1) = 0) ∧
      (0 < p → qzEntry (Id.run (qzZeroChase pure p k r st)).A p (p - 1) = 0) ∧
      qzEntry (Id.run (qzZeroChase pure p k r st)).A (r + 1) r = 0 := by
  set f := fun (st : QZArrays n) (j : Fin n) => Id.run
    (if h : k ≤ (j : ℕ) ∧ (j : ℕ) < r ∧ r < n then
      qzZeroChaseStep pure p j ⟨(j : ℕ) + 1, by omega⟩ st
    else pure st) with hf
  have key := foldl_induction_getElem (List.finRange n) f
    (fun q st => st.IsEquiv A₀ B₀ ∧ st.A.IsUpperHessenberg ∧ st.B.IsUpperTriangular ∧
      qzEntry st.B (max k (min q r)) (max k (min q r)) = 0 ∧
      (0 < p → qzEntry st.A p (p - 1) = 0) ∧ qzEntry st.A (r + 1) r = 0) st
    ⟨h, hA, hB, by rwa [show max k (min 0 r) = k by omega], hp, hr₁⟩ (by
      intro q hq s ⟨hs, hsA, hsB, hsz, hsp, hsr⟩
      have hq' : q < n := by simpa using hq
      have hv : ((List.finRange n)[q] : ℕ) = q := by simp
      by_cases hg : k ≤ q ∧ q < r
      · have hg' : k ≤ ((List.finRange n)[q] : ℕ) ∧ ((List.finRange n)[q] : ℕ) < r ∧ r < n := by
          rw [hv]; exact ⟨hg.1, hg.2, hr⟩
        have hfq : f s (List.finRange n)[q] = Id.run (qzZeroChaseStep pure p
            (List.finRange n)[q] ⟨((List.finRange n)[q] : ℕ) + 1, by omega⟩ s) := by
          simp only [hf, hg', and_self, ↓reduceDIte]
        rw [hfq]
        have hz : max k (min q r) = q := by omega
        rw [hz, qzEntry_of_lt _ hq' hq'] at hsz
        have hBj : s.B (List.finRange n)[q] (List.finRange n)[q] = 0 := by
          rw [← hsz]; congr 1 <;> ext <;> simp
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := qzZeroChaseStep_spec (j := (List.finRange n)[q])
          (j₁ := ⟨((List.finRange n)[q] : ℕ) + 1, by omega⟩) rfl (by rw [hv]; omega) hs hsA hsB
          hBj hsp
        refine ⟨h1, h2, h3, ?_, h5, ?_⟩
        · rw [show max k (min (q + 1) r) = q + 1 by omega, qzEntry_of_lt _ (by omega) (by omega)]
          rw [← h4]; congr 1 <;> ext <;> simp
        · by_cases hr1 : r + 1 < n
          · rw [qzEntry_of_lt _ hr1 hr, h6 _ _ (by simp; omega) (by simp; omega),
              ← qzEntry_of_lt s.A hr1 hr]
            exact hsr
          · exact qzEntry_of_not_lt _ (by omega)
      · have hg' : ¬ (k ≤ ((List.finRange n)[q] : ℕ) ∧ ((List.finRange n)[q] : ℕ) < r ∧ r < n) := by
          rw [hv]; exact fun h => hg ⟨h.1, h.2.1⟩
        have hfq : f s (List.finRange n)[q] = s := by
          simp only [hf, hg', ↓reduceDIte, Id.run_pure]
        rw [hfq]
        refine ⟨hs, hsA, hsB, ?_, hsp, hsr⟩
        rwa [show max k (min (q + 1) r) = max k (min q r) by omega])
  have hrun : Id.run (qzZeroChase pure p k r st) = Id.run
      (if h : p < r ∧ r < n then
        qzColumnZero pure ⟨r - 1, by omega⟩ ⟨r, h.2⟩ ⟨r, h.2⟩ ((List.finRange n).foldl f st)
      else pure ((List.finRange n).foldl f st)) := by
    simp only [qzZeroChase, Id.run_bind, hf, List.idRun_foldlM]
  rw [hrun]
  simp only [List.length_finRange] at key
  obtain ⟨hs, hsA, hsB, hsz, hsp, hsr⟩ := key
  rw [show max k (min n r) = r by omega] at hsz
  set s := (List.finRange n).foldl f st with hs_def
  by_cases hpr : p < r
  · have hc : p < r ∧ r < n := ⟨hpr, hr⟩
    simp only [hc, and_self, ↓reduceDIte]
    set l : Fin n := ⟨r - 1, by omega⟩ with hl
    set m : Fin n := ⟨r, hr⟩ with hm
    have hlm : l ≠ m := fun e => by have := congrArg Fin.val e; simp [l, m] at this; omega
    obtain ⟨c, s', hcs, hz, hcz⟩ := qzColumnZero_run hlm m s
    rw [hcz]
    rw [isUpperHessenberg_iff_fin] at hsA ⊢
    rw [isUpperTriangular_iff_fin] at hsB ⊢
    have hH : ∀ (Y : Matrix (Fin n) (Fin n) ℝ) x y, (Y * givensRotation l m c s') x y =
        if y = l then c * Y x l - s' * Y x m else if y = m then s' * Y x l + c * Y x m
          else Y x y := fun Y x y => mul_givensRotation_apply hlm c s' Y x y
    have hBrr : s.B m m = 0 := by
      have := hsz; rwa [qzEntry_of_lt s.B hr hr] at this
    have hAr1 : ∀ h : r + 1 < n, s.A ⟨r + 1, h⟩ m = 0 := fun h1 => by
      have := hsr; rwa [qzEntry_of_lt s.A h1 hr] at this
    have hml : m ≠ l := hlm.symm
    have e1 : (⟨r - 1, (by omega : r - 1 < n)⟩ : Fin n) = l := rfl
    have e2 : (⟨r, hr⟩ : Fin n) = m := rfl
    refine ⟨hs.rot_right hlm hcs, ?_, ?_, ?_, fun _ => ?_, fun hp0 => ?_, ?_⟩
    · intro x y hxy
      simp only
      rw [hH]
      split_ifs with h1 h2
      · subst h1
        rw [hsA x l hxy]
        by_cases hx : (x : ℕ) = r + 1
        · have : x = ⟨r + 1, by omega⟩ := Fin.ext hx
          rw [this, hAr1]; ring
        · rw [hsA x m (by simp [m]; simp [l] at hxy; omega)]; ring
      · subst h2
        rw [hsA x l (by simp [l]; simp [m] at hxy; omega), hsA x m hxy]; ring
      · exact hsA x y hxy
    · intro x y hxy
      simp only
      rw [hH]
      split_ifs with h1 h2
      · subst h1
        rw [hsB x l hxy]
        by_cases hx : (x : ℕ) = r
        · have : x = m := Fin.ext hx
          rw [this, hBrr]; ring
        · rw [hsB x m (by simp [m]; simp [l] at hxy; omega)]; ring
      · subst h2
        rw [hsB x l (by simp [l]; simp [m] at hxy; omega), hsB x m hxy]; ring
      · exact hsB x y hxy
    · change qzEntry (s.B * givensRotation l m c s') r r = 0
      rw [qzEntry_of_lt (s.B * givensRotation l m c s') hr hr, hH, e2]
      simp only [hml, ↓reduceIte]
      rw [hsB m l (by simp [l, m]; omega), hBrr]
      ring
    · change qzEntry (s.A * givensRotation l m c s') r (r - 1) = 0
      rw [qzEntry_of_lt (s.A * givensRotation l m c s') hr (by omega), hH, e1, e2]
      simp only [↓reduceIte]
      linear_combination hz
    · change qzEntry (s.A * givensRotation l m c s') p (p - 1) = 0
      rw [qzEntry_of_lt (s.A * givensRotation l m c s') (by omega) (by omega), hH]
      have h1 : (⟨p - 1, by omega⟩ : Fin n) ≠ l := fun e => by
        have := congrArg Fin.val e; simp [l] at this; omega
      have h2 : (⟨p - 1, by omega⟩ : Fin n) ≠ m := fun e => by
        have := congrArg Fin.val e; simp [m] at this; omega
      simp only [h1, h2, ↓reduceIte]
      rw [← qzEntry_of_lt s.A (by omega) (by omega)]
      exact hsp hp0
    · by_cases hr1 : r + 1 < n
      · change qzEntry (s.A * givensRotation l m c s') (r + 1) r = 0
        rw [qzEntry_of_lt (s.A * givensRotation l m c s') hr1 hr, hH, e2]
        simp only [hml, ↓reduceIte]
        rw [hsA _ l (by simp [l]; omega), hAr1 hr1]
        ring
      · exact qzEntry_of_not_lt _ (by omega)
  · have hc : ¬ (p < r ∧ r < n) := fun h => hpr h.1
    simp only [hc, ↓reduceDIte, Id.run_pure]
    exact ⟨hs, hsA, hsB, hsz, fun h => absurd h hpr, hsp, hsr⟩

end ZeroChaseSpec

/-! ### §7.7.7 The overall QZ process -/

/-- The trailing block of an upper Hessenberg array from the index $s$ on is decoupled and upper
quasi-triangular: $s = 0$ or $a_{s,s-1} = 0$, and for every $i$ with $s < i$ and $i + 1 < n$,
$a_{i,i-1} = 0$ or $a_{i+1,i} = 0$. Entries out of range count as $0$. -/
def qzTrailingQuasi (A : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) : Prop :=
  (s = 0 ∨ qzEntry A s (s - 1) = 0) ∧
    ∀ i < n, s < i → i + 1 < n → qzEntry A i (i - 1) = 0 ∨ qzEntry A (i + 1) i = 0

/-- The subdiagonal entries $a_{i,i-1}$ with $r - d < i \le r$ are nonzero, so that the block ending
at $r$ is unreduced. Here $r - d$ is truncated subtraction. -/
def qzUnreducedTail (A : Matrix (Fin n) (Fin n) ℝ) (r d : ℕ) : Prop :=
  ∀ i ≤ r, r - d < i → qzEntry A i (i - 1) ≠ 0

section Programs

open GolubVanLoan.Chapter05

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The deflation sweep of Algorithm 7.7.3 of [golub2013matrix]: "Set to zero subdiagonal entries
that satisfy $|a_{i,i-1}| \le \varepsilon(|a_{i-1,i-1}| + |a_{ii}|)$", for $i = 1, \dots, n-1$
in order. The right side is rounded, $\mathrm{fl}(\varepsilon \cdot \mathrm{fl}(|a_{i-1,i-1}| +
|a_{ii}|))$; the absolute values and the comparison are exact.
-/
noncomputable def qzDeflate (ε : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun A (i : Fin n) =>
    if h : 0 < (i : ℕ) then do
      let i₀ : Fin n := ⟨(i : ℕ) - 1, by omega⟩
      let t ← rnd (ε * (← rnd (|A i₀ i₀| + |A i i|)))
      if |A i i₀| ≤ t then pure (of fun a b => if a = i ∧ b = i₀ then 0 else A a b)
      else pure A
    else pure A) A

open Classical in
/-- One pass of the `until q = n` loop of Algorithm 7.7.3 of [golub2013matrix]. A finished state is
kept. Otherwise the pass deflates $A$ and then, in the words of the source, it finds "the
largest nonnegative $q$ and the smallest nonnegative $p$ such that" $$A = \begin{bmatrix} A_{11}
& A_{12} & A_{13} \\ 0 & A_{22} & A_{23} \\ 0 & 0 & A_{33} \end{bmatrix}$$ with blocks of sizes
$p$, $n - p - q$ and $q$, where "$A_{33}$ is upper quasi-triangular and $A_{22}$ is upper
Hessenberg and unreduced". If $q = n$, the state is finished. Otherwise, on the block
$p, \dots, r$ with $r = n - q - 1$: "if $B_{22}$ is singular, zero $a_{n-q,n-q-1}$", by the zero
chase from the last zero on the diagonal of $B$ in the block; "else apply Algorithm 7.7.2 to
$A_{22}$ and $B_{22}$ and update", by accumulating the reflector data into $Q$ and $Z$.

The integers $q$ and $p$ are found by `Nat.findGreatest` over
`GolubVanLoan.Chapter07.qzTrailingQuasi` and `GolubVanLoan.Chapter07.qzUnreducedTail`. The
singularity test of $B_{22}$ compares its diagonal entries with $0$ exactly. The reflector data
are accumulated by `GolubVanLoan.Chapter05.householderApplyRight` on the columns of the block.

**Reading.** The source instructs a zero chase when the active triangular block is singular.
Lean compares its diagonal against zero exactly, chooses the last zero, and accumulates both
transformations in either branch. -/
noncomputable def qzPass (ε : ℝ) (st : QZArrays n × Bool) : M (QZArrays n × Bool) :=
  if st.2 then pure st else do
    let A ← qzDeflate rnd ε st.1.A
    let q := Nat.findGreatest (fun q => qzTrailingQuasi A (n - q)) n
    if q = n then pure (⟨A, st.1.B, st.1.Q, st.1.Z⟩, true) else do
      let r := n - q - 1
      let p := r - Nat.findGreatest (fun d => qzUnreducedTail A r d) r
      let blk := (List.finRange n).filter fun (i : Fin n) => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ r
      match (blk.filter fun i => st.1.B i i = 0).getLast? with
      | some k => do
        let st' ← qzZeroChase rnd p k r ⟨A, st.1.B, st.1.Q, st.1.Z⟩
        pure (st', false)
      | none => do
        let out ← algorithm_7_7_2 rnd p r A st.1.B
        let Q ← out.2.2.1.foldlM (fun Q d =>
          householderApplyRight rnd d.1 d.2 (List.finRange n) blk Q) st.1.Q
        let Z ← out.2.2.2.foldlM (fun Z d =>
          householderApplyRight rnd d.1 d.2 (List.finRange n) blk Z) st.1.Z
        pure (⟨out.1, out.2.1, Q, Z⟩, false)

/-- **Algorithm 7.7.3** of [golub2013matrix] (the QZ algorithm, Moler and Stewart). "Given
$A \in \mathbb{R}^{n \times n}$ and $B \in \mathbb{R}^{n \times n}$, the following algorithm
computes orthogonal $Q$ and $Z$ such that $Q^T A Z = T$ is upper quasi-triangular and
$Q^T B Z = S$ is upper triangular. $A$ is overwritten by $T$ and $B$ by $S$":
```
Using Algorithm 7.7.1, overwrite A with QᵀAZ (upper Hessenberg)
    and B with QᵀBZ (upper triangular).
until q = n
    (one qzPass)
end
```
The `until` loop runs at most `fuel` passes. The result is $(T, S, Q, Z)$ together with the flag
`done`, which says that $q = n$ was reached. The exact semantics is
`GolubVanLoan.Chapter07.algorithm_7_7_3_spec`.

**Reading.** The source loops until the whole active pencil is in generalized Schur form and
discusses the cost of optional factor accumulation. Lean always accumulates both factors and
returns its state with a stop flag after at most the supplied number of passes. -/
noncomputable def algorithm_7_7_3 (ε : ℝ) (A B : Matrix (Fin n) (Fin n) ℝ) (fuel : ℕ) :
    M (QZArrays n × Bool) := do
  let st ← algorithm_7_7_1 rnd A B
  (List.range fuel).foldlM (fun st _ => qzPass rnd ε st) (st, false)

end Programs

/-! ### §7.7.8 Generalized inverse iteration and deflating subspaces -/

/-- **§7.7.8** of [golub2013matrix], generalized inverse iteration. Let
$A, B \in \mathbb{C}^{n \times n}$ with $B$ nonsingular, and $\mu \in \mathbb{C}$. Then $$(A -
\mu B)^{-1} B = (B^{-1} A - \mu I)^{-1}.$$ So the iteration $(A - \mu B) z^{(k)} = B q^{(k-1)}$
is inverse iteration (7.6.1) for $B^{-1} A$ with the same shift.

**Typo.** The source prints the eigenvalue estimate as $\lambda^{(k)} = q^{(k)H} A q^{(k)} /
q^{(k)H} A q^{(k)}$; the denominator is $q^{(k)H} B q^{(k)}$.

With Lean's convention that a singular matrix has inverse $0$, the identity holds for every
$\mu$: when $A - \mu B$ is singular, both sides are $0$.

**Reading.** The source discusses an iteration with vector normalization and an eigenvalue
estimate. This theorem establishes the inverse-matrix identity only, and uses totalized
inversion also at singular shifts. -/
theorem generalizedInverseIteration_eq {A B : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B) (μ : ℂ) :
    (A - μ • B)⁻¹ * B = (B⁻¹ * A - μ • 1)⁻¹ := by
  have hBd : IsUnit B.det := (isUnit_iff_isUnit_det B).1 hB
  have hfac : A - μ • B = B * (B⁻¹ * A - μ • 1) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, mul_nonsing_inv _ hBd, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one]
  rw [hfac, Matrix.mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ hBd, Matrix.mul_one]

/-- **§7.7.8** of [golub2013matrix], deflating subspaces from the generalized Schur form. Let
$A, B, Q, Z \in \mathbb{C}^{n \times n}$ with $Q$ and $Z$ unitary, and let $Q^H A Z$ and
$Q^H B Z$ be upper triangular. Let $q_j$ and $z_j$ be the columns of $Q$ and $Z$. Then for every
$k$, $$\operatorname{span}\{A z_1, \dots, A z_k\} \subseteq \operatorname{span}\{q_1, \dots,
q_k\}, \qquad \operatorname{span}\{B z_1, \dots, B z_k\} \subseteq \operatorname{span}\{q_1,
\dots, q_k\},$$ and $\operatorname{span}\{z_1, \dots, z_k\}$ is a deflating subspace of
$A - \lambda B$.

A subspace $S$ is deflating (`Matrix.IsDeflatingSubspace`) if $\{Ax + By : x, y \in S\}$ has
dimension at most $\dim S$. The index `k : Fin n` is 0-based, so the spans are over the columns
$0, \dots, k$. -/
theorem deflatingSubspace_of_generalizedSchur {A B Q Z : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (hZ : Z ∈ unitaryGroup (Fin n) ℂ)
    (hT : (star Q * A * Z).IsUpperTriangular) (hS : (star Q * B * Z).IsUpperTriangular)
    (k : Fin n) :
    (Submodule.span ℂ (Set.range fun j : Set.Iic k => A *ᵥ Z.col j) ≤
        Submodule.span ℂ (Set.range fun j : Set.Iic k => Q.col j)) ∧
      (Submodule.span ℂ (Set.range fun j : Set.Iic k => B *ᵥ Z.col j) ≤
        Submodule.span ℂ (Set.range fun j : Set.Iic k => Q.col j)) ∧
      IsDeflatingSubspace A B (Submodule.span ℂ (Set.range fun j : Set.Iic k => Z.col j)) := by
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hZZ : Z * star Z = 1 := mem_unitaryGroup_iff.1 hZ
  have hQu : IsUnit Q := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hQQ)
  have hZu : IsUnit Z := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hZZ)
  have hinv : Q⁻¹ = star Q := Matrix.inv_eq_right_inv hQQ
  exact isDeflatingSubspace_span_cols_of_isUpperTriangular hQu hZu (by rwa [hinv])
    (by rwa [hinv]) k

/-! ### §7.7.9 The polynomial eigenvalue problem -/

/-- **Equation (7.7.5)** of [golub2013matrix], the companion pencil of a cubic $P(\lambda) = A_0 +
\lambda A_1 + \lambda^2 A_2 + \lambda^3 A_3$ with $A_i \in \mathbb{C}^{n \times n}$:
$$L(\lambda) = \begin{bmatrix} 0 & 0 & A_0 \\ -I & 0 & A_1 \\ 0 & -I & A_2 \end{bmatrix} +
\lambda \begin{bmatrix} I & 0 & 0 \\ 0 & I & 0 \\ 0 & 0 & A_3 \end{bmatrix}.$$

The three block rows are indexed by `(Fin n ⊕ Fin n) ⊕ Fin n`. -/
def cubicPencil (A₀ A₁ A₂ A₃ : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix ((Fin n ⊕ Fin n) ⊕ Fin n) ((Fin n ⊕ Fin n) ⊕ Fin n) ℂ :=
  fromBlocks (fromBlocks 0 0 (-1) 0) (fromRows A₀ A₁) (fromCols 0 (-1)) A₂ +
    l • fromBlocks 1 0 0 A₃

/-- A function on a sum type is $0$ if and only if both of its restrictions are $0$. -/
private theorem sum_elim_eq_zero_iff {α β : Type*} {a : α → ℂ} {b : β → ℂ} :
    Sum.elim a b = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h => ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩,
    ?_⟩
  rintro ⟨rfl, rfl⟩
  exact Sum.elim_zero_zero

/-- The block rows of $L(\lambda) [u_1; u_2; x]$ for the pencil (7.7.5) are $\lambda u_1 + A_0 x$,
$-u_1 + \lambda u_2 + A_1 x$ and $-u_2 + (A_2 + \lambda A_3) x$. -/
private theorem cubicPencil_mulVec (A₀ A₁ A₂ A₃ : Matrix (Fin n) (Fin n) ℂ) (l : ℂ)
    (u₁ u₂ x : Fin n → ℂ) :
    cubicPencil A₀ A₁ A₂ A₃ l *ᵥ Sum.elim (Sum.elim u₁ u₂) x =
      Sum.elim (Sum.elim (l • u₁ + A₀ *ᵥ x) (-u₁ + l • u₂ + A₁ *ᵥ x))
        (-u₂ + (A₂ + l • A₃) *ᵥ x) := by
  ext ((i | i) | i) <;>
    simp [cubicPencil, add_mulVec, smul_mulVec, fromBlocks_mulVec, fromRows_mulVec,
      fromCols_mulVec, neg_mulVec, one_mulVec] <;> ring

/-- **Equations (7.7.3)–(7.7.5)** of [golub2013matrix]. Let
$A_0, A_1, A_2, A_3 \in \mathbb{C}^{n \times n}$ and $\lambda \in \mathbb{C}$, let $P(\lambda) =
A_0 + \lambda A_1 + \lambda^2 A_2 + \lambda^3 A_3$ be the cubic (7.7.4), and let $L(\lambda)$ be
its companion pencil (7.7.5). The following hold.

1. If $L(\lambda) [u_1; u_2; x] = 0$, then $P(\lambda) x = 0$, the problem (7.7.3).
2. If $P(\lambda) x = 0$, then $L(\lambda) [u_1; u_2; x] = 0$ for $u_2 = (A_2 + \lambda A_3) x$
   and $u_1 = A_1 x + \lambda u_2$.
3. There is $v \neq 0$ with $L(\lambda) v = 0$ if and only if there is $x \neq 0$ with
   $P(\lambda) x = 0$, so $L$ and $P$ have the same eigenvalues.

The block rows give $u_2 = (A_2 + \lambda A_3) x$, $u_1 = A_1 x + \lambda u_2$ and
$\lambda u_1 + A_0 x = P(\lambda) x$. The source's chain writes $A_0 + \dots$ where
$A_0 x + \dots$ is meant.

**Reading.** The source’s calculation eliminates $u_1,u_2$ to derive $P(\lambda)x=0$. Lean also
reconstructs those blocks in the opposite direction and proves equivalence of nonzero kernels. -/
theorem equation_7_7_5 (A₀ A₁ A₂ A₃ : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    (∀ u₁ u₂ x : Fin n → ℂ, cubicPencil A₀ A₁ A₂ A₃ l *ᵥ Sum.elim (Sum.elim u₁ u₂) x = 0 →
      (A₀ + l • A₁ + l ^ 2 • A₂ + l ^ 3 • A₃) *ᵥ x = 0) ∧
    (∀ x : Fin n → ℂ, (A₀ + l • A₁ + l ^ 2 • A₂ + l ^ 3 • A₃) *ᵥ x = 0 →
      cubicPencil A₀ A₁ A₂ A₃ l *ᵥ
        Sum.elim (Sum.elim (A₁ *ᵥ x + l • (A₂ + l • A₃) *ᵥ x) ((A₂ + l • A₃) *ᵥ x)) x = 0) ∧
    ((∃ v ≠ 0, cubicPencil A₀ A₁ A₂ A₃ l *ᵥ v = 0) ↔
      ∃ x ≠ 0, (A₀ + l • A₁ + l ^ 2 • A₂ + l ^ 3 • A₃) *ᵥ x = 0) := by
  have hrows : ∀ u₁ u₂ x : Fin n → ℂ,
      cubicPencil A₀ A₁ A₂ A₃ l *ᵥ Sum.elim (Sum.elim u₁ u₂) x = 0 →
        u₂ = (A₂ + l • A₃) *ᵥ x ∧ u₁ = l • u₂ + A₁ *ᵥ x ∧ A₀ *ᵥ x = -(l • u₁) := by
    intro u₁ u₂ x h
    rw [cubicPencil_mulVec, sum_elim_eq_zero_iff, sum_elim_eq_zero_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨neg_add_eq_zero.1 h3, neg_add_eq_zero.1 (by rw [← add_assoc]; exact h2),
      (neg_eq_of_add_eq_zero_right h1).symm⟩
  have hP : ∀ u₁ u₂ x : Fin n → ℂ,
      cubicPencil A₀ A₁ A₂ A₃ l *ᵥ Sum.elim (Sum.elim u₁ u₂) x = 0 →
        (A₀ + l • A₁ + l ^ 2 • A₂ + l ^ 3 • A₃) *ᵥ x = 0 := by
    intro u₁ u₂ x h
    obtain ⟨e3, e2, e1⟩ := hrows u₁ u₂ x h
    simp only [add_mulVec, smul_mulVec]
    rw [e1, e2, e3]
    simp only [add_mulVec, smul_mulVec]
    module
  have hL : ∀ x : Fin n → ℂ, (A₀ + l • A₁ + l ^ 2 • A₂ + l ^ 3 • A₃) *ᵥ x = 0 →
      cubicPencil A₀ A₁ A₂ A₃ l *ᵥ
        Sum.elim (Sum.elim (A₁ *ᵥ x + l • (A₂ + l • A₃) *ᵥ x) ((A₂ + l • A₃) *ᵥ x)) x = 0 := by
    intro x h
    rw [cubicPencil_mulVec, sum_elim_eq_zero_iff, sum_elim_eq_zero_iff]
    refine ⟨⟨?_, ?_⟩, neg_add_cancel _⟩
    · rw [← h]
      simp only [add_mulVec, smul_mulVec]
      module
    · abel
  refine ⟨hP, hL, ⟨?_, ?_⟩⟩
  · rintro ⟨v, hv, h⟩
    have hv' : v = Sum.elim (Sum.elim (fun i => v (Sum.inl (Sum.inl i)))
        (fun i => v (Sum.inl (Sum.inr i)))) (fun i => v (Sum.inr i)) := by
      ext ((i | i) | i) <;> rfl
    rw [hv'] at h hv
    refine ⟨_, fun hx => hv ?_, hP _ _ _ h⟩
    obtain ⟨e3, e2, -⟩ := hrows _ _ _ h
    rw [hx, mulVec_zero] at e3
    rw [e3, smul_zero, hx, mulVec_zero, add_zero] at e2
    rw [e2, e3, hx, Sum.elim_zero_zero, Sum.elim_zero_zero]
  · rintro ⟨x, hx, h⟩
    exact ⟨_, fun h' => hx (funext fun i => congrFun h' (Sum.inr i)), hL x h⟩

/-! ### §7.7.9 The polynomial eigenvalue problem: the linearization (7.7.6) -/

section Linearization

variable {e : ℕ}

/-- The $\lambda$-matrices of §7.7.9 of [golub2013matrix]. For
$A_0, \dots, A_d \in \mathbb{C}^{n \times n}$, $k \ge 0$ and $\lambda \in \mathbb{C}$,
$$P_k(\lambda) = A_k + \lambda A_{k+1} + \dots + \lambda^{d-k} A_d.$$ Then
$P_0(\lambda) = P(\lambda)$ is (7.7.4), and $P_k(\lambda) = 0$ for $k > d$.

The coefficients are `A : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ`. -/
noncomputable def lambdaTail {d : ℕ} (A : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (l : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j : Fin (d + 1), if k ≤ (j : ℕ) then l ^ ((j : ℕ) - k) • A j else 0

/-- §7.7.9 of [golub2013matrix]: $P_k(\lambda) = A_k + \lambda P_{k+1}(\lambda)$ for $k \le d$. -/
theorem lambdaTail_eq_add {d : ℕ} (A : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) {k : ℕ}
    (hk : k < d + 1) (l : ℂ) :
    lambdaTail A k l = A ⟨k, hk⟩ + l • lambdaTail A (k + 1) l := by
  have h : ∀ j : Fin (d + 1), (if k ≤ (j : ℕ) then l ^ ((j : ℕ) - k) • A j else 0) =
      (if j = ⟨k, hk⟩ then A j else 0) +
        l • (if k + 1 ≤ (j : ℕ) then l ^ ((j : ℕ) - (k + 1)) • A j else 0) := by
    intro j
    by_cases hj : j = ⟨k, hk⟩
    · subst hj
      simp
    · have hj' : (j : ℕ) ≠ k := fun e => hj (Fin.ext e)
      by_cases hkj : k + 1 ≤ (j : ℕ)
      · have hkj' : k ≤ (j : ℕ) := by omega
        simp only [hkj', hj, hkj, ↓reduceIte, zero_add, smul_smul, ← pow_succ']
        congr 2
        omega
      · have hkj' : ¬ k ≤ (j : ℕ) := by omega
        simp [hkj', hj, hkj]
  simp only [lambdaTail, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, Finset.smul_sum]

/-- $P_d(\lambda) = A_d$. -/
theorem lambdaTail_self {d : ℕ} (A : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    lambdaTail A d l = A (Fin.last d) := by
  rw [lambdaTail, Finset.sum_eq_single (Fin.last d)]
  · simp
  · intro j _ hj
    have : ¬ d ≤ (j : ℕ) := fun h =>
      hj (Fin.ext (le_antisymm (Nat.lt_succ_iff.1 j.isLt) h))
    simp [this]
  · simp

/-- The coefficient $A_k$ at a natural index $k$, and $0$ for $k > d$. -/
private noncomputable def coeffAt {d : ℕ} (A : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  if h : k < d + 1 then A ⟨k, h⟩ else 0

/-- A sum over `Fin m` of a term that is selected by the value of the index is the term if $t < m$,
and $0$ otherwise. -/
private theorem sum_ite_val_eq {X : Type*} [AddCommMonoid X] (m t : ℕ) (Y : X) :
    (∑ b : Fin m, if (b : ℕ) = t then Y else 0) = if t < m then Y else 0 := by
  split_ifs with ht
  · rw [Finset.sum_eq_single ⟨t, ht⟩]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ t := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    have : (b : ℕ) ≠ t := fun h => ht (h ▸ b.isLt)
    simp [this]

/-- The blocks of $S(\lambda)$: $I$ on the diagonal and $-\lambda I$ on the superdiagonal. -/
private def sBlocks (l : ℂ) : Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => if (a : ℕ) = b then 1 else if (b : ℕ) = a + 1 then -(l • 1) else 0

/-- The blocks of $\operatorname{diag}(P(\lambda), I_{(d-1)n})$. -/
private noncomputable def dBlocks (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => if (a : ℕ) = b then (if (a : ℕ) = 0 then lambdaTail A 0 l else 1) else 0

/-- The blocks of $T(\lambda)$: the first block row $[0 \ \cdots \ 0 \ I]$, $-I$ on the subdiagonal,
and the last block column $[I; P_1(\lambda); \dots; P_{d-1}(\lambda)]$. -/
private noncomputable def tBlocks (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => if (b : ℕ) = e then (if (a : ℕ) = 0 then 1 else lambdaTail A a l)
    else if (a : ℕ) = b + 1 then -1 else 0

/-- The blocks of $L(\lambda)$, written as $L_0 + \lambda L_1$. -/
private def lBlocks (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => (if (b : ℕ) = e then A a.castSucc else if (a : ℕ) = b + 1 then -1 else 0) +
    l • (if (a : ℕ) = b then (if (a : ℕ) = e then A (Fin.last (e + 1)) else 1) else 0)

/-- The matrix $S(\lambda)$ of (7.7.6) in [golub2013matrix], with $d = e + 1$ block rows of size
$n$: identity blocks on the diagonal and $-\lambda I_n$ on the block superdiagonal.

The matrix is indexed by `Fin d × Fin n`, the block index first. -/
def linearizationS (l : ℂ) : Matrix (Fin (e + 1) × Fin n) (Fin (e + 1) × Fin n) ℂ :=
  comp _ _ _ _ ℂ (sBlocks l)

/-- The matrix $\operatorname{diag}(P(\lambda), I_{(d-1)n})$ of (7.7.6) in [golub2013matrix], with
$d = e + 1$ block rows of size $n$ and $P = P_0$ (`GolubVanLoan.Chapter07.lambdaTail`). -/
noncomputable def linearizationDiag (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1) × Fin n) (Fin (e + 1) × Fin n) ℂ :=
  comp _ _ _ _ ℂ (dBlocks A l)

/-- The matrix $T(\lambda)$ of (7.7.6) in [golub2013matrix], with $d = e + 1$ block rows of size
$n$: the first block row is $[0 \ \cdots \ 0 \ I]$, the block subdiagonal is $-I_n$, and the
last block column is $[I; P_1(\lambda); \dots; P_{d-1}(\lambda)]$. -/
noncomputable def linearizationT (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1) × Fin n) (Fin (e + 1) × Fin n) ℂ :=
  comp _ _ _ _ ℂ (tBlocks A l)

/-- The companion-form pencil $L(\lambda)$ of (7.7.6) in [golub2013matrix], with $d = e + 1$ block
rows of size $n$. Its block rows are $$[\lambda I \ \ 0 \ \cdots \ A_0], \quad [-I \ \ \lambda I
\ \cdots \ A_1], \quad \dots, \quad [0 \ \cdots \ -I \ \ A_{d-1} + \lambda A_d],$$ so
$L(\lambda) = L_0 + \lambda L_1$, where $L_0$ has $-I$ on the block subdiagonal and the last
block column $[A_0; \dots; A_{d-1}]$, and $L_1 = \operatorname{diag}(I, \dots, I, A_d)$. -/
def linearizationPencil (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1) × Fin n) (Fin (e + 1) × Fin n) ℂ :=
  comp _ _ _ _ ℂ (lBlocks A l)

/-- The block identity behind (7.7.6): the product of the blocks of $S(\lambda)$,
$\operatorname{diag}(P(\lambda), I)$ and $T(\lambda)$ is the block matrix of $L(\lambda)$. -/
private theorem blocks_mul (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    sBlocks l * dBlocks A l * tBlocks A l = lBlocks A l := by
  refine Matrix.ext fun a c => ?_
  have hSD : ∀ b, (sBlocks (n := n) (e := e) l * dBlocks A l) a b =
      sBlocks l a b * dBlocks A l b b := by
    intro b
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · intro b' _ hb'
      have : (b' : ℕ) ≠ b := fun h => hb' (Fin.ext h)
      simp [dBlocks, this]
    · simp
  set K : Matrix (Fin n) (Fin n) ℂ := if (c : ℕ) = e then lambdaTail A (a + 1) l
    else if (a : ℕ) = c then -1 else 0 with hK
  have hterm : ∀ b : Fin (e + 1), sBlocks l a b * dBlocks A l b b * tBlocks A l b c =
      (if b = a then dBlocks A l a a * tBlocks A l a c else 0) +
        (if (b : ℕ) = a + 1 then -(l • K) else 0) := by
    intro b
    by_cases hba : b = a
    · subst hba
      simp [sBlocks]
    · have hba' : (b : ℕ) ≠ a := fun h => hba (Fin.ext h)
      by_cases hb1 : (b : ℕ) = a + 1
      · have h1 : ¬ (a : ℕ) = a + 1 := by omega
        have h2 : ¬ (a : ℕ) + 1 = 0 := by omega
        have h3 : ((a : ℕ) + 1 = (c : ℕ) + 1) ↔ (a : ℕ) = c := by omega
        simp only [sBlocks, dBlocks, tBlocks, of_apply, hba, hb1, h1, h2, h3, ↓reduceIte,
          zero_add, K]
        split_ifs <;> simp
      · have hab : (a : ℕ) ≠ b := by omega
        simp [sBlocks, hba, hab, hb1]
  rw [Matrix.mul_apply]
  simp_rw [hSD]
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_add_distrib, Finset.sum_ite_eq',
    sum_ite_val_eq]
  have hAa : A a.castSucc = coeffAt A a := by simp [coeffAt, Fin.castSucc, Fin.castAdd, Fin.castLE]
  simp only [Finset.mem_univ, ↓reduceIte, dBlocks, tBlocks, lBlocks, of_apply, K, hAa]
  have hrec : ∀ k ≤ e, lambdaTail A k l = coeffAt A k + l • lambdaTail A (k + 1) l :=
    fun k hk => by rw [lambdaTail_eq_add A (by omega)]; simp [coeffAt, show k < e + 2 by omega]
  have hlast : lambdaTail A (e + 1) l = A (Fin.last (e + 1)) := lambdaTail_self A l
  have hae := Nat.lt_succ_iff.1 a.isLt
  have hce := Nat.lt_succ_iff.1 c.isLt
  generalize (a : ℕ) = x at hae ⊢
  generalize (c : ℕ) = y at hce ⊢
  by_cases hy : y = e
  · subst hy
    by_cases hx0 : x = 0
    · subst hx0
      by_cases he : y = 0
      · subst he
        simp [hrec 0 le_rfl, hlast]
      · have h1 : 0 < y := Nat.pos_of_ne_zero he
        simp [Ne.symm he, h1, hrec 0 (Nat.zero_le _)]
    · by_cases hxe : x = y
      · subst hxe
        simp [hx0, hrec x le_rfl, hlast]
      · have h1 : x + 1 < y + 1 := by omega
        simp [hx0, hxe, h1, hrec x hae]
  · by_cases hxy : x = y
    · subst hxy
      have h1 : x + 1 < e + 1 := by omega
      simp [hy, h1]
    · by_cases hx0 : x = 0
      · subst hx0
        simp [hy, hxy]
      · simp [hy, hxy, hx0]

/-- A block matrix that is block upper triangular with identity diagonal blocks has determinant $1$.
-/
private theorem det_comp_eq_one
    {X : Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ)}
    (hX : ∀ a b, b < a → X a b = 0) (hd : ∀ a, X a a = 1) :
    (comp _ _ _ _ ℂ X).det = 1 := by
  have hbt : (comp _ _ _ _ ℂ X).BlockTriangular Prod.fst := by
    intro i j hij
    simp [hX _ _ hij]
  rw [hbt.det]
  refine Finset.prod_eq_one fun k _ => ?_
  have h1 : (comp _ _ _ _ ℂ X).toSquareBlock Prod.fst k = 1 := by
    ext ⟨⟨a, i⟩, ha⟩ ⟨⟨b, j⟩, hb⟩
    simp only at ha hb
    subst ha hb
    simp only [toSquareBlock, toSquareBlockProp, toBlock, submatrix_apply, comp_apply, hd,
      Matrix.one_apply, Subtype.mk.injEq, Prod.mk.injEq, true_and]
  rw [h1, det_one]

/-- The constant factor $T_0$ of $T(\lambda)$: $I$ in block $(0, d-1)$ and $-I$ on the block
subdiagonal. -/
private def t0Blocks : Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => if (b : ℕ) = e then (if (a : ℕ) = 0 then 1 else 0)
    else if (a : ℕ) = b + 1 then -1 else 0

/-- The unit upper triangular factor $V(\lambda)$ of $T(\lambda) = T_0 V(\lambda)$. -/
private noncomputable def vBlocks (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => if (a : ℕ) = b then 1 else if (b : ℕ) = e then -lambdaTail A (a + 1) l else 0

/-- A sum over `Fin m` whose left factor is supported at one index value $t < m$ is the term at $t$.
-/
private theorem sum_single_mul_left {X : Type*} [NonUnitalNonAssocSemiring X] {m t : ℕ}
    (ht : t < m) (x : X) (g : Fin m → X) :
    ∑ b : Fin m, (if (b : ℕ) = t then x else 0) * g b = x * g ⟨t, ht⟩ := by
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ t := fun h => hb (Fin.ext h)
    simp [this]
  · simp

/-- The rows of $T_0$: row $a$ has its only nonzero block in column $a - 1$, or in column $d - 1$
for $a = 0$. -/
private theorem t0Blocks_row (a b : Fin (e + 1)) :
    (t0Blocks : Matrix _ _ (Matrix (Fin n) (Fin n) ℂ)) a b =
      if (b : ℕ) = (if (a : ℕ) = 0 then e else (a : ℕ) - 1) then
        (if (a : ℕ) = 0 then 1 else -1) else 0 := by
  have hb := b.isLt
  have ha := a.isLt
  simp only [t0Blocks, of_apply]
  split_ifs <;> first | rfl | omega

/-- The columns of $T_0$: column $b$ has its only nonzero block in row $b + 1$, or in row $0$ for
$b = d - 1$. -/
private theorem t0Blocks_col (a b : Fin (e + 1)) :
    (t0Blocks : Matrix _ _ (Matrix (Fin n) (Fin n) ℂ)) a b =
      if (a : ℕ) = (if (b : ℕ) = e then 0 else (b : ℕ) + 1) then
        (if (b : ℕ) = e then 1 else -1) else 0 := by
  have hb := b.isLt
  have ha := a.isLt
  simp only [t0Blocks, of_apply]
  split_ifs <;> rfl

private theorem tBlocks_eq_mul (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    tBlocks A l = t0Blocks * vBlocks A l := by
  refine Matrix.ext fun a c => ?_
  have ha := a.isLt
  have hc := c.isLt
  have hτ : (if (a : ℕ) = 0 then e else (a : ℕ) - 1) < e + 1 := by split_ifs <;> omega
  rw [Matrix.mul_apply]
  simp_rw [t0Blocks_row a]
  rw [sum_single_mul_left hτ]
  simp only [tBlocks, vBlocks, of_apply]
  by_cases ha0 : (a : ℕ) = 0
  · by_cases hce : (c : ℕ) = e
    · simp [ha0, hce]
    · have : (e : ℕ) ≠ c := fun h => hce h.symm
      simp [ha0, hce, this]
  · by_cases hce : (c : ℕ) = e
    · have : (a : ℕ) - 1 ≠ e := by omega
      have h1 : (a : ℕ) - 1 + 1 = a := by omega
      simp [ha0, hce, this, h1]
    · have h1 : ((a : ℕ) - 1 = c) ↔ ((a : ℕ) = c + 1) := by omega
      simp only [ha0, hce, ↓reduceIte, h1]
      split_ifs <;> simp

/-- The block transpose of $T_0$ is its inverse. -/
private theorem t0Blocks_transpose_mul :
    (of fun a b => (t0Blocks : Matrix _ _ (Matrix (Fin n) (Fin n) ℂ)) b a) * t0Blocks =
      (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ)) := by
  refine Matrix.ext fun a c => ?_
  have ha := a.isLt
  have hc := c.isLt
  have hσ : (if (a : ℕ) = e then 0 else (a : ℕ) + 1) < e + 1 := by split_ifs <;> omega
  rw [Matrix.mul_apply]
  simp only [of_apply]
  simp_rw [t0Blocks_col _ a]
  rw [sum_single_mul_left hσ, t0Blocks_col]
  simp only
  by_cases hac : a = c
  · subst hac
    split_ifs <;> first | (exfalso; omega) | simp
  · have hac' : (a : ℕ) ≠ c := fun h => hac (Fin.ext h)
    rw [one_apply_ne hac]
    split_ifs <;> first | (exfalso; omega) | simp

/-- **Equation (7.7.6)** of [golub2013matrix], the linearization of a polynomial eigenvalue problem.
Let $d \ge 1$, let $A_0, \dots, A_d \in \mathbb{C}^{n \times n}$, and let $P(\lambda) = A_0 +
\lambda A_1 + \dots + \lambda^d A_d$. Then for every $\lambda \in \mathbb{C}$, $$S(\lambda)
\begin{bmatrix} P(\lambda) & 0 \\ 0 & I_{(d-1)n} \end{bmatrix} T(\lambda) = L(\lambda),$$ where
$L(\lambda)$ is the companion-form pencil of degree one. Moreover $\det S(\lambda) = 1$,
$\det T(\lambda) = \pm 1$, and $\det T(\lambda)$ does not depend on $\lambda$. In the words of
the source, "$L(\lambda)$ is a linearization of $P(\lambda)$".

The source displays the steps for $d = 2$ and $d = 3$; the theorem holds for every $d \ge 1$.
The degree is $d = e + 1$, and the coefficients are
`A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ`. The factors are
`GolubVanLoan.Chapter07.linearizationS`, `GolubVanLoan.Chapter07.linearizationDiag`,
`GolubVanLoan.Chapter07.linearizationT` and `GolubVanLoan.Chapter07.linearizationPencil`.

**Reading.** The source assumes a nonzero leading coefficient and describes a degree-one
linearization. Lean proves the factorization and determinant identities for all supplied
coefficients and each evaluation point. The pencil is affine in $\lambda$ and can have lower
degree for degenerate coefficients. -/
theorem equation_7_7_6 (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    linearizationS l * linearizationDiag A l * linearizationT A l = linearizationPencil A l ∧
      (linearizationS (n := n) (e := e) l).det = 1 ∧
      ((linearizationT A l).det = 1 ∨ (linearizationT A l).det = -1) ∧
      ∀ l', (linearizationT A l').det = (linearizationT A l).det := by
  have hmul : ∀ X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ),
      comp _ _ _ _ ℂ (X * Y) = comp _ _ _ _ ℂ X * comp _ _ _ _ ℂ Y := fun X Y =>
    (compRingEquiv (Fin (e + 1)) (Fin n) ℂ).map_mul X Y
  have hT : ∀ l', (linearizationT A l').det =
      (comp _ _ _ _ ℂ (t0Blocks (n := n) (e := e))).det := by
    intro l'
    rw [linearizationT, tBlocks_eq_mul, hmul, det_mul,
      det_comp_eq_one (X := vBlocks A l') _ _, mul_one]
    · intro a b hab
      have : (a : ℕ) ≠ b := fun h => (Fin.ne_of_gt hab) (Fin.ext h)
      have hb : (b : ℕ) ≠ e := by have := a.isLt; have := Fin.lt_def.1 hab; omega
      simp [vBlocks, this, hb]
    · intro a
      simp [vBlocks]
  refine ⟨?_, ?_, ?_, fun l' => by rw [hT, hT]⟩
  · rw [linearizationS, linearizationDiag, linearizationT, linearizationPencil, ← hmul, ← hmul,
      blocks_mul]
  · refine det_comp_eq_one (fun a b hab => ?_) fun a => ?_
    · have h1 : (a : ℕ) ≠ b := fun h => (Fin.ne_of_gt hab) (Fin.ext h)
      have h2 : (b : ℕ) ≠ a + 1 := by have := Fin.lt_def.1 hab; omega
      simp [sBlocks, h1, h2]
    · simp [sBlocks]
  · rw [hT]
    have htr : comp _ _ _ _ ℂ
        (of fun a b => (t0Blocks (n := n) (e := e)) b a) =
        (comp _ _ _ _ ℂ (t0Blocks (n := n) (e := e)))ᵀ := by
      ext ⟨a, i⟩ ⟨b, j⟩
      simp only [comp_apply, of_apply, transpose_apply, t0Blocks]
      split_ifs <;> simp [Matrix.one_apply, eq_comm]
    have h1 := congrArg det (congrArg (comp _ _ _ _ ℂ) (t0Blocks_transpose_mul (n := n) (e := e)))
    rw [hmul, htr, det_mul, det_transpose, Matrix.comp_one, det_one] at h1
    exact mul_self_eq_one_iff.1 h1

end Linearization


/-! ### §7.7.6–§7.7.7 The QZ step and the QZ algorithm: exact semantics -/

section Reflectors

open GolubVanLoan.Chapter05

/-- The exact output $(v, \beta)$ of `house` on a duplicate-free nonempty index list $o$: $v$
vanishes off $o$, either $\beta = 0$ or $\beta\, v^T v = 2$, and $(I - \beta v v^T) x$ vanishes
at every index of $o$ other than its head. -/
private theorem houseOn_exact {o : List (Fin n)} (ho : o.Nodup) (hne : o ≠ []) (x : Fin n → ℝ) :
    (∀ l, l ∉ o → (Id.run (houseOn pure o x)).1 l = 0) ∧
      ((Id.run (houseOn pure o x)).2 = 0 ∨
        (Id.run (houseOn pure o x)).2 *
          ((Id.run (houseOn pure o x)).1 ⬝ᵥ (Id.run (houseOn pure o x)).1) = 2) ∧
      ∀ i ∈ o, i ≠ o.head hne → ((1 - (Id.run (houseOn pure o x)).2 •
        vecMulVec (Id.run (houseOn pure o x)).1 (Id.run (houseOn pure o x)).1) *ᵥ x) i = 0 := by
  obtain ⟨-, hout, hβ, -, hmul⟩ := houseOn_spec ho hne x
  refine ⟨hout, hβ, fun i hi hih => ?_⟩
  rw [hmul]
  simp [hih, hi]

private theorem nodup_three {a b c : Fin n} (h1 : (a : ℕ) ≠ b) (h2 : (a : ℕ) ≠ c)
    (h3 : (b : ℕ) ≠ c) :
    [a, b, c].Nodup := by
  refine List.nodup_cons.2 ⟨fun h => ?_, List.nodup_cons.2 ⟨fun h => ?_, List.nodup_singleton _⟩⟩
  · rcases List.mem_cons.1 h with h | h
    · exact h1 (congrArg Fin.val h)
    · exact h2 (congrArg Fin.val (List.mem_singleton.1 h))
  · exact h3 (congrArg Fin.val (List.mem_singleton.1 h))

private theorem nodup_two {a b : Fin n} (h1 : (a : ℕ) ≠ b) : [a, b].Nodup :=
  List.nodup_cons.2 ⟨by simpa [Fin.ext_iff] using h1, List.nodup_singleton _⟩

end Reflectors

section QZStepInvariant

open GolubVanLoan.Chapter05

/-- The loop invariant of the QZ step on the block $p, \dots, r$ before the step at $j$: the
equivalence with the reflector data, the support of the data and the dichotomy for $\beta$, the
bulge of $A$ (only at $(j+1, j-1)$, $(j+2, j-1)$ and $(j+2, j)$ once $j > p$), $B$ upper
triangular, the block decoupled from column $p - 1$ and row $r + 1$, the current $x, y, z$ read
from column $j - 1$, the initial state at $j = p$, and the first left reflector. -/
private structure QZStepInv (A₀ B₀ : Matrix (Fin n) (Fin n) ℝ) (p r j : ℕ) (x₀ y₀ z₀ : ℝ)
    (st : QZStepState n) : Prop where
  eqA : st.A = (householderProduct st.dQ)ᵀ * A₀ * householderProduct st.dZ
  eqB : st.B = (householderProduct st.dQ)ᵀ * B₀ * householderProduct st.dZ
  betaQ : ∀ d ∈ st.dQ, d.2 = 0 ∨ d.2 * (d.1 ⬝ᵥ d.1) = 2
  betaZ : ∀ d ∈ st.dZ, d.2 = 0 ∨ d.2 * (d.1 ⬝ᵥ d.1) = 2
  suppQ : ∀ d ∈ st.dQ, ∀ l : Fin n, ((l : ℕ) < p ∨ r < l) → d.1 l = 0
  suppZ : ∀ d ∈ st.dZ, ∀ l : Fin n, ((l : ℕ) < p ∨ r < l) → d.1 l = 0
  bulge : ∀ i c : Fin n, (c : ℕ) + 1 < i → ¬ (p < j ∧ (((i : ℕ) = j + 1 ∧ (c : ℕ) + 1 = j) ∨
    ((i : ℕ) = j + 2 ∧ (c : ℕ) + 1 = j) ∨ ((i : ℕ) = j + 2 ∧ (c : ℕ) = j))) → st.A i c = 0
  tri : ∀ i c : Fin n, (c : ℕ) < i → st.B i c = 0
  col : ∀ i c : Fin n, 0 < p → (c : ℕ) + 1 = p → p ≤ (i : ℕ) → st.A i c = 0
  row : ∀ i c : Fin n, (i : ℕ) = r + 1 → (c : ℕ) ≤ r → st.A i c = 0
  xyz : ∀ i c : Fin n, p < j → (c : ℕ) + 1 = j →
    ((i : ℕ) = j → st.x = st.A i c) ∧ ((i : ℕ) = j + 1 → st.y = st.A i c) ∧
      ((i : ℕ) = j + 2 → j + 2 ≤ r → st.z = st.A i c)
  init : j = p → st.dQ = [] ∧ st.x = x₀ ∧ st.y = y₀ ∧ st.z = z₀
  first : p < j → ∃ d₀ rest, st.dQ = d₀ :: rest ∧ (∀ l : Fin n, (l : ℕ) ≠ p →
      ((1 - d₀.2 • vecMulVec d₀.1 d₀.1) *ᵥ fun i : Fin n => if (i : ℕ) = p then x₀ else
        if (i : ℕ) = p + 1 then y₀ else if (i : ℕ) = p + 2 then z₀ else 0) l = 0) ∧
      ∀ d ∈ rest, ∀ l : Fin n, (l : ℕ) = p → d.1 l = 0

variable {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ}

/-- One step of the loop of the QZ step keeps the invariant and moves the bulge from $j$ to $j + 1$.
-/
private theorem qzStep_inv {p r : ℕ} (hr : r < n) {x₀ y₀ z₀ : ℝ} {j : Fin n} (hpj : p ≤ j)
    (hjr : (j : ℕ) + 2 ≤ r) {st : QZStepState n}
    (h : QZStepInv A₀ B₀ p r j x₀ y₀ z₀ st) :
    QZStepInv A₀ B₀ p r (j + 1) x₀ y₀ z₀
      (Id.run (qzStep pure r j ⟨(j : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 2, by omega⟩ st)) := by
  set j₁ : Fin n := ⟨(j : ℕ) + 1, by omega⟩ with hj₁
  set j₂ : Fin n := ⟨(j : ℕ) + 2, by omega⟩ with hj₂
  have hj₁v : (j₁ : ℕ) = j + 1 := rfl
  have hj₂v : (j₂ : ℕ) = j + 2 := rfl
  have hmem : ∀ i : Fin n, i ∈ [j, j₁, j₂] ↔
      ((i : ℕ) = j ∨ (i : ℕ) = j + 1 ∨ (i : ℕ) = j + 2) := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hj₁v,
      hj₂v]
  have hmem' : ∀ i : Fin n, i ∈ [j₂, j₁, j] ↔
      ((i : ℕ) = j ∨ (i : ℕ) = j + 1 ∨ (i : ℕ) = j + 2) := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hj₁v,
      hj₂v]
    omega
  have hmem₃ : ∀ i : Fin n, i ∈ [j₁, j] ↔ ((i : ℕ) = j ∨ (i : ℕ) = j + 1) := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hj₁v]
    omega
  have hnd : [j, j₁, j₂].Nodup := nodup_three (by omega) (by omega) (by omega)
  have hnd' : [j₂, j₁, j].Nodup := nodup_three (by omega) (by omega) (by omega)
  have hnd₃ : [j₁, j].Nodup := nodup_two (by omega)
  -- the first reflector `Q_k`
  obtain ⟨hq0, hqβ, hqz⟩ := houseOn_exact hnd (List.cons_ne_nil _ _) (fun i =>
    if i = j then st.x else if i = j₁ then st.y else if i = j₂ then st.z else 0)
  set q := Id.run (houseOn pure [j, j₁, j₂] (fun i =>
    if i = j then st.x else if i = j₁ then st.y else if i = j₂ then st.z else 0)) with hq
  set P₁ : Matrix (Fin n) (Fin n) ℝ := 1 - q.2 • vecMulVec q.1 q.1 with hP₁
  set A₁ := P₁ * st.A with hA₁
  set B₁ := P₁ * st.B with hB₁
  -- the reflector `Z_{k1}`
  obtain ⟨hz0, hzβ, hzz⟩ := houseOn_exact hnd' (List.cons_ne_nil _ _) (B₁ j₂)
  set z₁ := Id.run (houseOn pure [j₂, j₁, j] (B₁ j₂)) with hz₁
  set P₂ : Matrix (Fin n) (Fin n) ℝ := 1 - z₁.2 • vecMulVec z₁.1 z₁.1 with hP₂
  set A₂ := A₁ * P₂ with hA₂
  set B₂ := B₁ * P₂ with hB₂
  -- the reflector `Z_{k2}`
  obtain ⟨hw0, hwβ, hwz⟩ := houseOn_exact hnd₃ (List.cons_ne_nil _ _) (B₂ j₁)
  set z₂ := Id.run (houseOn pure [j₁, j] (B₂ j₁)) with hz₂
  set P₃ : Matrix (Fin n) (Fin n) ℝ := 1 - z₂.2 • vecMulVec z₂.1 z₂.1 with hP₃
  set A₃ := A₂ * P₃ with hA₃
  set B₃ := B₂ * P₃ with hB₃
  have hrun : Id.run (qzStep pure r j j₁ j₂ st) = ⟨A₃, B₃, st.dQ ++ [q], st.dZ ++ [z₁, z₂],
      A₃ j₁ j, A₃ j₂ j, if (j : ℕ) + 3 ≤ r then qzEntry A₃ ((j : ℕ) + 3) j else st.z⟩ := by
    simp only [qzStep, Id.run_bind, Id.run_pure]
    rw [← hq, householderApplyLeft_spec_of_forall_mem hnd (List.nodup_finRange n)
      List.mem_finRange hq0, householderApplyLeft_spec_of_forall_mem hnd
      (List.nodup_finRange n) List.mem_finRange hq0, ← hP₁, ← hA₁, ← hB₁, ← hz₁,
      householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd' List.mem_finRange
      hz0, householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd'
      List.mem_finRange hz0, ← hP₂, ← hA₂, ← hB₂, ← hz₂,
      householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd₃ List.mem_finRange
      hw0, householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd₃
      List.mem_finRange hw0]
  rw [hrun]
  have hjpos : p < (j : ℕ) + 1 := by omega
  -- the columns and rows of the reflectors
  have hq0' : ∀ l : Fin n, ¬ ((l : ℕ) = j ∨ (l : ℕ) = j + 1 ∨ (l : ℕ) = j + 2) → q.1 l = 0 :=
    fun l hl => hq0 l ((hmem l).not.2 hl)
  have hz0' : ∀ l : Fin n, ¬ ((l : ℕ) = j ∨ (l : ℕ) = j + 1 ∨ (l : ℕ) = j + 2) → z₁.1 l = 0 :=
    fun l hl => hz0 l ((hmem' l).not.2 hl)
  have hw0' : ∀ l : Fin n, ¬ ((l : ℕ) = j ∨ (l : ℕ) = j + 1) → z₂.1 l = 0 :=
    fun l hl => hw0 l ((hmem₃ l).not.2 hl)
  -- `A₁`: the bulge column `j - 1` is cleared, a fill-in may appear at `(j + 2, j)`
  have hA₁z : ∀ i c : Fin n, (c : ℕ) + 1 < i → ¬ ((i : ℕ) = j + 2 ∧ (c : ℕ) = j) →
      A₁ i c = 0 := by
    intro i c hic hne
    by_cases hio : (i : ℕ) = j ∨ (i : ℕ) = j + 1 ∨ (i : ℕ) = j + 2
    · by_cases hcj : (c : ℕ) + 1 = j
      · by_cases hpj' : p < (j : ℕ)
        · -- the reflector clears the column `j - 1` below its first entry
          have hcol : ∀ l ∈ [j, j₁, j₂], st.A l c = (fun i =>
              if i = j then st.x else if i = j₁ then st.y else if i = j₂ then st.z else 0) l := by
            intro l hl
            obtain ⟨hx, hy, hz⟩ := h.xyz l c hpj' hcj
            rw [hmem] at hl
            rcases hl with hl | hl | hl
            · have : l = j := Fin.ext hl
              subst this
              simp [hx rfl]
            · have : l = j₁ := Fin.ext hl
              subst this
              have hne : j₁ ≠ j := fun e => by rw [e] at hj₁v; omega
              simp [hne, hy hj₁v]
            · have : l = j₂ := Fin.ext hl
              subst this
              have hne : j₂ ≠ j := fun e => by rw [e] at hj₂v; omega
              have hne' : j₂ ≠ j₁ := fun e => by rw [e] at hj₂v; omega
              simp [hne, hne', hz hj₂v hjr]
          rw [hA₁, one_sub_smul_vecMulVec_mul_apply_eq_mulVec hq0 _ _ _ hcol ((hmem i).2 hio)]
          exact hqz i ((hmem i).2 hio) (fun e => by rw [e, List.head_cons] at hic; omega)
        · -- `j = p`: the column `p - 1` vanishes on the block
          have hp0 : 0 < p := by omega
          have hcol : ∀ l ∈ [j, j₁, j₂], st.A l c = 0 := fun l hl => by
            rw [hmem] at hl
            exact h.col l c hp0 (by omega) (by omega)
          rw [hA₁, one_sub_smul_vecMulVec_mul_apply_of_forall hq0 _ _ hcol]
          exact h.col i c hp0 (by omega) (by omega)
      · have hcol : ∀ l ∈ [j, j₁, j₂], st.A l c = 0 := fun l hl => by
          rw [hmem] at hl
          exact h.bulge l c (by omega) (by omega)
        rw [hA₁, one_sub_smul_vecMulVec_mul_apply_of_forall hq0 _ _ hcol]
        exact h.bulge i c hic (by omega)
    · rw [hA₁, one_sub_smul_vecMulVec_mul_apply_of_notMem hq0 _ _ ((hmem i).not.2 hio)]
      exact h.bulge i c hic (by omega)
  -- `B₁`: upper triangular except in the rows `j + 1, j + 2`, columns `j, j + 1`
  have hB₁z : ∀ i c : Fin n, (c : ℕ) < i →
      ¬ (((i : ℕ) = j + 1 ∨ (i : ℕ) = j + 2) ∧ ((c : ℕ) = j ∨ (c : ℕ) = j + 1)) → B₁ i c = 0 := by
    intro i c hic hne
    by_cases hio : (i : ℕ) = j ∨ (i : ℕ) = j + 1 ∨ (i : ℕ) = j + 2
    · have hcol : ∀ l ∈ [j, j₁, j₂], st.B l c = 0 := fun l hl => by
        rw [hmem] at hl
        exact h.tri l c (by omega)
      rw [hB₁, one_sub_smul_vecMulVec_mul_apply_of_forall hq0 _ _ hcol]
      exact h.tri i c hic
    · rw [hB₁, one_sub_smul_vecMulVec_mul_apply_of_notMem hq0 _ _ ((hmem i).not.2 hio)]
      exact h.tri i c hic
  -- `B₂`: only `(j + 1, j)` below the diagonal
  have hB₂z : ∀ i c : Fin n, (c : ℕ) < i → ¬ ((i : ℕ) = j + 1 ∧ (c : ℕ) = j) → B₂ i c = 0 := by
    intro i c hic hne
    by_cases hco : (c : ℕ) = j ∨ (c : ℕ) = j + 1 ∨ (c : ℕ) = j + 2
    · by_cases hi2 : (i : ℕ) = j + 2
      · have hi : i = j₂ := Fin.ext hi2
        subst hi
        rw [hB₂, mul_one_sub_smul_vecMulVec_apply_eq_mulVec]
        exact hzz c ((hmem' c).2 hco) (fun e => by rw [e, List.head_cons] at hic; omega)
      · have hrow : ∀ l ∈ [j₂, j₁, j], B₁ i l = 0 := fun l hl => by
          rw [hmem'] at hl
          exact hB₁z i l (by omega) (by omega)
        rw [hB₂, mul_one_sub_smul_vecMulVec_apply_of_forall hz0 _ _ hrow]
        exact hB₁z i c hic (by omega)
    · rw [hB₂, mul_one_sub_smul_vecMulVec_apply_of_notMem hz0 _ _ _ ((hmem' c).not.2 hco)]
      exact hB₁z i c hic (by omega)
  -- `A₂`: the bulge moves to `(j + 2, j)`, `(j + 3, j)`, `(j + 3, j + 1)`
  have hA₂z : ∀ i c : Fin n, (c : ℕ) + 1 < i → ¬ (((i : ℕ) = j + 2 ∧ (c : ℕ) = j) ∨
      ((i : ℕ) = j + 3 ∧ ((c : ℕ) = j ∨ (c : ℕ) = j + 1))) → A₂ i c = 0 := by
    intro i c hic hne
    by_cases hco : (c : ℕ) = j ∨ (c : ℕ) = j + 1 ∨ (c : ℕ) = j + 2
    · have hrow : ∀ l ∈ [j₂, j₁, j], A₁ i l = 0 := fun l hl => by
        rw [hmem'] at hl
        exact hA₁z i l (by omega) (by omega)
      rw [hA₂, mul_one_sub_smul_vecMulVec_apply_of_forall hz0 _ _ hrow]
      exact hA₁z i c hic (by omega)
    · rw [hA₂, mul_one_sub_smul_vecMulVec_apply_of_notMem hz0 _ _ _ ((hmem' c).not.2 hco)]
      exact hA₁z i c hic (by omega)
  -- `B₃` is upper triangular
  have hB₃z : ∀ i c : Fin n, (c : ℕ) < i → B₃ i c = 0 := by
    intro i c hic
    by_cases hco : (c : ℕ) = j ∨ (c : ℕ) = j + 1
    · by_cases hi1 : (i : ℕ) = j + 1
      · have hi : i = j₁ := Fin.ext hi1
        subst hi
        rw [hB₃, mul_one_sub_smul_vecMulVec_apply_eq_mulVec]
        exact hwz c ((hmem₃ c).2 hco) (fun e => by rw [e, List.head_cons] at hic; omega)
      · have hrow : ∀ l ∈ [j₁, j], B₂ i l = 0 := fun l hl => by
          rw [hmem₃] at hl
          exact hB₂z i l (by omega) (by omega)
        rw [hB₃, mul_one_sub_smul_vecMulVec_apply_of_forall hw0 _ _ hrow]
        exact hB₂z i c hic (by omega)
    · rw [hB₃, mul_one_sub_smul_vecMulVec_apply_of_notMem hw0 _ _ _ ((hmem₃ c).not.2 hco)]
      exact hB₂z i c hic (by omega)
  -- `A₃` keeps the new bulge
  have hA₃z : ∀ i c : Fin n, (c : ℕ) + 1 < i → ¬ (((i : ℕ) = j + 2 ∧ (c : ℕ) = j) ∨
      ((i : ℕ) = j + 3 ∧ ((c : ℕ) = j ∨ (c : ℕ) = j + 1))) → A₃ i c = 0 := by
    intro i c hic hne
    by_cases hco : (c : ℕ) = j ∨ (c : ℕ) = j + 1
    · have hrow : ∀ l ∈ [j₁, j], A₂ i l = 0 := fun l hl => by
        rw [hmem₃] at hl
        exact hA₂z i l (by omega) (by omega)
      rw [hA₃, mul_one_sub_smul_vecMulVec_apply_of_forall hw0 _ _ hrow]
      exact hA₂z i c hic (by omega)
    · rw [hA₃, mul_one_sub_smul_vecMulVec_apply_of_notMem hw0 _ _ _ ((hmem₃ c).not.2 hco)]
      exact hA₂z i c hic (by omega)
  -- the decoupling of column `p - 1` and row `r + 1`
  have hcol₃ : ∀ i c : Fin n, 0 < p → (c : ℕ) + 1 = p → p ≤ (i : ℕ) → A₃ i c = 0 := by
    intro i c hp0 hc hi
    have hco : ¬ ((c : ℕ) = j ∨ (c : ℕ) = j + 1 ∨ (c : ℕ) = j + 2) := by omega
    have hco₃ : ¬ ((c : ℕ) = j ∨ (c : ℕ) = j + 1) := by omega
    rw [hA₃, mul_one_sub_smul_vecMulVec_apply_of_notMem hw0 _ _ _ ((hmem₃ c).not.2 hco₃), hA₂,
      mul_one_sub_smul_vecMulVec_apply_of_notMem hz0 _ _ _ ((hmem' c).not.2 hco), hA₁,
      one_sub_smul_vecMulVec_mul_apply_of_forall hq0 _ _ (fun l hl => by
        rw [hmem] at hl; exact h.col l c hp0 hc (by omega))]
    exact h.col i c hp0 hc hi
  have hrowA₁ : ∀ i c : Fin n, (i : ℕ) = r + 1 → (c : ℕ) ≤ r → A₁ i c = 0 := by
    intro i c hi hc
    rw [hA₁, one_sub_smul_vecMulVec_mul_apply_of_notMem hq0 _ _ ((hmem i).not.2 (by omega))]
    exact h.row i c hi hc
  have hrowA₂ : ∀ i c : Fin n, (i : ℕ) = r + 1 → (c : ℕ) ≤ r → A₂ i c = 0 := by
    intro i c hi hc
    rw [hA₂, mul_one_sub_smul_vecMulVec_apply_of_forall hz0 _ _ (fun l hl => by
      rw [hmem'] at hl; exact hrowA₁ i l hi (by omega))]
    exact hrowA₁ i c hi hc
  have hrow₃ : ∀ i c : Fin n, (i : ℕ) = r + 1 → (c : ℕ) ≤ r → A₃ i c = 0 := by
    intro i c hi hc
    rw [hA₃, mul_one_sub_smul_vecMulVec_apply_of_forall hw0 _ _ (fun l hl => by
      rw [hmem₃] at hl; exact hrowA₂ i l hi (by omega))]
    exact hrowA₂ i c hi hc
  -- the reflector products
  have hsym : ∀ d : (Fin n → ℝ) × ℝ, (1 - d.2 • vecMulVec d.1 d.1)ᵀ = 1 - d.2 • vecMulVec d.1 d.1 :=
    fun d => transpose_one_sub_smul_vecMulVec _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hB₃z, hcol₃, hrow₃, ?_, fun e => by omega, ?_⟩
  · -- `eqA`
    simp only
    rw [householderProduct_concat, show st.dZ ++ [z₁, z₂] = (st.dZ ++ [z₁]) ++ [z₂] by simp,
      householderProduct_concat, householderProduct_concat, transpose_mul, hsym, hA₃, hA₂, hA₁,
      h.eqA]
    simp only [hP₁, hP₂, hP₃, Matrix.mul_assoc]
  · simp only
    rw [householderProduct_concat, show st.dZ ++ [z₁, z₂] = (st.dZ ++ [z₁]) ++ [z₂] by simp,
      householderProduct_concat, householderProduct_concat, transpose_mul, hsym, hB₃, hB₂, hB₁,
      h.eqB]
    simp only [hP₁, hP₂, hP₃, Matrix.mul_assoc]
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h.betaQ d hd
    · rw [List.mem_singleton.1 hd]; exact hqβ
  · intro d hd
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd
    · exact h.betaZ d hd
    · rw [hd]; exact hzβ
    · rw [hd]; exact hwβ
  · intro d hd l hl
    rcases List.mem_append.1 hd with hd | hd
    · exact h.suppQ d hd l hl
    · rw [List.mem_singleton.1 hd]; exact hq0' l (by omega)
  · intro d hd l hl
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd
    · exact h.suppZ d hd l hl
    · rw [hd]; exact hz0' l (by omega)
    · rw [hd]; exact hw0' l (by omega)
  · -- the new bulge
    intro i c hic hne
    exact hA₃z i c hic (by push_cast at hne; omega)
  · -- `x, y, z` for the next step
    intro i c _ hc
    push_cast at hc ⊢
    have hcj : c = j := Fin.ext (by omega)
    subst hcj
    refine ⟨fun hi => ?_, fun hi => ?_, fun hi hir => ?_⟩
    · congr 1
      exact Fin.ext (by omega)
    · congr 1
      exact Fin.ext (by omega)
    · simp only [show (c : ℕ) + 3 ≤ r by omega, ↓reduceIte]
      rw [qzEntry_of_lt A₃ (by omega) c.isLt]
      congr 1
      exact Fin.ext (by simp; omega)
  · -- the first reflector
    intro _
    by_cases hjp : (j : ℕ) = p
    · obtain ⟨hdQ, hx, hy, hz⟩ := h.init hjp
      refine ⟨q, [], by simp [hdQ], fun l hl => ?_, by simp⟩
      have hu : (fun i : Fin n => if (i : ℕ) = p then x₀ else if (i : ℕ) = p + 1 then y₀
          else if (i : ℕ) = p + 2 then z₀ else 0) =
          fun i => if i = j then st.x else if i = j₁ then st.y else if i = j₂ then st.z
            else 0 := by
        funext i
        simp only [Fin.ext_iff, hj₁v, hj₂v, hjp, hx, hy, hz]
      rw [hu]
      by_cases hlo : (l : ℕ) = j ∨ (l : ℕ) = j + 1 ∨ (l : ℕ) = j + 2
      · exact hqz l ((hmem l).2 hlo) (fun e => by rw [e, List.head_cons] at hl; omega)
      · rw [FloatingPoint.one_sub_smul_vecMulVec_mulVec_apply, hq0' l hlo]
        have h1 : l ≠ j := fun e => by rw [e] at hlo; omega
        have h2 : l ≠ j₁ := fun e => by rw [e] at hlo; omega
        have h3 : l ≠ j₂ := fun e => by rw [e] at hlo; omega
        simp [h1, h2, h3]
    · obtain ⟨d₀, rest, hdQ, hd₀, hrest⟩ := h.first (by omega)
      refine ⟨d₀, rest ++ [q], by simp [hdQ], hd₀, fun d hd l hl => ?_⟩
      rcases List.mem_append.1 hd with hd | hd
      · exact hrest d hd l hl
      · rw [List.mem_singleton.1 hd]; exact hq0' l (by omega)

end QZStepInvariant

section QZStepSpec

open GolubVanLoan.Chapter05

variable {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ}

/-- The invariant of the QZ step holds before its loop. -/
private theorem qzStepInv_init {p r : ℕ} (hr : r < n) {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsUpperHessenberg) (hB : B.IsUpperTriangular)
    (hp : 0 < p → qzEntry A p (p - 1) = 0) (hr₁ : qzEntry A (r + 1) r = 0) (x₀ y₀ z₀ : ℝ) :
    QZStepInv A B p r p x₀ y₀ z₀ ⟨A, B, [], [], x₀, y₀, z₀⟩ := by
  rw [isUpperHessenberg_iff_fin] at hA
  rw [isUpperTriangular_iff_fin] at hB
  refine ⟨by simp [householderProduct_nil], by simp [householderProduct_nil], by simp, by simp,
    by simp, by simp, fun i c hic _ => hA i c hic, hB, fun i c hp0 hc hi => ?_,
    fun i c hi hc => ?_, fun _ _ h => absurd h (lt_irrefl p), fun _ => ⟨rfl, rfl, rfl, rfl⟩,
    fun h => absurd h (lt_irrefl p)⟩
  · by_cases hip : (i : ℕ) = p
    · have := hp hp0
      rw [qzEntry_of_lt A (by omega) (by omega)] at this
      convert this using 2 <;> exact Fin.ext (by simp; omega)
    · exact hA i c (by omega)
  · by_cases hcr : (c : ℕ) = r
    · rw [qzEntry_of_lt A (by omega) (by omega)] at hr₁
      convert hr₁ using 2 <;> exact Fin.ext (by simp; omega)
    · exact hA i c (by omega)

/-- The loop of the QZ step keeps the invariant; after the loop the bulge is at $j = r - 1$. -/
private theorem qzLoop_inv {p r : ℕ} (hpr : p < r) (hr : r < n) {x₀ y₀ z₀ : ℝ}
    {st : QZStepState n} (h : QZStepInv A₀ B₀ p r p x₀ y₀ z₀ st) :
    QZStepInv A₀ B₀ p r (r - 1) x₀ y₀ z₀
      ((List.finRange n).foldl (fun st (j : Fin n) =>
        Id.run (if h : p ≤ (j : ℕ) ∧ (j : ℕ) + 2 ≤ r then
          qzStep pure r j ⟨(j : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 2, by omega⟩ st
        else pure st)) st) := by
  have key := foldl_induction_getElem (List.finRange n) (fun st (j : Fin n) =>
      Id.run (if h : p ≤ (j : ℕ) ∧ (j : ℕ) + 2 ≤ r then
        qzStep pure r j ⟨(j : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 2, by omega⟩ st
      else pure st))
    (fun t st => QZStepInv A₀ B₀ p r (min (max t p) (r - 1)) x₀ y₀ z₀ st) st
    (by rwa [show min (max 0 p) (r - 1) = p by omega]) fun t ht st hst => ?_
  · rwa [List.length_finRange, show min (max n p) (r - 1) = r - 1 by omega] at key
  · have hjt : ((List.finRange n)[t] : ℕ) = t := by simp
    by_cases hc : p ≤ ((List.finRange n)[t] : ℕ) ∧ ((List.finRange n)[t] : ℕ) + 2 ≤ r
    · simp only [hc, and_self, ↓reduceDIte]
      have := qzStep_inv hr hc.1 hc.2
        (by rwa [show min (max t p) (r - 1) = ((List.finRange n)[t] : ℕ) by omega] at hst)
      rwa [show min (max (t + 1) p) (r - 1) = ((List.finRange n)[t] : ℕ) + 1 by omega]
    · simp only [hc, ↓reduceDIte, Id.run_pure]
      rwa [show min (max (t + 1) p) (r - 1) = min (max t p) (r - 1) by omega]

/-- The state after the loop of Algorithm 7.7.2, in exact arithmetic. -/
private noncomputable def qzLoopState (p : ℕ) {r : ℕ} (hr : r < n)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    QZStepState n :=
  (List.finRange n).foldl (fun st (j : Fin n) =>
    Id.run (if h : p ≤ (j : ℕ) ∧ (j : ℕ) + 2 ≤ r then
      qzStep pure r j ⟨(j : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 2, by omega⟩ st
    else pure st))
    ⟨A, B, [], [], (Id.run (qzShiftVector pure p r A B)).1,
      (Id.run (qzShiftVector pure p r A B)).2.1, (Id.run (qzShiftVector pure p r A B)).2.2⟩

/-- The exact run of Algorithm 7.7.2, unfolded. -/
private theorem algorithm_7_7_2_pure {p r : ℕ} (hpr : p < r) (hr : r < n)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_7_7_2 pure p r A B) =
      let st := qzLoopState p hr A B
      let r₁ : Fin n := ⟨r - 1, by omega⟩
      let r' : Fin n := ⟨r, hr⟩
      let q := Id.run (houseOn pure [r₁, r'] fun i => if i = r₁ then st.x else if i = r' then st.y
        else 0)
      let A₁ := (1 - q.2 • vecMulVec q.1 q.1) * st.A
      let B₁ := (1 - q.2 • vecMulVec q.1 q.1) * st.B
      let z := Id.run (houseOn pure [r', r₁] (B₁ r'))
      ((A₁ * (1 - z.2 • vecMulVec z.1 z.1)), B₁ * (1 - z.2 • vecMulVec z.1 z.1), st.dQ ++ [q],
        st.dZ ++ [z]) := by
  have hr₁r : (⟨r - 1, by omega⟩ : Fin n) ≠ ⟨r, hr⟩ := fun e => by
    have := congrArg Fin.val e; simp at this; omega
  have hnd : [(⟨r - 1, by omega⟩ : Fin n), ⟨r, hr⟩].Nodup := nodup_two (by simp; omega)
  have hnd' : [(⟨r, hr⟩ : Fin n), ⟨r - 1, by omega⟩].Nodup := nodup_two (by simp; omega)
  simp only [algorithm_7_7_2, qzLoopState, hpr, hr, and_self, ↓reduceDIte, Id.run_bind,
    Id.run_pure, List.idRun_foldlM]
  rw [householderApplyLeft_spec_of_forall_mem hnd (List.nodup_finRange n) List.mem_finRange
      (houseOn_spec hnd (List.cons_ne_nil _ _) _).2.1,
    householderApplyLeft_spec_of_forall_mem hnd (List.nodup_finRange n) List.mem_finRange
      (houseOn_spec hnd (List.cons_ne_nil _ _) _).2.1,
    householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd' List.mem_finRange
      (houseOn_spec hnd' (List.cons_ne_nil _ _) _).2.1,
    householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd' List.mem_finRange
      (houseOn_spec hnd' (List.cons_ne_nil _ _) _).2.1]

/-- Algorithm 7.7.2 on a block, in exact arithmetic. Let $p < r < n$, let
$A \in \mathbb{R}^{n \times n}$ be upper Hessenberg with the block $p, \dots, r$ decoupled
($a_{p,p-1} = 0$ if $p > 0$, and $a_{r+1,r} = 0$ if $r + 1 < n$), and let $B$ be upper
triangular. Let $(A', B', d_Q, d_Z)$ be the exact run of the QZ step on the block, and let $Q$
and $Z$ be the products of the reflectors in $d_Q$ and $d_Z$. Then $Q$ and $Z$ are orthogonal,
$A' = Q^T A Z$ is upper Hessenberg, $B' = Q^T B Z$ is upper triangular, and all reflector
vectors vanish outside the block. If the block has at least three indices, then the first left
reflector $(v_0, \beta_0)$ satisfies $\beta_0 = 0$ or $\beta_0 v_0^T v_0 = 2$, it maps the shift
vector, $(x, y, z)$ at the indices $p, p+1, p+2$, to a multiple of $e_p$, and the vectors of the
other left reflectors vanish at $p$.

The products are `GolubVanLoan.Chapter05.householderProduct dQ` and
`GolubVanLoan.Chapter05.householderProduct dZ`, and the shift vector is the exact run of
`GolubVanLoan.Chapter07.qzShiftVector`. -/
theorem algorithm_7_7_2_block {p r : ℕ} (hpr : p < r) (hr : r < n)
    {A B A' B' : Matrix (Fin n) (Fin n) ℝ} {dQ dZ : List ((Fin n → ℝ) × ℝ)}
    (hA : A.IsUpperHessenberg) (hB : B.IsUpperTriangular)
    (hp : 0 < p → qzEntry A p (p - 1) = 0) (hr₁ : qzEntry A (r + 1) r = 0)
    (h : Id.run (algorithm_7_7_2 pure p r A B) = (A', B', dQ, dZ)) :
    householderProduct dQ ∈ orthogonalGroup (Fin n) ℝ ∧
      householderProduct dZ ∈ orthogonalGroup (Fin n) ℝ ∧
      A' = (householderProduct dQ)ᵀ * A * householderProduct dZ ∧
      B' = (householderProduct dQ)ᵀ * B * householderProduct dZ ∧
      A'.IsUpperHessenberg ∧ B'.IsUpperTriangular ∧
      (∀ d ∈ dQ, ∀ l : Fin n, ((l : ℕ) < p ∨ r < l) → d.1 l = 0) ∧
      (∀ d ∈ dZ, ∀ l : Fin n, ((l : ℕ) < p ∨ r < l) → d.1 l = 0) ∧
      (p + 2 ≤ r → ∃ d₀ rest, dQ = d₀ :: rest ∧ (d₀.2 = 0 ∨ d₀.2 * (d₀.1 ⬝ᵥ d₀.1) = 2) ∧
        (∀ l : Fin n, (l : ℕ) ≠ p → ((1 - d₀.2 • vecMulVec d₀.1 d₀.1) *ᵥ fun i : Fin n =>
          if (i : ℕ) = p then (Id.run (qzShiftVector pure p r A B)).1
          else if (i : ℕ) = p + 1 then (Id.run (qzShiftVector pure p r A B)).2.1
          else if (i : ℕ) = p + 2 then (Id.run (qzShiftVector pure p r A B)).2.2 else 0) l = 0) ∧
        ∀ d ∈ rest, ∀ l : Fin n, (l : ℕ) = p → d.1 l = 0) := by
  have hinv : QZStepInv A B p r (r - 1) (Id.run (qzShiftVector pure p r A B)).1
      (Id.run (qzShiftVector pure p r A B)).2.1 (Id.run (qzShiftVector pure p r A B)).2.2
      (qzLoopState p hr A B) :=
    qzLoop_inv hpr hr (qzStepInv_init hr hA hB hp hr₁ _ _ _)
  rw [algorithm_7_7_2_pure hpr hr] at h
  dsimp only at h
  generalize qzLoopState p hr A B = st at hinv h
  set r₁ : Fin n := ⟨r - 1, by omega⟩ with hr₁def
  set r' : Fin n := ⟨r, hr⟩ with hr'def
  have hr₁v : (r₁ : ℕ) = r - 1 := rfl
  have hr'v : (r' : ℕ) = r := rfl
  have hmem : ∀ i : Fin n, i ∈ [r₁, r'] ↔ ((i : ℕ) = r - 1 ∨ (i : ℕ) = r) := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hr₁v, hr'v]
  have hmem' : ∀ i : Fin n, i ∈ [r', r₁] ↔ ((i : ℕ) = r - 1 ∨ (i : ℕ) = r) := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hr₁v, hr'v]
    omega
  have hnd : [r₁, r'].Nodup := nodup_two (by omega)
  have hnd' : [r', r₁].Nodup := nodup_two (by omega)
  obtain ⟨hq0, hqβ, hqz⟩ := houseOn_exact hnd (List.cons_ne_nil _ _) (fun i =>
    if i = r₁ then st.x else if i = r' then st.y else 0)
  set q := Id.run (houseOn pure [r₁, r'] (fun i =>
    if i = r₁ then st.x else if i = r' then st.y else 0)) with hq
  set P₁ : Matrix (Fin n) (Fin n) ℝ := 1 - q.2 • vecMulVec q.1 q.1 with hP₁
  set A₁ := P₁ * st.A with hA₁
  set B₁ := P₁ * st.B with hB₁
  obtain ⟨hz0, hzβ, hzz⟩ := houseOn_exact hnd' (List.cons_ne_nil _ _) (B₁ r')
  set z := Id.run (houseOn pure [r', r₁] (B₁ r')) with hz
  set P₂ : Matrix (Fin n) (Fin n) ℝ := 1 - z.2 • vecMulVec z.1 z.1 with hP₂
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  have hq0' : ∀ l : Fin n, ¬ ((l : ℕ) = r - 1 ∨ (l : ℕ) = r) → q.1 l = 0 :=
    fun l hl => hq0 l ((hmem l).not.2 hl)
  have hz0' : ∀ l : Fin n, ¬ ((l : ℕ) = r - 1 ∨ (l : ℕ) = r) → z.1 l = 0 :=
    fun l hl => hz0 l ((hmem' l).not.2 hl)
  -- `A₁` is upper Hessenberg: the reflector clears the last bulge entry `(r, r - 2)`
  have hA₁z : ∀ i c : Fin n, (c : ℕ) + 1 < i → A₁ i c = 0 := by
    intro i c hic
    by_cases hio : (i : ℕ) = r - 1 ∨ (i : ℕ) = r
    · by_cases hcj : (c : ℕ) + 1 = r - 1
      · by_cases hpj : p < r - 1
        · have hcol : ∀ l ∈ [r₁, r'], st.A l c = (fun i =>
              if i = r₁ then st.x else if i = r' then st.y else 0) l := by
            intro l hl
            obtain ⟨hx, hy, -⟩ := hinv.xyz l c hpj hcj
            rw [hmem] at hl
            rcases hl with hl | hl
            · have : l = r₁ := Fin.ext hl
              subst this
              simp [hx rfl]
            · have : l = r' := Fin.ext hl
              subst this
              have hne : r' ≠ r₁ := fun e => by rw [e] at hr'v; omega
              simp [hne, hy (by omega)]
          rw [hA₁, one_sub_smul_vecMulVec_mul_apply_eq_mulVec hq0 _ _ _ hcol ((hmem i).2 hio)]
          exact hqz i ((hmem i).2 hio) (fun e => by rw [e, List.head_cons] at hic; omega)
        · have hp0 : 0 < p := by omega
          have hcol : ∀ l ∈ [r₁, r'], st.A l c = 0 := fun l hl => by
            rw [hmem] at hl
            exact hinv.col l c hp0 (by omega) (by omega)
          rw [hA₁, one_sub_smul_vecMulVec_mul_apply_of_forall hq0 _ _ hcol]
          exact hinv.col i c hp0 (by omega) (by omega)
      · have hcol : ∀ l ∈ [r₁, r'], st.A l c = 0 := fun l hl => by
          rw [hmem] at hl
          exact hinv.bulge l c (by omega) (by omega)
        rw [hA₁, one_sub_smul_vecMulVec_mul_apply_of_forall hq0 _ _ hcol]
        exact hinv.bulge i c hic (by omega)
    · rw [hA₁, one_sub_smul_vecMulVec_mul_apply_of_notMem hq0 _ _ ((hmem i).not.2 hio)]
      by_cases hir : (i : ℕ) = r + 1
      · exact hinv.row i c hir (by omega)
      · exact hinv.bulge i c hic (by omega)
  -- `B₁`: upper triangular except at `(r, r - 1)`
  have hB₁z : ∀ i c : Fin n, (c : ℕ) < i → ¬ ((i : ℕ) = r ∧ (c : ℕ) = r - 1) → B₁ i c = 0 := by
    intro i c hic hne
    by_cases hio : (i : ℕ) = r - 1 ∨ (i : ℕ) = r
    · have hcol : ∀ l ∈ [r₁, r'], st.B l c = 0 := fun l hl => by
        rw [hmem] at hl
        exact hinv.tri l c (by omega)
      rw [hB₁, one_sub_smul_vecMulVec_mul_apply_of_forall hq0 _ _ hcol]
      exact hinv.tri i c hic
    · rw [hB₁, one_sub_smul_vecMulVec_mul_apply_of_notMem hq0 _ _ ((hmem i).not.2 hio)]
      exact hinv.tri i c hic
  have hsym : ∀ d : (Fin n → ℝ) × ℝ,
      (1 - d.2 • vecMulVec d.1 d.1)ᵀ = 1 - d.2 • vecMulVec d.1 d.1 :=
    fun d => transpose_one_sub_smul_vecMulVec _ _
  have hβQ : ∀ d ∈ st.dQ ++ [q], d.2 = 0 ∨ d.2 * (d.1 ⬝ᵥ d.1) = 2 := by
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hinv.betaQ d hd
    · rw [List.mem_singleton.1 hd]; exact hqβ
  have hβZ : ∀ d ∈ st.dZ ++ [z], d.2 = 0 ∨ d.2 * (d.1 ⬝ᵥ d.1) = 2 := by
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hinv.betaZ d hd
    · rw [List.mem_singleton.1 hd]; exact hzβ
  refine ⟨householderProduct_mem_orthogonalGroup hβQ, householderProduct_mem_orthogonalGroup hβZ,
    ?_, ?_, ?_, ?_, ?_, ?_, fun hpr2 => ?_⟩
  · rw [householderProduct_concat, householderProduct_concat, transpose_mul, hsym, hA₁,
      hinv.eqA]
    simp only [hP₁, hP₂, Matrix.mul_assoc]
  · rw [householderProduct_concat, householderProduct_concat, transpose_mul, hsym, hB₁,
      hinv.eqB]
    simp only [hP₁, hP₂, Matrix.mul_assoc]
  · -- `A₁ P₂` is upper Hessenberg
    rw [isUpperHessenberg_iff_fin]
    intro i c hic
    by_cases hco : (c : ℕ) = r - 1 ∨ (c : ℕ) = r
    · have hrow : ∀ l ∈ [r', r₁], A₁ i l = 0 := fun l hl => by
        rw [hmem'] at hl
        by_cases hi : (i : ℕ) = r + 1 ∧ (l : ℕ) = r
        · rw [hA₁, one_sub_smul_vecMulVec_mul_apply_of_notMem hq0 _ _ ((hmem i).not.2 (by omega))]
          exact hinv.row i l hi.1 (by omega)
        · exact hA₁z i l (by omega)
      rw [mul_one_sub_smul_vecMulVec_apply_of_forall hz0 _ _ hrow]
      exact hA₁z i c hic
    · rw [mul_one_sub_smul_vecMulVec_apply_of_notMem hz0 _ _ _ ((hmem' c).not.2 hco)]
      exact hA₁z i c hic
  · -- `B₁ P₂` is upper triangular
    rw [isUpperTriangular_iff_fin]
    intro i c hic
    by_cases hco : (c : ℕ) = r - 1 ∨ (c : ℕ) = r
    · by_cases hi : (i : ℕ) = r
      · have hi' : i = r' := Fin.ext hi
        subst hi'
        rw [mul_one_sub_smul_vecMulVec_apply_eq_mulVec]
        exact hzz c ((hmem' c).2 hco) (fun e => by rw [e, List.head_cons] at hic; omega)
      · have hrow : ∀ l ∈ [r', r₁], B₁ i l = 0 := fun l hl => by
          rw [hmem'] at hl
          exact hB₁z i l (by omega) (by omega)
        rw [mul_one_sub_smul_vecMulVec_apply_of_forall hz0 _ _ hrow]
        exact hB₁z i c hic (by omega)
    · rw [mul_one_sub_smul_vecMulVec_apply_of_notMem hz0 _ _ _ ((hmem' c).not.2 hco)]
      exact hB₁z i c hic (by omega)
  · intro d hd l hl
    rcases List.mem_append.1 hd with hd | hd
    · exact hinv.suppQ d hd l hl
    · rw [List.mem_singleton.1 hd]; exact hq0' l (by omega)
  · intro d hd l hl
    rcases List.mem_append.1 hd with hd | hd
    · exact hinv.suppZ d hd l hl
    · rw [List.mem_singleton.1 hd]; exact hz0' l (by omega)
  · obtain ⟨d₀, rest, hdQ, hd₀, hrest⟩ := hinv.first (by omega)
    refine ⟨d₀, rest ++ [q], by rw [hdQ]; rfl, hinv.betaQ d₀ (by rw [hdQ]; exact
      List.mem_cons_self), hd₀, fun d hd l hl => ?_⟩
    rcases List.mem_append.1 hd with hd | hd
    · exact hrest d hd l hl
    · rw [List.mem_singleton.1 hd]; exact hq0' l (by omega)

end QZStepSpec

/-! ### Algorithm 7.7.2 performs a Francis step on $AB^{-1}$ -/

section QZFrancis

open GolubVanLoan.Chapter05

/-- The entries of the product of an upper Hessenberg matrix $M$ and an upper triangular matrix $B$:
$(MB)_{ic} = \sum_{i - 1 \le k \le c} m_{ik} b_{kc}$. -/
private theorem hess_mul_tri_apply {M B : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsUpperHessenberg)
    (hB : B.IsUpperTriangular) (i c : Fin n) :
    (M * B) i c =
      ∑ k : Fin n, if (i : ℕ) ≤ (k : ℕ) + 1 ∧ (k : ℕ) ≤ c then M i k * B k c else 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rfl
  · rcases not_and_or.1 h with h | h
    · rw [isUpperHessenberg_iff_fin.1 hM i k (by omega), zero_mul]
    · rw [isUpperTriangular_iff_fin.1 hB k c (by omega), mul_zero]

/-- A sum with exactly one selected term is that term. -/
private theorem sum_ite_one {f : Fin n → ℝ} {P : Fin n → Prop} [DecidablePred P] (a : Fin n)
    (hP : ∀ k, P k ↔ k = a) : (∑ k, if P k then f k else 0) = f a := by
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [ite_eq_right ((hP b).not.2 hb)])
    (fun h => absurd (Finset.mem_univ a) h), ite_eq_left ((hP a).2 rfl)]

/-- A sum with exactly two selected terms is their sum. -/
private theorem sum_ite_two {f : Fin n → ℝ} {P : Fin n → Prop} [DecidablePred P] {a b : Fin n}
    (hab : a ≠ b) (hP : ∀ k, P k ↔ k = a ∨ k = b) :
    (∑ k, if P k then f k else 0) = f a + f b := by
  rw [Fintype.sum_eq_add a b hab (fun x hx => ite_eq_right ((hP x).not.2 (by tauto))),
    ite_eq_left ((hP a).2 (Or.inl rfl)), ite_eq_left ((hP b).2 (Or.inr rfl))]

/-- A sum with exactly three selected terms is their sum. -/
private theorem sum_ite_three {f : Fin n → ℝ} {P : Fin n → Prop} [DecidablePred P]
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : ∀ k, P k ↔ k = a ∨ k = b ∨ k = c) :
    (∑ k, if P k then f k else 0) = f a + f b + f c := by
  rw [← Finset.sum_subset (Finset.subset_univ {a, b, c}) (fun x _ hx => by
      rw [ite_eq_right ((hP x).not.2 (by simpa using hx))]),
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, ite_eq_left ((hP a).2 (by simp)),
    ite_eq_left ((hP b).2 (by simp)), ite_eq_left ((hP c).2 (by simp)), add_assoc]

variable {N : ℕ}

/-- The shift vector of the QZ step is the first column of $(M - aI)(M - bI)$ for $M = AB^{-1}$,
where $a + b$ and $ab$ are the trace and the determinant of the trailing $2 \times 2$ block of
$M$: the forward substitutions of `GolubVanLoan.Chapter07.qzShiftVector` compute the entries of
$M$ that it needs. -/
private theorem qzShiftVector_full {A B M : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    (hA : A.IsUpperHessenberg) (hB : B.IsUpperTriangular) (hBd : ∀ i, B i i ≠ 0)
    (hMdef : M = A * B⁻¹) :
    Id.run (qzShiftVector pure 0 (N + 2) A B) =
      (M ⟨0, by omega⟩ ⟨0, by omega⟩ * M ⟨0, by omega⟩ ⟨0, by omega⟩ +
          M ⟨0, by omega⟩ ⟨1, by omega⟩ * M ⟨1, by omega⟩ ⟨0, by omega⟩ -
          (M ⟨N + 1, by omega⟩ ⟨N + 1, by omega⟩ + M ⟨N + 2, by omega⟩ ⟨N + 2, by omega⟩) *
            M ⟨0, by omega⟩ ⟨0, by omega⟩ +
          (M ⟨N + 1, by omega⟩ ⟨N + 1, by omega⟩ * M ⟨N + 2, by omega⟩ ⟨N + 2, by omega⟩ -
            M ⟨N + 1, by omega⟩ ⟨N + 2, by omega⟩ * M ⟨N + 2, by omega⟩ ⟨N + 1, by omega⟩),
        M ⟨1, by omega⟩ ⟨0, by omega⟩ * (M ⟨0, by omega⟩ ⟨0, by omega⟩ +
          M ⟨1, by omega⟩ ⟨1, by omega⟩ -
          (M ⟨N + 1, by omega⟩ ⟨N + 1, by omega⟩ + M ⟨N + 2, by omega⟩ ⟨N + 2, by omega⟩)),
        M ⟨1, by omega⟩ ⟨0, by omega⟩ * M ⟨2, by omega⟩ ⟨1, by omega⟩) := by
  have hdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => hBd i
  have hM : M.IsUpperHessenberg := hMdef ▸ hA.mul_isUpperTriangular hB.inv
  have hMB : M * B = A := by
    rw [hMdef, Matrix.mul_assoc, nonsing_inv_mul B hdet, Matrix.mul_one]
  have hent : ∀ i c : Fin (N + 3),
      A i c = ∑ k : Fin (N + 3),
        if (i : ℕ) ≤ (k : ℕ) + 1 ∧ (k : ℕ) ≤ c then M i k * B k c else 0 := fun i c => by
    rw [← hess_mul_tri_apply hM hB, hMB]
  -- the index names
  set i0 : Fin (N + 3) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (N + 3) := ⟨1, by omega⟩ with hi1
  set i2 : Fin (N + 3) := ⟨2, by omega⟩ with hi2
  set ia : Fin (N + 3) := ⟨N, by omega⟩ with hia
  set ib : Fin (N + 3) := ⟨N + 1, by omega⟩ with hib
  set ic : Fin (N + 3) := ⟨N + 2, by omega⟩ with hic
  have v0 : (i0 : ℕ) = 0 := rfl
  have v1 : (i1 : ℕ) = 1 := rfl
  have v2 : (i2 : ℕ) = 2 := rfl
  have va : (ia : ℕ) = N := rfl
  have vb : (ib : ℕ) = N + 1 := rfl
  have vc : (ic : ℕ) = N + 2 := rfl
  have n01 : i0 ≠ i1 := fun e => by have := congrArg Fin.val e; omega
  have nab : ia ≠ ib := fun e => by have := congrArg Fin.val e; omega
  have nac : ia ≠ ic := fun e => by have := congrArg Fin.val e; omega
  have nbc : ib ≠ ic := fun e => by have := congrArg Fin.val e; omega
  -- `a = m b` entry by entry
  have e00 : A i0 i0 = M i0 i0 * B i0 i0 := by
    rw [hent, sum_ite_one i0 fun k => by simp only [Fin.ext_iff, v0]; omega]
  have e10 : A i1 i0 = M i1 i0 * B i0 i0 := by
    rw [hent, sum_ite_one i0 fun k => by simp only [Fin.ext_iff, v0, v1]; omega]
  have e01 : A i0 i1 = M i0 i0 * B i0 i1 + M i0 i1 * B i1 i1 := by
    rw [hent, sum_ite_two n01 fun k => by simp only [Fin.ext_iff, v0, v1]; omega]
  have e11 : A i1 i1 = M i1 i0 * B i0 i1 + M i1 i1 * B i1 i1 := by
    rw [hent, sum_ite_two n01 fun k => by simp only [Fin.ext_iff, v0, v1]; omega]
  have e21 : A i2 i1 = M i2 i1 * B i1 i1 := by
    rw [hent, sum_ite_one i1 fun k => by simp only [Fin.ext_iff, v1, v2]; omega]
  have eba : A ib ia = M ib ia * B ia ia := by
    rw [hent, sum_ite_one ia fun k => by simp only [Fin.ext_iff, va, vb]; omega]
  have ebb : A ib ib = M ib ia * B ia ib + M ib ib * B ib ib := by
    rw [hent, sum_ite_two nab fun k => by simp only [Fin.ext_iff, va, vb]; omega]
  have ebc : A ib ic = M ib ia * B ia ic + M ib ib * B ib ic + M ib ic * B ic ic := by
    rw [hent, sum_ite_three nab nac nbc fun k => by simp only [Fin.ext_iff, va, vb, vc]; omega]
  have ecb : A ic ib = M ic ib * B ib ib := by
    rw [hent, sum_ite_one ib fun k => by simp only [Fin.ext_iff, vb, vc]; omega]
  have ecc : A ic ic = M ic ib * B ib ic + M ic ic * B ic ic := by
    rw [hent, sum_ite_two nbc fun k => by simp only [Fin.ext_iff, vb, vc]; omega]
  have hd : ∀ {a b c : ℝ}, b ≠ 0 → a = c * b → a / b = c := fun hb h => by
    rw [h, mul_div_cancel_right₀ _ hb]
  have m00 : A i0 i0 / B i0 i0 = M i0 i0 := hd (hBd _) e00
  have m10 : A i1 i0 / B i0 i0 = M i1 i0 := hd (hBd _) e10
  have m01 : (A i0 i1 - M i0 i0 * B i0 i1) / B i1 i1 = M i0 i1 := hd (hBd _) (by rw [e01]; ring)
  have m11 : (A i1 i1 - M i1 i0 * B i0 i1) / B i1 i1 = M i1 i1 := hd (hBd _) (by rw [e11]; ring)
  have m21 : A i2 i1 / B i1 i1 = M i2 i1 := hd (hBd _) e21
  have mba : A ib ia / B ia ia = M ib ia := hd (hBd _) eba
  have mbb : (A ib ib - M ib ia * B ia ib) / B ib ib = M ib ib := hd (hBd _) (by rw [ebb]; ring)
  have mbc : (A ib ic - M ib ia * B ia ic - M ib ib * B ib ic) / B ic ic = M ib ic :=
    hd (hBd _) (by rw [ebc]; ring)
  have mcb : A ic ib / B ib ib = M ic ib := hd (hBd _) ecb
  have mcc : (A ic ic - M ic ib * B ib ic) / B ic ic = M ic ic := hd (hBd _) (by rw [ecc]; ring)
  have hrun : Id.run (qzShiftVector pure 0 (N + 2) A B) =
      (let m₁₁ := A i0 i0 / B i0 i0
       let m₂₁ := A i1 i0 / B i0 i0
       let m₁₂ := (A i0 i1 - m₁₁ * B i0 i1) / B i1 i1
       let m₂₂ := (A i1 i1 - m₂₁ * B i0 i1) / B i1 i1
       let μ := A ib ia / B ia ia
       let e := (A ib ib - μ * B ia ib) / B ib ib
       let f := (A ib ic - μ * B ia ic - e * B ib ic) / B ic ic
       let g := A ic ib / B ib ib
       let h := (A ic ic - g * B ib ic) / B ic ic
       (m₁₁ * m₁₁ + m₁₂ * m₂₁ - (e + h) * m₁₁ + (e * h - f * g),
         m₂₁ * (m₁₁ + m₂₂ - (e + h)), m₂₁ * (A i2 i1 / B i1 i1))) := by
    simp only [qzShiftVector, Id.run_bind, Id.run_pure, show 0 + 2 ≤ N + 2 by omega,
      ↓reduceIte]
    simp (disch := omega) only [qzEntry_of_lt]
    rfl
  rw [hrun]
  dsimp only
  rw [m00, m10, m01, m11, m21, mba, mbb, mbc, mcb, mcc]

/-- A two-sided orthogonal equivalence of a pencil is a similarity of $AB^{-1}$. Let
$A, B, Q, Z \in \mathbb{R}^{k \times k}$ with $Q$ and $Z$ orthogonal and $B$ nonsingular. Then
$$(Q^T A Z)(Q^T B Z)^{-1} = Q^T (AB^{-1}) Q.$$

**Typo.** The source prints $AB^{-1}$ as the left side after updating both matrices. The left
side here uses the transformed pair and equals the similarity of the original product. -/
theorem transpose_mul_mul_mul_inv {k : ℕ} {A B Q Z : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin k) ℝ) (hZ : Z ∈ orthogonalGroup (Fin k) ℝ)
    (hB : IsUnit B.det) : Qᵀ * A * Z * (Qᵀ * B * Z)⁻¹ = Qᵀ * (A * B⁻¹) * Q := by
  have hZZ : Z * Zᵀ = 1 := (mem_orthogonalGroup_iff (Fin k) ℝ).1 hZ
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff (Fin k) ℝ).1 hQ
  have hinv : (Qᵀ * B * Z)⁻¹ = Zᵀ * B⁻¹ * Q := by
    refine Matrix.inv_eq_left_inv ?_
    rw [show Zᵀ * B⁻¹ * Q * (Qᵀ * B * Z) = Zᵀ * (B⁻¹ * ((Q * Qᵀ) * B)) * Z by
      simp only [Matrix.mul_assoc], hQQ, Matrix.one_mul, nonsing_inv_mul B hB, Matrix.mul_one,
      (mem_orthogonalGroup_iff' (Fin k) ℝ).1 hZ]
  rw [hinv, show Qᵀ * A * Z * (Zᵀ * B⁻¹ * Q) = Qᵀ * A * (Z * Zᵀ) * B⁻¹ * Q by
    simp only [Matrix.mul_assoc], hZZ, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- An upper triangular matrix with nonzero diagonal entries is nonsingular. -/
private theorem isUnit_det_of_diag {k : ℕ} {B : Matrix (Fin k) (Fin k) ℝ}
    (hB : B.IsUpperTriangular) (hBd : ∀ i, B i i ≠ 0) : IsUnit B.det := by
  rw [det_of_isUpperTriangular hB, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun i _ => hBd i

/-- The QZ step is a Francis step on $AB^{-1}$ ([golub2013matrix] §7.7.6: "$\bar A \bar B^{-1}$ is
essentially the same matrix that would result if a Francis QR step were explicitly applied to
$AB^{-1}$"). Let $n \ge 3$, let $A \in \mathbb{R}^{n \times n}$ be unreduced upper Hessenberg,
let $B$ be upper triangular with nonzero diagonal entries, and let $M = AB^{-1}$, with $s$ and
$t$ the trace and the determinant of its trailing $2 \times 2$ block. Let $Q$ and $Z$ be
orthogonal with $Q^T A Z$ upper Hessenberg and $Q^T B Z$ upper triangular. Let $P$ satisfy
$P^2 = I$ and $Q e_1 = P e_1$, and let $P$ map the first column of $M^2 - sM + tI$ to a multiple
of $e_1$. Then $(Q^T A Z)(Q^T B Z)^{-1} = Q^T M Q$, the matrix $Q^T (M^2 - sM + tI)$ is upper
triangular, and $(Q^T A Z)(Q^T B Z)^{-1}$ is a Francis step of $M$ with the shifts $s, t$
(`Matrix.IsFrancisStep`).

The proof applies `GolubVanLoan.Chapter07.isFrancisStep_of_first_reflector`. The matrix $M$ is
unreduced since $m_{k+1,k} b_{kk} = a_{k+1,k}$. -/
theorem isFrancisStep_of_qz {N : ℕ} {A B Q Z P : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    (hA : IsUnreduced A) (hB : B.IsUpperTriangular) (hBd : ∀ i, B i i ≠ 0)
    (hQ : Q ∈ orthogonalGroup (Fin (N + 3)) ℝ) (hZ : Z ∈ orthogonalGroup (Fin (N + 3)) ℝ)
    (hA' : (Qᵀ * A * Z).IsUpperHessenberg) (hB' : (Qᵀ * B * Z).IsUpperTriangular)
    (hP : P * P = 1) (hQP : Q *ᵥ Pi.single 0 1 = P *ᵥ Pi.single 0 1)
    (hPu : ∀ i, i ≠ 0 → (P *ᵥ (A * B⁻¹ * (A * B⁻¹) - trailingTrace (A * B⁻¹) • (A * B⁻¹) +
      trailingDet (A * B⁻¹) • 1).col 0) i = 0) :
    Qᵀ * A * Z * (Qᵀ * B * Z)⁻¹ = Qᵀ * (A * B⁻¹) * Q ∧
      (Qᵀ * (A * B⁻¹ * (A * B⁻¹) - trailingTrace (A * B⁻¹) • (A * B⁻¹) +
        trailingDet (A * B⁻¹) • 1)).IsUpperTriangular ∧
      IsFrancisStep (trailingTrace (A * B⁻¹)) (trailingDet (A * B⁻¹)) (A * B⁻¹)
        (Qᵀ * A * Z * (Qᵀ * B * Z)⁻¹) := by
  have hdet := isUnit_det_of_diag hB hBd
  have hMQ := transpose_mul_mul_mul_inv (A := A) hQ hZ hdet
  have hMH : (A * B⁻¹).IsUpperHessenberg := hA.1.mul_isUpperTriangular hB.inv
  have hGH : (Qᵀ * (A * B⁻¹) * Q).IsUpperHessenberg := by
    rw [← hMQ]
    exact hA'.mul_isUpperTriangular hB'.inv
  have hMB : A * B⁻¹ * B = A := by
    rw [Matrix.mul_assoc, nonsing_inv_mul B hdet, Matrix.mul_one]
  have hMU : IsUnreduced (A * B⁻¹) := by
    refine isUnreducedUpperHessenberg_iff_fin.2 ⟨hMH, fun k hk hM0 => ?_⟩
    refine (isUnreduced_iff.1 hA).2 k hk ?_
    rw [← hMB, hess_mul_tri_apply hMH hB,
      sum_ite_one ⟨k, by omega⟩ fun j => by simp [Fin.ext_iff]; omega, hM0, zero_mul]
  obtain ⟨htri, -, hF⟩ := isFrancisStep_of_first_reflector hMU hQ hGH hP hQP hPu
  refine ⟨hMQ, htri, ?_⟩
  rw [hMQ]
  exact hF

/-- The shift vector of the QZ step on the whole pencil is the first column of
$(M - a_1 I)(M - a_2 I)$, $M = AB^{-1}$. -/
private theorem qzShift_col {A B : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    (hA : A.IsUpperHessenberg) (hB : B.IsUpperTriangular) (hBd : ∀ i, B i i ≠ 0) :
    (A * B⁻¹ * (A * B⁻¹) - trailingTrace (A * B⁻¹) • (A * B⁻¹) +
      trailingDet (A * B⁻¹) • 1).col 0 = fun i : Fin (N + 3) =>
        if (i : ℕ) = 0 then (Id.run (qzShiftVector pure 0 (N + 2) A B)).1
        else if (i : ℕ) = 1 then (Id.run (qzShiftVector pure 0 (N + 2) A B)).2.1
        else if (i : ℕ) = 2 then (Id.run (qzShiftVector pure 0 (N + 2) A B)).2.2 else 0 := by
  set M := A * B⁻¹ with hMdef
  have hMH : M.IsUpperHessenberg := hA.mul_isUpperTriangular hB.inv
  have hsv := qzShiftVector_full hA hB hBd (M := M) rfl
  set s := trailingTrace M with hs
  set t := trailingDet M with ht
  have hs' : s = M ⟨N + 1, by omega⟩ ⟨N + 1, by omega⟩ + M ⟨N + 2, by omega⟩ ⟨N + 2, by omega⟩ :=
    rfl
  have ht' : t = M ⟨N + 1, by omega⟩ ⟨N + 1, by omega⟩ * M ⟨N + 2, by omega⟩ ⟨N + 2, by omega⟩ -
      M ⟨N + 1, by omega⟩ ⟨N + 2, by omega⟩ * M ⟨N + 2, by omega⟩ ⟨N + 1, by omega⟩ := rfl
  rw [← hs', ← ht'] at hsv
  set i0 : Fin (N + 3) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (N + 3) := ⟨1, by omega⟩ with hi1
  set i2 : Fin (N + 3) := ⟨2, by omega⟩ with hi2
  have v0 : (i0 : ℕ) = 0 := rfl
  have v1 : (i1 : ℕ) = 1 := rfl
  have v2 : (i2 : ℕ) = 2 := rfl
  have hMM : ∀ i, (M * M) i i0 = M i i0 * M i0 i0 + M i i1 * M i1 i0 := fun i => by
    rw [Matrix.mul_apply, Fintype.sum_eq_add i0 i1
      (fun e => by have := congrArg Fin.val e; rw [v0, v1] at this; omega) fun k hk => by
        have a : (k : ℕ) ≠ 0 := fun e => hk.1 (Fin.ext e)
        have b : (k : ℕ) ≠ 1 := fun e => hk.2 (Fin.ext e)
        rw [isUpperHessenberg_iff_fin.1 hMH k i0 (by rw [v0]; omega), mul_zero]]
  have hPcol : ∀ i, (M * M - s • M + t • 1) i i0 = M i i0 * M i0 i0 + M i i1 * M i1 i0 -
      s * M i i0 + t * (1 : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ) i i0 := fun i => by
    rw [Matrix.add_apply, Matrix.sub_apply, hMM, Matrix.smul_apply, Matrix.smul_apply,
      smul_eq_mul, smul_eq_mul]
  have hi00 : (0 : Fin (N + 3)) = i0 := Fin.ext rfl
  funext i
  rw [col_apply, hi00, hPcol, hsv]
  dsimp only
  by_cases h0 : (i : ℕ) = 0
  · have : i = i0 := Fin.ext h0
    subst this
    rw [ite_eq_left v0, one_apply_eq]
    ring
  have hne0 : i ≠ i0 := fun e => h0 (by rw [e])
  rw [ite_eq_right h0, one_apply_ne hne0, mul_zero, add_zero]
  by_cases h1 : (i : ℕ) = 1
  · have : i = i1 := Fin.ext h1
    subst this
    rw [ite_eq_left v1]
    ring
  rw [ite_eq_right h1]
  have hi0' : M i i0 = 0 := isUpperHessenberg_iff_fin.1 hMH i i0 (by rw [v0]; omega)
  by_cases h2 : (i : ℕ) = 2
  · have : i = i2 := Fin.ext h2
    subst this
    rw [ite_eq_left v2, hi0']
    ring
  · have hi1' : M i i1 = 0 := isUpperHessenberg_iff_fin.1 hMH i i1 (by rw [v1]; omega)
    rw [ite_eq_right h2, hi0', hi1']
    ring

/-- **Algorithm 7.7.2** of [golub2013matrix], exact semantics. Let $n \ge 3$, let
$A \in \mathbb{R}^{n \times n}$ be unreduced upper Hessenberg, and let
$B \in \mathbb{R}^{n \times n}$ be upper triangular with nonzero diagonal entries. Let
$M = AB^{-1}$, and let $s$ and $t$ be the trace and the determinant of the trailing $2 \times 2$
block of $M$. Let $(A', B', d_Q, d_Z)$ be the exact run of the QZ step on the whole pencil, and
let $Q$ and $Z$ be the products of the reflectors in $d_Q$ and $d_Z$. Then $Q$ and $Z$ are
orthogonal, $$A' = Q^T A Z, \qquad B' = Q^T B Z,$$ $A'$ is upper Hessenberg, $B'$ is upper
triangular, $A' B'^{-1} = Q^T M Q$, and $A' B'^{-1}$ is a Francis step of $M$ with the shifts
$s, t$.

This is the source's claim that "$Q$ has the same first column as the orthogonal similarity
transformation in Algorithm 7.5.1 when it is applied to $AB^{-1}$", and that
"$\bar A \bar B^{-1}$ is essentially the same matrix that would result if a Francis QR step were
explicitly applied to $AB^{-1}$". Since $Q e_1$ is parallel to $(M - aI)(M - bI) e_1$, the
matrix $Q^T (M - aI)(M - bI)$ is upper triangular by the implicit Q theorem
(`Matrix.IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval`). Here $n = N + 3$, the
run is on the block $p = 0$, $r = N + 2$, and a Francis step is `Matrix.IsFrancisStep`.

**Typo.** In the discussion before Algorithm 7.7.2, the left side of the similarity relation
should be the updated product $\bar A\bar B^{-1}$. The source prints the original $AB^{-1}$ on
both sides.  **Reading.** The exact theorem proves the Francis-step relation for a full window
of order at least three; it states the implicit polynomial-factorization condition rather than
equality of first columns of two particular programs. -/
theorem algorithm_7_7_2_spec {N : ℕ} {A B A' B' : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    {dQ dZ : List ((Fin (N + 3) → ℝ) × ℝ)} (hA : IsUnreduced A) (hB : B.IsUpperTriangular)
    (hBd : ∀ i, B i i ≠ 0) (h : Id.run (algorithm_7_7_2 pure 0 (N + 2) A B) = (A', B', dQ, dZ)) :
    let M := A * B⁻¹
    let s := M (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc +
      M (Fin.last (N + 2)) (Fin.last (N + 2))
    let t := M (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc *
        M (Fin.last (N + 2)) (Fin.last (N + 2)) -
      M (Fin.last (N + 1)).castSucc (Fin.last (N + 2)) *
        M (Fin.last (N + 2)) (Fin.last (N + 1)).castSucc
    householderProduct dQ ∈ orthogonalGroup (Fin (N + 3)) ℝ ∧
      householderProduct dZ ∈ orthogonalGroup (Fin (N + 3)) ℝ ∧
      A' = (householderProduct dQ)ᵀ * A * householderProduct dZ ∧
      B' = (householderProduct dQ)ᵀ * B * householderProduct dZ ∧
      A'.IsUpperHessenberg ∧ B'.IsUpperTriangular ∧
      A' * B'⁻¹ = (householderProduct dQ)ᵀ * M * householderProduct dQ ∧
      IsFrancisStep s t M (A' * B'⁻¹) := by
  intro M s t
  obtain ⟨hQo, hZo, hA', hB', hA'H, hB'T, -, -, hfirst⟩ := algorithm_7_7_2_block (by omega)
    (by omega) hA.1 hB (fun h => absurd h (lt_irrefl 0)) (qzEntry_of_not_lt A (by omega)) h
  obtain ⟨d₀, rest, hdQ, hβ₀, hPu₀, hrest⟩ := hfirst (by omega)
  subst hA' hB'
  set P₀ := 1 - d₀.2 • vecMulVec d₀.1 d₀.1 with hP₀
  have hQP : householderProduct dQ *ᵥ Pi.single 0 1 = P₀ *ᵥ Pi.single 0 1 := by
    rw [hdQ, householderProduct_cons, ← mulVec_mulVec,
      householderProduct_mulVec_single fun q hq => hrest q hq 0 rfl]
  have hPP : P₀ * P₀ = 1 := by
    refine one_sub_smul_vecMulVec_mul_self_eq_one
      (one_sub_smul_vecMulVec_mem_orthogonalGroup ?_)
    rcases hβ₀ with hb | hb
    · rw [hb, zero_mul]
    · rw [hb, sub_self, mul_zero]
  simp only [Nat.zero_add] at hPu₀
  obtain ⟨hMQ, -, hF⟩ := isFrancisStep_of_qz hA hB hBd hQo hZo hA'H hB'T hPP hQP fun i hi => by
    rw [qzShift_col hA.1 hB hBd]
    exact hPu₀ i fun e => hi (Fin.ext e)
  exact ⟨hQo, hZo, rfl, rfl, hA'H, hB'T, hMQ, hF⟩

/-- `GolubVanLoan.Chapter07.qzEntry` of the diagonal block on the window $[p, p + k)$ at the indices
$i, j < k$ is `GolubVanLoan.Chapter07.qzEntry` of the matrix at $p + i, p + j$. -/
theorem qzEntry_windowBlock {p k : ℕ} (h : p + k ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) {i j : ℕ}
    (hi : i < k) (hj : j < k) : qzEntry (windowBlock p h A) i j = qzEntry A (p + i) (p + j) := by
  rw [qzEntry_of_lt _ hi hj, qzEntry_of_lt _ (by omega) (by omega)]
  rfl

/-- The shift vector of the QZ step on the block $p, \dots, p + N + 2$ is the shift vector of the
diagonal blocks on that window. -/
private theorem qzShiftVector_windowBlock {p : ℕ} (h : p + (N + 3) ≤ n)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (qzShiftVector pure p (p + (N + 2)) A B) =
      Id.run (qzShiftVector pure 0 (N + 2) (windowBlock p h A) (windowBlock p h B)) := by
  simp only [qzShiftVector, Id.run_bind, Id.run_pure, show p + 2 ≤ p + (N + 2) by omega,
    show 0 + 2 ≤ N + 2 by omega, ↓reduceIte]
  simp (disch := omega) only [qzEntry_windowBlock]
  simp only [show p + (N + 2) - 1 = p + (N + 2 - 1) by omega,
    show p + (N + 2) - 2 = p + (N + 2 - 2) by omega, Nat.add_zero, Nat.zero_add]

/-- A QZ step on the window $[p, p + N + 3)$, the loop body of Algorithm 7.7.3 of [golub2013matrix]
("apply Algorithm 7.7.2 to $A_{22}$ and $B_{22}$"). Let $A_{22}$, $B_{22}$, $Q_{22}$ and
$Z_{22}$ be the diagonal blocks of $A$, $B$, $Q$ and $Z$ on the window, let
$M = A_{22} B_{22}^{-1}$, and let $s$ and $t$ be the trace and the determinant of the trailing
$2 \times 2$ block of $M$. The pair $(Q, Z)$ is a **QZ step on the window** if $Q$ and $Z$ are
orthogonal and equal to the identity outside the window, $Q_{22}^T A_{22} Z_{22}$ is upper
Hessenberg, $Q_{22}^T B_{22} Z_{22}$ is upper triangular, and $Q_{22}^T (M^2 - sM + tI)$ is
upper triangular.

If $B_{22}$ is upper triangular with nonzero diagonal entries, then the new $A_{22} B_{22}^{-1}$
is a Francis step of $M$ (`GolubVanLoan.Chapter07.IsQZStepOn.isFrancisStep`). The diagonal
blocks are `GolubVanLoan.Chapter07.windowBlock`, and "equal to the identity outside the window"
is `GolubVanLoan.Chapter07.IsBlockSupported`. -/
def IsQZStepOn (p N : ℕ) (h : p + (N + 3) ≤ n) (A B Q Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Q ∈ orthogonalGroup (Fin n) ℝ ∧ Z ∈ orthogonalGroup (Fin n) ℝ ∧
    IsBlockSupported p (p + (N + 3)) Q ∧ IsBlockSupported p (p + (N + 3)) Z ∧
    ((windowBlock p h Q)ᵀ * windowBlock p h A * windowBlock p h Z).IsUpperHessenberg ∧
    ((windowBlock p h Q)ᵀ * windowBlock p h B * windowBlock p h Z).IsUpperTriangular ∧
    ((windowBlock p h Q)ᵀ * (windowBlock p h A * (windowBlock p h B)⁻¹ *
      (windowBlock p h A * (windowBlock p h B)⁻¹) -
      trailingTrace (windowBlock p h A * (windowBlock p h B)⁻¹) •
        (windowBlock p h A * (windowBlock p h B)⁻¹) +
      trailingDet (windowBlock p h A * (windowBlock p h B)⁻¹) • 1)).IsUpperTriangular

/-- Let $(Q, Z)$ be a QZ step on the window $[p, p + N + 3)$ for $(A, B)$, and let $B_{22}$ be upper
triangular with nonzero diagonal entries. Let $M = A_{22} B_{22}^{-1}$. Then the new window
blocks satisfy $$(Q^T A Z)_{22} \, ((Q^T B Z)_{22})^{-1} = Q_{22}^T M Q_{22},$$ and this matrix
is a Francis step of $M$ (`Matrix.IsFrancisStep`) with the trace and the determinant of the
trailing $2 \times 2$ block of $M$ as shifts. -/
theorem IsQZStepOn.isFrancisStep {p N : ℕ} {h : p + (N + 3) ≤ n}
    {A B Q Z : Matrix (Fin n) (Fin n) ℝ} (hS : IsQZStepOn p N h A B Q Z)
    (hB : (windowBlock p h B).IsUpperTriangular) (hBd : ∀ i, windowBlock p h B i i ≠ 0) :
    windowBlock p h (Qᵀ * A * Z) * (windowBlock p h (Qᵀ * B * Z))⁻¹ =
        (windowBlock p h Q)ᵀ * (windowBlock p h A * (windowBlock p h B)⁻¹) *
          windowBlock p h Q ∧
      IsFrancisStep (trailingTrace (windowBlock p h A * (windowBlock p h B)⁻¹))
        (trailingDet (windowBlock p h A * (windowBlock p h B)⁻¹))
        (windowBlock p h A * (windowBlock p h B)⁻¹)
        (windowBlock p h (Qᵀ * A * Z) * (windowBlock p h (Qᵀ * B * Z))⁻¹) := by
  obtain ⟨hQ, hZ, hQS, hZS, hA', hB', htri⟩ := hS
  have hQ₂ := windowBlock_mem_orthogonalGroup h hQ hQS
  have hMQ := transpose_mul_mul_mul_inv (A := windowBlock p h A) hQ₂
    (windowBlock_mem_orthogonalGroup h hZ hZS) (isUnit_det_of_diag hB hBd)
  rw [windowBlock_transpose_mul_mul h hQS hZS, windowBlock_transpose_mul_mul h hQS hZS]
  exact ⟨hMQ, windowBlock p h Q, hQ₂, hMQ, hA'.mul_isUpperTriangular hB'.inv, htri⟩

/-- **Algorithm 7.7.2** of [golub2013matrix] on a window, the step that Algorithm 7.7.3 runs on its
unreduced block. Let $p + N + 3 \le n$, let $A \in \mathbb{R}^{n \times n}$ be upper Hessenberg
with the block $p, \dots, p + N + 2$ decoupled ($a_{p,p-1} = 0$ if $p > 0$, and
$a_{p+N+3,p+N+2} = 0$ if $p + N + 3 < n$), and let $B$ be upper triangular. Let the diagonal
block $A_{22}$ on the window be unreduced and the diagonal block $B_{22}$ have nonzero diagonal
entries. Let $(A', B', d_Q, d_Z)$ be the exact run of the QZ step on the block, and let $Q$ and
$Z$ be the products of the reflectors in $d_Q$ and $d_Z$. Then $A' = Q^T A Z$, $B' = Q^T B Z$,
and $(Q, Z)$ is a QZ step on the window (`GolubVanLoan.Chapter07.IsQZStepOn`).

The first left reflector maps the shift vector, which is the first column of
$(M - a_1 I)(M - a_2 I)$ for $M = A_{22} B_{22}^{-1}$, to a multiple of $e_p$, and the other
left reflectors fix $e_p$. The proof combines `GolubVanLoan.Chapter07.algorithm_7_7_2_block` and
`GolubVanLoan.Chapter07.isFrancisStep_of_qz`. -/
theorem algorithm_7_7_2_window {p N : ℕ} (hm : p + (N + 3) ≤ n)
    {A B A' B' : Matrix (Fin n) (Fin n) ℝ} {dQ dZ : List ((Fin n → ℝ) × ℝ)}
    (hA : A.IsUpperHessenberg) (hB : B.IsUpperTriangular)
    (hp : 0 < p → qzEntry A p (p - 1) = 0) (hr₁ : qzEntry A (p + (N + 2) + 1) (p + (N + 2)) = 0)
    (h : Id.run (algorithm_7_7_2 pure p (p + (N + 2)) A B) = (A', B', dQ, dZ))
    (hU : IsUnreduced (windowBlock p hm A)) (hBd : ∀ i, windowBlock p hm B i i ≠ 0) :
    A' = (householderProduct dQ)ᵀ * A * householderProduct dZ ∧
      B' = (householderProduct dQ)ᵀ * B * householderProduct dZ ∧
      IsQZStepOn p N hm A B (householderProduct dQ) (householderProduct dZ) := by
  obtain ⟨hQo, hZo, hA', hB', hA'H, hB'T, hsQ, hsZ, hfirst⟩ :=
    algorithm_7_7_2_block (by omega) (by omega) hA hB hp hr₁ h
  refine ⟨hA', hB', ?_⟩
  obtain ⟨d₀, rest, hdQ, hβ₀, hPu₀, hrest⟩ := hfirst (by omega)
  have hsQ' : ∀ d ∈ dQ, ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < p + (N + 3)) → d.1 i = 0 :=
    fun d hd i hi => hsQ d hd i (by omega)
  have hsZ' : ∀ d ∈ dZ, ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < p + (N + 3)) → d.1 i = 0 :=
    fun d hd i hi => hsZ d hd i (by omega)
  have hQS := isBlockSupported_householderProduct hsQ'
  have hZS := isBlockSupported_householderProduct hsZ'
  set P₀ : Matrix (Fin n) (Fin n) ℝ := 1 - d₀.2 • vecMulVec d₀.1 d₀.1 with hP₀
  have hP₀S : IsBlockSupported p (p + (N + 3)) P₀ :=
    isBlockSupported_reflector d₀.2 (hsQ' d₀ (by rw [hdQ]; exact List.mem_cons_self))
  have hPP : P₀ * P₀ = 1 := by
    refine one_sub_smul_vecMulVec_mul_self_eq_one
      (one_sub_smul_vecMulVec_mem_orthogonalGroup ?_)
    rcases hβ₀ with hb | hb
    · rw [hb, zero_mul]
    · rw [hb, sub_self, mul_zero]
  have hQP : householderProduct dQ *ᵥ Pi.single (windowEmb p hm 0) 1 =
      P₀ *ᵥ Pi.single (windowEmb p hm 0) 1 := by
    rw [hdQ, householderProduct_cons, ← mulVec_mulVec,
      householderProduct_mulVec_single fun q hq => hrest q hq _ (by simp)]
  set u : Fin n → ℝ := fun i =>
    if (i : ℕ) = p then (Id.run (qzShiftVector pure p (p + (N + 2)) A B)).1
    else if (i : ℕ) = p + 1 then (Id.run (qzShiftVector pure p (p + (N + 2)) A B)).2.1
    else if (i : ℕ) = p + 2 then (Id.run (qzShiftVector pure p (p + (N + 2)) A B)).2.2
    else 0 with hu
  have hu0 : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < p + (N + 3)) → u i = 0 := by
    intro i hi
    simp only [hu]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  have hPu : ∀ i, i ≠ windowEmb p hm 0 → (P₀ *ᵥ u) i = 0 := fun i hi =>
    hPu₀ i fun e => hi (Fin.ext (by simp [e]))
  obtain ⟨hPP₂, hQP₂, hPu₂⟩ := windowBlock_first_reflector hm hP₀S hPP hQP hu0 hPu
  have hB₂ : (windowBlock p hm B).IsUpperTriangular := isUpperTriangular_windowBlock hm hB
  have hu₂ : (windowBlock p hm A * (windowBlock p hm B)⁻¹ *
      (windowBlock p hm A * (windowBlock p hm B)⁻¹) -
      trailingTrace (windowBlock p hm A * (windowBlock p hm B)⁻¹) •
        (windowBlock p hm A * (windowBlock p hm B)⁻¹) +
      trailingDet (windowBlock p hm A * (windowBlock p hm B)⁻¹) • 1).col 0 =
        u ∘ windowEmb p hm := by
    rw [qzShift_col (isUpperHessenberg_windowBlock hm hA) hB₂ hBd, hu,
      qzShiftVector_windowBlock hm]
    funext a
    simp
  have hA₂ : ((windowBlock p hm (householderProduct dQ))ᵀ * windowBlock p hm A *
      windowBlock p hm (householderProduct dZ)).IsUpperHessenberg := by
    rw [← windowBlock_transpose_mul_mul hm hQS hZS, ← hA']
    exact isUpperHessenberg_windowBlock hm hA'H
  have hB₂' : ((windowBlock p hm (householderProduct dQ))ᵀ * windowBlock p hm B *
      windowBlock p hm (householderProduct dZ)).IsUpperTriangular := by
    rw [← windowBlock_transpose_mul_mul hm hQS hZS, ← hB']
    exact isUpperTriangular_windowBlock hm hB'T
  obtain ⟨-, htri, -⟩ := isFrancisStep_of_qz hU hB₂ hBd
    (windowBlock_mem_orthogonalGroup hm hQo hQS) (windowBlock_mem_orthogonalGroup hm hZo hZS)
    hA₂ hB₂' hPP₂ hQP₂ (by rw [hu₂]; exact hPu₂)
  exact ⟨hQo, hZo, hQS, hZS, hA₂, hB₂', htri⟩

end QZFrancis

/-! ### Algorithm 7.7.3: the specification -/

section QZAlgorithmSpec

open GolubVanLoan.Chapter05

open scoped Matrix.Norms.Frobenius

/-- In exact arithmetic, the deflation sweep of Algorithm 7.7.3 gives the same matrix as the
deflation sweep `GolubVanLoan.Chapter07.qrDeflate` of Algorithm 7.5.2. -/
theorem qzDeflate_pure_eq (ε : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (qzDeflate pure ε A) = Id.run (qrDeflate pure ε A) := by
  unfold qzDeflate qrDeflate
  rw [List.idRun_foldlM, List.idRun_foldlM]
  congr 1
  funext H i
  rw [qrDeflateStep_pure]
  by_cases hi : 0 < (i : ℕ)
  · simp only [hi, ↓reduceDIte, ↓reduceIte, Id.run_bind, Id.run_pure]
    rw [add_comm |H _ _|]
    split_ifs
    · ext a b
      by_cases ha : a = i
      · subst ha
        by_cases hb : b = ⟨(a : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩
        · simp [hb]
        · simp [hb]
      · simp [ha, updateRow_apply]
    · rfl
  · simp only [hi, ↓reduceDIte, ↓reduceIte, Id.run_pure]

/-- `GolubVanLoan.Chapter07.SubdiagZero A i` holds if and only if $a_{i,i-1} = 0$ whenever
$0 < i < n$. -/
theorem subdiagZero_iff_qzEntry {A : Matrix (Fin n) (Fin n) ℝ} {i : ℕ} :
    SubdiagZero A i ↔ (i < n → 0 < i → qzEntry A i (i - 1) = 0) :=
  ⟨fun h hi hpos => by rw [qzEntry_of_lt A hi (by omega)]; exact h hi hpos,
    fun h hi hpos => by have := h hi hpos; rwa [qzEntry_of_lt A hi (by omega)] at this⟩

/-- The invariant of the passes of Algorithm 7.7.3: $(A, B) = (Q^T (A_0 + E) Z, Q^T B_0 Z)$ with $Q$
and $Z$ orthogonal, $A$ upper Hessenberg, $B$ upper triangular, $\|E\|_F \le (c - 1) \|A_0\|_F$
and $E = 0$ when $\varepsilon = 0$, and no two consecutive nonzero subdiagonal entries of $A$
once the state is finished. -/
private def QZPassInv (ε : ℝ) (A₀ B₀ : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (st : QZArrays n × Bool) : Prop :=
  st.1.Q ∈ orthogonalGroup (Fin n) ℝ ∧ st.1.Z ∈ orthogonalGroup (Fin n) ℝ ∧
    st.1.B = st.1.Qᵀ * B₀ * st.1.Z ∧ st.1.A.IsUpperHessenberg ∧ st.1.B.IsUpperTriangular ∧
    (st.2 = true → NoTwoSubdiag st.1.A) ∧
    ∃ E, st.1.A = st.1.Qᵀ * (A₀ + E) * st.1.Z ∧ ‖E‖ ≤ (c - 1) * ‖A₀‖ ∧ (ε = 0 → E = 0)

open Classical in
/-- The exact run of an unfinished pass of Algorithm 7.7.3, unfolded. -/
private theorem qzPass_false_pure (ε : ℝ) (st : QZArrays n) :
    Id.run (qzPass pure ε (st, false)) =
      let A := Id.run (qzDeflate pure ε st.A)
      if Nat.findGreatest (fun q => qzTrailingQuasi A (n - q)) n = n then
        (⟨A, st.B, st.Q, st.Z⟩, true)
      else
        let r := n - Nat.findGreatest (fun q => qzTrailingQuasi A (n - q)) n - 1
        let p := r - Nat.findGreatest (fun d => qzUnreducedTail A r d) r
        let blk := (List.finRange n).filter fun (i : Fin n) => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ r
        match (blk.filter fun i => st.B i i = 0).getLast? with
        | some k => (Id.run (qzZeroChase pure p k r ⟨A, st.B, st.Q, st.Z⟩), false)
        | none =>
          let out := Id.run (algorithm_7_7_2 pure p r A st.B)
          (⟨out.1, out.2.1,
            Id.run (out.2.2.1.foldlM (fun Q d =>
              householderApplyRight pure d.1 d.2 (List.finRange n) blk Q) st.Q),
            Id.run (out.2.2.2.foldlM (fun Z d =>
              householderApplyRight pure d.1 d.2 (List.finRange n) blk Z) st.Z)⟩, false) := by
  simp only [qzPass, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Accumulating reflector data that are supported on the block into $Q$, by
`GolubVanLoan.Chapter05.householderApplyRight` on the columns of the block, multiplies $Q$ by
the product of the reflectors. -/
private theorem foldlM_householderApplyRight {blk : List (Fin n)} (hblk : blk.Nodup)
    {data : List ((Fin n → ℝ) × ℝ)} (hdata : ∀ d ∈ data, ∀ l, l ∉ blk → d.1 l = 0)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (data.foldlM (fun Q d => householderApplyRight pure d.1 d.2 (List.finRange n) blk Q)
      Q) = Q * householderProduct data := by
  rw [List.idRun_foldlM]
  induction data generalizing Q with
  | nil => simp [householderProduct_nil]
  | cons d data ih =>
    rw [List.foldl_cons, householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hblk
      List.mem_finRange (hdata d List.mem_cons_self),
      ih (fun d' hd' => hdata d' (List.mem_cons_of_mem _ hd')), householderProduct_cons,
      Matrix.mul_assoc]

/-- The zero-chase branch of a pass of Algorithm 7.7.3 of [golub2013matrix], on the deflated matrix
$A_1$ and on $B$. It says: $p \le k \le r < n$; the block $A_{22}$ with the indices
$p, \dots, r$ is unreduced and decoupled ($a_{p,p-1} = 0$ if $p > 0$), and the trailing block
from $r + 1$ on is decoupled and upper quasi-triangular; $b_{kk} = 0$, so that $B_{22}$ is
singular ("if $B_{22}$ is singular, zero $a_{n-q,n-q-1}$"); $Q_2$ and $Z_2$ are orthogonal,
$Q_2^T A_1 Z_2$ is upper Hessenberg and $Q_2^T B Z_2$ is upper triangular,
$(Q_2^T B Z_2)_{rr} = 0$, and $(Q_2^T A_1 Z_2)_{r,r-1} = 0$ if $p < r$. -/
def IsQZChasePass (p r k : ℕ) (A₁ B Q₂ Z₂ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  p ≤ k ∧ k ≤ r ∧ r < n ∧ (0 < p → qzEntry A₁ p (p - 1) = 0) ∧ qzTrailingQuasi A₁ (r + 1) ∧
    qzUnreducedTail A₁ r (r - p) ∧ qzEntry B k k = 0 ∧
    Q₂ ∈ orthogonalGroup (Fin n) ℝ ∧ Z₂ ∈ orthogonalGroup (Fin n) ℝ ∧
    (Q₂ᵀ * A₁ * Z₂).IsUpperHessenberg ∧ (Q₂ᵀ * B * Z₂).IsUpperTriangular ∧
    qzEntry (Q₂ᵀ * B * Z₂) r r = 0 ∧ (p < r → qzEntry (Q₂ᵀ * A₁ * Z₂) r (r - 1) = 0)

/-- The QZ-step branch of a pass of Algorithm 7.7.3 of [golub2013matrix], on the deflated matrix
$A_1$ and on $B$. It says: the block $A_{22}$ with the indices $p, \dots, p + N + 2$ is
unreduced and decoupled ($a_{p,p-1} = 0$ if $p > 0$), and the trailing block from $p + N + 3$ on
is decoupled and upper quasi-triangular; the diagonal entries of $B_{22}$ are nonzero;
$(Q_2, Z_2)$ is a QZ step on the window (`GolubVanLoan.Chapter07.IsQZStepOn`), so that
$Q_2 = \operatorname{diag}(I_p, Q, I_q)$ and $Z_2 = \operatorname{diag}(I_p, Z, I_q)$; and
$Q_2^T A_1 Z_2$ is upper Hessenberg and $Q_2^T B Z_2$ is upper triangular. -/
def IsQZStepPass (p N : ℕ) (h : p + (N + 3) ≤ n) (A₁ B Q₂ Z₂ : Matrix (Fin n) (Fin n) ℝ) :
    Prop :=
  (0 < p → qzEntry A₁ p (p - 1) = 0) ∧ qzTrailingQuasi A₁ (p + (N + 3)) ∧
    IsUnreduced (windowBlock p h A₁) ∧ (∀ i, windowBlock p h B i i ≠ 0) ∧
    IsQZStepOn p N h A₁ B Q₂ Z₂ ∧ (Q₂ᵀ * A₁ * Z₂).IsUpperHessenberg ∧
    (Q₂ᵀ * B * Z₂).IsUpperTriangular

/-- One unfinished pass of Algorithm 7.7.3, in exact arithmetic. Let $Q$ and $Z$ be orthogonal, $A$
upper Hessenberg and $B$ upper triangular, and let $A_1$ be the deflation of $A$ by
`GolubVanLoan.Chapter07.qrDeflate`. Then one of the following describes the pass: $A_1$ has no
two consecutive nonzero subdiagonal entries and the pass returns $(A_1, B, Q, Z)$ as finished;
or the pass is a zero chase (`GolubVanLoan.Chapter07.IsQZChasePass`) with some $Q_2, Z_2$ and
returns $(Q_2^T A_1 Z_2, Q_2^T B Z_2, Q Q_2, Z Z_2)$ as unfinished; or the pass is a QZ step on
the unreduced block (`GolubVanLoan.Chapter07.IsQZStepPass`) with some $Q_2, Z_2$ and returns the
same form of state as unfinished. -/
theorem qzPass_false_spec (ε : ℝ) {st : QZArrays n} {A₁ : Matrix (Fin n) (Fin n) ℝ}
    (hA₁ : Id.run (qrDeflate pure ε st.A) = A₁) (hQ : st.Q ∈ orthogonalGroup (Fin n) ℝ)
    (hZ : st.Z ∈ orthogonalGroup (Fin n) ℝ) (hA : st.A.IsUpperHessenberg)
    (hB : st.B.IsUpperTriangular) :
    (NoTwoSubdiag A₁ ∧ Id.run (qzPass pure ε (st, false)) = (⟨A₁, st.B, st.Q, st.Z⟩, true)) ∨
      (∃ (p r k : ℕ) (Q₂ Z₂ : Matrix (Fin n) (Fin n) ℝ), IsQZChasePass p r k A₁ st.B Q₂ Z₂ ∧
        Id.run (qzPass pure ε (st, false)) =
          (⟨Q₂ᵀ * A₁ * Z₂, Q₂ᵀ * st.B * Z₂, st.Q * Q₂, st.Z * Z₂⟩, false)) ∨
      ∃ (p N : ℕ) (h : p + (N + 3) ≤ n) (Q₂ Z₂ : Matrix (Fin n) (Fin n) ℝ),
        IsQZStepPass p N h A₁ st.B Q₂ Z₂ ∧
        Id.run (qzPass pure ε (st, false)) =
          (⟨Q₂ᵀ * A₁ * Z₂, Q₂ᵀ * st.B * Z₂, st.Q * Q₂, st.Z * Z₂⟩, false) := by
  classical
  have hA₁H : A₁.IsUpperHessenberg := hA₁ ▸ (qrDeflate_isQRDeflation ε st.A).isUpperHessenberg hA
  rw [qzPass_false_pure]
  dsimp only
  rw [qzDeflate_pure_eq, hA₁]
  have hq : qzTrailingQuasi A₁ (n - Nat.findGreatest (fun q => qzTrailingQuasi A₁ (n - q)) n) :=
    Nat.findGreatest_spec (P := fun q => qzTrailingQuasi A₁ (n - q)) (m := 0) (Nat.zero_le n)
      ⟨Or.inr (qzEntry_of_not_lt A₁ (by omega)), fun i hi hni _ => absurd hni (by omega)⟩
  have hqn := Nat.findGreatest_le (P := fun q => qzTrailingQuasi A₁ (n - q)) n
  have hqmax : ∀ k, Nat.findGreatest (fun q => qzTrailingQuasi A₁ (n - q)) n < k → k ≤ n →
      ¬ qzTrailingQuasi A₁ (n - k) := fun k h1 h2 =>
    Nat.findGreatest_is_greatest (P := fun q => qzTrailingQuasi A₁ (n - q)) h1 h2
  generalize Nat.findGreatest (fun q => qzTrailingQuasi A₁ (n - q)) n = q at hq hqn hqmax ⊢
  split_ifs with hqe
  · -- `q = n`: done
    rw [hqe, Nat.sub_self] at hq
    refine Or.inl ⟨fun i hi => ?_, rfl⟩
    rw [subdiagZero_iff_qzEntry, subdiagZero_iff_qzEntry]
    by_cases hin : i + 1 < n
    · rcases hq.2 i (by omega) (by omega) hin with h | h
      · exact Or.inl fun _ _ => h
      · exact Or.inr fun _ _ => by simpa using h
    · exact Or.inr fun h => absurd h (by omega)
  have hqlt : q < n := lt_of_le_of_ne hqn hqe
  generalize hrdef : n - q - 1 = r
  have hr : r < n := by omega
  have hqr : qzTrailingQuasi A₁ (r + 1) := by rwa [show r + 1 = n - q by omega]
  have hr₁ : qzEntry A₁ (r + 1) r = 0 := by
    rcases hqr.1 with h | h
    · omega
    · rwa [show r + 1 - 1 = r by omega] at h
  have hd0 : qzUnreducedTail A₁ r (Nat.findGreatest (fun d => qzUnreducedTail A₁ r d) r) :=
    Nat.findGreatest_spec (P := fun d => qzUnreducedTail A₁ r d) (m := 0) (Nat.zero_le r)
      fun i _ hi => absurd hi (by omega)
  have hdle := Nat.findGreatest_le (P := fun d => qzUnreducedTail A₁ r d) r
  have hdmax : ∀ k, Nat.findGreatest (fun d => qzUnreducedTail A₁ r d) r < k → k ≤ r →
      ¬ qzUnreducedTail A₁ r k := fun k h1 h2 => Nat.findGreatest_is_greatest h1 h2
  generalize Nat.findGreatest (fun d => qzUnreducedTail A₁ r d) r = dd at hd0 hdle hdmax ⊢
  generalize hpdef : r - dd = p
  have hp : 0 < p → qzEntry A₁ p (p - 1) = 0 := by
    intro hp0
    have hnot := hdmax (dd + 1) (by omega) (by omega)
    simp only [qzUnreducedTail, not_forall, not_not] at hnot
    obtain ⟨i, hir, hi, hzero⟩ := hnot
    by_cases hip : r - dd < i
    · exact absurd hzero (hd0 i hir hip)
    · rwa [show i = p by omega] at hzero
  have hmemblk : ∀ i : Fin n, i ∈ (List.finRange n).filter
      (fun (i : Fin n) => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ r) ↔ (p ≤ (i : ℕ) ∧ (i : ℕ) ≤ r) := by
    intro i
    simp
  have hblk : ((List.finRange n).filter fun (i : Fin n) => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ r).Nodup :=
    (List.nodup_finRange n).filter _
  have hQQ : st.Q * st.Qᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 hQ
  have hZZ : st.Z * st.Zᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 hZ
  right
  split
  · -- a zero on the diagonal of `B₂₂`: the zero chase
    left
    rename_i k hk
    have hkmem := List.mem_of_getLast? hk
    rw [List.mem_filter, hmemblk] at hkmem
    obtain ⟨⟨hpk, hkr⟩, hBk⟩ := hkmem
    have hBk' : qzEntry st.B k k = 0 := by rw [qzEntry_fin]; simpa using hBk
    have hequiv : QZArrays.IsEquiv (st.Q * A₁ * st.Zᵀ) (st.Q * st.B * st.Zᵀ)
        ⟨A₁, st.B, st.Q, st.Z⟩ := by
      have hQQ' : st.Qᵀ * st.Q = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hQ
      have hZZ' : st.Zᵀ * st.Z = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hZ
      refine ⟨hQ, hZ, ?_, ?_⟩
      · change A₁ = st.Qᵀ * (st.Q * A₁ * st.Zᵀ) * st.Z
        rw [show st.Qᵀ * (st.Q * A₁ * st.Zᵀ) * st.Z = (st.Qᵀ * st.Q) * A₁ * (st.Zᵀ * st.Z) by
          simp only [Matrix.mul_assoc], hQQ', hZZ', Matrix.one_mul, Matrix.mul_one]
      · change st.B = st.Qᵀ * (st.Q * st.B * st.Zᵀ) * st.Z
        rw [show st.Qᵀ * (st.Q * st.B * st.Zᵀ) * st.Z = (st.Qᵀ * st.Q) * st.B * (st.Zᵀ * st.Z) by
          simp only [Matrix.mul_assoc], hQQ', hZZ', Matrix.one_mul, Matrix.mul_one]
    obtain ⟨⟨hQ', hZ', hA'E, hB'E⟩, hA'H, hB'T, hBrr, hArr, -⟩ :=
      qzZeroChase_spec hpk hkr hr hequiv hA₁H hB hBk' hp hr₁
    generalize Id.run (qzZeroChase pure p k r ⟨A₁, st.B, st.Q, st.Z⟩) = st' at *
    have eA : (st.Qᵀ * st'.Q)ᵀ * A₁ * (st.Zᵀ * st'.Z) = st'.A := by
      rw [hA'E, transpose_mul, transpose_transpose]
      simp only [Matrix.mul_assoc]
    have eB : (st.Qᵀ * st'.Q)ᵀ * st.B * (st.Zᵀ * st'.Z) = st'.B := by
      rw [hB'E, transpose_mul, transpose_transpose]
      simp only [Matrix.mul_assoc]
    have eQ : st.Q * (st.Qᵀ * st'.Q) = st'.Q := by
      rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    have eZ : st.Z * (st.Zᵀ * st'.Z) = st'.Z := by
      rw [← Matrix.mul_assoc, hZZ, Matrix.one_mul]
    refine ⟨p, r, k, st.Qᵀ * st'.Q, st.Zᵀ * st'.Z,
      ⟨hpk, hkr, hr, hp, hqr, by rwa [show r - p = dd by omega], hBk',
        mul_mem (Matrix.transpose_mem_unitaryGroup_iff.2 hQ) hQ',
        mul_mem (Matrix.transpose_mem_unitaryGroup_iff.2 hZ) hZ', by rw [eA]; exact hA'H,
        by rw [eB]; exact hB'T, by rw [eB]; exact hBrr, fun hpr => by rw [eA]; exact hArr hpr⟩,
      ?_⟩
    rw [eA, eB, eQ, eZ]
  · -- the QZ step on the block
    right
    rename_i hnone
    have hpr2 : p + 2 ≤ r := by
      by_contra hlt
      refine hqmax (n - p) (by omega) (by omega) ?_
      rw [show n - (n - p) = p by omega]
      refine ⟨?_, fun i hi hpi hin => ?_⟩
      · rcases Nat.eq_zero_or_pos p with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (hp h0)
      · by_cases hir : r + 1 < i
        · exact hq.2 i hi (by omega) hin
        · by_cases hir' : i = r + 1
          · left
            rw [hir', Nat.add_sub_cancel]
            exact hr₁
          · right
            rw [show i = r by omega]
            exact hr₁
    obtain ⟨N, rfl⟩ : ∃ N, r = p + (N + 2) := ⟨r - p - 2, by omega⟩
    have hm : p + (N + 3) ≤ n := by omega
    have hBd : ∀ a, windowBlock p hm st.B a a ≠ 0 := fun a ha => by
      rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hnone
      have hmem : windowEmb p hm a ∈ (List.finRange n).filter
          (fun (i : Fin n) => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ p + (N + 2)) := by
        rw [hmemblk]
        have := a.isLt
        simp only [val_windowEmb]
        omega
      exact hnone _ hmem (by simpa using ha)
    have hU : IsUnreduced (windowBlock p hm A₁) := by
      refine isUnreduced_iff.2 ⟨isUpperHessenberg_windowBlock hm hA₁H, fun k hk h0 => ?_⟩
      refine hd0 (p + k + 1) (by omega) (by omega) ?_
      rw [qzEntry_of_lt _ (by omega) (by omega)]
      rw [windowBlock_apply] at h0
      convert h0 using 2 <;> exact Fin.ext (by simp only [val_windowEmb]; omega)
    generalize hout : Id.run (algorithm_7_7_2 pure p (p + (N + 2)) A₁ st.B) = out
    obtain ⟨A', B', dQ, dZ⟩ := out
    obtain ⟨-, -, -, -, hA'H, hB'T, hsQ, hsZ, -⟩ :=
      algorithm_7_7_2_block (by omega) (by omega) hA₁H hB hp hr₁ hout
    obtain ⟨hA'eq, hB'eq, hS⟩ := algorithm_7_7_2_window hm hA₁H hB hp hr₁ hout hU hBd
    dsimp only
    rw [foldlM_householderApplyRight hblk (fun d hd l hl => hsQ d hd l (by
        rw [hmemblk] at hl; omega)),
      foldlM_householderApplyRight hblk (fun d hd l hl => hsZ d hd l (by
        rw [hmemblk] at hl; omega))]
    refine ⟨p, N, hm, householderProduct dQ, householderProduct dZ,
      ⟨hp, by rwa [show p + (N + 2) + 1 = p + (N + 3) by omega] at hqr, hU, hBd, hS,
        by rw [← hA'eq]; exact hA'H, by rw [← hB'eq]; exact hB'T⟩, ?_⟩
    rw [hA'eq, hB'eq]

/-- One pass of Algorithm 7.7.3 of [golub2013matrix] in exact arithmetic, as a relation between the
states $((A, B, Q, Z), \mathit{done})$ before and after. A finished state is kept. An unfinished
state is deflated (`GolubVanLoan.Chapter07.IsQRDeflation`) to $A_1$, and then one of three
things happens: $A_1$ has no two consecutive nonzero subdiagonal entries and the state
$(A_1, B, Q, Z)$ is finished; or the zero chase runs on a block with a zero on the diagonal of
$B_{22}$ (`GolubVanLoan.Chapter07.IsQZChasePass`); or a QZ step runs on the unreduced block
(`GolubVanLoan.Chapter07.IsQZStepPass`), which is a Francis step on $A_{22} B_{22}^{-1}$. In the
last two cases the new state is $(Q_2^T A_1 Z_2, Q_2^T B Z_2, Q Q_2, Z Z_2)$ and is unfinished. -/
def IsQZPass (ε : ℝ) (st st' : QZArrays n × Bool) : Prop :=
  (st.2 = true → st' = st) ∧
    (st.2 = false → ∃ A₁, IsQRDeflation ε st.1.A A₁ ∧
      ((NoTwoSubdiag A₁ ∧ st' = (⟨A₁, st.1.B, st.1.Q, st.1.Z⟩, true)) ∨
        (∃ (p r k : ℕ) (Q₂ Z₂ : Matrix (Fin n) (Fin n) ℝ),
          IsQZChasePass p r k A₁ st.1.B Q₂ Z₂ ∧
          st' = (⟨Q₂ᵀ * A₁ * Z₂, Q₂ᵀ * st.1.B * Z₂, st.1.Q * Q₂, st.1.Z * Z₂⟩, false)) ∨
        ∃ (p N : ℕ) (h : p + (N + 3) ≤ n) (Q₂ Z₂ : Matrix (Fin n) (Fin n) ℝ),
          IsQZStepPass p N h A₁ st.1.B Q₂ Z₂ ∧
          st' = (⟨Q₂ᵀ * A₁ * Z₂, Q₂ᵀ * st.1.B * Z₂, st.1.Q * Q₂, st.1.Z * Z₂⟩, false)))

/-- **Algorithm 7.7.3** of [golub2013matrix], a pass is the source's loop body. Let
$\varepsilon \in \mathbb{R}$ and let the state have $Q$ and $Z$ orthogonal, $A$ upper Hessenberg
and $B$ upper triangular. Then the exact run of one pass is related to the state by
`GolubVanLoan.Chapter07.IsQZPass`: a deflation followed by the zero chase or by a QZ step on the
unreduced block. -/
theorem qzPass_isQZPass (ε : ℝ) {st : QZArrays n × Bool}
    (hQ : st.1.Q ∈ orthogonalGroup (Fin n) ℝ) (hZ : st.1.Z ∈ orthogonalGroup (Fin n) ℝ)
    (hA : st.1.A.IsUpperHessenberg) (hB : st.1.B.IsUpperTriangular) :
    IsQZPass ε st (Id.run (qzPass pure ε st)) := by
  obtain ⟨st, d⟩ := st
  cases d with
  | true => exact ⟨fun _ => rfl, fun h => absurd h (by simp)⟩
  | false =>
    exact ⟨fun h => absurd h (by simp), fun _ => ⟨_, qrDeflate_isQRDeflation ε st.A,
      qzPass_false_spec ε rfl hQ hZ hA hB⟩⟩

/-- One pass of Algorithm 7.7.3 keeps the invariant of the passes, with the perturbation factor
multiplied by $(1 + 2\varepsilon)^n$ for the deflation
(`GolubVanLoan.Chapter07.qrDeflate_spec`); the zero chase and the QZ step are exact
equivalences. -/
private theorem qzPass_inv {ε : ℝ} (hε : 0 ≤ ε) {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hc : 1 ≤ c) {st : QZArrays n × Bool} (hst : QZPassInv ε A₀ B₀ c st) :
    QZPassInv ε A₀ B₀ ((1 + 2 * ε) ^ n * c) (Id.run (qzPass pure ε st)) := by
  classical
  obtain ⟨st, d⟩ := st
  obtain ⟨hQ, hZ, hBE, hAH, hBT, hdone, E, hAE, hE, hE0⟩ := hst
  have hA0 : 0 ≤ ‖A₀‖ := norm_nonneg _
  have hpow : 1 ≤ (1 + 2 * ε) ^ n := one_le_pow₀ (by linarith)
  cases d with
  | true =>
    refine ⟨hQ, hZ, hBE, hAH, hBT, hdone, E, hAE, hE.trans ?_, hE0⟩
    have : c ≤ (1 + 2 * ε) ^ n * c := le_mul_of_one_le_left (by linarith) hpow
    nlinarith
  | false =>
    obtain ⟨E₁, hA₁E, hE₁, hE₁0, hA₁H⟩ := qrDeflate_spec hε hQ hZ A₀ hAE hE hE0 hAH
    rcases qzPass_false_spec ε rfl hQ hZ hAH hBT with ⟨h2, hrun⟩ |
        ⟨p, r, k, Q₂, Z₂, ⟨-, -, -, -, -, -, -, hQ₂, hZ₂, hA'H, hB'T, -⟩, hrun⟩ |
        ⟨p, N, h, Q₂, Z₂, ⟨-, -, -, -, ⟨hQ₂, hZ₂, -⟩, hA'H, hB'T⟩, hrun⟩
    · rw [hrun]
      exact ⟨hQ, hZ, hBE, hA₁H, hBT, fun _ => h2, E₁, hA₁E, hE₁, hE₁0⟩
    all_goals
      rw [hrun]
      refine ⟨mul_mem hQ hQ₂, mul_mem hZ hZ₂, ?_, hA'H, hB'T, fun h => by simp at h, E₁, ?_,
        hE₁, hE₁0⟩
      · change Q₂ᵀ * st.B * Z₂ = (st.Q * Q₂)ᵀ * B₀ * (st.Z * Z₂)
        rw [hBE, transpose_mul]
        simp only [Matrix.mul_assoc]
      · change Q₂ᵀ * Id.run (qrDeflate pure ε st.A) * Z₂ = (st.Q * Q₂)ᵀ * (A₀ + E₁) * (st.Z * Z₂)
        rw [hA₁E, transpose_mul]
        simp only [Matrix.mul_assoc]

/-- The passes of Algorithm 7.7.3 keep the invariant, and the perturbation factor grows by
$(1 + 2\varepsilon)^n$ per pass. -/
private theorem qzPass_foldl {ε : ℝ} (hε : 0 ≤ ε) (A₀ B₀ : Matrix (Fin n) (Fin n) ℝ) :
    ∀ (l : List ℕ) (c : ℝ) (st : QZArrays n × Bool), 1 ≤ c → QZPassInv ε A₀ B₀ c st →
      QZPassInv ε A₀ B₀ ((1 + 2 * ε) ^ (n * l.length) * c)
        (l.foldl (fun st _ => Id.run (qzPass pure ε st)) st)
  | [], c, st, _, h => by simpa using h
  | a :: l, c, st, hc, h => by
    have hpow : 1 ≤ (1 + 2 * ε) ^ n := one_le_pow₀ (by linarith)
    have := qzPass_foldl hε A₀ B₀ l _ _ (one_le_mul_of_one_le_of_one_le hpow hc)
      (qzPass_inv hε hc h)
    rw [List.foldl_cons, show (1 + 2 * ε) ^ (n * (a :: l).length) * c =
      (1 + 2 * ε) ^ (n * l.length) * ((1 + 2 * ε) ^ n * c) by
        rw [List.length_cons, Nat.mul_succ, pow_add]; ring]
    exact this

/-- **Algorithm 7.7.3** of [golub2013matrix], exact semantics. Let
$A, B \in \mathbb{R}^{n \times n}$ and $\varepsilon \ge 0$, and let
$((T, S, Q, Z), \mathit{done})$ be the output of the QZ algorithm in exact arithmetic after at
most `fuel` passes. Then $Q$ and $Z$ are orthogonal, $S = Q^T B Z$ is upper triangular, and
there is a perturbation $E$ with $$T = Q^T (A + E) Z, \qquad \|E\|_F \le \bigl((1 +
2\varepsilon)^{n \cdot \mathit{fuel}} - 1\bigr) \|A\|_F,$$ and $E = 0$ when $\varepsilon = 0$.
The matrix $T$ is upper Hessenberg, and if the loop ended ($q = n$, `done`), then $T$ is upper
quasi-triangular. Moreover the iteration is the source's: there is a sequence of states whose
first state is unfinished, is Hessenberg–triangular and satisfies the invariant
`GolubVanLoan.Chapter07.QZArrays.IsEquiv` for $(A, B)$, as the output of Algorithm 7.7.1 does,
in which each state comes from the previous one by a pass in the sense of
`GolubVanLoan.Chapter07.IsQZPass`, and which ends at $((T, S, Q, Z), \mathit{done})$ after
`fuel` passes.

When the loop ended, $(T, S)$ is a generalized real Schur form of $(A + E, B)$: this is Theorem
7.7.2 made constructive, up to the perturbation of the deflations. The zero chase and the QZ
steps are exact equivalences, so $E$ comes from the deflations alone. The norm is the Frobenius
norm.

**Reading.** The source describes a completed floating-point factorization with spectral-norm
perturbations in both arrays. Lean gives a bounded exact-arithmetic run with an explicit
Frobenius bound for threshold deflations in $A$, exact equivalence on $B$, and quasi-
triangularity conditional on the stop flag. -/
theorem algorithm_7_7_3_spec {ε : ℝ} (hε : 0 ≤ ε) (A B : Matrix (Fin n) (Fin n) ℝ) (fuel : ℕ)
    {st : QZArrays n} {done : Bool}
    (h : Id.run (algorithm_7_7_3 pure ε A B fuel) = (st, done)) :
    st.Q ∈ orthogonalGroup (Fin n) ℝ ∧ st.Z ∈ orthogonalGroup (Fin n) ℝ ∧
      st.B = st.Qᵀ * B * st.Z ∧ st.B.IsUpperTriangular ∧
      (∃ E : Matrix (Fin n) (Fin n) ℝ, st.A = st.Qᵀ * (A + E) * st.Z ∧
        ‖E‖ ≤ ((1 + 2 * ε) ^ (n * fuel) - 1) * ‖A‖ ∧ (ε = 0 → E = 0)) ∧
      st.A.IsUpperHessenberg ∧ (done = true → st.A.IsQuasiUpperTriangular) ∧
      ∃ sts : ℕ → QZArrays n × Bool, (sts 0).2 = false ∧ (sts 0).1.IsEquiv A B ∧
        (sts 0).1.A.IsUpperHessenberg ∧ (sts 0).1.B.IsUpperTriangular ∧
        (∀ k < fuel, IsQZPass ε (sts k) (sts (k + 1))) ∧ sts fuel = (st, done) := by
  have hrun : Id.run (algorithm_7_7_3 pure ε A B fuel) =
      Id.run ((List.range fuel).foldlM (fun st _ => qzPass pure ε st)
        (Id.run (algorithm_7_7_1 pure A B), false)) := rfl
  rw [hrun, List.idRun_foldlM] at h
  obtain ⟨hQ₀, hZ₀, hA₀, hB₀, hA₀H, hB₀T⟩ := algorithm_7_7_1_spec A B
  have hinit : QZPassInv ε A B 1 (Id.run (algorithm_7_7_1 pure A B), false) :=
    ⟨hQ₀, hZ₀, hB₀, hA₀H, hB₀T, fun h => by simp at h, 0, by rw [add_zero]; exact hA₀, by simp,
      fun _ => rfl⟩
  let sts : ℕ → QZArrays n × Bool := fun k =>
    (List.range k).foldl (fun st _ => Id.run (qzPass pure ε st))
      (Id.run (algorithm_7_7_1 pure A B), false)
  have hinvk : ∀ k, QZPassInv ε A B ((1 + 2 * ε) ^ (n * k)) (sts k) := fun k => by
    have := qzPass_foldl hε A B (List.range k) 1 _ le_rfl hinit
    rwa [List.length_range, mul_one] at this
  have hstep : ∀ k, sts (k + 1) = Id.run (qzPass pure ε (sts k)) := fun k => by
    simp only [sts, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hfuel : sts fuel = (st, done) := h
  have hpass := hinvk fuel
  rw [hfuel] at hpass
  obtain ⟨hQ, hZ, hBE, hAH, hBT, hdone, E, hAE, hE, hE0⟩ := hpass
  refine ⟨hQ, hZ, hBE, hBT, ⟨E, hAE, hE, hE0⟩, hAH, fun hd =>
    isQuasiUpperTriangular_of_noTwoSubdiag hAH (hdone hd), sts, rfl,
    ⟨hQ₀, hZ₀, hA₀, hB₀⟩, hA₀H, hB₀T, fun k _ => ?_, hfuel⟩
  obtain ⟨hQk, hZk, -, hAk, hBk, -⟩ := hinvk k
  rw [hstep]
  exact qzPass_isQZPass ε hQk hZk hAk hBk

end QZAlgorithmSpec

end GolubVanLoan.Chapter07
