/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.SVD
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Basics

/-!
# Quarteroni, Sacco and Saleri, Section 1.9: The singular value decomposition

This module formalizes §1.9 of [quarteroni2000numerical]. Every matrix
$A \in \mathbb{C}^{m \times n}$ has a singular value decomposition $U^H A V = \Sigma =
\operatorname{diag}(\sigma_1, \dots, \sigma_p)$ with $U$ and $V$ unitary, $p = \min(m, n)$ and
$\sigma_1 \ge \dots \ge \sigma_p \ge 0$ (Property 1.7). The singular values are the square roots of
the eigenvalues of $A^H A$ (1.10); for a Hermitian matrix they are the moduli of the eigenvalues.
The rank of $A$ is the number of nonzero singular values, and the kernel and the range of $A$ are
spanned by columns of $V$ and of $U$. The Moore–Penrose pseudo-inverse is
$A^\dagger = V \Sigma^\dagger U^H$ (Definition 1.15), and it equals $(A^H A)^{-1} A^H$ when $A$ has
full column rank.

The proofs specialize the backbone module `Numlib.LinearAlgebra.Matrix.SVD`.

## Main definitions

* Definition 1.15, `QuarteroniSaccoSaleri.Chapter01.definition_1_15`: the Moore–Penrose
  pseudo-inverse $A^\dagger = V \Sigma^\dagger U^H$, stated for the backbone's `Matrix.pinv`.

## Main results

* Property 1.7, `QuarteroniSaccoSaleri.Chapter01.property_1_7`: every complex matrix has a singular
  value decomposition, and a real matrix has one with real orthogonal factors.
* Equation (1.10), `QuarteroniSaccoSaleri.Chapter01.equation_1_10`:
  $\sigma_i(A) = \sqrt{\lambda_i(A^H A)}$, and the columns of $V$ and $U$ are eigenvectors of
  $A^H A$ and $A A^H$.
* §1.9, `QuarteroniSaccoSaleri.Chapter01.singularValues_of_isHermitian`: the singular values of a
  Hermitian matrix are the moduli of its eigenvalues.
* §1.9, `QuarteroniSaccoSaleri.Chapter01.rank_eq_card_singularValues_ne_zero`: the rank is the
  number of nonzero singular values.
* §1.9, `QuarteroniSaccoSaleri.Chapter01.ker_range_of_svd`: the kernel and the range of $A$ in terms
  of the singular vectors.
* Definition 1.15, `QuarteroniSaccoSaleri.Chapter01.definition_1_15_fullRank`:
  $A^\dagger = (A^H A)^{-1} A^H$ when $\operatorname{rank} A = n$, and $A^\dagger = A^{-1}$ for a
  nonsingular square $A$.
* Exercise 12 of Chapter 1, `QuarteroniSaccoSaleri.Chapter01.exercise_1_12`: $A^\dagger A = I_n$
  when $\operatorname{rank} A = n$, and $A^\dagger A A^\dagger = A^\dagger$ and $A A^\dagger A = A$.

## Conventions

* The rectangular diagonal matrix $\Sigma = \operatorname{diag}(\sigma_1, \dots, \sigma_p) \in
  \mathbb{C}^{m \times n}$ of (1.9) is the backbone's `Matrix.rectDiagonal σ` for a sequence
  `σ : ℕ → ℂ`, whose values at indices $i \ge \min(m, n)$ are not used.
* Indices are 0-based, so the book's $\sigma_1$ is `σ 0`. The columns $u_i$ of $U$ and $v_j$ of $V$
  are `Uᵀ i` and `Vᵀ j`.
* The sorted singular values $\sigma_1 \ge \sigma_2 \ge \dots \ge 0$ are Mathlib's
  `(toEuclideanLin A).singularValues : ℕ → ℝ`. The backbone's
  `Matrix.colSingularValues A : Fin n → ℝ` are the same numbers indexed by the columns of $A$, in
  the order of the eigenvalues of $A^H A$; (1.10) is their definition.

## Implementation notes

* The statements about "an SVD" take as hypothesis an arbitrary factorization
  $U^H A V = \operatorname{diag}(\sigma)$ with $U$ and $V$ unitary, where the $\sigma_i$ are not
  assumed to be sorted or nonnegative.
* Lean's convention $0^{-1} = 0$ makes $\Sigma^\dagger = \operatorname{diag}(1/\sigma_1, \dots,
  1/\sigma_r, 0, \dots, 0)$ the entrywise inverse of the diagonal of $\Sigma$, with no case split on
  the rank $r$.

## Deviations from the source

* **Exercise 12 of Chapter 1** (generalization). The book assumes $\operatorname{rank} A = n$; the
  identities $A^\dagger A A^\dagger = A^\dagger$ and $A A^\dagger A = A$ are stated for every $A$.
  See `QuarteroniSaccoSaleri.Chapter01.exercise_1_12`.
-/

open Finset Matrix
open scoped ComplexOrder

namespace QuarteroniSaccoSaleri.Chapter01

variable {m n : ℕ}

/-! ### Property 1.7: the SVD -/

/-- **Property 1.7** of [quarteroni2000numerical], with (1.9). Let $A \in \mathbb{C}^{m \times n}$
and $p = \min(m, n)$. There are unitary matrices $U \in \mathbb{C}^{m \times m}$ and
$V \in \mathbb{C}^{n \times n}$ such that
$$U^H A V = \Sigma = \operatorname{diag}(\sigma_1, \dots, \sigma_p) \in \mathbb{C}^{m \times n},
  \qquad \sigma_1 \ge \dots \ge \sigma_p \ge 0.$$
This is the **singular value decomposition** of $A$, and the $\sigma_i$ are the **singular
values** of $A$. The sequence of the singular values is nonincreasing and nonnegative, and it
vanishes from the index $p$ on. If $B \in \mathbb{R}^{m \times n}$, there are real orthogonal
matrices $U$ and $V$ with $U^T B V = \Sigma$, where $\Sigma$ holds the singular values of $B$.

The singular values are Mathlib's sorted sequence `(toEuclideanLin A).singularValues`, indexed
from $0$. The proof specializes the backbone theorem `Matrix.exists_svd`. -/
theorem property_1_7 (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) (Fin n) ℝ) :
    (∃ U ∈ unitaryGroup (Fin m) ℂ, ∃ V ∈ unitaryGroup (Fin n) ℂ,
      star U * A * V = rectDiagonal fun i => (((toEuclideanLin A).singularValues i : ℝ) : ℂ)) ∧
      Antitone (toEuclideanLin A).singularValues ∧
      (∀ i, 0 ≤ (toEuclideanLin A).singularValues i) ∧
      (∀ i, min m n ≤ i → (toEuclideanLin A).singularValues i = 0) ∧
      ∃ U ∈ orthogonalGroup (Fin m) ℝ, ∃ V ∈ orthogonalGroup (Fin n) ℝ,
        Uᵀ * B * V = rectDiagonal fun i => (toEuclideanLin B).singularValues i := by
  refine ⟨exists_svd A, (toEuclideanLin A).singularValues_antitone,
    (toEuclideanLin A).singularValues_nonneg, fun i hi => ?_, ?_⟩
  · rcases le_or_gt m n with hmn | hmn
    · rw [min_eq_left hmn] at hi
      exact (toEuclideanLin A).singularValues_of_finrank_codomain_le
        (finrank_euclideanSpace_fin.trans_le hi)
    · rw [min_eq_right hmn.le] at hi
      exact (toEuclideanLin A).singularValues_of_finrank_le (finrank_euclideanSpace_fin.trans_le hi)
  · obtain ⟨U, hU, V, hV, h⟩ := exists_svd B
    refine ⟨U, hU, V, hV, ?_⟩
    rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose, h]
    rfl

/-! ### Equation (1.10): the singular values through $A^H A$ -/

/-- For square matrices $M$, $V$ and a diagonal matrix $D = \operatorname{diag}(d)$, if $MV = VD$
then every column $v_j$ of $V$ satisfies $M v_j = d_j v_j$. -/
private theorem mulVec_transpose_eq_of_mul_eq_mul_diagonal {k : ℕ} {M V : Matrix (Fin k) (Fin k) ℂ}
    {d : Fin k → ℂ} (h : M * V = V * diagonal d) (j : Fin k) : M *ᵥ Vᵀ j = d j • Vᵀ j := by
  ext r
  have := congrFun (congrFun h r) j
  rw [mul_diagonal] at this
  simp only [mulVec, dotProduct, transpose_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.mul_apply, this, mul_comm]

/-- **Equation (1.10)** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{m \times n}$. The
singular values of $A$, indexed by the columns, are
$$\sigma_i(A) = \sqrt{\lambda_i(A^H A)}, \qquad i = 1, \dots, n,$$
where $\lambda_i(A^H A)$ are the eigenvalues of the Hermitian matrix $A^H A$; so
$\sigma_i(A)^2 = \lambda_i(A^H A)$. Now let $U \in \mathbb{C}^{m \times m}$ and
$V \in \mathbb{C}^{n \times n}$ be unitary with $U^H A V = \Sigma = \operatorname{diag}(\sigma)$
for some $\sigma_1, \sigma_2, \dots \in \mathbb{C}$. Then:

* if $U^H A V = \operatorname{diag}(\tau)$ for a nonincreasing sequence $\tau$ of nonnegative
  reals, then $\tau_i$ is the $i$-th sorted singular value of $A$ for every $i \le \min(m, n)$;
* $A = U \Sigma V^H$ and $A^H A = V \Sigma^H \Sigma V^H$;
* the columns $v_j$ of $V$, the **right singular vectors**, are eigenvectors of $A^H A$:
  $A^H A v_j = |\sigma_j|^2 v_j$ for $j \le m$, and $A^H A v_j = 0$ for $j > m$;
* the columns $u_i$ of $U$, the **left singular vectors**, are eigenvectors of $A A^H$:
  $A A^H u_i = |\sigma_i|^2 u_i$ for $i \le n$, and $A A^H u_i = 0$ for $i > n$.

The singular values indexed by the columns are the backbone's `Matrix.colSingularValues A`,
defined by the square root in (1.10). The second clause uses the backbone theorem
`Matrix.singularValues_eq_of_svd`. In Lean the indices are 0-based, so the conditions
$i \le \min(m, n)$, $j \le m$ and $i \le n$ read `i < m ∧ i < n`, `j < m` and `i < n`. -/
theorem equation_1_10 (A : Matrix (Fin m) (Fin n) ℂ) {U : Matrix (Fin m) (Fin m) ℂ}
    {V : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin m) ℂ)
    (hV : V ∈ unitaryGroup (Fin n) ℂ) {σ : ℕ → ℂ} (h : star U * A * V = rectDiagonal σ) :
    (∀ i, A.colSingularValues i = √((isHermitian_conjTranspose_mul_self A).eigenvalues i) ∧
        A.colSingularValues i ^ 2 = (isHermitian_conjTranspose_mul_self A).eigenvalues i) ∧
      (∀ τ : ℕ → ℝ, Antitone τ → (∀ i, 0 ≤ τ i) →
        star U * A * V = rectDiagonal (fun i => ((τ i : ℝ) : ℂ)) →
        ∀ i, i < m → i < n → (toEuclideanLin A).singularValues i = τ i) ∧
      A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℂ) * star V ∧
      Aᴴ * A = V * ((rectDiagonal σ : Matrix (Fin m) (Fin n) ℂ)ᴴ * rectDiagonal σ) * star V ∧
      (∀ j : Fin n, (Aᴴ * A) *ᵥ Vᵀ j = (if (j : ℕ) < m then star (σ j) * σ j else 0) • Vᵀ j) ∧
      ∀ i : Fin m, (A * Aᴴ) *ᵥ Uᵀ i = (if (i : ℕ) < n then σ i * star (σ i) else 0) • Uᵀ i := by
  have hA : A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℂ) * Vᴴ :=
    eq_mul_mul_star_of_star_mul_mul_eq hU hV h
  have hUU : Uᴴ * U = 1 := mem_unitaryGroup_iff'.1 hU
  have hVV : Vᴴ * V = 1 := mem_unitaryGroup_iff'.1 hV
  have hAA : Aᴴ * A = V * ((rectDiagonal σ : Matrix (Fin m) (Fin n) ℂ)ᴴ * rectDiagonal σ) *
      Vᴴ := by
    rw [hA, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ, hUU, Matrix.one_mul]
  refine ⟨fun i => ⟨rfl, sq_colSingularValues A i⟩,
    fun τ hτ hτ0 hτA i him hin => singularValues_eq_of_svd hU hV hτ hτ0 hτA him hin, hA, hAA,
    fun j => ?_, fun i => ?_⟩
  · refine mulVec_transpose_eq_of_mul_eq_mul_diagonal
      (d := fun j : Fin n => if (j : ℕ) < m then star (σ j) * σ j else 0) ?_ j
    rw [hAA, Matrix.mul_assoc, hVV, Matrix.mul_one, conjTranspose_rectDiagonal_mul_self]
  · refine mulVec_transpose_eq_of_mul_eq_mul_diagonal
      (d := fun i : Fin m => if (i : ℕ) < n then σ i * star (σ i) else 0) ?_ i
    have hAAt : A * Aᴴ = U * (rectDiagonal σ * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℂ)ᴴ) *
        Uᴴ := by
      rw [hA, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ, hVV, Matrix.one_mul]
    rw [hAAt, Matrix.mul_assoc, hUU, Matrix.mul_one, rectDiagonal_conjTranspose,
      rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
    rfl

/-- **Section 1.9** of [quarteroni2000numerical], the Hermitian case. Let
$A \in \mathbb{C}^{n \times n}$ be Hermitian with eigenvalues $\lambda_1, \dots, \lambda_n$.
Then the singular values of $A$ are $|\lambda_1|, \dots, |\lambda_n|$: there is a permutation
$e$ of the indices with $\sigma_{e(i)}(A) = |\lambda_i(A)|$ for all $i$.

The reason is that $A^H A = A^2$, so $\sigma_i = \sqrt{\lambda_i^2} = |\lambda_i|$. The singular
values are `Matrix.colSingularValues A`, and the eigenvalues are `hA.eigenvalues`. The proof is
the backbone theorem `Matrix.IsHermitian.exists_equiv_colSingularValues_eq_abs_eigenvalues`. -/
theorem singularValues_of_isHermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ∃ e : Fin n ≃ Fin n, ∀ i, A.colSingularValues (e i) = |hA.eigenvalues i| :=
  hA.exists_equiv_colSingularValues_eq_abs_eigenvalues

/-! ### The rank, the kernel and the range from the SVD -/

/-- **Section 1.9** of [quarteroni2000numerical], the rank. Let $A \in \mathbb{C}^{m \times n}$. The
rank of $A$ is the number of nonzero singular values of $A$: if $\sigma_1 \ge \dots \ge
\sigma_r > \sigma_{r+1} = \dots = \sigma_p = 0$, then $\operatorname{rank} A = r$. Equivalently,
the sorted singular value $\sigma_i$ (0-based) is positive if and only if
$i < \operatorname{rank} A$, and it is zero if and only if $i \ge \operatorname{rank} A$.

The statement holds both for the singular values indexed by the columns,
`Matrix.colSingularValues A`, and for the sorted sequence `(toEuclideanLin A).singularValues`.
The proof uses the backbone theorem `Matrix.card_colSingularValues_ne_zero` and Mathlib's
`LinearMap.card_support_singularValues`. -/
theorem rank_eq_card_singularValues_ne_zero (A : Matrix (Fin m) (Fin n) ℂ) :
    A.rank = Fintype.card {i : Fin n // A.colSingularValues i ≠ 0} ∧
      A.rank = (toEuclideanLin A).singularValues.support.card ∧
      (∀ i, 0 < (toEuclideanLin A).singularValues i ↔ i < A.rank) ∧
      ∀ i, (toEuclideanLin A).singularValues i = 0 ↔ A.rank ≤ i := by
  have hr : Module.finrank ℂ (LinearMap.range (toEuclideanLin A)) = A.rank := by
    rw [rank_eq_finrank_range_toLin A (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis, toEuclideanLin_eq_toLin_orthonormal]
  refine ⟨(card_colSingularValues_ne_zero A).symm, ?_, fun i => ?_, fun i => ?_⟩
  · rw [LinearMap.card_support_singularValues, hr]
  · rw [LinearMap.singularValues_pos_iff_lt_finrank_range, hr]
  · rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range, hr]

/-- **Section 1.9** of [quarteroni2000numerical], the kernel and the range. Let
$A \in \mathbb{C}^{m \times n}$, and let $U \in \mathbb{C}^{m \times m}$ and
$V \in \mathbb{C}^{n \times n}$ be unitary with $U^H A V = \operatorname{diag}(\sigma)$. Then
the kernel of $A$ is the span of the columns $v_j$ of $V$ with $j > m$ or $\sigma_j = 0$, and
the range of $A$ is the span of the columns $u_i$ of $U$ with $i \le n$ and $\sigma_i \neq 0$.
For sorted singular values with $\sigma_r > \sigma_{r+1} = 0$, these are $\ker(A) =
\operatorname{span}\{v_{r+1}, \dots, v_n\}$ and $\operatorname{range}(A) =
\operatorname{span}\{u_1, \dots, u_r\}$.

In Lean the indices are 0-based, so $j > m$ and $i \le n$ read `m ≤ j` and `i < n`. The proof
uses the backbone theorems `Matrix.ker_mulVecLin_eq_span_of_svd` and
`Matrix.range_mulVecLin_eq_span_of_svd`. -/
theorem ker_range_of_svd {A : Matrix (Fin m) (Fin n) ℂ} {U : Matrix (Fin m) (Fin m) ℂ}
    {V : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin m) ℂ)
    (hV : V ∈ unitaryGroup (Fin n) ℂ) {σ : ℕ → ℂ} (h : star U * A * V = rectDiagonal σ) :
    LinearMap.ker A.mulVecLin = Submodule.span ℂ (Vᵀ '' {j : Fin n | m ≤ (j : ℕ) ∨ σ j = 0}) ∧
      LinearMap.range A.mulVecLin = Submodule.span ℂ (Uᵀ '' {i : Fin m | (i : ℕ) < n ∧ σ i ≠ 0}) :=
  ⟨ker_mulVecLin_eq_span_of_svd hU hV h, range_mulVecLin_eq_span_of_svd hU hV h⟩

/-! ### Definition 1.15: the Moore–Penrose pseudo-inverse -/

/-- **Definition 1.15** of [quarteroni2000numerical], with (1.11). Let
$A \in \mathbb{C}^{m \times n}$, and let $U \in \mathbb{C}^{m \times m}$ and
$V \in \mathbb{C}^{n \times n}$ be unitary with
$U^H A V = \Sigma = \operatorname{diag}(\sigma)$. The **Moore–Penrose pseudo-inverse**, or
**generalized inverse**, of $A$ is
$$A^\dagger = V \Sigma^\dagger U^H, \qquad \Sigma^\dagger =
  \operatorname{diag}\Big(\frac{1}{\sigma_1}, \dots, \frac{1}{\sigma_r}, 0, \dots, 0\Big) \in
  \mathbb{C}^{n \times m},$$
where $\Sigma^\dagger$ inverts the nonzero diagonal entries of $\Sigma$ and keeps the zero ones.
The matrix $A^\dagger$ does not depend on the chosen decomposition.

The statement is a theorem about the backbone's `Matrix.pinv A`, which is defined without a
decomposition. The matrix $\Sigma^\dagger$ is the entrywise inverse of the diagonal, because
$0^{-1} = 0$ in Lean. The proof is the backbone theorem `Matrix.pinv_eq_of_svd`. -/
theorem definition_1_15 {A : Matrix (Fin m) (Fin n) ℂ} {U : Matrix (Fin m) (Fin m) ℂ}
    {V : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin m) ℂ)
    (hV : V ∈ unitaryGroup (Fin n) ℂ) {σ : ℕ → ℂ} (h : star U * A * V = rectDiagonal σ) :
    A.pinv = V * (rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℂ) * star U :=
  pinv_eq_of_svd hU hV h

/-- **Definition 1.15** of [quarteroni2000numerical], the full-rank cases. Let
$A \in \mathbb{C}^{m \times n}$, $B \in \mathbb{R}^{m \times n}$ and
$C \in \mathbb{C}^{n \times n}$. If $\operatorname{rank} A = n$ (the columns of $A$ are linearly
independent, which needs $n \le m$), then $A^\dagger = (A^H A)^{-1} A^H$. If
$\operatorname{rank} B = n$, then $B^\dagger = (B^T B)^{-1} B^T$. If
$\operatorname{rank} C = n$, then $C^\dagger = C^{-1}$.

The proof uses the backbone theorems
`Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit` and
`Matrix.pinv_eq_inv`. -/
theorem definition_1_15_fullRank (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℂ) :
    (A.rank = n → A.pinv = (Aᴴ * A)⁻¹ * Aᴴ) ∧ (B.rank = n → B.pinv = (Bᵀ * B)⁻¹ * Bᵀ) ∧
      (C.rank = n → C.pinv = C⁻¹) := by
  refine ⟨fun hA => ?_, fun hB => ?_,
    fun hC => pinv_eq_inv (isUnit_of_rank_eq_card (by rw [Fintype.card_fin]; exact hC))⟩
  · exact pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit
      (isUnit_of_rank_eq_card (by rw [rank_conjTranspose_mul_self, hA, Fintype.card_fin]))
  · rw [← conjTranspose_eq_transpose_of_trivial]
    exact pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit
      (isUnit_of_rank_eq_card (by rw [rank_conjTranspose_mul_self, hB, Fintype.card_fin]))

/-- **Exercise 12 of Chapter 1** of [quarteroni2000numerical], which §1.9 cites for the properties
of $A^\dagger$. Let $A \in \mathbb{C}^{m \times n}$ and $C \in \mathbb{C}^{n \times n}$. Then:
(1) if $\operatorname{rank} A = n$, then $A^\dagger A = I_n$; (2)
$A^\dagger A A^\dagger = A^\dagger$ and $A A^\dagger A = A$; (3) if $\operatorname{rank} C = n$,
then $C^\dagger = C^{-1}$.

**Generalization.** The book assumes $\operatorname{rank} A = n$ for all three parts. The
identities (2) are stated here for every $A$.

The proof of (2) uses the backbone theorems `Matrix.pinv_mul_self_mul_pinv` and
`Matrix.mul_pinv_mul_self`. -/
theorem exercise_1_12 (A : Matrix (Fin m) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ) :
    (A.rank = n → A.pinv * A = 1) ∧ (A.pinv * A * A.pinv = A.pinv ∧ A * A.pinv * A = A) ∧
      (C.rank = n → C.pinv = C⁻¹) := by
  refine ⟨fun hA => ?_, ⟨pinv_mul_self_mul_pinv A, mul_pinv_mul_self A⟩,
    (definition_1_15_fullRank A 0 C).2.2⟩
  have hG : IsUnit (Aᴴ * A) :=
    isUnit_of_rank_eq_card (by rw [rank_conjTranspose_mul_self, hA, Fintype.card_fin])
  rw [(definition_1_15_fullRank A 0 C).1 hA, Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hG)]

end QuarteroniSaccoSaleri.Chapter01
