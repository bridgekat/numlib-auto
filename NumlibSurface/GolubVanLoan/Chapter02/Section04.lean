/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.Polar
import NumlibSurface.GolubVanLoan.Chapter02.Section01
import NumlibSurface.GolubVanLoan.Chapter02.Section03

/-!
# Golub and Van Loan, Section 2.4: The singular value decomposition

This module formalizes §2.4 of [golub2013matrix]. Theorem 2.4.1 says that every
$A \in \mathbb{R}^{m \times n}$ has a singular value decomposition $U^T A V = \Sigma =
\operatorname{diag}(\sigma_1, \dots, \sigma_p)$ with $U$ and $V$ orthogonal, $p = \min\{m, n\}$ and
$\sigma_1 \ge \dots \ge \sigma_p \ge 0$. The module defines the largest and the smallest singular
values $\sigma_{\max}(A)$ and $\sigma_{\min}(A)$, and proves the consequences of the SVD in
Corollaries 2.4.2–2.4.7 with (2.4.1)–(2.4.2): the singular vectors are eigenvectors of $A^T A$ and
$A A^T$, $\|A\|_2 = \sigma_1$, $\|A\|_F^2 = \sigma_1^2 + \dots + \sigma_p^2$, the perturbation of
$\sigma_{\max}$ and $\sigma_{\min}$, the effect of adding a column, the rank, null space and range,
and the expansion $A = \sum_{i=1}^r \sigma_i u_i v_i^T$. It then proves the Eckart–Young theorem
(Theorem 2.4.8 with (2.4.3)–(2.4.4)): the truncation $A_k = \sum_{i=1}^k \sigma_i u_i v_i^T$ is a
closest matrix of rank $k$ to $A$ in the 2-norm, at distance $\sigma_{k+1}$. The two remarks after
it, the thin SVD of §2.4.3 and the complex SVD of §2.4.4 complete the module.

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.SVD` (existence,
`Matrix.IsSVD`, the null space and the range, `Matrix.svdTruncation`, the least singular value as
the least stretch), `Numlib.Analysis.Matrix.SingularValues` (Weyl's inequality, column deletion, and
Eckart–Young in the 2-norm and the Frobenius norm) and `Numlib.LinearAlgebra.Matrix.Polar` (the
first columns of a unitary matrix, for the thin SVD).

## Main definitions

* §2.4.1, `GolubVanLoan.Chapter02.sigmaMax`: the largest singular value
  $\sigma_{\max}(A) = \sigma_1$.
* §2.4.1, `GolubVanLoan.Chapter02.sigmaMin`: the smallest singular value
  $\sigma_{\min}(A) = \sigma_p$, $p = \min\{m, n\}$.

## Main results

* Theorem 2.4.1, `GolubVanLoan.Chapter02.theorem_2_4_1`: every real matrix has an SVD whose diagonal
  is the sorted singular values.
* Corollary 2.4.2, `GolubVanLoan.Chapter02.corollary_2_4_2`: for $m \ge n$, $A v_i = \sigma_i u_i$
  and $A^T u_i = \sigma_i v_i$.
* Equations (2.4.1)–(2.4.2), `GolubVanLoan.Chapter02.equation_2_4_1` and
  `GolubVanLoan.Chapter02.equation_2_4_2`: $A^T A v_i = \sigma_i^2 v_i$ and
  $A A^T u_i = \sigma_i^2 u_i$.
* Corollary 2.4.3, `GolubVanLoan.Chapter02.corollary_2_4_3`: $\|A\|_2 = \sigma_1$ and $\|A\|_F =
  \sqrt{\sigma_1^2 + \dots + \sigma_p^2}$.
* Corollary 2.4.4, `GolubVanLoan.Chapter02.corollary_2_4_4`: $\sigma_{\max}(A + E) \le
  \sigma_{\max}(A) + \|E\|_2$ and $\sigma_{\min}(A + E) \ge \sigma_{\min}(A) - \|E\|_2$.
* Corollary 2.4.5, `GolubVanLoan.Chapter02.corollary_2_4_5`: appending a column does not decrease
  $\sigma_{\max}$ and does not increase $\sigma_{\min}$.
* Corollary 2.4.6, `GolubVanLoan.Chapter02.corollary_2_4_6`: if exactly $r$ singular values are
  positive, then $\operatorname{rank}(A) = r$ and the singular vectors span the null space and the
  range.
* Corollary 2.4.7, `GolubVanLoan.Chapter02.corollary_2_4_7`: $A = \sum_{i=1}^r \sigma_i u_i v_i^T$
  for $r = \operatorname{rank}(A)$.
* Theorem 2.4.8 with (2.4.3)–(2.4.4), `GolubVanLoan.Chapter02.theorem_2_4_8`: the Eckart–Young
  theorem in the 2-norm.
* §2.4.2, `GolubVanLoan.Chapter02.sigmaMin_eq_dist_rankDeficient`: $\sigma_{\min}(A)$ is the 2-norm
  distance from $A$ to the rank-deficient matrices.
* §2.4.2, `GolubVanLoan.Chapter02.svdTruncation_isLeast_frobenius`: the Eckart–Young theorem in the
  Frobenius norm.
* §2.4.3, `GolubVanLoan.Chapter02.thin_svd`: the thin SVD $A = U_1 \Sigma_1 V^T$ for $m \ge n$.
* §2.4.4, `GolubVanLoan.Chapter02.complex_svd`: the SVD of a complex matrix, and the unitary
  invariance of the 2-norm and the Frobenius norm.

## Proof outline

The backbone constructs the SVD from an orthonormal eigenbasis of $A^T A$, not by the induction
through $\|A\|_2$ of the source. The lower bound in the Eckart–Young theorem is Weyl's inequality
$\sigma_{i+j-1}(A + B) \le \sigma_i(A) + \sigma_j(B)$, whose proof is the kernel intersection
argument of the source.

## Conventions

* Matrices are `Matrix (Fin m) (Fin n) ℝ` with 0-based indices. The singular value $\sigma_i(A)$ of
  the source, $1 \le i \le p = \min\{m, n\}$, is `A.sortedSingularValues (i - 1)`. It is defined for
  every shape and is $0$ from the rank on.
* "An SVD $U^T A V = \Sigma$ of $A$" is the hypothesis `Matrix.IsSVD A U σ V`: $U$ and $V$ are
  orthogonal (the unitary group over $\mathbb{R}$, where `star` is the transpose), $U^T A V = $
  `Matrix.rectDiagonal σ`, and $\sigma$ is antitone and nonnegative. Its first $p$ values are the
  sorted singular values (`Matrix.IsSVD.singularValues_eq`).
* The singular vectors $u_i$ and $v_i$ are the columns `U.col i` and `V.col i`.
* The 2-norm is `Matrix.lpOpNorm 2`, and the Frobenius norm is the scoped norm
  `Matrix.Norms.Frobenius`. The range and the null space are those of `Matrix.toEuclideanLin`, as in
  §2.1.
* The truncation $A_k$ of (2.4.3) is `Matrix.svdTruncation U σ V k`. It is defined from the factors,
  because the SVD is not unique.

## Deviations from the source

* **Corollary 2.4.5** (reading). The source does not define $\sigma_{\min}$ of an $m \times 0$
  matrix; the corollary assumes $n \ge 1$. See `GolubVanLoan.Chapter02.corollary_2_4_5`.
* **Remark after Theorem 2.4.8** (reading). The statement that $\sigma_{\min}(A)$ is the distance to
  the rank-deficient matrices assumes $m, n \ge 1$. See
  `GolubVanLoan.Chapter02.sigmaMin_eq_dist_rankDeficient`.

## Not formalized

* **The hyperellipsoid picture after Corollary 2.4.2.** It is prose.
* **The pointer to §8.6 for the computation of the SVD.** It is prose.
-/

open Matrix WithLp

namespace GolubVanLoan.Chapter02

variable {m n : ℕ}

/-! ### §2.4.1 Derivation -/

/-- **Section 2.4.1** of [golub2013matrix], the largest singular value. For
$A \in \mathbb{R}^{m \times n}$, $\sigma_{\max}(A)$ is the largest singular value $\sigma_1$ of
$A$.

It is `A.sortedSingularValues 0`, which is $0$ when $m = 0$ or $n = 0$. -/
noncomputable def sigmaMax (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  A.sortedSingularValues 0

/-- **Section 2.4.1** of [golub2013matrix], the smallest singular value. For
$A \in \mathbb{R}^{m \times n}$ and $p = \min\{m, n\}$, $\sigma_{\min}(A)$ is the smallest of
the $p$ singular values $\sigma_1 \ge \dots \ge \sigma_p$ of $A$. It is $0$ when $A$ is rank
deficient.

It is `A.sortedSingularValues (p - 1)` with natural number subtraction, so for $p = 0$ it is
`A.sortedSingularValues 0`, which is $0$. -/
noncomputable def sigmaMin (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  A.sortedSingularValues (min m n - 1)

/-- For $A \in \mathbb{R}^{m \times n}$, $\sigma_{\max}(A)$ is the largest of the column-indexed
singular values `Matrix.colSingularValues` of the backbone. Both sides are $0$ when $n = 0$. -/
theorem sigmaMax_eq_iSup_colSingularValues (A : Matrix (Fin m) (Fin n) ℝ) :
    sigmaMax A = ⨆ i, A.colSingularValues i := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [Real.iSup_of_isEmpty, sigmaMax]
    exact sortedSingularValues_eq_zero_of_min_le A (by simp)
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact (sortedSingularValues_zero_eq_l2_opNorm A).trans (l2_opNorm_eq_iSup_colSingularValues A)

/-- For $A \in \mathbb{R}^{m \times n}$ with $n \le m$, $\sigma_{\min}(A)$ is the least of the
column-indexed singular values `Matrix.colSingularValues` of the backbone. Both sides are $0$
when $n = 0$. -/
theorem sigmaMin_eq_iInf_colSingularValues (A : Matrix (Fin m) (Fin n) ℝ) (hmn : n ≤ m) :
    sigmaMin A = ⨅ i, A.colSingularValues i := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [Real.iInf_of_isEmpty, sigmaMin]
    exact sortedSingularValues_eq_zero_of_min_le A (by simp)
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [sigmaMin, min_eq_right hmn, ← sortedSingularValues_eq_iInf_colSingularValues,
      Fintype.card_fin]

/-- **Theorem 2.4.1** of [golub2013matrix] (singular value decomposition). For
$A \in \mathbb{R}^{m \times n}$ there are orthogonal matrices $U \in \mathbb{R}^{m \times m}$
and $V \in \mathbb{R}^{n \times n}$ with
$$U^T A V = \Sigma = \operatorname{diag}(\sigma_1, \dots, \sigma_p) \in \mathbb{R}^{m \times n},
  \qquad p = \min\{m, n\},$$
where $\sigma_1 \ge \sigma_2 \ge \dots \ge \sigma_p \ge 0$.

The statement is `Matrix.IsSVD A U A.sortedSingularValues V`, so the diagonal is the sorted
singular values. The proof applies `Matrix.exists_svd`. -/
theorem theorem_2_4_1 (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U V, IsSVD A U A.sortedSingularValues V := by
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  exact ⟨U, V, ⟨hU, hV, h⟩, A.sortedSingularValues_antitone, A.sortedSingularValues_nonneg⟩

/-! ### §2.4.2 Properties -/

/-- If `Matrix.IsSVD A U σ V`, then $A v_j = \sigma_j u_j$ for every column index $j$ with $j < m$.
-/
private theorem mulVec_col_of_isSVD {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (j : Fin n)
    (hj : (j : ℕ) < m) : A *ᵥ V.col j = σ j • U.col ⟨j, hj⟩ := by
  have hVV : star V * V = 1 := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
  have hAV : A * V = U * (rectDiagonal fun i => σ i : Matrix (Fin m) (Fin n) ℝ) := by
    conv_lhs => rw [h.eq_mul_mul_star]
    rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
    simp only [RCLike.ofReal_real_eq_id, id]
  funext a
  change (A * V) a j = σ j * U a ⟨j, hj⟩
  rw [hAV, mul_rectDiagonal_apply]
  simp [hj, mul_comm]

/-- **Corollary 2.4.2** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$ with $m \ge n$. Then for $i = 1, \dots, n$,
$$A v_i = \sigma_i u_i, \qquad A^T u_i = \sigma_i v_i.$$

The SVD is `Matrix.IsSVD A U σ V`. The index $i$ is 0-based in `Fin n`, and $u_i$ is the column
`U.col (Fin.castLE hmn i)`. -/
theorem corollary_2_4_2 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (hmn : n ≤ m) (i : Fin n) :
    A *ᵥ V.col i = σ i • U.col (Fin.castLE hmn i) ∧
      Aᵀ *ᵥ U.col (Fin.castLE hmn i) = σ i • V.col i := by
  refine ⟨mulVec_col_of_isSVD h i (lt_of_lt_of_le i.isLt hmn), ?_⟩
  have h' := h.conjTranspose
  rw [conjTranspose_eq_transpose_of_trivial] at h'
  exact mulVec_col_of_isSVD h' (Fin.castLE hmn i) i.isLt

/-- **Equation (2.4.1)** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$ with $m \ge n$. Then for $i = 1, \dots, n$,
$$A^T A v_i = \sigma_i^2 v_i.$$
-/
theorem equation_2_4_1 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (hmn : n ≤ m) (i : Fin n) :
    (Aᵀ * A) *ᵥ V.col i = σ i ^ 2 • V.col i := by
  obtain ⟨h1, h2⟩ := corollary_2_4_2 h hmn i
  rw [← mulVec_mulVec, h1, mulVec_smul, h2, smul_smul, sq]

/-- **Equation (2.4.2)** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$ with $m \ge n$. Then for $i = 1, \dots, n$,
$$A A^T u_i = \sigma_i^2 u_i.$$
-/
theorem equation_2_4_2 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (hmn : n ≤ m) (i : Fin n) :
    (A * Aᵀ) *ᵥ U.col (Fin.castLE hmn i) = σ i ^ 2 • U.col (Fin.castLE hmn i) := by
  obtain ⟨h1, h2⟩ := corollary_2_4_2 h hmn i
  rw [← mulVec_mulVec, h2, mulVec_smul, h1, smul_smul, sq]

/-- For $A \in \mathbb{R}^{m \times n}$, $\sigma_1(A) = \|A\|_2$. -/
private theorem sortedSingularValues_zero_eq_lpOpNorm (A : Matrix (Fin m) (Fin n) ℝ) :
    A.sortedSingularValues 0 = lpOpNorm 2 A :=
  (sortedSingularValues_zero_eq_l2_opNorm A).trans (lpOpNorm_two A).symm

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Corollary 2.4.3** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$ and
$p = \min\{m, n\}$,
$$\|A\|_2 = \sigma_1, \qquad \|A\|_F = \sqrt{\sigma_1^2 + \dots + \sigma_p^2}.$$

The singular value $\sigma_i$ is `A.sortedSingularValues (i - 1)`. -/
theorem corollary_2_4_3 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 2 A = A.sortedSingularValues 0 ∧
      ‖A‖ = √(∑ i ∈ Finset.range (min m n), A.sortedSingularValues i ^ 2) := by
  refine ⟨(sortedSingularValues_zero_eq_lpOpNorm A).symm, ?_⟩
  rw [← Real.sqrt_sq (norm_nonneg A), frobenius_norm_sq_eq_sum_sq_sortedSingularValues,
    Fintype.card_fin]
  congr 1
  refine (Finset.sum_subset (Finset.range_mono (min_le_right m n)) fun i _ hi => ?_).symm
  rw [Finset.mem_range, not_lt] at hi
  rw [sortedSingularValues_eq_zero_of_min_le A (by simpa using hi), zero_pow two_ne_zero]

end Frobenius

/-- **Corollary 2.4.4** of [golub2013matrix]. For $A, E \in \mathbb{R}^{m \times n}$,
$$\sigma_{\max}(A + E) \le \sigma_{\max}(A) + \|E\|_2, \qquad \sigma_{\min}(A + E) \ge
  \sigma_{\min}(A) - \|E\|_2.$$

Both bounds are instances of Weyl's inequality $\sigma_{i+j-1}(A + B) \le \sigma_i(A) +
\sigma_j(B)$, `Matrix.sortedSingularValues_add_le`. The proof needs no hypothesis $m \ge n$. -/
theorem corollary_2_4_4 (A E : Matrix (Fin m) (Fin n) ℝ) :
    sigmaMax (A + E) ≤ sigmaMax A + lpOpNorm 2 E ∧
      sigmaMin A - lpOpNorm 2 E ≤ sigmaMin (A + E) := by
  refine ⟨?_, ?_⟩
  · have h := sortedSingularValues_add_le A E 0 0
    rwa [sortedSingularValues_zero_eq_lpOpNorm E] at h
  · have h := sortedSingularValues_add_le (A + E) (-E) (min m n - 1) 0
    rw [add_zero, add_neg_cancel_right, sortedSingularValues_zero_eq_lpOpNorm,
      lpOpNorm_neg] at h
    rw [sigmaMin, sigmaMin]
    linarith

/-- **Corollary 2.4.5** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with
$m > n \ge 1$, and let $z \in \mathbb{R}^m$. Then
$$\sigma_{\max}([A \mid z]) \ge \sigma_{\max}(A), \qquad \sigma_{\min}([A \mid z]) \le
  \sigma_{\min}(A).$$

**Reading.** The source assumes only $m > n$. For $n = 0$ the source does not define
$\sigma_{\min}(A)$, and the Lean value $0$ would make the second inequality false. So the
corollary assumes $n \ge 1$.

The matrix $[A \mid z]$ is `Matrix.of fun i => Fin.snoc (A i) (z i)`. The first inequality is
column deletion, `Matrix.sortedSingularValues_submatrix_le`. For the second, both matrices have
at least as many rows as columns, so $\sigma_{\min}$ is the least stretch
$\min_{\|x\|_2 = 1} \|Ax\|_2$ (`Matrix.iInf_colSingularValues_eq_iInf_norm`), and $[A \mid z]
\begin{bmatrix} x \\ 0 \end{bmatrix} = Ax$. -/
theorem corollary_2_4_5 (A : Matrix (Fin m) (Fin n) ℝ) (hmn : n < m) (hn : 1 ≤ n)
    (z : Fin m → ℝ) :
    sigmaMax A ≤ sigmaMax (Matrix.of fun i => Fin.snoc (α := fun _ => ℝ) (A i) (z i) :
      Matrix (Fin m) (Fin (n + 1)) ℝ) ∧
    sigmaMin (Matrix.of fun i => Fin.snoc (α := fun _ => ℝ) (A i) (z i) :
      Matrix (Fin m) (Fin (n + 1)) ℝ) ≤ sigmaMin A := by
  set Ã : Matrix (Fin m) (Fin (n + 1)) ℝ :=
    Matrix.of fun i => Fin.snoc (α := fun _ => ℝ) (A i) (z i) with hÃ
  have hsub : Ã.submatrix id Fin.castSucc = A := by
    ext i j
    simp [hÃ]
  refine ⟨?_, ?_⟩
  · calc sigmaMax A = (Ã.submatrix id Fin.castSucc).sortedSingularValues 0 := by rw [hsub]; rfl
      _ ≤ Ã.sortedSingularValues 0 := sortedSingularValues_submatrix_le Ã Function.injective_id
        (Fin.castSucc_injective _) 0
  · have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨x, hx1, hx⟩ := A.exists_norm_eq_iInf_colSingularValues
    have hmin1 : min m n - 1 = Fintype.card (Fin n) - 1 := by
      rw [Fintype.card_fin, min_eq_right hmn.le]
    have hmin2 : min m (n + 1) - 1 = Fintype.card (Fin (n + 1)) - 1 := by
      rw [Fintype.card_fin, min_eq_right hmn]
    rw [sigmaMin, sigmaMin, hmin1, hmin2, sortedSingularValues_eq_iInf_colSingularValues,
      sortedSingularValues_eq_iInf_colSingularValues, iInf_colSingularValues_eq_iInf_norm, ← hx]
    set y : EuclideanSpace ℝ (Fin (n + 1)) :=
      toLp 2 (Function.extend Fin.castSucc (ofLp x) 0) with hy
    have hy1 : ‖y‖ = 1 := by
      rw [← hx1, hy, PiLp.norm_toLp_extend 2 (Fin.castSucc_injective n), toLp_ofLp]
    have hAy : toEuclideanLin Ã y = toEuclideanLin A x := by
      have h := submatrix_mulVec_eq_comp_mulVec_extend Ã id (Fin.castSucc_injective n) (ofLp x)
      rw [hsub, Function.comp_id] at h
      rw [hy, toEuclideanLin_toLp, toEuclideanLin_apply, h]
    have hbdd : BddBelow (Set.range fun v : {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} =>
        ‖toEuclideanLin Ã v‖) := ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩
    calc (⨅ v : {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1}, ‖toEuclideanLin Ã v‖)
        ≤ ‖toEuclideanLin Ã y‖ := ciInf_le hbdd ⟨y, hy1⟩
      _ = ‖toEuclideanLin A x‖ := by rw [hAy]

/-- A vector of `EuclideanSpace` lies in the span of the images of a set $s$ of vectors if and only
if the underlying vector lies in the span of $s$. -/
private theorem mem_span_toLp_image_iff {k : ℕ} (s : Set (Fin k → ℝ))
    (x : EuclideanSpace ℝ (Fin k)) :
    x ∈ Submodule.span ℝ (toLp 2 '' s) ↔ ofLp x ∈ Submodule.span ℝ s := by
  have h : (toLp 2 '' s : Set (EuclideanSpace ℝ (Fin k))) =
      (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm '' s := rfl
  rw [h, Submodule.span_image_linearEquiv, Submodule.mem_map_equiv]
  rfl

/-- **Corollary 2.4.6** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$, let $p = \min\{m, n\}$, and let $r \le p$ be such that for
$i = 1, \dots, p$ we have $\sigma_i > 0$ if and only if $i \le r$. Then
$$\operatorname{rank}(A) = r, \qquad \operatorname{null}(A) = \operatorname{span}\{v_{r+1},
  \dots, v_n\}, \qquad \operatorname{ran}(A) = \operatorname{span}\{u_1, \dots, u_r\}.$$

The indices are 0-based in Lean: the hypothesis is $0 < \sigma_i \iff i < r$ for $i < p$, and
the spans are over the columns $j \ge r$ of $V$ and the columns $i < r$ of $U$. The proof
applies `Matrix.IsSVD.ker_mulVecLin_eq_span`, `Matrix.IsSVD.range_mulVecLin_eq_span` and
`Matrix.sortedSingularValues_eq_zero_iff_rank_le`. -/
theorem corollary_2_4_6 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {r : ℕ} (hr : r ≤ min m n)
    (hσ : ∀ i < min m n, 0 < σ i ↔ i < r) :
    A.rank = r ∧
      LinearMap.ker (toEuclideanLin A) =
        Submodule.span ℝ ((fun j => toLp 2 (V.col j)) '' {j : Fin n | r ≤ (j : ℕ)}) ∧
      LinearMap.range (toEuclideanLin A) =
        Submodule.span ℝ ((fun i => toLp 2 (U.col i)) '' {i : Fin m | (i : ℕ) < r}) := by
  have hs : ∀ i < min m n, σ i = A.sortedSingularValues i := fun i hi =>
    h.singularValues_eq (lt_of_lt_of_le hi (min_le_left _ _))
      (lt_of_lt_of_le hi (min_le_right _ _))
  refine ⟨le_antisymm ?_ ?_, ?_, ?_⟩
  · rcases lt_or_eq_of_le hr with hlt | heq
    · have h0 : σ r = 0 :=
        le_antisymm (not_lt.1 fun hpos => lt_irrefl r ((hσ r hlt).1 hpos)) (h.nonneg r)
      rwa [hs r hlt, sortedSingularValues_eq_zero_iff_rank_le] at h0
    · rw [heq]
      exact le_min A.rank_le_height A.rank_le_width
  · by_contra hlt
    push Not at hlt
    have hr1 : r - 1 < min m n := by omega
    have hpos := (hσ (r - 1) hr1).2 (by omega)
    rw [hs _ hr1, (sortedSingularValues_eq_zero_iff_rank_le A (r - 1)).2 (by omega)] at hpos
    exact lt_irrefl 0 hpos
  · have hset : {j : Fin n | m ≤ (j : ℕ) ∨ σ j = 0} = {j : Fin n | r ≤ (j : ℕ)} := by
      ext j
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro (hj | hj)
        · exact le_trans (le_trans hr (min_le_left _ _)) hj
        · by_contra hjr
          push Not at hjr
          have hjp : (j : ℕ) < min m n := lt_of_lt_of_le hjr hr
          exact lt_irrefl 0 (hj ▸ (hσ j hjp).2 hjr)
      · intro hj
        by_cases hjm : m ≤ (j : ℕ)
        · exact Or.inl hjm
        · refine Or.inr (le_antisymm (not_lt.1 fun hpos => ?_) (h.nonneg j))
          have := (hσ j (lt_min (not_le.1 hjm) j.isLt)).1 hpos
          omega
    ext x
    rw [← Set.image_image (toLp 2) (fun j => V.col j), mem_span_toLp_image_iff, ← hset,
      show (fun j => V.col j) = Vᵀ from rfl, ← h.ker_mulVecLin_eq_span, LinearMap.mem_ker,
      LinearMap.mem_ker, mulVecLin_apply, toEuclideanLin_apply, WithLp.toLp_eq_zero]
  · have hset : {i : Fin m | (i : ℕ) < n ∧ σ i ≠ 0} = {i : Fin m | (i : ℕ) < r} := by
      ext i
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hin, hi⟩
        exact (hσ i (lt_min i.isLt hin)).1 (lt_of_le_of_ne (h.nonneg i) (Ne.symm hi))
      · intro hi
        have hip : (i : ℕ) < min m n := lt_of_lt_of_le hi hr
        exact ⟨lt_of_lt_of_le hip (min_le_right _ _), ((hσ i hip).2 hi).ne'⟩
    ext x
    rw [← Set.image_image (toLp 2) (fun i => U.col i), mem_span_toLp_image_iff, ← hset,
      show (fun i => U.col i) = Uᵀ from rfl, ← h.range_mulVecLin_eq_span]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨ofLp y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨toLp 2 y, by rw [toEuclideanLin_toLp]; exact congrArg (toLp 2) hy⟩

/-- The truncation (2.4.3) is a sum of rank-one matrices: $U \Sigma_k V^T = \sum_{i=1}^k \sigma_i
u_i v_i^T$ for $k \le \min\{m, n\}$. -/
private theorem svdTruncation_eq_sum (U : Matrix (Fin m) (Fin m) ℝ) (σ : ℕ → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    svdTruncation U σ V k =
      ∑ i : Fin k, σ i • vecMulVec (U.col (Fin.castLE hkm i)) (V.col (Fin.castLE hkn i)) := by
  ext a b
  simp only [svdTruncation, RCLike.ofReal_real_eq_id, id]
  rw [Matrix.mul_apply, Matrix.sum_apply]
  have hg : ∀ j : Fin n,
      (U * (rectDiagonal (fun i => if i < k then σ i else 0) :
        Matrix (Fin m) (Fin n) ℝ)) a j * star V j b =
        if (j : ℕ) < k then (if h : (j : ℕ) < m then U a ⟨j, h⟩ * σ j else 0) * V b j
        else 0 := by
    intro j
    rw [mul_rectDiagonal_apply]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => hg j, ← Fin.sum_castLE_eq_sum_ite hkn]
  refine Finset.sum_congr rfl fun i _ => ?_
  have him : (i : ℕ) < m := lt_of_lt_of_le i.isLt hkm
  simp only [Fin.val_castLE, him, ↓reduceDIte, Matrix.smul_apply, vecMulVec_apply, col_apply,
    smul_eq_mul]
  rw [show (⟨i, him⟩ : Fin m) = Fin.castLE hkm i from rfl]
  ring

open scoped Matrix.Norms.L2Operator in
/-- **Corollary 2.4.7** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have rank $r$, and
let $U^T A V = \Sigma$ be any SVD of $A$. Then
$$A = \sum_{i=1}^r \sigma_i u_i v_i^T.$$

The proof uses that the truncation at the rank has the residual norm
$\|A - A_r\|_2 = \sigma_{r+1} = 0$ (`Matrix.l2_opNorm_sub_svdTruncation`). -/
theorem corollary_2_4_7 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) :
    A = ∑ i : Fin A.rank, σ i • vecMulVec (U.col (Fin.castLE A.rank_le_height i))
      (V.col (Fin.castLE A.rank_le_width i)) := by
  rw [← svdTruncation_eq_sum]
  have h0 := l2_opNorm_sub_svdTruncation h A.rank
  rw [(sortedSingularValues_eq_zero_iff_rank_le A A.rank).2 le_rfl, norm_eq_zero,
    sub_eq_zero] at h0
  exact h0

/-- **Theorem 2.4.8** of [golub2013matrix] (Eckart–Young), with (2.4.3) and (2.4.4). Let
$U^T A V = \Sigma$ be an SVD of $A \in \mathbb{R}^{m \times n}$, and let
$k < r = \operatorname{rank}(A)$. Let
$$A_k = \sum_{i=1}^k \sigma_i u_i v_i^T$$
as in (2.4.3). Then $\operatorname{rank}(A_k) = k$ and, as in (2.4.4),
$$\min_{\operatorname{rank}(B) = k} \|A - B\|_2 = \|A - A_k\|_2 = \sigma_{k+1}.$$

The matrix $A_k$ is `Matrix.svdTruncation U σ V k`, and the theorem also states that it equals
the sum (2.4.3). The value $\sigma_{k+1}$ is `σ k` with 0-based indices. The minimum is an
`IsLeast` statement over the matrices of rank exactly $k$. The proof applies
`Matrix.rank_svdTruncation`, `Matrix.l2_opNorm_sub_svdTruncation` and the lower bound
`Matrix.sortedSingularValues_le_l2_opNorm_sub_of_rank_le`. -/
theorem theorem_2_4_8 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {k : ℕ} (hk : k < A.rank) :
    svdTruncation U σ V k =
        ∑ i : Fin k, σ i • vecMulVec (U.col (Fin.castLE (hk.le.trans A.rank_le_height) i))
          (V.col (Fin.castLE (hk.le.trans A.rank_le_width) i)) ∧
      (svdTruncation U σ V k).rank = k ∧
      lpOpNorm 2 (A - svdTruncation U σ V k) = σ k ∧
      IsLeast ((fun B => lpOpNorm 2 (A - B)) '' {B | B.rank = k}) (σ k) := by
  have hσk : σ k = A.sortedSingularValues k :=
    h.singularValues_eq (lt_of_lt_of_le hk A.rank_le_height)
      (lt_of_lt_of_le hk A.rank_le_width)
  have hnorm : lpOpNorm 2 (A - svdTruncation U σ V k) = σ k := by
    rw [lpOpNorm_two, l2_opNorm_sub_svdTruncation h k, hσk]
  have hrank := rank_svdTruncation h hk.le
  refine ⟨svdTruncation_eq_sum U σ V _ _, hrank, hnorm, ⟨⟨_, hrank, hnorm⟩, ?_⟩⟩
  rintro _ ⟨B, hB, rfl⟩
  rw [hσk]
  dsimp only
  rw [lpOpNorm_two]
  exact sortedSingularValues_le_l2_opNorm_sub_of_rank_le (le_of_eq hB)

/-- **Section 2.4.2** of [golub2013matrix], after Theorem 2.4.8: the smallest singular value of $A$
is the 2-norm distance from $A$ to the set of all rank-deficient matrices. Let
$A \in \mathbb{R}^{m \times n}$ with $m, n \ge 1$. Then
$$\sigma_{\min}(A) = \min \{ \|A - B\|_2 : B \in \mathbb{R}^{m \times n}, \
  \operatorname{rank}(B) < \min\{m, n\} \}.$$

**Reading.** The source states the remark with no condition on the shape. For $m = 0$ or $n = 0$
there is no rank-deficient matrix, so the statement assumes $m, n \ge 1$.

Rank deficiency is `GolubVanLoan.Chapter02.IsRankDeficient` of §2.1. The proof is the
Eckart–Young theorem at $k = p - 1$, `Matrix.isLeast_l2_opNorm_sub_of_rank_le`. -/
theorem sigmaMin_eq_dist_rankDeficient (A : Matrix (Fin m) (Fin n) ℝ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    IsLeast ((fun B => lpOpNorm 2 (A - B)) '' {B | IsRankDeficient B}) (sigmaMin A) := by
  have hset : {B : Matrix (Fin m) (Fin n) ℝ | IsRankDeficient B} =
      {B | B.rank ≤ min m n - 1} := by
    ext B
    change B.rank < min m n ↔ B.rank ≤ min m n - 1
    have : 1 ≤ min m n := le_min hm hn
    omega
  have hfun : (fun B : Matrix (Fin m) (Fin n) ℝ => lpOpNorm 2 (A - B)) =
      fun B => lpOpNorm 2 (A - B) := rfl
  rw [hset, hfun]
  have h := isLeast_l2_opNorm_sub_of_rank_le A (min m n - 1)
  simp only [← lpOpNorm_two] at h
  exact h

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Section 2.4.2** of [golub2013matrix], after Theorem 2.4.8: the Eckart–Young theorem in the
Frobenius norm. Let $U^T A V = \Sigma$ be an SVD of $A \in \mathbb{R}^{m \times n}$, let
$p = \min\{m, n\}$, let $k < \operatorname{rank}(A)$, and let $A_k$ be the truncation (2.4.3).
Then $A_k$ is a closest matrix of rank $k$ to $A$ in the Frobenius norm, and
$$\|A - A_k\|_F = \sqrt{\sigma_{k+1}^2 + \dots + \sigma_p^2}.$$

The source states this result without proof; it is due to Mirsky. The proof applies
`Matrix.isLeast_frobenius_norm_sub_of_rank_le` and `Matrix.frobenius_norm_sub_svdTruncation`. -/
theorem svdTruncation_isLeast_frobenius {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V)
    {k : ℕ} (hk : k < A.rank) :
    IsLeast ((fun B => ‖A - B‖) '' {B | B.rank = k}) ‖A - svdTruncation U σ V k‖ ∧
      ‖A - svdTruncation U σ V k‖ = √(∑ i ∈ Finset.Ico k (min m n), σ i ^ 2) := by
  have hval : ‖A - svdTruncation U σ V k‖ = √(∑ i ∈ Finset.Ico k (min m n), σ i ^ 2) := by
    rw [frobenius_norm_sub_svdTruncation h k]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := (Finset.mem_Ico.1 hi).2
    rw [h.singularValues_eq (lt_of_lt_of_le hi' (min_le_left _ _))
      (lt_of_lt_of_le hi' (min_le_right _ _))]
  refine ⟨⟨⟨_, rank_svdTruncation h hk.le, rfl⟩, ?_⟩, hval⟩
  rintro _ ⟨B, hB, rfl⟩
  have hlb := (isLeast_frobenius_norm_sub_of_rank_le A k).2 ⟨B, le_of_eq hB, rfl⟩
  rw [frobenius_norm_sub_svdTruncation h k]
  simpa only [Fintype.card_fin] using hlb

end Frobenius

/-! ### §2.4.3 The thin SVD -/

/-- **Section 2.4.3** of [golub2013matrix], the thin SVD. Let $A = U \Sigma V^T$ be an SVD of
$A \in \mathbb{R}^{m \times n}$ with $m \ge n$. Let $U_1 = U(:, 1{:}n)$ and $\Sigma_1 =
\Sigma(1{:}n, 1{:}n) = \operatorname{diag}(\sigma_1, \dots, \sigma_n)$. Then $U_1$ has
orthonormal columns, $U_1^T U_1 = I$, and
$$A = U_1 \Sigma_1 V^T.$$

The block $U_1$ is `U.submatrix id (Fin.castLE hmn)`. -/
theorem thin_svd {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (hmn : n ≤ m) :
    (U.submatrix id (Fin.castLE hmn))ᵀ * U.submatrix id (Fin.castLE hmn) = 1 ∧
      A = U.submatrix id (Fin.castLE hmn) * diagonal (fun i : Fin n => σ i) * Vᵀ := by
  refine ⟨?_, ?_⟩
  · have h1 := conjTranspose_submatrix_castLE_mul_self hmn h.mem_unitaryGroup_left
    rwa [conjTranspose_eq_transpose_of_trivial] at h1
  · conv_lhs => rw [h.eq_mul_mul_star, mul_rectDiagonal_eq_submatrix_mul_diagonal hmn]
    simp [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-! ### §2.4.4 Unitary matrices and the complex SVD -/

section Complex

open scoped Matrix.Norms.Frobenius

/-- **Section 2.4.4** of [golub2013matrix], the complex SVD. For $A \in \mathbb{C}^{m \times n}$
there are unitary matrices $U \in \mathbb{C}^{m \times m}$ and $V \in \mathbb{C}^{n \times n}$
with
$$U^H A V = \operatorname{diag}(\sigma_1, \dots, \sigma_p) \in \mathbb{R}^{m \times n}, \qquad
  p = \min\{m, n\},$$
where $\sigma_1 \ge \dots \ge \sigma_p \ge 0$. Moreover, for unitary
$Q \in \mathbb{C}^{m \times m}$ and $Z \in \mathbb{C}^{n \times n}$,
$$\|QAZ\|_2 = \|A\|_2, \qquad \|QAZ\|_F = \|A\|_F.$$

The SVD is `Matrix.IsSVD A U A.sortedSingularValues V` over $\mathbb{C}$. The remark of the
source that "all of the real SVD properties have obvious complex analogs" is the `RCLike`
generality of the backbone. -/
theorem complex_svd (A : Matrix (Fin m) (Fin n) ℂ) :
    (∃ U V, IsSVD A U A.sortedSingularValues V) ∧
      ∀ {Q : Matrix (Fin m) (Fin m) ℂ} {Z : Matrix (Fin n) (Fin n) ℂ},
        Q ∈ unitaryGroup (Fin m) ℂ → Z ∈ unitaryGroup (Fin n) ℂ →
          lpOpNorm 2 (Q * A * Z) = lpOpNorm 2 A ∧ ‖Q * A * Z‖ = ‖A‖ := by
  refine ⟨?_, fun hQ hZ => ⟨?_, frobenius_norm_unitary_mul_mul_unitary hQ A hZ⟩⟩
  · obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
    exact ⟨U, V, ⟨hU, hV, h⟩, A.sortedSingularValues_antitone, A.sortedSingularValues_nonneg⟩
  · rw [lpOpNorm_two, lpOpNorm_two]
    exact l2_opNorm_unitary_mul_mul_unitary hQ A hZ

end Complex

end GolubVanLoan.Chapter02
