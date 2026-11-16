/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Cauchy–Binet formula

This file expresses the determinant of a product of rectangular matrices as a sum over selections of
columns and rows, over any commutative ring $R$. Let $P \in R^{p \times m}$ and
$Q \in R^{m \times p}$, so that $PQ$ is a square matrix of order $p$. For a map
$r \colon \{1, \dots, p\} \to \{1, \dots, m\}$, write $P_{:, r}$ for the $p \times p$ matrix with
the columns $r(1), \dots, r(p)$ of $P$, and $Q_{r, :}$ for the $p \times p$ matrix with the rows
$r(1), \dots, r(p)$ of $Q$. The Cauchy–Binet formula, in the form proved here, is
$$p! \, \det(PQ) = \sum_{r} \det(P_{:, r}) \det(Q_{r, :}),$$
where the sum runs over all maps $r$.

## Main results

* `Matrix.det_mul_eq_sum_prod_mul_det_submatrix`: $\det(PQ) = \sum_r \bigl(\prod_i Q_{r(i), i}\bigr)
  \det(P_{:, r})$.
* `Matrix.factorial_mul_det_mul`: the **Cauchy–Binet formula** $p! \det(PQ) = \sum_r \det(P_{:, r})
  \det(Q_{r, :})$.
* `Matrix.factorial_mul_det_transpose_mul_diagonal_mul`: the case of a weighted Gram matrix, $p!
  \det(X^T D Y) = \sum_r \bigl(\prod_i d_{r(i)}\bigr) \det(X_{r, :}) \det(Y_{r, :})$.

## Implementation notes

* The formula is symmetrized over the orderings of the selected indices: the sum runs over all maps
  $r \colon p \to m$, not over the $p$-element subsets of $m$. A map $r$ that is not injective
  contributes $0$, because two selected columns are equal. Each $p$-element subset is counted $p!$
  times, with the same sign in both determinants, and this gives the factor $p!$. The statement and
  the proof then need no sorted subsets and no reindexing.
* The matrices are indexed by finite types `p` and `m`. The Lean terms `P.submatrix id r` and
  `Q.submatrix r id` are the matrices $P_{:, r}$ and $Q_{r, :}$.
-/

namespace Matrix

section CauchyBinet

variable {R : Type*} [CommRing R] {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p]
  [DecidableEq p]

omit [DecidableEq m] in
/-- Let $R$ be a commutative ring, let $P \in R^{p \times m}$ and let $Q \in R^{m \times p}$. Then
$$\det(PQ) = \sum_{r \colon p \to m} \Bigl(\prod_{i} Q_{r(i), i}\Bigr) \det(P_{:, r}),$$
where the sum runs over all maps $r$ from the index set of $p$ to the index set of $m$, and
$P_{:, r}$ is the square matrix with the columns $r(1), \dots, r(p)$ of $P$.

This is the first step of the proof of Mathlib's `Matrix.det_mul`, for rectangular factors. The
matrix $P_{:, r}$ is `P.submatrix id r`. -/
theorem det_mul_eq_sum_prod_mul_det_submatrix (P : Matrix p m R) (Q : Matrix m p R) :
    (P * Q).det = ∑ r : p → m, (∏ i, Q (r i) i) * (P.submatrix id r).det := by
  simp only [det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
    Fintype.piFinset_univ, submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

omit [DecidableEq m] in
/-- The **Cauchy–Binet formula**. Let $R$ be a commutative ring, let $P \in R^{p \times m}$ and let
$Q \in R^{m \times p}$. Then
$$p! \, \det(PQ) = \sum_{r \colon p \to m} \det(P_{:, r}) \det(Q_{r, :}),$$
where the sum runs over all maps $r$ from the index set of $p$ to the index set of $m$,
$P_{:, r}$ is the square matrix with the columns $r(1), \dots, r(p)$ of $P$, and $Q_{r, :}$ is
the square matrix with the rows $r(1), \dots, r(p)$ of $Q$.

A map $r$ that is not injective contributes $0$, and each $p$-element set of indices is counted
$p!$ times, with the same sign in both determinants. The matrices $P_{:, r}$ and $Q_{r, :}$ are
`P.submatrix id r` and `Q.submatrix r id`. The proof rewrites
`Matrix.det_mul_eq_sum_prod_mul_det_submatrix` for each ordering $\sigma$ of the selection, with
a sign, and the sum over $\sigma$ gives $\det(Q_{r, :})$. -/
theorem factorial_mul_det_mul (P : Matrix p m R) (Q : Matrix m p R) :
    ((Fintype.card p).factorial : R) * (P * Q).det =
      ∑ r : p → m, (P.submatrix id r).det * (Q.submatrix r id).det := by
  have h2 : ∀ σ : Equiv.Perm p, (P * Q).det = ∑ r : p → m,
      (Equiv.Perm.sign σ : R) * (∏ i, Q (r (σ i)) i) * (P.submatrix id r).det := fun σ => by
    rw [det_mul_eq_sum_prod_mul_det_submatrix]
    rw [← (Equiv.arrowCongr σ.symm (Equiv.refl m)).sum_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    have e1 : (Equiv.arrowCongr σ.symm (Equiv.refl m) r) = r ∘ σ := by
      funext i
      simp
    have e3 : (P.submatrix id (r ∘ σ)).det = (Equiv.Perm.sign σ : R) * (P.submatrix id r).det := by
      have : P.submatrix id (r ∘ σ) = (P.submatrix id r).submatrix id σ := rfl
      rw [this, det_permute']
    rw [e1, e3]
    simp only [Function.comp_apply]
    ring
  have hsum : ((Fintype.card p).factorial : R) * (P * Q).det =
      ∑ σ : Equiv.Perm p, (P * Q).det := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  rw [hsum, Finset.sum_congr rfl fun σ _ => h2 σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [det_apply' (Q.submatrix r id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id]
  ring

/-- The **Cauchy–Binet formula for a weighted Gram matrix**. Let $R$ be a commutative ring, let
$X, Y \in R^{m \times p}$, let $d \in R^m$, and let $D = \operatorname{diag}(d)$. Then
$$p! \, \det(X^T D Y) = \sum_{r \colon p \to m} \Bigl(\prod_{i} d_{r(i)}\Bigr) \det(X_{r, :})
  \det(Y_{r, :}),$$
where the sum runs over all maps $r$ from the index set of $p$ to the index set of $m$, and
$X_{r, :}$ is the square matrix with the rows $r(1), \dots, r(p)$ of $X$.

This is the case $P = X^T D$, $Q = Y$ of `Matrix.factorial_mul_det_mul`. The matrix $X_{r, :}$
is `X.submatrix r id`. -/
theorem factorial_mul_det_transpose_mul_diagonal_mul (X Y : Matrix m p R) (d : m → R) :
    ((Fintype.card p).factorial : R) * (Xᵀ * diagonal d * Y).det =
      ∑ r : p → m, (∏ i, d (r i)) * (X.submatrix r id).det * (Y.submatrix r id).det := by
  rw [factorial_mul_det_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  have : (Xᵀ * diagonal d).submatrix id r = (X.submatrix r id)ᵀ * diagonal fun i => d (r i) := by
    ext i j
    simp [mul_diagonal]
  rw [this, det_mul, det_transpose, det_diagonal, mul_comm (X.submatrix r id).det]

end CauchyBinet

end Matrix
