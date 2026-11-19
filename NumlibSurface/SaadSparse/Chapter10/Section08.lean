/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Preconditioner.ILU
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 10.8: Preconditioners for the normal equations

This module formalizes Section 10.8.3 of [saad2003iterative], the incomplete Gram–Schmidt process.
Algorithm 10.17 runs the Gram–Schmidt process on the rows $a_1, a_2, \dots$ of a matrix $A$ and
drops the coefficients $l_{ij}$ with $(i, j)$ in a set $P_L$. It computes
$\hat{q}_i = a_i - \sum_{j < i} l_{ij} q_j$ with $l_{ij} = (a_i, q_j)$ for the retained $j$, then
$l_{ii} = \|\hat{q}_i\|_2$ and $q_i = \hat{q}_i / l_{ii}$. Because the subtracted vector is built
from the retained coefficients, $a_i = \sum_{j \le i} l_{ij} q_j$ holds however much is dropped, so
$A = LQ$ is an exact factorization (Proposition 10.17); what is lost is the orthogonality of $Q$.

Theorem 10.18 compares the factor $L$ with incomplete Cholesky. If $P_L$ is symmetric, avoids the
diagonal, and satisfies the condition of the theorem, then the rows of $Q$ that are retained in one
row of $L$ are pairwise orthogonal. Then the cross terms of $(a_i, a_j)$ vanish, and $L L^T$ agrees
with $B = A A^T$ off $P_L$: $L$ is an incomplete Cholesky factor of $B$ for $P_L$. The book states
the theorem without proof and cites the literature; the proof here is an induction over the rows
(`SaadSparse.Chapter10.IsICPattern.inner_imgsQ_eq_zero`). Incomplete Cholesky factorizations are
`Matrix.IsIC` of `Numlib.Preconditioner.ILU`.

## Main definitions

* Algorithm 10.17, `SaadSparse.Chapter10.imgsHat`: the vector $\hat{q}_i$ of line 4.
* Algorithm 10.17, `SaadSparse.Chapter10.imgsQ`: the normalized vector $q_i$ of line 7.
* Algorithm 10.17, `SaadSparse.Chapter10.imgsL`: the coefficients $l_{ij}$ of lines 2, 3 and 6.
* Algorithm 10.17, `SaadSparse.Chapter10.imgsLMat`: the lower triangular factor $L$.
* Algorithm 10.17, `SaadSparse.Chapter10.imgsQMat`: the factor $Q$ with the rows $q_i$.
* Theorem 10.18, `SaadSparse.Chapter10.IsICPattern`: the hypothesis on the zero pattern $P_L$.

## Main results

* Proposition 10.17, `SaadSparse.Chapter10.proposition_10_17`: for a nonsingular $A$, Algorithm
  10.17 does not break down and gives an exact factorization $A = LQ$.
* Theorem 10.18, `SaadSparse.Chapter10.theorem_10_18`: the factor $L$ of Algorithm 10.17 is an
  incomplete Cholesky factor of $A A^T$ for $P_L$.

## Conventions

* $A$ is an $n \times m$ matrix, as in Theorem 10.18; Proposition 10.17, which the book states for a
  nonsingular $A$, is the square case.
* Indices are $0$-based: `imgsQ A dropL j` is the book's $q_{j+1}$. The rows are indexed by the
  natural numbers and are $0$ past $n$, so that the recursion of Algorithm 10.17 needs no dependent
  arithmetic.
* The set $P_L$ is the predicate `dropL : ℕ → ℕ → Bool`: `dropL i j = true` means that $l_{ij}$ is
  dropped.
* Saad's inner product $(x, y)$ is Mathlib's `inner 𝕜 y x`, so $l_{ij} = (a_i, q_j)$ is
  `inner 𝕜 (imgsQ A dropL j) (rowVec A i)`.

## Implementation notes

* No dropping is applied to $Q$: line 5 of Algorithm 10.17 is not modelled. This is the hypothesis
  $P_Q = \emptyset$ of Proposition 10.17.
* The book's "if $l_{ii} = 0$ then Stop" is Lean's $x / 0 = 0$: at a breakdown $q_i = 0$.
* Section 10.8.1 (CGNE and CGNR with SSOR) constructs no new object: it is the normal equations of
  `Numlib.Krylov.NormalEquations` with the SSOR splitting of $A A^T$ or $A^T A$. Its only claim,
  that the methods do not break down because $A^T A$ and $A A^T$ are positive definite for a
  nonsingular $A$, is `Krylov.adjoint_comp_isSymmetricCoercive`.

## Deviations from the source

* **Totalization.** Natural-index row selection returns zero outside the matrix. See
  `SaadSparse.Chapter10.rowVec`.
* **Scope.** The incomplete Gram–Schmidt recurrence drops entries only from $L$, uses complex inner
  products and totalizes normalization. See `SaadSparse.Chapter10.imgsHat`,
  `SaadSparse.Chapter10.imgsQ`, `SaadSparse.Chapter10.imgsL`, `SaadSparse.Chapter10.imgsLMat`,
  `SaadSparse.Chapter10.imgsQMat`, `SaadSparse.Chapter10.imgsL_of_gt`,
  `SaadSparse.Chapter10.imgsL_of_not_drop`, `SaadSparse.Chapter10.imgsHat_eq`,
  `SaadSparse.Chapter10.imgsL_diag_smul_imgsQ`.
* **Correction.** The row identity sums through its row index, with no residual from dropping $Q$
  entries. See `SaadSparse.Chapter10.rowVec_eq_sum`.
* **Correction.** The incomplete LQ factor has positive diagonal entries, as established in the
  printed proof. See `SaadSparse.Chapter10.proposition_10_17`.
* **Correction.** The incomplete Cholesky comparison requires a symmetric drop pattern with a
  retained diagonal. See `SaadSparse.Chapter10.IsICPattern`.
* **Reading.** The incomplete Cholesky condition is proved for the classical recurrence with the
  corrected symmetric pattern. See `SaadSparse.Chapter10.theorem_10_18`.
* **Theorem 10.18** (correction). The printed condition constrains only pairs $(i, j)$ with $i < j$,
  while Algorithm 10.17 drops entries $l_{ij}$ with $j < i$, so the theorem is false as printed. The
  hypothesis adds the symmetry of $P_L$. See `SaadSparse.Chapter10.IsICPattern`.
* **Theorem 10.18** (reading). The book attaches the theorem to Algorithm 10.18, the incomplete
  modified Gram–Schmidt process; it is stated for Algorithm 10.17, which computes the same $L$ under
  the hypothesis. See `SaadSparse.Chapter10.theorem_10_18`.

## Not formalized

* **Section 10.8.2** (shifted IC(0)). It is an algorithm with an empirical discussion of the shift
  and no theorem.
* **Algorithm 10.18** (incomplete modified Gram–Schmidt).
-/

namespace SaadSparse.Chapter10

section IncompleteGramSchmidt

variable {n m : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The row $a_i$ of $A \in \mathbb{K}^{n \times m}$ as a vector of $\mathbb{K}^m$, for $i < n$, and
the zero vector for $i \ge n$.

**Reading.** Lean uses a natural row index and returns zero at an out-of-range index. The source
uses only actual rows.
-/
noncomputable def rowVec (A : Matrix (Fin n) (Fin m) 𝕜) (i : ℕ) : EuclideanSpace 𝕜 (Fin m) :=
  if h : i < n then WithLp.toLp 2 (A ⟨i, h⟩) else 0

/-- For an index $i < n$, `SaadSparse.Chapter10.rowVec A i` is the row $i$ of $A$. -/
@[simp]
theorem rowVec_coe (A : Matrix (Fin n) (Fin m) 𝕜) (i : Fin n) :
    rowVec A (i : ℕ) = WithLp.toLp 2 (A i) := by
  simp [rowVec, i.isLt]

/-- One term $l_{ij} q_j$ of the sum on line 4 of Algorithm 10.17, with $q_j$ computed from
$\hat{q}_j$; it is $0$ if $l_{ij}$ is dropped. -/
private noncomputable def imgsTerm (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool)
    (i j : ℕ) (qhat : EuclideanSpace 𝕜 (Fin m)) : EuclideanSpace 𝕜 (Fin m) :=
  (if dropL i j then 0
    else inner 𝕜 (((‖qhat‖ : 𝕜))⁻¹ • qhat) (rowVec A i)) • ((‖qhat‖ : 𝕜))⁻¹ • qhat

/-- **Algorithm 10.17** of [saad2003iterative], lines 2–4. For $A \in \mathbb{K}^{n \times m}$ and a
dropping rule $P_L$, the unnormalized vector is
$$\hat{q}_i = a_i - \sum_{j < i,\ (i, j) \notin P_L} (a_i, q_j) \, q_j,$$
where $q_j = \hat{q}_j / \|\hat{q}_j\|_2$. The sum runs over the coefficients that the dropping
rule retains.

**Reading.** The recurrence accepts a fixed Boolean rule for dropping entries of $L$, while the book
also allows dropping from $Q$ and choosing patterns dynamically. It extends the scalar formulas to
complex inner products and normalizes a zero row to zero instead of stopping.
-/
noncomputable def imgsHat (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool) :
    ℕ → EuclideanSpace 𝕜 (Fin m)
  | i => rowVec A i - ∑ j : Finset.range i, imgsTerm A dropL i j (imgsHat A dropL j)
  decreasing_by exact Finset.mem_range.1 j.2

/-- **Algorithm 10.17** of [saad2003iterative], line 7. The normalized vector is
$$q_i = \hat{q}_i / l_{ii}, \qquad l_{ii} = \|\hat{q}_i\|_2.$$

The book's "if $l_{ii} = 0$ then Stop" is Lean's $x / 0 = 0$, which gives $q_i = 0$ at a
breakdown.

**Reading.** The recurrence accepts a fixed Boolean rule for dropping entries of $L$, while the book
also allows dropping from $Q$ and choosing patterns dynamically. It extends the scalar formulas to
complex inner products and normalizes a zero row to zero instead of stopping.
-/
noncomputable def imgsQ (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool) (i : ℕ) :
    EuclideanSpace 𝕜 (Fin m) :=
  ((‖imgsHat A dropL i‖ : 𝕜))⁻¹ • imgsHat A dropL i

/-- **Algorithm 10.17** of [saad2003iterative], lines 2, 3 and 6. The coefficients of the factor $L$
are
$$l_{ij} = \begin{cases}
  (a_i, q_j) & \text{if } j < i \text{ and } (i, j) \notin P_L, \\
  0 & \text{if } j < i \text{ and } (i, j) \in P_L, \\
  \|\hat{q}_i\|_2 & \text{if } j = i, \\
  0 & \text{if } j > i.
\end{cases}$$

**Reading.** The recurrence accepts a fixed Boolean rule for dropping entries of $L$, while the book
also allows dropping from $Q$ and choosing patterns dynamically. It extends the scalar formulas to
complex inner products and normalizes a zero row to zero instead of stopping.
-/
noncomputable def imgsL (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool) (i j : ℕ) : 𝕜 :=
  if j < i then (if dropL i j then 0 else inner 𝕜 (imgsQ A dropL j) (rowVec A i))
  else if j = i then ((‖imgsHat A dropL i‖ : ℝ) : 𝕜)
  else 0

/-- **Algorithm 10.17** of [saad2003iterative], the lower triangular factor
$L = (l_{ij}) \in \mathbb{K}^{n \times n}$.

**Reading.** The recurrence accepts a fixed Boolean rule for dropping entries of $L$, while the book
also allows dropping from $Q$ and choosing patterns dynamically. It extends the scalar formulas to
complex inner products and normalizes a zero row to zero instead of stopping.
-/
noncomputable def imgsLMat (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => imgsL A dropL (i : ℕ) (j : ℕ)

/-- **Algorithm 10.17** of [saad2003iterative], the factor $Q \in \mathbb{K}^{n \times m}$ whose
rows are the vectors $q_i$. It is not orthogonal in general, because entries of $L$ are dropped.

**Reading.** The recurrence accepts a fixed Boolean rule for dropping entries of $L$, while the book
also allows dropping from $Q$ and choosing patterns dynamically. It extends the scalar formulas to
complex inner products and normalizes a zero row to zero instead of stopping.
-/
noncomputable def imgsQMat (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool) :
    Matrix (Fin n) (Fin m) 𝕜 :=
  Matrix.of fun i j => WithLp.ofLp (imgsQ A dropL (i : ℕ)) j

variable (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool)

/-- The entries of `SaadSparse.Chapter10.imgsLMat` are the coefficients $l_{ij}$. -/
@[simp]
theorem imgsLMat_apply (i j : Fin n) : imgsLMat A dropL i j = imgsL A dropL (i : ℕ) (j : ℕ) := rfl

/-- The rows of `SaadSparse.Chapter10.imgsQMat` are the vectors $q_i$. -/
@[simp]
theorem imgsQMat_apply (i : Fin n) (j : Fin m) :
    imgsQMat A dropL i j = WithLp.ofLp (imgsQ A dropL (i : ℕ)) j := rfl

/-- $L$ is lower triangular: $l_{ij} = 0$ for $i < j$. -/
theorem imgsL_of_lt {i j : ℕ} (h : i < j) : imgsL A dropL i j = 0 := by
  have h1 : ¬(j < i) := by omega
  have h2 : ¬(j = i) := by omega
  simp [imgsL, h1, h2]

/-- The diagonal coefficient is $l_{ii} = \|\hat{q}_i\|_2$ (line 6 of Algorithm 10.17). -/
theorem imgsL_diag (i : ℕ) : imgsL A dropL i i = ((‖imgsHat A dropL i‖ : ℝ) : 𝕜) := by
  simp [imgsL]

/-- For $j < i$, the coefficient $l_{ij}$ is $0$ if $(i, j) \in P_L$ and $(a_i, q_j)$ otherwise.

**Reading.** The recurrence accepts a fixed Boolean rule for dropping entries of $L$, while the book
also allows dropping from $Q$ and choosing patterns dynamically. It extends the scalar formulas to
complex inner products and normalizes a zero row to zero instead of stopping.
-/
theorem imgsL_of_gt {i j : ℕ} (h : j < i) :
    imgsL A dropL i j =
      if dropL i j then 0 else inner 𝕜 (imgsQ A dropL j) (rowVec A i) := by
  simp [imgsL, h]

/-- For $j < i$ and $(i, j) \in P_L$, the coefficient $l_{ij}$ is $0$ (line 3 of Algorithm 10.17).
-/
theorem imgsL_of_drop {i j : ℕ} (h : j < i) (hd : dropL i j) : imgsL A dropL i j = 0 := by
  simp [imgsL_of_gt A dropL h, hd]

/-- For $j < i$ and $(i, j) \notin P_L$, the coefficient $l_{ij}$ is $(a_i, q_j)$ (line 2 of
Algorithm 10.17).

**Reading.** The recurrence accepts a fixed Boolean rule for dropping entries of $L$, while the book
also allows dropping from $Q$ and choosing patterns dynamically. It extends the scalar formulas to
complex inner products and normalizes a zero row to zero instead of stopping.
-/
theorem imgsL_of_not_drop {i j : ℕ} (h : j < i) (hd : ¬ dropL i j) :
    imgsL A dropL i j = inner 𝕜 (imgsQ A dropL j) (rowVec A i) := by
  simp [imgsL_of_gt A dropL h, hd]

/-- Line 4 of Algorithm 10.17 in terms of the coefficients:
$\hat{q}_i = a_i - \sum_{j < i} l_{ij} q_j$.

**Reading.** The recurrence accepts a fixed Boolean rule for dropping entries of $L$, while the book
also allows dropping from $Q$ and choosing patterns dynamically. It extends the scalar formulas to
complex inner products and normalizes a zero row to zero instead of stopping.
-/
theorem imgsHat_eq (i : ℕ) :
    imgsHat A dropL i =
      rowVec A i - ∑ j ∈ Finset.range i, imgsL A dropL i j • imgsQ A dropL j := by
  rw [imgsHat, ← Finset.sum_coe_sort (Finset.range i)]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [imgsTerm, imgsL_of_gt A dropL (Finset.mem_range.1 j.2)]
  rfl

/-- Line 7 of Algorithm 10.17 read backwards: $l_{ii} q_i = \hat{q}_i$. At a breakdown both sides
are $0$, so no hypothesis is needed.

**Reading.** The recurrence accepts a fixed Boolean rule for dropping entries of $L$, while the book
also allows dropping from $Q$ and choosing patterns dynamically. It extends the scalar formulas to
complex inner products and normalizes a zero row to zero instead of stopping.
-/
theorem imgsL_diag_smul_imgsQ (i : ℕ) :
    imgsL A dropL i i • imgsQ A dropL i = imgsHat A dropL i := by
  rcases eq_or_ne (imgsHat A dropL i) 0 with h | h
  · simp [imgsQ, h]
  · have hnorm : ((‖imgsHat A dropL i‖ : ℝ) : 𝕜) ≠ 0 := by
      simpa using norm_ne_zero_iff.2 h
    rw [imgsL_diag, imgsQ, smul_smul, mul_inv_cancel₀ hnorm, one_smul]

/-- **Equation (10.83)** of [saad2003iterative] with $P_Q = \emptyset$. For every $i$,
$$a_i = \sum_{j \le i} l_{ij} q_j,$$
however much is dropped from $L$. So dropping in $L$ alone still gives an exact factorization:
the vector subtracted on line 4 is built from the retained coefficients themselves.

**Correction.** The source display sums up to $j$ while also using $j$ as the running index. The sum
goes up to the row index $i$. Lean uses the case with no dropping from $Q$ and the totalized
normalization, including a zero row remainder.
-/
theorem rowVec_eq_sum (i : ℕ) :
    rowVec A i = ∑ j ∈ Finset.range (i + 1), imgsL A dropL i j • imgsQ A dropL j := by
  rw [Finset.sum_range_succ, imgsL_diag_smul_imgsQ, imgsHat_eq]
  abel

/-- Every vector $\hat{q}_i$ of Algorithm 10.17 lies in the span of the rows $a_0, \dots, a_i$. -/
theorem imgsHat_mem_span (i : ℕ) :
    imgsHat A dropL i ∈ Submodule.span 𝕜 (rowVec A '' Set.Iic i) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [imgsHat_eq]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨i, Set.mem_Iic.2 le_rfl, rfl⟩)
      (Submodule.sum_mem _ ?_)
    intro j hj
    have hji : j < i := Finset.mem_range.1 hj
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hji.le)) (ih j hji)

/-- The rows of a nonsingular matrix $A \in \mathbb{K}^{n \times n}$ are linearly independent. -/
theorem linearIndependent_rowVec {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A) :
    LinearIndependent 𝕜 fun i : Fin n => rowVec A (i : ℕ) := by
  have hrows : LinearIndependent 𝕜 A.row := Matrix.linearIndependent_row_iff_isUnit.2 hA
  have hmap := hrows.map' (WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).symm.toLinearMap
    (LinearEquiv.ker _)
  have heq : (fun i : Fin n => rowVec A (i : ℕ)) =
      ⇑(WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).symm.toLinearMap ∘ A.row := by
    funext i
    rw [rowVec_coe]
    rfl
  rw [heq]
  exact hmap

/-- If the rows of $A \in \mathbb{K}^{n \times m}$ are linearly independent, then $\hat{q}_i \neq 0$
for every $i < n$: Algorithm 10.17 does not break down. Otherwise (10.83) would write $a_i$ as a
combination of the earlier rows, since each $q_k$ is a combination of $a_0, \dots, a_k$. -/
theorem imgsHat_ne_zero (hA : LinearIndependent 𝕜 fun i : Fin n => rowVec A (i : ℕ)) (i : Fin n) :
    imgsHat A dropL (i : ℕ) ≠ 0 := by
  intro h0
  have hspan : rowVec A (i : ℕ) ∈
      Submodule.span 𝕜 ((fun j : Fin n => rowVec A (j : ℕ)) ''
        {j : Fin n | (j : ℕ) < (i : ℕ)}) := by
    have hsum : rowVec A (i : ℕ) =
        ∑ j ∈ Finset.range (i : ℕ), imgsL A dropL (i : ℕ) j • imgsQ A dropL j := by
      rw [imgsHat_eq] at h0
      rw [← sub_eq_zero]
      exact h0
    rw [hsum]
    refine Submodule.sum_mem _ fun j hj => ?_
    have hji : j < (i : ℕ) := Finset.mem_range.1 hj
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    refine Submodule.span_mono ?_ (imgsHat_mem_span A dropL j)
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨k, (hk.trans hji.le).trans_lt i.isLt⟩, lt_of_le_of_lt hk hji, rfl⟩
  exact hA.notMem_span_image (s := {j : Fin n | (j : ℕ) < (i : ℕ)}) (by simp) hspan

/-- If the rows of $A \in \mathbb{R}^{n \times m}$ are linearly independent, then
$l_{ii} = \|\hat{q}_i\|_2 > 0$ for every $i < n$, so Algorithm 10.17 runs to completion. This is
the no-breakdown clause of Proposition 10.17 for a rectangular matrix. -/
theorem imgsL_diag_pos {A : Matrix (Fin n) (Fin m) ℝ} (dropL : ℕ → ℕ → Bool)
    (hA : LinearIndependent ℝ fun i : Fin n => rowVec A (i : ℕ)) (i : Fin n) :
    0 < imgsL A dropL (i : ℕ) (i : ℕ) := by
  rw [imgsL_diag]
  simpa using norm_pos_iff.2 (imgsHat_ne_zero A dropL hA i)

/-- **Proposition 10.17** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular, let $P_L$ be any dropping rule for $L$, and apply no dropping to $Q$. Then the
incomplete Gram–Schmidt process, Algorithm 10.17, does not break down, and it computes an exact
factorization
$$A = LQ,$$
in which $L$ is lower triangular with positive diagonal and $Q$ is nonsingular. Precisely:
$l_{ii} > 0$ for every $i$, $l_{ij} = 0$ for $i < j$, $LQ = A$, and $Q$ is nonsingular.

The factor $Q$ is not orthogonal in general. The proof is the book's: if $l_{ii} = 0$, then
(10.83) would write the row $a_i$ as a combination of the earlier rows, against the
nonsingularity of $A$.

**Correction.** The book says $L$ has positive elements. The algorithm gives positivity only on the
diagonal: off-diagonal computed coefficients can be zero or negative. Lean asserts precisely
positive diagonal entries, exact reconstruction, and nonsingular $Q$.
-/
theorem proposition_10_17 {A : Matrix (Fin n) (Fin n) ℝ} (dropL : ℕ → ℕ → Bool)
    (hA : IsUnit A) :
    (∀ i : Fin n, 0 < imgsL A dropL (i : ℕ) (i : ℕ)) ∧
      (∀ i j : Fin n, (i : ℕ) < (j : ℕ) → imgsL A dropL (i : ℕ) (j : ℕ) = 0) ∧
      imgsLMat A dropL * imgsQMat A dropL = A ∧ IsUnit (imgsQMat A dropL) := by
  have hdiag : ∀ i : Fin n, 0 < imgsL A dropL (i : ℕ) (i : ℕ) :=
    imgsL_diag_pos dropL (linearIndependent_rowVec hA)
  have hlower : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → imgsL A dropL (i : ℕ) (j : ℕ) = 0 :=
    fun i j h => imgsL_of_lt A dropL h
  have hfac : imgsLMat A dropL * imgsQMat A dropL = A := by
    ext i k
    have hrow := congrArg (fun z : EuclideanSpace ℝ (Fin n) => WithLp.ofLp z k)
      (rowVec_eq_sum A dropL (i : ℕ))
    simp only [rowVec_coe, WithLp.ofLp_toLp, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hrow
    have hconv : ∑ j : Fin n, imgsLMat A dropL i j * imgsQMat A dropL j k
        = ∑ j ∈ Finset.range n,
            imgsL A dropL (i : ℕ) j * WithLp.ofLp (imgsQ A dropL j) k :=
      Fin.sum_univ_eq_sum_range
        (fun j => imgsL A dropL (i : ℕ) j * WithLp.ofLp (imgsQ A dropL j) k) n
    rw [Matrix.mul_apply, hconv, hrow]
    have hsub : Finset.range ((i : ℕ) + 1) ⊆ Finset.range n := fun j hj =>
      Finset.mem_range.2 (by have := Finset.mem_range.1 hj; have := i.isLt; omega)
    refine (Finset.sum_subset hsub fun j _ hj => ?_).symm
    rw [Finset.mem_range, not_lt] at hj
    rw [imgsL_of_lt A dropL (by omega), zero_mul]
  refine ⟨hdiag, hlower, hfac, ?_⟩
  -- `A = L Q` with `A` nonsingular forces `det Q ≠ 0`
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  rw [← hfac, Matrix.det_mul] at hdetA
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdetA)

end IncompleteGramSchmidt

section IncompleteCholesky

open scoped Matrix RealInnerProductSpace

variable {n m : ℕ}

/-! ### The zero-pattern hypothesis of Theorem 10.18 -/

/-- **Theorem 10.18** of [saad2003iterative], the hypothesis on the zero pattern. A dropping rule
$P_L$ satisfies the hypothesis if it avoids the diagonal, it is symmetric, and for all $i, j, k$
with $i < j$ and $i < k$,
$$(i, j) \in P_L \text{ and } (i, k) \notin P_L \implies (j, k) \in P_L.$$

**Correction.** The book does not print the symmetry, and the theorem is false without it. The
printed condition constrains the pairs $(i, j)$ with $i < j$, while the algorithm drops the
entries $l_{ij}$ with $j < i$, so without a link between the two triangles the hypothesis says
nothing about what is dropped. For example, take rows $(1,0,0)$, $(1,1,0)$ and $(1,1,1)$,
and drop only $(3,1)$ in $1$-based indices. The printed condition holds vacuously, but the
retained entry $(LL^T)_{32}=1$ differs from $(AA^T)_{32}=2$. The zero
pattern of a Cholesky factorization is symmetric, because it is the pattern of both $L$ and
$L^T$; this is the link, and `Matrix.IsIC` asks for it as well.

On the entries that the algorithm drops, the pairs $(i, j)$ with $j < i$, the last condition
becomes the two statements `SaadSparse.Chapter10.IsICPattern.notDrop_row` and
`SaadSparse.Chapter10.IsICPattern.notDrop_trans`, which are all that the proof of Theorem 10.18
uses.

**Correction.** Symmetry links the upper-triangular pairs in the printed condition with the
lower-triangular pairs subject to dropping. Lean requires that symmetry and a retained diagonal over
all natural indices.
-/
structure IsICPattern (dropL : ℕ → ℕ → Bool) : Prop where
  /-- $P_L$ contains no diagonal position, $(i, i) \notin P_L$; this is the only restriction that
  the book places on $P_L$ in general. -/
  notDrop_diag : ∀ i, ¬ dropL i i
  /-- $P_L$ is symmetric, $(i, j) \in P_L \iff (j, i) \in P_L$, as the zero pattern of a Cholesky
  factorization is. -/
  symm : ∀ i j, dropL i j = dropL j i
  /-- The condition displayed in Theorem 10.18: for $i < j$ and $i < k$, $(i, j) \in P_L$ and
  $(i, k) \notin P_L$ imply $(j, k) \in P_L$. -/
  drop_of_notDrop : ∀ i j k, i < j → i < k → dropL i j → ¬ dropL i k → dropL j k

section Pattern

variable {dropL : ℕ → ℕ → Bool} (hP : IsICPattern dropL)
include hP

namespace IsICPattern

/-- Under the hypothesis of Theorem 10.18, coefficients retained in one row are retained between
themselves: if $l < k \le i$ and neither $l_{ik}$ nor $l_{il}$ is dropped, then $l_{kl}$ is not
dropped.

This is the condition of Theorem 10.18 with its two later indices in the order $j < k$, read on
the lower triangle through the symmetry of $P_L$. -/
theorem notDrop_row {i k l : ℕ} (hlk : l < k) (hki : k ≤ i) (hik : ¬ dropL i k)
    (hil : ¬ dropL i l) : ¬ dropL k l := fun h => hik <| by
  have h1 : dropL l k := by rw [hP.symm l k]; exact h
  have h2 : ¬ dropL l i := by rw [hP.symm l i]; exact hil
  rw [hP.symm i k]
  exact hP.drop_of_notDrop l k i hlk (hlk.trans_le hki) h1 h2

/-- Under the hypothesis of Theorem 10.18, retention is transitive down the rows: if $l < j < i$ and
both $l_{ij}$ and $l_{jl}$ are retained, then $l_{il}$ is retained.

This is the condition of Theorem 10.18 with its two later indices in the order $k < j$, read on
the lower triangle through the symmetry of $P_L$. -/
theorem notDrop_trans {i j l : ℕ} (hlj : l < j) (hji : j < i) (hij : ¬ dropL i j)
    (hjl : ¬ dropL j l) : ¬ dropL i l := fun h => hij <| by
  have h1 : dropL l i := by rw [hP.symm l i]; exact h
  have h2 : ¬ dropL l j := by rw [hP.symm l j]; exact hjl
  exact hP.drop_of_notDrop l i j (hlj.trans hji) hlj h1 h2

end IsICPattern

end Pattern

/-! ### Orthogonality off the pattern -/

variable (A : Matrix (Fin n) (Fin m) ℝ) (dropL : ℕ → ℕ → Bool)

/-- Over $\mathbb{R}$, the normalization of line 7 of Algorithm 10.17 is the multiplication by the
real number $\|\hat{q}_i\|_2^{-1}$. -/
theorem imgsQ_real (i : ℕ) :
    imgsQ A dropL i = (‖imgsHat A dropL i‖)⁻¹ • imgsHat A dropL i := by
  simp [imgsQ]

/-- If $\hat{q}_j = 0$, then $l_{ij} = 0$ for every $i$: a breakdown at step $j$ makes the whole
column $j$ of $L$ zero, because $q_j = 0$ and $l_{jj} = \|\hat{q}_j\|_2 = 0$. -/
theorem imgsL_eq_zero_of_imgsHat_eq_zero {j : ℕ} (h : imgsHat A dropL j = 0) (i : ℕ) :
    imgsL A dropL i j = 0 := by
  rcases lt_trichotomy j i with hji | hji | hji
  · have hq : imgsQ A dropL j = 0 := by simp [imgsQ, h]
    simp [imgsL_of_gt A dropL hji, hq]
  · subst hji
    simp [imgsL_diag, h]
  · exact imgsL_of_lt A dropL hji

/-- For all $i, k$, $l_{ik} (q_k, q_k) = l_{ik}$: each $q_k$ is a unit vector, except at a
breakdown, where the coefficients $l_{ik}$ vanish instead. -/
theorem imgsL_mul_inner_self (i k : ℕ) :
    imgsL A dropL i k * ⟪imgsQ A dropL k, imgsQ A dropL k⟫ = imgsL A dropL i k := by
  rcases eq_or_ne (imgsHat A dropL k) 0 with h | h
  · rw [imgsL_eq_zero_of_imgsHat_eq_zero A dropL h i, zero_mul]
  · have hnorm : ‖imgsQ A dropL k‖ = 1 := by
      rw [imgsQ_real, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow, mul_one]

/-- $A A^T$ is the Gram matrix of the rows of $A$: $(A A^T)_{ij} = (a_i, a_j)$. -/
theorem mul_transpose_apply (i j : Fin n) :
    (A * Aᵀ) i j = ⟪rowVec A (i : ℕ), rowVec A (j : ℕ)⟫ := by
  simp [Matrix.mul_apply, PiLp.inner_apply, rowVec_coe, mul_comm]

/-- The Gram matrix $A A^T$ is symmetric. -/
theorem mul_transpose_apply_comm (i j : Fin n) : (A * Aᵀ) i j = (A * Aᵀ) j i := by
  rw [mul_transpose_apply A, mul_transpose_apply A, real_inner_comm]

section Factorization

variable {dropL} (hP : IsICPattern dropL)
include hP

namespace IsICPattern

/-- Under the hypothesis of Theorem 10.18, a nonzero coefficient $l_{ik}$ with $k \le i$ is one that
the dropping rule retains. -/
theorem notDrop_of_imgsL_ne_zero {i k : ℕ} (hki : k ≤ i) (h : imgsL A dropL i k ≠ 0) :
    ¬ dropL i k := by
  rcases eq_or_lt_of_le hki with hk | hk
  · rw [hk]; exact hP.notDrop_diag i
  · exact fun hd => h (imgsL_of_drop A dropL hk hd)

/-- Under the hypothesis of Theorem 10.18, if $j < i$ and the coefficient $l_{ij}$ is retained, then
$(q_i, q_j) = 0$. So $Q Q^T$ differs from the identity only inside the pattern, and only there
does $L L^T$ differ from $A A^T$. This is the orthogonality on which Theorem 10.18 rests.

The proof is an induction on $i$. In $(\hat{q}_i, q_j) = (a_i, q_j) - \sum_{k < i} l_{ik} (q_k,
q_j)$ the term $k = j$ cancels $(a_i, q_j)$, and every other term vanishes: a nonzero $l_{ik}$
means that $l_{ik}$ and $l_{ij}$ are both retained in row $i$, so
`SaadSparse.Chapter10.IsICPattern.notDrop_row` retains the coefficient that links $k$ and $j$,
and the induction hypothesis applies to it. -/
theorem inner_imgsQ_eq_zero (i : ℕ) :
    ∀ j < i, ¬ dropL i j → ⟪imgsQ A dropL i, imgsQ A dropL j⟫ = 0 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hji hij
    have key : ⟪imgsHat A dropL i, imgsQ A dropL j⟫ = 0 := by
      rw [imgsHat_eq, inner_sub_left, sum_inner]
      have hterm : ∀ k ∈ Finset.range i, k ≠ j →
          ⟪imgsL A dropL i k • imgsQ A dropL k, imgsQ A dropL j⟫ = 0 := by
        intro k hk hkj
        rw [real_inner_smul_left]
        rcases eq_or_ne (imgsL A dropL i k) 0 with h0 | h0
        · rw [h0, zero_mul]
        have hki : k < i := Finset.mem_range.1 hk
        have hik : ¬ dropL i k := fun hd => h0 (imgsL_of_drop A dropL hki hd)
        rcases lt_or_gt_of_ne hkj with hkj' | hkj'
        · rw [← real_inner_comm (imgsQ A dropL k) (imgsQ A dropL j),
            ih j hji k hkj' (hP.notDrop_row hkj' hji.le hij hik), mul_zero]
        · rw [ih k hki j hkj' (hP.notDrop_row hkj' hki.le hik hij), mul_zero]
      rw [Finset.sum_eq_single j hterm fun h => absurd (Finset.mem_range.2 hji) h,
        real_inner_smul_left, imgsL_mul_inner_self, imgsL_of_not_drop A dropL hji hij,
        real_inner_comm, sub_self]
    rw [imgsQ_real, real_inner_smul_left, key, mul_zero]

/-- Under the hypothesis of Theorem 10.18, the cross terms of $(a_i, a_j)$ vanish: if $j \le i$,
$k \le i$, $l \le j$, $k \neq l$, and $l_{ij}$, $l_{ik}$ and $l_{jl}$ are all retained, then
$(q_k, q_l) = 0$.

Both $k$ and $l$ are retained in row $i$, $l$ by
`SaadSparse.Chapter10.IsICPattern.notDrop_trans`, so
`SaadSparse.Chapter10.IsICPattern.notDrop_row` and
`SaadSparse.Chapter10.IsICPattern.inner_imgsQ_eq_zero` apply to the pair. -/
theorem inner_imgsQ_eq_zero_of_ne {i j k l : ℕ} (hji : j ≤ i) (hij : ¬ dropL i j) (hki : k ≤ i)
    (hlj : l ≤ j) (hik : ¬ dropL i k) (hjl : ¬ dropL j l) (hkl : k ≠ l) :
    ⟪imgsQ A dropL k, imgsQ A dropL l⟫ = 0 := by
  have hil : ¬ dropL i l := by
    rcases eq_or_lt_of_le hlj with h | h
    · rw [h]; exact hij
    · rcases eq_or_lt_of_le hji with h' | h'
      · rw [← h']; exact hjl
      · exact hP.notDrop_trans h h' hij hjl
  rcases lt_or_gt_of_ne hkl with h | h
  · rw [← real_inner_comm (imgsQ A dropL k) (imgsQ A dropL l)]
    exact hP.inner_imgsQ_eq_zero A l k h (hP.notDrop_row h (hlj.trans hji) hil hik)
  · exact hP.inner_imgsQ_eq_zero A k l h (hP.notDrop_row h hki hik hil)

/-- Under the hypothesis of Theorem 10.18, if $k < j < i$ and $l_{ij}$ and $l_{ik}$ are both
retained, then $(q_k, q_j) = 0$.

This is why Algorithms 10.17 and 10.18 agree under the hypothesis. The incomplete modified
Gram–Schmidt process of Algorithm 10.18 computes $l_{ij}$ against the partially updated row
$a_i - \sum_{k < j} l_{ik} q_k$ instead of against $a_i$, so it differs from Algorithm 10.17 by
the corrections $l_{ik} (q_k, q_j)$ for $k < j < i$, and each of these inner products vanishes.
An induction on $j$ therefore gives the same coefficients from both algorithms. Algorithm 10.18
itself is not formalized. -/
theorem inner_imgsQ_eq_zero_of_lt {i j k : ℕ} (hji : j < i) (hkj : k < j) (hij : ¬ dropL i j)
    (hik : ¬ dropL i k) : ⟪imgsQ A dropL k, imgsQ A dropL j⟫ = 0 :=
  hP.inner_imgsQ_eq_zero_of_ne A hji.le hij (hkj.trans hji).le le_rfl hik
    (hP.notDrop_diag j) hkj.ne

/-- Under the hypothesis of Theorem 10.18, if $j \le i$ and $l_{ij}$ is retained, then the entry
$b_{ij} = (a_i, a_j)$ of $B = A A^T$ is the entry of $L L^T$:
$$(a_i, a_j) = \sum_{k \le j} l_{ik} l_{jk}.$$

Expanding both rows by (10.83) turns $(a_i, a_j)$ into a double sum over the rows of $Q$. Its
off-diagonal terms vanish by `SaadSparse.Chapter10.IsICPattern.inner_imgsQ_eq_zero_of_ne`, and
its diagonal terms are $l_{ik} l_{jk}$ by `SaadSparse.Chapter10.imgsL_mul_inner_self`. -/
theorem inner_rowVec_eq_sum {i j : ℕ} (hji : j ≤ i) (hij : ¬ dropL i j) :
    ⟪rowVec A i, rowVec A j⟫
      = ∑ k ∈ Finset.range (j + 1), imgsL A dropL i k * imgsL A dropL j k := by
  rw [rowVec_eq_sum A dropL i, rowVec_eq_sum A dropL j, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlj : l ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  rw [Finset.sum_eq_single_of_mem l (Finset.mem_range.2 (by omega)) ?_]
  · rw [← mul_assoc, mul_comm (imgsL A dropL i l), mul_assoc, imgsL_mul_inner_self, mul_comm]
  · intro k hk hkl
    have hki : k ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rcases eq_or_ne (imgsL A dropL i k) 0 with h0 | h0
    · rw [h0, zero_mul, mul_zero]
    rcases eq_or_ne (imgsL A dropL j l) 0 with h1 | h1
    · rw [h1, zero_mul]
    rw [hP.inner_imgsQ_eq_zero_of_ne A hji hij hki hlj (hP.notDrop_of_imgsL_ne_zero A hki h0)
      (hP.notDrop_of_imgsL_ne_zero A hlj h1) hkl, mul_zero, mul_zero]

/-- Under the hypothesis of Theorem 10.18, $(L L^T)_{ij} = (A A^T)_{ij}$ for all indices
$j \le i < n$ with $(i, j) \notin P_L$. -/
theorem imgsLMat_mul_transpose_apply {i j : Fin n} (hji : (j : ℕ) ≤ (i : ℕ))
    (hij : ¬ dropL (i : ℕ) (j : ℕ)) :
    (imgsLMat A dropL * (imgsLMat A dropL)ᵀ) i j = (A * Aᵀ) i j := by
  rw [mul_transpose_apply A, hP.inner_rowVec_eq_sum A hji hij, Matrix.mul_apply]
  have hentry : ∀ k : Fin n, imgsLMat A dropL i k * (imgsLMat A dropL)ᵀ k j
      = imgsL A dropL (i : ℕ) (k : ℕ) * imgsL A dropL (j : ℕ) (k : ℕ) := fun _ => rfl
  rw [Finset.sum_congr rfl fun k _ => hentry k,
    Fin.sum_univ_eq_sum_range
      (fun k => imgsL A dropL (i : ℕ) k * imgsL A dropL (j : ℕ) k) n]
  refine (Finset.sum_subset (fun k hk => ?_) fun k _ hk => ?_).symm
  · exact Finset.mem_range.2 (by
      have := Finset.mem_range.1 hk
      have := i.isLt
      omega)
  · rw [Finset.mem_range, not_lt] at hk
    rw [imgsL_of_lt A dropL (by omega : (j : ℕ) < k), mul_zero]

end IsICPattern

/-- **Theorem 10.18** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times m}$ and let
$B = A A^T$. Let $P_L$ be a zero pattern that avoids the diagonal, is symmetric, and satisfies,
for all $i, j, k$ with $i < j$ and $i < k$,
$$(i, j) \in P_L \text{ and } (i, k) \notin P_L \implies (j, k) \in P_L.$$
Then the matrix $L$ obtained from the incomplete Gram–Schmidt process with the zero pattern
$P_L$ is an incomplete Cholesky factor of $B$ for $P_L$: $L$ is lower triangular, $l_{ij} = 0$
for $(i, j) \in P_L$, and $(L L^T)_{ij} = b_{ij}$ for $(i, j) \notin P_L$.

**Correction.** The book does not require $P_L$ to be symmetric, and without symmetry the
theorem is false; see `SaadSparse.Chapter10.IsICPattern`.

**Reading.** The book attaches the theorem to Algorithm 10.18, the incomplete modified
Gram–Schmidt process, while `SaadSparse.Chapter10.imgsL` is Algorithm 10.17. Under the
hypothesis on $P_L$ the two algorithms compute the same $L$, because every correction that the
modified process makes to a coefficient is an inner product that
`SaadSparse.Chapter10.IsICPattern.inner_imgsQ_eq_zero_of_lt` shows to vanish.

The book states that $L$ is identical with the factor of the incomplete Cholesky factorization
of $B$ with the same zero pattern. The formal statement is `Matrix.IsIC`. By
`Matrix.IsIC.eq_of_diag_pos`, $L$ is the only such factor with a positive diagonal, and
`SaadSparse.Chapter10.imgsL_diag_pos` gives a positive diagonal when the rows of $A$ are
linearly independent. The book states the theorem without proof and cites the literature. The
proof here is the orthogonality `SaadSparse.Chapter10.IsICPattern.inner_imgsQ_eq_zero`: under
the hypothesis on $P_L$, the rows of $Q$ retained in one row of $L$ are pairwise orthogonal, so
all cross terms of $(a_i, a_j) = \sum_{k, l} l_{ik} l_{jl} (q_k, q_l)$ vanish, and what remains
is the entry $(i, j)$ of $L L^T$.

**Reading.** Lean proves that the incomplete classical Gram–Schmidt factor satisfies the corrected
incomplete Cholesky specification. The printed result refers to modified Gram–Schmidt and identifies
the two factors explicitly. The formal result does not compare two algorithm outputs, and
positive-diagonal uniqueness can be invoked separately for independent rows.
-/
theorem theorem_10_18 :
    Matrix.IsIC {p : Fin n × Fin n | dropL (p.1 : ℕ) (p.2 : ℕ)} (A * Aᵀ) (imgsLMat A dropL) where
  l_eq_zero_of_lt i j hij := imgsL_of_lt A dropL hij
  l_eq_zero_of_mem i j hij := by
    rcases lt_trichotomy (j : ℕ) (i : ℕ) with h | h | h
    · exact imgsL_of_drop A dropL h hij
    · exact absurd (by simpa [h] using hij) (hP.notDrop_diag (i : ℕ))
    · exact imgsL_of_lt A dropL h
  agree i j hij := by
    rcases le_total (j : ℕ) (i : ℕ) with h | h
    · exact hP.imgsLMat_mul_transpose_apply A h hij
    · rw [mul_transpose_apply_comm A i j,
        ← hP.imgsLMat_mul_transpose_apply A h (by rw [hP.symm]; exact hij)]
      exact mul_transpose_apply_comm (imgsLMat A dropL) i j

end Factorization

end IncompleteCholesky

end SaadSparse.Chapter10
