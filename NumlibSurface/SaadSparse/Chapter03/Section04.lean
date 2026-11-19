/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 3.4: Storage schemes

This module formalizes §3.4 of [saad2003iterative]: the coordinate format, the compressed sparse row
format, the modified sparse row format, the diagonal format and the Ellpack-Itpack format. The
section states no theorem and no numbered definition. Its mathematical content is three worked
examples, and each writes one small matrix out in one layout. Each example is stated here as the
round trip that its layout promises: the arrays decode to the matrix that they came from. For the
diagonal format the decoding is the defining relation $\mathrm{DIAG}(i, j) = a_{i, i +
\mathrm{IOFF}(j)}$ of the source, and for the Ellpack-Itpack format it is the identity that makes
the matrix-by-vector product of Algorithm 11.5 correct. The proofs are computations on the given
arrays.

## Main definitions

* Example 3.7, `SaadSparse.Chapter03.matrix_3_7`: the $5 \times 5$ matrix with the twelve nonzero
  entries $1$ to $12$.
* Example 3.7, `SaadSparse.Chapter03.cooAA`, `SaadSparse.Chapter03.cooJR` and
  `SaadSparse.Chapter03.cooJC`: the values, row indices and column indices of its coordinate format.
* §3.4, `SaadSparse.Chapter03.csrAA`, `SaadSparse.Chapter03.csrJA` and `SaadSparse.Chapter03.csrIA`:
  the values, column indices and row pointers of its compressed sparse row format.
* §3.4, `SaadSparse.Chapter03.msrAA`, `SaadSparse.Chapter03.msrJA` and
  `SaadSparse.Chapter03.msrPtr`: the two arrays of its modified sparse row format and the row
  pointers in the second one.
* Example 3.8, `SaadSparse.Chapter03.matrix_3_8`: the $5 \times 5$ matrix whose nonzero entries lie
  on the diagonals with offsets $-1$, $0$ and $2$.
* Example 3.8, `SaadSparse.Chapter03.ioff_3_8` and `SaadSparse.Chapter03.diag_3_8`: the offsets and
  the stored diagonals of its diagonal format.
* Example 3.9, `SaadSparse.Chapter03.coef_3_9` and `SaadSparse.Chapter03.jcoef_3_9`: the values and
  column positions of its Ellpack-Itpack format.

## Main results

* Example 3.7, `SaadSparse.Chapter03.example_3_7`: the coordinate arrays represent the matrix, store
  only nonzero values, and store no position twice.
* §3.4, `SaadSparse.Chapter03.example_3_7_csr`: the compressed sparse row arrays represent the
  matrix of Example 3.7.
* §3.4, `SaadSparse.Chapter03.example_3_7_msr`: the modified sparse row arrays represent the matrix
  of Example 3.7.
* Example 3.8, `SaadSparse.Chapter03.example_3_8`: the diagonal-format arrays represent the matrix,
  and the positions marked $*$ are those that fall outside the matrix.
* Example 3.9, `SaadSparse.Chapter03.example_3_9`: the Ellpack-Itpack arrays represent the matrix of
  Example 3.8 and compute its matrix-by-vector product.

## Conventions

* The source indexes its arrays from $1$. Here they are indexed from $0$, so $\mathrm{IA}(1) = 1$ of
  the source is `SaadSparse.Chapter03.csrIA 0 = 0`, and a column number $j$ of the source is $j - 1$
  here.
* The array lengths are those of the source: twelve stored values in Example 3.7, $n + 1 + 7 = 13$
  positions in the modified sparse row arrays, and $n \times N_d = 5 \times 3$ in the diagonal and
  Ellpack-Itpack arrays.
* The positions that the source marks $*$ are unused by the decoders. In the diagonal format
  a single parameter supplies all three unused entries.

## Implementation notes

* A round-trip statement is a single equation: $a_{ij}$ equals what the arrays say about the entry
  $(i, j)$, as a sum of the stored values for that position. It is stronger than the two
  containments read separately: every stored value is an entry of the matrix, every nonzero entry is
  stored, and no position is stored twice in a way that changes the sum. For the coordinate format,
  the further claim that the twelve stored positions are distinct, so that the array length is the
  number $N_z$ of nonzeros, is a separate clause.

## Deviations from the source

* **§3.4, compressed sparse rows** (typo). Row pointers replace the coordinate row-index
  array $\mathrm{JR}$. The prose prints $\mathrm{JC}$ for that array.
  See `SaadSparse.Chapter03.csrIA` and `SaadSparse.Chapter03.example_3_7_csr`.
* **Example 3.8** (reading). The diagonal layout assigns a common value to all three
  unused positions, and the decoder ignores them. See `SaadSparse.Chapter03.diag_3_8`
  and `SaadSparse.Chapter03.example_3_8`.

## Not formalized

* **The compressed sparse column format** of §3.4, which the section names but does not write out.
* **§3.5, the code fragments for the matrix-by-vector product.** They state nothing, and the
  correctness of a sparse matrix-by-vector product against `Matrix.mulVec` is a specification that
  the source does not state.
* **§3.6, sparse direct solution methods.** Minimum degree and nested dissection are described as
  algorithms, and this edition states no complexity or fill-in result. The separator property of the
  level sets is in §3.3.3, as `SaadSparse.Chapter03.levelSet_blockTridiagonal`.
* **§3.7, test problems**, which is descriptive.
-/

open Finset Matrix

namespace SaadSparse.Chapter03

/-! ### Example 3.7: the coordinate, compressed sparse row and modified sparse row formats -/

/-- **Example 3.7** of [saad2003iterative], the matrix. It is the $5 \times 5$ matrix
$$\begin{bmatrix} 1 & 0 & 0 & 2 & 0 \\ 3 & 4 & 0 & 5 & 0 \\ 6 & 0 & 7 & 8 & 9 \\ 0 & 0 & 10 & 11
  & 0 \\ 0 & 0 & 0 & 0 & 12 \end{bmatrix},$$
whose twelve nonzero entries are $1$ to $12$. -/
def matrix_3_7 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 2, 0;
     3, 4, 0, 5, 0;
     6, 0, 7, 8, 9;
     0, 0, 10, 11, 0;
     0, 0, 0, 0, 12]

/-- **Example 3.7** of [saad2003iterative], the array $\mathrm{AA}$ of the coordinate format: the
twelve nonzero values $12, 9, 7, 5, 1, 2, 11, 3, 6, 4, 8, 10$, in the arbitrary order in which
the source lists them. -/
def cooAA : Fin 12 → ℝ := ![12, 9, 7, 5, 1, 2, 11, 3, 6, 4, 8, 10]

/-- **Example 3.7** of [saad2003iterative], the array $\mathrm{JR}$ of the coordinate format: the
row index of each stored value, $0$-based. -/
def cooJR : Fin 12 → Fin 5 := ![4, 2, 2, 1, 0, 0, 3, 1, 2, 1, 2, 3]

/-- **Example 3.7** of [saad2003iterative], the array $\mathrm{JC}$ of the coordinate format: the
column index of each stored value, $0$-based. -/
def cooJC : Fin 12 → Fin 5 := ![4, 4, 2, 3, 0, 3, 3, 0, 0, 1, 3, 2]

/-- **Example 3.7** of [saad2003iterative], the coordinate format. Let $A$ be the matrix of Example
3.7, and let $\mathrm{AA}$, $\mathrm{JR}$ and $\mathrm{JC}$ be the arrays of its coordinate
format, of length $12$. Then the following hold.

* For all $i, j$, $$a_{ij} = \sum_{k \,:\, \mathrm{JR}(k) = i,\ \mathrm{JC}(k) = j}
  \mathrm{AA}(k).$$
* $\mathrm{AA}(k) \neq 0$ for every $k$, so only nonzero values are stored.
* If $\mathrm{JR}(k) = \mathrm{JR}(l)$ and $\mathrm{JC}(k) = \mathrm{JC}(l)$, then $k = l$.

The first clause is the round trip. The third says that the twelve stored positions are
distinct, so that the arrays have the length $N_z = 12$ of the source and each sum in the first
clause has at most one term. -/
theorem example_3_7 :
    (∀ i j, matrix_3_7 i j = ∑ k : Fin 12, if cooJR k = i ∧ cooJC k = j then cooAA k else 0) ∧
      (∀ k, cooAA k ≠ 0) ∧
      (∀ k l : Fin 12, cooJR k = cooJR l → cooJC k = cooJC l → k = l) := by
  refine ⟨fun i j => ?_, fun k => ?_, by decide⟩
  · fin_cases i <;> fin_cases j <;> simp [matrix_3_7, cooAA, cooJR, cooJC, Fin.sum_univ_succ]
  · fin_cases k <;> norm_num [cooAA]

/-- **Section 3.4** of [saad2003iterative], the array $\mathrm{AA}$ of the compressed sparse row
format of the matrix of Example 3.7: the nonzero values $1, \dots, 12$, row by row. -/
def csrAA : Fin 12 → ℝ := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- **Section 3.4** of [saad2003iterative], the array $\mathrm{JA}$ of the compressed sparse row
format of the matrix of Example 3.7: the column index of each stored value, $0$-based. -/
def csrJA : Fin 12 → Fin 5 := ![0, 3, 0, 1, 3, 0, 2, 3, 4, 2, 3, 4]

/-- **Section 3.4** of [saad2003iterative], the array $\mathrm{IA}$ of the compressed sparse row
format of the matrix of Example 3.7: the position at which each row starts, $0$-based, followed
by the extra entry $\mathrm{IA}(n + 1) = \mathrm{IA}(1) + N_z$.

**Typo.** The source prose says to replace $\mathrm{JC}$ with pointers. The row-pointers
array replaces $\mathrm{JR}$, while $\mathrm{JA}$ still stores the column indices. -/
def csrIA : Fin 6 → ℕ := ![0, 2, 5, 9, 11, 12]

/-- **Section 3.4** of [saad2003iterative], the compressed sparse row format of the matrix of
Example 3.7. Let $A$ be this matrix, and let $\mathrm{AA}$, $\mathrm{JA}$ and $\mathrm{IA}$ be
the arrays of its compressed sparse row format. Then the following hold.

* For all $i, j$, $$a_{ij} = \sum_{p \,:\, \mathrm{IA}(i) \le p < \mathrm{IA}(i + 1),\
  \mathrm{JA}(p) = j} \mathrm{AA}(p).$$
* $\mathrm{IA}(n + 1) = \mathrm{IA}(1) + 12$.
* $\mathrm{IA}(i) \le \mathrm{IA}(i + 1)$ for every row $i$.

The first clause is the round trip, restricted for each row $i$ to the block of positions that
the pointer array assigns to it. The second is the remark of the source that
$\mathrm{IA}(n + 1) = \mathrm{IA}(1) + N_z$. The third says that $\mathrm{IA}$ is nondecreasing,
so the blocks that it cuts out are consecutive and disjoint.

All arrays are $0$-based: row $i$ of the formula is `i.castSucc` in
`SaadSparse.Chapter03.csrIA`, and row $i + 1$ is `i.succ`.

**Typo.** The source's row pointers replace the coordinate array $\mathrm{JR}$ even
though the prose prints $\mathrm{JC}$. The decoder uses $\mathrm{JA}$ for columns. -/
theorem example_3_7_csr :
    (∀ i j, matrix_3_7 i j =
        ∑ p : Fin 12, if csrIA i.castSucc ≤ (p : ℕ) ∧ (p : ℕ) < csrIA i.succ ∧ csrJA p = j
          then csrAA p else 0) ∧
      csrIA 5 = csrIA 0 + 12 ∧
      (∀ i : Fin 5, csrIA i.castSucc ≤ csrIA i.succ) := by
  refine ⟨fun i j => ?_, by decide, by decide⟩
  fin_cases i <;> fin_cases j <;> simp [matrix_3_7, csrAA, csrJA, csrIA, Fin.sum_univ_succ]

/-- **Section 3.4** of [saad2003iterative], the array $\mathrm{AA}$ of the modified sparse row
format of the matrix of Example 3.7: the five diagonal entries, then the unused position $n + 1$
that the source marks $*$, then the off-diagonal entries row by row. The value $*$ at the unused
position is a parameter. -/
def msrAA (star : ℝ) : Fin 13 → ℝ := ![1, 4, 7, 11, 12, star, 2, 3, 5, 6, 8, 9, 10]

/-- **Section 3.4** of [saad2003iterative], the array $\mathrm{JA}$ of the modified sparse row
format of the matrix of Example 3.7: the $n + 1$ row pointers, then the column index of each
stored off-diagonal entry, all $0$-based. The source counts positions from $1$, so its
$\mathrm{JA}(1) = 7$ is `SaadSparse.Chapter03.msrJA 0 = 6` here. -/
def msrJA : Fin 13 → ℕ := ![6, 7, 9, 12, 13, 13, 3, 0, 3, 0, 3, 4, 2]

/-- The row pointers of the modified sparse row format of Example 3.7: the first $n + 1 = 6$ entries
of the array $\mathrm{JA}$. -/
def msrPtr (i : Fin 6) : ℕ := msrJA (Fin.castLE (by norm_num) i)

/-- **Section 3.4** of [saad2003iterative], the modified sparse row format of the matrix of Example
3.7. Let $A$ be this matrix, let $\mathrm{AA}$ and $\mathrm{JA}$ be the two arrays of its
modified sparse row format, with an arbitrary value $*$ at the unused position $n + 1$ of
$\mathrm{AA}$, and let $\mathrm{JA}(1), \dots, \mathrm{JA}(n + 1)$ be the row pointers. Then the
following hold.

* $\mathrm{AA}(i) = a_{ii}$ for $i = 1, \dots, 5$: the first $n$ positions of $\mathrm{AA}$
  contain the diagonal elements of the matrix in order.
* For all $i \neq j$, $$a_{ij} = \sum_{p \,:\, \mathrm{JA}(i) \le p < \mathrm{JA}(i + 1),\
  \mathrm{JA}(p) = j} \mathrm{AA}(p).$$
* $\mathrm{JA}(n) = \mathrm{JA}(n + 1) = 14$, in the $1$-based counting of the source.

The second clause is the round trip for the off-diagonal entries. The third is the closing
observation of the source, and says that the last row is a zero row after its diagonal element
is removed. The statement holds for every value of $*$.

All arrays are $0$-based here, so the third clause reads `msrPtr 4 = 13 ∧ msrPtr 5 = 13`, and a
column $j$ in the second clause is compared with `msrJA p` as a natural number. -/
theorem example_3_7_msr (star : ℝ) :
    (∀ i : Fin 5, msrAA star (Fin.castLE (by norm_num) i) = matrix_3_7 i i) ∧
      (∀ i j : Fin 5, i ≠ j → matrix_3_7 i j =
        ∑ p : Fin 13, if msrPtr i.castSucc ≤ (p : ℕ) ∧ (p : ℕ) < msrPtr i.succ ∧ msrJA p = (j : ℕ)
          then msrAA star p else 0) ∧
      msrPtr 4 = 13 ∧ msrPtr 5 = 13 := by
  refine ⟨fun i => ?_, fun i j hij => ?_, by decide, by decide⟩
  · fin_cases i <;> simp [msrAA, matrix_3_7, Fin.castLE]
  · fin_cases i <;> fin_cases j <;>
      simp_all [matrix_3_7, msrAA, msrJA, msrPtr, Fin.sum_univ_succ]

/-! ### Examples 3.8 and 3.9: the diagonal and Ellpack-Itpack formats -/

/-- **Example 3.8** of [saad2003iterative], the matrix. It is the $5 \times 5$ matrix
$$\begin{bmatrix} 1 & 0 & 2 & 0 & 0 \\ 3 & 4 & 0 & 5 & 0 \\ 0 & 6 & 7 & 0 & 8 \\ 0 & 0 & 9 & 10
  & 0 \\ 0 & 0 & 0 & 11 & 12 \end{bmatrix},$$
whose nonzero entries lie on the three diagonals with offsets $-1$, $0$ and $2$. Example 3.9 and
Example 11.1 use the same matrix. -/
def matrix_3_8 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 2, 0, 0;
     3, 4, 0, 5, 0;
     0, 6, 7, 0, 8;
     0, 0, 9, 10, 0;
     0, 0, 0, 11, 12]

/-- **Example 3.8** of [saad2003iterative], the array $\mathrm{IOFF}$ of the diagonal format: the
offsets $-1$, $0$ and $2$ of the three stored diagonals. -/
def ioff_3_8 : Fin 3 → ℤ := ![-1, 0, 2]

/-- **Example 3.8** of [saad2003iterative], the array $\mathrm{DIAG}$ of the diagonal format: the
three diagonals with offsets $-1$, $0$ and $2$, stored as the columns of an
$n \times N_d = 5 \times 3$ array. The three positions that the source marks $*$ fall off the
ends of the subdiagonal and the superdiagonal.

**Reading.** The three unused positions can carry arbitrary data. The definition
uses one common parameter for those positions. -/
def diag_3_8 (star : ℝ) : Matrix (Fin 5) (Fin 3) ℝ :=
  !![star, 1, 2;
     3, 4, 5;
     6, 7, 8;
     9, 10, star;
     11, 12, star]

/-- **Example 3.8** of [saad2003iterative], the diagonal format. Let $A$ be the matrix of Example
3.8, and let $\mathrm{DIAG}$ and $\mathrm{IOFF}$ be the arrays of its diagonal format, with an
arbitrary value $*$ at the unused positions. Then the following hold.

* For all $i, c$, $$a_{ic} = \sum_{j \,:\, c = i + \mathrm{IOFF}(j)} \mathrm{DIAG}(i, j).$$
* If $a_{ic} \neq 0$, then $c = i + \mathrm{IOFF}(j)$ for some $j$.
* If $i + \mathrm{IOFF}(j)$ is not a column index of $A$, then $\mathrm{DIAG}(i, j) = *$.

The first clause is the round trip, read through the defining relation $\mathrm{DIAG}(i, j) =
a_{i, i + \mathrm{IOFF}(j)}$ of the source: $a_{ic}$ is the value that $\mathrm{DIAG}$ holds on
the stored diagonal through $(i, c)$, and $0$ when no stored diagonal passes through $(i, c)$.
The second is the hypothesis of the format, that every nonzero entry lies on a stored diagonal,
and it follows from the first. The third identifies the positions marked $*$: they are those
where $i + \mathrm{IOFF}(j)$ is not a column of the matrix, and they carry no information.

**Reading.** The statement uses one parameter for the source's three unused positions.
Their shared value never enters the sums for valid columns.

The column $i + \mathrm{IOFF}(j)$ is computed in $\mathbb{Z}$, with $0$-based indices. -/
theorem example_3_8 (star : ℝ) :
    (∀ i c : Fin 5, matrix_3_8 i c =
        ∑ j : Fin 3, if (c : ℤ) = (i : ℤ) + ioff_3_8 j then diag_3_8 star i j else 0) ∧
      (∀ i c : Fin 5, matrix_3_8 i c ≠ 0 → ∃ j : Fin 3, (c : ℤ) = (i : ℤ) + ioff_3_8 j) ∧
      (∀ (i : Fin 5) (j : Fin 3), (∀ c : Fin 5, (c : ℤ) ≠ (i : ℤ) + ioff_3_8 j) →
        diag_3_8 star i j = star) := by
  have hdec : ∀ i c : Fin 5, matrix_3_8 i c =
      ∑ j : Fin 3, if (c : ℤ) = (i : ℤ) + ioff_3_8 j then diag_3_8 star i j else 0 := by
    intro i c
    fin_cases i <;> fin_cases c <;> simp [matrix_3_8, diag_3_8, ioff_3_8, Fin.sum_univ_succ]
  refine ⟨hdec, fun i c hic => ?_, fun i j h => ?_⟩
  · by_contra hc
    refine hic ?_
    rw [hdec i c]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun hj => absurd ⟨j, hj⟩ hc
  · revert h
    fin_cases i <;> fin_cases j <;> intro h <;>
      first
        | (exact absurd h (by decide))
        | simp [diag_3_8]

/-- **Example 3.9** of [saad2003iterative], the array $\mathrm{COEF}$ of the Ellpack-Itpack format
of the matrix of Example 3.8: the nonzero entries of each row, with the short rows completed by
zeros. -/
def coef_3_9 : Matrix (Fin 5) (Fin 3) ℝ :=
  !![1, 2, 0;
     3, 4, 5;
     6, 7, 8;
     9, 10, 0;
     11, 12, 0]

/-- **Example 3.9** of [saad2003iterative], the array $\mathrm{JCOEF}$ of the Ellpack-Itpack format:
the column position of each entry of $\mathrm{COEF}$, $0$-based.

The columns of the padding zeros of the short rows 1, 4 and 5 are the row numbers, as the source
says. Any column would do, and `SaadSparse.Chapter03.example_3_9` holds for this choice because
the padding entries of $\mathrm{COEF}$ are zero. -/
def jcoef_3_9 : Matrix (Fin 5) (Fin 3) (Fin 5) :=
  !![0, 2, 0;
     0, 1, 3;
     1, 2, 4;
     2, 3, 3;
     3, 4, 4]

/-- **Example 3.9** of [saad2003iterative], the Ellpack-Itpack format. Let $A$ be the matrix of
Example 3.8, and let $\mathrm{COEF}$ and $\mathrm{JCOEF}$ be the arrays of its Ellpack-Itpack
format, with three positions in each row. Then the following hold.

* For all $i, j$, $$a_{ij} = \sum_{p \,:\, \mathrm{JCOEF}(i, p) = j} \mathrm{COEF}(i, p).$$
* For every $x \in \mathbb{R}^5$ and every row $i$, $$(Ax)_i = \sum_{p = 1}^{3} \mathrm{COEF}(i,
  p)\, x_{\mathrm{JCOEF}(i, p)}.$$

The first clause is the round trip. The second is the purpose of the format: it is the inner
loop of the matrix-by-vector product of Algorithm 11.5.

The padding zeros are harmless because they are zero. Their column numbers are chosen
arbitrarily, and here they repeat a column that is already used, so the pointwise reading
$\mathrm{COEF}(i, j) = a_{i, \mathrm{JCOEF}(i, j)}$ is false, while the two clauses above are
true. The product $Ax$ is `matrix_3_8 *ᵥ x`. -/
theorem example_3_9 :
    (∀ i j : Fin 5, matrix_3_8 i j =
        ∑ p : Fin 3, if jcoef_3_9 i p = j then coef_3_9 i p else 0) ∧
      (∀ (x : Fin 5 → ℝ) (i : Fin 5),
        (matrix_3_8 *ᵥ x) i = ∑ p : Fin 3, coef_3_9 i p * x (jcoef_3_9 i p)) := by
  refine ⟨fun i j => ?_, fun x i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [matrix_3_8, coef_3_9, jcoef_3_9, Fin.sum_univ_succ]
  · fin_cases i <;>
      simp [matrix_3_8, coef_3_9, jcoef_3_9, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end SaadSparse.Chapter03
