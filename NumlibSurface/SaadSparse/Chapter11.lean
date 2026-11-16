/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.SaadSparse.Chapter03.Section03
import NumlibSurface.SaadSparse.Chapter03.Section04

/-!
# Saad, Chapter 11: Parallel implementations

This module formalizes the one example of Chapter 11 of [saad2003iterative] with mathematical
content: Example 11.1, the jagged diagonal format of Section 11.5.4. The chapter describes forms of
parallelism, parallel architectures, the types of operations, the storage formats of sparse matrices
with their matrix-vector products, and the parallelism of the standard preconditioning operations.
It contains no theorem, proposition, lemma, corollary or numbered definition; besides Algorithms
11.1–11.8 and the display (11.1), which is $Lx = b$, it has two numbered examples.

Example 11.1 stores a $5 \times 5$ matrix $A$ in the jagged diagonal format. The rows of $A$ are
first permuted by decreasing number of nonzero entries, which gives $PA$ for a permutation matrix
$P$. The $j$-th jagged diagonal of $PA$ consists of the $j$-th nonzero entries of the rows, and the
arrays `DJ`, `JDIAG` and `IDIAG` store their values, their columns and their starting positions. The
matrix is that of Examples 3.8 and 3.9, `SaadSparse.Chapter03.matrix_3_8` of
`NumlibSurface.SaadSparse.Chapter03.Section04`. Like the storage examples of Section 3.4, the
example is stated as the round trip that the layout promises: the arrays decode to $PA$.

## Main definitions

* Example 11.1, `SaadSparse.Chapter11.perm_11_1`: the permutation that sorts the rows.
* Example 11.1, `SaadSparse.Chapter11.sorted_11_1`: the matrix $PA$.
* Example 11.1, `SaadSparse.Chapter11.dj_11_1`: the array `DJ` of values.
* Example 11.1, `SaadSparse.Chapter11.jdiag_11_1`: the array `JDIAG` of column positions.
* Example 11.1, `SaadSparse.Chapter11.idiag_11_1`: the array `IDIAG` of starting positions.
* Example 11.1, `SaadSparse.Chapter11.jrow_11_1`: the row of each stored value.
* Example 11.1, `SaadSparse.Chapter11.rowNnz_11_1`: the number of nonzero entries in each row of
  $PA$.

## Main results

* Example 11.1, `SaadSparse.Chapter11.example_11_1`: the jagged diagonal format of $PA$ decodes to
  $PA$, and its three jagged diagonals have the lengths $5$, $5$ and $2$.

## Conventions

* Indices are $0$-based. The arrays `JDIAG` and `IDIAG` hold $0$-based positions, so each entry is
  one less than in the book.

## Implementation notes

* The identification of the sorted matrix with the product $PA$ by a permutation matrix is
  `SaadSparse.Chapter03.proposition_3_2`.

## Not formalized

* **Example 11.2.** It is level scheduling on a mesh obtained by refining Figure 3.1, and neither
  the mesh nor the permuted matrix of Figure 11.12 is reproduced in the source text, so there is
  nothing to state it over.
* **Section 11.6.3** (level scheduling). The book defines the depth of a vertex of the dependency
  graph of a triangular solve by $\mathrm{depth}(i) = 1 + \max\{\mathrm{depth}(j) : l_{ij} \neq 0\}$
  and calls a level the set of vertices of equal depth, but it states no property of these notions:
  not that the levels partition the vertices, not that their number bounds the parallel depth, and
  not that the permuted matrix is block strictly lower triangular.
* **Algorithms 11.1–11.8.**
-/

open Finset Matrix

namespace SaadSparse.Chapter11

/-! ### Example 11.1: the jagged diagonal format -/

/-- **Example 11.1** of [saad2003iterative], the row permutation. The permutation $\pi$ of
$\{0, \dots, 4\}$ with $\pi = (1, 2, 0, 3, 4)$ sorts the rows of the matrix by decreasing number
of nonzero entries: row $r$ of the sorted matrix is row $\pi(r)$ of the original matrix. In the
book's $1$-based numbering, the new rows are the old rows $2, 3, 1, 4, 5$. The book's $P$ is the
permutation matrix of $\pi$. -/
def perm_11_1 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv := by decide
  right_inv := by decide

/-- **Example 11.1** of [saad2003iterative], the matrix
$$PA = \begin{bmatrix}
  3 & 4 & 0 & 5 & 0 \\
  0 & 6 & 7 & 0 & 8 \\
  1 & 0 & 2 & 0 & 0 \\
  0 & 0 & 9 & 10 & 0 \\
  0 & 0 & 0 & 11 & 12
\end{bmatrix}.$$
It is the matrix of Examples 3.8 and 3.9 with its rows sorted by decreasing number of nonzero
entries. -/
def sorted_11_1 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![3, 4, 0, 5, 0;
     0, 6, 7, 0, 8;
     1, 0, 2, 0, 0;
     0, 0, 9, 10, 0;
     0, 0, 0, 11, 12]

/-- **Example 11.1** of [saad2003iterative], the array
$$\mathtt{DJ} = (3, 6, 1, 9, 11, 4, 7, 2, 10, 12, 5, 8)$$
of the values of the jagged diagonals of $PA$, one jagged diagonal after another. -/
def dj_11_1 : Fin 12 → ℝ := ![3, 6, 1, 9, 11, 4, 7, 2, 10, 12, 5, 8]

/-- **Example 11.1** of [saad2003iterative], the array
$$\mathtt{JDIAG} = (0, 1, 0, 2, 3, 1, 2, 2, 3, 4, 3, 4)$$
of the column positions of the values in `DJ`, counted from $0$. -/
def jdiag_11_1 : Fin 12 → Fin 5 := ![0, 1, 0, 2, 3, 1, 2, 2, 3, 4, 3, 4]

/-- **Example 11.1** of [saad2003iterative], the array
$$\mathtt{IDIAG} = (0, 5, 10, 12)$$
of the positions in `DJ` at which the jagged diagonals start, counted from $0$, followed by the
length of `DJ`. -/
def idiag_11_1 : Fin 4 → ℕ := ![0, 5, 10, 12]

/-- **Example 11.1** of [saad2003iterative], the row of $PA$ of each stored value:
$$(0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1).$$
The $k$-th stored value belongs to row $k - \mathtt{IDIAG}(d)$ of the $d$-th jagged diagonal;
this is the fourth clause of `SaadSparse.Chapter11.example_11_1`. -/
def jrow_11_1 : Fin 12 → Fin 5 := ![0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1]

/-- **Example 11.1** of [saad2003iterative], the numbers $(3, 3, 2, 2, 2)$ of nonzero entries in the
rows of $PA$. The sorting makes them non-increasing. -/
def rowNnz_11_1 : Fin 5 → ℕ := ![3, 3, 2, 2, 2]

/-- **Example 11.1** of [saad2003iterative], the jagged diagonal format on one $5 \times 5$ matrix.
Let $A$ be the matrix of Example 3.8, let $\pi$ and $P$ be the permutation and its permutation
matrix, and let `DJ`, `JDIAG` and `IDIAG` be the arrays of the example. Then:

* the sorted matrix `SaadSparse.Chapter11.sorted_11_1` is the product $PA$;
* the rows of $PA$ have $3, 3, 2, 2, 2$ nonzero entries, which is non-increasing;
* for each position $k \in \{0, \dots, 11\}$ of `DJ` there is a jagged diagonal
  $d \in \{0, 1, 2\}$ with $\mathtt{IDIAG}(d) \le k < \mathtt{IDIAG}(d + 1)$, and the value at
  $k$ belongs to row $k - \mathtt{IDIAG}(d)$ of $PA$;
* the arrays `DJ` and `JDIAG` decode to $PA$: $(PA)_{rc}$ is the sum of the values
  $\mathtt{DJ}(k)$ with row $r$ and $\mathtt{JDIAG}(k) = c$;
* the three jagged diagonals have the lengths $5$, $5$ and $2$: "two j-diagonals of full length
  (five) and one of length two".

The identification of the sorted matrix with the product $PA$ is
`SaadSparse.Chapter03.proposition_3_2`. The row of each stored value is
`SaadSparse.Chapter11.jrow_11_1`. -/
theorem example_11_1 :
    sorted_11_1 = perm_11_1.permMatrix ℝ * Chapter03.matrix_3_8 ∧
      (∀ r : Fin 5, (∑ c : Fin 5, if sorted_11_1 r c = 0 then 0 else 1) = rowNnz_11_1 r) ∧
      Antitone rowNnz_11_1 ∧
      (∀ k : Fin 12, ∃ d : Fin 3, idiag_11_1 d.castSucc ≤ (k : ℕ) ∧
          (k : ℕ) < idiag_11_1 d.succ ∧ (k : ℕ) - idiag_11_1 d.castSucc = (jrow_11_1 k : ℕ)) ∧
      (∀ r c : Fin 5, sorted_11_1 r c =
        ∑ k : Fin 12, if jrow_11_1 k = r ∧ jdiag_11_1 k = c then dj_11_1 k else 0) ∧
      idiag_11_1 1 - idiag_11_1 0 = 5 ∧ idiag_11_1 2 - idiag_11_1 1 = 5 ∧
      idiag_11_1 3 - idiag_11_1 2 = 2 := by
  refine ⟨?_, fun r => ?_, by decide, by decide, fun r c => ?_, by decide, by decide, by decide⟩
  · have h : Chapter03.matrix_3_8.submatrix perm_11_1 id = sorted_11_1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [← h]
    exact (Chapter03.proposition_3_2 Chapter03.matrix_3_8 perm_11_1).1
  · fin_cases r <;> norm_num [sorted_11_1, rowNnz_11_1, Fin.sum_univ_succ]
  · fin_cases r <;> fin_cases c <;>
      simp [sorted_11_1, dj_11_1, jdiag_11_1, jrow_11_1, Fin.sum_univ_succ]

end SaadSparse.Chapter11
