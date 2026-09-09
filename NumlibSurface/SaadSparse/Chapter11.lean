import NumlibSurface.SaadSparse.Chapter03.Section03
import NumlibSurface.SaadSparse.Chapter03.Section04

/-!
# Saad Chapter 11: parallel implementations

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, Chapter 11.

The chapter contains **no theorem, proposition, lemma, corollary or numbered definition** — a
search for any of those words followed by an `11.n` over the whole chapter returns nothing — one
tagged display, (11.1), which is `L x = b`, Algorithms 11.1–11.8, and two numbered examples.
Section by section: §11.1 introduction; §11.2 forms of parallelism (functional units, pipelining,
vector processors, multiprocessing); §11.3 shared- and distributed-memory architectures; §11.4
types of operations; §11.5 storage formats and the matrix-vector product in each (CSR/CSC,
diagonal, Ellpack-Itpack, jagged diagonal, distributed sparse matrices); §11.6 the standard
preconditioning operations, parallelism in forward sweeps, and level scheduling for 5-point
matrices and for irregular graphs.

So this module is one example.  `example_11_1` is Example 11.1, the jagged diagonal format of
§11.5.4 written out for one `5 × 5` matrix — the same matrix as Examples 3.8 and 3.9, which is why
this file reads it from `Chapter03/Section04.lean` rather than writing it again — and, like the
storage examples of §3.4, it is stated as the round trip the layout promises: the arrays `DJ`,
`JDIAG` and `IDIAG` decode to the row-sorted matrix `PA`.  The row permutation is Saad's `P`, and
`Chapter03.proposition_3_2` is what turns the sorted matrix into `P A`.

The one other place with mathematical substance is §11.6.3, which defines the depth of a vertex of
the dependency graph of a triangular solve by `depth(i) = 1 + max {depth(j) : l_ij ≠ 0}` and calls
a *level* the set of vertices of equal depth.  The book states no property of it: not that the
levels partition the vertices, not that their number bounds the parallel depth, not that the
permuted matrix is block strictly lower triangular.  There is nothing to state faithfully to the
book, so nothing is missing here; a source that does state such a property would be planned with
that source.

Example 11.2 is not tracked: it is level scheduling on a mesh obtained by refining Figure 3.1,
and neither the mesh nor the permuted matrix of Figure 11.12 is reproduced in the source text, so
there is nothing to state it over.
-/

open Finset Matrix

namespace SaadSparse.Chapter11

/-! ### Example 11.1: the jagged diagonal format -/

/-- The row permutation of Example 11.1, which sorts the rows of the matrix by decreasing number of
nonzero entries: the new rows are the old rows `2, 3, 1, 4, 5`.  Saad's `P` is its permutation
matrix. -/
def perm_11_1 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv := by decide
  right_inv := by decide

/-- The matrix `PA` of Example 11.1: the matrix of Examples 3.8 and 3.9 with its rows sorted by
decreasing number of nonzero entries. -/
def sorted_11_1 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![3, 4, 0, 5, 0;
     0, 6, 7, 0, 8;
     1, 0, 2, 0, 0;
     0, 0, 9, 10, 0;
     0, 0, 0, 11, 12]

/-- The array `DJ` of Example 11.1: the values of the jagged diagonals of `PA`, one j-diagonal
after another. -/
def dj_11_1 : Fin 12 → ℝ := ![3, 6, 1, 9, 11, 4, 7, 2, 10, 12, 5, 8]

/-- The array `JDIAG` of Example 11.1: the column position of each value of `DJ`, `0`-based. -/
def jdiag_11_1 : Fin 12 → Fin 5 := ![0, 1, 0, 2, 3, 1, 2, 2, 3, 4, 3, 4]

/-- The array `IDIAG` of Example 11.1: the position at which each j-diagonal starts, with the
length of the array at the end. -/
def idiag_11_1 : Fin 4 → ℕ := ![0, 5, 10, 12]

/-- The row of `PA` that each stored value belongs to: the `k`-th stored value belongs to row
`k - IDIAG(d)` of the `d`-th j-diagonal, which is the third clause of `example_11_1`. -/
def jrow_11_1 : Fin 12 → Fin 5 := ![0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1]

/-- The number of nonzero entries in each row of `PA`, which the sorting makes non-increasing. -/
def rowNnz_11_1 : Fin 5 → ℕ := ![3, 3, 2, 2, 2]

/-- **Saad Example 11.1**: the jagged diagonal format of §11.5.4 on one `5 × 5` matrix.

The clauses are the example read in order.  `PA` is `P A` for the permutation that sorts the rows
by number of nonzero entries, largest first — the identification of the sorted matrix with a
product by a permutation matrix being `Chapter03.proposition_3_2`; the row counts are `3, 3, 2, 2,
2`, which is non-increasing; the `k`-th stored value belongs to row `k - IDIAG(d)` of the `d`-th
j-diagonal, which is what `jrow_11_1` records; the arrays `DJ`, `JDIAG` then decode to `PA`; and
the three j-diagonals have the lengths the example closes with, "two j-diagonals of full length
(five) and one of length two". -/
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
