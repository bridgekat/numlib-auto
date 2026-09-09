import NumlibSurface.SaadSparse.Common

/-!
# Saad §3.4: storage schemes

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §3.4: the coordinate format, compressed sparse row and column, the modified sparse row
format, the diagonal format and Ellpack-Itpack.

The section states no theorem, proposition, lemma, corollary or numbered definition: it is
data-structure description, and its content is three worked examples, which is what this file
carries.  Each of them writes one small matrix out in one layout, and each is stated here as the
*round trip* the layout promises — the arrays decode to the matrix they came from:

* `example_3_7` is the coordinate format of Example 3.7, `example_3_7_csr` the compressed sparse
  row form of the same matrix and `example_3_7_msr` the modified sparse row form, the two layouts
  §3.4 goes on to write out for "the above matrix".
* `example_3_8` is the diagonal format, stated through the book's own defining relation
  `DIAG(i, j) = a_{i, i + ioff(j)}`.
* `example_3_9` is Ellpack-Itpack, stated as the identity that makes Algorithm 11.5 correct.

## Conventions

Saad indexes his arrays from `1`; here they are `0`-based, so the book's `IA(1) = 1` is
`csrIA 0 = 0` and a column number `j` of the book is `j - 1`.  The lengths are the book's: twelve
stored values in Example 3.7, `n + 1 + 7 = 13` positions in the modified sparse row arrays, and
`n × Nd = 5 × 3` in the diagonal and Ellpack-Itpack ones.

The positions the book marks `*` are genuinely unused, and that is how they are stated: the two
declarations that meet one quantify over its value, so no proof can depend on it.

A "round trip" statement is a single equation `A i j = (what the arrays say about entry (i, j))`.
It is stronger than the two containments read separately: it says that every stored value is an
entry of `A`, that every nonzero entry is stored, and that nothing is stored twice in a way that
would change the sum.  For the coordinate format the further claim that the twelve triples are
*distinct*, so that the array length really is `Nz`, is stated on its own.

## Not formalized

The two matrix-by-vector code fragments of §3.5 and the compressed sparse column variant, which the
section names but does not write out.  `plans/NumlibSurface/SaadSparse/Chapter03.toml` records the
rest of the chapter's exclusions.
-/

open Finset Matrix

namespace SaadSparse.Chapter03

/-! ### Example 3.7: the coordinate, compressed sparse row and modified sparse row formats -/

/-- The `5 × 5` matrix of Example 3.7, with the twelve nonzero entries `1.` to `12.`. -/
def matrix_3_7 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 2, 0;
     3, 4, 0, 5, 0;
     6, 0, 7, 8, 9;
     0, 0, 10, 11, 0;
     0, 0, 0, 0, 12]

/-- The array `AA` of Example 3.7's coordinate format: the twelve nonzero values, in the arbitrary
order the book lists them in. -/
def cooAA : Fin 12 → ℝ := ![12, 9, 7, 5, 1, 2, 11, 3, 6, 4, 8, 10]

/-- The array `JR` of Example 3.7: the row index of each stored value, `0`-based. -/
def cooJR : Fin 12 → Fin 5 := ![4, 2, 2, 1, 0, 0, 3, 1, 2, 1, 2, 3]

/-- The array `JC` of Example 3.7: the column index of each stored value, `0`-based. -/
def cooJC : Fin 12 → Fin 5 := ![4, 4, 2, 3, 0, 3, 3, 0, 0, 1, 3, 2]

/-- **Saad Example 3.7**, the coordinate format: the arrays `AA`, `JR`, `JC` represent the matrix.

The first clause is the round trip — entry `(i, j)` of the matrix is the sum of the stored values
whose row and column indices are `i` and `j` — the second says that only nonzero values are
stored, and the third that the twelve triples are pairwise distinct, so that the arrays have the
book's length `Nz = 12` and the sum of the first clause has at most one term. -/
theorem example_3_7 :
    (∀ i j, matrix_3_7 i j = ∑ k : Fin 12, if cooJR k = i ∧ cooJC k = j then cooAA k else 0) ∧
      (∀ k, cooAA k ≠ 0) ∧
      (∀ k l : Fin 12, cooJR k = cooJR l → cooJC k = cooJC l → k = l) := by
  refine ⟨fun i j => ?_, fun k => ?_, by decide⟩
  · fin_cases i <;> fin_cases j <;> simp [matrix_3_7, cooAA, cooJR, cooJC, Fin.sum_univ_succ]
  · fin_cases k <;> norm_num [cooAA]

/-- The array `AA` of the compressed sparse row form of Example 3.7's matrix: the nonzero values,
row by row. -/
def csrAA : Fin 12 → ℝ := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- The array `JA` of the compressed sparse row form: the column index of each stored value. -/
def csrJA : Fin 12 → Fin 5 := ![0, 3, 0, 1, 3, 0, 2, 3, 4, 2, 3, 4]

/-- The array `IA` of the compressed sparse row form: the position at which each row starts, with
the extra entry `IA(n + 1) = IA(1) + Nz` at the end. -/
def csrIA : Fin 6 → ℕ := ![0, 2, 5, 9, 11, 12]

/-- **Saad §3.4**, the compressed sparse row form of the matrix of Example 3.7: the arrays `AA`,
`JA`, `IA` represent it.

The first clause is the round trip, restricted for each row `i` to the block
`IA(i) ≤ p < IA(i + 1)` of positions the pointer array assigns to it; the second is the book's
remark that `IA(n + 1)` is `IA(1) + Nz`, and the third that `IA` is non-decreasing, so the blocks it
cuts out are consecutive and disjoint — which is what makes a pointer array a pointer array. -/
theorem example_3_7_csr :
    (∀ i j, matrix_3_7 i j =
        ∑ p : Fin 12, if csrIA i.castSucc ≤ (p : ℕ) ∧ (p : ℕ) < csrIA i.succ ∧ csrJA p = j
          then csrAA p else 0) ∧
      csrIA 5 = csrIA 0 + 12 ∧
      (∀ i : Fin 5, csrIA i.castSucc ≤ csrIA i.succ) := by
  refine ⟨fun i j => ?_, by decide, by decide⟩
  fin_cases i <;> fin_cases j <;> simp [matrix_3_7, csrAA, csrJA, csrIA, Fin.sum_univ_succ]

/-- The array `AA` of the modified sparse row form of Example 3.7's matrix: the five diagonal
entries, the unused position `n + 1` the book marks `*`, and then the off-diagonal entries row by
row.  The unused position is a parameter, so that nothing can depend on it. -/
def msrAA (star : ℝ) : Fin 13 → ℝ := ![1, 4, 7, 11, 12, star, 2, 3, 5, 6, 8, 9, 10]

/-- The array `JA` of the modified sparse row form: the `n + 1` row pointers first, then the column
index of each stored off-diagonal entry.  The book's positions are `1`-based, so its `JA(1) = 7`
is `msrJA 0 = 6` here. -/
def msrJA : Fin 13 → ℕ := ![6, 7, 9, 12, 13, 13, 3, 0, 3, 0, 3, 4, 2]

/-- The row pointers of the modified sparse row form, the first `n + 1` entries of `JA`. -/
def msrPtr (i : Fin 6) : ℕ := msrJA (Fin.castLE (by norm_num) i)

/-- **Saad §3.4**, the modified sparse row form of the matrix of Example 3.7: the two arrays `AA`
and `JA` represent it.

The first clause is the book's "the first `n` positions in `AA` contain the diagonal elements of
the matrix in order"; the second is the round trip for the off-diagonal entries, each row `i`
reading the block `JA(i) ≤ p < JA(i + 1)`; and the third is the book's own closing observation,
`JA(n) = JA(n + 1) = 14`, which says that the last row is a zero row once the diagonal element has
been removed.  Nothing depends on the value at the unused position `n + 1` of `AA`, which is
universally quantified. -/
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

/-- The `5 × 5` matrix of Example 3.8, whose nonzero entries lie on the three diagonals with
offsets `-1`, `0` and `2`.  Example 3.9 and Example 11.1 use the same matrix. -/
def matrix_3_8 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 2, 0, 0;
     3, 4, 0, 5, 0;
     0, 6, 7, 0, 8;
     0, 0, 9, 10, 0;
     0, 0, 0, 11, 12]

/-- The array `IOFF` of Example 3.8: the offsets of the three stored diagonals. -/
def ioff_3_8 : Fin 3 → ℤ := ![-1, 0, 2]

/-- The array `DIAG` of Example 3.8, the three diagonals stored as the columns of an `n × Nd`
array.  The three positions the book marks `*` fall off the ends of the sub- and super-diagonal
and are a parameter, so that nothing can depend on them. -/
def diag_3_8 (star : ℝ) : Matrix (Fin 5) (Fin 3) ℝ :=
  !![star, 1, 2;
     3, 4, 5;
     6, 7, 8;
     9, 10, star;
     11, 12, star]

/-- **Saad Example 3.8**, the diagonal format: the arrays `DIAG` and `IOFF` represent the matrix.

The first clause is the round trip, read through the book's own defining relation
`DIAG(i, j) = a_{i, i + ioff(j)}`: entry `(i, c)` of the matrix is what `DIAG` holds on the
diagonal through it, and `0` when no stored diagonal passes through `(i, c)`.  The second is the
hypothesis of the format, that every nonzero entry does lie on one of the three stored diagonals,
and follows from the first.  The third identifies the positions of `DIAG` the book marks `*`: they
are the ones where `i + ioff(j)` is not a column of the matrix, they carry no information, and
their value is universally quantified so that nothing can depend on it. -/
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

/-- The array `COEF` of Example 3.9: the nonzero entries of each row, the short rows completed by
zeros. -/
def coef_3_9 : Matrix (Fin 5) (Fin 3) ℝ :=
  !![1, 2, 0;
     3, 4, 5;
     6, 7, 8;
     9, 10, 0;
     11, 12, 0]

/-- The array `JCOEF` of Example 3.9: the column position of each entry of `COEF`.  The columns
chosen for the padding zeros of the short rows 1, 4 and 5 are the row numbers, as the book says;
any column between `1` and `n` would do, and the statement of `example_3_9` holds for the choice
made here because the padded entries of `COEF` are zero. -/
def jcoef_3_9 : Matrix (Fin 5) (Fin 3) (Fin 5) :=
  !![0, 2, 0;
     0, 1, 3;
     1, 2, 4;
     2, 3, 3;
     3, 4, 4]

/-- **Saad Example 3.9**, the Ellpack-Itpack format: the arrays `COEF` and `JCOEF` represent the
matrix of Example 3.8.

The first clause is the round trip, and the second is what the format is for: the matrix-by-vector
product is the row-wise sum `y_i = ∑_j COEF(i, j) x(JCOEF(i, j))`, which is the inner loop of
Algorithm 11.5.  The padded zeros are harmless exactly because they are zero: their column numbers
are chosen arbitrarily, and here they repeat a column that is already used, so the *pointwise*
reading `COEF(i, j) = a_{i, JCOEF(i, j)}` would be false while these two are true. -/
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
