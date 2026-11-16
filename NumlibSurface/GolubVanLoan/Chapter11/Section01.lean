/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.MinMax
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Sparse.Fill
import Numlib.LinearAlgebra.Sparse.Reordering
import NumlibSurface.GolubVanLoan.Chapter04.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section02

/-!
# Golub and Van Loan, Section 11.1: Direct methods

This module formalizes §11.1 of [golub2013matrix], which treats direct methods for sparse linear
systems: sparse Cholesky, QR and LU factorizations. The section has no numbered theorem. Its precise
content is the following. The compressed-column format of §11.1.1 has two algorithms, the sparse
gaxpy (11.1.1) and the outer-product update with a preallocated pattern (11.1.2). The first step
(11.1.3)–(11.1.4) of the outer-product Cholesky factorization and the first step (11.1.10)–(11.1.11)
of the pivoted LU factorization are each one Schur complement. The graph facts of §11.1.4–11.1.7 say
that a symmetric permutation relabels the adjacency graph, that a level-set (Cuthill–McKee) ordering
is block tridiagonal, that the Cholesky factor vanishes off the symbolic fill of Facts 1–2 (Parter's
rule), and that a nested dissection creates no fill between the dissected halves. Cholesky with
symmetric pivoting (11.1.8) is a program, with the minimum-degree pivot rule. The section also
contains the seminormal equations of §11.1.8, the row-by-row Givens QR factorization (11.1.9), and
the structural-symmetry remark of §11.1.9 in its symbolic reading, with a counterexample to the
literal one.

The proofs use the Schur complement of `Numlib.LinearAlgebra.Matrix.SchurComplement`, the sparsity
patterns and the symbolic fill of `Numlib.LinearAlgebra.Sparse.Fill` and
`Numlib.LinearAlgebra.Sparse.Reordering`, the Cholesky results of §4.2 and the Givens QR
factorization of §5.2.

## Main definitions

* §11.1.1, `GolubVanLoan.Chapter11.CompressedColumn`: the compressed-column format.
* §11.1.1, `GolubVanLoan.Chapter11.CompressedColumn.toMatrix`: the matrix that a compressed-column
  structure represents.
* Equation (11.1.1), `GolubVanLoan.Chapter11.sparseGaxpy`: the sparse gaxpy, as a program.
* Equation (11.1.2), `GolubVanLoan.Chapter11.sparseOuterProductUpdate`: the outer-product update
  with a preallocated pattern, as a program.
* Equation (11.1.6), `GolubVanLoan.Chapter11.profileIndex`: the profile index $f_i(A)$, the column
  of the first nonzero entry of row $i$ at or left of the diagonal.
* §11.1.5, `GolubVanLoan.Chapter11.profile`: the profile $n + \sum_i (i - f_i(A))$.
* §11.1.6, `GolubVanLoan.Chapter11.minDegreePivot`: the minimum-degree pivot rule.
* Equation (11.1.8), `GolubVanLoan.Chapter11.choleskyWithPivoting`: Cholesky with symmetric
  pivoting, as a program.
* Equation (11.1.9), `GolubVanLoan.Chapter11.rowGivensQR`: the row-by-row Givens QR factorization,
  as a program.

## Main results

* Equation (11.1.1), `GolubVanLoan.Chapter11.equation_11_1_1`: the sparse gaxpy overwrites $y$ with
  $y + Ax$.
* Equation (11.1.2), `GolubVanLoan.Chapter11.equation_11_1_2`: the update overwrites $A$ with
  $A + uv^T$ when the pattern of $A$ has room for it.
* Equations (11.1.3)–(11.1.4), `GolubVanLoan.Chapter11.equation_11_1_3`: the first step of the
  Cholesky factorization as a block factorization with the Schur complement $B - vv^T/\alpha$.
* §11.1.4, `GolubVanLoan.Chapter11.adjGraph_submatrix_iso`: a symmetric permutation relabels the
  adjacency graph.
* §11.1.5, `GolubVanLoan.Chapter11.submatrix_apply_eq_zero_of_levels_far`: entries between nodes
  whose levels differ by two or more vanish.
* Equation (11.1.8), `GolubVanLoan.Chapter11.equation_11_1_8`: Cholesky with symmetric pivoting
  computes the Cholesky factor of $PAP^T$.
* §11.1.6, `GolubVanLoan.Chapter11.minDegree_cholesky`: the same with the minimum-degree pivot rule.
* §11.1.6, `GolubVanLoan.Chapter11.cholesky_apply_eq`: the formula $g_{ij} = (a_{ij} - \sum_{k<j}
  g_{ik} g_{jk}) / g_{jj}$.
* §11.1.6, Facts 1–2, `GolubVanLoan.Chapter11.cholesky_eq_zero_of_not_isCholeskyFill`: the Cholesky
  factor vanishes off the symbolic fill.
* §11.1.7, `GolubVanLoan.Chapter11.nestedDissection_cholesky`: the Cholesky factor inherits the zero
  block of a dissection.
* §11.1.8, `GolubVanLoan.Chapter11.seminormal_cholesky`: if $AP^T = QR$, then $R$ is the Cholesky
  factor of $P(A^TA)P^T$.
* §11.1.8, `GolubVanLoan.Chapter11.seminormal_normalEquations`: the normal equations are equivalent
  to the seminormal equations $R^TR(Px) = P(A^Tb)$.
* §11.1.8, `GolubVanLoan.Chapter11.seminormal_refinement`: one step of iterative improvement with
  the seminormal equations solves the normal equations.
* Equation (11.1.9), `GolubVanLoan.Chapter11.rowGivensQR_run_eq`: in exact arithmetic the row-by-row
  Givens QR factorization is the row-oriented Givens QR factorization of §5.2.5.
* Equation (11.1.9), `GolubVanLoan.Chapter11.equation_11_1_9`: the row-by-row Givens QR
  factorization computes a QR factorization.
* Equations (11.1.10)–(11.1.11), `GolubVanLoan.Chapter11.equation_11_1_10`: the first step of
  pivoted LU as a block factorization with the Schur complement $B - vw^T/\alpha$.
* §11.1.9, `GolubVanLoan.Chapter11.symbolicElim_isPatternSymm`: the pattern that (11.1.11) predicts
  for a structurally symmetric matrix is symmetric.
* §11.1.9, `GolubVanLoan.Chapter11.symbolicElim_isPatternSymm_counterexample`: the computed
  $A^{(1)}$ need not be structurally symmetric.

## Conventions

* Matrices are real, `Matrix (Fin n) (Fin n) ℝ`, with 0-based indices: the source's $a_{ij}$,
  $i, j = 1{:}n$, is `A (i - 1) (j - 1)`.
* The source's permutation $P = I_n(:, p)$ acts as `A.submatrix p p`, which is $PAP^T$, and $Pv$ for
  a vector $v$ is `v ∘ p`.
* The lower Cholesky factor $G$ of the source, with $A = GG^T$, is $H^T$ for the backbone's
  `Matrix.IsCholesky A H`, where $H$ is upper triangular with positive diagonal and $H^H H = A$.

## Implementation notes

* The compressed-column format is the surface structure `GolubVanLoan.Chapter11.CompressedColumn`,
  read as a matrix by `GolubVanLoan.Chapter11.CompressedColumn.toMatrix`. Storage formats have no
  backbone theory, and the only claims of the source about them are that the loops (11.1.1)–(11.1.2)
  compute $y + Ax$ and $A + uv^T$.
* The programs follow the algorithm conventions of `NumlibSurface.GolubVanLoan`. They are generic in
  a monad `M` with a rounding hook `rnd : ℝ → M ℝ`, through which every product, sum, quotient and
  square root passes. Loops are `List.foldlM` over index lists, and index comparisons are exact.
* The source analyses no rounding error in this section, so only exact specifications (`M := Id`,
  `rnd := pure`) are stated.

## Deviations from the source

* **Equation (11.1.8)** (correction). The source runs the loop for $k = 1{:}n-2$, which leaves the
  last two columns unfactored; the program runs it for $k = 1{:}n$. See
  `GolubVanLoan.Chapter11.choleskyWithPivoting`.
* **Formula after Fact 2, §11.1.6** (generalization). The source states the formula for $j < i$; it
  holds for all $i$ and $j$. See `GolubVanLoan.Chapter11.cholesky_apply_eq`.
* **Facts 1–2, §11.1.6** (reading). The source says that $g_{ij}$ is nonzero at the predicted
  positions "assuming no numerical cancellation", which has no exact reading; the theorem states the
  exact converse, that $g_{ij}$ vanishes off the symbolic fill. See
  `GolubVanLoan.Chapter11.cholesky_eq_zero_of_not_isCholeskyFill`.
* **Structural symmetry, §11.1.9** (correction). The source says that one elimination step keeps
  structural symmetry; this is false for the computed $A^{(1)}$, and the theorem states it for the
  predicted pattern. See `GolubVanLoan.Chapter11.symbolicElim_isPatternSymm` and
  `GolubVanLoan.Chapter11.symbolicElim_isPatternSymm_counterexample`.

## Not formalized

* **The heuristics and challenges of choosing $P$.** Choosing $P$ to minimize $\mathrm{nnz}(G)$ is
  not a statement.
* **Markowitz pivoting and the threshold $\tau$.**
* **The elimination tree.** The source defines it in prose and states no theorem about it.
* **The row orderings for sparse QR**, including the row orderings that limit fill-in during
  (11.1.9).
* **The complexity claims of §11.1.2 and §11.1.7.**
* **Björck's accuracy claim for the seminormal equations with one refinement step.**
* **The numerical examples:** (11.1.5), its profile $37 \to 25$, and the elimination tree example of
  Davis. Numerical examples are out of scope for the library.
* **The Problems of §11.1.** Problems are out of scope for the library.
-/

open Matrix Finset

namespace GolubVanLoan.Chapter11

/-! ### §11.1.1: the compressed-column format -/

/-- **Section 11.1.1** of [golub2013matrix], the compressed-column format. An element stores an
$m \times n$ matrix with $\mathrm{nnz}$ stored entries. It consists of the stored values `val`,
the row index `row k` of each stored value, and the column starts `colStart j` for
$j = 0, \dots, n$; these are the source's $A.\mathrm{val}$, $A.r$ and $A.c$. The column starts
satisfy $A.c(0) = 0$ and $A.c(n) = \mathrm{nnz}$ and are nondecreasing, column $j$ occupies the
positions $k$ with $A.c(j) \le k < A.c(j+1)$, and inside each column the row indices are
strictly increasing.

The positions are 0-based. The condition $A.c(n) = \mathrm{nnz}$ is the 0-based form of the
source's "the last component of $A.c$ houses $\mathrm{nnz}(A) + 1$". The merge of (11.1.2)
relies on the increasing row indices. A vector of $\mathbb{R}^m$ in this format is a
`CompressedColumn m 1 nnz`. -/
structure CompressedColumn (m n nnz : ℕ) where
  /-- The stored values, the source's $A.\mathrm{val}$. -/
  val : Fin nnz → ℝ
  /-- The row index of each stored value, the source's $A.r$. -/
  row : Fin nnz → Fin m
  /-- The position where each column begins, the source's $A.c$ in 0-based form. -/
  colStart : Fin (n + 1) → ℕ
  /-- The first column begins at position $0$. -/
  colStart_zero : colStart 0 = 0
  /-- The columns end at position $\mathrm{nnz}$. -/
  colStart_last : colStart (Fin.last n) = nnz
  /-- The column starts are nondecreasing. -/
  colStart_mono : Monotone colStart
  /-- Inside each column the row indices are strictly increasing. -/
  row_strictMono : ∀ (j : Fin n) (k l : Fin nnz), colStart j.castSucc ≤ k → k < l →
    (l : ℕ) < colStart j.succ → row k < row l

namespace CompressedColumn

variable {m n nnz : ℕ} (A : CompressedColumn m n nnz)

/-- The stored positions $k$ of column $j$, those with $A.c(j) \le k < A.c(j+1)$, in increasing
order: the source's $k = A.c(j){:}A.c(j+1) - 1$. -/
def positions (j : Fin n) : List (Fin nnz) :=
  (List.finRange nnz).filter fun k => A.colStart j.castSucc ≤ k ∧ (k : ℕ) < A.colStart j.succ

/-- A position $k$ belongs to column $j$ if and only if $A.c(j) \le k < A.c(j+1)$. -/
theorem mem_positions {j : Fin n} {k : Fin nnz} :
    k ∈ A.positions j ↔ A.colStart j.castSucc ≤ k ∧ (k : ℕ) < A.colStart j.succ := by
  simp [positions]

/-- The list of positions of a column has no repeated entries. -/
theorem nodup_positions (j : Fin n) : (A.positions j).Nodup :=
  (List.nodup_finRange nnz).filter _

/-- No position belongs to two different columns. -/
theorem eq_of_mem_positions {j j' : Fin n} {k : Fin nnz} (h : k ∈ A.positions j)
    (h' : k ∈ A.positions j') : j = j' := by
  rw [mem_positions] at h h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : A.colStart j.succ ≤ A.colStart j'.castSucc :=
      A.colStart_mono (Fin.le_def.2 (by simpa using hlt))
    omega
  · have : A.colStart j'.succ ≤ A.colStart j.castSucc :=
      A.colStart_mono (Fin.le_def.2 (by simpa using hlt))
    omega

/-- Along the positions of a column the row indices are strictly increasing. -/
theorem pairwise_row_lt (j : Fin n) :
    (A.positions j).Pairwise fun k l => A.row k < A.row l := by
  refine ((List.pairwise_lt_finRange nnz).filter _).imp_of_mem fun {k l} hk hl hkl => ?_
  rw [mem_positions] at hk hl
  exact A.row_strictMono j k l hk.1 hkl hl.2

/-- Two stored positions of the same column with the same row index are equal. -/
theorem eq_of_row_eq {j : Fin n} {k l : Fin nnz} (hk : k ∈ A.positions j)
    (hl : l ∈ A.positions j) (h : A.row k = A.row l) : k = l := by
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · rw [mem_positions] at hk hl
    exact absurd h (A.row_strictMono j k l hk.1 hkl hl.2).ne
  · rfl
  · rw [mem_positions] at hk hl
    exact absurd h.symm (A.row_strictMono j l k hl.1 hkl hk.2).ne

/-- **Section 11.1.1** of [golub2013matrix], the matrix that a compressed-column structure
represents. Entry $a_{ij}$ is the stored value at the position of column $j$ whose row index is
$i$, and $a_{ij} = 0$ when column $j$ stores no entry with row index $i$.

The entry is written as the sum of the stored values of column $j$ with row index $i$. The sum
has at most one term, by `GolubVanLoan.Chapter11.CompressedColumn.eq_of_row_eq`. -/
noncomputable def toMatrix : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, if k ∈ A.positions j ∧ A.row k = i then A.val k else 0

/-- Entry $(i, j)$ of the represented matrix is the sum of the stored values of column $j$ with row
index $i$. -/
theorem toMatrix_apply (i : Fin m) (j : Fin n) :
    A.toMatrix i j = ∑ k, if k ∈ A.positions j ∧ A.row k = i then A.val k else 0 := rfl

/-- Every position of a one-column structure, that is, of a sparse vector, belongs to its only
column. -/
theorem mem_positions_zero (u : CompressedColumn m 1 nnz) (k : Fin nnz) : k ∈ u.positions 0 := by
  rw [mem_positions]
  refine ⟨by simp [u.colStart_zero], ?_⟩
  have h : (Fin.succ (0 : Fin 1)) = Fin.last 1 := rfl
  rw [h, u.colStart_last]
  exact k.2

/-- The row indices of a sparse vector are strictly increasing. -/
theorem row_strictMono_zero (u : CompressedColumn m 1 nnz) : StrictMono u.row := fun k l hkl =>
  u.row_strictMono 0 k l ((u.mem_positions.1 (u.mem_positions_zero k)).1) hkl
    ((u.mem_positions.1 (u.mem_positions_zero l)).2)

/-- Entry $i$ of a sparse vector is the sum of its stored values with row index $i$. -/
theorem toMatrix_apply_zero (u : CompressedColumn m 1 nnz) (i : Fin m) :
    u.toMatrix i 0 = ∑ k, if u.row k = i then u.val k else 0 := by
  simp [toMatrix_apply, u.mem_positions_zero]

end CompressedColumn

/-! ### §11.1.2: the sparse gaxpy and the outer-product update -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Equation (11.1.1)** of [golub2013matrix], the sparse gaxpy. For
$A \in \mathbb{R}^{m \times n}$ in compressed-column format and conventionally stored
$x \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$, the algorithm is
```
for j = 1:n
    k = A.c(j):A.c(j+1) − 1
    y(A.r(k)) = y(A.r(k)) + A.val(k)·x(j)
end
```
It overwrites $y$ with $y + Ax$ (`GolubVanLoan.Chapter11.equation_11_1_1`).

Each product and each sum is rounded. -/
def sparseGaxpy {mm n nnz : ℕ} (A : CompressedColumn mm n nnz) (x : Fin n → ℝ) (y : Fin mm → ℝ) :
    M (Fin mm → ℝ) :=
  (List.finRange n).foldlM (fun y j =>
    (A.positions j).foldlM (fun y k => do
      let p ← rnd (A.val k * x j)
      let s ← rnd (y (A.row k) + p)
      pure (Function.update y (A.row k) s)) y) y

/-- **Equation (11.1.2)** of [golub2013matrix], the outer-product update with a preallocated
pattern. For $A \in \mathbb{R}^{m \times n}$, $u \in \mathbb{R}^m$ and $v \in \mathbb{R}^n$, all
in compressed-column format, the algorithm is
```
for β = 1:nnz(v)
    j = v.r(β)
    α = 1
    for ℓ = A.c(j):A.c(j+1) − 1
        if α ≤ nnz(u) && A.r(ℓ) = u.r(α)
            A.val(ℓ) = A.val(ℓ) + u.val(α)·v.val(β)
            α = α + 1
        end
    end
end
```
It changes the stored values of $A$ and keeps the pattern.

The pattern, the fields `row` and `colStart`, is not changed. The index $\alpha$ is 0-based
here; it is the merge pointer into the stored entries of $u$. The index comparisons are exact,
and each product and each sum is rounded. -/
def sparseOuterProductUpdate {mm n nnz nu nv : ℕ} (A : CompressedColumn mm n nnz)
    (u : CompressedColumn mm 1 nu) (v : CompressedColumn n 1 nv) :
    M (CompressedColumn mm n nnz) := do
  let val ← (List.finRange nv).foldlM (fun val β => do
    let st ← (A.positions (v.row β)).foldlM (fun (st : (Fin nnz → ℝ) × ℕ) ℓ =>
      if h : st.2 < nu then
        if A.row ℓ = u.row ⟨st.2, h⟩ then do
          let p ← rnd (u.val ⟨st.2, h⟩ * v.val β)
          let s ← rnd (st.1 ℓ + p)
          pure (Function.update st.1 ℓ s, st.2 + 1)
        else pure st
      else pure st) (val, 0)
    pure st.1) A.val
  pure { A with val := val }

end Programs

/-- Along a list of distinct positions, the inner loop of the exact sparse gaxpy adds $c$ times each
stored value that it visits to the entry of $y$ at the row index of that value. -/
private theorem sparseGaxpy_inner {mm nnz : ℕ} (row : Fin nnz → Fin mm) (val : Fin nnz → ℝ)
    (c : ℝ) (l : List (Fin nnz)) (hl : l.Nodup) (y : Fin mm → ℝ) :
    l.foldl (fun y k => Function.update y (row k) (y (row k) + val k * c)) y =
      y + fun i => ∑ k, if k ∈ l ∧ row k = i then val k * c else 0 := by
  induction l generalizing y with
  | nil => ext i; simp
  | cons a l ih =>
    rw [List.foldl_cons, ih (List.nodup_cons.1 hl).2]
    have ha := (List.nodup_cons.1 hl).1
    ext i
    have hsplit : ∀ k, (if k ∈ a :: l ∧ row k = i then val k * c else 0) =
        (if k = a then (if row a = i then val a * c else 0) else 0) +
          (if k ∈ l ∧ row k = i then val k * c else 0) := by
      intro k
      by_cases hk : k = a
      · subst hk; simp [ha]
      · simp [hk]
    simp only [Pi.add_apply, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    by_cases h : row a = i
    · subst h; simp; ring
    · simp [h, Ne.symm h]

/-- **Equation (11.1.1)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ be in
compressed-column format, and let $x \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$. In exact
arithmetic the sparse gaxpy overwrites $y$ with $y + Ax$, where $A$ is the matrix that the
structure represents. -/
theorem equation_11_1_1 {mm n nnz : ℕ} (A : CompressedColumn mm n nnz) (x : Fin n → ℝ)
    (y : Fin mm → ℝ) : Id.run (sparseGaxpy pure A x y) = y + A.toMatrix *ᵥ x := by
  simp only [sparseGaxpy, List.idRun_foldlM, Id.run_pure, pure_bind]
  simp only [fun y j => sparseGaxpy_inner A.row A.val (x j) (A.positions j)
    (A.nodup_positions j) y]
  suffices h : ∀ (l : List (Fin n)) (y : Fin mm → ℝ),
      l.foldl (fun y j => y + fun i => ∑ k, if k ∈ A.positions j ∧ A.row k = i then
        A.val k * x j else 0) y = y + fun i => (l.map fun j => A.toMatrix i j * x j).sum by
    rw [h]
    ext i
    simp [mulVec, dotProduct, Fin.sum_univ_def]
  intro l
  induction l with
  | nil => intro y; ext; simp
  | cons a l ih =>
    intro y
    rw [List.foldl_cons, ih]
    ext i
    simp only [Pi.add_apply, List.map_cons, List.sum_cons, CompressedColumn.toMatrix_apply,
      Finset.sum_mul, ite_mul, zero_mul]
    ring

/-- The step of the exact inner loop of (11.1.2) at the stored position $\ell$; the second component
of the state is the merge pointer into the stored entries of $u$. -/
private def outerUpdateStep {mm nnz nu : ℕ} (row : Fin nnz → Fin mm)
    (u : CompressedColumn mm 1 nu) (c : ℝ) (st : (Fin nnz → ℝ) × ℕ) (ℓ : Fin nnz) :
    (Fin nnz → ℝ) × ℕ :=
  if h : st.2 < nu then
    if row ℓ = u.row ⟨st.2, h⟩ then
      (Function.update st.1 ℓ (st.1 ℓ + u.val ⟨st.2, h⟩ * c), st.2 + 1)
    else st
  else st

/-- The merge invariant of (11.1.2): along a list of positions with strictly increasing row indices
that contains the row $u.r(a)$ of every $a \ge \alpha_0$, the merge from the pointer $\alpha_0$
adds $u.\mathrm{val}(a) \cdot c$ at the position of row $u.r(a)$ for each $a \ge \alpha_0$, and
changes nothing else. -/
private theorem outerUpdate_inner {mm nnz nu : ℕ} (row : Fin nnz → Fin mm)
    (u : CompressedColumn mm 1 nu) (c : ℝ) (L : List (Fin nnz))
    (hL : L.Pairwise fun k l => row k < row l) (α₀ : ℕ) (val : Fin nnz → ℝ)
    (H : ∀ a : Fin nu, α₀ ≤ (a : ℕ) → ∃ k ∈ L, row k = u.row a) :
    (L.foldl (outerUpdateStep row u c) (val, α₀)).1 = val + fun k =>
      if k ∈ L then ∑ a : Fin nu, if α₀ ≤ (a : ℕ) ∧ u.row a = row k then u.val a * c else 0
      else 0 := by
  have hu := u.row_strictMono_zero
  induction L generalizing α₀ val with
  | nil => ext k; simp
  | cons ℓ L ih =>
    rw [List.pairwise_cons] at hL
    have hℓL : ℓ ∉ L := fun h => lt_irrefl _ (hL.1 ℓ h)
    rw [List.foldl_cons]
    by_cases hm : ∃ h : α₀ < nu, row ℓ = u.row ⟨α₀, h⟩
    · obtain ⟨h1, h2⟩ := hm
      have hstep : outerUpdateStep row u c (val, α₀) ℓ =
          (Function.update val ℓ (val ℓ + u.val ⟨α₀, h1⟩ * c), α₀ + 1) := by
        simp [outerUpdateStep, h1, h2]
      rw [hstep, ih hL.2]
      · ext k
        by_cases hk : k = ℓ
        · subst hk
          simp only [Pi.add_apply, Function.update_self, hℓL, ite_false, add_zero,
            List.mem_cons, true_or, ite_true]
          rw [Finset.sum_eq_single ⟨α₀, h1⟩]
          · simp [h2]
          · intro a _ ha
            rw [ite_eq_right]
            rintro ⟨-, hr⟩
            exact ha (hu.injective (hr.trans h2))
          · simp
        · simp only [Pi.add_apply, Function.update_of_ne hk, List.mem_cons, hk, false_or]
          split_ifs with hkL
          · congr 1
            refine Finset.sum_congr rfl fun a _ => ?_
            by_cases ha : (a : ℕ) = α₀
            · have hne : u.row a ≠ row k := by
                rw [show a = ⟨α₀, h1⟩ from Fin.ext ha, ← h2]
                exact (hL.1 k hkL).ne
              simp [hne]
            · have hiff : α₀ + 1 ≤ (a : ℕ) ↔ α₀ ≤ (a : ℕ) := by omega
              simp only [hiff]
          · rfl
      · intro a ha
        obtain ⟨k, hk, hr⟩ := H a (by omega)
        rcases List.mem_cons.1 hk with rfl | hk
        · have e : (a : ℕ) = α₀ := congrArg Fin.val (hu.injective (hr.symm.trans h2))
          omega
        · exact ⟨k, hk, hr⟩
    · have hnot : ∀ a : Fin nu, α₀ ≤ (a : ℕ) → u.row a ≠ row ℓ := by
        intro a ha hr
        have h1 : α₀ < nu := lt_of_le_of_lt ha a.2
        have h2 : row ℓ ≠ u.row ⟨α₀, h1⟩ := fun e => hm ⟨h1, e⟩
        obtain ⟨k, hk, hk'⟩ := H ⟨α₀, h1⟩ le_rfl
        rcases List.mem_cons.1 hk with rfl | hk
        · exact h2 hk'
        · have h3 := hL.1 k hk
          have h4 : u.row ⟨α₀, h1⟩ ≤ u.row a := hu.monotone (Fin.le_def.2 ha)
          rw [hk'] at h3
          exact (h3.trans_le h4).ne hr.symm
      have hstep : outerUpdateStep row u c (val, α₀) ℓ = (val, α₀) := by
        unfold outerUpdateStep
        split_ifs with h1 h2
        · exact absurd ⟨h1, h2⟩ hm
        · rfl
        · rfl
      rw [hstep, ih hL.2]
      · ext k
        by_cases hk : k = ℓ
        · subst hk
          simp only [Pi.add_apply, hℓL, ite_false, List.mem_cons, true_or, ite_true]
          rw [Finset.sum_eq_zero fun a _ => ite_eq_right fun h => hnot a h.1 h.2]
        · simp [hk]
      · intro a ha
        obtain ⟨k, hk, hr⟩ := H a ha
        rcases List.mem_cons.1 hk with rfl | hk
        · exact absurd hr.symm (hnot a ha)
        · exact ⟨k, hk, hr⟩

/-- A loop that adds one increment in each step adds the sum of the increments. -/
private theorem foldl_add_eq {nnz nv : ℕ} (D : Fin nv → Fin nnz → ℝ)
    (F : Fin nv → (Fin nnz → ℝ) → (Fin nnz → ℝ)) (hF : ∀ β val, F β val = val + D β)
    (l : List (Fin nv)) (val : Fin nnz → ℝ) :
    l.foldl (fun val β => F β val) val = val + fun k => (l.map fun β => D β k).sum := by
  induction l generalizing val with
  | nil => ext; simp
  | cons β l ih =>
    rw [List.foldl_cons, ih, hF]
    ext k
    simp only [Pi.add_apply, List.map_cons, List.sum_cons]
    ring

/-- **Equation (11.1.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$u \in \mathbb{R}^m$ and $v \in \mathbb{R}^n$ be in compressed-column format. Assume that the
pattern of $A$ has room for the update: for every stored entry $v_j$ of $v$, the stored rows of
column $j$ of $A$ include every stored row of $u$. Then in exact arithmetic the algorithm
overwrites $A$ with $A + uv^T$.

The hypothesis is the source's "storing zeros in locations that are destined to become nonzero".
The merge pointer $\alpha$ works because the row indices of $u$ and of each column of $A$ are
strictly increasing. -/
theorem equation_11_1_2 {mm n nnz nu nv : ℕ} (A : CompressedColumn mm n nnz)
    (u : CompressedColumn mm 1 nu) (v : CompressedColumn n 1 nv)
    (hA : ∀ (β : Fin nv) (a : Fin nu), ∃ k ∈ A.positions (v.row β), A.row k = u.row a) :
    (Id.run (sparseOuterProductUpdate pure A u v)).toMatrix =
      A.toMatrix + vecMulVec (fun i => u.toMatrix i 0) (fun j => v.toMatrix j 0) := by
  set D : Fin nv → Fin nnz → ℝ := fun β k => if k ∈ A.positions (v.row β) then
    ∑ a : Fin nu, if u.row a = A.row k then u.val a * v.val β else 0 else 0 with hD
  have hrun : (Id.run (sparseOuterProductUpdate pure A u v)).val =
      (List.finRange nv).foldl (fun val β =>
        ((A.positions (v.row β)).foldl (outerUpdateStep A.row u (v.val β)) (val, 0)).1)
        A.val := by
    simp only [sparseOuterProductUpdate, List.idRun_foldlM, Id.run_bind, Id.run_pure]
    rfl
  have hval : (Id.run (sparseOuterProductUpdate pure A u v)).val =
      A.val + fun k => ∑ β, D β k := by
    rw [hrun, foldl_add_eq D _ (fun β val => by
      rw [outerUpdate_inner _ _ _ _ (A.pairwise_row_lt _) 0 val (fun a _ => hA β a)]
      ext k
      simp [hD])]
    ext k
    simp [Fin.sum_univ_def]
  have hpos : ∀ j, (Id.run (sparseOuterProductUpdate pure A u v)).positions j =
      A.positions j := fun _ => rfl
  have hrow : (Id.run (sparseOuterProductUpdate pure A u v)).row = A.row := rfl
  ext i j
  set ui := ∑ a : Fin nu, if u.row a = i then u.val a else 0 with hui
  set vj := ∑ β : Fin nv, if v.row β = j then v.val β else 0 with hvj
  have hDk : ∀ k, k ∈ A.positions j → A.row k = i → ∑ β, D β k = ui * vj := by
    intro k hk hki
    rw [hvj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [hD]
    by_cases hβ : v.row β = j
    · rw [ite_eq_left (by rwa [hβ]), ite_eq_left hβ, hui, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hki]
      split_ifs <;> simp
    · rw [ite_eq_right (fun h => hβ (A.eq_of_mem_positions h hk)), ite_eq_right hβ, mul_zero]
  rw [CompressedColumn.toMatrix_apply, hpos, hrow, hval, Matrix.add_apply, vecMulVec_apply,
    CompressedColumn.toMatrix_apply_zero, CompressedColumn.toMatrix_apply_zero, ← hui, ← hvj]
  simp only [Pi.add_apply, ite_add_zero, Finset.sum_add_distrib]
  rw [← CompressedColumn.toMatrix_apply]
  congr 1
  by_cases h0 : ui * vj = 0
  · rw [h0]
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h
    · exact (hDk k h.1 h.2).trans h0
    · rfl
  · obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul h0)
    obtain ⟨β, -, hβ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h0)
    have ha' : u.row a = i := by
      by_contra h
      exact ha (ite_eq_right h)
    have hβ' : v.row β = j := by
      by_contra h
      exact hβ (ite_eq_right h)
    obtain ⟨k₀, hk₀, hrk₀⟩ := hA β a
    rw [hβ'] at hk₀
    rw [Finset.sum_eq_single k₀]
    · rw [ite_eq_left ⟨hk₀, hrk₀.trans ha'⟩, hDk k₀ hk₀ (hrk₀.trans ha')]
    · intro k _ hk
      rw [ite_eq_right]
      rintro ⟨hk1, hk2⟩
      exact hk (A.eq_of_row_eq hk1 hk₀ (hk2.trans (hrk₀.trans ha').symm))
    · simp

/-! ### §11.1.3: the first step of the outer-product Cholesky factorization -/

/-- **Equations (11.1.3)–(11.1.4)** of [golub2013matrix]. Let $\alpha > 0$, $v \in \mathbb{R}^n$ and
$B \in \mathbb{R}^{n \times n}$. Then
$$\begin{bmatrix} \alpha & v^T \\ v & B \end{bmatrix}
  = \begin{bmatrix} \sqrt{\alpha} & 0 \\ v / \sqrt{\alpha} & I \end{bmatrix}
    \begin{bmatrix} 1 & 0 \\ 0 & A^{(1)} \end{bmatrix}
    \begin{bmatrix} \sqrt{\alpha} & v^T / \sqrt{\alpha} \\ 0 & I \end{bmatrix},
  \qquad A^{(1)} = B - \frac{v v^T}{\alpha},$$
and $A^{(1)}$ is the Schur complement of the pivot $\alpha$: its entry $(i, j)$ is
$b_{ij} - v_i \alpha^{-1} v_j$.

The block matrices are indexed by `Fin 1 ⊕ Fin n` (`Matrix.fromBlocks`). The Schur complement is
`Matrix.schurComplementSingle` at the index `Sum.inl 0`. -/
theorem equation_11_1_3 {n : ℕ} {α : ℝ} (hα : 0 < α) (v : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    fromBlocks (of fun _ _ => α) (of fun (_ : Fin 1) j => v j) (of fun i (_ : Fin 1) => v i) B =
        fromBlocks (of fun _ _ => √α) 0 (of fun i (_ : Fin 1) => v i / √α) 1 *
          fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (B - α⁻¹ • vecMulVec v v) *
          fromBlocks (of fun _ _ => √α) (of fun (_ : Fin 1) j => v j / √α) 0 1 ∧
      ∀ i j, (B - α⁻¹ • vecMulVec v v) i j =
        (fromBlocks (of fun _ _ => α) (of fun (_ : Fin 1) j => v j)
          (of fun i (_ : Fin 1) => v i) B).schurComplementSingle (Sum.inl 0)
            ⟨Sum.inr i, Sum.inr_ne_inl⟩ ⟨Sum.inr j, Sum.inr_ne_inl⟩ := by
  have hs : √α * √α = α := Real.mul_self_sqrt hα.le
  have hs0 : √α ≠ 0 := (Real.sqrt_pos.2 hα).ne'
  refine ⟨?_, fun i j => ?_⟩
  · rw [fromBlocks_multiply, fromBlocks_multiply]
    ext (i | i) (j | j)
    · simp [Matrix.mul_apply, hs]
    · simp [Matrix.mul_apply]; field_simp
    · simp [Matrix.mul_apply]; field_simp
    · simp [Matrix.mul_apply, vecMulVec_apply, div_mul_div_comm, Real.mul_self_sqrt hα.le]
      ring
  · simp [vecMulVec_apply]; ring

/-! ### §11.1.4–11.1.5: graphs, profiles and the Cuthill–McKee ordering -/

/-- **Section 11.1.4** of [golub2013matrix], symmetric permutations relabel the adjacency graph. Let
$A \in \mathbb{R}^{n \times n}$ and let $\sigma$ be a permutation of the indices. Then the
relabelling $i \mapsto \sigma(i)$ is a graph isomorphism from the pattern graph of
$A(\sigma, \sigma)$ to the pattern graph of $A$. Moreover, if $A$ is symmetric, then $i$ and $j$
are adjacent in the pattern graph of $A$ if and only if $i \neq j$ and $a_{ij} \neq 0$.

The source says that "if $P$ is a permutation, then, except for vertex labeling, the adjacency
graphs for $A$ and $PAP^T$ look the same". The pattern graph is `Matrix.adjGraph`, in which $i$
and $j$ are adjacent when $i \neq j$ and $a_{ij} \neq 0$ or $a_{ji} \neq 0$. By the second part,
for a symmetric matrix it is the adjacency graph $\mathcal{G}_A$ of the source, with a node for
each row and an edge $(i, j)$ for each nonzero off-diagonal entry $a_{ij}$. -/
theorem adjGraph_submatrix_iso {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) :
    (∃ e : (A.submatrix σ σ).adjGraph ≃g A.adjGraph, ∀ i, e i = σ i) ∧
      (A.IsSymm → ∀ i j, A.adjGraph.Adj i j ↔ i ≠ j ∧ A i j ≠ 0) :=
  ⟨⟨A.adjGraphIso σ, fun _ => rfl⟩, fun hA _ _ => by
    rw [adjGraph_adj_iff_of_isSymm hA, adjDigraph_adj]⟩

open Classical in
/-- **Equation (11.1.6)** of [golub2013matrix], the profile index. For
$A \in \mathbb{R}^{n \times n}$ and a row $i$,
$$f_i(A) = \min\{j : 1 \le j \le i,\ a_{ij} \neq 0\}.$$
If row $i$ has no nonzero entry at or left of the diagonal, the minimum of the source is
undefined; the definition then gives $f_i(A) = i$, so that the row contributes $0$ to the
profile.

The indices are 0-based. -/
noncomputable def profileIndex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Fin n :=
  if h : (univ.filter fun j => j ≤ i ∧ A i j ≠ 0).Nonempty then
    (univ.filter fun j => j ≤ i ∧ A i j ≠ 0).min' h
  else i

/-- The profile index of row $i$ satisfies $f_i(A) \le i$. -/
theorem profileIndex_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    profileIndex A i ≤ i := by
  classical
  unfold profileIndex
  split_ifs with h
  · exact (Finset.mem_filter.1 (Finset.min'_mem _ h)).2.1
  · exact le_rfl

/-- **Section 11.1.5** of [golub2013matrix], the profile. For $A \in \mathbb{R}^{n \times n}$,
$$\operatorname{profile}(A) = n + \sum_{i=1}^n (i - f_i(A)),$$
where $f_i(A)$ is the profile index (11.1.6). The source uses the profile only in Problem
P11.1.6. -/
noncomputable def profile {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  n + ∑ i : Fin n, ((i : ℕ) - (profileIndex A i : ℕ))

/-- **Section 11.1.5** of [golub2013matrix], the level structure behind the Cuthill–McKee ordering.
Let $A \in \mathbb{R}^{n \times n}$, let $v$ be a node and let $\sigma$ be a permutation of the
indices. The level of a node is its distance to $v$ in the adjacency graph $\mathcal{G}_A$. If
the levels of $\sigma(k)$ and $\sigma(l)$ differ by $2$ or more, then entry $(k, l)$ of
$A(\sigma, \sigma)$ is $0$.

Take an ordering that lists the level sets $S_0, S_1, \dots$ one after another, such as the
Cuthill–McKee ordering with any tie-breaking. For it, the theorem says that $A(\sigma, \sigma)$
is block tridiagonal with the level sets as diagonal blocks. The theorem itself is a fact about
$A$ and the levels, and the ordering is not constructed.

The graph is the pattern graph `Matrix.adjGraph A`, and the distance is `SimpleGraph.dist`,
which is $0$ for a node that is not connected to $v$. -/
theorem submatrix_apply_eq_zero_of_levels_far {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n)
    (σ : Equiv.Perm (Fin n)) {k l : Fin n}
    (h : A.adjGraph.dist v (σ k) + 2 ≤ A.adjGraph.dist v (σ l) ∨
      A.adjGraph.dist v (σ l) + 2 ≤ A.adjGraph.dist v (σ k)) :
    A.submatrix σ σ k l = 0 := by
  rw [submatrix_apply]
  rcases h with h | h
  · exact apply_eq_zero_of_dist_lt v h
  · exact apply_eq_zero_of_dist_lt' v h

/-! ### §11.1.6: minimum degree, Cholesky with pivoting, and the symbolic fill -/

/-- **Section 11.1.6** of [golub2013matrix], the minimum-degree pivot rule. At step $k$, the pivot
is the index $p \ge k$ whose node has minimal degree in the graph of the trailing block
$A(k{:}n, k{:}n)$, that is, the index that minimizes the number of indices $i \ge k$ with
$i \neq p$ and $a_{ip} \neq 0$. Ties are broken by the least index.

The indices are 0-based. The minimum is `List.argmin` over the indices $p \ge k$ in increasing
order. -/
noncomputable def minDegreePivot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Fin n :=
  (((List.finRange n).filter fun p => k ≤ p).argmin fun p =>
    (univ.filter fun i => k ≤ i ∧ i ≠ p ∧ A i p ≠ 0).card).getD k

/-- The minimum-degree pivot at step $k$ is an index $p \ge k$ of the trailing block. -/
theorem le_minDegreePivot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    k ≤ minDegreePivot A k := by
  unfold minDegreePivot
  cases h : ((List.finRange n).filter fun p => k ≤ p).argmin fun p =>
      (univ.filter fun i => k ≤ i ∧ i ≠ p ∧ A i p ≠ 0).card with
  | none => exact le_rfl
  | some p =>
    have := List.argmin_mem (Option.mem_def.2 h)
    simpa using this

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Equation (11.1.8)** of [golub2013matrix], Cholesky with symmetric pivoting, for a pivot rule
`pivot`; the minimum-degree ordering is `pivot := GolubVanLoan.Chapter11.minDegreePivot`. The
state is the pair $(P, A)$ of the accumulated permutation and the working array. For
$k = 1, \dots, n$:

* Steps 1–3: $q = \mathrm{pivot}(A, k)$, and $P_k$ is the transposition of $k$ and $q$. Then
  $P = \operatorname{diag}(I_{k-1}, P_k) P$, $A(k{:}n, k{:}n) = P_k A(k{:}n, k{:}n) P_k^T$ and
  $A(k{:}n, 1{:}k-1) = P_k A(k{:}n, 1{:}k-1)$.
* Step 4: $A(k{:}n, k) = A(k{:}n, k) / \sqrt{A(k, k)}$.
* Step 5: $A(k+1{:}n, k+1{:}n) = A(k+1{:}n, k+1{:}n) - A(k+1{:}n, k)\, A(k+1{:}n, k)^T$.

On exit the lower triangle of $A$ holds the Cholesky factor $G$ of $PAP^T$.

**Correction.** The source runs the loop for $k = 1{:}n-2$, which leaves the last two columns
unfactored. The program runs it for $k = 1{:}n$.

In Step 4 the square root is followed by one rounding, and each quotient is rounded. In Step 5
each product and each difference is rounded. The permutation $P$ acts as `A₀.submatrix p p` on
the input `A₀`. Indices are 0-based. -/
noncomputable def choleskyWithPivoting {n : ℕ}
    (pivot : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Equiv.Perm (Fin n) × Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (st : Equiv.Perm (Fin n) × Matrix (Fin n) (Fin n) ℝ) k => do
    let s := Equiv.swap k (pivot st.2 k)
    let A₁ : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => st.2 (s i) (if k ≤ i then s j else j)
    let d ← rnd (Real.sqrt (A₁ k k))
    let A₂ ← ((List.finRange n).filter fun i => k ≤ i).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) i => do
        let g ← rnd (A i k / d)
        pure (A.updateRow i (Function.update (A i) k g))) A₁
    let A₃ ← ((List.finRange n).filter fun i => k < i).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) i =>
        ((List.finRange n).filter fun j => k < j).foldlM
          (fun (A : Matrix (Fin n) (Fin n) ℝ) j => do
            let p ← rnd (A i k * A j k)
            let t ← rnd (A i j - p)
            pure (A.updateRow i (Function.update (A i) j t))) A) A₂
    pure (s.trans st.1, A₃)) (1, A)

end Programs

/-! ### The exact semantics of (11.1.8) -/

/-- The exact step of (11.1.8) at column $k$, with the loops of Steps 4 and 5 in closed form. -/
private noncomputable def cholPivStep {n : ℕ}
    (pivot : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n)
    (st : Equiv.Perm (Fin n) × Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Equiv.Perm (Fin n) × Matrix (Fin n) (Fin n) ℝ :=
  let s := Equiv.swap k (pivot st.2 k)
  let A₁ : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => st.2 (s i) (if k ≤ i then s j else j)
  let A₂ : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => if k ≤ i ∧ j = k then A₁ i k / √(A₁ k k) else A₁ i j
  (s.trans st.1,
    Matrix.of fun i j => if k < i ∧ k < j then A₂ i j - A₂ i k * A₂ j k else A₂ i j)

/-- Step 4 of (11.1.8) in closed form: the entries of column $k$ in the listed rows are divided by
$d$. -/
private theorem foldl_divCol {n : ℕ} (k : Fin n) (d : ℝ) (L : List (Fin n)) (hL : L.Nodup)
    (A₀ : Matrix (Fin n) (Fin n) ℝ) :
    L.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) i =>
      A.updateRow i (Function.update (A i) k (A i k / d))) A₀ =
      Matrix.of fun i j => if i ∈ L ∧ j = k then A₀ i k / d else A₀ i j := by
  induction L generalizing A₀ with
  | nil => ext i j; simp
  | cons a L ih =>
    rw [List.foldl_cons, ih (List.nodup_cons.1 hL).2]
    have ha := (List.nodup_cons.1 hL).1
    ext i j
    by_cases hi : i = a
    · subst hi
      by_cases hj : j = k <;> simp [updateRow_apply, Function.update_apply, ha, hj]
    · by_cases hj : j = k <;> simp [updateRow_apply, hi, hj]

/-- One row of Step 5 of (11.1.8) in closed form: for each listed column $j$, entry $(i, j)$ loses
$a_{ik} a_{jk}$. -/
private theorem foldl_schurRow {n : ℕ} (i k : Fin n) (J : List (Fin n)) (hJ : J.Nodup)
    (hk : k ∉ J) (A₀ : Matrix (Fin n) (Fin n) ℝ) :
    J.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) j =>
      A.updateRow i (Function.update (A i) j (A i j - A i k * A j k))) A₀ =
      Matrix.of fun i' j => if i' = i ∧ j ∈ J then A₀ i j - A₀ i k * A₀ j k else A₀ i' j := by
  induction J generalizing A₀ with
  | nil => ext i j; simp
  | cons a J ih =>
    rw [List.foldl_cons, ih (List.nodup_cons.1 hJ).2 (fun h => hk (List.mem_cons_of_mem a h))]
    have ha := (List.nodup_cons.1 hJ).1
    have hka : k ≠ a := fun h => hk (h ▸ List.mem_cons_self)
    have hcol : ∀ j, (A₀.updateRow i (Function.update (A₀ i) a (A₀ i a - A₀ i k * A₀ a k))) j k
        = A₀ j k := fun j => by
      by_cases hj : j = i
      · subst hj; simp [updateRow_apply, hka]
      · simp [updateRow_apply, hj]
    ext i' j
    simp only [of_apply, hcol]
    by_cases hi : i' = i
    · subst hi
      by_cases hj : j = a
      · subst hj; simp [updateRow_apply, ha]
      · by_cases hjJ : j ∈ J <;> simp [updateRow_apply, hj, hjJ]
    · simp [updateRow_apply, hi]

/-- Step 5 of (11.1.8) in closed form: each listed trailing entry $(i, j)$ loses $a_{ik} a_{jk}$. -/
private theorem foldl_schur {n : ℕ} (k : Fin n) (I J : List (Fin n)) (hI : I.Nodup)
    (hJ : J.Nodup) (hk : k ∉ J) (A₀ : Matrix (Fin n) (Fin n) ℝ) :
    I.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) i =>
      J.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) j =>
        A.updateRow i (Function.update (A i) j (A i j - A i k * A j k))) A) A₀ =
      Matrix.of fun i j => if i ∈ I ∧ j ∈ J then A₀ i j - A₀ i k * A₀ j k else A₀ i j := by
  induction I generalizing A₀ with
  | nil => ext i j; simp
  | cons a I ih =>
    rw [List.foldl_cons, foldl_schurRow a k J hJ hk, ih (List.nodup_cons.1 hI).2]
    have ha := (List.nodup_cons.1 hI).1
    ext i j
    by_cases hi : i = a
    · subst hi; simp [ha]
    · by_cases hiI : i ∈ I
      · by_cases hjJ : j ∈ J
        · simp [hi, hiI, hjJ, hk]
        · simp [hi, hjJ]
      · simp [hi, hiI]

/-- The exact run of (11.1.8) is the loop of the exact steps. -/
private theorem choleskyWithPivoting_run {n : ℕ}
    (pivot : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (choleskyWithPivoting pure pivot A) =
      (List.finRange n).foldl (cholPivStep pivot) (1, A) := by
  unfold choleskyWithPivoting
  rw [List.idRun_foldlM]
  congr 1
  funext st k
  simp only [Id.run_bind, Id.run_pure, List.idRun_foldlM, pure_bind]
  rw [foldl_divCol _ _ _ ((List.nodup_finRange n).filter _),
    foldl_schur _ _ _ ((List.nodup_finRange n).filter _) ((List.nodup_finRange n).filter _)
      (by simp)]
  simp [cholPivStep, List.mem_filter]

/-- The invariant of (11.1.8) after $c$ columns: $PAP^T = G_c G_c^T + \operatorname{diag}(0, S)$,
where $G_c$ is the lower triangle of the first $c$ columns of the array, the trailing block $S$
is positive definite, and the computed diagonal entries are positive. -/
private structure CholPivInv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℕ)
    (st : Equiv.Perm (Fin n) × Matrix (Fin n) (Fin n) ℝ) : Prop where
  eq : ∀ i j, A (st.1 i) (st.1 j) =
    ∑ l : Fin n, (if (l : ℕ) < c ∧ l ≤ i ∧ l ≤ j then st.2 i l * st.2 j l else 0) +
      (if c ≤ (i : ℕ) ∧ c ≤ (j : ℕ) then st.2 i j else 0)
  posDef : (Matrix.of fun (i j : {i : Fin n // c ≤ (i : ℕ)}) => st.2 i j).PosDef
  diag_pos : ∀ l : Fin n, (l : ℕ) < c → 0 < st.2 l l

/-- A sum over the first $c + 1$ indices is the sum over the first $c$ indices plus the term of
index $c$. -/
private theorem sum_ite_lt_succ {n c : ℕ} (k : Fin n) (hk : (k : ℕ) = c) (P : Fin n → Prop)
    [DecidablePred P] (f : Fin n → ℝ) :
    ∑ l : Fin n, (if (l : ℕ) < c + 1 ∧ P l then f l else 0) =
      ∑ l : Fin n, (if (l : ℕ) < c ∧ P l then f l else 0) + (if P k then f k else 0) := by
  have h : ∀ l : Fin n, (if (l : ℕ) < c + 1 ∧ P l then f l else 0) =
      (if (l : ℕ) < c ∧ P l then f l else 0) + (if l = k then (if P k then f k else 0) else 0) := by
    intro l
    by_cases hl : l = k
    · subst hl; simp [hk]
    · have : (l : ℕ) ≠ c := fun h => hl (Fin.ext (h.trans hk.symm))
      have hiff : (l : ℕ) < c + 1 ↔ (l : ℕ) < c := by omega
      simp [hl, hiff]
  rw [Finset.sum_congr rfl fun l _ => h l, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- One step of (11.1.8) keeps the invariant. -/
private theorem cholPivInv_step {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (pivot : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n) (hpivot : ∀ M k, k ≤ pivot M k)
    {c : ℕ} (hc : c < n) {st : Equiv.Perm (Fin n) × Matrix (Fin n) (Fin n) ℝ}
    (h : CholPivInv A c st) : CholPivInv A (c + 1) (cholPivStep pivot st ⟨c, hc⟩) := by
  obtain ⟨p, M⟩ := st
  set k : Fin n := ⟨c, hc⟩ with hkdef
  have hkc : (k : ℕ) = c := rfl
  set s := Equiv.swap k (pivot M k) with hsdef
  have hq : k ≤ pivot M k := hpivot M k
  -- the transposition fixes the computed columns and preserves the trailing block
  have hs_lt : ∀ i : Fin n, (i : ℕ) < c → s i = i := fun i hi =>
    Equiv.swap_apply_of_ne_of_ne (fun e => by rw [e] at hi; omega)
      (fun e => by rw [e] at hi; exact absurd (Fin.le_def.1 hq) (by omega))
  have hs_ge : ∀ i : Fin n, c ≤ (s i : ℕ) ↔ c ≤ (i : ℕ) := by
    intro i
    rw [hsdef, Equiv.swap_apply_def]
    have := Fin.le_def.1 hq
    split_ifs with h1 h2
    · subst h1; simp only [hkc]; omega
    · subst h2; simp only [hkc]; omega
    · rfl
  have hle : ∀ i : Fin n, k ≤ i ↔ c ≤ (i : ℕ) := fun i => Fin.le_def
  have hlt : ∀ i : Fin n, k < i ↔ c + 1 ≤ (i : ℕ) := fun i => by rw [Fin.lt_def]; omega
  set M₁ : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => M (s i) (if k ≤ i then s j else j)
    with hM₁
  -- the permuted trailing block is positive definite, hence symmetric
  have hP₁ : (Matrix.of fun (i j : {i : Fin n // c ≤ (i : ℕ)}) => M₁ i j).PosDef := by
    have := h.posDef.submatrix (e := fun i : {i : Fin n // c ≤ (i : ℕ)} =>
      (⟨s i, (hs_ge i).2 i.2⟩ : {i : Fin n // c ≤ (i : ℕ)}))
      (fun a b e => Subtype.ext (s.injective (congrArg Subtype.val e)))
    convert this using 1
    ext i j
    simp [hM₁, (hle (i : Fin n)).2 i.2]
  have hsym : ∀ i j : Fin n, c ≤ (i : ℕ) → c ≤ (j : ℕ) → M₁ i j = M₁ j i := fun i j hi hj => by
    have := hP₁.isHermitian.apply ⟨i, hi⟩ ⟨j, hj⟩
    simpa using this.symm
  have hαpos : 0 < M₁ k k := by
    have := hP₁.diag_pos (i := ⟨k, le_rfl⟩)
    simpa using this
  have hα0 : M₁ k k ≠ 0 := hαpos.ne'
  have hdpos : 0 < √(M₁ k k) := Real.sqrt_pos.2 hαpos
  have hdd : √(M₁ k k) * √(M₁ k k) = M₁ k k := Real.mul_self_sqrt hαpos.le
  have hM₃_apply : ∀ i j : Fin n, (cholPivStep pivot (p, M) k).2 i j = if k < i ∧ k < j then
      M₁ i j - M₁ i k / √(M₁ k k) * (M₁ j k / √(M₁ k k)) else
        if k ≤ i ∧ j = k then M₁ i k / √(M₁ k k) else M₁ i j := by
    intro i j
    by_cases hij : k < i ∧ k < j
    · simp [cholPivStep, hM₁, hij, hij.1.le, hij.2.le, hij.2.ne', ← hsdef]
    · simp [cholPivStep, hM₁, hij, ← hsdef]
  rw [show cholPivStep pivot (p, M) k = (s.trans p, (cholPivStep pivot (p, M) k).2) from rfl]
  generalize (cholPivStep pivot (p, M) k).2 = M₃ at hM₃_apply ⊢
  -- the computed columns are unchanged
  have hM₃_old : ∀ i l : Fin n, (l : ℕ) < c → M₃ i l = M (s i) l := by
    intro i l hl
    have h1 : ¬ (k < i ∧ k < l) := fun h' => by have := (hlt l).1 h'.2; omega
    have h2 : l ≠ k := fun e => by rw [e] at hl; simp [hkc] at hl
    rw [hM₃_apply, ite_eq_right h1, ite_eq_right (fun h' => h2 h'.2), hM₁, of_apply]
    split_ifs <;> simp only [hs_lt l hl]
  have hM₃_col : ∀ i : Fin n, k ≤ i → M₃ i k = M₁ i k / √(M₁ k k) := by
    intro i hi
    rw [hM₃_apply, ite_eq_right (fun h' => lt_irrefl _ h'.2), ite_eq_left ⟨hi, rfl⟩]
  refine ⟨fun i j => ?_, ?_, fun l hl => ?_⟩
  · -- the factorization identity
    dsimp only
    have hold := h.eq (s i) (s j)
    dsimp only at hold
    rw [Equiv.trans_apply, Equiv.trans_apply, hold,
      sum_ite_lt_succ k hkc (fun l => l ≤ i ∧ l ≤ j)]
    have hsum : ∑ l : Fin n, (if (l : ℕ) < c ∧ l ≤ s i ∧ l ≤ s j then M (s i) l * M (s j) l
        else 0) = ∑ l : Fin n, (if (l : ℕ) < c ∧ l ≤ i ∧ l ≤ j then M₃ i l * M₃ j l else 0) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : (l : ℕ) < c
      · have hli : l ≤ s i ↔ l ≤ i := by
          by_cases hi : c ≤ (i : ℕ)
          · have := (hs_ge i).2 hi
            simp only [Fin.le_def]; omega
          · rw [hs_lt i (by omega)]
        have hlj : l ≤ s j ↔ l ≤ j := by
          by_cases hj : c ≤ (j : ℕ)
          · have := (hs_ge j).2 hj
            simp only [Fin.le_def]; omega
          · rw [hs_lt j (by omega)]
        simp only [hl, hli, hlj, true_and, hM₃_old i l hl, hM₃_old j l hl]
      · simp [hl]
    rw [hsum, add_assoc]
    congr 1
    simp only [hs_ge, (hle i).symm, (hle j).symm]
    by_cases hi : k ≤ i
    · by_cases hj : k ≤ j
      · have hMij : M (s i) (s j) = M₁ i j := by simp [hM₁, hi]
        rw [ite_eq_left ⟨hi, hj⟩, ite_eq_left ⟨hi, hj⟩, hMij, hM₃_col i hi, hM₃_col j hj]
        rcases hi.lt_or_eq with hi' | hi'
        · rcases hj.lt_or_eq with hj' | hj'
          · rw [ite_eq_left ⟨(hlt i).1 hi', (hlt j).1 hj'⟩, hM₃_apply, ite_eq_left ⟨hi', hj'⟩]
            ring
          · subst hj'
            rw [ite_eq_right (fun h' => by have := h'.2; omega), add_zero, div_mul_div_comm,
              hdd, mul_div_cancel_right₀ _ hα0]
        · subst hi'
          rw [ite_eq_right (fun h' => by have := h'.1; omega), add_zero, div_mul_div_comm, hdd]
          rcases hj.lt_or_eq with hj' | hj'
          · rw [hsym k j le_rfl ((hle j).1 hj), mul_div_cancel_left₀ _ hα0]
          · subst hj'
            rw [mul_div_cancel_right₀ _ hα0]
      · rw [ite_eq_right (fun h' => hj h'.2), ite_eq_right (fun h' => hj h'.2),
          ite_eq_right (fun h' => hj ((hle j).2 (by omega)))]
        ring
    · rw [ite_eq_right (fun h' => hi h'.1), ite_eq_right (fun h' => hi h'.1),
        ite_eq_right (fun h' => hi ((hle i).2 (by omega)))]
      ring
  · -- the new trailing block is a Schur complement of the old one
    dsimp only
    have hH := posDef_hermitianPart_schurComplementSingle
      (by rwa [hP₁.isHermitian.hermitianPart_eq]) (⟨k, le_rfl⟩ : {i : Fin n // c ≤ (i : ℕ)})
    have := hH.submatrix (e := fun i : {i : Fin n // c + 1 ≤ (i : ℕ)} =>
      (⟨⟨i, by omega⟩, fun e => by
        have := congrArg (fun x : {i : Fin n // c ≤ (i : ℕ)} => ((x : Fin n) : ℕ)) e
        simp at this; omega⟩ : {x : {i : Fin n // c ≤ (i : ℕ)} // x ≠ ⟨k, le_rfl⟩}))
      (fun a b e => Subtype.ext (by
        have := congrArg (fun x : {x : {i : Fin n // c ≤ (i : ℕ)} // x ≠ ⟨k, le_rfl⟩} =>
          ((x : {i : Fin n // c ≤ (i : ℕ)}) : Fin n)) e
        simpa using this))
    convert this using 1
    ext i j
    have hi := (hlt i).2 i.2
    have hj := (hlt j).2 j.2
    simp only [submatrix_apply, hermitianPart_apply, schurComplementSingle_apply, of_apply,
      starRingEnd_apply, star_trivial, hM₃_apply, ite_eq_left (And.intro hi hj)]
    rw [hsym j i ((hle j).1 hj.le) ((hle i).1 hi.le), hsym k i le_rfl ((hle i).1 hi.le),
      hsym k j le_rfl ((hle j).1 hj.le), div_mul_div_comm, hdd]
    ring
  · -- the diagonal
    dsimp only
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | hl
    · rw [hM₃_old l l hl, hs_lt l hl]; exact h.diag_pos l hl
    · have hlk : l = k := Fin.ext hl
      subst hlk
      rw [hM₃_col _ le_rfl]
      exact div_pos hαpos hdpos

/-- The invariant of (11.1.8) holds after the whole loop. -/
private theorem cholPivInv_loop {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (pivot : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n) (hpivot : ∀ M k, k ≤ pivot M k) :
    ∀ m c, c + m = n → ∀ st, CholPivInv A c st →
      CholPivInv A n (((List.finRange n).drop c).foldl (cholPivStep pivot) st) := by
  intro m
  induction m with
  | zero =>
    intro c hc st h
    have hcn : c = n := by omega
    subst hcn
    rw [List.drop_eq_nil_of_le (by simp), List.foldl_nil]
    exact h
  | succ m ih =>
    intro c hc st h
    have hcn : c < n := by omega
    rw [List.drop_eq_getElem_cons (by simpa using hcn), List.foldl_cons, List.getElem_finRange]
    exact ih (c + 1) (by omega) _ (cholPivInv_step pivot hpivot hcn h)

/-- **Equation (11.1.8)** of [golub2013matrix], correctness in exact arithmetic. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, and let the pivot rule take its
pivot from the trailing block: $k \le \mathrm{pivot}(M, k)$ for every $M$ and $k$. Let $(P, M)$
be the exact output of Cholesky with symmetric pivoting, and let $G$ be the lower triangle of
$M$. Then $G$ is the Cholesky factor of $PAP^T$: $G$ is lower triangular with positive diagonal,
and $PAP^T = GG^T$.

Here $PAP^T$ is `A.submatrix p p`, and the conclusion is
`Matrix.IsCholesky (A.submatrix p p) Gᵀ`, whose factor $G^T$ is upper triangular. -/
theorem equation_11_1_8 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (pivot : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n) (hpivot : ∀ M k, k ≤ pivot M k) :
    let out := Id.run (choleskyWithPivoting pure pivot A)
    (A.submatrix out.1 out.1).IsCholesky
      (Matrix.of fun i j => if j ≤ i then out.2 i j else 0)ᵀ := by
  intro out
  have hinv : CholPivInv A n out := by
    have h0 : CholPivInv A 0 (1, A) :=
      ⟨fun i j => by simp, hA.submatrix Subtype.val_injective, fun l hl => absurd hl (by omega)⟩
    have := cholPivInv_loop pivot hpivot n 0 (zero_add n) (1, A) h0
    rw [List.drop_zero, ← choleskyWithPivoting_run] at this
    exact this
  obtain ⟨heq, -, hdiag⟩ := hinv
  refine ⟨fun i j hij => ?_, fun i => ?_, ?_⟩
  · have : ¬ i ≤ j := not_le.2 hij
    simp [this]
  · simpa using hdiag i i.2
  · ext i j
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose, Matrix.mul_apply,
      submatrix_apply, heq i j]
    have hlast : ¬ (n ≤ (i : ℕ) ∧ n ≤ (j : ℕ)) := fun h => by have := i.2; omega
    rw [ite_eq_right hlast, add_zero]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : l ≤ i <;> by_cases h2 : l ≤ j <;> simp [h1, h2, l.2]

/-- With the minimum-degree pivot rule of §11.1.6, the exact run of (11.1.8) on a symmetric positive
definite $A$ returns $(P, M)$ such that the lower triangle $G$ of $M$ is the Cholesky factor of
$PAP^T$. -/
theorem minDegree_cholesky {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    let out := Id.run (choleskyWithPivoting pure minDegreePivot A)
    (A.submatrix out.1 out.1).IsCholesky
      (Matrix.of fun i j => if j ≤ i then out.2 i j else 0)ᵀ :=
  equation_11_1_8 hA minDegreePivot le_minDegreePivot

/-- **Section 11.1.6** of [golub2013matrix], the formula after Fact 2. Let
$A, H \in \mathbb{R}^{n \times n}$ with `Matrix.IsCholesky A H`, and let $G = H^T$ be the lower
Cholesky factor, so that $A = GG^T$. Then for all $i$ and $j$,
$$g_{ij} = \frac{a_{ij} - \sum_{k < j} g_{ik} g_{jk}}{g_{jj}}.$$

**Generalization.** The source states the formula for $j < i$. It holds for all $i$ and $j$: for
$i < j$ both sides vanish, and for $i = j$ it is the formula for the diagonal entry.

The formula is entry $i$ of the column formula (4.2.9) of the gaxpy Cholesky factorization,
`GolubVanLoan.Chapter04.equation_4_2_9`. -/
theorem cholesky_apply_eq {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℝ} (h : A.IsCholesky H)
    (i j : Fin n) :
    Hᵀ i j = (A i j - ∑ k ∈ univ.filter (· < j), Hᵀ i k * Hᵀ j k) / Hᵀ j j := by
  have hA : A = Hᵀ * Hᵀᵀ := by
    rw [transpose_transpose, ← h.conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial]
  have h49 := congrFun (Chapter04.equation_4_2_9 h.isUpperTriangular.transpose hA j) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply] at h49
  rw [eq_div_iff (by simpa using h.diag_ne_zero j), mul_comm, h49]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => mul_comm _ _)

/-- **Section 11.1.6** of [golub2013matrix], Facts 1 and 2, the exact half. Let
$A, H \in \mathbb{R}^{n \times n}$ with `Matrix.IsCholesky A H`, and let $G = H^T$ be the lower
Cholesky factor. If $j < i$ and $(i, j)$ is not in the symbolic fill of $A$, then $g_{ij} = 0$.
The symbolic fill, `Matrix.IsCholeskyFill`, is the smallest set of positions that contains the
strictly lower nonzero entries of $A$ and is closed under Parter's rule: if $(i, k)$ and
$(j, k)$ are in it and $k < j < i$, then $(i, j)$ is in it.

**Reading.** The source says that $g_{ij}$ is nonzero at the positions that Facts 1 and 2
describe, "assuming no numerical cancellation". That statement has no exact reading. The theorem
states the converse direction, which is exact, and which the preallocation of Step 0′ needs. -/
theorem cholesky_eq_zero_of_not_isCholeskyFill {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℝ}
    (h : A.IsCholesky H) {i j : Fin n} (hji : j < i) (hfill : ¬ A.IsCholeskyFill i j) :
    Hᵀ i j = 0 :=
  h.apply_eq_zero_of_not_isCholeskyFill hji hfill

/-! ### §11.1.7: nested dissection -/

/-- **Section 11.1.7** of [golub2013matrix], the Cholesky factor inherits the zero block of a
dissection. Let $A, H \in \mathbb{R}^{n \times n}$ with `Matrix.IsCholesky A H`, and let
$G = H^T$. Split the indices as $I_1 = [0, n_1)$, $I_2 = [n_1, n_1 + n_2)$ and the separator
after them. If $a_{ij} = 0$ for all $i \in I_2$ and $j \in I_1$, then $g_{ij} = 0$ for all
$i \in I_2$ and $j \in I_1$: no fill enters the zero block.

This is the situation of the dissected form $P_0 A P_0^T = [A_1\ 0\ C_1^T; 0\ A_2\ C_2^T; C_1\
C_2\ S]$, with the permuted matrix written as $A$. Repeating the dissection on each diagonal
block gives the same statement one level down. -/
theorem nestedDissection_cholesky {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℝ} (h : A.IsCholesky H)
    (n₁ n₂ : ℕ) (hA : ∀ i j : Fin n, n₁ ≤ (i : ℕ) → (i : ℕ) < n₁ + n₂ → (j : ℕ) < n₁ → A i j = 0)
    {i j : Fin n} (hi₁ : n₁ ≤ (i : ℕ)) (hi₂ : (i : ℕ) < n₁ + n₂) (hj : (j : ℕ) < n₁) :
    Hᵀ i j = 0 := by
  rw [transpose_apply]
  refine h.apply_eq_zero_of_separated (S := {j : Fin n | (j : ℕ) < n₁})
    (T := {i : Fin n | n₁ ≤ (i : ℕ) ∧ (i : ℕ) < n₁ + n₂}) (fun a b hba hb => ?_)
    (fun i hi j hj => hA i j hi.1 hi.2 hj) ⟨hi₁, hi₂⟩ hj (Fin.lt_def.2 (by omega))
  exact lt_of_le_of_lt (Fin.le_def.1 hba) hb

/-! ### §11.1.8: sparse QR and the seminormal equations -/

/-- **Section 11.1.8** of [golub2013matrix], the Cholesky factor of the normal equations from a QR
factorization. Let $A, Q \in \mathbb{R}^{m \times n}$ and $R \in \mathbb{R}^{n \times n}$, and
let $P$ be a permutation. If $AP^T = QR$, $Q^T Q = I$, and $R$ is upper triangular with positive
diagonal, then $R$ is the Cholesky factor of $P(A^TA)P^T$: `Matrix.IsCholesky` holds for
$P(A^TA)P^T$ and $R$, so in particular $P(A^TA)P^T = R^TR$.

The source says that "if $AP^T = QR$ is the thin QR factorization of $AP^T$, then
$P(A^TA)P^T = R^TR$, i.e., $R^T$ is the Cholesky factor of $P(A^TA)P^T$". Here $AP^T = A(:, p)$
is `A.submatrix id σ`. The positive diagonal of $R$ makes $A$ of full column rank. -/
theorem seminormal_cholesky {m n : ℕ} {A Q : Matrix (Fin m) (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin n) ℝ} (σ : Equiv.Perm (Fin n)) (hQR : A.submatrix id σ = Q * R)
    (hQ : Qᵀ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) :
    ((Aᵀ * A).submatrix σ σ).IsCholesky R := by
  have h := isCholesky_conjTranspose_mul_self_of_qr hQR (by simpa using hQ) hR hd
  rwa [conjTranspose_eq_transpose_of_trivial, transpose_submatrix,
    ← submatrix_mul _ _ _ _ _ Function.bijective_id] at h

/-- **Section 11.1.8** of [golub2013matrix], the seminormal equations. Let $AP^T = QR$ be as in
`GolubVanLoan.Chapter11.seminormal_cholesky`, and let $x \in \mathbb{R}^n$ and
$b \in \mathbb{R}^m$. Then the normal equations $A^TAx = A^Tb$ hold if and only if
$$R^TR\,(Px) = P(A^Tb).$$
The factor $Q$ is not needed to form these equations. -/
theorem seminormal_normalEquations {m n : ℕ} {A Q : Matrix (Fin m) (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin n) ℝ} (σ : Equiv.Perm (Fin n)) (hQR : A.submatrix id σ = Q * R)
    (hQ : Qᵀ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) (x : Fin n → ℝ)
    (b : Fin m → ℝ) :
    (Aᵀ * A) *ᵥ x = Aᵀ *ᵥ b ↔ (Aᵀ *ᵥ b) ∘ σ = (Rᵀ * R) *ᵥ (x ∘ σ) := by
  have hRR : Rᵀ * R = (Aᵀ * A).submatrix σ σ := by
    rw [← (seminormal_cholesky σ hQR hQ hR hd).conjTranspose_mul_self,
      conjTranspose_eq_transpose_of_trivial]
  rw [hRR, submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
    Function.comp_id]
  exact ⟨fun h => by rw [h], fun h => (σ.surjective.injective_comp_right h).symm⟩

/-- **Section 11.1.8** of [golub2013matrix], Steps 3–4, one step of iterative improvement. Let
$AP^T = QR$ be as in `GolubVanLoan.Chapter11.seminormal_cholesky`, let $b \in \mathbb{R}^m$ and
$x_0, e \in \mathbb{R}^n$, and let $r = b - Ax_0$. If $e$ solves the seminormal equations
$R^TR\,(Pe) = P(A^Tr)$, then $x_0 + e$ solves the normal equations: $A^TA(x_0 + e) = A^Tb$.

This holds for every $x_0$, however inaccurate, because $A^TA(x_0 + e) = A^Tb - A^Tr + A^Tr$.
The accuracy of the computed result is the analysis of Björck, which is not formalized. -/
theorem seminormal_refinement {m n : ℕ} {A Q : Matrix (Fin m) (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin n) ℝ} (σ : Equiv.Perm (Fin n)) (hQR : A.submatrix id σ = Q * R)
    (hQ : Qᵀ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) (b : Fin m → ℝ)
    (x₀ e : Fin n → ℝ) (he : (Rᵀ * R) *ᵥ (e ∘ σ) = (Aᵀ *ᵥ (b - A *ᵥ x₀)) ∘ σ) :
    (Aᵀ * A) *ᵥ (x₀ + e) = Aᵀ *ᵥ b := by
  have h := (seminormal_normalEquations σ hQR hQ hR hd e (b - A *ᵥ x₀)).2 he.symm
  rw [mulVec_add, h, mulVec_sub, ← mulVec_mulVec]
  abel

/-- **Equation (11.1.9)** of [golub2013matrix], the row-by-row Givens QR factorization, which
introduces zeros into $A \in \mathbb{R}^{m \times n}$ one row at a time:
```
for i = 2:m
  for j = 1:min{i − 1, n}
    if a_ij ≠ 0
      compute a Givens rotation G with G [a_jj; a_ij] = [×; 0]
      update the rows j, i of A on the columns j:n by G
```
The program assumes $n \le m$, the least-squares setting of §11.1.8.

The rotation is `GolubVanLoan.Chapter05.algorithm_5_1_3` (Algorithm 5.1.3) of
$(a_{jj}, a_{ij})$, and the update is the row helper `GolubVanLoan.Chapter05.givensApplyLeft` on
the columns $j, \dots, n - 1$ (algorithm conventions 5, 10 and 13). The test $a_{ij} \neq 0$ is
an exact comparison on the computed entry (algorithm convention 1). -/
noncomputable def rowGivensQR {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m n : ℕ}
    (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange m).foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) =>
    ((List.finRange n).filter (fun j : Fin n => (j : ℕ) < i)).foldlM
      (fun (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
        if A i j ≠ 0 then do
          let jj : Fin m := Fin.castLE hnm j
          let cs ← GolubVanLoan.Chapter05.algorithm_5_1_3 rnd (A jj j) (A i j)
          GolubVanLoan.Chapter05.givensApplyLeft rnd jj i cs.1 cs.2
            (GolubVanLoan.Chapter05.indexFrom n j) A
        else pure A) A) A

/-- If $b_{ij} = 0$, the exact Givens step in the plane $(p, i)$ at column $j$ is the identity,
because Algorithm 5.1.3 returns $(c, s) = (1, 0)$ for $b = 0$. -/
private theorem givensStepExact_of_eq_zero {m n : ℕ} {p i : Fin m} (hpi : p ≠ i) (j : Fin n)
    {B : Matrix (Fin m) (Fin n) ℝ} (h : B i j = 0) :
    GolubVanLoan.Chapter05.givensStepExact p i j B = B := by
  have hcs : Id.run (GolubVanLoan.Chapter05.algorithm_5_1_3 pure (B p j) (B i j)) = (1, 0) := by
    simp only [h, GolubVanLoan.Chapter05.algorithm_5_1_3, ↓reduceIte]
    rfl
  rw [GolubVanLoan.Chapter05.givensStepExact, hcs,
    GolubVanLoan.Chapter05.givensApplyLeft_spec hpi 1 0
      (GolubVanLoan.Chapter05.nodup_indexFrom n j)]
  ext r q
  rw [of_apply]
  split_ifs
  · rw [GolubVanLoan.Chapter05.givensRotation_transpose_mul_apply hpi]
    split_ifs with h1 h2
    · rw [h1]; ring
    · rw [h2]; ring
    · rfl
  · rfl

/-- In exact arithmetic the test $a_{ij} \neq 0$ of the row-by-row Givens QR factorization (11.1.9)
of [golub2013matrix] changes nothing: for $n \le m$ and $A \in \mathbb{R}^{m \times n}$, the
exact run of `GolubVanLoan.Chapter11.rowGivensQR` equals the exact run of the row-oriented
Givens QR factorization of §5.2.5 (the second reordering of Algorithm 5.2.4),
`GolubVanLoan.Chapter05.givensQRByRow`. -/
theorem rowGivensQR_run_eq {m n : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (rowGivensQR pure hnm A) =
      Id.run (GolubVanLoan.Chapter05.givensQRByRow pure hnm A) := by
  simp only [rowGivensQR, GolubVanLoan.Chapter05.givensQRByRow, List.idRun_foldlM]
  congr 1
  funext B i
  refine List.foldl_ext _ _ _ fun B j hj => ?_
  have hji : (j : ℕ) < i := by simpa using hj
  have hpi : Fin.castLE hnm j ≠ i := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega
  split_ifs with h0
  · rfl
  · exact (givensStepExact_of_eq_zero hpi j (not_not.1 h0)).symm

/-- **Equation (11.1.9)** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{m \times n}$
with $n \le m$, and let $R$ be the exact output of the row-by-row Givens QR factorization. Then
there is an orthogonal $Q \in \mathbb{R}^{m \times m}$ with $A = QR$ and $R$ zero below the
diagonal, and $R^TR = A^TA$.

The matrix $Q$ is the product of the plane rotations. When $A$ has full column rank, the first
$n$ rows of $R$ are therefore the triangular factor of the thin QR factorization, up to the
signs of the rows. The QR factorization is `Matrix.IsQR`. The proof combines
`GolubVanLoan.Chapter11.rowGivensQR_run_eq` and `GolubVanLoan.Chapter05.givensQRByRow_spec`. -/
theorem equation_11_1_9 {m n : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    (∃ Q, IsQR A Q (Id.run (rowGivensQR pure hnm A))) ∧
      (Id.run (rowGivensQR pure hnm A))ᵀ * Id.run (rowGivensQR pure hnm A) = Aᵀ * A := by
  rw [rowGivensQR_run_eq]
  obtain ⟨Q, hQ⟩ := GolubVanLoan.Chapter05.givensQRByRow_spec hnm A
  refine ⟨⟨Q, hQ⟩, ?_⟩
  have hQQ : Qᵀ * Q = 1 := by
    have := (mem_unitaryGroup_iff'.1 hQ.mem_unitaryGroup)
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  conv_rhs => rw [← hQ.mul_eq]
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQQ, Matrix.one_mul]

/-! ### §11.1.9: sparse LU -/

/-- **Equations (11.1.10)–(11.1.11)** of [golub2013matrix], the first step of pivoted LU. Let the
permuted matrix $PAQ^T$ have the block form $[\alpha\ w^T; v\ B]$ with $\alpha \neq 0$,
$v, w \in \mathbb{R}^n$ and $B \in \mathbb{R}^{n \times n}$. Then
$$\begin{bmatrix} \alpha & w^T \\ v & B \end{bmatrix}
  = \begin{bmatrix} 1 & 0 \\ v / \alpha & I \end{bmatrix}
    \begin{bmatrix} \alpha & w^T \\ 0 & A^{(1)} \end{bmatrix},
  \qquad A^{(1)} = B - \frac{v w^T}{\alpha},$$
and $A^{(1)}$ is the Schur complement of the pivot $\alpha$: its entry $(i, j)$ is
$b_{ij} - v_i \alpha^{-1} w_j$.

The statement is about the block matrix itself; $P$ and $Q$ do not appear in it. The block
matrices are indexed by `Fin 1 ⊕ Fin n`, and the Schur complement is
`Matrix.schurComplementSingle` at the index `Sum.inl 0`. -/
theorem equation_11_1_10 {n : ℕ} {α : ℝ} (hα : α ≠ 0) (v w : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    fromBlocks (of fun _ _ => α) (of fun (_ : Fin 1) j => w j) (of fun i (_ : Fin 1) => v i) B =
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 (of fun i (_ : Fin 1) => v i / α) 1 *
          fromBlocks (of fun _ _ => α) (of fun (_ : Fin 1) j => w j) 0
            (B - α⁻¹ • vecMulVec v w) ∧
      ∀ i j, (B - α⁻¹ • vecMulVec v w) i j =
        (fromBlocks (of fun _ _ => α) (of fun (_ : Fin 1) j => w j)
          (of fun i (_ : Fin 1) => v i) B).schurComplementSingle (Sum.inl 0)
            ⟨Sum.inr i, Sum.inr_ne_inl⟩ ⟨Sum.inr j, Sum.inr_ne_inl⟩ := by
  refine ⟨?_, fun i j => ?_⟩
  · rw [fromBlocks_multiply]
    ext (i | i) (j | j)
    · simp
    · simp
    · simp [Matrix.mul_apply]; field_simp
    · simp [Matrix.mul_apply, vecMulVec_apply]
      field_simp
      ring
  · simp [vecMulVec_apply]; ring

/-- **Section 11.1.9** of [golub2013matrix], structural symmetry of the predicted pattern. Let
$A \in \mathbb{R}^{(n+1) \times (n+1)}$ be structurally symmetric, let $\sigma$ be a
permutation, and write $PAP^T = A(\sigma, \sigma) = [\alpha\ w^T; v\ B]$. Then $PAP^T$ is
structurally symmetric, and the pattern that (11.1.11) predicts for $A^{(1)} = B - vw^T/\alpha$
is symmetric: for all $i$ and $j$,
$$b_{ij} \neq 0 \text{ or } (v_i \neq 0 \text{ and } w_j \neq 0)
  \iff b_{ji} \neq 0 \text{ or } (v_j \neq 0 \text{ and } w_i \neq 0).$$

**Correction.** The source says that if $A$ is structurally symmetric and $P = Q$, then
$A^{(1)}$ is structurally symmetric. This is false for the computed $A^{(1)}$, because of
numerical cancellation; see `GolubVanLoan.Chapter11.symbolicElim_isPatternSymm_counterexample`.
The theorem states the claim for the predicted pattern.

A matrix is structurally symmetric when $a_{ij}$ and $a_{ji}$ are zero or nonzero together
(`Matrix.IsPatternSymm`). The index `0` is the pivot, and $b_{ij}$, $v_i$ and $w_j$ are the
entries $(i+1, j+1)$, $(i+1, 0)$ and $(0, j+1)$ of `A.submatrix σ σ`. -/
theorem symbolicElim_isPatternSymm {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsPatternSymm) (σ : Equiv.Perm (Fin (n + 1))) :
    (A.submatrix σ σ).IsPatternSymm ∧ ∀ i j : Fin n,
      (A.submatrix σ σ i.succ j.succ ≠ 0 ∨
          (A.submatrix σ σ i.succ 0 ≠ 0 ∧ A.submatrix σ σ 0 j.succ ≠ 0)) ↔
        (A.submatrix σ σ j.succ i.succ ≠ 0 ∨
          (A.submatrix σ σ j.succ 0 ≠ 0 ∧ A.submatrix σ σ 0 i.succ ≠ 0)) := by
  have hM := hA.submatrix σ
  refine ⟨hM, fun i j => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact h.imp (hM _ _).1 fun h' => ⟨(hM _ _).1 h'.2, (hM _ _).1 h'.1⟩
  · exact h.imp (hM _ _).1 fun h' => ⟨(hM _ _).1 h'.2, (hM _ _).1 h'.1⟩

/-- The claim of §11.1.9 of [golub2013matrix] that one elimination step keeps structural symmetry is
false as stated. The matrix
$$A = \begin{bmatrix} 1 & 1 & 1 \\ 1 & 1 & 2 \\ 1 & 1 & 1 \end{bmatrix}$$
is structurally symmetric, but one elimination step with the pivot $(1, 1)$ gives $A^{(1)} =
\begin{bmatrix} 0 & 1 \\ 0 & 0 \end{bmatrix}$, which is not. The cause is numerical
cancellation, which the remark of the source ignores. -/
theorem symbolicElim_isPatternSymm_counterexample :
    (!![1, 1, 1; 1, 1, 2; 1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).IsPatternSymm ∧
      ¬ ((!![1, 1, 1; 1, 1, 2; 1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).schurComplementSingle
        0).IsPatternSymm := by
  refine ⟨fun i j => ?_, fun h => ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num
  · have := h ⟨1, by decide⟩ ⟨2, by decide⟩
    norm_num [schurComplementSingle_apply] at this

end GolubVanLoan.Chapter11
