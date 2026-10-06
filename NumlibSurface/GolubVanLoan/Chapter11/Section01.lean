import Mathlib.Data.List.MinMax
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Sparse.Fill
import Numlib.LinearAlgebra.Sparse.Reordering
import NumlibSurface.GolubVanLoan.Chapter04.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section02

/-!
# Golub–Van Loan §11.1: direct methods

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition,
§11.1, *Direct Methods* (sparse Cholesky, QR and LU). The section has no numbered theorem; its
precise content is

* the two storage-format algorithms (11.1.1) (the sparse gaxpy) and (11.1.2) (the outer-product
  update with a preallocated pattern), for the compressed-column format of §11.1.1;
* the first step (11.1.3)–(11.1.4) of the outer-product Cholesky factorization and the first step
  (11.1.10)–(11.1.11) of the pivoted LU factorization, both one Schur complement
  (`Matrix.schurComplementSingle`);
* the graph-theoretic facts of §11.1.4–11.1.7: a symmetric permutation relabels the adjacency
  graph, a level-set (Cuthill–McKee) ordering is block tridiagonal, the Cholesky factor vanishes
  off the symbolic fill of Facts 1–2 (Parter's rule), and a nested dissection creates no fill
  between the dissected halves;
* Cholesky with symmetric pivoting (11.1.8) as a program, with the minimum-degree pivot rule;
* the seminormal equations of §11.1.8;
* the structural-symmetry remark of §11.1.9, in its symbolic reading, with a counterexample to
  the literal one.

## Design

Matrices are real, `Matrix (Fin n) (Fin n) ℝ`, 0-based: the book's `a_ij` (`i, j = 1:n`) is
`A (i−1) (j−1)`. The book's permutation `P = I_n(:, p)` acts as `A.submatrix p p` (`= P A Pᵀ`),
and `P v` for a vector is `v ∘ p`. The lower Cholesky factor `G` of the book (`A = G Gᵀ`) is `Hᵀ`
for the backbone's `Matrix.IsCholesky A H` (`H` upper triangular with positive diagonal,
`Hᴴ H = A`).

The compressed-column format is a surface structure `CompressedColumn m n nnz` with a `toMatrix`
reading; storage formats have no backbone theory, and the only claims the book makes about them are
that the loops (11.1.1)–(11.1.2) compute `y + A x` and `A + u vᵀ`. The programs follow the
algorithm conventions of `NumlibSurface/GolubVanLoan`: generic in a monad `M` with a rounding hook
`rnd : ℝ → M ℝ` through which every product, sum, quotient and square root passes; loops are
`List.foldlM` over index lists; index comparisons are exact. The book analyses no rounding error in
this section, so only exact specifications (`M := Id`, `rnd := pure`) are stated.

The printed facts "`g_ij` is nonzero assuming no numerical cancellation" have no exact reading; the
formal content is the other direction, which is exact: the Cholesky factor vanishes off the
symbolic fill (`Matrix.IsCholeskyFill`, `cholesky_eq_zero_of_not_isCholeskyFill`). The same holds
for §11.1.9's "`A⁽¹⁾` is structurally symmetric": true of the predicted pattern
(`symbolicElim_isPatternSymm`), false of the computed matrix
(`symbolicElim_isPatternSymm_counterexample`).

## Main results

* `CompressedColumn`, `CompressedColumn.toMatrix` — the compressed-column format.
* `sparseGaxpy`, `equation_11_1_1` — (11.1.1) computes `y + A x`.
* `sparseOuterProductUpdate`, `equation_11_1_2` — (11.1.2) computes `A + u vᵀ` when the pattern of
  `A` has room for it.
* `equation_11_1_3`, `equation_11_1_10` — the first Cholesky and LU steps as block factorizations.
* `adjGraph_submatrix_iso`, `submatrix_apply_eq_zero_of_levels_far` — §11.1.4–11.1.5.
* `profileIndex`, `profile` (the book uses the profile only in Problem P11.1.6), `minDegreePivot`,
  `choleskyWithPivoting`, `equation_11_1_8`, `minDegree_cholesky`.
* `cholesky_apply_eq`, `cholesky_eq_zero_of_not_isCholeskyFill`, `nestedDissection_cholesky`.
* `seminormal_cholesky`, `seminormal_normalEquations`, `seminormal_refinement` — §11.1.8.
* `rowGivensQR`, `equation_11_1_9` — the row-by-row Givens QR (11.1.9), a program calling chapter
  5's `givens` and row rotation, which computes a QR factorization.
* `symbolicElim_isPatternSymm`, `symbolicElim_isPatternSymm_counterexample` — §11.1.9.

## Not formalized here

The heuristics and "challenges" (choosing `P` to minimize `nnz(G)` is not a statement), Markowitz
pivoting and the threshold `τ`, the elimination tree (defined in prose, no theorem), the row
orderings for sparse QR, the complexity claims of §11.1.2 and §11.1.7, Björck's accuracy claim for
the seminormal equations with one refinement step, the numerical examples ((11.1.5), its profile
`37 → 25`, the Davis e-tree example), the row orderings that limit fill-in during (11.1.9), and the
Problems.
-/

open Matrix Finset

namespace GolubVanLoan.Chapter11

/-! ### §11.1.1: the compressed-column format -/

/-- **The compressed-column format** of §11.1.1: an `m × n` matrix with `nnz` stored entries. The
book's `A.val` is `val`, `A.r` is `row`, and `A.c` is `colStart`, shifted to 0-based positions:
column `j` occupies the positions `colStart j ≤ k < colStart (j+1)`, so `colStart 0 = 0` and
`colStart n = nnz` (the book's "the last component of `A.c` houses `nnz(A) + 1`"). Inside each
column the row indices are strictly increasing, which the merge of (11.1.2) relies on. A vector of
`ℝ^m` in this format is a `CompressedColumn m 1 nnz`. -/
structure CompressedColumn (m n nnz : ℕ) where
  /-- The stored values `A.val`. -/
  val : Fin nnz → ℝ
  /-- The row index `A.r(k)` of the stored value `A.val(k)`. -/
  row : Fin nnz → Fin m
  /-- The position `A.c(j)` where column `j` begins. -/
  colStart : Fin (n + 1) → ℕ
  /-- The first column begins at position `0`. -/
  colStart_zero : colStart 0 = 0
  /-- The columns end at position `nnz`. -/
  colStart_last : colStart (Fin.last n) = nnz
  /-- The column starts are nondecreasing. -/
  colStart_mono : Monotone colStart
  /-- Inside each column the row indices are strictly increasing. -/
  row_strictMono : ∀ (j : Fin n) (k l : Fin nnz), colStart j.castSucc ≤ k → k < l →
    (l : ℕ) < colStart j.succ → row k < row l

namespace CompressedColumn

variable {m n nnz : ℕ} (A : CompressedColumn m n nnz)

/-- The stored positions of column `j`, in increasing order: the book's
`k = A.c(j) : A.c(j+1) − 1`. -/
def positions (j : Fin n) : List (Fin nnz) :=
  (List.finRange nnz).filter fun k => A.colStart j.castSucc ≤ k ∧ (k : ℕ) < A.colStart j.succ

/-- Membership in the positions of a column. -/
theorem mem_positions {j : Fin n} {k : Fin nnz} :
    k ∈ A.positions j ↔ A.colStart j.castSucc ≤ k ∧ (k : ℕ) < A.colStart j.succ := by
  simp [positions]

/-- The positions of a column are distinct. -/
theorem nodup_positions (j : Fin n) : (A.positions j).Nodup :=
  (List.nodup_finRange nnz).filter _

/-- The positions of two different columns are disjoint. -/
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

/-- The row index of a stored entry determines it inside its column. -/
theorem eq_of_row_eq {j : Fin n} {k l : Fin nnz} (hk : k ∈ A.positions j)
    (hl : l ∈ A.positions j) (h : A.row k = A.row l) : k = l := by
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · rw [mem_positions] at hk hl
    exact absurd h (A.row_strictMono j k l hk.1 hkl hl.2).ne
  · rfl
  · rw [mem_positions] at hk hl
    exact absurd h.symm (A.row_strictMono j l k hl.1 hkl hk.2).ne

/-- **The matrix a compressed-column structure represents**: `a_ij` is the stored value at the
position of column `j` whose row index is `i`, and `0` when no such position is stored. -/
noncomputable def toMatrix : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, if k ∈ A.positions j ∧ A.row k = i then A.val k else 0

/-- The entries of the represented matrix. -/
theorem toMatrix_apply (i : Fin m) (j : Fin n) :
    A.toMatrix i j = ∑ k, if k ∈ A.positions j ∧ A.row k = i then A.val k else 0 := rfl

/-- Every position of a one-column structure (a sparse vector) belongs to its only column. -/
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

/-- The entries of a sparse vector. -/
theorem toMatrix_apply_zero (u : CompressedColumn m 1 nnz) (i : Fin m) :
    u.toMatrix i 0 = ∑ k, if u.row k = i then u.val k else 0 := by
  simp [toMatrix_apply, u.mem_positions_zero]

end CompressedColumn

/-! ### §11.1.2: the sparse gaxpy and the outer-product update -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The sparse gaxpy (11.1.1).** For `A ∈ ℝ^{m×n}` in compressed-column format and conventionally
stored `x`, `y`:
```
for j = 1:n
    k = A.c(j):A.c(j+1) − 1
    y(A.r(k)) = y(A.r(k)) + A.val(k)·x(j)
end
```
"overwrites `y` with `y + Ax`" (`equation_11_1_1`); each product and each sum is rounded. -/
def sparseGaxpy {mm n nnz : ℕ} (A : CompressedColumn mm n nnz) (x : Fin n → ℝ) (y : Fin mm → ℝ) :
    M (Fin mm → ℝ) :=
  (List.finRange n).foldlM (fun y j =>
    (A.positions j).foldlM (fun y k => do
      let p ← rnd (A.val k * x j)
      let s ← rnd (y (A.row k) + p)
      pure (Function.update y (A.row k) s)) y) y

/-- **The outer-product update with a preallocated pattern (11.1.2).** For `A`, `u`, `v` in
compressed-column format:
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
The pattern (`row`, `colStart`) is not changed; the index `α` (0-based here) is the merge pointer
into the stored entries of `u`, and the index comparisons are exact. -/
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

/-- The inner loop of the exact sparse gaxpy adds `x j` times the stored entries it visits. -/
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

/-- **(11.1.1) overwrites `y` with `y + A x`.** -/
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

/-- The step of the exact inner loop of (11.1.2) at the stored position `ℓ`, the merge pointer
into the entries of `u` being `st.2`. -/
private def outerUpdateStep {mm nnz nu : ℕ} (row : Fin nnz → Fin mm)
    (u : CompressedColumn mm 1 nu) (c : ℝ) (st : (Fin nnz → ℝ) × ℕ) (ℓ : Fin nnz) :
    (Fin nnz → ℝ) × ℕ :=
  if h : st.2 < nu then
    if row ℓ = u.row ⟨st.2, h⟩ then
      (Function.update st.1 ℓ (st.1 ℓ + u.val ⟨st.2, h⟩ * c), st.2 + 1)
    else st
  else st

/-- **The merge invariant of (11.1.2).** Along a list of positions with strictly increasing row
indices containing every row `u.r(a)`, `a ≥ α₀`, the merge from the pointer `α₀` adds
`u.val(a) · c` at the position of row `u.r(a)`, for each `a ≥ α₀`, and nothing else. -/
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

/-- A loop adding one increment per step adds their sum. -/
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

/-- **(11.1.2) computes `A + u vᵀ`** when the pattern of `A` has room for it: if for every stored
entry `v_j` of `v` the stored rows of column `j` of `A` include every stored row of `u` (the book's
"storing zeros in locations that are destined to become nonzero"), the exact loop overwrites `A`
with `A + u vᵀ`. The merge pointer `α` works because the row indices of `u` and of each column of
`A` are strictly increasing. -/
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

/-- **(11.1.3)–(11.1.4).** For `A = [α vᵀ; v B]` with `α > 0`,
`A = [√α 0; v/√α I] [1 0; 0 A⁽¹⁾] [√α vᵀ/√α; 0 I]` with `A⁽¹⁾ = B − v vᵀ/α`; and `A⁽¹⁾` is the
backbone's one-step Schur complement `Matrix.schurComplementSingle` of `A` at the pivot. The
block matrices are indexed by `Fin 1 ⊕ Fin n` (`Matrix.fromBlocks`). -/
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

/-- §11.1.4: "If `P` is a permutation, then, except for vertex labeling, the adjacency graphs for
`A` and `P A Pᵀ` look the same": the relabelling by `σ` is a graph isomorphism between the pattern
graphs of `A.submatrix σ σ` and `A`. For a symmetric matrix the pattern graph is the book's
adjacency graph `𝒢_A`: a node per row and an edge `(i, j)` for each nonzero off-diagonal `a_ij`. -/
theorem adjGraph_submatrix_iso {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) :
    (∃ e : (A.submatrix σ σ).adjGraph ≃g A.adjGraph, ∀ i, e i = σ i) ∧
      (A.IsSymm → ∀ i j, A.adjGraph.Adj i j ↔ i ≠ j ∧ A i j ≠ 0) :=
  ⟨⟨A.adjGraphIso σ, fun _ => rfl⟩, fun hA _ _ => by
    rw [adjGraph_adj_iff_of_isSymm hA, adjDigraph_adj]⟩

open Classical in
/-- **The profile index (11.1.6)**: `f_i(A) = min {j : 1 ≤ j ≤ i, a_ij ≠ 0}`, 0-based. When row
`i` has no nonzero at or left of the diagonal the book's minimum is undefined; then `f_i = i`, so
that the row contributes `0` to the profile. -/
noncomputable def profileIndex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Fin n :=
  if h : (univ.filter fun j => j ≤ i ∧ A i j ≠ 0).Nonempty then
    (univ.filter fun j => j ≤ i ∧ A i j ≠ 0).min' h
  else i

/-- The profile index of a row lies at or left of the diagonal. -/
theorem profileIndex_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    profileIndex A i ≤ i := by
  classical
  unfold profileIndex
  split_ifs with h
  · exact (Finset.mem_filter.1 (Finset.min'_mem _ h)).2.1
  · exact le_rfl

/-- **The profile** of §11.1.5: `profile(A) = n + ∑_{i=1}^n (i − f_i(A))`. -/
noncomputable def profile {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  n + ∑ i : Fin n, ((i : ℕ) - (profileIndex A i : ℕ))

/-- §11.1.5, **the level structure behind the Cuthill–McKee ordering**: for any permutation `σ`
and root `v` of `𝒢_A`, the entry `(k, l)` of `A(σ, σ)` vanishes whenever the levels (graph
distances to `v`) of the nodes `σ k` and `σ l` differ by two or more. For an ordering that lists
the level sets `S₀, S₁, …` consecutively (the Cuthill–McKee ordering, with any tie-breaking) this
says that `A(σ, σ)` is block tridiagonal with the level sets as diagonal blocks; the statement
itself is a fact about `A` and the levels, and the ordering is not constructed here. -/
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

/-- **The minimum-degree pivot rule** of §11.1.6: at step `k`, the index `p ≥ k` whose node has
minimal degree in the graph of the trailing block `A(k:n, k:n)` — the number of `i ≥ k`, `i ≠ p`,
with `a_ip ≠ 0` — ties broken by the least index. -/
noncomputable def minDegreePivot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Fin n :=
  (((List.finRange n).filter fun p => k ≤ p).argmin fun p =>
    (univ.filter fun i => k ≤ i ∧ i ≠ p ∧ A i p ≠ 0).card).getD k

/-- The minimum-degree pivot is taken from the trailing block. -/
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

/-- **Cholesky with symmetric pivoting (11.1.8)**, for a pivot rule `pivot` (the minimum-degree
ordering is `pivot := minDegreePivot`). The state is `(p, A)`, the accumulated permutation (the
book's `P`, acting as `A₀.submatrix p p`) and the working array. For `k = 1:n`:

* Steps 1–3: `q = pivot A k`, `P_k` the transposition of `k` and `q`; `P = diag(I_{k−1}, P_k) P`;
  `A(k:n, k:n) = P_k A(k:n, k:n) P_kᵀ` and `A(k:n, 1:k−1) = P_k A(k:n, 1:k−1)`;
* Step 4: `A(k:n, k) = A(k:n, k)/√A(k, k)` (one `√` followed by one rounding, then one rounded
  division per entry);
* Step 5: `A(k+1:n, k+1:n) = A(k+1:n, k+1:n) − A(k+1:n, k) A(k+1:n, k)ᵀ`.

The book runs `k = 1:n−2`, which leaves the last two columns unfactored; the program runs the loop
to `n`. On exit the lower triangle of `A` holds `G`. -/
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

/-! #### The exact semantics of (11.1.8) -/

/-- The exact step of (11.1.8) at column `k`, with the loops of Steps 4–5 in closed form. -/
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

/-- Step 4 of (11.1.8) in closed form: the listed rows of column `k` are divided by `d`. -/
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

/-- One row of Step 5 of (11.1.8) in closed form. -/
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

/-- Step 5 of (11.1.8) in closed form: the listed trailing entries lose `a_ik a_jk`. -/
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

/-- The exact run of (11.1.8) is the loop of `cholPivStep`. -/
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

/-- The invariant of (11.1.8) after `c` columns: `P A Pᵀ = G_c G_cᵀ + [0 0; 0 S]`, where `G_c` is
the lower triangle of the first `c` columns of the array and the trailing block `S` is positive
definite, and the computed diagonal entries are positive. -/
private structure CholPivInv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℕ)
    (st : Equiv.Perm (Fin n) × Matrix (Fin n) (Fin n) ℝ) : Prop where
  eq : ∀ i j, A (st.1 i) (st.1 j) =
    ∑ l : Fin n, (if (l : ℕ) < c ∧ l ≤ i ∧ l ≤ j then st.2 i l * st.2 j l else 0) +
      (if c ≤ (i : ℕ) ∧ c ≤ (j : ℕ) then st.2 i j else 0)
  posDef : (Matrix.of fun (i j : {i : Fin n // c ≤ (i : ℕ)}) => st.2 i j).PosDef
  diag_pos : ∀ l : Fin n, (l : ℕ) < c → 0 < st.2 l l

/-- Splitting off the last term of a sum over the first `c + 1` indices. -/
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

/-- **One step of (11.1.8) keeps the invariant.** -/
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

/-- The invariant holds after the whole loop. -/
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

/-- **(11.1.8) computes a Cholesky factorization of `P A Pᵀ`.** For symmetric positive definite
`A` and any pivot rule taking its pivot from the trailing block (`k ≤ pivot M k`), the exact run
returns `(p, M)` such that the lower triangle `G` of `M` is the Cholesky factor of
`A(p, p) = P A Pᵀ`: `Matrix.IsCholesky (A.submatrix p p) Gᵀ`. -/
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
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose, mul_apply, submatrix_apply,
      heq i j]
    have hlast : ¬ (n ≤ (i : ℕ) ∧ n ≤ (j : ℕ)) := fun h => by have := i.2; omega
    rw [ite_eq_right hlast, add_zero]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : l ≤ i <;> by_cases h2 : l ≤ j <;> simp [h1, h2, l.2]

/-- **(11.1.8) with the minimum-degree rule**: the exact run of `choleskyWithPivoting` with
`minDegreePivot` returns a Cholesky factorization of `P A Pᵀ`. -/
theorem minDegree_cholesky {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    let out := Id.run (choleskyWithPivoting pure minDegreePivot A)
    (A.submatrix out.1 out.1).IsCholesky
      (Matrix.of fun i j => if j ≤ i then out.2 i j else 0)ᵀ :=
  equation_11_1_8 hA minDegreePivot le_minDegreePivot

/-- §11.1.6, the formula after Fact 2: for `j < i`,
`g_ij = (a_ij − ∑_{k=1}^{j−1} g_ik g_jk) / g_jj`, where `G = Hᵀ` is the lower Cholesky factor:
entry `i` of the gaxpy Cholesky column formula (4.2.9) (`Chapter04.equation_4_2_9`), which holds
for every `i` (for `i < j` both sides vanish, for `i = j` it is the diagonal formula). -/
theorem cholesky_apply_eq {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℝ} (h : A.IsCholesky H)
    (i j : Fin n) :
    Hᵀ i j = (A i j - ∑ k ∈ univ.filter (· < j), Hᵀ i k * Hᵀ j k) / Hᵀ j j := by
  have hA : A = Hᵀ * Hᵀᵀ := by
    rw [transpose_transpose, ← h.conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial]
  have h49 := congrFun (Chapter04.equation_4_2_9 h.isUpperTriangular.transpose hA j) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply] at h49
  rw [eq_div_iff (by simpa using h.diag_ne_zero j), mul_comm, h49]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => mul_comm _ _)

/-- **Facts 1–2 of §11.1.6, the exact half**: the entry `g_ij`, `j < i`, of the lower Cholesky
factor vanishes unless `(i, j)` is in the symbolic fill of Facts 1–2 (`Matrix.IsCholeskyFill`: the
strictly lower nonzeros of `A`, closed under Parter's rule "`g_ik ≠ 0`, `g_jk ≠ 0`, `k < j < i` ⇒
`g_ij ≠ 0`"). This is what the preallocation of Step 0′ needs; the printed converse ("nonzero
assuming no numerical cancellation") has no exact reading. -/
theorem cholesky_eq_zero_of_not_isCholeskyFill {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℝ}
    (h : A.IsCholesky H) {i j : Fin n} (hji : j < i) (hfill : ¬ A.IsCholeskyFill i j) :
    Hᵀ i j = 0 :=
  h.apply_eq_zero_of_not_isCholeskyFill hji hfill

/-! ### §11.1.7: nested dissection -/

/-- §11.1.7, **the Cholesky factor inherits the zero block of a dissection**: if `P₀ A P₀ᵀ` (here
`A` itself) has the dissected form `[A₁ 0 C₁ᵀ; 0 A₂ C₂ᵀ; C₁ C₂ S]` — the indices split as
`I₁ = [0, n₁)`, `I₂ = [n₁, n₁ + n₂)` and the separator after them, with `A` vanishing between `I₂`
and `I₁` — then `g_ij = 0` for `i ∈ I₂`, `j ∈ I₁`: no fill enters the zero block. Repeating on each
diagonal block is the same statement one level down. -/
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

/-- §11.1.8: "if `A Pᵀ = Q R` is the thin QR factorization of `A Pᵀ`, then `P (Aᵀ A) Pᵀ = Rᵀ R`,
i.e., `Rᵀ` is the Cholesky factor of `P (Aᵀ A) Pᵀ`." Here `A Pᵀ = A(:, p)` is
`A.submatrix id σ`, `Q` has orthonormal columns, and `R` is upper triangular with positive
diagonal (which makes `A` of full column rank). -/
theorem seminormal_cholesky {m n : ℕ} {A Q : Matrix (Fin m) (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin n) ℝ} (σ : Equiv.Perm (Fin n)) (hQR : A.submatrix id σ = Q * R)
    (hQ : Qᵀ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) :
    ((Aᵀ * A).submatrix σ σ).IsCholesky R := by
  have h := isCholesky_conjTranspose_mul_self_of_qr hQR (by simpa using hQ) hR hd
  rwa [conjTranspose_eq_transpose_of_trivial, transpose_submatrix,
    ← submatrix_mul _ _ _ _ _ Function.bijective_id] at h

/-- §11.1.8, **the seminormal equations**: with `A Pᵀ = Q R` as in `seminormal_cholesky`, the normal
equations `Aᵀ A x = Aᵀ b` are equivalent to `P (Aᵀ b) = Rᵀ R (P x)`; `Q` is not needed. -/
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

/-- §11.1.8, Steps 3–4 (**one step of iterative improvement**): with `A Pᵀ = Q R` as in
`seminormal_cholesky`, `r = b − A x₀` and `e` solving the seminormal equations
`Rᵀ R (P e) = P (Aᵀ r)`, the improved `x₀ + e` solves the normal equations:
`Aᵀ A (x₀ + e) = Aᵀ b − Aᵀ r + Aᵀ r = Aᵀ b`. This holds for *any* `x₀`, however contaminated; the
accuracy of the computed result is Björck's analysis and is not formalized. -/
theorem seminormal_refinement {m n : ℕ} {A Q : Matrix (Fin m) (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin n) ℝ} (σ : Equiv.Perm (Fin n)) (hQR : A.submatrix id σ = Q * R)
    (hQ : Qᵀ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) (b : Fin m → ℝ)
    (x₀ e : Fin n → ℝ) (he : (Rᵀ * R) *ᵥ (e ∘ σ) = (Aᵀ *ᵥ (b - A *ᵥ x₀)) ∘ σ) :
    (Aᵀ * A) *ᵥ (x₀ + e) = Aᵀ *ᵥ b := by
  have h := (seminormal_normalEquations σ hQR hQ hR hd e (b - A *ᵥ x₀)).2 he.symm
  rw [mulVec_add, h, mulVec_sub, ← mulVec_mulVec]
  abel

/-- **The row-by-row Givens QR (11.1.9)**, "introducing zeros into `A ∈ ℝ^{m×n}` one row at a time":
```
for i = 2:m
  for j = 1:min{i − 1, n}
    if a_ij ≠ 0
      compute a Givens rotation G with G [a_jj; a_ij] = [×; 0]
      update the rows j, i of A on the columns j:n by G
```
With `n ≤ m` (the least-squares setting of §11.1.8). The rotation is chapter 5's `givens`
(Algorithm 5.1.3) of `(a_jj, a_ij)` and the update its row helper `givensApplyLeft` on the column
list `[j, …, n−1]` (conventions 5, 10, 13); the test `a_ij ≠ 0` is an exact comparison on the
computed entry (convention 1). -/
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

/-- A skipped rotation (`a_ij = 0`) is the rotation `givens` would have computed: for `b = 0`,
Algorithm 5.1.3 returns `(c, s) = (1, 0)`, and the exact Givens step is the identity. -/
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

/-- In exact arithmetic the test `a_ij ≠ 0` of (11.1.9) changes nothing: the exact run is chapter
5's row-oriented Givens QR (§5.2.5, the second reordering). -/
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

/-- **Exact semantics of (11.1.9)**: for `n ≤ m`, the overwritten array `R` is the triangular
factor of a QR factorization `A = Q R` (`Q` orthogonal, the product of the plane rotations; `R`
zero below the diagonal), so `Rᵀ R = Aᵀ A`: its first `n` rows are the `R` of the thin QR
factorization up to row signs. From `rowGivensQR_run_eq` and chapter 5's `givensQRByRow_spec`. -/
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

/-- **(11.1.10)–(11.1.11).** The first step of pivoted LU: for `P A Qᵀ = [α wᵀ; v B]` with
`α ≠ 0`, `P A Qᵀ = [1 0; v/α I_{n−1}] [α wᵀ; 0 A⁽¹⁾]` with `A⁽¹⁾ = B − v wᵀ/α`, the backbone's
one-step Schur complement at the pivot. -/
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

/-- §11.1.9, "if `A` is structurally symmetric and `P = Q`, then `A⁽¹⁾` is structurally symmetric",
in its exact, **symbolic** reading: a symmetric permutation `M = P A Pᵀ` of a structurally symmetric
`A` is structurally symmetric, and the pattern (11.1.11) predicts for `A⁽¹⁾ = B − v wᵀ/α` —
`b_ij ≠ 0` or (`v_i ≠ 0` and `w_j ≠ 0`) — is symmetric. The computed `A⁽¹⁾` need not be
(`symbolicElim_isPatternSymm_counterexample`). -/
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

/-- The printed claim of §11.1.9 is **false as stated**: `A = [1 1 1; 1 1 2; 1 1 1]` is structurally
symmetric, but one elimination step with pivot `(1, 1)` gives `A⁽¹⁾ = [0 1; 0 0]`, which is not —
numerical cancellation, which the book's remark ignores. -/
theorem symbolicElim_isPatternSymm_counterexample :
    (!![1, 1, 1; 1, 1, 2; 1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).IsPatternSymm ∧
      ¬ ((!![1, 1, 1; 1, 1, 2; 1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).schurComplementSingle
        0).IsPatternSymm := by
  refine ⟨fun i j => ?_, fun h => ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num
  · have := h ⟨1, by decide⟩ ⟨2, by decide⟩
    norm_num [schurComplementSingle_apply] at this

end GolubVanLoan.Chapter11
