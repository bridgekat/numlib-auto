/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Block`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Block multiplication and block triangular products

This module collects facts about how products of matrices see a partition of their indices into
blocks. They are the general rules behind the triangular, banded and trapezoidal shapes of
`Numlib.LinearAlgebra.Matrix.Triangular` and `Numlib.LinearAlgebra.Matrix.Band`. The first is
**block multiplication** with blocks of arbitrary sizes: the $(a, b)$ block of $AB$ is
$\sum_c A_{ac} B_{cb}$ ([golub2013matrix], Theorem 1.3.1). The second says that the diagonal of a
product of two block triangular matrices with singleton blocks is the product of the diagonals. The
third is the rectangular product rule: if $A_{ik} = 0$ whenever $c(k) < b(i)$ and $B_{kj} = 0$
whenever $d(j) < c(k)$, then $(AB)_{ij} = 0$ whenever $d(j) < b(i)$. This rule gives the trapezoidal
shapes of rectangular factorizations.

The module also provides two vocabularies for a block split of matrices indexed by
$\{0, \dots, N - 1\}$. The first splits the indices into the first $r$ indices and the last $N - r$
indices, and builds block vectors $\begin{bmatrix} y \\ z \end{bmatrix}$ from them. The second is
the block diagonal matrix $\operatorname{diag}(a, Q)$ with a $1 \times 1$ corner $a$, as in §6.5.3
of [golub2013matrix].

## Main definitions

* `Matrix.tailIdx`: the last $N - r$ indices $r, r + 1, \dots, N - 1$ of $\{0, \dots, N - 1\}$.
* `Matrix.blockEquiv`: the bijection $\{0, \dots, r - 1\} \sqcup \{0, \dots, N - r - 1\} \to \{0,
  \dots, N - 1\}$ formed by the first and the last indices.
* `Matrix.blockVec`: the vector $\begin{bmatrix} y \\ z \end{bmatrix}$ with $y$ on the first $r$
  indices and $z$ on the others.
* `Matrix.consDiag`: the block diagonal matrix $\operatorname{diag}(a, Q)$ with the scalar $a$ in
  the corner.

## Main results

* `Matrix.mul_submatrix_sigmaMk_eq_sum`: block multiplication, $(AB)_{ab} = \sum_c A_{ac} B_{cb}$,
  for blocks of arbitrary sizes.
* `Matrix.BlockTriangular.mul_apply_self_of_injective`: the diagonal of a product of two block
  triangular matrices with singleton blocks is the product of the diagonals.
* `Matrix.mul_apply_eq_zero_of_lt`: the rectangular product rule.
* `Matrix.fromBlocks_submatrix_sum_map`: reindexing a $2 \times 2$ block matrix on both sides
  reindexes each block.
* `Matrix.exists_fromBlocks_zero₂₁_pow_eq`: the powers of a $2 \times 2$ block upper triangular
  matrix are block upper triangular, with the powers of the diagonal blocks on the diagonal.
* `Matrix.fromRows_add`, `Matrix.fromRows_sub`: matrices partitioned by rows add and subtract
  blockwise.
* `Matrix.sum_eq_sum_castLE_add_sum_tailIdx`: a sum over $\{0, \dots, N - 1\}$ splits into the sums
  over the first $r$ and the last $N - r$ indices.
* `Matrix.conjTranspose_submatrix_mul_submatrix_of_mem_unitaryGroup`: two column blocks $V_{:, f}$
  and $V_{:, g}$ of a unitary matrix satisfy $V_{:, f}^H V_{:, g} = I_{f, g}$; the row form is
  `Matrix.submatrix_mul_conjTranspose_submatrix_of_mem_unitaryGroup`.

## Implementation notes

* Blocks of arbitrary sizes are indexed by `Sigma` types: the rows of $A$ are `Σ a, m a`, and the
  $(a, c)$ block of $A$ is `A.submatrix (Sigma.mk a) (Sigma.mk c)`. Mathlib has the $2 \times 2$
  case `Matrix.fromBlocks_multiply`, the block diagonal case `Matrix.blockDiagonal'_mul` and the
  case of square blocks of equal size `Matrix.compRingEquiv`, but not the general statement.
* The diagonal of a product is stated for `Matrix.BlockTriangular` with an injective block map. Its
  instances are `Matrix.IsUpperTriangular.mul_apply_self` and
  `Matrix.IsLowerTriangular.mul_apply_self`. The rectangular product rule is the form of
  `Matrix.BlockTriangular.mul` with a block map on each of the three index types.
* The first $r$ indices are `Fin.castLE h : Fin r → Fin N`, and the last $N - r$ indices are
  `Matrix.tailIdx h : Fin (N - r) → Fin N`. A matrix reindexed along `Matrix.blockEquiv` on both
  sides is a `Matrix.fromBlocks` matrix of its four blocks.
* `Matrix.fromRows_add` and `Matrix.fromRows_sub` are the companions of Mathlib's
  `Matrix.fromRows_neg`.
* `Matrix.consDiag` is built with `Fin.cons`.
-/

namespace Matrix

/-! ### Block multiplication over a `Sigma` index -/

section Sigma

variable {ι α β R : Type*} [Fintype ι] {m : α → Type*} {p : ι → Type*} {n : β → Type*}
  [∀ c, Fintype (p c)] [NonUnitalNonAssocSemiring R]

/-- **Block multiplication** ([golub2013matrix], Theorem 1.3.1). Let $A$ and $B$ be matrices over a
semiring, partitioned into blocks of arbitrary sizes, with the column blocks of $A$ and the row
blocks of $B$ indexed by the same finite set. Then for every row block $a$ of $A$ and every
column block $b$ of $B$,
$$(AB)_{ab} = \sum_c A_{ac} B_{cb}.$$

The matrices are `A : Matrix (Σ a, m a) (Σ c, p c) R` and `B : Matrix (Σ c, p c) (Σ b, n b) R`,
and the block $A_{ac}$ is `A.submatrix (Sigma.mk a) (Sigma.mk c)`. -/
theorem mul_submatrix_sigmaMk_eq_sum (A : Matrix (Σ a, m a) (Σ c, p c) R)
    (B : Matrix (Σ c, p c) (Σ b, n b) R) (a : α) (b : β) :
    (A * B).submatrix (Sigma.mk a) (Sigma.mk b) =
      ∑ c, A.submatrix (Sigma.mk a) (Sigma.mk c) * B.submatrix (Sigma.mk c) (Sigma.mk b) := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sigma, Matrix.sum_apply]

end Sigma

/-! ### Diagonals of block triangular products -/

section Diag

variable {n R α : Type*} [LinearOrder α] {b : n → α} [Fintype n] [NonUnitalNonAssocSemiring R]

/-- Let $M$ and $N$ be square matrices over a semiring that are block triangular for an injective
block map $b$ into a linear order, that is, block triangular with singleton blocks. Then for
every index $i$, $(MN)_{ii} = M_{ii} N_{ii}$.

In $\sum_k M_{ik} N_{ki}$, every term with $k \ne i$ has $b(k) \ne b(i)$, and then one of the
two factors is $0$. Block triangularity is `Matrix.BlockTriangular`: $M_{ij} = 0$ whenever
$b(j) < b(i)$. -/
theorem BlockTriangular.mul_apply_self_of_injective {M N : Matrix n n R}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (hb : Function.Injective b) (i : n) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne (hb.ne hk) with h | h
  · rw [hM h, zero_mul]
  · rw [hN h, mul_zero]

end Diag

/-! ### The rectangular product rule -/

section Rectangular

/-- **The rectangular product rule.** Let $b$, $c$ and $d$ be maps from the row indices of $A$, the
inner indices and the column indices of $B$ into a linear order, with finitely many inner
indices. Suppose that $A_{ik} = 0$ whenever $c(k) < b(i)$, and $B_{kj} = 0$ whenever
$d(j) < c(k)$. Then
$$(AB)_{ij} = 0 \quad \text{whenever } d(j) < b(i).$$

Every term $A_{ik} B_{kj}$ of the product has $c(k) < b(i)$ or $d(j) < b(i) \le c(k)$. This is
the rectangular form of `Matrix.BlockTriangular.mul`, and it gives the trapezoidal shapes of
rectangular factorizations. -/
theorem mul_apply_eq_zero_of_lt {α l m n R : Type*} [LinearOrder α] [Fintype m]
    [NonUnitalNonAssocSemiring R] {b : l → α} {c : m → α} {d : n → α} {A : Matrix l m R}
    {B : Matrix m n R} (hA : ∀ i k, c k < b i → A i k = 0) (hB : ∀ k j, d j < c k → B k j = 0)
    {i : l} {j : n} (hij : d j < b i) : (A * B) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (c k) (b i) with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k j (hij.trans_le h), mul_zero]

end Rectangular

/-! ### Reindexing a `2 × 2` block matrix -/

section Reindex

variable {l m n o l' m' n' o' α : Type*}

/-- Reindexing a $2 \times 2$ block matrix by `Sum.map` on both sides reindexes each block:
$$\begin{bmatrix} A & B \\ C & D \end{bmatrix}_{(f \sqcup g), (h \sqcup k)} = \begin{bmatrix}
  A_{fh} & B_{fk} \\ C_{gh} & D_{gk} \end{bmatrix}.$$
-/
theorem fromBlocks_submatrix_sum_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : n' → n) (g : o' → o) (h : l' → l) (k : m' → m) :
    (fromBlocks A B C D).submatrix (Sum.map f g) (Sum.map h k) =
      fromBlocks (A.submatrix f h) (B.submatrix f k) (C.submatrix g h) (D.submatrix g k) := by
  ext (i | i) (j | j) <;> rfl

end Reindex

/-! ### Powers of a block upper triangular matrix -/

/-- **The powers of a $2 \times 2$ block upper triangular matrix.** Let $M_{11}$ and $M_{22}$ be
square matrices over a semiring and let $M_{12}$ be a matrix of the matching shape. Then for
every $k \in \mathbb{N}$ there is a matrix $Y$ with
$$\begin{bmatrix} M_{11} & M_{12} \\ 0 & M_{22} \end{bmatrix}^k = \begin{bmatrix} M_{11}^k & Y
  \\ 0 & M_{22}^k \end{bmatrix}.$$
This is the block form of `Matrix.BlockTriangular.pow`. -/
theorem exists_fromBlocks_zero₂₁_pow_eq {p q R : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] [Semiring R] (M₁₁ : Matrix p p R) (M₁₂ : Matrix p q R) (M₂₂ : Matrix q q R)
    (k : ℕ) : ∃ Y, fromBlocks M₁₁ M₁₂ 0 M₂₂ ^ k = fromBlocks (M₁₁ ^ k) Y 0 (M₂₂ ^ k) := by
  induction k with
  | zero => exact ⟨0, by rw [pow_zero, pow_zero, pow_zero, fromBlocks_one]⟩
  | succ k ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨M₁₁ ^ k * M₁₂ + Y * M₂₂, ?_⟩
    rw [pow_succ, hY, fromBlocks_multiply, pow_succ, pow_succ]
    simp

/-! ### Sums of matrices partitioned by rows -/

section FromRows

variable {m₁ m₂ n α : Type*}

/-- Matrices partitioned by rows add blockwise:
$$\begin{bmatrix} A_1 \\ A_2 \end{bmatrix} + \begin{bmatrix} B_1 \\ B_2 \end{bmatrix} =
  \begin{bmatrix} A_1 + B_1 \\ A_2 + B_2 \end{bmatrix}.$$
-/
theorem fromRows_add [Add α] (A₁ B₁ : Matrix m₁ n α) (A₂ B₂ : Matrix m₂ n α) :
    fromRows A₁ A₂ + fromRows B₁ B₂ = fromRows (A₁ + B₁) (A₂ + B₂) := by
  ext (i | i) j <;> rfl

/-- Matrices partitioned by rows subtract blockwise:
$$\begin{bmatrix} A_1 \\ A_2 \end{bmatrix} - \begin{bmatrix} B_1 \\ B_2 \end{bmatrix} =
  \begin{bmatrix} A_1 - B_1 \\ A_2 - B_2 \end{bmatrix}.$$
-/
theorem fromRows_sub [Sub α] (A₁ B₁ : Matrix m₁ n α) (A₂ B₂ : Matrix m₂ n α) :
    fromRows A₁ A₂ - fromRows B₁ B₂ = fromRows (A₁ - B₁) (A₂ - B₂) := by
  ext (i | i) j <;> rfl

end FromRows

/-! ### Leading and trailing indices of `Fin N` -/

section TailIdx

variable {α : Type*} {r N : ℕ}

/-- For $r \le N$, the last $N - r$ indices $r, r + 1, \dots, N - 1$ of $\{0, \dots, N - 1\}$,
indexed by $\{0, \dots, N - r - 1\}$: the index $j$ is sent to $r + j$. -/
def tailIdx (h : r ≤ N) (j : Fin (N - r)) : Fin N := ⟨r + j, by omega⟩

/-- The trailing index `Matrix.tailIdx h j` has the value $r + j$. -/
@[simp]
theorem val_tailIdx (h : r ≤ N) (j : Fin (N - r)) : (tailIdx h j : ℕ) = r + j := rfl

/-- The map `Matrix.tailIdx h` is injective. -/
theorem tailIdx_injective (h : r ≤ N) : Function.Injective (tailIdx h) := fun a b e =>
  Fin.ext (by have := congrArg Fin.val e; simp only [val_tailIdx] at this; omega)

/-- For $r \le N$, the bijection $\{0, \dots, r - 1\} \sqcup \{0, \dots, N - r - 1\} \to \{0, \dots,
N - 1\}$ that sends $i$ in the first part to $i$ and $j$ in the second part to $r + j$.

The first part is sent by `Fin.castLE h`, and the second part by `Matrix.tailIdx h`. A matrix
reindexed along this bijection on both sides is a `Matrix.fromBlocks` matrix of its four blocks. -/
def blockEquiv (h : r ≤ N) : Fin r ⊕ Fin (N - r) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))

/-- `Matrix.blockEquiv` sends `Sum.inl i` to the index `Fin.castLE h i`, which has the value $i$. -/
@[simp]
theorem blockEquiv_inl (h : r ≤ N) (i : Fin r) :
    blockEquiv h (Sum.inl i) = Fin.castLE h i := Fin.ext rfl

/-- `Matrix.blockEquiv` sends `Sum.inr j` to the trailing index `Matrix.tailIdx h j`, which has the
value $r + j$. -/
@[simp]
theorem blockEquiv_inr (h : r ≤ N) (j : Fin (N - r)) :
    blockEquiv h (Sum.inr j) = tailIdx h j := Fin.ext rfl

/-- For an index $i < r$ of $\{0, \dots, N - 1\}$, the inverse of `Matrix.blockEquiv` sends $i$ to
$i$ in the first part. -/
theorem blockEquiv_symm_apply_of_lt (h : r ≤ N) {i : Fin N} (hi : (i : ℕ) < r) :
    (blockEquiv h).symm i = Sum.inl ⟨i, hi⟩ :=
  (Equiv.symm_apply_eq _).2 (Fin.ext rfl)

/-- For an index $i \ge r$ of $\{0, \dots, N - 1\}$, the inverse of `Matrix.blockEquiv` sends $i$ to
$i - r$ in the second part. -/
theorem blockEquiv_symm_apply_of_le (h : r ≤ N) {i : Fin N} (hi : r ≤ (i : ℕ)) :
    (blockEquiv h).symm i = Sum.inr ⟨i - r, by omega⟩ :=
  (Equiv.symm_apply_eq _).2 <| Fin.ext <| by
    rw [blockEquiv_inr, val_tailIdx]; exact (Nat.add_sub_cancel' hi).symm

/-- For $r \le N$, a vector $y$ indexed by $\{0, \dots, r - 1\}$ and a vector $z$ indexed by
$\{0, \dots, N - r - 1\}$, the vector $\begin{bmatrix} y \\ z \end{bmatrix}$ indexed by
$\{0, \dots, N - 1\}$: its entry $k$ is $y_k$ if $k < r$ and $z_{k - r}$ otherwise. -/
def blockVec (h : r ≤ N) (y : Fin r → α) (z : Fin (N - r) → α) : Fin N → α :=
  fun k => if hk : (k : ℕ) < r then y ⟨k, hk⟩ else z ⟨k - r, by omega⟩

/-- The first $r$ entries of $\begin{bmatrix} y \\ z \end{bmatrix}$ are the entries of $y$. -/
@[simp]
theorem blockVec_castLE (h : r ≤ N) (y : Fin r → α) (z : Fin (N - r) → α) (i : Fin r) :
    blockVec h y z (Fin.castLE h i) = y i := by
  simp [blockVec]

/-- The last $N - r$ entries of $\begin{bmatrix} y \\ z \end{bmatrix}$ are the entries of $z$: entry
$r + j$ is $z_j$. -/
@[simp]
theorem blockVec_tailIdx (h : r ≤ N) (y : Fin r → α) (z : Fin (N - r) → α) (j : Fin (N - r)) :
    blockVec h y z (tailIdx h j) = z j := by
  simp [blockVec, tailIdx]

/-- For $r \le N$, a sum over $\{0, \dots, N - 1\}$ splits into the first $r$ and the last $N - r$
indices:
$$\sum_{k = 0}^{N - 1} f(k) = \sum_{i = 0}^{r - 1} f(i) + \sum_{j = 0}^{N - r - 1} f(r + j).$$
-/
theorem sum_eq_sum_castLE_add_sum_tailIdx {β : Type*} [AddCommMonoid β] (h : r ≤ N)
    (f : Fin N → β) :
    ∑ k, f k = ∑ i : Fin r, f (Fin.castLE h i) + ∑ j : Fin (N - r), f (tailIdx h j) := by
  classical
  set g : ℕ → β := fun k => if hk : k < N then f ⟨k, hk⟩ else 0 with hg
  have h1 : ∑ k, f k = ∑ k ∈ Finset.range N, g k := by
    rw [← Fin.sum_univ_eq_sum_range g N]
    exact Finset.sum_congr rfl fun k _ => by simp [hg]
  have h2 : ∑ i : Fin r, f (Fin.castLE h i) = ∑ k ∈ Finset.range r, g k := by
    rw [← Fin.sum_univ_eq_sum_range g r]
    exact Finset.sum_congr rfl fun i _ => by simp [hg, Fin.castLE, show (i : ℕ) < N by omega]
  have h3 : ∑ j : Fin (N - r), f (tailIdx h j) = ∑ k ∈ Finset.range (N - r), g (r + k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => g (r + k)) (N - r)]
    exact Finset.sum_congr rfl fun j _ => by simp [hg, tailIdx, show r + (j : ℕ) < N by omega]
  rw [h1, h2, h3, ← Finset.sum_range_add, Nat.add_sub_cancel' h]

/-- Every vector $x$ indexed by $\{0, \dots, N - 1\}$ is the block vector of its first $r$ entries
and its last $N - r$ entries. -/
theorem blockVec_head_tail (h : r ≤ N) (x : Fin N → α) :
    blockVec h (fun i => x (Fin.castLE h i)) (fun j => x (tailIdx h j)) = x := by
  funext k
  unfold blockVec
  split_ifs with hk
  · rfl
  · exact congrArg x (Fin.ext (by simp; omega))

end TailIdx

/-! ### Column and row blocks of a unitary matrix -/

section UnitaryBlocks

variable {n l o α : Type*} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]
  {V : Matrix n n α}

/-- Let $V$ be a unitary matrix over a commutative ring with an involution, and let $f$ and $g$
select columns of $V$. Then the two column blocks are orthonormal to each other:
$(V_{:, f})^H V_{:, g} = I_{f, g}$, the $(f, g)$ block of the identity matrix. -/
theorem conjTranspose_submatrix_mul_submatrix_of_mem_unitaryGroup
    (hV : V ∈ unitaryGroup n α) (f : l → n) (g : o → n) :
    (V.submatrix id f)ᴴ * V.submatrix id g = (1 : Matrix n n α).submatrix f g := by
  rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hV]

/-- Let $V$ be a unitary matrix over a commutative ring with an involution, and let $f$ and $g$
select rows of $V$. Then the two row blocks are orthonormal to each other:
$V_{f, :} (V_{g, :})^H = I_{f, g}$, the $(f, g)$ block of the identity matrix. -/
theorem submatrix_mul_conjTranspose_submatrix_of_mem_unitaryGroup
    (hV : V ∈ unitaryGroup n α) (f : l → n) (g : o → n) :
    V.submatrix f id * (V.submatrix g id)ᴴ = (1 : Matrix n n α).submatrix f g := by
  rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 hV]

end UnitaryBlocks

/-! ### The block diagonal matrix `diag(a, Q)` -/

section ConsDiag

variable {α : Type*} {m n p : ℕ}

/-!
### Row forms of tuple lemmas

The tuple lemmas `Fin.cons_zero`, `Fin.cons_succ`, `Fin.insertNth_apply_same` and
`Fin.insertNth_apply_succAbove` do not apply as `simp` lemmas to a tuple of rows given as a
`Matrix`, because its type is not syntactically a function type. The following lemmas are their row
forms.
-/

/-- The first row of the matrix with first row $w$ and further rows those of $A$ is $w$. -/
@[simp]
theorem cons_rows_zero (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α) (j : Fin n) :
    (Fin.cons w A : Fin (m + 1) → Fin n → α) 0 j = w j := rfl

/-- Row $i + 1$ of the matrix with first row $w$ and further rows those of $A$ is row $i$ of $A$. -/
@[simp]
theorem cons_rows_succ (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α) (i : Fin m)
    (j : Fin n) : (Fin.cons w A : Fin (m + 1) → Fin n → α) i.succ j = A i j := rfl

/-- Let $A$ be a matrix with $m$ rows, $w$ a row, and $k \in \{0, \dots, m\}$. In the matrix
`Fin.insertNth k w A`, obtained by inserting $w$ into the rows of $A$ at position $k$, row $k$
is $w$.

This is the row form of `Fin.insertNth_apply_same`, which does not apply as a `simp` lemma to a
tuple of rows given as a `Matrix`. -/
@[simp]
theorem insertNth_rows_same (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α)
    (k : Fin (m + 1)) (j : Fin n) :
    (Fin.insertNth k w A : Fin (m + 1) → Fin n → α) k j = w j := by
  have h := Fin.insertNth_apply_same (α := fun _ => Fin n → α) k w (fun i => A i)
  exact congrFun h j

/-- Let $A$ be a matrix with $m$ rows, $w$ a row, and $k \in \{0, \dots, m\}$. In the matrix
`Fin.insertNth k w A`, obtained by inserting $w$ into the rows of $A$ at position $k$, the other
rows are the rows of $A$ in their order: row `k.succAbove i` is row $i$ of $A$.

This is the row form of `Fin.insertNth_apply_succAbove`. -/
@[simp]
theorem insertNth_rows_succAbove (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α)
    (k : Fin (m + 1)) (i : Fin m) (j : Fin n) :
    (Fin.insertNth k w A : Fin (m + 1) → Fin n → α) (k.succAbove i) j = A i j := by
  have h := Fin.insertNth_apply_succAbove (α := fun _ => Fin n → α) k w (fun i => A i) i
  exact congrFun h j

/-- **The block diagonal matrix $\operatorname{diag}(a, Q)$.** For a scalar $a$ and an $m \times n$
matrix $Q$, this is the $(m + 1) \times (n + 1)$ matrix
$$\operatorname{diag}(a, Q) = \begin{bmatrix} a & 0 \\ 0 & Q \end{bmatrix},$$
with $a$ in the corner $(0, 0)$ and $Q$ in the trailing block. The case
$\operatorname{diag}(1, Q)$ appears in §6.5.3 of [golub2013matrix]. -/
def consDiag [Zero α] (a : α) (Q : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) α :=
  of (Fin.cons (Fin.cons a 0) fun i => Fin.cons 0 (Q i))

section Apply

variable [Zero α] (a : α) (Q : Matrix (Fin m) (Fin n) α)

/-- The corner entry of $\operatorname{diag}(a, Q)$ is $a$. -/
@[simp] theorem consDiag_zero_zero : consDiag a Q 0 0 = a := rfl

/-- The first row of $\operatorname{diag}(a, Q)$ is $0$ off the corner. -/
@[simp] theorem consDiag_zero_succ (j : Fin n) : consDiag a Q 0 j.succ = 0 := rfl

/-- The first column of $\operatorname{diag}(a, Q)$ is $0$ off the corner. -/
@[simp] theorem consDiag_succ_zero (i : Fin m) : consDiag a Q i.succ 0 = 0 := rfl

/-- The trailing block of $\operatorname{diag}(a, Q)$ is $Q$: the entry $(i + 1, j + 1)$ is
$Q_{ij}$. -/
@[simp] theorem consDiag_succ_succ (i : Fin m) (j : Fin n) : consDiag a Q i.succ j.succ = Q i j :=
  rfl

end Apply

/-- For a scalar $a$, an $m \times n$ matrix $Q$, a vector $w$ of length $p$ and an $n \times p$
matrix $X$,
$$\operatorname{diag}(a, Q) \begin{bmatrix} w^T \\ X \end{bmatrix} = \begin{bmatrix} a w^T \\ QX
  \end{bmatrix}.$$
-/
theorem consDiag_mul_of_cons [NonUnitalNonAssocSemiring α] (a : α) (Q : Matrix (Fin m) (Fin n) α)
    (w : Fin p → α) (X : Matrix (Fin n) (Fin p) α) :
    consDiag a Q * of (Fin.cons w X) = of (Fin.cons (a • w) (Q * X)) := by
  ext i j
  induction i using Fin.cases <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- $\operatorname{diag}(a, Q) \operatorname{diag}(b, Q') = \operatorname{diag}(ab, QQ')$. -/
theorem consDiag_mul_consDiag [NonUnitalNonAssocSemiring α] (a b : α)
    (Q : Matrix (Fin m) (Fin n) α) (Q' : Matrix (Fin n) (Fin p) α) :
    consDiag a Q * consDiag b Q' = consDiag (a * b) (Q * Q') := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- $\operatorname{diag}(1, I) = I$. -/
@[simp]
theorem consDiag_one [Zero α] [One α] : consDiag (1 : α) (1 : Matrix (Fin m) (Fin m) α) = 1 := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- $\operatorname{diag}(a, Q)^H = \operatorname{diag}(\bar a, Q^H)$, where $\bar a$ is the
involution `star a`. -/
theorem conjTranspose_consDiag [AddMonoid α] [StarAddMonoid α] (a : α)
    (Q : Matrix (Fin m) (Fin n) α) : (consDiag a Q)ᴴ = consDiag (star a) Qᴴ := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;> simp

/-- Over a commutative ring with an involution, if $a \bar a = 1$ and $Q$ is unitary, then
$\operatorname{diag}(a, Q)$ is unitary. -/
theorem consDiag_mem_unitaryGroup [CommRing α] [StarRing α] {a : α} (ha : a * star a = 1)
    {Q : Matrix (Fin m) (Fin m) α} (hQ : Q ∈ unitaryGroup (Fin m) α) :
    consDiag a Q ∈ unitaryGroup (Fin (m + 1)) α := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_consDiag, consDiag_mul_consDiag,
    ha, ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 hQ, consDiag_one]

end ConsDiag

end Matrix
