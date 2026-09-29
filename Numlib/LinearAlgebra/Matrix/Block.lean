/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Block`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Block multiplication and block triangular products

Three facts about how products of matrices see a partition of their indices into blocks, the
general rules behind the triangular, banded and trapezoidal shapes of
`Numlib/LinearAlgebra/Matrix/Triangular` and `Numlib/LinearAlgebra/Matrix/Band`.

## Main results

* `Matrix.mul_submatrix_sigmaMk_eq_sum`: **block multiplication** with blocks of arbitrary sizes.
  For `A : Matrix (Σ a, m a) (Σ c, p c) R` and `B : Matrix (Σ c, p c) (Σ b, n b) R`, the `(a, b)`
  block of `A * B` is `∑ c, A_{ac} B_{cb}` ([golub2013matrix] Theorem 1.3.1). Mathlib has the
  `2 × 2` case `Matrix.fromBlocks_multiply`, the block diagonal case `Matrix.blockDiagonal'_mul`
  and the case of uniform square blocks `Matrix.compRingEquiv`, but not the general statement.
* `Matrix.BlockTriangular.mul_apply_self_of_injective`: the diagonal of a product of two block
  triangular matrices with singleton blocks is the product of the diagonals; its instances are the
  triangular statements `Matrix.IsUpperTriangular.mul_apply_self` and
  `Matrix.IsLowerTriangular.mul_apply_self`.
* `Matrix.mul_apply_eq_zero_of_lt`: **the rectangular product rule**, the form of
  `Matrix.BlockTriangular.mul` with a block map on each of the three index types, behind the
  trapezoidal shapes of rectangular factorizations.
* `Matrix.fromBlocks_submatrix_sum_map`: reindexing a `2 × 2` block matrix by `Sum.map` on both
  sides reindexes each block.

## Leading and trailing blocks on `Fin`

Two vocabularies for a block split of `Fin`-indexed matrices without a reindexing to a sum type:

* the head `Fin.castLE h : Fin r → Fin N` and the tail `Matrix.tailIdx h : Fin (N - r) → Fin N`
  of `Fin N`, the vector `[y; z]` built from them (`Matrix.blockVec`), and the matching split of a
  sum (`Matrix.sum_eq_sum_castLE_add_sum_tailIdx`);
* the block diagonal matrix `diag(a, Q)` with a `1 × 1` corner (`Matrix.consDiag`), built by
  `Fin.cons`, with its product, identity, conjugate transpose and unitarity rules.

## References

* [golub2013matrix] §1.3, §6.5.3.
-/

namespace Matrix

/-! ### Block multiplication over a `Sigma` index -/

section Sigma

variable {ι α β R : Type*} [Fintype ι] {m : α → Type*} {p : ι → Type*} {n : β → Type*}
  [∀ c, Fintype (p c)] [NonUnitalNonAssocSemiring R]

/-- **Block multiplication** ([golub2013matrix] Theorem 1.3.1): the `(a, b)` block of `A * B` is
`∑ c, A_{ac} B_{cb}`, for blocks of arbitrary sizes indexed by `Sigma` types. -/
theorem mul_submatrix_sigmaMk_eq_sum (A : Matrix (Σ a, m a) (Σ c, p c) R)
    (B : Matrix (Σ c, p c) (Σ b, n b) R) (a : α) (b : β) :
    (A * B).submatrix (Sigma.mk a) (Sigma.mk b) =
      ∑ c, A.submatrix (Sigma.mk a) (Sigma.mk c) * B.submatrix (Sigma.mk c) (Sigma.mk b) := by
  ext i j
  simp [mul_apply, Fintype.sum_sigma, sum_apply]

end Sigma

/-! ### Diagonals of block triangular products -/

section Diag

variable {n R α : Type*} [LinearOrder α] {b : n → α} [Fintype n] [NonUnitalNonAssocSemiring R]

/-- The diagonal of a product of two block triangular matrices with singleton blocks is the
product of the diagonals: in `∑ k, M i k * N k i` every term with `k ≠ i` has `b k ≠ b i`, and one
of the two factors then vanishes. -/
theorem BlockTriangular.mul_apply_self_of_injective {M N : Matrix n n R}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (hb : Function.Injective b) (i : n) :
    (M * N) i i = M i i * N i i := by
  rw [mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne (hb.ne hk) with h | h
  · rw [hM h, zero_mul]
  · rw [hN h, mul_zero]

end Diag

/-! ### The rectangular product rule -/

section Rectangular

/-- **The rectangular product rule** behind the trapezoidal shapes, the rectangular form of
`Matrix.BlockTriangular.mul` with a block map on each of the three index types: if `A i k = 0`
whenever `c k < b i` and `B k j = 0` whenever `d j < c k`, then `(A * B) i j = 0` whenever
`d j < b i`, because every term `A i k * B k j` of the product has `c k < b i` or
`d j < b i ≤ c k`. -/
theorem mul_apply_eq_zero_of_lt {α l m n R : Type*} [LinearOrder α] [Fintype m]
    [NonUnitalNonAssocSemiring R] {b : l → α} {c : m → α} {d : n → α} {A : Matrix l m R}
    {B : Matrix m n R} (hA : ∀ i k, c k < b i → A i k = 0) (hB : ∀ k j, d j < c k → B k j = 0)
    {i : l} {j : n} (hij : d j < b i) : (A * B) i j = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (c k) (b i) with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k j (hij.trans_le h), mul_zero]

end Rectangular

/-! ### Reindexing a `2 × 2` block matrix -/

section Reindex

variable {l m n o l' m' n' o' α : Type*}

/-- Reindexing a block matrix by `Sum.map` on both sides reindexes each block. -/
theorem fromBlocks_submatrix_sum_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : n' → n) (g : o' → o) (h : l' → l) (k : m' → m) :
    (fromBlocks A B C D).submatrix (Sum.map f g) (Sum.map h k) =
      fromBlocks (A.submatrix f h) (B.submatrix f k) (C.submatrix g h) (D.submatrix g k) := by
  ext (i | i) (j | j) <;> rfl

end Reindex

/-! ### Leading and trailing indices of `Fin N` -/

section TailIdx

variable {α : Type*} {r N : ℕ}

/-- The trailing indices `r, r + 1, …, N − 1` of `Fin N`, indexed by `Fin (N − r)`. -/
def tailIdx (h : r ≤ N) (j : Fin (N - r)) : Fin N := ⟨r + j, by omega⟩

/-- The value of a trailing index. -/
@[simp]
theorem val_tailIdx (h : r ≤ N) (j : Fin (N - r)) : (tailIdx h j : ℕ) = r + j := rfl

/-- The trailing indices are distinct. -/
theorem tailIdx_injective (h : r ≤ N) : Function.Injective (tailIdx h) := fun a b e =>
  Fin.ext (by have := congrArg Fin.val e; simp only [val_tailIdx] at this; omega)

/-- The vector `[y; z]` on `Fin N`, with `y` on the first `r` indices and `z` on the rest. -/
def blockVec (h : r ≤ N) (y : Fin r → α) (z : Fin (N - r) → α) : Fin N → α :=
  fun k => if hk : (k : ℕ) < r then y ⟨k, hk⟩ else z ⟨k - r, by omega⟩

/-- The head of `[y; z]` is `y`. -/
@[simp]
theorem blockVec_castLE (h : r ≤ N) (y : Fin r → α) (z : Fin (N - r) → α) (i : Fin r) :
    blockVec h y z (Fin.castLE h i) = y i := by
  simp [blockVec]

/-- The tail of `[y; z]` is `z`. -/
@[simp]
theorem blockVec_tailIdx (h : r ≤ N) (y : Fin r → α) (z : Fin (N - r) → α) (j : Fin (N - r)) :
    blockVec h y z (tailIdx h j) = z j := by
  simp [blockVec, tailIdx]

/-- A sum over `Fin N` splits into the leading `r` and the trailing `N − r` indices. -/
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

/-- Every vector on `Fin N` is the block vector of its head and tail. -/
theorem blockVec_head_tail (h : r ≤ N) (x : Fin N → α) :
    blockVec h (fun i => x (Fin.castLE h i)) (fun j => x (tailIdx h j)) = x := by
  funext k
  unfold blockVec
  split_ifs with hk
  · rfl
  · exact congrArg x (Fin.ext (by simp; omega))

end TailIdx

/-! ### The block diagonal matrix `diag(a, Q)` -/

section ConsDiag

variable {α : Type*} {m n p : ℕ}

/-! The tuple lemmas `Fin.cons_zero` and `Fin.cons_succ` do not fire on a tuple of rows given as a
`Matrix`, whose type is not syntactically a function type; these are their row forms. -/

/-- The first row of `Fin.cons w A` is `w`. -/
@[simp]
theorem cons_rows_zero (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α) (j : Fin n) :
    (Fin.cons w A : Fin (m + 1) → Fin n → α) 0 j = w j := rfl

/-- The later rows of `Fin.cons w A` are the rows of `A`. -/
@[simp]
theorem cons_rows_succ (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α) (i : Fin m)
    (j : Fin n) : (Fin.cons w A : Fin (m + 1) → Fin n → α) i.succ j = A i j := rfl

/-- **The block diagonal matrix `diag(a, Q)`** on `Fin (m + 1) × Fin (n + 1)`: `a` in the corner
`(0, 0)`, `Q` on the trailing block, zero elsewhere ([golub2013matrix] §6.5.3, `diag(1, Q)`). -/
def consDiag [Zero α] (a : α) (Q : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) α :=
  of (Fin.cons (Fin.cons a 0) fun i => Fin.cons 0 (Q i))

section Apply

variable [Zero α] (a : α) (Q : Matrix (Fin m) (Fin n) α)

/-- The corner entry of `diag(a, Q)`. -/
@[simp] theorem consDiag_zero_zero : consDiag a Q 0 0 = a := rfl

/-- The first row of `diag(a, Q)` vanishes off the corner. -/
@[simp] theorem consDiag_zero_succ (j : Fin n) : consDiag a Q 0 j.succ = 0 := rfl

/-- The first column of `diag(a, Q)` vanishes off the corner. -/
@[simp] theorem consDiag_succ_zero (i : Fin m) : consDiag a Q i.succ 0 = 0 := rfl

/-- The trailing block of `diag(a, Q)` is `Q`. -/
@[simp] theorem consDiag_succ_succ (i : Fin m) (j : Fin n) : consDiag a Q i.succ j.succ = Q i j :=
  rfl

end Apply

/-- `diag(a, Q) [wᵀ; X] = [a wᵀ; Q X]`. -/
theorem consDiag_mul_of_cons [NonUnitalNonAssocSemiring α] (a : α) (Q : Matrix (Fin m) (Fin n) α)
    (w : Fin p → α) (X : Matrix (Fin n) (Fin p) α) :
    consDiag a Q * of (Fin.cons w X) = of (Fin.cons (a • w) (Q * X)) := by
  ext i j
  induction i using Fin.cases <;> simp [mul_apply, Fin.sum_univ_succ]

/-- `diag(a, Q) diag(b, Q') = diag(a b, Q Q')`. -/
theorem consDiag_mul_consDiag [NonUnitalNonAssocSemiring α] (a b : α)
    (Q : Matrix (Fin m) (Fin n) α) (Q' : Matrix (Fin n) (Fin p) α) :
    consDiag a Q * consDiag b Q' = consDiag (a * b) (Q * Q') := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [mul_apply, Fin.sum_univ_succ]

/-- `diag(1, 1) = 1`. -/
@[simp]
theorem consDiag_one [Zero α] [One α] : consDiag (1 : α) (1 : Matrix (Fin m) (Fin m) α) = 1 := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- `diag(a, Q)ᴴ = diag(a⋆, Qᴴ)`. -/
theorem conjTranspose_consDiag [AddMonoid α] [StarAddMonoid α] (a : α)
    (Q : Matrix (Fin m) (Fin n) α) : (consDiag a Q)ᴴ = consDiag (star a) Qᴴ := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;> simp

/-- `diag(a, Q)` is unitary when `a` is and `Q` is. -/
theorem consDiag_mem_unitaryGroup [CommRing α] [StarRing α] {a : α} (ha : a * star a = 1)
    {Q : Matrix (Fin m) (Fin m) α} (hQ : Q ∈ unitaryGroup (Fin m) α) :
    consDiag a Q ∈ unitaryGroup (Fin (m + 1)) α := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_consDiag, consDiag_mul_consDiag,
    ha, ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 hQ, consDiag_one]

end ConsDiag

end Matrix
