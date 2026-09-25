/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Orthogonal bidiagonalization

Every rectangular matrix is carried by a unitary matrix on each side to an upper bidiagonal one,
`Uᴴ A V = B`: the **Golub–Kahan bidiagonalization** ([golub2013matrix] §5.4.8, (5.4.13);
[quarteroni2000numerical] (5.57); Golub–Kahan 1965), the first stage of every algorithm for the
singular value decomposition and the matrix form of the Golub–Kahan–Lanczos process of
`Numlib/Krylov/Bidiagonalization`.

## Main results

* `Matrix.exists_unitary_mul_mul_unitary_apply_eq_zero`: entrywise, for any `M × N` matrix, the
  entries of `Uᴴ A V` off the diagonal and the first superdiagonal vanish. Tail reflectors
  (`Matrix.householderTail` of `Numlib/LinearAlgebra/Matrix/QR`) alternate on the left (column
  `k`, pivot `k`) and on the right (row `k`, pivot `k + 1`); the right reflector's axis vanishes on
  the columns `≤ k`, so the zeros already created survive.
* `Matrix.exists_orthogonal_mul_mul_orthogonal_isUpperBidiagonal`: for `N ≤ M`, `Uᴴ A V` is zero
  below row `N` and upper bidiagonal (`Matrix.IsUpperBidiagonal` of
  `Numlib/LinearAlgebra/Matrix/Hessenberg`) on top.
* `Matrix.IsUpperBidiagonalRect`, `Matrix.IsLowerBidiagonalRect`: the rectangular shapes, dual
  under transposition, with their bandwidth characterizations
  (`Matrix.isUpperBidiagonalRect_iff_hasBandwidthRect`) and their agreement with the square
  shapes on `Fin N` (`Matrix.isUpperBidiagonalRect_iff_isUpperBidiagonal`).
* `Matrix.IsBidiagonalization A U V B`: the factorization `Uᴴ A V = B` as a named specification,
  with existence (`Matrix.exists_isBidiagonalization`), the `R`-bidiagonalization
  (`Matrix.IsBidiagonalization.of_isQR`, [golub2013matrix] §5.4.9: a QR factorization first, then
  a bidiagonalization of the square triangular block, glued by `diag(U_R, I)`), and the link to the
  tridiagonalization of `Aᴴ A` (`Matrix.IsBidiagonalization.isTridiagonal_conjTranspose_mul_self`).

## Implementation notes

The square bidiagonal shapes `Matrix.IsUpperBidiagonal`, `Matrix.IsLowerBidiagonal` are phrased with
the order on the index and live in `Numlib/LinearAlgebra/Matrix/Hessenberg`; the statements here
are on `Fin M × Fin N`, with the index difference taken in `ℕ` as in the rectangular band
vocabulary of `Numlib/LinearAlgebra/Matrix/Band`. The lower shape is the one of the `(k + 1) × k`
matrix of the Golub–Kahan lower bidiagonalization ([golub2013matrix] (10.4.18)).

The block matrices `[B; 0]` and `diag(U, I)` of the `R`-bidiagonalization are `Matrix.padRows`
(the right inverse of `Matrix.firstRows`) and `Matrix.padOne`, both defined through
`Matrix.fromRows`/`Matrix.fromBlocks` reindexed along `Fin N ⊕ Fin (M - N) ≃ Fin M`, so that the
block product rules of Mathlib apply.

## References

* [golub2013matrix] §5.4.8, §5.4.9.
* [quarteroni2000numerical] §5.8.3.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The Golub–Kahan bidiagonalization -/

section Bidiagonal

variable {M N : ℕ}

/-- The left half-step of the bidiagonalization: the tail reflector of column `k` with pivot `k`
clears that column below the diagonal, keeps the rows before `k` and the columns already cleared. -/
private theorem bidiag_left_step (B : Matrix (Fin M) (Fin N) 𝕜) {k : ℕ} (hk : k < N)
    (hB : ∀ (i : Fin M) (j : Fin N), ((i : ℕ) < k ∨ (j : ℕ) < k) → (i : ℕ) ≠ j →
      (i : ℕ) + 1 ≠ j → B i j = 0) :
    ∃ P : Matrix (Fin M) (Fin M) 𝕜, P.IsHermitian ∧ P ∈ Matrix.unitaryGroup (Fin M) 𝕜 ∧
      ∀ (i : Fin M) (j : Fin N), ((i : ℕ) < k ∨ (j : ℕ) < k + 1) → (i : ℕ) ≠ j →
        (i : ℕ) + 1 ≠ j → (P * B) i j = 0 := by
  refine ⟨householder (householderTail (fun i => B i ⟨k, hk⟩) k), isHermitian_householder _,
    householder_householderTail_mem_unitaryGroup _ _, fun i j hij hne1 hne2 => ?_⟩
  rcases hij with hi | hj
  · rw [householder_mul_apply_of_apply_eq_zero (householderTail_apply_of_lt _ hi)]
    exact hB i j (Or.inl hi) hne1 hne2
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
  · rw [householder_mul_apply, householder_mulVec_eq_self_of_apply_eq_zero fun r hr => ?_]
    · exact hB i j (Or.inr hjk) hne1 hne2
    · have hkr : k ≤ (r : ℕ) := not_lt.1 fun hrk => hr (householderTail_apply_of_lt _ hrk)
      exact hB r j (Or.inr hjk) (by omega) (by omega)
  · have hjκ : j = ⟨k, hk⟩ := Fin.ext hjk
    subst hjκ
    rw [householder_mul_apply]
    rcases lt_or_gt_of_ne hne1 with hik | hik
    · rw [householder_householderTail_mulVec_apply_of_lt _ hik]
      exact hB i _ (Or.inl hik) hne1 hne2
    · exact householder_householderTail_mulVec_apply_of_gt _ hik

/-- The right half-step of the bidiagonalization: the reflector of the conjugate tail axis of row
`k` with pivot `k + 1` clears that row beyond the superdiagonal, keeps the columns `≤ k` and the
rows already cleared. -/
private theorem bidiag_right_step (B : Matrix (Fin M) (Fin N) 𝕜) {k : ℕ} (hk : k < M)
    (hB : ∀ (i : Fin M) (j : Fin N), ((i : ℕ) < k ∨ (j : ℕ) < k + 1) → (i : ℕ) ≠ j →
      (i : ℕ) + 1 ≠ j → B i j = 0) :
    ∃ V ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin M) (j : Fin N), ((i : ℕ) < k + 1 ∨ (j : ℕ) < k + 1) → (i : ℕ) ≠ j →
        (i : ℕ) + 1 ≠ j → (B * V) i j = 0 := by
  refine ⟨householder (star (householderTail (fun j => B ⟨k, hk⟩ j) (k + 1))),
    householder_star_householderTail_mem_unitaryGroup _ _, fun i j hij hne1 hne2 => ?_⟩
  rcases hij with hi | hj
  swap
  · rw [mul_householder_apply_of_apply_eq_zero
      (by rw [Pi.star_apply, householderTail_apply_of_lt _ hj, star_zero])]
    exact hB i j (Or.inr hj) hne1 hne2
  rw [mul_householder_star_apply]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hik | hik
  · rw [householder_mulVec_eq_self_of_apply_eq_zero fun r hr => ?_]
    · exact hB i j (Or.inl hik) hne1 hne2
    · have hkr : k + 1 ≤ (r : ℕ) := not_lt.1 fun hrk => hr (householderTail_apply_of_lt _ hrk)
      exact hB i r (Or.inl hik) (by omega) (by omega)
  · have hiκ : i = ⟨k, hk⟩ := Fin.ext hik
    subst hiκ
    rcases lt_or_gt_of_ne hne2 with hjk | hjk
    · exact householder_householderTail_mulVec_apply_of_gt _ hjk
    · rw [householder_householderTail_mulVec_apply_of_lt _ hjk]
      exact hB _ j (Or.inr hjk) hne1 hne2

/-- **The Golub–Kahan bidiagonalization**, entrywise ([quarteroni2000numerical] (5.57);
[golub1989matrix] §5.4.3): any rectangular matrix is carried by a unitary matrix on each side to
one whose only nonzero entries lie on the diagonal and the first superdiagonal. Alternating tail
reflectors on the left (column `k`, pivot `k`) and on the right (row `k`, pivot `k + 1`); the
right reflector's axis vanishes on the columns `≤ k`, so the zeros already created survive. -/
theorem exists_unitary_mul_mul_unitary_apply_eq_zero (A : Matrix (Fin M) (Fin N) 𝕜) :
    ∃ U ∈ Matrix.unitaryGroup (Fin M) 𝕜, ∃ V ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin M) (j : Fin N), (i : ℕ) ≠ j → (i : ℕ) + 1 ≠ j → (Uᴴ * A * V) i j = 0 := by
  suffices h : ∀ k : ℕ, ∃ U ∈ Matrix.unitaryGroup (Fin M) 𝕜, ∃ V ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin M) (j : Fin N), ((i : ℕ) < k ∨ (j : ℕ) < k) → (i : ℕ) ≠ j → (i : ℕ) + 1 ≠ j →
        (Uᴴ * A * V) i j = 0 by
    obtain ⟨U, hU, V, hV, h⟩ := h N
    exact ⟨U, hU, V, hV, fun i j => h i j (Or.inr j.isLt)⟩
  intro k
  induction k with
  | zero => exact ⟨1, one_mem _, 1, one_mem _, fun i j hij => absurd hij (by simp)⟩
  | succ k ih =>
    obtain ⟨U, hU, V, hV, hB⟩ := ih
    by_cases hkN : k < N
    swap
    · refine ⟨U, hU, V, hV, fun i j hij => hB i j ?_⟩
      rcases hij with hi | hj
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr (by have := j.isLt; omega)
      · exact Or.inr (by have := j.isLt; omega)
    obtain ⟨P, hPh, hPu, hPB⟩ := bidiag_left_step (Uᴴ * A * V) hkN hB
    have hUP : (U * P)ᴴ * A * V = P * (Uᴴ * A * V) := by
      rw [conjTranspose_mul, hPh.eq]
      simp only [Matrix.mul_assoc]
    by_cases hkM : k < M
    swap
    · refine ⟨U * P, mul_mem hU hPu, V, hV, fun i j hij hne1 hne2 => ?_⟩
      rw [hUP]
      refine hPB i j ?_ hne1 hne2
      rcases hij with hi | hj
      · exact Or.inl (by have := i.isLt; omega)
      · exact Or.inr hj
    obtain ⟨W, hWu, hWB⟩ := bidiag_right_step (P * (Uᴴ * A * V)) hkM hPB
    refine ⟨U * P, mul_mem hU hPu, V * W, mul_mem hV hWu, fun i j hij hne1 hne2 => ?_⟩
    rw [← Matrix.mul_assoc, hUP]
    exact hWB i j hij hne1 hne2

/-- **The Golub–Kahan bidiagonalization** ([quarteroni2000numerical] (5.57); [golub1989matrix]
§5.4.3): for `A : Matrix (Fin M) (Fin N) 𝕜` with `N ≤ M` there are unitary `U`, `V` with
`Uᴴ A V = (B; 0)`, zero below row `N` and upper bidiagonal on top. This is the first phase of the
Golub–Kahan–Reinsch computation of the singular value decomposition. -/
theorem exists_orthogonal_mul_mul_orthogonal_isUpperBidiagonal (h : N ≤ M)
    (A : Matrix (Fin M) (Fin N) 𝕜) :
    ∃ U ∈ Matrix.unitaryGroup (Fin M) 𝕜, ∃ V ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      (∀ (i : Fin M) (j : Fin N), N ≤ (i : ℕ) → (Uᴴ * A * V) i j = 0) ∧
        ((Uᴴ * A * V).submatrix (Fin.castLE h) id).IsUpperBidiagonal := by
  obtain ⟨U, hU, V, hV, hB⟩ := exists_unitary_mul_mul_unitary_apply_eq_zero A
  refine ⟨U, hU, V, hV, fun i j hi =>
    hB i j (by have := j.isLt; omega) (by have := j.isLt; omega), ?_⟩
  intro i j hij
  rw [submatrix_apply, id]
  rcases hij with hji | ⟨l, hil, hlj⟩
  · have h1 := Fin.lt_def.1 hji
    exact hB _ _ (by simp; omega) (by simp; omega)
  · have h1 := Fin.lt_def.1 hil
    have h2 := Fin.lt_def.1 hlj
    exact hB _ _ (by simp; omega) (by simp; omega)

end Bidiagonal

/-! ### Rectangular bidiagonal shapes -/

section Shapes

variable {R : Type*} [Zero R] {M N : ℕ}

/-- A rectangular matrix is **upper bidiagonal** when its only nonzero entries lie on the diagonal
and the first superdiagonal, the index difference taken in `ℕ`: the shape of [golub2013matrix]
(5.4.13) for `M ≥ N` (the rows from the `N`-th on vanish automatically) and of `[B | 0]` for
`M < N`. On a square `Fin N` it is `Matrix.IsUpperBidiagonal`
(`Matrix.isUpperBidiagonalRect_iff_isUpperBidiagonal`). -/
def IsUpperBidiagonalRect (B : Matrix (Fin M) (Fin N) R) : Prop :=
  ∀ (i : Fin M) (j : Fin N), (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → B i j = 0

/-- A rectangular matrix is **lower bidiagonal** when its only nonzero entries lie on the diagonal
and the first subdiagonal: the shape of the `(k + 1) × k` matrix of the Golub–Kahan lower
bidiagonalization ([golub2013matrix] (10.4.18)). It is the transpose of the upper shape
(`Matrix.isUpperBidiagonalRect_transpose_iff`). -/
def IsLowerBidiagonalRect (B : Matrix (Fin M) (Fin N) R) : Prop :=
  ∀ (i : Fin M) (j : Fin N), (i : ℕ) ≠ j → (i : ℕ) ≠ j + 1 → B i j = 0

/-- Transposition carries the upper bidiagonal shape to the lower one. -/
theorem isUpperBidiagonalRect_transpose_iff {B : Matrix (Fin M) (Fin N) R} :
    Bᵀ.IsUpperBidiagonalRect ↔ B.IsLowerBidiagonalRect :=
  forall_comm

/-- Transposition carries the lower bidiagonal shape to the upper one. -/
theorem isLowerBidiagonalRect_transpose_iff {B : Matrix (Fin M) (Fin N) R} :
    Bᵀ.IsLowerBidiagonalRect ↔ B.IsUpperBidiagonalRect :=
  forall_comm

/-- "Upper bidiagonal" is "lower bandwidth `0`, upper bandwidth `1`" ([golub2013matrix]
Table 1.2.1). -/
theorem isUpperBidiagonalRect_iff_hasBandwidthRect {B : Matrix (Fin M) (Fin N) R} :
    B.IsUpperBidiagonalRect ↔ B.HasLowerBandwidthRect 0 ∧ B.HasUpperBandwidthRect 1 := by
  refine ⟨fun h => ⟨fun i j hij => h i j (by omega) (by omega),
    fun i j hij => h i j (by omega) (by omega)⟩, fun h i j h1 h2 => ?_⟩
  rcases lt_or_gt_of_ne h1 with hj | hj
  · exact h.1 i j (by omega)
  · exact h.2 i j (by omega)

/-- "Lower bidiagonal" is "lower bandwidth `1`, upper bandwidth `0`", by transposition from the
upper shape. -/
theorem isLowerBidiagonalRect_iff_hasBandwidthRect {B : Matrix (Fin M) (Fin N) R} :
    B.IsLowerBidiagonalRect ↔ B.HasLowerBandwidthRect 1 ∧ B.HasUpperBandwidthRect 0 := by
  rw [← isUpperBidiagonalRect_transpose_iff, isUpperBidiagonalRect_iff_hasBandwidthRect,
    hasLowerBandwidthRect_transpose_iff, hasUpperBandwidthRect_transpose_iff, and_comm]

/-- On a square `Fin N`, the rectangular upper bidiagonal shape is the order-theoretic one of
`Numlib/LinearAlgebra/Matrix/Hessenberg`. -/
theorem isUpperBidiagonalRect_iff_isUpperBidiagonal {B : Matrix (Fin N) (Fin N) R} :
    B.IsUpperBidiagonalRect ↔ B.IsUpperBidiagonal := by
  refine ⟨fun h i j hij => ?_, fun h i j h1 h2 => ?_⟩
  · rcases hij with hij | ⟨k, hik, hkj⟩
    · rw [Fin.lt_def] at hij
      exact h i j (by omega) (by omega)
    · rw [Fin.lt_def] at hik hkj
      exact h i j (by omega) (by omega)
  · rcases lt_or_gt_of_ne h1 with hj | hj
    · exact h i j (Or.inl (Fin.lt_def.2 hj))
    · exact h i j (Or.inr ⟨⟨i + 1, by omega⟩, Fin.lt_def.2 (by simp),
        Fin.lt_def.2 (by simp; omega)⟩)

/-- On a square `Fin N`, the rectangular lower bidiagonal shape is the order-theoretic one of
`Numlib/LinearAlgebra/Matrix/Hessenberg`, by transposition from the upper shape. -/
theorem isLowerBidiagonalRect_iff_isLowerBidiagonal {B : Matrix (Fin N) (Fin N) R} :
    B.IsLowerBidiagonalRect ↔ B.IsLowerBidiagonal := by
  rw [← isUpperBidiagonalRect_transpose_iff, isUpperBidiagonalRect_iff_isUpperBidiagonal,
    isUpperBidiagonal_transpose_iff]

/-- The Gram matrix `Bᴴ B` of an upper bidiagonal matrix is tridiagonal: `(Bᴴ B)_{ij}` sums
`conj(b_{ki}) b_{kj}` over the rows `k` with `i, j ∈ {k, k + 1}`. -/
theorem IsUpperBidiagonalRect.isTridiagonal_conjTranspose_mul_self {R : Type*}
    [NonUnitalNonAssocSemiring R] [StarAddMonoid R] {B : Matrix (Fin M) (Fin N) R}
    (hB : B.IsUpperBidiagonalRect) : (Bᴴ * B).IsTridiagonal := by
  intro i j hij
  have hij' : (j : ℕ) + 1 < i ∨ (i : ℕ) + 1 < j := by
    rcases hij with ⟨l, h1, h2⟩ | ⟨l, h1, h2⟩ <;> rw [Fin.lt_def] at h1 h2 <;> omega
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [conjTranspose_apply]
  by_cases hk : (i : ℕ) = k ∨ (i : ℕ) = k + 1
  · rw [hB k j (by omega) (by omega), mul_zero]
  · rw [hB k i (by omega) (by omega), star_zero, zero_mul]

end Shapes

/-! ### Padding a matrix to more rows -/

section Pad

variable {α : Type*} {M N : ℕ} {n' : Type*}

/-- `[B; 0]`: a matrix on `Fin N` rows stacked on `M - N` zero rows, for `N ≤ M`; the right
inverse of `Matrix.firstRows` (`Matrix.firstRows_padRows`). -/
def padRows [Zero α] (B : Matrix (Fin N) n' α) (h : N ≤ M) : Matrix (Fin M) n' α :=
  (fromRows B (0 : Matrix (Fin (M - N)) n' α)).submatrix
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))).symm id

/-- `diag(U, I)`: a square matrix on the first `N` indices of `Fin M` extended by the identity on
the last `M - N`, for `N ≤ M` — the `diag(U_R, I_{m-n})` of [golub2013matrix] §5.4.9. -/
def padOne [Zero α] [One α] (U : Matrix (Fin N) (Fin N) α) (h : N ≤ M) :
    Matrix (Fin M) (Fin M) α :=
  (fromBlocks U 0 0 (1 : Matrix (Fin (M - N)) (Fin (M - N)) α)).submatrix
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))).symm
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))).symm

private theorem finSumFinSub_symm_apply_of_lt (h : N ≤ M) {i : Fin M} (hi : (i : ℕ) < N) :
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))).symm i = Sum.inl ⟨i, hi⟩ :=
  (Equiv.symm_apply_eq _).2 (Fin.ext (by simp))

private theorem finSumFinSub_symm_apply_of_le (h : N ≤ M) {i : Fin M} (hi : N ≤ (i : ℕ)) :
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))).symm i =
      Sum.inr ⟨i - N, by omega⟩ :=
  (Equiv.symm_apply_eq _).2 (Fin.ext (by simp; omega))

/-- The entries of `[B; 0]`. -/
theorem padRows_apply [Zero α] (B : Matrix (Fin N) n' α) (h : N ≤ M) (i : Fin M) (j : n') :
    padRows B h i j = if hi : (i : ℕ) < N then B ⟨i, hi⟩ j else 0 := by
  rw [padRows, submatrix_apply, id]
  split_ifs with hi
  · rw [finSumFinSub_symm_apply_of_lt h hi, fromRows_apply_inl]
  · rw [finSumFinSub_symm_apply_of_le h (not_lt.1 hi), fromRows_apply_inr, zero_apply]

/-- `Matrix.padRows` is a right inverse of `Matrix.firstRows`. -/
@[simp]
theorem firstRows_padRows [Zero α] (B : Matrix (Fin N) n' α) (h : N ≤ M) :
    firstRows (padRows B h) h = B := by
  ext i j
  simp [padRows_apply]

/-- A matrix whose rows from the `N`-th on vanish is `[B; 0]` of its first `N` rows. -/
theorem padRows_firstRows [Zero α] {R : Matrix (Fin M) n' α} (h : N ≤ M)
    (hR : ∀ (i : Fin M) (j : n'), N ≤ (i : ℕ) → R i j = 0) : padRows (firstRows R h) h = R := by
  ext i j
  rw [padRows_apply]
  split_ifs with hi
  · rfl
  · exact (hR i j (not_lt.1 hi)).symm

/-- `[B; 0] C = [B C; 0]`. -/
theorem padRows_mul [Fintype n'] [NonUnitalNonAssocSemiring α] {p : Type*}
    (B : Matrix (Fin N) n' α) (C : Matrix n' p α) (h : N ≤ M) :
    padRows B h * C = padRows (B * C) h := by
  ext i j
  rw [mul_apply, padRows_apply]
  simp_rw [padRows_apply]
  split_ifs with hi
  · simp [mul_apply]
  · simp

/-- `diag(U, I) [B; 0] = [U B; 0]`. -/
theorem padOne_mul_padRows [Semiring α] (U : Matrix (Fin N) (Fin N) α)
    (B : Matrix (Fin N) n' α) (h : N ≤ M) : padOne U h * padRows B h = padRows (U * B) h := by
  rw [padOne, padRows, padRows, submatrix_mul_equiv, fromBlocks_mul_fromRows]
  simp

/-- `diag(U, I)ᴴ = diag(Uᴴ, I)`. -/
theorem conjTranspose_padOne [NonAssocSemiring α] [StarRing α] (U : Matrix (Fin N) (Fin N) α)
    (h : N ≤ M) : (padOne U h)ᴴ = padOne Uᴴ h := by
  rw [padOne, padOne, conjTranspose_submatrix, fromBlocks_conjTranspose, conjTranspose_zero,
    conjTranspose_zero, conjTranspose_one]

/-- `diag(U, I)` is unitary when `U` is. -/
theorem padOne_mem_unitaryGroup [CommRing α] [StarRing α] {U : Matrix (Fin N) (Fin N) α}
    (hU : U ∈ unitaryGroup (Fin N) α) (h : N ≤ M) : padOne U h ∈ unitaryGroup (Fin M) α := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_padOne, padOne, padOne,
    submatrix_mul_equiv, fromBlocks_multiply, ← star_eq_conjTranspose,
    mem_unitaryGroup_iff'.1 hU]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    fromBlocks_one]
  exact submatrix_one_equiv _

end Pad

/-! ### The bidiagonalization as a named factorization -/

section Factorization

variable {M N : ℕ}

/-- **An orthogonal bidiagonalization** `Uᴴ A V = B` of a rectangular matrix
([golub2013matrix] §5.4.8, (5.4.13)): `U`, `V` unitary and `B` upper bidiagonal. The specification
of Householder bidiagonalization and of the `R`-bidiagonalization. -/
structure IsBidiagonalization (A : Matrix (Fin M) (Fin N) 𝕜) (U : Matrix (Fin M) (Fin M) 𝕜)
    (V : Matrix (Fin N) (Fin N) 𝕜) (B : Matrix (Fin M) (Fin N) 𝕜) : Prop where
  /-- The left factor is unitary. -/
  left_mem_unitaryGroup : U ∈ unitaryGroup (Fin M) 𝕜
  /-- The right factor is unitary. -/
  right_mem_unitaryGroup : V ∈ unitaryGroup (Fin N) 𝕜
  /-- The two-sided transformation of `A` is `B`. -/
  conj_eq : Uᴴ * A * V = B
  /-- The transformed matrix is upper bidiagonal. -/
  isUpperBidiagonalRect : B.IsUpperBidiagonalRect

/-- **Every rectangular matrix has an orthogonal bidiagonalization** ([golub2013matrix] (5.4.13)):
`Matrix.exists_unitary_mul_mul_unitary_apply_eq_zero` repackaged. -/
theorem exists_isBidiagonalization (A : Matrix (Fin M) (Fin N) 𝕜) :
    ∃ U V B, IsBidiagonalization A U V B := by
  obtain ⟨U, hU, V, hV, hB⟩ := exists_unitary_mul_mul_unitary_apply_eq_zero A
  exact ⟨U, V, _, hU, hV, rfl, fun i j h1 h2 => hB i j (Ne.symm h1) (Ne.symm h2)⟩

/-- A padded upper bidiagonal matrix is upper bidiagonal. -/
theorem IsUpperBidiagonalRect.padRows {R : Type*} [Zero R] {B : Matrix (Fin N) (Fin N) R}
    (hB : B.IsUpperBidiagonalRect) (h : N ≤ M) : (padRows B h).IsUpperBidiagonalRect := by
  intro i j h1 h2
  rw [padRows_apply]
  split_ifs with hi
  · exact hB _ j h1 h2
  · rfl

/-- **`R`-bidiagonalization** ([golub2013matrix] §5.4.9; Chan 1982): for `N ≤ M`, a QR
factorization `A = Q R` followed by a bidiagonalization `U_Rᴴ R₁ V = B₁` of the square top block
`R₁` of `R` bidiagonalizes `A` as `(Q diag(U_R, I))ᴴ A V = [B₁; 0]`. -/
theorem IsBidiagonalization.of_isQR (hNM : N ≤ M) {A : Matrix (Fin M) (Fin N) 𝕜}
    {Q : Matrix (Fin M) (Fin M) 𝕜} {R : Matrix (Fin M) (Fin N) 𝕜} (hQR : IsQR A Q R)
    {UR V B₁ : Matrix (Fin N) (Fin N) 𝕜} (hB : IsBidiagonalization (firstRows R hNM) UR V B₁) :
    IsBidiagonalization A (Q * padOne UR hNM) V (padRows B₁ hNM) where
  left_mem_unitaryGroup :=
    mul_mem hQR.mem_unitaryGroup (padOne_mem_unitaryGroup hB.left_mem_unitaryGroup hNM)
  right_mem_unitaryGroup := hB.right_mem_unitaryGroup
  conj_eq := by
    have hA : Qᴴ * A = R := by
      rw [← hQR.mul_eq, ← Matrix.mul_assoc, ← star_eq_conjTranspose,
        Unitary.star_mul_self_of_mem hQR.mem_unitaryGroup, Matrix.one_mul]
    rw [conjTranspose_mul, Matrix.mul_assoc _ Qᴴ, hA,
      ← padRows_firstRows hNM fun i j hi => hQR.apply_eq_zero_of_le hi j, conjTranspose_padOne,
      padOne_mul_padRows, padRows_mul, hB.conj_eq]
  isUpperBidiagonalRect := hB.isUpperBidiagonalRect.padRows hNM

/-- "The bidiagonalization of `A` is related to the tridiagonalization of `Aᴴ A`"
([golub2013matrix] §5.4.8, §8.3.1): `Vᴴ (Aᴴ A) V = Bᴴ B`, and `Bᴴ B` is tridiagonal. -/
theorem IsBidiagonalization.isTridiagonal_conjTranspose_mul_self {A : Matrix (Fin M) (Fin N) 𝕜}
    {U : Matrix (Fin M) (Fin M) 𝕜} {V : Matrix (Fin N) (Fin N) 𝕜} {B : Matrix (Fin M) (Fin N) 𝕜}
    (hB : IsBidiagonalization A U V B) :
    Vᴴ * (Aᴴ * A) * V = Bᴴ * B ∧ (Bᴴ * B).IsTridiagonal := by
  refine ⟨?_, hB.isUpperBidiagonalRect.isTridiagonal_conjTranspose_mul_self⟩
  have hU : U * Uᴴ = 1 := by
    rw [← star_eq_conjTranspose, Unitary.mul_star_self_of_mem hB.left_mem_unitaryGroup]
  rw [← hB.conj_eq, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U, hU, Matrix.one_mul]

end Factorization

end Matrix
