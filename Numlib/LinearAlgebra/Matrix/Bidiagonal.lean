/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv

/-!
# Orthogonal bidiagonalization

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. Every $M \times N$ matrix $A$ over $\mathbb{K}$ is
carried by a unitary matrix on each side to an upper bidiagonal matrix: there are unitary $U$ and
$V$ such that $B = U^H A V$ has nonzero entries only on the diagonal and the first superdiagonal.
This is the **Golub–Kahan bidiagonalization**, introduced by Golub and Kahan in 1965
([golub2013matrix], §5.4.8 and (5.4.13); [quarteroni2000numerical], (5.57) and §5.8.3). It is the
first stage of the algorithms for the singular value decomposition, and it is the matrix form of the
Golub–Kahan–Lanczos process of `Numlib.Krylov.Bidiagonalization`.

The module also defines the rectangular upper and lower bidiagonal shapes, and it names the
factorization $U^H A V = B$ as a specification. For $N \le M$, the $R$-bidiagonalization of
[golub2013matrix], §5.4.9, first computes a QR factorization $A = QR$ and then bidiagonalizes the
square top block of $R$. The bidiagonalization of $A$ is related to the tridiagonalization of
$A^H A$: if $U^H A V = B$, then $V^H (A^H A) V = B^H B$, and $B^H B$ is tridiagonal.

## Main definitions

* `Matrix.IsUpperBidiagonalRect`, `Matrix.IsLowerBidiagonalRect`: an $M \times N$ matrix is upper
  bidiagonal if $b_{ij} = 0$ unless $j = i$ or $j = i + 1$, and lower bidiagonal if $b_{ij} = 0$
  unless $i = j$ or $i = j + 1$.
* `Matrix.padRows`, `Matrix.padOne`: for $N \le M$, the $M$-row matrix
  $\begin{bmatrix} B \\ 0 \end{bmatrix}$ and the $M \times M$ matrix $\operatorname{diag}(U, I)$.
* `Matrix.IsBidiagonalization`: $U$ and $V$ are unitary, $U^H A V = B$, and $B$ is upper bidiagonal.

## Main results

* `Matrix.exists_unitary_mul_mul_unitary_apply_eq_zero`: for every $M \times N$ matrix $A$ there are
  unitary $U$, $V$ such that $(U^H A V)_{ij} = 0$ unless $j = i$ or $j = i + 1$.
* `Matrix.exists_unitary_mul_mul_unitary_isUpperBidiagonal`: for $N \le M$, the matrix $U^H A V$ is
  zero below row $N$, and its top $N \times N$ block is upper bidiagonal.
* `Matrix.isUpperBidiagonalRect_iff_hasBandwidthRect`: upper bidiagonal means lower bandwidth $0$
  and upper bandwidth $1$.
* `Matrix.isUpperBidiagonalRect_iff_isUpperBidiagonal`: on a square matrix, the rectangular upper
  bidiagonal shape is `Matrix.IsUpperBidiagonal`.
* `Matrix.exists_isBidiagonalization`: every rectangular matrix has an orthogonal bidiagonalization.
* `Matrix.IsBidiagonalization.of_isQR`: the $R$-bidiagonalization $(Q \operatorname{diag}(U_R, I))^H
  A V = \begin{bmatrix} B_1 \\ 0 \end{bmatrix}$.
* `Matrix.IsBidiagonalization.isTridiagonal_conjTranspose_mul_self`: $V^H (A^H A) V = B^H B$, and
  $B^H B$ is tridiagonal.

## Proof outline

Householder reflectors that act on the tail of a vector (`Matrix.householderTail` of
`Numlib.LinearAlgebra.Matrix.QR`) alternate on the left and on the right. At step $k$, a reflector
on the left with pivot $k$ clears column $k$ below the diagonal, and a reflector on the right with
pivot $k + 1$ clears row $k$ beyond the first superdiagonal. The axis of the right reflector
vanishes on the columns $0, \dots, k$, so the zeros that are already created stay zero.

## Implementation notes

* The square bidiagonal shapes `Matrix.IsUpperBidiagonal` and `Matrix.IsLowerBidiagonal` of
  `Numlib.LinearAlgebra.Matrix.Hessenberg` use the order on the index type. The statements here are
  on `Fin M × Fin N`, with the index difference taken in $\mathbb{N}$, as for the rectangular
  bandwidths of `Numlib.LinearAlgebra.Matrix.Band`. The lower shape is the shape of the
  $(k + 1) \times k$ matrix of the Golub–Kahan lower bidiagonalization ([golub2013matrix],
  (10.4.18)).
* The block matrices $\begin{bmatrix} B \\ 0 \end{bmatrix}$ and $\operatorname{diag}(U, I)$ of the
  $R$-bidiagonalization are `Matrix.padRows` and `Matrix.padOne`. They are defined through
  `Matrix.fromRows` and `Matrix.fromBlocks`, reindexed along `Matrix.blockEquiv : Fin N ⊕ Fin (M -
  N) ≃ Fin M` of `Numlib.LinearAlgebra.Matrix.Block`, so that the block product rules of Mathlib
  apply. `Matrix.padRows` is a right inverse of `Matrix.firstRows`.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The Golub–Kahan bidiagonalization -/

section Bidiagonal

variable {M N : ℕ}

/-- The left half-step of the bidiagonalization: a unitary Hermitian reflector clears column $k$
below the diagonal and keeps the zeros of the rows before $k$ and of the columns before $k$. -/
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

/-- The right half-step of the bidiagonalization: a unitary reflector clears row $k$ beyond the
first superdiagonal and keeps the zeros of the rows before $k$ and of the columns $0, \dots, k$. -/
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

/-- **The Golub–Kahan bidiagonalization**, entrywise. Let $A$ be an $M \times N$ matrix over
$\mathbb{K}$. Then there are unitary matrices $U$ of order $M$ and $V$ of order $N$ such that
$$(U^H A V)_{ij} = 0 \quad \text{whenever } j \ne i \text{ and } j \ne i + 1.$$
This is (5.57) of [quarteroni2000numerical] and §5.4.8 of [golub2013matrix].

The indices are natural numbers from $0$. The proof alternates tail reflectors on the left
(column $k$, pivot $k$) and on the right (row $k$, pivot $k + 1$). The axis of the right
reflector vanishes on the columns $0, \dots, k$, so the zeros already created stay zero. -/
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
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
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
      · exact Or.inl (by omega)
      · exact Or.inr hj
    obtain ⟨W, hWu, hWB⟩ := bidiag_right_step (P * (Uᴴ * A * V)) hkM hPB
    refine ⟨U * P, mul_mem hU hPu, V * W, mul_mem hV hWu, fun i j hij hne1 hne2 => ?_⟩
    rw [← Matrix.mul_assoc, hUP]
    exact hWB i j hij hne1 hne2

/-- **The Golub–Kahan bidiagonalization.** Let $A$ be an $M \times N$ matrix over $\mathbb{K}$ with
$N \le M$. Then there are unitary matrices $U$ of order $M$ and $V$ of order $N$ such that
$$U^H A V = \begin{bmatrix} B \\ 0 \end{bmatrix},$$
where the rows of $U^H A V$ from row $N$ on are zero and the top $N \times N$ block $B$ is upper
bidiagonal. This is (5.57) of [quarteroni2000numerical] and §5.4.8 of [golub2013matrix].

This is the first phase of the Golub–Kahan–Reinsch computation of the singular value
decomposition. The top block is `(Uᴴ * A * V).submatrix (Fin.castLE h) id`, and upper bidiagonal
means `Matrix.IsUpperBidiagonal`. -/
theorem exists_unitary_mul_mul_unitary_isUpperBidiagonal (h : N ≤ M)
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
  · exact hB _ _ (by simp; omega) (by simp; omega)
  · exact hB _ _ (by simp; omega) (by simp; omega)

end Bidiagonal

/-! ### Rectangular bidiagonal shapes -/

section Shapes

variable {R : Type*} [Zero R] {M N : ℕ}

/-- An $M \times N$ matrix $B$ is **upper bidiagonal** if its only nonzero entries lie on the
diagonal and the first superdiagonal: $b_{ij} = 0$ whenever $j \ne i$ and $j \ne i + 1$, with
natural-number indices.

For $M \ge N$ this is the shape of (5.4.13) of [golub2013matrix]; the rows from row $N$ on are
then zero automatically. For $M < N$ the columns from column $M + 1$ on are zero, and the entry
$b_{M-1, M}$ can be nonzero, so the matrix is $\begin{bmatrix} B' & 0 \end{bmatrix}$ with an
upper bidiagonal $M \times (M + 1)$ block $B'$. On a square matrix it is
`Matrix.IsUpperBidiagonal` (see `Matrix.isUpperBidiagonalRect_iff_isUpperBidiagonal`). -/
def IsUpperBidiagonalRect (B : Matrix (Fin M) (Fin N) R) : Prop :=
  ∀ (i : Fin M) (j : Fin N), (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → B i j = 0

/-- An $M \times N$ matrix $B$ is **lower bidiagonal** if its only nonzero entries lie on the
diagonal and the first subdiagonal: $b_{ij} = 0$ whenever $i \ne j$ and $i \ne j + 1$, with
natural-number indices.

This is the shape of the $(k + 1) \times k$ matrix of the Golub–Kahan lower bidiagonalization
([golub2013matrix], (10.4.18)). It is the transpose of the upper shape (see
`Matrix.isUpperBidiagonalRect_transpose_iff`). -/
def IsLowerBidiagonalRect (B : Matrix (Fin M) (Fin N) R) : Prop :=
  ∀ (i : Fin M) (j : Fin N), (i : ℕ) ≠ j → (i : ℕ) ≠ j + 1 → B i j = 0

/-- For an $M \times N$ matrix $B$, the transpose $B^T$ is upper bidiagonal if and only if $B$ is
lower bidiagonal. -/
theorem isUpperBidiagonalRect_transpose_iff {B : Matrix (Fin M) (Fin N) R} :
    Bᵀ.IsUpperBidiagonalRect ↔ B.IsLowerBidiagonalRect :=
  forall_comm

/-- For an $M \times N$ matrix $B$, the transpose $B^T$ is lower bidiagonal if and only if $B$ is
upper bidiagonal. -/
theorem isLowerBidiagonalRect_transpose_iff {B : Matrix (Fin M) (Fin N) R} :
    Bᵀ.IsLowerBidiagonalRect ↔ B.IsUpperBidiagonalRect :=
  forall_comm

/-- An $M \times N$ matrix is upper bidiagonal if and only if it has lower bandwidth $0$ and upper
bandwidth $1$ ([golub2013matrix], Table 1.2.1). -/
theorem isUpperBidiagonalRect_iff_hasBandwidthRect {B : Matrix (Fin M) (Fin N) R} :
    B.IsUpperBidiagonalRect ↔ B.HasLowerBandwidthRect 0 ∧ B.HasUpperBandwidthRect 1 := by
  refine ⟨fun h => ⟨fun i j hij => h i j (by omega) (by omega),
    fun i j hij => h i j (by omega) (by omega)⟩, fun h i j h1 h2 => ?_⟩
  rcases lt_or_gt_of_ne h1 with hj | hj
  · exact h.1 i j (by omega)
  · exact h.2 i j (by omega)

/-- An $M \times N$ matrix is lower bidiagonal if and only if it has lower bandwidth $1$ and upper
bandwidth $0$. -/
theorem isLowerBidiagonalRect_iff_hasBandwidthRect {B : Matrix (Fin M) (Fin N) R} :
    B.IsLowerBidiagonalRect ↔ B.HasLowerBandwidthRect 1 ∧ B.HasUpperBandwidthRect 0 := by
  rw [← isUpperBidiagonalRect_transpose_iff, isUpperBidiagonalRect_iff_hasBandwidthRect,
    hasLowerBandwidthRect_transpose_iff, hasUpperBandwidthRect_transpose_iff, and_comm]

/-- For a square matrix indexed by $\{0, \dots, N - 1\}$, the rectangular upper bidiagonal shape
`Matrix.IsUpperBidiagonalRect` is equivalent to the order-theoretic shape
`Matrix.IsUpperBidiagonal` of `Numlib.LinearAlgebra.Matrix.Hessenberg`. -/
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

/-- For a square matrix indexed by $\{0, \dots, N - 1\}$, the rectangular lower bidiagonal shape
`Matrix.IsLowerBidiagonalRect` is equivalent to the order-theoretic shape
`Matrix.IsLowerBidiagonal` of `Numlib.LinearAlgebra.Matrix.Hessenberg`. -/
theorem isLowerBidiagonalRect_iff_isLowerBidiagonal {B : Matrix (Fin N) (Fin N) R} :
    B.IsLowerBidiagonalRect ↔ B.IsLowerBidiagonal := by
  rw [← isUpperBidiagonalRect_transpose_iff, isUpperBidiagonalRect_iff_isUpperBidiagonal,
    isUpperBidiagonal_transpose_iff]

/-- If an $M \times N$ matrix $B$ over a semiring with an involution is upper bidiagonal, then
$B^H B$ is tridiagonal.

The entry $(B^H B)_{ij}$ is the sum of $\overline{b_{ki}} b_{kj}$ over the rows $k$ with
$i, j \in \{k, k + 1\}$. -/
theorem IsUpperBidiagonalRect.isTridiagonal_conjTranspose_mul_self {R : Type*}
    [NonUnitalNonAssocSemiring R] [StarAddMonoid R] {B : Matrix (Fin M) (Fin N) R}
    (hB : B.IsUpperBidiagonalRect) : (Bᴴ * B).IsTridiagonal := by
  intro i j hij
  have hij' : (j : ℕ) + 1 < i ∨ (i : ℕ) + 1 < j := by
    rcases hij with ⟨l, h1, h2⟩ | ⟨l, h1, h2⟩ <;> rw [Fin.lt_def] at h1 h2 <;> omega
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [conjTranspose_apply]
  by_cases hk : (i : ℕ) = k ∨ (i : ℕ) = k + 1
  · rw [hB k j (by omega) (by omega), mul_zero]
  · rw [hB k i (by omega) (by omega), star_zero, zero_mul]

end Shapes

/-! ### Padding a matrix to more rows -/

section Pad

variable {α : Type*} {M N : ℕ} {n' : Type*}

/-- For $N \le M$ and an $N \times n'$ matrix $B$, `Matrix.padRows B h` is the $M \times n'$ matrix
$$\begin{bmatrix} B \\ 0 \end{bmatrix}$$
that stacks $B$ on $M - N$ zero rows. It is a right inverse of `Matrix.firstRows` (see
`Matrix.firstRows_padRows`). -/
def padRows [Zero α] (B : Matrix (Fin N) n' α) (h : N ≤ M) : Matrix (Fin M) n' α :=
  (fromRows B (0 : Matrix (Fin (M - N)) n' α)).submatrix (blockEquiv h).symm id

/-- For $N \le M$ and a square matrix $U$ of order $N$, `Matrix.padOne U h` is the square matrix of
order $M$
$$\operatorname{diag}(U, I) = \begin{bmatrix} U & 0 \\ 0 & I_{M - N} \end{bmatrix}.$$
It is the matrix $\operatorname{diag}(U_R, I_{m-n})$ of [golub2013matrix], §5.4.9. -/
def padOne [Zero α] [One α] (U : Matrix (Fin N) (Fin N) α) (h : N ≤ M) :
    Matrix (Fin M) (Fin M) α :=
  (fromBlocks U 0 0 (1 : Matrix (Fin (M - N)) (Fin (M - N)) α)).submatrix (blockEquiv h).symm
    (blockEquiv h).symm

/-- The entries of $\begin{bmatrix} B \\ 0 \end{bmatrix}$: the entry in row $i$ and column $j$ is
$b_{ij}$ if $i < N$ and $0$ otherwise. -/
theorem padRows_apply [Zero α] (B : Matrix (Fin N) n' α) (h : N ≤ M) (i : Fin M) (j : n') :
    padRows B h i j = if hi : (i : ℕ) < N then B ⟨i, hi⟩ j else 0 := by
  rw [padRows, submatrix_apply, id]
  split_ifs with hi
  · rw [blockEquiv_symm_apply_of_lt h hi, fromRows_apply_inl]
  · rw [blockEquiv_symm_apply_of_le h (not_lt.1 hi), fromRows_apply_inr, Matrix.zero_apply]

/-- The first $N$ rows of $\begin{bmatrix} B \\ 0 \end{bmatrix}$ form $B$: `Matrix.padRows` is a
right inverse of `Matrix.firstRows`. -/
@[simp]
theorem firstRows_padRows [Zero α] (B : Matrix (Fin N) n' α) (h : N ≤ M) :
    firstRows (padRows B h) h = B := by
  ext i j
  simp [padRows_apply]

/-- For $N \le M$, the matrix $\begin{bmatrix} B \\ 0 \end{bmatrix}$ is the product of the first $N$
columns of the identity matrix of order $M$ with $B$. -/
theorem padRows_eq_mul [NonAssocSemiring α] (B : Matrix (Fin N) n' α)
    (h : N ≤ M) : padRows B h = (1 : Matrix (Fin M) (Fin M) α).submatrix id (Fin.castLE h) * B := by
  ext i j
  rw [padRows_apply, Matrix.mul_apply]
  simp only [submatrix_apply, id_eq, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  split_ifs with hi
  · rw [Finset.sum_eq_single ⟨i, hi⟩]
    · simp
    · exact fun k _ hk =>
        ite_eq_right fun (e : i = Fin.castLE h k) => hk (Fin.ext (congrArg Fin.val e).symm)
    · simp
  · exact (Finset.sum_eq_zero fun k _ =>
      ite_eq_right fun e => hi (by rw [e]; exact k.isLt)).symm

/-- Let $N \le M$, and let $R$ be a matrix with $M$ rows whose rows from row $N$ on are zero. Then
$R = \begin{bmatrix} R_1 \\ 0 \end{bmatrix}$, where $R_1$ consists of the first $N$ rows of $R$. -/
theorem padRows_firstRows [Zero α] {R : Matrix (Fin M) n' α} (h : N ≤ M)
    (hR : ∀ (i : Fin M) (j : n'), N ≤ (i : ℕ) → R i j = 0) : padRows (firstRows R h) h = R := by
  ext i j
  rw [padRows_apply]
  split_ifs with hi
  · rfl
  · exact (hR i j (not_lt.1 hi)).symm

/-- For $N \le M$, $\begin{bmatrix} B \\ 0 \end{bmatrix} C = \begin{bmatrix} BC \\ 0 \end{bmatrix}$.
-/
theorem padRows_mul [Fintype n'] [NonUnitalNonAssocSemiring α] {p : Type*}
    (B : Matrix (Fin N) n' α) (C : Matrix n' p α) (h : N ≤ M) :
    padRows B h * C = padRows (B * C) h := by
  ext i j
  rw [Matrix.mul_apply, padRows_apply]
  simp_rw [padRows_apply]
  split_ifs with hi
  · simp [Matrix.mul_apply]
  · simp

/-- For $N \le M$, $\operatorname{diag}(U, I) \begin{bmatrix} B \\ 0 \end{bmatrix} = \begin{bmatrix}
UB \\ 0 \end{bmatrix}$. -/
theorem padOne_mul_padRows [Semiring α] (U : Matrix (Fin N) (Fin N) α)
    (B : Matrix (Fin N) n' α) (h : N ≤ M) : padOne U h * padRows B h = padRows (U * B) h := by
  rw [padOne, padRows, padRows, submatrix_mul_equiv, fromBlocks_mul_fromRows]
  simp

/-- For $N \le M$, $\operatorname{diag}(U, I)^H = \operatorname{diag}(U^H, I)$. -/
theorem conjTranspose_padOne [NonAssocSemiring α] [StarRing α] (U : Matrix (Fin N) (Fin N) α)
    (h : N ≤ M) : (padOne U h)ᴴ = padOne Uᴴ h := by
  rw [padOne, padOne, conjTranspose_submatrix, fromBlocks_conjTranspose, conjTranspose_zero,
    conjTranspose_zero, conjTranspose_one]

/-- For $N \le M$, if $U$ is unitary, then $\operatorname{diag}(U, I)$ is unitary. -/
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

/-- An **orthogonal bidiagonalization** of an $M \times N$ matrix $A$ over $\mathbb{K}$ consists of
unitary matrices $U$ of order $M$ and $V$ of order $N$ and an upper bidiagonal $M \times N$
matrix $B$ with
$$U^H A V = B.$$
See §5.4.8 and (5.4.13) of [golub2013matrix].

The structure extends the two-sided unitary equivalence `Matrix.IsUnitaryEquiv A U B V`, with
the fields `mem_unitaryGroup_left`, `mem_unitaryGroup_right` and `star_mul_mul`. It is the
specification of Householder bidiagonalization and of the $R$-bidiagonalization. -/
structure IsBidiagonalization (A : Matrix (Fin M) (Fin N) 𝕜) (U : Matrix (Fin M) (Fin M) 𝕜)
    (V : Matrix (Fin N) (Fin N) 𝕜) (B : Matrix (Fin M) (Fin N) 𝕜) : Prop
    extends IsUnitaryEquiv A U B V where
  /-- The matrix $B$ is upper bidiagonal. -/
  isUpperBidiagonalRect : B.IsUpperBidiagonalRect

/-- **Every rectangular matrix has an orthogonal bidiagonalization.** For every $M \times N$ matrix
$A$ over $\mathbb{K}$ there are $U$, $V$ and $B$ that form an orthogonal bidiagonalization
$U^H A V = B$ ([golub2013matrix], (5.4.13)).

This is `Matrix.exists_unitary_mul_mul_unitary_apply_eq_zero` in the form of
`Matrix.IsBidiagonalization`. -/
theorem exists_isBidiagonalization (A : Matrix (Fin M) (Fin N) 𝕜) :
    ∃ U V B, IsBidiagonalization A U V B := by
  obtain ⟨U, hU, V, hV, hB⟩ := exists_unitary_mul_mul_unitary_apply_eq_zero A
  exact ⟨U, V, _, ⟨hU, hV, rfl⟩, fun i j h1 h2 => hB i j (Ne.symm h1) (Ne.symm h2)⟩

/-- For $N \le M$, if a square matrix $B$ of order $N$ is upper bidiagonal, then
$\begin{bmatrix} B \\ 0 \end{bmatrix}$ is upper bidiagonal. -/
theorem IsUpperBidiagonalRect.padRows {R : Type*} [Zero R] {B : Matrix (Fin N) (Fin N) R}
    (hB : B.IsUpperBidiagonalRect) (h : N ≤ M) : (padRows B h).IsUpperBidiagonalRect := by
  intro i j h1 h2
  rw [padRows_apply]
  split_ifs with hi
  · exact hB _ j h1 h2
  · rfl

/-- **$R$-bidiagonalization** ([golub2013matrix], §5.4.9). Let $A$ be an $M \times N$ matrix over
$\mathbb{K}$ with $N \le M$, and let $A = QR$ be a QR factorization, with $Q$ unitary and $R$
upper trapezoidal. Let $R_1$ be the top $N \times N$ block of $R$, and let $U_R^H R_1 V = B_1$
be an orthogonal bidiagonalization of $R_1$. Then
$$\bigl(Q \operatorname{diag}(U_R, I)\bigr)^H A V = \begin{bmatrix} B_1 \\ 0 \end{bmatrix}$$
is an orthogonal bidiagonalization of $A$.

This method is due to Chan (1982). The QR factorization is `Matrix.IsQR A Q R`, the block $R_1$
is `Matrix.firstRows R hNM`, and $\operatorname{diag}(U_R, I)$ and
$\begin{bmatrix} B_1 \\ 0 \end{bmatrix}$ are `Matrix.padOne` and `Matrix.padRows`. -/
theorem IsBidiagonalization.of_isQR (hNM : N ≤ M) {A : Matrix (Fin M) (Fin N) 𝕜}
    {Q : Matrix (Fin M) (Fin M) 𝕜} {R : Matrix (Fin M) (Fin N) 𝕜} (hQR : IsQR A Q R)
    {UR V B₁ : Matrix (Fin N) (Fin N) 𝕜} (hB : IsBidiagonalization (firstRows R hNM) UR V B₁) :
    IsBidiagonalization A (Q * padOne UR hNM) V (padRows B₁ hNM) where
  mem_unitaryGroup_left :=
    mul_mem hQR.mem_unitaryGroup (padOne_mem_unitaryGroup hB.mem_unitaryGroup_left hNM)
  mem_unitaryGroup_right := hB.mem_unitaryGroup_right
  star_mul_mul := by
    have hA : Qᴴ * A = R := by
      rw [← hQR.mul_eq, ← Matrix.mul_assoc, ← star_eq_conjTranspose,
        Unitary.star_mul_self_of_mem hQR.mem_unitaryGroup, Matrix.one_mul]
    rw [star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc _ Qᴴ, hA,
      ← padRows_firstRows hNM fun i j hi => hQR.apply_eq_zero_of_le hi j, conjTranspose_padOne,
      padOne_mul_padRows, padRows_mul, hB.conjTranspose_mul_mul]
  isUpperBidiagonalRect := hB.isUpperBidiagonalRect.padRows hNM

/-- The bidiagonalization of $A$ is related to the tridiagonalization of $A^H A$ ([golub2013matrix],
§5.4.8 and §8.3.1). If $U^H A V = B$ is an orthogonal bidiagonalization of an $M \times N$
matrix $A$, then
$$V^H (A^H A) V = B^H B,$$
and $B^H B$ is tridiagonal. -/
theorem IsBidiagonalization.isTridiagonal_conjTranspose_mul_self {A : Matrix (Fin M) (Fin N) 𝕜}
    {U : Matrix (Fin M) (Fin M) 𝕜} {V : Matrix (Fin N) (Fin N) 𝕜} {B : Matrix (Fin M) (Fin N) 𝕜}
    (hB : IsBidiagonalization A U V B) :
    Vᴴ * (Aᴴ * A) * V = Bᴴ * B ∧ (Bᴴ * B).IsTridiagonal :=
  ⟨hB.conjTranspose_mul_self, hB.isUpperBidiagonalRect.isTridiagonal_conjTranspose_mul_self⟩

end Factorization

end Matrix
