/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Numlib.LinearAlgebra.Matrix.Band

/-!
# Hessenberg, tridiagonal and bidiagonal matrices

The named shapes of band width one, on a matrix indexed by a linearly ordered type.

## Main definitions

* `Matrix.IsUpperHessenberg`, `Matrix.IsTridiagonal`: zero below the first subdiagonal, and zero
  outside the three central diagonals. Both are stated over a bare `LinearOrder` on the index type,
  as "no index lies strictly between the two", which on `Fin n` is the usual condition on the
  difference of the indices (`Matrix.isUpperHessenberg_iff_fin`).
* `Matrix.IsUpperHessenbergRect`: the rectangular `(m + 1) × m` form of the same condition, as in
  the matrix `H̄ₘ` of the Arnoldi process; it is lower bandwidth `1` in the rectangular vocabulary
  of `Numlib/LinearAlgebra/Matrix/Band`
  (`Matrix.isUpperHessenbergRect_iff_hasLowerBandwidthRect_one`).
* `Matrix.IsUpperBidiagonal`, `Matrix.IsLowerBidiagonal`: the two bidiagonal shapes, the shape of
  the Golub–Kahan bidiagonalization and of the factors of a tridiagonal matrix.
* `Matrix.tridiagonalOf b d c`: the tridiagonal matrix `tridiag(b, d, c)` with the given
  subdiagonal, diagonal and superdiagonal, on `Fin (N + 1)`, with its three-term product formula
  `Matrix.tridiagonalOf_mulVec`.

## Main results

* The shapes in the band vocabulary of `Numlib/LinearAlgebra/Matrix/Band`: upper Hessenberg is
  lower bandwidth `1` (`Matrix.isUpperHessenberg_iff_hasLowerBandwidth_one`), tridiagonal is both
  bandwidths `1` (`Matrix.isTridiagonal_iff_hasBandwidth_one`), and the bidiagonal shapes have
  bandwidths `1` and `0` (`Matrix.IsLowerBidiagonal.hasBandwidth`); since products add bands, an
  upper triangular matrix times an upper Hessenberg one is upper Hessenberg
  (`Matrix.IsUpperTriangular.mul_isUpperHessenberg`), the `R Q` of the QR iteration.
* `Matrix.IsUpperHessenberg.isTridiagonal_of_isHermitian`: a Hermitian upper Hessenberg matrix is
  tridiagonal.

The triangular vocabulary (the triangular parts `Matrix.strictLower`, `Matrix.strictUpper`,
`Matrix.diagPart` and the unit triangular matrices) is in `Numlib/LinearAlgebra/Matrix/Triangular`,
the bandwidths in `Numlib/LinearAlgebra/Matrix/Band`, the block product rules in
`Numlib/LinearAlgebra/Matrix/Block`, and the rectangular bidiagonal shapes in
`Numlib/LinearAlgebra/Matrix/Bidiagonal`.
-/


namespace Matrix

variable {n R : Type*} [LinearOrder n]

/-- Upper Hessenberg: zero below the first subdiagonal. "Below the first subdiagonal" is spelled
as "some index lies strictly between the column and the row", which needs no arithmetic on the
index type and is the usual condition `j + 1 < i` on `Fin n`. -/
def IsUpperHessenberg [Zero R] (H : Matrix n n R) : Prop :=
  ∀ i j, (∃ k, j < k ∧ k < i) → H i j = 0

/-- Tridiagonal: zero outside the three central diagonals, that is, upper Hessenberg together with
its mirror image above the first superdiagonal. -/
def IsTridiagonal [Zero R] (T : Matrix n n R) : Prop :=
  ∀ i j, (∃ k, j < k ∧ k < i) ∨ (∃ k, i < k ∧ k < j) → T i j = 0

/-- A tridiagonal matrix is upper Hessenberg: tridiagonality is the Hessenberg condition together
with its mirror image above the first superdiagonal, so it is the stronger of the two. -/
theorem IsTridiagonal.isUpperHessenberg [Zero R] {T : Matrix n n R} (hT : T.IsTridiagonal) :
    T.IsUpperHessenberg := fun i j h => hT i j (Or.inl h)

/-- Rectangular upper Hessenberg (`(m+1) × m`, as in Arnoldi's `H̄_m`). -/
def IsUpperHessenbergRect [Zero R] {m : ℕ} (H : Matrix (Fin (m + 1)) (Fin m) R) : Prop :=
  ∀ (i : Fin (m + 1)) (j : Fin m), (j : ℕ) + 1 < (i : ℕ) → H i j = 0

/-- The two spellings of "rectangular upper Hessenberg" agree: the Arnoldi shape `H̄ₘ` is lower
bandwidth `1` in the rectangular vocabulary of [golub2013matrix] §1.2.1. -/
theorem isUpperHessenbergRect_iff_hasLowerBandwidthRect_one [Zero R] {m : ℕ}
    {H : Matrix (Fin (m + 1)) (Fin m) R} :
    H.IsUpperHessenbergRect ↔ H.HasLowerBandwidthRect 1 :=
  Iff.rfl

section Bidiagonal

variable [Zero R]

/-- Upper bidiagonal: zero off the diagonal and the first superdiagonal. As in
`Matrix.IsTridiagonal`, "on the first superdiagonal" is spelled as "no index lies strictly between
the row and the column". This is the shape of the Golub–Kahan bidiagonalization
([quarteroni2000numerical] (5.57)) and of the `U` factor of a tridiagonal matrix. -/
def IsUpperBidiagonal (B : Matrix n n R) : Prop :=
  ∀ i j, j < i ∨ (∃ k, i < k ∧ k < j) → B i j = 0

/-- Lower bidiagonal: zero off the diagonal and the first subdiagonal, the shape of the `L` factor
of a tridiagonal matrix. -/
def IsLowerBidiagonal (B : Matrix n n R) : Prop :=
  ∀ i j, i < j ∨ (∃ k, j < k ∧ k < i) → B i j = 0

/-- An upper bidiagonal matrix is upper triangular. -/
theorem IsUpperBidiagonal.isUpperTriangular {B : Matrix n n R} (hB : B.IsUpperBidiagonal) :
    B.IsUpperTriangular := fun i j h => hB i j (Or.inl h)

/-- An upper bidiagonal matrix is tridiagonal. -/
theorem IsUpperBidiagonal.isTridiagonal {B : Matrix n n R} (hB : B.IsUpperBidiagonal) :
    B.IsTridiagonal := fun i j h =>
  hB i j (h.imp_left fun ⟨_, hk⟩ => hk.1.trans hk.2)

/-- The transpose of an upper bidiagonal matrix is upper Hessenberg. -/
theorem IsUpperBidiagonal.transpose_isUpperHessenberg {B : Matrix n n R}
    (hB : B.IsUpperBidiagonal) : Bᵀ.IsUpperHessenberg := fun i j h => hB j i (Or.inr h)

/-- A lower bidiagonal matrix is lower triangular. -/
theorem IsLowerBidiagonal.isLowerTriangular {B : Matrix n n R} (hB : B.IsLowerBidiagonal) :
    B.IsLowerTriangular := fun i j h => hB i j (Or.inl h)

/-- A lower bidiagonal matrix is tridiagonal. -/
theorem IsLowerBidiagonal.isTridiagonal {B : Matrix n n R} (hB : B.IsLowerBidiagonal) :
    B.IsTridiagonal := fun i j h =>
  hB i j (h.symm.imp_left fun ⟨_, hk⟩ => hk.1.trans hk.2)

/-- A lower bidiagonal matrix is upper Hessenberg. -/
theorem IsLowerBidiagonal.isUpperHessenberg {B : Matrix n n R} (hB : B.IsLowerBidiagonal) :
    B.IsUpperHessenberg := hB.isTridiagonal.isUpperHessenberg

/-- Transposition exchanges the two bidiagonal shapes. -/
theorem isLowerBidiagonal_transpose_iff {B : Matrix n n R} :
    Bᵀ.IsLowerBidiagonal ↔ B.IsUpperBidiagonal :=
  ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩

/-- Transposition exchanges the two bidiagonal shapes. -/
theorem isUpperBidiagonal_transpose_iff {B : Matrix n n R} :
    Bᵀ.IsUpperBidiagonal ↔ B.IsLowerBidiagonal :=
  ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩

end Bidiagonal

section Hermitian

/-- A symmetric upper Hessenberg matrix is tridiagonal: an entry above the first superdiagonal is
the mirror image of one below the first subdiagonal, which is zero ([quarteroni2000numerical]
Remark 5.4). -/
theorem IsUpperHessenberg.isTridiagonal_of_isSymm [Zero R] {H : Matrix n n R}
    (hH : H.IsUpperHessenberg) (hs : H.IsSymm) : H.IsTridiagonal := fun i j h => by
  rcases h with h | h
  · exact hH i j h
  · rw [← hs.apply i j]
    exact hH j i h

/-- A Hermitian upper Hessenberg matrix is tridiagonal ([quarteroni2000numerical] Remark 5.4). -/
theorem IsUpperHessenberg.isTridiagonal_of_isHermitian [AddMonoid R] [StarAddMonoid R]
    {H : Matrix n n R} (hH : H.IsUpperHessenberg) (hs : H.IsHermitian) : H.IsTridiagonal :=
  fun i j h => by
  rcases h with h | h
  · exact hH i j h
  · rw [← hs.apply i j, hH j i h, star_zero]

end Hermitian

/-! ### The shapes as bands -/

section Bandwidth

variable [Fintype n] [Zero R] {A : Matrix n n R}

/-- Lower bandwidth `1` is the upper Hessenberg shape. -/
theorem isUpperHessenberg_iff_hasLowerBandwidth_one :
    A.IsUpperHessenberg ↔ A.HasLowerBandwidth 1 := by
  simp only [HasLowerBandwidth, one_lt_card_filter_le_lt_iff]
  rfl

/-- On `Fin N`, upper Hessenberg is the condition `A i j = 0` for `j + 1 < i`. -/
theorem isUpperHessenberg_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.IsUpperHessenberg ↔ ∀ i j : Fin N, (j : ℕ) + 1 < (i : ℕ) → A i j = 0 := by
  rw [isUpperHessenberg_iff_hasLowerBandwidth_one, hasLowerBandwidth_iff_fin]

/-- Tridiagonal means both bandwidths are `1` ([quarteroni2000numerical] §1.6.3). -/
theorem isTridiagonal_iff_hasBandwidth_one :
    A.IsTridiagonal ↔ A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth 1 := by
  simp only [HasLowerBandwidth, HasUpperBandwidth, one_lt_card_filter_le_lt_iff]
  exact ⟨fun h => ⟨fun i j hij => h i j (Or.inl hij), fun i j hij => h i j (Or.inr hij)⟩,
    fun h i j hij => hij.elim (h.1 i j) (h.2 i j)⟩

/-- A lower bidiagonal matrix has bandwidths `1` and `0`. -/
theorem IsLowerBidiagonal.hasBandwidth (hB : A.IsLowerBidiagonal) :
    A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth 0 :=
  ⟨(isTridiagonal_iff_hasBandwidth_one.1 hB.isTridiagonal).1,
    hasUpperBandwidth_zero_iff.2 hB.isLowerTriangular⟩

/-- An upper bidiagonal matrix has bandwidths `0` and `1`. -/
theorem IsUpperBidiagonal.hasBandwidth (hB : A.IsUpperBidiagonal) :
    A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth 1 :=
  ⟨hasLowerBandwidth_zero_iff.2 hB.isUpperTriangular,
    (isTridiagonal_iff_hasBandwidth_one.1 hB.isTridiagonal).2⟩

end Bandwidth

section Products

variable [Fintype n] [NonUnitalNonAssocSemiring R]

/-- An upper triangular matrix times an upper Hessenberg matrix is upper Hessenberg
([quarteroni2000numerical] §5.6.4, `R Q` in the QR iteration): bandwidths `0` and `1` add up to
`1`. -/
theorem IsUpperTriangular.mul_isUpperHessenberg {T H : Matrix n n R} (hT : T.IsUpperTriangular)
    (hH : H.IsUpperHessenberg) : (T * H).IsUpperHessenberg :=
  isUpperHessenberg_iff_hasLowerBandwidth_one.2 <| by
    simpa using (hasLowerBandwidth_zero_iff.2 hT).mul
      (isUpperHessenberg_iff_hasLowerBandwidth_one.1 hH)

/-- An upper Hessenberg matrix times an upper triangular matrix is upper Hessenberg
([quarteroni2000numerical] §5.6.3, `Q = H R⁻¹`). -/
theorem IsUpperHessenberg.mul_isUpperTriangular {H T : Matrix n n R} (hH : H.IsUpperHessenberg)
    (hT : T.IsUpperTriangular) : (H * T).IsUpperHessenberg :=
  isUpperHessenberg_iff_hasLowerBandwidth_one.2 <| by
    simpa using (isUpperHessenberg_iff_hasLowerBandwidth_one.1 hH).mul
      (hasLowerBandwidth_zero_iff.2 hT)

end Products

section Shift

variable [DecidableEq n]

/-- Adding a multiple of the identity preserves upper Hessenberg form (the `+ μ I` of a shifted
QR step, [quarteroni2000numerical] (5.52)). -/
theorem IsUpperHessenberg.add_smul_one [NonAssocSemiring R] {H : Matrix n n R}
    (hH : H.IsUpperHessenberg) (μ : R) : (H + μ • 1).IsUpperHessenberg := by
  intro i j h
  obtain ⟨k, hjk, hki⟩ := h
  have hij : i ≠ j := ne_of_gt (lt_trans hjk hki)
  rw [Matrix.add_apply, Matrix.smul_apply, one_apply_ne hij, smul_zero, add_zero]
  exact hH i j ⟨k, hjk, hki⟩

/-- Subtracting a multiple of the identity preserves upper Hessenberg form (the `- μ I` of a
shifted QR step, [quarteroni2000numerical] (5.52)). -/
theorem IsUpperHessenberg.sub_smul_one [NonAssocRing R] {H : Matrix n n R}
    (hH : H.IsUpperHessenberg) (μ : R) : (H - μ • 1).IsUpperHessenberg := by
  intro i j h
  obtain ⟨k, hjk, hki⟩ := h
  have hij : i ≠ j := ne_of_gt (lt_trans hjk hki)
  rw [Matrix.sub_apply, Matrix.smul_apply, one_apply_ne hij, smul_zero, sub_zero]
  exact hH i j ⟨k, hjk, hki⟩

end Shift

section TridiagonalOf

open Finset

variable {S : Type*} [Zero R] {N : ℕ}

/-- The tridiagonal matrix `tridiag(b, d, c)` of [quarteroni2000numerical] §1.6.3: `d` on the
diagonal, `b` on the subdiagonal (`b i` at `(i + 1, i)`) and `c` on the superdiagonal (`c i` at
`(i, i + 1)`), zero elsewhere. The book's `b₁, …, b_{n-1}`, `d₁, …, d_n` are `0`-indexed here, on
`Fin (N + 1)`. -/
def tridiagonalOf (b : Fin N → R) (d : Fin (N + 1) → R) (c : Fin N → R) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then d i
    else if h : (i : ℕ) = j + 1 then b ⟨j, by omega⟩
    else if h' : (j : ℕ) = i + 1 then c ⟨i, by omega⟩
    else 0

variable (b : Fin N → R) (d : Fin (N + 1) → R) (c : Fin N → R)

/-- The diagonal of `tridiag(b, d, c)`. -/
@[simp]
theorem tridiagonalOf_apply_self (i : Fin (N + 1)) : tridiagonalOf b d c i i = d i := by
  simp [tridiagonalOf]

/-- The subdiagonal of `tridiag(b, d, c)`. -/
@[simp]
theorem tridiagonalOf_apply_succ_castSucc (i : Fin N) :
    tridiagonalOf b d c i.succ i.castSucc = b i := by
  simp [tridiagonalOf]

/-- The superdiagonal of `tridiag(b, d, c)`. -/
@[simp]
theorem tridiagonalOf_apply_castSucc_succ (i : Fin N) :
    tridiagonalOf b d c i.castSucc i.succ = c i := by
  have h : (i : ℕ) ≠ i + 1 + 1 := by omega
  simp [tridiagonalOf, h]

/-- Away from the three central diagonals, `tridiag(b, d, c)` vanishes. -/
theorem tridiagonalOf_apply_of_ne {i j : Fin (N + 1)} (hij : (i : ℕ) ≠ j)
    (h₁ : (i : ℕ) ≠ j + 1) (h₂ : (j : ℕ) ≠ i + 1) : tridiagonalOf b d c i j = 0 := by
  simp [tridiagonalOf, hij, h₁, h₂]

/-- `tridiag(b, d, c)` is tridiagonal. -/
theorem isTridiagonal_tridiagonalOf : (tridiagonalOf b d c).IsTridiagonal := by
  intro i j h
  refine tridiagonalOf_apply_of_ne b d c ?_ ?_ ?_ <;>
    rcases h with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp only [Fin.lt_def] at hk <;> omega

/-- Transposition exchanges the two off-diagonals. -/
theorem tridiagonalOf_transpose : (tridiagonalOf b d c)ᵀ = tridiagonalOf c d b := by
  ext i j
  simp only [transpose_apply, tridiagonalOf, of_apply]
  split_ifs <;> first | rfl | omega | exact congrArg d (Fin.ext (by omega))

/-- Each term of `(tridiag(b, d, c) * x) i`, split into its three possible contributions. -/
theorem tridiagonalOf_apply_mul_eq [NonUnitalNonAssocSemiring S]
    (b : Fin N → S) (d : Fin (N + 1) → S) (c : Fin N → S) (x : Fin (N + 1) → S)
    (i j : Fin (N + 1)) :
    tridiagonalOf b d c i j * x j =
      (if j = i then d i * x i else 0) +
        (if h : (j : ℕ) + 1 = i then b ⟨j, by omega⟩ * x j else 0) +
        (if h : (j : ℕ) = i + 1 then c ⟨i, by omega⟩ * x j else 0) := by
  by_cases hij : i = j
  · subst hij
    simp [tridiagonalOf]
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp only [tridiagonalOf, of_apply, hij', ite_false, Ne.symm hij]
    split_ifs <;> first | omega | simp

/-- A sum over `Fin M` supported at the predecessor of `i`. -/
theorem sum_dite_val_add_one_eq {S : Type*} [AddCommMonoid S] {M : ℕ} (i : Fin M)
    (f : (j : Fin M) → (j : ℕ) + 1 = i → S) :
    ∑ j : Fin M, (if h : (j : ℕ) + 1 = i then f j h else 0) =
      if h : 0 < (i : ℕ) then f ⟨i - 1, by omega⟩ (by simp; omega) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i - 1, by omega⟩]
    · have h' : ((⟨i - 1, by omega⟩ : Fin M) : ℕ) + 1 = i := by simp; omega
      simp only [h', dite_true]
    · intro j _ hj
      have h' : ¬ ((j : ℕ) + 1 = i) := fun h' => hj (Fin.ext (by simp; omega))
      simp only [h', dite_false]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have h' : ¬ ((j : ℕ) + 1 = i) := by omega
    simp only [h', dite_false]

/-- A sum over `Fin M` supported at the successor of `i`. -/
theorem sum_dite_val_eq_add_one {S : Type*} [AddCommMonoid S] {M : ℕ} (i : Fin M)
    (f : (j : Fin M) → (j : ℕ) = i + 1 → S) :
    ∑ j : Fin M, (if h : (j : ℕ) = i + 1 then f j h else 0) =
      if h : (i : ℕ) + 1 < M then f ⟨i + 1, h⟩ rfl else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i + 1, by omega⟩]
    · simp only [dite_true]
    · intro j _ hj
      have h' : ¬ ((j : ℕ) = i + 1) := fun h' => hj (Fin.ext (by simp; omega))
      simp only [h', dite_false]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have h' : ¬ ((j : ℕ) = i + 1) := by omega
    simp only [h', dite_false]

/-- The three-term formula `(T x)ᵢ = bᵢ₋₁ xᵢ₋₁ + dᵢ xᵢ + cᵢ xᵢ₊₁` for `T = tridiag(b, d, c)`, with
the boundary terms absent at `i = 0` and `i = N`. -/
theorem tridiagonalOf_mulVec [NonUnitalNonAssocSemiring S]
    (b : Fin N → S) (d : Fin (N + 1) → S) (c : Fin N → S) (x : Fin (N + 1) → S)
    (i : Fin (N + 1)) :
    (tridiagonalOf b d c *ᵥ x) i =
      (if h : 0 < (i : ℕ) then b ⟨i - 1, by omega⟩ * x ⟨i - 1, by omega⟩ else 0) +
        d i * x i +
        (if h : (i : ℕ) < N then c ⟨i, h⟩ * x ⟨i + 1, by omega⟩ else 0) := by
  simp only [mulVec, dotProduct, tridiagonalOf_apply_mul_eq, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sum_dite_val_add_one_eq,
    sum_dite_val_eq_add_one]
  split_ifs <;> first | omega | abel

end TridiagonalOf

end Matrix
