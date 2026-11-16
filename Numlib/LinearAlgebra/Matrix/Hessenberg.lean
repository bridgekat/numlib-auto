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
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Numlib.LinearAlgebra.Matrix.Band

/-!
# Hessenberg, tridiagonal and bidiagonal matrices

This file defines the named matrix shapes of band width one, for a square matrix $A$ indexed by a
linearly ordered type: **upper Hessenberg** ($a_{ij} = 0$ for $i > j + 1$), **lower Hessenberg**
($a_{ij} = 0$ for $j > i + 1$), **tridiagonal** (both), and **upper** and **lower bidiagonal**
(nonzero entries only on the diagonal and on the first superdiagonal or subdiagonal). It relates
each shape to the lower and upper bandwidths of `Numlib.LinearAlgebra.Matrix.Band`, shows that a
symmetric or Hermitian upper Hessenberg matrix is tridiagonal, and shows that products with upper
triangular matrices and shifts by multiples of the identity keep the upper Hessenberg shape, as in
the QR iteration of [quarteroni2000numerical], §5.6.

The file also defines the tridiagonal matrix $\operatorname{tridiag}(b, d, c)$ with given
subdiagonal, diagonal and superdiagonal, with its three-term product formula, and the invariant
"upper Hessenberg in the first $k$ columns" of the Householder reductions to Hessenberg form. The
last result says that the moments $(T^j)_{00}$, $j \le 2m$, of a tridiagonal matrix $T$ of order
$m + 1$ do not depend on its last diagonal entry.

## Main definitions

* `Matrix.IsUpperHessenberg`: $a_{ij} = 0$ whenever some index lies strictly between $j$ and $i$.
* `Matrix.IsLowerHessenberg`: $a_{ij} = 0$ whenever some index lies strictly between $i$ and $j$.
* `Matrix.IsTridiagonal`: upper and lower Hessenberg at the same time.
* `Matrix.IsUpperHessenbergRect`: the rectangular $(m + 1) \times m$ upper Hessenberg shape, as in
  the matrix $\bar H_m$ of the Arnoldi process.
* `Matrix.IsUpperHessenbergInCols`: a matrix on `Fin N` is zero below the first subdiagonal in the
  columns $j < k$.
* `Matrix.IsUpperBidiagonal`, `Matrix.IsLowerBidiagonal`: the two bidiagonal shapes.
* `Matrix.tridiagonalOf`: the tridiagonal matrix $\operatorname{tridiag}(b, d, c)$ of order $N + 1$.

## Main results

* `Matrix.isUpperHessenberg_iff_hasLowerBandwidth_one`: upper Hessenberg is lower bandwidth $1$.
* `Matrix.isTridiagonal_iff_hasBandwidth_one`: tridiagonal is lower and upper bandwidth $1$.
* `Matrix.isUpperHessenberg_iff_fin`, `Matrix.isTridiagonal_iff_fin`,
  `Matrix.isUpperHessenberg_iff_nat`: the shapes on `Fin N` and on `ℕ` as conditions on the
  difference of the indices.
* `Matrix.IsUpperHessenberg.isTridiagonal_of_isHermitian`: a Hermitian upper Hessenberg matrix is
  tridiagonal.
* `Matrix.IsUpperTriangular.mul_isUpperHessenberg`: an upper triangular matrix times an upper
  Hessenberg matrix is upper Hessenberg.
* `Matrix.IsUpperHessenberg.sub_smul_one`: $H - \mu I$ is upper Hessenberg if $H$ is.
* `Matrix.tridiagonalOf_mulVec`: $(Tx)_i = b_{i-1} x_{i-1} + d_i x_i + c_i x_{i+1}$ for
  $T = \operatorname{tridiag}(b, d, c)$.
* `Matrix.isUnit_tridiagonalOf_one_zero`, `Matrix.isUnit_tridiagonalOf_zero`: a unit lower
  bidiagonal matrix, and an upper bidiagonal matrix with invertible diagonal entries, are invertible
  over any ring.
* `Matrix.pow_apply_zero_zero_eq_of_isTridiagonal`: the entries $(T^j)_{00}$, $j \le 2m$, of a
  tridiagonal $T$ of order $m + 1$ do not depend on $t_{mm}$.

## Implementation notes

* The shapes are stated over a bare `LinearOrder` on the index type. "Below the first subdiagonal"
  is spelled as "some index lies strictly between the column and the row", which needs no arithmetic
  on the index type. On `Fin n` and on `ℕ` it is the usual condition $j + 1 < i$.
* `Matrix.IsUpperHessenbergRect` is an abbreviation for `Matrix.HasLowerBandwidthRect` with
  bandwidth $1$.
* The triangular parts and the unit triangular matrices are in
  `Numlib.LinearAlgebra.Matrix.Triangular`, the bandwidths in `Numlib.LinearAlgebra.Matrix.Band`,
  the block product rules in `Numlib.LinearAlgebra.Matrix.Block`, and the rectangular bidiagonal
  shapes in `Numlib.LinearAlgebra.Matrix.Bidiagonal`.
-/

namespace Matrix

variable {n R : Type*} [LinearOrder n]

/-- A square matrix $H$ indexed by a linearly ordered type is **upper Hessenberg** if it is zero
below the first subdiagonal: $h_{ij} = 0$ whenever some index $k$ satisfies $j < k < i$.

This condition needs no arithmetic on the index type. On `Fin n` it is the usual condition
$h_{ij} = 0$ for $j + 1 < i$ (`Matrix.isUpperHessenberg_iff_fin`). -/
def IsUpperHessenberg [Zero R] (H : Matrix n n R) : Prop :=
  ∀ i j, (∃ k, j < k ∧ k < i) → H i j = 0

/-- A square matrix $H$ is **lower Hessenberg** if it is zero above the first superdiagonal:
$h_{ij} = 0$ whenever some index $k$ satisfies $i < k < j$. On `Fin n` this is $h_{ij} = 0$ for
$i + 1 < j$. It is the transpose of the upper Hessenberg shape. -/
def IsLowerHessenberg [Zero R] (H : Matrix n n R) : Prop :=
  ∀ i j, (∃ k, i < k ∧ k < j) → H i j = 0

/-- $H^T$ is lower Hessenberg if and only if $H$ is upper Hessenberg. -/
theorem isLowerHessenberg_transpose_iff [Zero R] {H : Matrix n n R} :
    Hᵀ.IsLowerHessenberg ↔ H.IsUpperHessenberg :=
  ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩

/-- $H^T$ is upper Hessenberg if and only if $H$ is lower Hessenberg. -/
theorem isUpperHessenberg_transpose_iff [Zero R] {H : Matrix n n R} :
    Hᵀ.IsUpperHessenberg ↔ H.IsLowerHessenberg :=
  ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩

/-- A square matrix $T$ is **tridiagonal** if it is zero outside the three central diagonals:
$t_{ij} = 0$ whenever some index lies strictly between $j$ and $i$, or strictly between $i$ and
$j$.

This is the upper Hessenberg condition together with its mirror image above the first
superdiagonal (`Matrix.isTridiagonal_iff_isUpperHessenberg_and_isLowerHessenberg`). -/
def IsTridiagonal [Zero R] (T : Matrix n n R) : Prop :=
  ∀ i j, (∃ k, j < k ∧ k < i) ∨ (∃ k, i < k ∧ k < j) → T i j = 0

/-- A tridiagonal matrix is upper Hessenberg.

The tridiagonal condition is the upper Hessenberg condition together with its mirror image, so
it is the stronger of the two. -/
theorem IsTridiagonal.isUpperHessenberg [Zero R] {T : Matrix n n R} (hT : T.IsTridiagonal) :
    T.IsUpperHessenberg := fun i j h => hT i j (Or.inl h)

/-- A tridiagonal matrix is lower Hessenberg. -/
theorem IsTridiagonal.isLowerHessenberg [Zero R] {T : Matrix n n R} (hT : T.IsTridiagonal) :
    T.IsLowerHessenberg := fun i j h => hT i j (Or.inr h)

/-- A matrix is tridiagonal if and only if it is both upper and lower Hessenberg. -/
theorem isTridiagonal_iff_isUpperHessenberg_and_isLowerHessenberg [Zero R] {T : Matrix n n R} :
    T.IsTridiagonal ↔ T.IsUpperHessenberg ∧ T.IsLowerHessenberg :=
  ⟨fun h => ⟨h.isUpperHessenberg, h.isLowerHessenberg⟩,
    fun h i j hij => hij.elim (h.1 i j) (h.2 i j)⟩

/-- Let $H$ be upper Hessenberg and let $f$ be a strictly monotone map of index types. Then the
submatrix $(h_{f(i) f(j)})_{i,j}$ is upper Hessenberg. -/
theorem IsUpperHessenberg.submatrix_of_strictMono {m : Type*} [LinearOrder m] [Zero R]
    {H : Matrix n n R} (hH : H.IsUpperHessenberg) {f : m → n} (hf : StrictMono f) :
    (H.submatrix f f).IsUpperHessenberg :=
  fun _ _ ⟨c, hjc, hci⟩ => hH _ _ ⟨f c, hf hjc, hf hci⟩

/-- A rectangular $(m + 1) \times m$ matrix $H$ is **upper Hessenberg** if $h_{ij} = 0$ whenever
$i > j + 1$. This is the shape of the matrix $\bar H_m$ of the Arnoldi process.

The definition is an abbreviation for lower bandwidth $1$ in the rectangular sense of
[golub2013matrix], §1.2.1, that is, `Matrix.HasLowerBandwidthRect H 1`. -/
abbrev IsUpperHessenbergRect [Zero R] {m : ℕ} (H : Matrix (Fin (m + 1)) (Fin m) R) : Prop :=
  H.HasLowerBandwidthRect 1

section Bidiagonal

variable [Zero R]

/-- A square matrix $B$ is **upper bidiagonal** if its only nonzero entries are on the diagonal and
on the first superdiagonal: $b_{ij} = 0$ whenever $j < i$, or some index lies strictly between
$i$ and $j$.

This is the shape of the Golub–Kahan bidiagonalization ([quarteroni2000numerical], (5.57)) and
of the factor $U$ in the LU factorization of a tridiagonal matrix. As in `Matrix.IsTridiagonal`,
"on the first superdiagonal" is spelled as "no index lies strictly between the row and the
column". -/
def IsUpperBidiagonal (B : Matrix n n R) : Prop :=
  ∀ i j, j < i ∨ (∃ k, i < k ∧ k < j) → B i j = 0

/-- A square matrix $B$ is **lower bidiagonal** if its only nonzero entries are on the diagonal and
on the first subdiagonal: $b_{ij} = 0$ whenever $i < j$, or some index lies strictly between $j$
and $i$.

This is the shape of the factor $L$ in the LU factorization of a tridiagonal matrix. -/
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

/-- $B^T$ is lower bidiagonal if and only if $B$ is upper bidiagonal. -/
theorem isLowerBidiagonal_transpose_iff {B : Matrix n n R} :
    Bᵀ.IsLowerBidiagonal ↔ B.IsUpperBidiagonal :=
  ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩

/-- $B^T$ is upper bidiagonal if and only if $B$ is lower bidiagonal. -/
theorem isUpperBidiagonal_transpose_iff {B : Matrix n n R} :
    Bᵀ.IsUpperBidiagonal ↔ B.IsLowerBidiagonal :=
  ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩

end Bidiagonal

section Hermitian

/-- Let $H$ be a square matrix indexed by a linearly ordered type. If $H$ is upper Hessenberg and
symmetric, $H^T = H$, then $H$ is tridiagonal.

An entry above the first superdiagonal is the mirror image of an entry below the first
subdiagonal, which is zero. This is Remark 5.4 of [quarteroni2000numerical]. -/
theorem IsUpperHessenberg.isTridiagonal_of_isSymm [Zero R] {H : Matrix n n R}
    (hH : H.IsUpperHessenberg) (hs : H.IsSymm) : H.IsTridiagonal := fun i j h => by
  rcases h with h | h
  · exact hH i j h
  · rw [← hs.apply i j]
    exact hH j i h

/-- Let $H$ be a square matrix indexed by a linearly ordered type, with entries in an additive
monoid with a star operation. If $H$ is upper Hessenberg and Hermitian, $H^* = H$, then $H$ is
tridiagonal.

This is Remark 5.4 of [quarteroni2000numerical]. The proof is the same as for
`Matrix.IsUpperHessenberg.isTridiagonal_of_isSymm`, since the star of zero is zero. -/
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

/-- Let $A$ be a square matrix indexed by a finite linearly ordered type. Then $A$ is upper
Hessenberg if and only if $A$ has lower bandwidth $1$ in the sense of
`Matrix.HasLowerBandwidth`. -/
theorem isUpperHessenberg_iff_hasLowerBandwidth_one :
    A.IsUpperHessenberg ↔ A.HasLowerBandwidth 1 := by
  simp only [HasLowerBandwidth, one_lt_card_filter_le_lt_iff]
  rfl

/-- Let $A$ be a square matrix indexed by `Fin N`. Then $A$ is upper Hessenberg if and only if
$a_{ij} = 0$ for all $i, j$ with $j + 1 < i$. -/
theorem isUpperHessenberg_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.IsUpperHessenberg ↔ ∀ i j : Fin N, (j : ℕ) + 1 < (i : ℕ) → A i j = 0 := by
  rw [isUpperHessenberg_iff_hasLowerBandwidth_one, hasLowerBandwidth_iff_fin]

/-- Let $H$ be a matrix indexed by $\mathbb{N} \times \mathbb{N}$. Then $H$ is upper Hessenberg if
and only if $h_{ij} = 0$ for all $i, j$ with $j + 1 < i$.

This is the form in which the $\mathbb{N}$-indexed coefficient arrays of the Krylov methods
state the shape. -/
theorem isUpperHessenberg_iff_nat {H : Matrix ℕ ℕ R} :
    H.IsUpperHessenberg ↔ ∀ i j : ℕ, j + 1 < i → H i j = 0 :=
  forall₂_congr fun i j => imp_congr_left
    ⟨fun ⟨k, hjk, hki⟩ => by omega, fun h => ⟨j + 1, by omega, h⟩⟩

/-- Let $H$ be an upper Hessenberg matrix indexed by $\mathbb{N} \times \mathbb{N}$. Then
$h_{ij} = 0$ for all $i, j \in \mathbb{N}$ with $j + 1 < i$. -/
theorem IsUpperHessenberg.eq_zero_of_add_one_lt {H : Matrix ℕ ℕ R} (hH : H.IsUpperHessenberg)
    (i j : ℕ) (h : j + 1 < i) : H i j = 0 :=
  isUpperHessenberg_iff_nat.1 hH i j h

/-- A square matrix $A$ indexed by a finite linearly ordered type is lower Hessenberg if and only if
it has upper bandwidth $1$. -/
theorem isLowerHessenberg_iff_hasUpperBandwidth_one :
    A.IsLowerHessenberg ↔ A.HasUpperBandwidth 1 := by
  simp only [HasUpperBandwidth, one_lt_card_filter_le_lt_iff]
  rfl

/-- A square matrix $A$ indexed by `Fin N` is lower Hessenberg if and only if $a_{ij} = 0$ for all
$i, j$ with $i + 1 < j$. -/
theorem isLowerHessenberg_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.IsLowerHessenberg ↔ ∀ i j : Fin N, (i : ℕ) + 1 < (j : ℕ) → A i j = 0 := by
  rw [isLowerHessenberg_iff_hasUpperBandwidth_one, hasUpperBandwidth_iff_fin]

/-- Let $A$ be a square matrix indexed by a finite linearly ordered type. Then $A$ is tridiagonal if
and only if $A$ has lower bandwidth $1$ and upper bandwidth $1$.

This is the definition of a tridiagonal matrix in [quarteroni2000numerical], §1.6.3. -/
theorem isTridiagonal_iff_hasBandwidth_one :
    A.IsTridiagonal ↔ A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth 1 := by
  simp only [HasLowerBandwidth, HasUpperBandwidth, one_lt_card_filter_le_lt_iff]
  exact ⟨fun h => ⟨fun i j hij => h i j (Or.inl hij), fun i j hij => h i j (Or.inr hij)⟩,
    fun h i j hij => hij.elim (h.1 i j) (h.2 i j)⟩

/-- Let $A$ be a square matrix indexed by `Fin N`. Then $A$ is tridiagonal if and only if
$a_{ij} = 0$ for all $i, j$ with $j + 1 < i$ or $i + 1 < j$. -/
theorem isTridiagonal_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.IsTridiagonal ↔ ∀ i j : Fin N, (j : ℕ) + 1 < i ∨ (i : ℕ) + 1 < j → A i j = 0 := by
  rw [isTridiagonal_iff_hasBandwidth_one, hasLowerBandwidth_iff_fin, hasUpperBandwidth_iff_fin]
  exact ⟨fun h i j hij => hij.elim (h.1 i j) (h.2 i j),
    fun h => ⟨fun i j hij => h i j (Or.inl hij), fun i j hij => h i j (Or.inr hij)⟩⟩

/-- A lower bidiagonal matrix has lower bandwidth $1$ and upper bandwidth $0$. -/
theorem IsLowerBidiagonal.hasBandwidth (hB : A.IsLowerBidiagonal) :
    A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth 0 :=
  ⟨(isTridiagonal_iff_hasBandwidth_one.1 hB.isTridiagonal).1,
    hasUpperBandwidth_zero_iff.2 hB.isLowerTriangular⟩

/-- An upper bidiagonal matrix has lower bandwidth $0$ and upper bandwidth $1$. -/
theorem IsUpperBidiagonal.hasBandwidth (hB : A.IsUpperBidiagonal) :
    A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth 1 :=
  ⟨hasLowerBandwidth_zero_iff.2 hB.isUpperTriangular,
    (isTridiagonal_iff_hasBandwidth_one.1 hB.isTridiagonal).2⟩

end Bandwidth

/-! ### Matrices upper Hessenberg in their leading columns -/

section InCols

variable {N : ℕ}

/-- A square matrix $A$ indexed by `Fin N` is **upper Hessenberg in its first $k$ columns** if it is
zero below the first subdiagonal in the columns $j < k$: $a_{ij} = 0$ whenever $j < k$ and
$j + 1 < i$.

This is the loop invariant of the Householder reductions to Hessenberg and to tridiagonal form.
At $k = N - 2$ it is the upper Hessenberg condition
(`Matrix.IsUpperHessenbergInCols.isUpperHessenberg`). -/
def IsUpperHessenbergInCols [Zero R] (A : Matrix (Fin N) (Fin N) R) (k : ℕ) : Prop :=
  ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → A i j = 0

/-- A square matrix $A$ indexed by `Fin N` is upper Hessenberg in its first $k$ columns if and only
if $a_{ij} = 0$ for all $i, j$ with $j < k$ and $j + 1 < i$. -/
theorem isUpperHessenbergInCols_iff [Zero R] {A : Matrix (Fin N) (Fin N) R} {k : ℕ} :
    A.IsUpperHessenbergInCols k ↔ ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → A i j = 0 :=
  Iff.rfl

/-- Every square matrix indexed by `Fin N` is upper Hessenberg in its first $0$ columns. -/
theorem isUpperHessenbergInCols_zero [Zero R] (A : Matrix (Fin N) (Fin N) R) :
    A.IsUpperHessenbergInCols 0 :=
  fun _ _ hj => absurd hj (Nat.not_lt_zero _)

/-- Let $A$ be a square matrix indexed by `Fin N` that is upper Hessenberg in its first $k$ columns,
with $N - 2 \le k$. Then $A$ is upper Hessenberg.

The difference $N - 2$ is truncated at $0$. The columns $N - 2$ and $N - 1$ have no entry below
the first subdiagonal, so they need no condition. -/
theorem IsUpperHessenbergInCols.isUpperHessenberg [Zero R] {A : Matrix (Fin N) (Fin N) R} {k : ℕ}
    (h : A.IsUpperHessenbergInCols k) (hk : N - 2 ≤ k) : A.IsUpperHessenberg :=
  fun i j ⟨l, hjl, hli⟩ => h i j (by omega) (by omega)

end InCols

section Products

variable [Fintype n] [NonUnitalNonAssocSemiring R]

/-- Let $T$ and $H$ be square matrices indexed by a finite linearly ordered type. If $T$ is upper
triangular and $H$ is upper Hessenberg, then $TH$ is upper Hessenberg.

This is the product $RQ$ of the QR iteration, [quarteroni2000numerical], §5.6.4. The bandwidths
$0$ and $1$ of the two factors add up to the lower bandwidth $1$ of the product. -/
theorem IsUpperTriangular.mul_isUpperHessenberg {T H : Matrix n n R} (hT : T.IsUpperTriangular)
    (hH : H.IsUpperHessenberg) : (T * H).IsUpperHessenberg :=
  isUpperHessenberg_iff_hasLowerBandwidth_one.2 <| by
    simpa using (hasLowerBandwidth_zero_iff.2 hT).mul
      (isUpperHessenberg_iff_hasLowerBandwidth_one.1 hH)

/-- Let $H$ and $T$ be square matrices indexed by a finite linearly ordered type. If $H$ is upper
Hessenberg and $T$ is upper triangular, then $HT$ is upper Hessenberg.

This is the factor $Q = H R^{-1}$ of the QR factorization of an upper Hessenberg matrix,
[quarteroni2000numerical], §5.6.3. -/
theorem IsUpperHessenberg.mul_isUpperTriangular {H T : Matrix n n R} (hH : H.IsUpperHessenberg)
    (hT : T.IsUpperTriangular) : (H * T).IsUpperHessenberg :=
  isUpperHessenberg_iff_hasLowerBandwidth_one.2 <| by
    simpa using (isUpperHessenberg_iff_hasLowerBandwidth_one.1 hH).mul
      (hasLowerBandwidth_zero_iff.2 hT)

end Products

section Shift

variable [DecidableEq n]

/-- Let $H$ be an upper Hessenberg square matrix and let $\mu$ be a scalar. Then $H + \mu I$ is
upper Hessenberg.

This is the shift $+ \mu I$ of a shifted QR step, [quarteroni2000numerical], (5.52). -/
theorem IsUpperHessenberg.add_smul_one [NonAssocSemiring R] {H : Matrix n n R}
    (hH : H.IsUpperHessenberg) (μ : R) : (H + μ • 1).IsUpperHessenberg := by
  intro i j h
  obtain ⟨k, hjk, hki⟩ := h
  have hij : i ≠ j := ne_of_gt (lt_trans hjk hki)
  rw [Matrix.add_apply, Matrix.smul_apply, one_apply_ne hij, smul_zero, add_zero]
  exact hH i j ⟨k, hjk, hki⟩

/-- Let $H$ be an upper Hessenberg square matrix over a ring and let $\mu$ be a scalar. Then
$H - \mu I$ is upper Hessenberg.

This is the shift $- \mu I$ of a shifted QR step, [quarteroni2000numerical], (5.52). -/
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

/-- The **tridiagonal matrix** $\operatorname{tridiag}(b, d, c)$ of [quarteroni2000numerical],
§1.6.3: for $b, c \in R^N$ and $d \in R^{N+1}$, the $(N + 1) \times (N + 1)$ matrix with $d_i$
at $(i, i)$, $b_i$ at $(i + 1, i)$, $c_i$ at $(i, i + 1)$, and zero elsewhere.

The book writes $b_1, \dots, b_{n-1}$ and $d_1, \dots, d_n$. Here all indices start at $0$, and
the matrix is indexed by `Fin (N + 1)`. -/
def tridiagonalOf (b : Fin N → R) (d : Fin (N + 1) → R) (c : Fin N → R) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then d i
    else if h : (i : ℕ) = j + 1 then b ⟨j, by omega⟩
    else if h' : (j : ℕ) = i + 1 then c ⟨i, by omega⟩
    else 0

variable (b : Fin N → R) (d : Fin (N + 1) → R) (c : Fin N → R)

/-- The entry $(i, i)$ of $\operatorname{tridiag}(b, d, c)$ is $d_i$. -/
@[simp]
theorem tridiagonalOf_apply_self (i : Fin (N + 1)) : tridiagonalOf b d c i i = d i := by
  simp [tridiagonalOf]

/-- The entry $(i + 1, i)$ of $\operatorname{tridiag}(b, d, c)$ is $b_i$. -/
@[simp]
theorem tridiagonalOf_apply_succ_castSucc (i : Fin N) :
    tridiagonalOf b d c i.succ i.castSucc = b i := by
  simp [tridiagonalOf]

/-- The entry $(i, i + 1)$ of $\operatorname{tridiag}(b, d, c)$ is $c_i$. -/
@[simp]
theorem tridiagonalOf_apply_castSucc_succ (i : Fin N) :
    tridiagonalOf b d c i.castSucc i.succ = c i := by
  have h : (i : ℕ) ≠ i + 1 + 1 := by omega
  simp [tridiagonalOf, h]

/-- The entry $(i, j)$ of $\operatorname{tridiag}(b, d, c)$ is zero if $i \ne j$, $i \ne j + 1$ and
$j \ne i + 1$. -/
theorem tridiagonalOf_apply_of_ne {i j : Fin (N + 1)} (hij : (i : ℕ) ≠ j)
    (h₁ : (i : ℕ) ≠ j + 1) (h₂ : (j : ℕ) ≠ i + 1) : tridiagonalOf b d c i j = 0 := by
  simp [tridiagonalOf, hij, h₁, h₂]

/-- For all $b, c \in R^N$ and $d \in R^{N+1}$, the matrix $\operatorname{tridiag}(b, d, c)$ is
tridiagonal. -/
theorem isTridiagonal_tridiagonalOf : (tridiagonalOf b d c).IsTridiagonal := by
  intro i j h
  refine tridiagonalOf_apply_of_ne b d c ?_ ?_ ?_ <;>
    rcases h with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp only [Fin.lt_def] at hk <;> omega

/-- For all $b, c \in R^N$ and $d \in R^{N+1}$, the transpose exchanges the two off-diagonals:
$$\operatorname{tridiag}(b, d, c)^T = \operatorname{tridiag}(c, d, b).$$
-/
theorem tridiagonalOf_transpose : (tridiagonalOf b d c)ᵀ = tridiagonalOf c d b := by
  ext i j
  simp only [transpose_apply, tridiagonalOf, of_apply]
  split_ifs <;> first | rfl | omega | exact congrArg d (Fin.ext (by omega))

/-- Let $T = \operatorname{tridiag}(b, d, c)$ and $x \in S^{N+1}$. Each term $t_{ij} x_j$ of
$(Tx)_i$ is the sum of three terms: $d_i x_i$ if $j = i$, $b_j x_j$ if $j + 1 = i$, and
$c_i x_j$ if $j = i + 1$, each term being zero when its condition fails. -/
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

/-- Let $M \in \mathbb{N}$, $i < M$, and let $f(j)$ be defined for the indices $j < M$ with
$j + 1 = i$. Then the sum over $j < M$ of $f(j)$ for $j + 1 = i$, and of $0$ otherwise, is
$f(i - 1)$ if $i > 0$, and $0$ if $i = 0$. -/
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

/-- Let $M \in \mathbb{N}$, $i < M$, and let $f(j)$ be defined for the indices $j < M$ with
$j = i + 1$. Then the sum over $j < M$ of $f(j)$ for $j = i + 1$, and of $0$ otherwise, is
$f(i + 1)$ if $i + 1 < M$, and $0$ otherwise. -/
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

/-- Let $S$ be a (not necessarily associative or unital) semiring, $b, c \in S^N$,
$d, x \in S^{N+1}$, and $T = \operatorname{tridiag}(b, d, c)$. Then for every
$i \in \{0, \dots, N\}$,
$$(Tx)_i = b_{i-1} x_{i-1} + d_i x_i + c_i x_{i+1},$$
where the first term is absent for $i = 0$ and the last term is absent for $i = N$. -/
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

/-- Let $S$ be a ring and $\ell \in S^N$. The unit lower bidiagonal matrix
$\operatorname{tridiag}(\ell, 1, 0)$, with ones on the diagonal and $\ell$ on the subdiagonal,
is invertible. -/
theorem isUnit_tridiagonalOf_one_zero [Ring S] (L : Fin N → S) :
    IsUnit (tridiagonalOf L 1 0) := by
  have h : tridiagonalOf L 1 0 = 1 + tridiagonalOf L 0 0 := by
    ext i j
    simp only [tridiagonalOf, of_apply, Matrix.add_apply, Matrix.one_apply, Pi.one_apply,
      Pi.zero_apply, Fin.ext_iff]
    split_ifs <;> simp
  rw [h]
  refine isUnit_one_add_of_potential _ (fun i => N - i)
    (fun i => Nat.lt_succ_of_le (Nat.sub_le _ _)) fun i j hij => ?_
  simp only [tridiagonalOf, of_apply, Pi.zero_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Let $S$ be a ring, $u \in S^{N+1}$ and $f \in S^N$, and assume that every $u_i$ is invertible.
Then the upper bidiagonal matrix $\operatorname{tridiag}(0, u, f)$, with $u$ on the diagonal and
$f$ on the superdiagonal, is invertible. -/
theorem isUnit_tridiagonalOf_zero [Ring S] (U : Fin (N + 1) → S) (F : Fin N → S)
    (hU : ∀ i, IsUnit (U i)) : IsUnit (tridiagonalOf 0 U F) := by
  have hdiag : IsUnit (diagonal U) := by
    refine ⟨⟨diagonal U, diagonal fun i => Ring.inverse (U i), ?_, ?_⟩, rfl⟩ <;>
      rw [diagonal_mul_diagonal, ← diagonal_one] <;> congr 1 <;> funext i
    · exact Ring.mul_inverse_cancel _ (hU i)
    · exact Ring.inverse_mul_cancel _ (hU i)
  have h : tridiagonalOf 0 U F
      = diagonal U * (1 + diagonal (fun i => Ring.inverse (U i)) * tridiagonalOf 0 0 F) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, diagonal_mul_diagonal]
    have hone : (diagonal fun i => U i * Ring.inverse (U i)) = 1 := by
      rw [← diagonal_one]
      congr 1
      funext i
      exact Ring.mul_inverse_cancel _ (hU i)
    rw [hone, Matrix.one_mul]
    ext i j
    simp only [tridiagonalOf, of_apply, Matrix.add_apply, diagonal_apply, Pi.zero_apply,
        Fin.ext_iff]
    split_ifs <;> simp
  rw [h]
  refine hdiag.mul
    (isUnit_one_add_of_potential _ (fun i => i) (fun i => i.isLt) fun i j hij => ?_)
  rw [diagonal_mul]
  simp only [tridiagonalOf, of_apply, Pi.zero_apply]
  split_ifs <;> first | simp | (exfalso; omega)

end TridiagonalOf

/-! ### Moments of tridiagonal matrices -/

section Moments

variable {S : Type*} [CommRing S] {m : ℕ}

private theorem pow_mulVec_single_zero_eq {M M' : Matrix (Fin (m + 1)) (Fin (m + 1)) S}
    (hM : M.IsTridiagonal)
    (heq : ∀ i j, ¬(i = Fin.last m ∧ j = Fin.last m) → M i j = M' i j) {k : ℕ} (hk : k ≤ m) :
    M ^ k *ᵥ Pi.single 0 1 = M' ^ k *ᵥ Pi.single 0 1 ∧
      ∀ l : Fin (m + 1), k < (l : ℕ) → (M ^ k *ᵥ Pi.single 0 1) l = 0 := by
  induction k with
  | zero =>
    refine ⟨by rw [pow_zero, pow_zero], fun l hl => ?_⟩
    rw [pow_zero, one_mulVec, Pi.single_apply, ite_eq_right (fun h => by subst h; simp at hl)]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hlast : (M ^ k *ᵥ Pi.single 0 1) (Fin.last m) = 0 := ih2 _ (by rw [Fin.val_last]; omega)
    have hstep : M *ᵥ (M ^ k *ᵥ Pi.single 0 1) = M' *ᵥ (M ^ k *ᵥ Pi.single 0 1) := by
      ext i
      change ∑ j, M i j * (M ^ k *ᵥ Pi.single 0 1) j = ∑ j, M' i j * (M ^ k *ᵥ Pi.single 0 1) j
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = Fin.last m
      · rw [hj, hlast, mul_zero, mul_zero]
      · rw [heq i j fun h => hj h.2]
    refine ⟨?_, fun l hl => ?_⟩
    · rw [pow_succ', ← mulVec_mulVec, pow_succ', ← mulVec_mulVec, hstep, ih1]
    · rw [pow_succ', ← mulVec_mulVec]
      change ∑ j, M l j * (M ^ k *ᵥ Pi.single 0 1) j = 0
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (j : ℕ) ≤ k
      · rw [hM l j (Or.inl ⟨⟨(j : ℕ) + 1, by omega⟩, Fin.lt_def.2 (by simp),
          Fin.lt_def.2 (by simp; omega)⟩), zero_mul]
      · rw [ih2 j (by omega), mul_zero]

/-- **Low moments do not see the last diagonal entry.** Let $S$ be a commutative ring and let
$M, M'$ be square matrices of order $m + 1$ over $S$, indexed by $\{0, \dots, m\}$. Assume that
$M$ is tridiagonal and that $M$ and $M'$ agree at every entry except possibly at $(m, m)$. Then
for every $j \le 2m$,
$$(M^j)_{00} = (M'^j)_{00}.$$

For $i \le m$ the vector $M^i e_0$ is supported on the first $i + 1$ coordinates, and it is
computed from the columns $0, \dots, i - 1$ only; the same holds for the row $e_0^T M^i$. Then
$(M^j)_{00} = e_0^T M^{i} M^{j - i} e_0$ with $i, j - i \le m$. This is the moment argument
behind the Gauss–Radau rule of [golub2013matrix], §10.2.5. -/
theorem pow_apply_zero_zero_eq_of_isTridiagonal {M M' : Matrix (Fin (m + 1)) (Fin (m + 1)) S}
    (hM : M.IsTridiagonal)
    (heq : ∀ i j, ¬(i = Fin.last m ∧ j = Fin.last m) → M i j = M' i j) {j : ℕ} (hj : j ≤ 2 * m) :
    (M ^ j) 0 0 = (M' ^ j) 0 0 := by
  have hMt : Mᵀ.IsTridiagonal := fun i k h => hM k i (h.symm)
  have heqt : ∀ i k, ¬(i = Fin.last m ∧ k = Fin.last m) → Mᵀ i k = M'ᵀ i k :=
    fun i k h => heq k i fun h' => h ⟨h'.2, h'.1⟩
  obtain ⟨j₁, j₂, rfl, h₁, h₂⟩ : ∃ j₁ j₂, j = j₁ + j₂ ∧ j₁ ≤ m ∧ j₂ ≤ m :=
    ⟨j / 2, j - j / 2, by omega, by omega, by omega⟩
  have hcol := (pow_mulVec_single_zero_eq hM heq h₂).1
  have hrow := (pow_mulVec_single_zero_eq hMt heqt h₁).1
  have hsplit : ∀ N : Matrix (Fin (m + 1)) (Fin (m + 1)) S, (N ^ (j₁ + j₂)) 0 0 =
      (Nᵀ ^ j₁ *ᵥ Pi.single 0 1) ⬝ᵥ (N ^ j₂ *ᵥ Pi.single 0 1) := by
    intro N
    rw [pow_add, ← transpose_pow, mulVec_single_one, mulVec_single_one, Matrix.mul_apply,
        dotProduct]
    rfl
  rw [hsplit, hsplit, hcol, hrow]

end Moments

end Matrix
