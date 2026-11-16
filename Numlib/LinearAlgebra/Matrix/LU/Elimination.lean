/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.LU`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Data.Finset.Card
import Numlib.LinearAlgebra.Matrix.LU

/-!
# One step of Gaussian elimination

Let $K$ be a field, let $n$ be a finite linearly ordered index set, and let $M \in K^{n \times n}$.
One step of Gaussian elimination at a pivot $p \in n$ subtracts $M_{ip} / M_{pp}$ times the row $p$
from each row $i > p$, and leaves the other rows alone. With the *multiplier matrix* $N$, which has
the entries $N_{ip} = M_{ip} / M_{pp}$ for $i > p$ and is zero elsewhere, the eliminated matrix is
$M' = M - NM = (I - N) M$. Since $N^2 = 0$, the matrix $G = I + N$ is unipotent with inverse
$I - N$, and $M = G M'$. The matrix $I - N$ is the Gaussian transformation matrix $M_p$ of
[quarteroni2000numerical], §3.3.1. This step is the elementary operation from which the LU
factorization of `Numlib.LinearAlgebra.Matrix.LU` and the incomplete factorizations of
`Numlib.Preconditioner.ILU` are built ([saad2003iterative], §10.3).

On $A \in K^{N \times N}$, the stages of the Gaussian elimination method are $A^{(0)} = A$ and
$A^{(k+1)} = M_k A^{(k)}$, the elimination of $A^{(k)}$ at the pivot $(k, k)$, for $k < N$. With
nonzero pivots $a^{(k)}_{kk}$ for $k = 0, \dots, N - 2$, this gives $A = LU$ with $U = A^{(N)}$ and
$L$ the unit lower triangular matrix of the multipliers, and these pivots are nonzero exactly when
the strict leading principal submatrices of $A$ are nonsingular. The module also defines the
Doolittle recurrence for the LU factors on any finite linear order, shows that it computes the same
factors, and derives the Crout factorization from it ([quarteroni2000numerical], §3.3).

## Main definitions

* `Matrix.elimMultipliers`: the multiplier matrix $N$ of one step of elimination at a pivot $p$.
* `Matrix.elimMul`: the unipotent factor $G = I + N$ of the step.
* `Matrix.elimStep`: the eliminated matrix $M - NM$.
* `Matrix.gaussTransform`: the Gaussian transformation matrix $I - N$.
* `Matrix.gemStage`: the stages $A^{(k)}$ of the Gaussian elimination method on $K^{N \times N}$.
* `Matrix.gemLower`: the unit lower triangular matrix $L$ of the multipliers.
* `Matrix.blockEmb`: the order embedding of the block of consecutive indices $k, \dots, k + j - 1$.
* `Matrix.luPacked`: the Doolittle recurrence, with both factors packed in one matrix.
* `Matrix.luLower`, `Matrix.luUpper`: the two Doolittle factors read off the packed form.
* `Matrix.croutLower`, `Matrix.croutUpper`: the Crout factors, which are the Doolittle factors of
  the transpose, transposed back.

## Main results

* `Matrix.elimStep_apply_pivot`: the step annihilates the pivot column below a nonzero pivot.
* `Matrix.elimMultipliers_mul_self`: $N^2 = 0$.
* `Matrix.inv_elimMul`: $G^{-1} = I - N$.
* `Matrix.elimMul_mul_elimStep`: $M = G M'$.
* `Matrix.gemStage_succ_eq_gaussTransform_mul`: $A^{(k+1)} = M_k A^{(k)}$.
* `Matrix.isLU_gemLower_gemStage`: if the pivots $a^{(k)}_{kk}$, $k = 0, \dots, N - 2$, are nonzero,
  then $A = LU$ with $U = A^{(N)}$.
* `Matrix.gemStage_pivots_ne_zero_iff`: these pivots are nonzero if and only if every strict leading
  principal submatrix of $A$ is nonsingular.
* `Matrix.elimStep_submatrix_orderEmbedding`, `Matrix.gemStage_submatrix_blockEmb`: elimination
  commutes with the restriction to a set of indices carried by an order embedding, so the
  elimination of a trailing block of $A^{(k)}$ is the restriction of the global elimination.
* `Matrix.elimStep_submatrix_id_of_apply_self`: one step commutes with a permutation of the columns
  that fixes the pivot.
* `Matrix.isLU_luLower_luUpper`: the Doolittle recurrence computes the LU factorization when the
  strict leading principal submatrices are nonsingular.
* `Matrix.luLower_eq_gemLower`: the Doolittle factors are the factors of Gaussian elimination.
* `Matrix.croutLower_mul_croutUpper`: the Crout factorization.

## Notation

* $A^{(k)}$ is `Matrix.gemStage A k`, with entries $a^{(k)}_{ij}$.
* $A(\le k)$ and $A(< k)$ are `Matrix.leadingPrincipalSubmatrix A k` and
  `Matrix.strictLeadingPrincipalSubmatrix A k`, the blocks of $A$ on the indices $i \le k$ and
  $i < k$.

## Implementation notes

* Indices and stages are numbered from $0$. The source numbers both from $1$, so $A^{(k)}$ here is
  $A^{(k+1)}$ in [quarteroni2000numerical], and the pivots $k = 0, \dots, N - 2$ here are its pivots
  $k = 1, \dots, n - 1$.
* The index type is kept fixed: elimination is multiplication by the unipotent matrix $G$ on all of
  $n$, not a Schur complement on the smaller index type `{i // i ≠ p}`. Then the accumulated lower
  factor of a factorization is a product of the matrices `Matrix.elimMul`, and no statement needs a
  reindexing. The same step on the smaller index type is `Matrix.schurComplementSingle` of
  `Numlib.LinearAlgebra.Matrix.SchurComplement`. Only the strict order $p < i$ of the index type is
  used, to say which rows lie below the pivot.
* Division by zero is $0$ in Lean. At a zero pivot the multipliers are $0$, and the step leaves the
  matrix unchanged.
* The last pivot $a^{(N-1)}_{N-1,N-1}$ is never used as a divisor. So the factorization theorems
  require only the pivots with $k + 1 < N$ to be nonzero, which makes the condition equivalent to
  the nonsingularity of the *strict* leading principal submatrices, and a singular matrix with
  nonsingular strict leading blocks can be factored. The restriction is necessary:
  `Matrix.gemStage_pivots_ne_zero_iff` with all $N$ pivots is false. For the matrix $B =
  \begin{bmatrix} 1 & 2 \\ 1 & 2 \end{bmatrix}$ of Example 3.3 of [quarteroni2000numerical], the
  strict leading principal submatrices are the empty matrix and $[1]$, both nonsingular, but the
  last pivot is $b_{22} - (b_{21} / b_{11}) b_{12} = 2 - 2 = 0$. The $1 \times 1$ zero matrix fails
  in the same way, with an empty strict block. In general the last pivot is
  $\det A / \det A(< N - 1)$, so it vanishes for every singular $A$ whose strict leading blocks are
  nonsingular. The source restricts its condition in the same way, to $k = 1, \dots, n - 1$, in the
  sentence after (3.33) and in Theorem 3.4.
* Everything is over a field, and nothing here is numerical. Pivoting and the growth factor are in
  `Numlib.LinearAlgebra.Matrix.LU.Pivoting`.
-/

open Finset

namespace Matrix

section Step

variable {n K : Type*} [LinearOrder n] [DecidableEq n] [Field K]

/-- The **multiplier matrix** of one step of Gaussian elimination at the pivot $p$: the matrix $N$
with
$$N_{ij} = \begin{cases} M_{ip} / M_{pp} & \text{if } i > p \text{ and } j = p, \\ 0 &
  \text{otherwise.} \end{cases}$$

Its only nonzero column is the column $p$, and its row $p$ is zero, so $N^2 = 0$
(`Matrix.elimMultipliers_mul_self`). If $M_{pp} = 0$, then $N = 0$, because division by zero is
$0$. -/
noncomputable def elimMultipliers (M : Matrix n n K) (p : n) : Matrix n n K :=
  Matrix.of fun i j => if p < i ∧ j = p then M i p * (M p p)⁻¹ else 0

/-- The **unipotent factor** $G = I + N$ of one step of Gaussian elimination at the pivot $p$, where
$N$ is the multiplier matrix `Matrix.elimMultipliers M p`. -/
noncomputable def elimMul (M : Matrix n n K) (p : n) : Matrix n n K :=
  1 + elimMultipliers M p

/-- The entry $(i, j)$ of the multiplier matrix is $M_{ip} / M_{pp}$ if $i > p$ and $j = p$, and $0$
otherwise. -/
@[simp]
theorem elimMultipliers_apply (M : Matrix n n K) (p i j : n) :
    elimMultipliers M p i j = if p < i ∧ j = p then M i p * (M p p)⁻¹ else 0 := rfl

variable [Fintype n]

/-- **One step of Gaussian elimination** at the pivot $p$: the matrix $M - NM$, with $N$ the
multiplier matrix `Matrix.elimMultipliers M p`. Its entries are
$$(M - NM)_{ij} = \begin{cases} M_{ij} - (M_{ip} / M_{pp}) M_{pj} & \text{if } i > p, \\ M_{ij}
  & \text{otherwise.} \end{cases}$$

The step is defined on the whole index type. So the accumulated lower factor of a factorization
is a product of the matrices `Matrix.elimMul`, and no reindexing is needed. The same step on the
index type without $p$ is `Matrix.schurComplementSingle`. -/
noncomputable def elimStep (M : Matrix n n K) (p : n) : Matrix n n K :=
  M - elimMultipliers M p * M

/-- The entry $(i, j)$ of the product $NM$ of the multiplier matrix and $M$ is
$(M_{ip} / M_{pp}) M_{pj}$ if $i > p$, and $0$ otherwise. -/
theorem elimMultipliers_mul_apply (M : Matrix n n K) (p i j : n) :
    (elimMultipliers M p * M) i j = if p < i then M i p * (M p p)⁻¹ * M p j else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : p < i
  · rw [ite_eq_left hi, Finset.sum_eq_single p (fun c _ hc => by simp [hc]) (by simp)]
    simp [hi]
  · simp [hi]

/-- The entry $(i, j)$ of the eliminated matrix is $M_{ij} - (M_{ip} / M_{pp}) M_{pj}$ if $i > p$,
and $M_{ij}$ otherwise. -/
theorem elimStep_apply (M : Matrix n n K) (p i j : n) :
    elimStep M p i j = M i j - if p < i then M i p * (M p p)⁻¹ * M p j else 0 := by
  rw [elimStep, Matrix.sub_apply, elimMultipliers_mul_apply]

/-- If $i \le p$, the step at the pivot $p$ does not change the row $i$: the entry $(i, j)$ of the
eliminated matrix is $M_{ij}$. -/
theorem elimStep_apply_of_not_lt (M : Matrix n n K) {p i : n} (hi : ¬ p < i) (j : n) :
    elimStep M p i j = M i j := by
  rw [elimStep_apply, ite_eq_right hi, sub_zero]

/-- If $i > p$, the entry $(i, j)$ of the eliminated matrix is $M_{ij} - (M_{ip} / M_{pp}) M_{pj}$.
-/
theorem elimStep_apply_of_lt (M : Matrix n n K) {p i : n} (hi : p < i) (j : n) :
    elimStep M p i j = M i j - M i p * (M p p)⁻¹ * M p j := by
  rw [elimStep_apply, ite_eq_left hi]

/-- If $M_{pp} \neq 0$ and $i > p$, the entry $(i, p)$ of the eliminated matrix is $0$: the step
annihilates the pivot column below the pivot. -/
theorem elimStep_apply_pivot (M : Matrix n n K) {p i : n} (hi : p < i) (hp : M p p ≠ 0) :
    elimStep M p i p = 0 := by
  rw [elimStep_apply_of_lt M hi, mul_assoc, inv_mul_cancel₀ hp, mul_one, sub_self]

/-- If $M_{pj} = 0$, the step at the pivot $p$ does not change the column $j$: the entry $(i, j)$ of
the eliminated matrix is $M_{ij}$ for every $i$. -/
theorem elimStep_apply_of_pivot_row_eq_zero (M : Matrix n n K) (p i : n) {j : n}
    (hj : M p j = 0) : elimStep M p i j = M i j := by
  rw [elimStep_apply, hj, mul_zero, ite_self, sub_zero]

/-- The multiplier matrix squares to zero: $N^2 = 0$. -/
theorem elimMultipliers_mul_self (M : Matrix n n K) (p : n) :
    elimMultipliers M p * elimMultipliers M p = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases eq_or_ne c p with rfl | hc
  · simp
  · simp [hc]

/-- $(I + N)(I - N) = I$, for the multiplier matrix $N$. -/
theorem elimMul_mul_one_sub (M : Matrix n n K) (p : n) :
    elimMul M p * (1 - elimMultipliers M p) = 1 := by
  rw [elimMul, add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    elimMultipliers_mul_self, sub_zero]
  abel

/-- $(I - N)(I + N) = I$, for the multiplier matrix $N$. -/
theorem one_sub_mul_elimMul (M : Matrix n n K) (p : n) :
    (1 - elimMultipliers M p) * elimMul M p = 1 := by
  rw [elimMul, Matrix.mul_add, Matrix.mul_one, sub_mul, Matrix.one_mul,
    elimMultipliers_mul_self, sub_zero]
  abel

/-- The unipotent factor $I + N$ of an elimination step is invertible. -/
theorem isUnit_elimMul (M : Matrix n n K) (p : n) : IsUnit (elimMul M p) :=
  ⟨⟨_, _, elimMul_mul_one_sub M p, one_sub_mul_elimMul M p⟩, rfl⟩

/-- The inverse of the unipotent factor is $(I + N)^{-1} = I - N$. -/
theorem inv_elimMul (M : Matrix n n K) (p : n) :
    (elimMul M p)⁻¹ = 1 - elimMultipliers M p :=
  Matrix.inv_eq_right_inv (elimMul_mul_one_sub M p)

/-- **The factorization of one elimination step**: $M = G M'$, with $G = I + N$ the unipotent factor
and $M' = M - NM$ the eliminated matrix. -/
theorem elimMul_mul_elimStep (M : Matrix n n K) (p : n) : elimMul M p * elimStep M p = M := by
  rw [elimStep, elimMul, Matrix.mul_sub, add_mul, Matrix.one_mul, add_mul, Matrix.one_mul,
    ← Matrix.mul_assoc, elimMultipliers_mul_self, Matrix.zero_mul, add_zero]
  abel

end Step

/-! ### The Gaussian transformation matrices -/

variable {n K : Type*} [LinearOrder n] [Field K]

/-- The **Gaussian transformation matrix** $M_p = I - N$ at the pivot $p$, with $N$ the multiplier
matrix `Matrix.elimMultipliers M p`. It is the identity with the negated multipliers
$-M_{ip} / M_{pp}$, $i > p$, in the column $p$.

In [quarteroni2000numerical], §3.3.1, it is written $M_p = I - m_p e_p^T$. It is the inverse of
the unipotent factor `Matrix.elimMul` (`Matrix.inv_elimMul_eq_gaussTransform`), and left
multiplication by it is one elimination step (`Matrix.gaussTransform_mul`). -/
noncomputable def gaussTransform (M : Matrix n n K) (p : n) : Matrix n n K :=
  1 - elimMultipliers M p

variable [Fintype n]

/-- $M_p (I + N) = I$: the Gaussian transformation and the unipotent factor are inverse to each
other. This is $M_p^{-1} = 2I - M_p$, equation (3.36) of [quarteroni2000numerical]. -/
theorem gaussTransform_mul_elimMul (M : Matrix n n K) (p : n) :
    gaussTransform M p * elimMul M p = 1 :=
  one_sub_mul_elimMul M p

/-- $(I + N) M_p = I$, for the unipotent factor $I + N$ and the Gaussian transformation $M_p$. -/
theorem elimMul_mul_gaussTransform (M : Matrix n n K) (p : n) :
    elimMul M p * gaussTransform M p = 1 :=
  elimMul_mul_one_sub M p

/-- The inverse of the unipotent factor is the Gaussian transformation: $(I + N)^{-1} = M_p$. -/
theorem inv_elimMul_eq_gaussTransform (M : Matrix n n K) (p : n) :
    (elimMul M p)⁻¹ = gaussTransform M p :=
  inv_elimMul M p

/-- One elimination step is left multiplication by the Gaussian transformation: $M_p M = M - NM$,
where the right side is `Matrix.elimStep M p`.

This is equation (3.35) of [quarteroni2000numerical]. -/
theorem gaussTransform_mul (M : Matrix n n K) (p : n) : gaussTransform M p * M = elimStep M p := by
  rw [gaussTransform, elimStep, sub_mul, Matrix.one_mul]

/-! ### The stages of Gaussian elimination on `Fin N` -/

section Stages

variable {N : ℕ}

/-- The **stages of the Gaussian elimination method** on $A \in K^{N \times N}$: $A^{(0)} = A$, and
for $k < N$ the stage $A^{(k+1)}$ is one elimination step of $A^{(k)}$ at the pivot $(k, k)$,
$$a^{(k+1)}_{ij} = \begin{cases} a^{(k)}_{ij} - (a^{(k)}_{ik} / a^{(k)}_{kk}) a^{(k)}_{kj} &
  \text{if } i > k, \\ a^{(k)}_{ij} & \text{otherwise.} \end{cases}$$
For $k \ge N$ the stage does not change: $A^{(k+1)} = A^{(k)}$.

These are the matrices $A^{(k)}$ of equation (3.29) of [quarteroni2000numerical], numbered from
$0$ here and from $1$ in the source. Under the pivot hypothesis of
`Matrix.isLU_gemLower_gemStage`, the stage $A^{(N)}$ is the upper factor $U$. -/
noncomputable def gemStage (A : Matrix (Fin N) (Fin N) K) : ℕ → Matrix (Fin N) (Fin N) K
  | 0 => A
  | k + 1 => if h : k < N then elimStep (gemStage A k) ⟨k, h⟩ else gemStage A k

variable (A : Matrix (Fin N) (Fin N) K)

/-- $A^{(0)} = A$. -/
@[simp]
theorem gemStage_zero : gemStage A 0 = A := rfl

/-- For $k < N$, the stage $A^{(k+1)}$ is the elimination step of $A^{(k)}$ at the pivot $k$. -/
theorem gemStage_succ_of_lt {k : ℕ} (h : k < N) :
    gemStage A (k + 1) = elimStep (gemStage A k) ⟨k, h⟩ := by
  simp only [gemStage, h, dite_true]

/-- For $k \ge N$, $A^{(k+1)} = A^{(k)}$. -/
theorem gemStage_succ_of_le {k : ℕ} (h : N ≤ k) : gemStage A (k + 1) = gemStage A k := by
  simp only [gemStage, not_lt.2 h, dite_false]

/-- For $k < N$,
$$A^{(k+1)} = M_k A^{(k)},$$
where $M_k$ is the Gaussian transformation matrix of $A^{(k)}$ at the pivot $k$.

This is equation (3.35) of [quarteroni2000numerical], with the stages numbered from $0$. -/
theorem gemStage_succ_eq_gaussTransform_mul {k : ℕ} (h : k < N) :
    gemStage A (k + 1) = gaussTransform (gemStage A k) ⟨k, h⟩ * gemStage A k := by
  rw [gemStage_succ_of_lt A h, gaussTransform_mul]

/-- The stage $A^{(k+1)}$ differs from $A^{(k)}$ only in the rows $i > k$: if $i \le k$, then
$a^{(k+1)}_{ij} = a^{(k)}_{ij}$ for every $j$. -/
theorem gemStage_succ_apply_of_le {k : ℕ} {i : Fin N} (hi : (i : ℕ) ≤ k) (j : Fin N) :
    gemStage A (k + 1) i j = gemStage A k i j := by
  by_cases h : k < N
  · rw [gemStage_succ_of_lt A h, elimStep_apply_of_not_lt _ (by simpa [Fin.lt_def] using hi)]
  · rw [gemStage_succ_of_le A (not_lt.1 h)]

/-- The row $i$ does not change after the stage $i$: if $i \le k \le k'$, then
$$a^{(k')}_{ij} = a^{(k)}_{ij}$$
for every column $j$. -/
theorem gemStage_apply_of_le {k k' : ℕ} {i : Fin N} (hi : (i : ℕ) ≤ k) (hk : k ≤ k') (j : Fin N) :
    gemStage A k' i j = gemStage A k i j := by
  induction k', hk using Nat.le_induction with
  | base => rfl
  | succ k' hk ih => rw [gemStage_succ_apply_of_le A (hi.trans hk), ih]

/-- The shape of $A^{(k)}$: suppose that the pivots $a^{(m)}_{mm}$ are nonzero for every $m < k$
with $m + 1 < N$. Then $A^{(k)}$ vanishes below the diagonal in its first $k$ columns: if
$j < k$ and $j < i$, then
$$a^{(k)}_{ij} = 0.$$

This is the shape of the matrices $A^{(k)}$ in equation (3.29) of [quarteroni2000numerical]. -/
theorem gemStage_apply_eq_zero_of_lt {k : ℕ}
    (hpiv : ∀ (m : ℕ) (hm : m < N), m < k → m + 1 < N → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0)
    {i j : Fin N} (hjk : (j : ℕ) < k) (hji : j < i) : gemStage A k i j = 0 := by
  induction k generalizing i j with
  | zero => exact absurd hjk (Nat.not_lt_zero _)
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hjk | hjk
    · have ih' : ∀ {i j : Fin N}, (j : ℕ) < k → j < i → gemStage A k i j = 0 :=
        ih fun m hm hmk => hpiv m hm (hmk.trans (Nat.lt_succ_self k))
      by_cases hkN : k < N
      · rw [gemStage_succ_of_lt A hkN,
          elimStep_apply_of_pivot_row_eq_zero _ _ _ (ih' hjk (Fin.mk_lt_of_lt_val hjk))]
        exact ih' hjk hji
      · rw [gemStage_succ_of_le A (not_lt.1 hkN)]
        exact ih' hjk hji
    · subst hjk
      rw [gemStage_succ_of_lt A j.2]
      exact elimStep_apply_pivot _ hji (hpiv j j.2 (Nat.lt_succ_self _)
        (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Fin.lt_def.1 hji)) i.2))

/-- The **multiplier matrix of Gaussian elimination** on $A \in K^{N \times N}$: the matrix $L$ with
$$l_{ij} = \begin{cases} a^{(j)}_{ij} / a^{(j)}_{jj} & \text{if } j < i, \\ 1 & \text{if } i =
  j, \\ 0 & \text{if } i < j. \end{cases}$$
The entry below the diagonal is the multiplier that the stage $j$ produces in the position
$(i, j)$.

This is the matrix $L$ of equation (3.37) of [quarteroni2000numerical]. A zero pivot gives the
multiplier $0$. -/
noncomputable def gemLower : Matrix (Fin N) (Fin N) K :=
  of fun i j => if j < i then gemStage A j i j / gemStage A j j j else if i = j then 1 else 0

/-- The multiplier matrix $L$ of Gaussian elimination is unit lower triangular. -/
theorem isUnitLowerTriangular_gemLower : (gemLower A).IsUnitLowerTriangular := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [gemLower, hij'.not_gt, hij'.ne]
  · simp [gemLower]

/-- The **partial multiplier matrix** $L_k$ after $k$ stages: the unit lower triangular matrix with
the multiplier $a^{(j)}_{ij} / a^{(j)}_{jj}$ in each position $(i, j)$ with $j < i$ and $j < k$,
ones on the diagonal, and zeros elsewhere. -/
noncomputable def gemLowerStage (k : ℕ) : Matrix (Fin N) (Fin N) K :=
  of fun i j =>
    if j < i ∧ (j : ℕ) < k then gemStage A j i j / gemStage A j j j else if i = j then 1 else 0

/-- $L_0 = I$. -/
theorem gemLowerStage_zero : gemLowerStage A 0 = 1 := by
  ext i j
  simp [gemLowerStage, Matrix.one_apply]

/-- If $k \ge N$, then $L_k = L$, the multiplier matrix `Matrix.gemLower A`. -/
theorem gemLowerStage_of_le {k : ℕ} (hk : N ≤ k) : gemLowerStage A k = gemLower A := by
  ext i j
  simp [gemLowerStage, gemLower, j.2.trans_le hk]

/-- For $k < N$, one more stage multiplies the partial multiplier matrix by the unipotent factor of
that stage: $L_{k+1} = L_k G_k$, with $G_k$ the unipotent factor `Matrix.elimMul` of $A^{(k)}$
at the pivot $k$. The product appends the column $k$ of multipliers. -/
theorem gemLowerStage_succ {k : ℕ} (h : k < N) :
    gemLowerStage A (k + 1) = gemLowerStage A k * elimMul (gemStage A k) ⟨k, h⟩ := by
  ext i j
  rw [elimMul, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single i (fun r _ hri => ?_) (fun h => absurd (mem_univ i) h)]
  · simp only [gemLowerStage, of_apply, elimMultipliers_apply, lt_irrefl, false_and, ite_false,
      ite_true, one_mul]
    by_cases hj : j = ⟨k, h⟩
    · subst hj
      have : ¬ ((⟨k, h⟩ : Fin N) < i ∧ k < k) := fun h => lt_irrefl _ h.2
      simp only [this, ite_false, and_true]
      split_ifs with h1 h2 h3 <;> simp_all [div_eq_mul_inv]
    · have : ¬ (j : ℕ) = k := fun h' => hj (Fin.ext h')
      simp only [hj, and_false, ite_false, add_zero]
      congr 1
      apply propext
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  · simp only [elimMultipliers_apply]
    split_ifs with hr
    · obtain ⟨hkr, rfl⟩ := hr
      have : ¬ (r < i ∧ (r : ℕ) < k) := fun h' => absurd h'.2 (not_lt.2 (Fin.lt_def.1 hkr).le)
      simp [gemLowerStage, this, Ne.symm hri]
    · rw [mul_zero]

/-- For every $k$,
$$A = L_k A^{(k)},$$
with $L_k$ the partial multiplier matrix after $k$ stages. No pivot needs to be nonzero. -/
theorem gemLowerStage_mul_gemStage (k : ℕ) : gemLowerStage A k * gemStage A k = A := by
  induction k with
  | zero => rw [gemLowerStage_zero, gemStage_zero, Matrix.one_mul]
  | succ k ih =>
    by_cases h : k < N
    · rw [gemLowerStage_succ A h, gemStage_succ_of_lt A h, Matrix.mul_assoc, elimMul_mul_elimStep,
        ih]
    · have hN : N ≤ k := not_lt.1 h
      rw [gemStage_succ_of_le A hN, gemLowerStage_of_le A (hN.trans (Nat.le_succ k)),
        ← gemLowerStage_of_le A hN, ih]

/-- Each partial multiplier matrix $L_k$ is unit lower triangular. -/
theorem isUnitLowerTriangular_gemLowerStage (k : ℕ) :
    (gemLowerStage A k).IsUnitLowerTriangular := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [gemLowerStage, hij'.not_gt, hij'.ne]
  · simp [gemLowerStage]

/-- **Gaussian elimination as a factorization method.** Let $A \in K^{N \times N}$, and suppose that
the pivots $a^{(k)}_{kk}$ are nonzero for $k = 0, \dots, N - 2$. Then
$$A = LU,$$
with $L$ the unit lower triangular multiplier matrix `Matrix.gemLower A` and $U = A^{(N)}$ upper
triangular.

This is the factorization of [quarteroni2000numerical], §3.3.1 and equation (3.37). The last
pivot is never used as a divisor, so it may be zero. -/
theorem isLU_gemLower_gemStage
    (hpiv : ∀ (m : ℕ) (hm : m < N), m + 1 < N → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0) :
    IsLU A (gemLower A) (gemStage A N) where
  isUnitLowerTriangular := isUnitLowerTriangular_gemLower A
  isUpperTriangular := fun i j hij =>
    gemStage_apply_eq_zero_of_lt A (fun m hm _ hmN => hpiv m hm hmN) j.2 hij
  mul_eq := by rw [← gemLowerStage_of_le A le_rfl, gemLowerStage_mul_gemStage]

/-- Let $k < N$, and suppose that the pivots $a^{(m)}_{mm}$ are nonzero for every $m < k$ with
$m + 1 < N$. Then the leading principal submatrices of order $k + 1$ give an LU factorization
$$A(\le k) = L_k(\le k) \, A^{(k)}(\le k),$$
with $L_k$ the partial multiplier matrix: the block $A^{(k)}(\le k)$ is already upper
triangular. -/
theorem isLU_leadingPrincipalSubmatrix_gemStage {k : ℕ} (hk : k < N)
    (hpiv : ∀ (m : ℕ) (hm : m < N), m < k → m + 1 < N → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0) :
    IsLU (A.leadingPrincipalSubmatrix ⟨k, hk⟩)
      ((gemLowerStage A k).leadingPrincipalSubmatrix ⟨k, hk⟩)
      ((gemStage A k).leadingPrincipalSubmatrix ⟨k, hk⟩) where
  isUnitLowerTriangular :=
    ⟨(isUnitLowerTriangular_gemLowerStage A k).isLowerTriangular.submatrix,
     fun i => (isUnitLowerTriangular_gemLowerStage A k).diag_eq_one i.1⟩
  isUpperTriangular := fun i j hij =>
    gemStage_apply_eq_zero_of_lt A hpiv (Fin.lt_def.1 ((Subtype.coe_lt_coe.2 hij).trans_le i.2))
      (Subtype.coe_lt_coe.2 hij)
  mul_eq := by
    conv_rhs => rw [← gemLowerStage_mul_gemStage A k]
    unfold leadingPrincipalSubmatrix
    rw [toBlock_mul_eq_add' _ (· ≤ ⟨k, hk⟩),
      (isUnitLowerTriangular_gemLowerStage A k).isLowerTriangular.toBlock_not_eq_zero
        (fun _ _ hi hji => hji.trans hi), Matrix.zero_mul, add_zero]

/-- **The pivots are nonzero if and only if the strict leading principal submatrices are
nonsingular.** For $A \in K^{N \times N}$, the pivots $a^{(k)}_{kk}$ are nonzero for
$k = 0, \dots, N - 2$ if and only if every strict leading principal submatrix $A(< k)$,
$k = 0, \dots, N - 1$, is nonsingular.

This is the sentence after equation (3.33) of [quarteroni2000numerical]. The last pivot
$a^{(N-1)}_{N-1,N-1}$ must be excluded: it is $\det A / \det A(< N - 1)$, so it vanishes for a
singular $A$ with nonsingular strict leading blocks, such as $B = \begin{bmatrix} 1 & 2 \\ 1 & 2
\end{bmatrix}$ of Example 3.3 of [quarteroni2000numerical]. In one direction, $\det A(< k)$ is
the product of the pivots $a^{(m)}_{mm}$ with $m < k$. In the other direction, a strong
induction uses $A = L_k A^{(k)}$ on the leading block of order $k + 1$, whose determinant is the
product of the pivots $a^{(m)}_{mm}$ with $m \le k$. -/
theorem gemStage_pivots_ne_zero_iff :
    (∀ (m : ℕ) (hm : m < N), m + 1 < N → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0) ↔
      A.HasUnitStrictLeadingPrincipalSubmatrices := by
  constructor
  · intro hpiv k
    have h := isLU_gemLower_gemStage A hpiv
    rw [isUnit_iff_isUnit_det, h.det_strictLeadingPrincipalSubmatrix, isUnit_iff_ne_zero,
      Finset.prod_ne_zero_iff]
    intro i hi
    have hik : i < k := (mem_filter.1 hi).2
    rw [gemStage_apply_of_le A le_rfl i.2.le]
    exact hpiv i i.2 (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Fin.lt_def.1 hik)) k.2)
  · intro hA m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm hmN
    have hLU := isLU_leadingPrincipalSubmatrix_gemStage A hm
      fun m' hm' hm'm hm'N => ih m' hm'm hm' hm'N
    have hunit : IsUnit (A.leadingPrincipalSubmatrix ⟨m, hm⟩) := by
      have := hA ⟨m + 1, hmN⟩
      unfold strictLeadingPrincipalSubmatrix at this
      unfold leadingPrincipalSubmatrix
      exact (isUnit_toBlock_congr A fun i => by simp [Fin.lt_def, Fin.le_def]).1 this
    have hdet : (∏ i, (gemStage A m).leadingPrincipalSubmatrix ⟨m, hm⟩ i i) ≠ 0 := by
      rw [← hLU.det_eq_prod_diag]
      -- `convert` reconciles the two `DecidableEq` instances on the index subtype
      convert isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1 hunit)
    rw [Finset.prod_ne_zero_iff] at hdet
    exact hdet ⟨⟨m, hm⟩, le_rfl⟩ (mem_univ _)

end Stages

/-!
### Restriction to a block of indices

Elimination is local: the entry $(i, j)$ of one step depends only on the entries in the positions
$(i, j)$, $(i, p)$, $(p, p)$ and $(p, j)$. So the step commutes with the restriction to any set of
indices carried by an order embedding, and with any permutation of the columns that fixes the pivot.
For the consecutive block $k, \dots, k + j - 1$ of `Matrix.blockEmb`, this says that the elimination
of a trailing block of $A^{(k)}$ is the restriction of the global elimination.
-/

/-- Let $\rho$ be a permutation of the indices with $\rho(p) = p$. Then one elimination step at $p$
commutes with the permutation of the columns by $\rho$: the step at $p$ of the matrix with the
entries $M_{i \rho(j)}$ is the matrix with the entries $M'_{i \rho(j)}$, where $M'$ is the step
of $M$ at $p$. -/
theorem elimStep_submatrix_id_of_apply_self {m : Type*} [LinearOrder m] [Fintype m]
    (M : Matrix m m K) {p : m} {ρ : Equiv.Perm m} (hρ : ρ p = p) :
    elimStep (M.submatrix id ρ) p = (elimStep M p).submatrix id ρ := by
  ext i j
  simp only [elimStep_apply, submatrix_apply, id, hρ]

/-- The order embedding $\{0, \dots, j - 1\} \to \{0, \dots, N - 1\}$, $i \mapsto k + i$, of the
block of $j$ consecutive indices that starts at $k$, for $k + j \le N$. -/
def blockEmb (k j N : ℕ) (h : k + j ≤ N) : Fin j ↪o Fin N :=
  OrderEmbedding.ofStrictMono (fun i => ⟨k + i, by have := i.isLt; omega⟩)
    (fun a b hab => by simp only [Fin.lt_def] at hab ⊢; omega)

/-- `Matrix.blockEmb k j N h` maps $i$ to $k + i$. -/
@[simp]
theorem blockEmb_apply {k j N : ℕ} (h : k + j ≤ N) (i : Fin j) (hki : k + (i : ℕ) < N) :
    blockEmb k j N h i = ⟨k + (i : ℕ), hki⟩ := rfl

/-- One elimination step commutes with the restriction to a set of indices carried by an order
embedding. Let $m$ and $n$ be finite linear orders, let $e \colon m \to n$ be an order
embedding, let $M \in K^{n \times n}$, and let $p \in m$. Then the step at $p$ of the
restriction $(M_{e(i) e(j)})_{i, j \in m}$ is the restriction along $e$ of the step of $M$ at
$e(p)$.

The entry $(i, j)$ of a step uses only the entries in the positions $(i, j)$, $(i, p)$, $(p, p)$
and $(p, j)$, which all lie in the block. -/
theorem elimStep_submatrix_orderEmbedding {m n K : Type*} [LinearOrder m] [Fintype m]
    [LinearOrder n] [Fintype n] [Field K] (M : Matrix n n K) (e : m ↪o n) (p : m) :
    elimStep (M.submatrix e e) p = (elimStep M (e p)).submatrix e e := by
  ext i j
  simp only [elimStep_apply, submatrix_apply, e.lt_iff_lt]

/-- **Gaussian elimination on a trailing block is the restriction of the global elimination.** Let
$A \in K^{N \times N}$ and $k + j \le N$, and let $B$ be the block of $A^{(k)}$ on the indices
$k, \dots, k + j - 1$. Then for every $t \le j$, the stage $B^{(t)}$ of Gaussian elimination on
$B$ is the block of $A^{(k + t)}$ on the same indices.

The block is taken along `Matrix.blockEmb`. -/
theorem gemStage_submatrix_blockEmb {K : Type*} [Field K] {N : ℕ} (A : Matrix (Fin N) (Fin N) K)
    {k j : ℕ} (h : k + j ≤ N) :
    ∀ t ≤ j, gemStage ((gemStage A k).submatrix (blockEmb k j N h) (blockEmb k j N h)) t =
      (gemStage A (k + t)).submatrix (blockEmb k j N h) (blockEmb k j N h) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have htj : t < j := by omega
    have hkt : k + t < N := by omega
    rw [gemStage_succ_of_lt _ htj, ih (by omega), elimStep_submatrix_orderEmbedding]
    have he : blockEmb k j N h ⟨t, htj⟩ = (⟨k + t, hkt⟩ : Fin N) := rfl
    rw [he, ← gemStage_succ_of_lt A hkt, Nat.add_assoc]

/-! ### The Doolittle recurrence -/

/-- The **Doolittle recurrence** in packed form, on a finite linear order. The function $\pi$ holds
both factors: for $i \le j$, $\pi_{ij}$ is the entry $u_{ij}$ of the upper factor, and for
$j < i$ it is the entry $l_{ij}$ of the unit lower factor. It is defined by
$$\pi_{ij} = a_{ij} - \sum_{r < i} \pi_{ir} \pi_{rj} \quad (i \le j), \qquad \pi_{ij} =
  \frac{1}{\pi_{jj}} \Big( a_{ij} - \sum_{r < j} \pi_{ir} \pi_{rj} \Big) \quad (j < i).$$

This is the recurrence (3.43) of [quarteroni2000numerical], as one total function. The recursion
is well founded on the number of indices below $\min(i, j)$, and at the same value the entries
$l$ come after the entries $u$. A zero pivot $\pi_{jj} = 0$ gives the value $0$, since division
by zero is $0$ in Lean. `Matrix.isLU_luLower_luUpper` says when the result is the LU
factorization. -/
noncomputable def luPacked (A : Matrix n n K) : n → n → K
  | i, j =>
    if j < i then
      (A i j - ∑ r ∈ (univ.filter (· < j)).attach, luPacked A i r * luPacked A r j) /
        luPacked A j j
    else A i j - ∑ r ∈ (univ.filter (· < i)).attach, luPacked A i r * luPacked A r j
termination_by i j => (#{k | k < min i j}, if j < i then 1 else 0)
decreasing_by
  · have hr : (r : n) < j := (mem_filter.1 r.2).2
    rw [min_eq_right (hr.trans ‹j < i›).le, min_eq_right ‹j < i›.le]
    exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr)
  · have hr : (r : n) < j := (mem_filter.1 r.2).2
    rw [min_eq_left hr.le, min_eq_right ‹j < i›.le]
    exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr)
  · rw [min_self, min_eq_right ‹j < i›.le]
    exact Prod.Lex.right _ (by simp [‹j < i›])
  · have hr : (r : n) < i := (mem_filter.1 r.2).2
    rw [min_eq_right hr.le, min_eq_left (not_lt.1 ‹¬ j < i›)]
    exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr)
  · have hr : (r : n) < i := (mem_filter.1 r.2).2
    rw [min_eq_left (hr.le.trans (not_lt.1 ‹¬ j < i›)), min_eq_left (not_lt.1 ‹¬ j < i›)]
    exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr)

section Doolittle

variable (A : Matrix n n K)

/-- The Doolittle recurrence for the upper factor: if $i \le j$, then $\pi_{ij} = a_{ij} - \sum_{r <
i} \pi_{ir} \pi_{rj}$. -/
theorem luPacked_of_le {i j : n} (hij : i ≤ j) :
    luPacked A i j = A i j - ∑ r ∈ univ.filter (· < i), luPacked A i r * luPacked A r j := by
  rw [luPacked, ite_eq_right (not_lt.2 hij),
    Finset.sum_attach (univ.filter (· < i)) fun r => luPacked A i r * luPacked A r j]

/-- The Doolittle recurrence for the lower factor: if $j < i$, then
$$\pi_{ij} = \frac{1}{\pi_{jj}} \Big( a_{ij} - \sum_{r < j} \pi_{ir} \pi_{rj} \Big).$$
-/
theorem luPacked_of_lt {i j : n} (hij : j < i) :
    luPacked A i j =
      (A i j - ∑ r ∈ univ.filter (· < j), luPacked A i r * luPacked A r j) / luPacked A j j := by
  rw [luPacked, ite_eq_left hij,
    Finset.sum_attach (univ.filter (· < j)) fun r => luPacked A i r * luPacked A r j]

/-- The **Doolittle lower factor**: the unit lower triangular matrix with the entries $\pi_{ij}$ of
the packed recurrence `Matrix.luPacked A` below the diagonal and ones on the diagonal. -/
noncomputable def luLower : Matrix n n K :=
  of fun i j => if j < i then luPacked A i j else if i = j then 1 else 0

/-- The **Doolittle upper factor**: the upper triangular matrix with the entries $\pi_{ij}$,
$i \le j$, of the packed recurrence `Matrix.luPacked A` on and above the diagonal. -/
noncomputable def luUpper : Matrix n n K :=
  of fun i j => if i ≤ j then luPacked A i j else 0

/-- **Correctness of the Doolittle recurrence.** Let $A = LU$ be an LU factorization, and suppose
that every strict leading principal submatrix of $A$ is nonsingular. Then for every $m$ and all
indices $i, j$ with $\min(i, j) = m$, the packed recurrence satisfies $\pi_{ij} = u_{ij}$ if
$i \le j$ and $\pi_{ij} = l_{ij}$ if $j < i$.

The statement is fixed at one value $m$ of $\min(i, j)$, so that it can be proved by strong
induction on $m$. The recurrence equations are the entrywise identities
`Matrix.IsLU.upper_apply_eq` and `Matrix.IsLU.lower_apply_mul_diag_eq` of any LU factorization.
This is the recurrence (3.43) of [quarteroni2000numerical]. -/
theorem luPacked_eq {L U : Matrix n n K} (h : IsLU A L U)
    (hA : A.HasUnitStrictLeadingPrincipalSubmatrices) (m : n) :
    ∀ i j, min i j = m → (i ≤ j → luPacked A i j = U i j) ∧ (j < i → luPacked A i j = L i j) := by
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  have hU : ∀ i j, min i j = m → i ≤ j → luPacked A i j = U i j := by
    intro i j hm hij
    rw [luPacked_of_le A hij, h.upper_apply_eq hij]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := (mem_filter.1 hr).2
    have hrm : r < m := by rw [← hm, min_eq_left hij]; exact hr'
    rw [(ih r hrm i r (min_eq_right hr'.le)).2 hr',
      (ih r hrm r j (min_eq_left (hr'.le.trans hij))).1 (hr'.le.trans hij)]
  refine fun i j hm => ⟨hU i j hm, fun hij => ?_⟩
  have hjm : j = m := (min_eq_right hij.le).symm.trans hm
  rw [luPacked_of_lt A hij, hU j j (by rw [min_self]; exact hjm) le_rfl,
    div_eq_iff (h.diag_upper_ne_zero_of_lt (hA i) hij), h.lower_apply_mul_diag_eq hij]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := (mem_filter.1 hr).2
  have hrm : r < m := hjm ▸ hr'
  rw [(ih r hrm i r (min_eq_right (hr'.trans hij).le)).2 (hr'.trans hij),
    (ih r hrm r j (min_eq_left hr'.le)).1 hr'.le]

/-- **Correctness of the Doolittle factorization.** If every strict leading principal submatrix of
$A$ is nonsingular, then the Doolittle factors form an LU factorization: `Matrix.luLower A` is
unit lower triangular, `Matrix.luUpper A` is upper triangular, and their product is $A$. -/
theorem isLU_luLower_luUpper (hA : A.HasUnitStrictLeadingPrincipalSubmatrices) :
    IsLU A (luLower A) (luUpper A) := by
  obtain ⟨L, U, h⟩ := exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix hA
  have hL : luLower A = L := by
    ext i j
    simp only [luLower, of_apply]
    split_ifs with hij hij'
    · exact (luPacked_eq A h hA _ i j rfl).2 hij
    · subst hij'
      exact (h.isUnitLowerTriangular.diag_eq_one i).symm
    · exact (h.isUnitLowerTriangular.isLowerTriangular (OrderDual.toDual_lt_toDual.2
        (lt_of_le_of_ne (not_lt.1 hij) hij'))).symm
  have hU : luUpper A = U := by
    ext i j
    simp only [luUpper, of_apply]
    split_ifs with hij
    · exact (luPacked_eq A h hA _ i j rfl).1 hij
    · exact (h.isUpperTriangular (not_le.1 hij)).symm
  rw [hL, hU]
  exact h

end Doolittle

/-- **The Doolittle factors are the factors of Gaussian elimination.** Let $A \in K^{N \times N}$,
and suppose that the pivots $a^{(k)}_{kk}$ are nonzero for $k = 0, \dots, N - 2$. Then the
Doolittle lower factor is the multiplier matrix `Matrix.gemLower A`, and the Doolittle upper
factor is the last stage $A^{(N)}$.

This expresses the remark of [quarteroni2000numerical], §3.3.4, that "the Doolittle
factorization is nothing but the $ijk$ version of GEM". The proof uses the uniqueness of the LU
factorization. -/
theorem luLower_eq_gemLower {N : ℕ} (A : Matrix (Fin N) (Fin N) K)
    (hpiv : ∀ (m : ℕ) (hm : m < N), m + 1 < N → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0) :
    luLower A = gemLower A ∧ luUpper A = gemStage A N :=
  (isLU_luLower_luUpper A ((gemStage_pivots_ne_zero_iff A).1 hpiv)).unique
    (isLU_gemLower_gemStage A hpiv) ((gemStage_pivots_ne_zero_iff A).1 hpiv)

/-! ### The Crout factorization -/

section Crout

variable (A : Matrix n n K)

/-- The **Crout lower factor** $(U')^T$, where $U'$ is the Doolittle upper factor of $A^T$. It is
lower triangular.

The Crout factorization of [quarteroni2000numerical], §3.3.4, is the factorization with
$u_{kk} = 1$. -/
noncomputable def croutLower : Matrix n n K := (luUpper Aᵀ)ᵀ

/-- The **Crout upper factor** $(L')^T$, where $L'$ is the Doolittle lower factor of $A^T$. It is
unit upper triangular. -/
noncomputable def croutUpper : Matrix n n K := (luLower Aᵀ)ᵀ

/-- **The Crout factorization.** If every strict leading principal submatrix of $A$ is nonsingular,
then
$$A = L U,$$
with $L$ the Crout lower factor, which is lower triangular, and $U$ the Crout upper factor,
which is unit upper triangular.

Unit upper triangularity is stated as: the transpose of $U$ is unit lower triangular. -/
theorem croutLower_mul_croutUpper (hA : A.HasUnitStrictLeadingPrincipalSubmatrices) :
    croutLower A * croutUpper A = A ∧ (croutLower A).IsLowerTriangular ∧
      (croutUpper A)ᵀ.IsUnitLowerTriangular := by
  have h := isLU_luLower_luUpper Aᵀ hA.transpose
  refine ⟨?_, h.isUpperTriangular.transpose, ?_⟩
  · rw [croutLower, croutUpper, ← transpose_mul, h.mul_eq, transpose_transpose]
  · rw [croutUpper, transpose_transpose]
    exact h.isUnitLowerTriangular

end Crout

end Matrix
