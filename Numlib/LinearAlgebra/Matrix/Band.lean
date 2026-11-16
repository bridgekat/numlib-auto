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
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.RingTheory.Nilpotent.Basic
import Numlib.LinearAlgebra.Matrix.Triangular

/-!
# Band matrices

Let $A$ be a square matrix indexed by a finite linear order $n$. For indices $j, i$, write $[j, i)$
for the set of indices $k$ with $j \le k < i$. The matrix $A$ has **lower bandwidth** $p$ if
$A_{ij} = 0$ whenever $[j, i)$ contains more than $p$ indices, and **upper bandwidth** $q$ if
$A_{ij} = 0$ whenever $[i, j)$ contains more than $q$ indices. On the index set
$\{0, \dots, N - 1\}$ the interval $[j, i)$ has $i - j$ elements, so these are the usual conditions
"$A_{ij} = 0$ for $i > j + p$" and "$A_{ij} = 0$ for $j > i + q$" of [quarteroni2000numerical],
§1.6.3, and [golub2013matrix], §1.2.1. For a rectangular matrix indexed by
$\{0, \dots, M - 1\} \times \{0, \dots, N - 1\}$, the same conditions are stated with natural-number
indices.

Bandwidth $0$ gives the triangular shapes, and both bandwidths $0$ give the diagonal matrices.
Bandwidth $1$ gives the Hessenberg, tridiagonal and bidiagonal shapes of
`Numlib.LinearAlgebra.Matrix.Hessenberg`. Sums keep the larger bandwidth, products add bandwidths,
and transposition exchanges the lower and the upper bandwidth. Finally, a matrix whose nonzero
entries strictly increase a bounded potential is nilpotent, so $1 + M$ is invertible; this covers
the strictly triangular and strictly banded shapes for an order of the indices other than the
natural one.

## Main definitions

* `Matrix.HasLowerBandwidth`, `Matrix.HasUpperBandwidth`: lower bandwidth $p$ and upper bandwidth
  $q$ of a square matrix indexed by a finite linear order.
* `Matrix.HasLowerBandwidthRect`, `Matrix.HasUpperBandwidthRect`: lower bandwidth $p$ and upper
  bandwidth $q$ of a rectangular matrix, $A_{ij} = 0$ for $i > j + p$, respectively for $j > i + q$.

## Main results

* `Matrix.hasLowerBandwidth_iff_fin`: on $\{0, \dots, N - 1\}$, lower bandwidth $p$ means
  $A_{ij} = 0$ whenever $i > j + p$.
* `Matrix.hasLowerBandwidth_zero_iff`, `Matrix.hasUpperBandwidth_zero_iff`: lower bandwidth $0$ is
  upper triangularity, and upper bandwidth $0$ is lower triangularity.
* `Matrix.isDiag_iff_hasBandwidth_zero`: a matrix is diagonal if and only if both its bandwidths are
  $0$.
* `Matrix.HasLowerBandwidth.add`, `Matrix.HasLowerBandwidth.mul`: $A + B$ has lower bandwidth
  $\max(p, p')$, and $AB$ has lower bandwidth $p + p'$; the same holds for the upper bandwidths.
* `Matrix.hasLowerBandwidth_transpose_iff`, `Matrix.hasUpperBandwidth_transpose_iff`: $A^T$ has
  lower bandwidth $p$ if and only if $A$ has upper bandwidth $p$, and conversely; the rectangular
  forms are `Matrix.hasLowerBandwidthRect_transpose_iff` and
  `Matrix.hasUpperBandwidthRect_transpose_iff`.
* `Matrix.hasLowerBandwidthRect_iff`, `Matrix.hasUpperBandwidthRect_iff`: on a square matrix the
  rectangular bandwidths agree with the order-theoretic ones.
* `Matrix.pow_apply_eq_zero_of_potential`, `Matrix.isUnit_one_add_of_potential`: if $M_{ij} = 0$
  whenever $f(j) \le f(i)$ for a bounded $f \colon \iota \to \mathbb{N}$, then $M$ is nilpotent and
  $1 + M$ is a unit.

## Implementation notes

* On a general finite linear order the definitions count indices in an interval and need no
  arithmetic on the indices, as in `Matrix.IsUpperHessenberg`. The count $|[j, i)|$ is
  `#{k | j ≤ k ∧ k < i}`.
* The rectangular predicates are stated on `Matrix (Fin M) (Fin N) R`, with the index difference
  taken in $\mathbb{N}$. Section 1.2.1 of [golub2013matrix] defines bandwidths for $m \times n$
  matrices (Table 1.2.1), and the bidiagonal and banded shapes of the singular value decomposition
  and of band LU factorization are rectangular.
* A product with lower bandwidth $p + p'$ is how the product $LU$ is read back in banded storage.
-/

namespace Matrix

variable {n R : Type*} [LinearOrder n]

/-! ### Counting indices in an interval -/

section Counts

open Finset

variable [Fintype n]

/-- On a finite linear order, the interval $[j, i)$ is nonempty if and only if $j < i$. -/
theorem card_filter_le_lt_pos_iff (i j : n) :
    0 < #{k | j ≤ k ∧ k < i} ↔ j < i := by
  rw [Finset.card_pos]
  constructor
  · rintro ⟨k, hk⟩
    simp only [mem_filter, mem_univ, true_and] at hk
    exact hk.1.trans_lt hk.2
  · intro h
    exact ⟨j, by simp [h]⟩

/-- On a finite linear order, the interval $[j, i)$ contains more than one index if and only if some
index $k$ satisfies $j < k < i$. -/
theorem one_lt_card_filter_le_lt_iff (i j : n) :
    1 < #{k | j ≤ k ∧ k < i} ↔ ∃ k, j < k ∧ k < i := by
  rw [Finset.one_lt_card]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [mem_filter, mem_univ, true_and] at ha hb
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨b, ha.1.trans_lt h, hb.2⟩
    · exact ⟨a, hb.1.trans_lt h, ha.2⟩
  · rintro ⟨k, hk₁, hk₂⟩
    exact ⟨j, by simp [hk₁.trans hk₂], k, by simp [hk₁.le, hk₂], hk₁.ne⟩

/-- On a finite linear order, for all indices $i, j, l$, the number of indices in $[j, i)$ is at
most the number in $[j, l)$ plus the number in $[l, i)$. -/
theorem card_filter_le_lt_le_add (i j l : n) :
    #{k | j ≤ k ∧ k < i} ≤ #{k | j ≤ k ∧ k < l} + #{k | l ≤ k ∧ k < i} := by
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro k hk
  simp only [mem_filter, mem_univ, true_and, mem_union] at hk ⊢
  rcases lt_or_ge k l with h | h
  · exact Or.inl ⟨hk.1, h⟩
  · exact Or.inr ⟨h, hk.2⟩

/-- On a finite linear order, if $j' \le j$ and $i \le i'$, then $[j', i')$ contains at least as
many indices as $[j, i)$. -/
theorem card_filter_le_lt_mono {i i' j j' : n} (hj : j' ≤ j) (hi : i ≤ i') :
    #{k | j ≤ k ∧ k < i} ≤ #{k | j' ≤ k ∧ k < i'} := by
  refine Finset.card_le_card fun k hk => ?_
  simp only [mem_filter, mem_univ, true_and] at hk ⊢
  exact ⟨hj.trans hk.1, hk.2.trans_le hi⟩

/-- On a finite linear order $n$, the interval $[j, i)$ does not contain $i$, so it contains at most
$|n| - 1$ indices. -/
theorem card_filter_le_lt_le_card_sub_one (i j : n) :
    #{k | j ≤ k ∧ k < i} ≤ Fintype.card n - 1 := by
  rw [← Finset.card_univ, ← Finset.card_erase_of_mem (mem_univ i)]
  refine Finset.card_le_card fun k hk => ?_
  simp only [mem_filter, mem_univ, true_and, mem_erase, and_true] at hk ⊢
  exact hk.2.ne

/-- On $\{0, \dots, N - 1\}$, the interval $[j, i)$ contains $i - j$ indices, with truncated
subtraction of natural numbers. -/
theorem card_filter_le_lt_fin {N : ℕ} (i j : Fin N) : #{k | j ≤ k ∧ k < i} = i - j := by
  rw [← Fin.card_Ico]
  congr 1
  ext k
  simp [Finset.mem_Ico]

end Counts

/-! ### Bandwidths of a square matrix -/

section Bandwidth

open Finset

variable [Fintype n] [Zero R]

/-- A square matrix $A$ indexed by a finite linear order has **lower bandwidth** $p$ if $A_{ij} = 0$
whenever the half-open interval $[j, i)$ contains more than $p$ indices.

On $\{0, \dots, N - 1\}$ the interval contains $i - j$ indices, so this is the condition
"$A_{ij} = 0$ for $i > j + p$" of [quarteroni2000numerical], §1.6.3 (see
`Matrix.hasLowerBandwidth_iff_fin`). Lower bandwidth $0$ is upper triangularity, and lower
bandwidth $1$ is the upper Hessenberg shape. -/
def HasLowerBandwidth (A : Matrix n n R) (p : ℕ) : Prop :=
  ∀ i j, p < #{k | j ≤ k ∧ k < i} → A i j = 0

/-- A square matrix $A$ indexed by a finite linear order has **upper bandwidth** $q$ if $A_{ij} = 0$
whenever the half-open interval $[i, j)$ contains more than $q$ indices.

On $\{0, \dots, N - 1\}$ this is the condition "$A_{ij} = 0$ for $j > i + q$" of
[quarteroni2000numerical], §1.6.3. Upper bandwidth $0$ is lower triangularity. The upper
bandwidth of $A$ is the lower bandwidth of $A^T$ (see `Matrix.hasLowerBandwidth_transpose_iff`). -/
def HasUpperBandwidth (A : Matrix n n R) (q : ℕ) : Prop :=
  ∀ i j, q < #{k | i ≤ k ∧ k < j} → A i j = 0

variable {A B : Matrix n n R} {p q : ℕ}

/-- The transpose $A^T$ has lower bandwidth $p$ if and only if $A$ has upper bandwidth $p$. -/
theorem hasLowerBandwidth_transpose_iff : Aᵀ.HasLowerBandwidth p ↔ A.HasUpperBandwidth p :=
  forall_comm

/-- The transpose $A^T$ has upper bandwidth $q$ if and only if $A$ has lower bandwidth $q$. -/
theorem hasUpperBandwidth_transpose_iff : Aᵀ.HasUpperBandwidth q ↔ A.HasLowerBandwidth q :=
  forall_comm

/-- A square matrix $A$ indexed by $\{0, \dots, N - 1\}$ has lower bandwidth $p$ if and only if
$A_{ij} = 0$ whenever $i > j + p$. -/
theorem hasLowerBandwidth_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.HasLowerBandwidth p ↔ ∀ i j : Fin N, (j : ℕ) + p < (i : ℕ) → A i j = 0 := by
  simp only [HasLowerBandwidth, card_filter_le_lt_fin]
  exact forall₂_congr fun i j => by constructor <;> intro h hij <;> apply h <;> omega

/-- A square matrix $A$ indexed by $\{0, \dots, N - 1\}$ has upper bandwidth $q$ if and only if
$A_{ij} = 0$ whenever $j > i + q$. -/
theorem hasUpperBandwidth_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.HasUpperBandwidth q ↔ ∀ i j : Fin N, (i : ℕ) + q < (j : ℕ) → A i j = 0 := by
  simp only [HasUpperBandwidth, card_filter_le_lt_fin]
  exact forall₂_congr fun i j => by constructor <;> intro h hij <;> apply h <;> omega

/-- If $A$ has lower bandwidth $p$ and $p \le q$, then $A$ has lower bandwidth $q$. -/
theorem HasLowerBandwidth.mono (h : A.HasLowerBandwidth p) (hpq : p ≤ q) :
    A.HasLowerBandwidth q := fun i j hij => h i j (hpq.trans_lt hij)

/-- If $A$ has upper bandwidth $p$ and $p \le q$, then $A$ has upper bandwidth $q$. -/
theorem HasUpperBandwidth.mono (h : A.HasUpperBandwidth p) (hpq : p ≤ q) :
    A.HasUpperBandwidth q := fun i j hij => h i j (hpq.trans_lt hij)

/-- Every square matrix indexed by a finite linear order $n$ has lower bandwidth $|n| - 1$. -/
theorem hasLowerBandwidth_card_sub_one : A.HasLowerBandwidth (Fintype.card n - 1) :=
  fun i j hij => absurd (card_filter_le_lt_le_card_sub_one i j) (not_le.2 hij)

/-- Every square matrix indexed by a finite linear order $n$ has upper bandwidth $|n| - 1$. -/
theorem hasUpperBandwidth_card_sub_one : A.HasUpperBandwidth (Fintype.card n - 1) :=
  fun i j hij => absurd (card_filter_le_lt_le_card_sub_one j i) (not_le.2 hij)

/-- A square matrix has lower bandwidth $0$ if and only if it is upper triangular
([quarteroni2000numerical], §1.6.2–1.6.3). -/
theorem hasLowerBandwidth_zero_iff : A.HasLowerBandwidth 0 ↔ A.IsUpperTriangular := by
  simp only [HasLowerBandwidth, card_filter_le_lt_pos_iff]
  exact ⟨fun h i j hij => h i j hij, fun h i j hij => h hij⟩

/-- A square matrix has upper bandwidth $0$ if and only if it is lower triangular. -/
theorem hasUpperBandwidth_zero_iff : A.HasUpperBandwidth 0 ↔ A.IsLowerTriangular := by
  simp only [HasUpperBandwidth, card_filter_le_lt_pos_iff]
  exact ⟨fun h i j hij => h i j hij, fun h i j hij => h hij⟩

/-- A square matrix is diagonal if and only if its lower bandwidth and its upper bandwidth are both
$0$. -/
theorem isDiag_iff_hasBandwidth_zero :
    A.IsDiag ↔ A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth 0 := by
  rw [hasLowerBandwidth_zero_iff, hasUpperBandwidth_zero_iff]
  refine ⟨fun h => ⟨fun i j hij => h (hij : j < i).ne',
    fun i j hij => h (OrderDual.toDual_lt_toDual.1 hij).ne⟩, fun h i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact h.2 hlt
  · exact h.1 hlt

/-- If $A$ has lower bandwidth $p$, then its strict lower triangular part has lower bandwidth $p$.
-/
theorem HasLowerBandwidth.strictLower (h : A.HasLowerBandwidth p) :
    (strictLower A).HasLowerBandwidth p := fun i j hij => by
  rw [strictLower_apply, h i j hij, ite_self]

/-- If $A$ has upper bandwidth $q$, then its strict upper triangular part has upper bandwidth $q$.
-/
theorem HasUpperBandwidth.strictUpper (h : A.HasUpperBandwidth q) :
    (strictUpper A).HasUpperBandwidth q := fun i j hij => by
  rw [strictUpper_apply, h i j hij, ite_self]

/-- The strict upper triangular part of a square matrix has lower bandwidth $0$. -/
theorem strictUpper_hasLowerBandwidth_zero : (strictUpper A).HasLowerBandwidth 0 :=
  hasLowerBandwidth_zero_iff.2 (strictUpper_blockTriangular A)

/-- The strict lower triangular part of a square matrix has upper bandwidth $0$. -/
theorem strictLower_hasUpperBandwidth_zero : (strictLower A).HasUpperBandwidth 0 :=
  hasUpperBandwidth_zero_iff.2 (strictLower_blockTriangular A)

/-- The diagonal part of a square matrix has lower bandwidth $0$. -/
theorem diagPart_hasLowerBandwidth_zero : (diagPart A).HasLowerBandwidth 0 :=
  hasLowerBandwidth_zero_iff.2 (blockTriangular_diagonal _)

/-- The diagonal part of a square matrix has upper bandwidth $0$. -/
theorem diagPart_hasUpperBandwidth_zero : (diagPart A).HasUpperBandwidth 0 :=
  hasUpperBandwidth_zero_iff.2 (blockTriangular_diagonal _)

end Bandwidth

/-! ### The algebra of bandwidths -/

section BandwidthAlgebra

open Finset

variable [Fintype n] {p p' q q' : ℕ}

/-- If $A$ has lower bandwidth $p$ and $B$ has lower bandwidth $p'$, then $A + B$ has lower
bandwidth $\max(p, p')$. -/
theorem HasLowerBandwidth.add [AddZeroClass R] {A B : Matrix n n R} (hA : A.HasLowerBandwidth p)
    (hB : B.HasLowerBandwidth p') : (A + B).HasLowerBandwidth (max p p') := fun i j hij => by
  rw [Matrix.add_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), add_zero]

/-- If $A$ has upper bandwidth $q$ and $B$ has upper bandwidth $q'$, then $A + B$ has upper
bandwidth $\max(q, q')$. -/
theorem HasUpperBandwidth.add [AddZeroClass R] {A B : Matrix n n R} (hA : A.HasUpperBandwidth q)
    (hB : B.HasUpperBandwidth q') : (A + B).HasUpperBandwidth (max q q') := fun i j hij => by
  rw [Matrix.add_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), add_zero]

/-- If $A$ has lower bandwidth $p$, then $cA$ has lower bandwidth $p$ for every scalar $c$. -/
theorem HasLowerBandwidth.smul {S : Type*} [Zero R] [SMulZeroClass S R] {A : Matrix n n R}
    (hA : A.HasLowerBandwidth p) (c : S) : (c • A).HasLowerBandwidth p := fun i j hij => by
  rw [Matrix.smul_apply, hA i j hij, smul_zero]

/-- If $A$ has upper bandwidth $q$, then $cA$ has upper bandwidth $q$ for every scalar $c$. -/
theorem HasUpperBandwidth.smul {S : Type*} [Zero R] [SMulZeroClass S R] {A : Matrix n n R}
    (hA : A.HasUpperBandwidth q) (c : S) : (c • A).HasUpperBandwidth q := fun i j hij => by
  rw [Matrix.smul_apply, hA i j hij, smul_zero]

/-- If $A$ has lower bandwidth $p$, then $-A$ has lower bandwidth $p$. -/
theorem HasLowerBandwidth.neg [NegZeroClass R] {A : Matrix n n R} (hA : A.HasLowerBandwidth p) :
    (-A).HasLowerBandwidth p := fun i j hij => by rw [Matrix.neg_apply, hA i j hij, neg_zero]

/-- If $A$ has upper bandwidth $q$, then $-A$ has upper bandwidth $q$. -/
theorem HasUpperBandwidth.neg [NegZeroClass R] {A : Matrix n n R} (hA : A.HasUpperBandwidth q) :
    (-A).HasUpperBandwidth q := fun i j hij => by rw [Matrix.neg_apply, hA i j hij, neg_zero]

/-- If $A$ has lower bandwidth $p$ and $B$ has lower bandwidth $p'$, then $A - B$ has lower
bandwidth $\max(p, p')$. -/
theorem HasLowerBandwidth.sub [SubNegZeroMonoid R] {A B : Matrix n n R}
    (hA : A.HasLowerBandwidth p) (hB : B.HasLowerBandwidth p') :
    (A - B).HasLowerBandwidth (max p p') := fun i j hij => by
  rw [Matrix.sub_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), sub_zero]

/-- If $A$ has upper bandwidth $q$ and $B$ has upper bandwidth $q'$, then $A - B$ has upper
bandwidth $\max(q, q')$. -/
theorem HasUpperBandwidth.sub [SubNegZeroMonoid R] {A B : Matrix n n R}
    (hA : A.HasUpperBandwidth q) (hB : B.HasUpperBandwidth q') :
    (A - B).HasUpperBandwidth (max q q') := fun i j hij => by
  rw [Matrix.sub_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), sub_zero]

variable [NonUnitalNonAssocSemiring R] {A B : Matrix n n R}

/-- Let $A$ and $B$ be square matrices over a semiring, indexed by a finite linear order. If $A$ has
lower bandwidth $p$ and $B$ has lower bandwidth $p'$, then $AB$ has lower bandwidth $p + p'$
([quarteroni2000numerical], §1.6.3).

In $(AB)_{ij} = \sum_k A_{ik} B_{kj}$, a nonzero term needs at most $p$ indices in $[k, i)$ and
at most $p'$ indices in $[j, k)$, and these two intervals cover $[j, i)$. -/
theorem HasLowerBandwidth.mul (hA : A.HasLowerBandwidth p) (hB : B.HasLowerBandwidth p') :
    (A * B).HasLowerBandwidth (p + p') := fun i j hij => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : p < #{l | k ≤ l ∧ l < i}
  · rw [hA i k hk, zero_mul]
  · rw [hB k j, mul_zero]
    have := card_filter_le_lt_le_add i j k
    omega

/-- Let $A$ and $B$ be square matrices over a semiring, indexed by a finite linear order. If $A$ has
upper bandwidth $q$ and $B$ has upper bandwidth $q'$, then $AB$ has upper bandwidth $q + q'$. -/
theorem HasUpperBandwidth.mul (hA : A.HasUpperBandwidth q) (hB : B.HasUpperBandwidth q') :
    (A * B).HasUpperBandwidth (q + q') := fun i j hij => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : q < #{l | i ≤ l ∧ l < k}
  · rw [hA i k hk, zero_mul]
  · rw [hB k j, mul_zero]
    have := card_filter_le_lt_le_add j i k
    omega

end BandwidthAlgebra

/-! ### Bandwidths of a rectangular matrix -/

section Rect

variable [Zero R] {M N : ℕ}

/-- An $M \times N$ matrix $A$ has **lower bandwidth** $p$ if $a_{ij} = 0$ whenever $i > j + p$
([golub2013matrix], §1.2.1).

The indices are natural numbers, and the condition reads the same with indices from $0$ and from
$1$. -/
def HasLowerBandwidthRect (A : Matrix (Fin M) (Fin N) R) (p : ℕ) : Prop :=
  ∀ (i : Fin M) (j : Fin N), (j : ℕ) + p < i → A i j = 0

/-- An $M \times N$ matrix $A$ has **upper bandwidth** $q$ if $a_{ij} = 0$ whenever $j > i + q$
([golub2013matrix], §1.2.1). -/
def HasUpperBandwidthRect (A : Matrix (Fin M) (Fin N) R) (q : ℕ) : Prop :=
  ∀ (i : Fin M) (j : Fin N), (i : ℕ) + q < j → A i j = 0

/-- For an $M \times N$ matrix $A$, the transpose $A^T$ has upper bandwidth $q$ if and only if $A$
has lower bandwidth $q$, in the sense of rectangular matrices. -/
theorem hasUpperBandwidthRect_transpose_iff {A : Matrix (Fin M) (Fin N) R} {q : ℕ} :
    Aᵀ.HasUpperBandwidthRect q ↔ A.HasLowerBandwidthRect q :=
  forall_comm

/-- For an $M \times N$ matrix $A$, the transpose $A^T$ has lower bandwidth $p$ if and only if $A$
has upper bandwidth $p$, in the sense of rectangular matrices. -/
theorem hasLowerBandwidthRect_transpose_iff {A : Matrix (Fin M) (Fin N) R} {p : ℕ} :
    Aᵀ.HasLowerBandwidthRect p ↔ A.HasUpperBandwidthRect p :=
  forall_comm

/-- For a square matrix indexed by $\{0, \dots, N - 1\}$, lower bandwidth $p$ in the sense of
rectangular matrices (`Matrix.HasLowerBandwidthRect`) is equivalent to lower bandwidth $p$ in
the sense of `Matrix.HasLowerBandwidth`. -/
theorem hasLowerBandwidthRect_iff {A : Matrix (Fin N) (Fin N) R} {p : ℕ} :
    A.HasLowerBandwidthRect p ↔ A.HasLowerBandwidth p :=
  hasLowerBandwidth_iff_fin.symm

/-- For a square matrix indexed by $\{0, \dots, N - 1\}$, upper bandwidth $q$ in the sense of
rectangular matrices (`Matrix.HasUpperBandwidthRect`) is equivalent to upper bandwidth $q$ in
the sense of `Matrix.HasUpperBandwidth`. -/
theorem hasUpperBandwidthRect_iff {A : Matrix (Fin N) (Fin N) R} {q : ℕ} :
    A.HasUpperBandwidthRect q ↔ A.HasUpperBandwidth q :=
  hasUpperBandwidth_iff_fin.symm

end Rect

/-! ### Nilpotency along a potential -/

section Potential

variable {ι S : Type*} [Fintype ι] [DecidableEq ι]

/-- Let $M$ be a square matrix over a semiring, indexed by a finite set $\iota$, and let
$f \colon \iota \to \mathbb{N}$ with $M_{ij} = 0$ whenever $f(j) \le f(i)$. Then for every
$k \in \mathbb{N}$, $(M^k)_{ij} = 0$ whenever $f(j) < f(i) + k$. In particular $M$ is nilpotent
when $f$ is bounded. -/
theorem pow_apply_eq_zero_of_potential [Semiring S] (M : Matrix ι ι S) (f : ι → ℕ)
    (hM : ∀ i j, f j ≤ f i → M i j = 0) (k : ℕ) :
    ∀ i j, f j < f i + k → (M ^ k) i j = 0 := by
  induction k with
  | zero =>
    intro i j h
    rw [pow_zero, one_apply_ne]
    rintro rfl
    omega
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : f j ≤ f r
    · rw [hM r j hr, mul_zero]
    · rw [ih i r (by omega), zero_mul]

/-- Let $M$ be a square matrix over a ring, indexed by a finite set $\iota$, and let
$f \colon \iota \to \mathbb{N}$ satisfy $f(i) < N$ for all $i$ and $M_{ij} = 0$ whenever
$f(j) \le f(i)$. Then $1 + M$ is a unit.

The reason is that $M^N = 0$ by `Matrix.pow_apply_eq_zero_of_potential`. -/
theorem isUnit_one_add_of_potential [Ring S] (M : Matrix ι ι S) (f : ι → ℕ) {N : ℕ}
    (hf : ∀ i, f i < N) (hM : ∀ i j, f j ≤ f i → M i j = 0) : IsUnit (1 + M) := by
  refine IsNilpotent.isUnit_one_add ⟨N, ?_⟩
  ext i j
  exact pow_apply_eq_zero_of_potential M f hM N i j (by have := hf j; omega)

end Potential

end Matrix
