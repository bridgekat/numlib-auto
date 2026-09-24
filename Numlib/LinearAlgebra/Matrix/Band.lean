/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Order.Interval.Finset.Fin
import Numlib.LinearAlgebra.Matrix.Triangular

/-!
# Band matrices

The lower and upper bandwidths of a square matrix indexed by a finite linear order, and of a
rectangular matrix indexed by `Fin m × Fin n`.

## Main definitions

* `Matrix.HasLowerBandwidth A p`, `Matrix.HasUpperBandwidth A q`: an entry `A i j` vanishes as soon
  as more than `p` indices lie in `[j, i)` (respectively more than `q` in `[i, j)`). On `Fin N` the
  count is `i - j`, so these are the conditions `i > j + p` and `j > i + q` of
  [quarteroni2000numerical] §1.6.3 and [golub2013matrix] §1.2.1
  (`Matrix.hasLowerBandwidth_iff_fin`); on a general finite linear order they need no arithmetic
  on the indices, in the spirit of `Matrix.IsUpperHessenberg`.
* `Matrix.HasLowerBandwidthRect`, `Matrix.HasUpperBandwidthRect`: the same conditions for a
  rectangular `Matrix (Fin m) (Fin n) R`, where the index difference is taken in `ℕ` —
  [golub2013matrix] §1.2.1 defines bandwidth for `m × n` matrices (Table 1.2.1), and the
  bidiagonal and banded shapes of the SVD and band-LU chapters are rectangular; on a square
  `Fin n` they agree with the order-theoretic predicates (`Matrix.hasLowerBandwidthRect_iff`).

## Main results

* Bands `0` are the triangular shapes (`Matrix.hasLowerBandwidth_zero_iff`,
  `Matrix.hasUpperBandwidth_zero_iff`) and both bands `0` the diagonal one
  (`Matrix.isDiag_iff_hasBandwidth_zero`); the bands `1` are the Hessenberg, tridiagonal and
  bidiagonal shapes of `Numlib/LinearAlgebra/Matrix/Hessenberg`.
* Sums keep the larger band (`Matrix.HasLowerBandwidth.add`) and products add bands
  (`Matrix.HasLowerBandwidth.mul`), which is how `L U` is read back in banded storage.
-/

namespace Matrix

variable {n R : Type*} [LinearOrder n]

/-! ### Counting indices in an interval -/

section Counts

open Finset

variable [Fintype n]

/-- Counting indices in a half-open interval, on a finite linear order. -/
theorem card_filter_le_lt_pos_iff (i j : n) :
    0 < #{k | j ≤ k ∧ k < i} ↔ j < i := by
  rw [Finset.card_pos]
  constructor
  · rintro ⟨k, hk⟩
    simp only [mem_filter, mem_univ, true_and] at hk
    exact hk.1.trans_lt hk.2
  · intro h
    exact ⟨j, by simp [h]⟩

/-- More than one index lies in `[j, i)` exactly when some index lies strictly between `j` and
`i`. -/
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

/-- The interval `[j, i)` is covered by `[j, l)` and `[l, i)`, whatever `l` is. -/
theorem card_filter_le_lt_le_add (i j l : n) :
    #{k | j ≤ k ∧ k < i} ≤ #{k | j ≤ k ∧ k < l} + #{k | l ≤ k ∧ k < i} := by
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro k hk
  simp only [mem_filter, mem_univ, true_and, mem_union] at hk ⊢
  rcases lt_or_ge k l with h | h
  · exact Or.inl ⟨hk.1, h⟩
  · exact Or.inr ⟨h, hk.2⟩

/-- A larger interval holds more indices. -/
theorem card_filter_le_lt_mono {i i' j j' : n} (hj : j' ≤ j) (hi : i ≤ i') :
    #{k | j ≤ k ∧ k < i} ≤ #{k | j' ≤ k ∧ k < i'} := by
  refine Finset.card_le_card fun k hk => ?_
  simp only [mem_filter, mem_univ, true_and] at hk ⊢
  exact ⟨hj.trans hk.1, hk.2.trans_le hi⟩

/-- The interval `[j, i)` misses `i`, so it holds at most `card n - 1` indices. -/
theorem card_filter_le_lt_le_card_sub_one (i j : n) :
    #{k | j ≤ k ∧ k < i} ≤ Fintype.card n - 1 := by
  rw [← Finset.card_univ, ← Finset.card_erase_of_mem (mem_univ i)]
  refine Finset.card_le_card fun k hk => ?_
  simp only [mem_filter, mem_univ, true_and, mem_erase, and_true] at hk ⊢
  exact hk.2.ne

/-- On `Fin N`, the interval `[j, i)` holds `i - j` indices. -/
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

/-- `A.HasLowerBandwidth p`: an entry `A i j` vanishes as soon as more than `p` indices lie in the
half-open interval `[j, i)`. On `Fin N` the count is `i - j`, so this is the condition `i > j + p`
of [quarteroni2000numerical] §1.6.3 (`Matrix.hasLowerBandwidth_iff_fin`); `p = 0` is upper
triangularity and `p = 1` the upper Hessenberg shape. -/
def HasLowerBandwidth (A : Matrix n n R) (p : ℕ) : Prop :=
  ∀ i j, p < #{k | j ≤ k ∧ k < i} → A i j = 0

/-- `A.HasUpperBandwidth q`: an entry `A i j` vanishes as soon as more than `q` indices lie in
`[i, j)`, the condition `j > i + q` of [quarteroni2000numerical] §1.6.3; `q = 0` is lower
triangularity. It is the lower bandwidth of the transpose
(`Matrix.hasUpperBandwidth_iff_transpose`). -/
def HasUpperBandwidth (A : Matrix n n R) (q : ℕ) : Prop :=
  ∀ i j, q < #{k | i ≤ k ∧ k < j} → A i j = 0

variable {A B : Matrix n n R} {p q : ℕ}

/-- The upper bandwidth of a matrix is the lower bandwidth of its transpose. -/
theorem hasUpperBandwidth_iff_transpose : A.HasUpperBandwidth q ↔ Aᵀ.HasLowerBandwidth q :=
  forall_comm

/-- The lower bandwidth of a matrix is the upper bandwidth of its transpose. -/
theorem hasLowerBandwidth_iff_transpose : A.HasLowerBandwidth p ↔ Aᵀ.HasUpperBandwidth p :=
  forall_comm

/-- On `Fin N`, lower bandwidth `p` is the usual condition: `A i j = 0` whenever `i > j + p`. -/
theorem hasLowerBandwidth_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.HasLowerBandwidth p ↔ ∀ i j : Fin N, (j : ℕ) + p < (i : ℕ) → A i j = 0 := by
  simp only [HasLowerBandwidth, card_filter_le_lt_fin]
  exact forall₂_congr fun i j => by constructor <;> intro h hij <;> apply h <;> omega

/-- On `Fin N`, upper bandwidth `q` is the usual condition: `A i j = 0` whenever `j > i + q`. -/
theorem hasUpperBandwidth_iff_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) R} :
    A.HasUpperBandwidth q ↔ ∀ i j : Fin N, (i : ℕ) + q < (j : ℕ) → A i j = 0 := by
  simp only [HasUpperBandwidth, card_filter_le_lt_fin]
  exact forall₂_congr fun i j => by constructor <;> intro h hij <;> apply h <;> omega

/-- A band is a band for every larger width. -/
theorem HasLowerBandwidth.mono (h : A.HasLowerBandwidth p) (hpq : p ≤ q) :
    A.HasLowerBandwidth q := fun i j hij => h i j (hpq.trans_lt hij)

/-- A band is a band for every larger width. -/
theorem HasUpperBandwidth.mono (h : A.HasUpperBandwidth p) (hpq : p ≤ q) :
    A.HasUpperBandwidth q := fun i j hij => h i j (hpq.trans_lt hij)

/-- Every matrix has lower bandwidth `card n - 1`. -/
theorem hasLowerBandwidth_card_sub_one : A.HasLowerBandwidth (Fintype.card n - 1) :=
  fun i j hij => absurd (card_filter_le_lt_le_card_sub_one i j) (not_le.2 hij)

/-- Every matrix has upper bandwidth `card n - 1`. -/
theorem hasUpperBandwidth_card_sub_one : A.HasUpperBandwidth (Fintype.card n - 1) :=
  fun i j hij => absurd (card_filter_le_lt_le_card_sub_one j i) (not_le.2 hij)

/-- Lower bandwidth `0` is upper triangularity ([quarteroni2000numerical] §1.6.2–1.6.3). -/
theorem hasLowerBandwidth_zero_iff : A.HasLowerBandwidth 0 ↔ A.IsUpperTriangular := by
  simp only [HasLowerBandwidth, card_filter_le_lt_pos_iff]
  exact ⟨fun h i j hij => h i j hij, fun h i j hij => h hij⟩

/-- Upper bandwidth `0` is lower triangularity. -/
theorem hasUpperBandwidth_zero_iff : A.HasUpperBandwidth 0 ↔ A.IsLowerTriangular := by
  simp only [HasUpperBandwidth, card_filter_le_lt_pos_iff]
  exact ⟨fun h i j hij => h i j hij, fun h i j hij => h hij⟩

/-- A matrix is diagonal exactly when both its bandwidths are `0`. -/
theorem isDiag_iff_hasBandwidth_zero :
    A.IsDiag ↔ A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth 0 := by
  rw [hasLowerBandwidth_zero_iff, hasUpperBandwidth_zero_iff]
  refine ⟨fun h => ⟨fun i j hij => h (hij : j < i).ne',
    fun i j hij => h (OrderDual.toDual_lt_toDual.1 hij).ne⟩, fun h i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact h.2 hlt
  · exact h.1 hlt

/-- The strict lower part inherits the lower bandwidth. -/
theorem HasLowerBandwidth.strictLower (h : A.HasLowerBandwidth p) :
    (strictLower A).HasLowerBandwidth p := fun i j hij => by
  rw [strictLower_apply, h i j hij, ite_self]

/-- The strict upper part inherits the upper bandwidth. -/
theorem HasUpperBandwidth.strictUpper (h : A.HasUpperBandwidth q) :
    (strictUpper A).HasUpperBandwidth q := fun i j hij => by
  rw [strictUpper_apply, h i j hij, ite_self]

/-- The strict upper part has lower bandwidth `0`. -/
theorem strictUpper_hasLowerBandwidth_zero : (strictUpper A).HasLowerBandwidth 0 :=
  hasLowerBandwidth_zero_iff.2 (strictUpper_blockTriangular A)

/-- The strict lower part has upper bandwidth `0`. -/
theorem strictLower_hasUpperBandwidth_zero : (strictLower A).HasUpperBandwidth 0 :=
  hasUpperBandwidth_zero_iff.2 (strictLower_blockTriangular A)

/-- The diagonal part has lower bandwidth `0`. -/
theorem diagPart_hasLowerBandwidth_zero : (diagPart A).HasLowerBandwidth 0 :=
  hasLowerBandwidth_zero_iff.2 (blockTriangular_diagonal _)

/-- The diagonal part has upper bandwidth `0`. -/
theorem diagPart_hasUpperBandwidth_zero : (diagPart A).HasUpperBandwidth 0 :=
  hasUpperBandwidth_zero_iff.2 (blockTriangular_diagonal _)

end Bandwidth

/-! ### The algebra of bandwidths -/

section BandwidthAlgebra

open Finset

variable [Fintype n] {p p' q q' : ℕ}

/-- Sums keep the larger lower bandwidth. -/
theorem HasLowerBandwidth.add [AddZeroClass R] {A B : Matrix n n R} (hA : A.HasLowerBandwidth p)
    (hB : B.HasLowerBandwidth p') : (A + B).HasLowerBandwidth (max p p') := fun i j hij => by
  rw [add_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), add_zero]

/-- Sums keep the larger upper bandwidth. -/
theorem HasUpperBandwidth.add [AddZeroClass R] {A B : Matrix n n R} (hA : A.HasUpperBandwidth q)
    (hB : B.HasUpperBandwidth q') : (A + B).HasUpperBandwidth (max q q') := fun i j hij => by
  rw [add_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), add_zero]

/-- Scalar multiples keep the lower bandwidth. -/
theorem HasLowerBandwidth.smul {S : Type*} [Zero R] [SMulZeroClass S R] {A : Matrix n n R}
    (hA : A.HasLowerBandwidth p) (c : S) : (c • A).HasLowerBandwidth p := fun i j hij => by
  rw [smul_apply, hA i j hij, smul_zero]

/-- Scalar multiples keep the upper bandwidth. -/
theorem HasUpperBandwidth.smul {S : Type*} [Zero R] [SMulZeroClass S R] {A : Matrix n n R}
    (hA : A.HasUpperBandwidth q) (c : S) : (c • A).HasUpperBandwidth q := fun i j hij => by
  rw [smul_apply, hA i j hij, smul_zero]

/-- Negation keeps the lower bandwidth. -/
theorem HasLowerBandwidth.neg [NegZeroClass R] {A : Matrix n n R} (hA : A.HasLowerBandwidth p) :
    (-A).HasLowerBandwidth p := fun i j hij => by rw [neg_apply, hA i j hij, neg_zero]

/-- Negation keeps the upper bandwidth. -/
theorem HasUpperBandwidth.neg [NegZeroClass R] {A : Matrix n n R} (hA : A.HasUpperBandwidth q) :
    (-A).HasUpperBandwidth q := fun i j hij => by rw [neg_apply, hA i j hij, neg_zero]

/-- Differences keep the larger lower bandwidth. -/
theorem HasLowerBandwidth.sub [SubNegZeroMonoid R] {A B : Matrix n n R}
    (hA : A.HasLowerBandwidth p) (hB : B.HasLowerBandwidth p') :
    (A - B).HasLowerBandwidth (max p p') := fun i j hij => by
  rw [sub_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), sub_zero]

/-- Differences keep the larger upper bandwidth. -/
theorem HasUpperBandwidth.sub [SubNegZeroMonoid R] {A B : Matrix n n R}
    (hA : A.HasUpperBandwidth q) (hB : B.HasUpperBandwidth q') :
    (A - B).HasUpperBandwidth (max q q') := fun i j hij => by
  rw [sub_apply, hA i j ((le_max_left _ _).trans_lt hij),
    hB i j ((le_max_right _ _).trans_lt hij), sub_zero]

variable [NonUnitalNonAssocSemiring R] {A B : Matrix n n R}

/-- Bandwidths add under products ([quarteroni2000numerical] §1.6.3): in `∑ k, A i k * B k j`, a
nonzero term needs at most `p` indices in `[k, i)` and at most `p'` in `[j, k)`, and these two
intervals cover `[j, i)`. -/
theorem HasLowerBandwidth.mul (hA : A.HasLowerBandwidth p) (hB : B.HasLowerBandwidth p') :
    (A * B).HasLowerBandwidth (p + p') := fun i j hij => by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : p < #{l | k ≤ l ∧ l < i}
  · rw [hA i k hk, zero_mul]
  · rw [hB k j, mul_zero]
    have := card_filter_le_lt_le_add i j k
    omega

/-- Bandwidths add under products, the upper version. -/
theorem HasUpperBandwidth.mul (hA : A.HasUpperBandwidth q) (hB : B.HasUpperBandwidth q') :
    (A * B).HasUpperBandwidth (q + q') := fun i j hij => by
  rw [mul_apply]
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

/-- Lower bandwidth `p` of a rectangular matrix ([golub2013matrix] §1.2.1): `a_ij = 0` whenever
`i > j + p`, the index difference taken in `ℕ` (the condition reads the same in `0`- and
`1`-based indexing). -/
def HasLowerBandwidthRect (A : Matrix (Fin M) (Fin N) R) (p : ℕ) : Prop :=
  ∀ (i : Fin M) (j : Fin N), (j : ℕ) + p < i → A i j = 0

/-- Upper bandwidth `q` of a rectangular matrix ([golub2013matrix] §1.2.1): `a_ij = 0` whenever
`j > i + q`. -/
def HasUpperBandwidthRect (A : Matrix (Fin M) (Fin N) R) (q : ℕ) : Prop :=
  ∀ (i : Fin M) (j : Fin N), (i : ℕ) + q < j → A i j = 0

/-- The upper bandwidth of the transpose is the lower bandwidth. -/
theorem hasUpperBandwidthRect_transpose_iff {A : Matrix (Fin M) (Fin N) R} {q : ℕ} :
    Aᵀ.HasUpperBandwidthRect q ↔ A.HasLowerBandwidthRect q :=
  forall_comm

/-- The lower bandwidth of the transpose is the upper bandwidth. -/
theorem hasLowerBandwidthRect_transpose_iff {A : Matrix (Fin M) (Fin N) R} {p : ℕ} :
    Aᵀ.HasLowerBandwidthRect p ↔ A.HasUpperBandwidthRect p :=
  forall_comm

/-- On a square `Fin N`, the rectangular lower bandwidth is the order-theoretic one. -/
theorem hasLowerBandwidthRect_iff {A : Matrix (Fin N) (Fin N) R} {p : ℕ} :
    A.HasLowerBandwidthRect p ↔ A.HasLowerBandwidth p :=
  hasLowerBandwidth_iff_fin.symm

/-- On a square `Fin N`, the rectangular upper bandwidth is the order-theoretic one. -/
theorem hasUpperBandwidthRect_iff {A : Matrix (Fin N) (Fin N) R} {q : ℕ} :
    A.HasUpperBandwidthRect q ↔ A.HasUpperBandwidth q :=
  hasUpperBandwidth_iff_fin.symm

end Rect

end Matrix
