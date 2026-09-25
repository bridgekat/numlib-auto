import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.Permutation
import NumlibSurface.GolubVanLoan.Chapter01.Section01

/-!
# Golub–Van Loan §1.2: structure and efficiency

Surface file for §1.2 of Golub and Van Loan, *Matrix Computations* (4th edition): bandwidth and
the band terminology of Table 1.2.1, triangular matrix multiplication (Algorithm 1.2.1), the band-
and symmetric-storage gaxpys (Algorithms 1.2.2–1.2.3), permutation matrices `I_n(v,:)` and the
three famous permutation matrices of §1.2.11 with (1.2.4).

## Design

Bandwidth is the backbone's: `Matrix.HasLowerBandwidth`/`Matrix.HasUpperBandwidth` of
`Numlib/LinearAlgebra/Matrix/Band` on square matrices (on `Fin n` they read `a_ij = 0` whenever
`i > j + p`, resp. `j > i + q`, the book's §1.2.1 definition verbatim, in 0- and 1-based indexing
alike: `Matrix.hasLowerBandwidth_iff_fin`); their rectangular forms, for the book's `m × n` column
of Table 1.2.1, are `Matrix.HasLowerBandwidthRect`/`Matrix.HasUpperBandwidthRect`.

The storage schemes (1.2.1) `A.band(i − j + q + 1, j) = a_ij` and (1.2.2)
`A.vec((n − j/2)(j − 1) + i) = a_ij` are not objects of their own: each is the hypothesis of its
algorithm's specification, relating the stored array to the matrix. In 0-based form (1.2.1) reads
`Aband ⟨i + q − j, _⟩ j = A i j` for `j ≤ i + q`, `i ≤ j + p`, and (1.2.2) reads
`Avec ⟨j n − j (j + 1) / 2 + i, _⟩ = A i j` for `j ≤ i`. The programs read the arrays through
`bandEntry` and `packedEntry`, which return `0` outside the stored range (never read there). The
book's integer arithmetic `α₁, α₂, β₁, β₂` of Algorithm 1.2.2 is the filter of the loop's index list
and is not rounded.

A permutation matrix `I_n(v,:)` for a permutation `v` is Mathlib's `v.permMatrix ℝ`, whose row `i`
is `e_{v(i)}ᵀ`. The exchange `ℰ_n`, the downshift `𝒟_n` and the perfect shuffle `𝒫_{p,r}` are the
backbone's `Matrix.exchange`, `Matrix.downshift`, `Matrix.perfectShuffle`
(`Numlib/LinearAlgebra/Matrix/Permutation`).

The exact specifications of the three algorithms are proved in exact arithmetic (`M := Id`):
the loops are fused into per-entry updates (`GolubVanLoan.Chapter01.foldlM_updateRow_row`,
`foldlM_updateRow_update_entry`), a loop writing one entry per step over a duplicate-free list is
evaluated entrywise, and a loop acting on every entry independently is interchanged with the
entry (`List.foldl_apply_of_pi`).

## Main results

* `table_1_2_1` — the band terminology, as a conjunction of characterizations.
* `algorithm_1_2_1`, `algorithm_1_2_1_spec` — triangular matrix multiplication.
* `algorithm_1_2_2`, `algorithm_1_2_2_spec` — the band storage gaxpy.
* `algorithm_1_2_3`, `algorithm_1_2_3_spec` — the symmetric storage gaxpy.
* `permutation_mulVec`, `permutation_transpose_mul_self`, `permutation_mul_mul_transpose` — §1.2.10.
* `exchange_eq_permMatrix_rev`, `exchange_mul_self`, `downshift`, `perfectShuffle_mulVec_eq`,
  `equation_1_2_4` — §1.2.11.

## Not formalized here

§1.2.4 (flop sums), §1.2.6 on diagonal scaling (Mathlib's `Matrix.diagonal_mul`,
`Matrix.mul_diagonal`), the prose definitions of (skew-)symmetric and (skew-)Hermitian (Mathlib's
`Matrix.IsSymm`, `Matrix.IsHermitian`), the example (1.2.3), the index vectors of §1.2.9 (`Fin`
maps), the count `2n(p + q + 1)` after Algorithm 1.2.2.
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter01

/-! ### Table 1.2.1: band terminology -/

/-- **Table 1.2.1** (band terminology), for `A ∈ ℝ^{n×n}`: diagonal is bandwidths `(0, 0)`, upper
triangular `(0, n − 1)`, lower triangular `(n − 1, 0)`, tridiagonal `(1, 1)`, upper bidiagonal
`(0, 1)`, lower bidiagonal `(1, 0)`, upper Hessenberg `(1, n − 1)`, lower Hessenberg (`Aᵀ` upper
Hessenberg) `(n − 1, 1)`. For a rectangular `A ∈ ℝ^{m×n}` the rows read the same with
`Matrix.HasLowerBandwidthRect`/`Matrix.HasUpperBandwidthRect`, the bound `m − 1` or `n − 1` then
holding for every matrix. -/
theorem table_1_2_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.IsDiag ↔ A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth 0) ∧
    (A.IsUpperTriangular ↔ A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth (n - 1)) ∧
    (A.IsLowerTriangular ↔ A.HasLowerBandwidth (n - 1) ∧ A.HasUpperBandwidth 0) ∧
    (A.IsTridiagonal ↔ A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth 1) ∧
    (A.IsUpperBidiagonal ↔ A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth 1) ∧
    (A.IsLowerBidiagonal ↔ A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth 0) ∧
    (A.IsUpperHessenberg ↔ A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth (n - 1)) ∧
    (Aᵀ.IsUpperHessenberg ↔ A.HasLowerBandwidth (n - 1) ∧ A.HasUpperBandwidth 1) := by
  have hlow : A.HasLowerBandwidth (n - 1) := by
    simpa using (Matrix.hasLowerBandwidth_card_sub_one (A := A))
  have hup : A.HasUpperBandwidth (n - 1) := by
    simpa using (Matrix.hasUpperBandwidth_card_sub_one (A := A))
  refine ⟨Matrix.isDiag_iff_hasBandwidth_zero, ?_, ?_, Matrix.isTridiagonal_iff_hasBandwidth_one,
    ?_, ?_, ?_, ?_⟩
  · rw [Matrix.hasLowerBandwidth_zero_iff]
    exact ⟨fun h => ⟨h, hup⟩, And.left⟩
  · rw [Matrix.hasUpperBandwidth_zero_iff]
    exact ⟨fun h => ⟨hlow, h⟩, And.right⟩
  · refine ⟨Matrix.IsUpperBidiagonal.hasBandwidth, fun ⟨h₀, h₁⟩ i j hij => ?_⟩
    rcases hij with hij | hij
    · exact Matrix.hasLowerBandwidth_zero_iff.1 h₀ hij
    · exact (Matrix.isTridiagonal_iff_hasBandwidth_one.2
        ⟨h₀.mono zero_le_one, h₁⟩) i j (Or.inr hij)
  · refine ⟨Matrix.IsLowerBidiagonal.hasBandwidth, fun ⟨h₁, h₀⟩ i j hij => ?_⟩
    rcases hij with hij | hij
    · exact Matrix.hasUpperBandwidth_zero_iff.1 h₀ hij
    · exact (Matrix.isTridiagonal_iff_hasBandwidth_one.2
        ⟨h₁, h₀.mono zero_le_one⟩) i j (Or.inl hij)
  · rw [Matrix.isUpperHessenberg_iff_hasLowerBandwidth_one]
    exact ⟨fun h => ⟨h, hup⟩, And.left⟩
  · rw [Matrix.isUpperHessenberg_iff_hasLowerBandwidth_one,
      ← Matrix.hasUpperBandwidth_iff_transpose]
    exact ⟨fun h => ⟨hlow, h⟩, And.right⟩

/-! ### Exact evaluation of loops writing one entry per step -/

/-- In exact arithmetic, a loop over a duplicate-free index list whose step `a` rewrites entry `a`
from its current value leaves the entries off the list alone and writes each entry of the list
once, from its initial value. -/
theorem idRun_foldlM_update_apply {ι β : Type} [DecidableEq ι] (g : ι → β → Id β)
    (l : List ι) (hl : l.Nodup) (y₀ : ι → β) (i : ι) :
    Id.run (l.foldlM (fun (y : ι → β) a => do
      let b ← g a (y a); pure (Function.update y a b)) y₀) i =
      if i ∈ l then Id.run (g i (y₀ i)) else y₀ i := by
  induction l generalizing y₀ with
  | nil => simp
  | cons a l ih =>
    rcases List.nodup_cons.1 hl with ⟨ha, hl'⟩
    simp only [List.foldlM_cons, Id.run_bind, Id.run_pure]
    rw [ih hl']
    by_cases hia : i = a
    · subst hia
      simp [ha]
    · have hmem : i ∈ a :: l ↔ i ∈ l := by simp [hia]
      rw [if_congr hmem rfl rfl]
      split_ifs <;> simp [Function.update_of_ne hia]

/-- The row form of `idRun_foldlM_update_apply`. -/
theorem idRun_foldlM_updateRow_apply {m n : ℕ} (g : Fin m → (Fin n → ℝ) → Id (Fin n → ℝ))
    (l : List (Fin m)) (hl : l.Nodup) (C₀ : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Id.run (l.foldlM (fun (C : Matrix (Fin m) (Fin n) ℝ) a => do
      let r ← g a (C a); pure (C.updateRow a r)) C₀) i =
      if i ∈ l then Id.run (g i (C₀ i)) else C₀ i :=
  idRun_foldlM_update_apply (β := Fin n → ℝ) g l hl C₀ i

/-- A sum over a filtered `List.finRange` is the sum of the indicator. -/
private theorem sum_map_filter_finRange {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (f : Fin n → ℝ) :
    (((List.finRange n).filter fun k => decide (P k)).map f).sum = ∑ k, if P k then f k else 0 := by
  rw [Fin.sum_univ_def]
  induction (List.finRange n) with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

/-! ### Algorithm 1.2.1: triangular matrix multiplication -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 1.2.1 (Triangular Matrix Multiplication).** "Given upper triangular matrices
`A, B, C ∈ ℝ^{n×n}`, this algorithm overwrites `C` with `C + AB`":
```
for i = 1:n
    for j = i:n
        for k = i:j
            C(i,j) = C(i,j) + A(i,k) B(k,j)
        end
    end
end
```
The ranges `j = i:n` and `k = i:j` are filtered index lists. -/
def algorithm_1_2_1 {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun C i =>
    ((List.finRange n).filter (i ≤ ·)).foldlM (fun C j =>
      ((List.finRange n).filter (fun k => i ≤ k ∧ k ≤ j)).foldlM (fun C k => do
        let p ← rnd (A i k * B k j)
        let c ← rnd (C i j + p)
        pure (C.updateRow i (Function.update (C i) j c))) C) C) C

/-- The entry `A.band(i − j + q + 1, j)` of the band storage (1.2.1), 0-based `Aband (i + q − j) j`;
`0` outside the stored array (Algorithm 1.2.2 reads only inside the band). -/
def bandEntry {p q n : ℕ} (Aband : Matrix (Fin (p + q + 1)) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  if h : (i : ℕ) + q - j < p + q + 1 then Aband ⟨i + q - j, h⟩ j else 0

/-- **Algorithm 1.2.2 (Band Storage Gaxpy).** "Suppose `A ∈ ℝ^{n×n}` has lower bandwidth `p` and
upper bandwidth `q` and is stored in the `A.band` format (1.2.1). If `x, y ∈ ℝⁿ`, then this
algorithm overwrites `y` with `y + Ax`":
```
for j = 1:n
    α₁ = max(1, j − q), α₂ = min(n, j + p)
    β₁ = max(1, q + 2 − j), β₂ = β₁ + α₂ − α₁
    y(α₁:α₂) = y(α₁:α₂) + A.band(β₁:β₂, j) x(j)
end
```
The rows `α₁:α₂` are the `i` with `j ≤ i + q` and `i ≤ j + p`, and `A.band(β₁:β₂, j)` lists their
entries `Aband (i + q − j) j`. -/
def algorithm_1_2_2 {n : ℕ} (p q : ℕ) (Aband : Matrix (Fin (p + q + 1)) (Fin n) ℝ)
    (x y : Fin n → ℝ) : M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (y : Fin n → ℝ) (j : Fin n) =>
    ((List.finRange n).filter (fun (i : Fin n) => (j : ℕ) ≤ i + q ∧ (i : ℕ) ≤ j + p)).foldlM
      (fun (y : Fin n → ℝ) (i : Fin n) => do
      let t ← rnd (bandEntry Aband i j * x j)
      let s ← rnd (y i + t)
      pure (Function.update y i s)) y) y

/-- The position `j n − j(j+1)/2 + i` of `a_ij`, `j ≤ i`, in the packed storage (1.2.2), 0-based
(the book's `(n − j/2)(j − 1) + i` with `i ↦ i + 1`, `j ↦ j + 1`, minus one). -/
def packedIndex (n : ℕ) (i j : Fin n) : ℕ :=
  (j : ℕ) * n - (j : ℕ) * ((j : ℕ) + 1) / 2 + (i : ℕ)

/-- The entry `A.vec(k)` of the packed symmetric storage (1.2.2), 0-based; `0` outside the array
(Algorithm 1.2.3 reads only inside it). -/
def packedEntry {n : ℕ} (Avec : Fin (n * (n + 1) / 2) → ℝ) (k : ℕ) : ℝ :=
  if h : k < n * (n + 1) / 2 then Avec ⟨k, h⟩ else 0

/-- **Algorithm 1.2.3 (Symmetric Storage Gaxpy).** "Suppose `A ∈ ℝ^{n×n}` is symmetric and stored
in the `A.vec` style (1.2.2). If `x, y ∈ ℝⁿ`, then this algorithm overwrites `y` with `y + Ax`":
```
for j = 1:n
    for i = 1:j−1
        y(i) = y(i) + A.vec((i−1)n − i(i−1)/2 + j) x(j)
    end
    for i = j:n
        y(i) = y(i) + A.vec((j−1)n − j(j−1)/2 + i) x(j)
    end
end
```
in 0-based indices `A.vec(i n − i(i+1)/2 + j)` and `A.vec(j n − j(j+1)/2 + i)`, the index formed
in `ℕ` (integer arithmetic, not rounded). -/
def algorithm_1_2_3 {n : ℕ} (Avec : Fin (n * (n + 1) / 2) → ℝ) (x y : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (y : Fin n → ℝ) (j : Fin n) => do
    let y ← ((List.finRange n).filter (· < j)).foldlM (fun (y : Fin n → ℝ) (i : Fin n) => do
      let t ← rnd (packedEntry Avec (packedIndex n j i) * x j)
      let s ← rnd (y i + t)
      pure (Function.update y i s)) y
    ((List.finRange n).filter (j ≤ ·)).foldlM (fun (y : Fin n → ℝ) (i : Fin n) => do
      let t ← rnd (packedEntry Avec (packedIndex n i j) * x j)
      let s ← rnd (y i + t)
      pure (Function.update y i s)) y) y

end Programs

/-! ### The specifications -/

/-- The row loop of Algorithm 1.2.1 after fusion: for each `j ≥ i`, the abbreviated inner product
`∑_{k=i}^{j} a_ik b_kj` accumulated onto `c_ij`. -/
private def triangularRow {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (row : Fin n → ℝ) : M (Fin n → ℝ) :=
  ((List.finRange n).filter (i ≤ ·)).foldlM (fun row j => do
    let c ← dotAccum rnd ((List.finRange n).filter (fun k => i ≤ k ∧ k ≤ j)) (A i)
      (fun k => B k j) (row j)
    pure (Function.update row j c)) row

/-- Algorithm 1.2.1 as a loop writing one row per step. -/
private theorem algorithm_1_2_1_eq {M : Type → Type} [Monad M] [LawfulMonad M] (rnd : ℝ → M ℝ)
    {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) :
    algorithm_1_2_1 rnd A B C = (List.finRange n).foldlM (fun C i => do
      let row ← triangularRow rnd A B i (C i); pure (C.updateRow i row)) C := by
  unfold algorithm_1_2_1
  congr 1
  funext C i
  rw [triangularRow, ← foldlM_updateRow_row i (fun j c =>
    dotAccum rnd ((List.finRange n).filter (fun k => i ≤ k ∧ k ≤ j)) (A i) (fun k => B k j) c)]
  congr 1
  funext C j
  have := foldlM_updateRow_update_entry i j
    (fun k c => do let p ← rnd (A i k * B k j); rnd (c + p))
    ((List.finRange n).filter (fun k => i ≤ k ∧ k ≤ j)) C
  simp only [bind_assoc] at this
  exact this

/-- **Algorithm 1.2.1 overwrites `C` with `C + AB`** for upper triangular `A` and `B`: for
`i ≤ j` the abbreviated inner product `∑_{k=i}^{j} a_ik b_kj` is `(AB)_ij` because
`a_ik b_kj = 0` whenever `k < i` or `j < k`; the entries with `j < i` are untouched, and there
`(AB)_ij = 0`. (The book also takes `C` upper triangular; the statement does not need it.) -/
theorem algorithm_1_2_1_spec {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) :
    Id.run (algorithm_1_2_1 pure A B C) = C + A * B := by
  rw [algorithm_1_2_1_eq]
  ext i j
  rw [idRun_foldlM_updateRow_apply _ _ (List.nodup_finRange n), ite_eq_left (List.mem_finRange i),
    triangularRow, idRun_foldlM_update_apply _ _ ((List.nodup_finRange n).filter _),
    Matrix.add_apply, Matrix.mul_apply]
  split_ifs with hij
  · rw [dotAccum_id, sum_map_filter_finRange (fun k => i ≤ k ∧ k ≤ j)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rfl
    · rcases not_and_or.1 hk with hk | hk
      · rw [hA (not_le.1 hk), zero_mul]
      · rw [hB (not_le.1 hk), mul_zero]
  · have hji : j < i := by simpa using hij
    have hz : ∑ k, A i k * B k j = 0 := Finset.sum_eq_zero fun k _ => by
      rcases lt_or_ge k i with hk | hk
      · rw [hA hk, zero_mul]
      · rw [hB (hji.trans_le hk), mul_zero]
    rw [hz, add_zero]

/-- **Algorithm 1.2.2 overwrites `y` with `y + Ax`** when `A` has lower bandwidth `p` and upper
bandwidth `q` and `Aband` stores it in the format (1.2.1), `Aband (i + q − j) j = a_ij` inside the
band. As for Algorithm 1.1.4, with the out-of-band terms of `(Ax)_i` zero by the bandwidths. -/
theorem algorithm_1_2_2_spec {n : ℕ} (p q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hp : A.HasLowerBandwidth p) (hq : A.HasUpperBandwidth q)
    (Aband : Matrix (Fin (p + q + 1)) (Fin n) ℝ)
    (hband : ∀ (i j : Fin n) (h₁ : (j : ℕ) ≤ i + q) (h₂ : (i : ℕ) ≤ j + p),
      Aband ⟨i + q - j, by omega⟩ j = A i j)
    (x y : Fin n → ℝ) :
    Id.run (algorithm_1_2_2 pure p q Aband x y) = y + A *ᵥ x := by
  rw [Matrix.hasLowerBandwidth_iff_fin] at hp
  rw [Matrix.hasUpperBandwidth_iff_fin] at hq
  funext i
  unfold algorithm_1_2_2
  rw [List.idRun_foldlM, List.foldl_apply_of_pi _
    (fun (j i : Fin n) (b : ℝ) =>
      b + if (j : ℕ) ≤ i + q ∧ (i : ℕ) ≤ j + p then bandEntry Aband i j * x j else 0)
    (fun y j i => ?_), List.foldl_add_eq_add_sum_map, Pi.add_apply, ← Fin.sum_univ_def]
  · simp only [Matrix.mulVec, dotProduct]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [bandEntry, dite_eq_left (by omega), hband i j h.1 h.2]
    · rcases not_and_or.1 h with h | h
      · rw [hq i j (by omega), zero_mul]
      · rw [hp i j (by omega), zero_mul]
  · have := idRun_foldlM_update_apply
      (fun (i : Fin n) (b : ℝ) => (pure (b + bandEntry Aband i j * x j) : Id ℝ))
      _ ((List.nodup_finRange n).filter
        (fun (i : Fin n) => decide ((j : ℕ) ≤ i + q ∧ (i : ℕ) ≤ j + p))) y i
    simp only [pure_bind] at this ⊢
    refine this.trans ?_
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, Id.run_pure]
    split_ifs <;> simp

/-- The index `j n − j(j+1)/2 + i` of `a_ij`, `j ≤ i`, in the packed storage (1.2.2) is in range. -/
theorem packedIndex_lt {n : ℕ} {i j : Fin n} (h : j ≤ i) :
    packedIndex n i j < n * (n + 1) / 2 := by
  unfold packedIndex
  have hi := i.isLt
  have hji : (j : ℕ) ≤ i := h
  obtain ⟨a, ha⟩ : ∃ a, (j : ℕ) * (j + 1) = 2 * a :=
    ⟨j * (j + 1) / 2, (Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self j)).symm⟩
  obtain ⟨b, hb⟩ : ∃ b, n * (n + 1) = 2 * b :=
    ⟨n * (n + 1) / 2, (Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)).symm⟩
  rw [ha, hb, Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos]
  have key : (j : ℤ) * n + i < b + a := by
    have ha' : ((j : ℕ) : ℤ) * (j + 1) = 2 * a := by exact_mod_cast ha
    have hb' : (n : ℤ) * (n + 1) = 2 * b := by exact_mod_cast hb
    have hi' : ((i : ℕ) : ℤ) + 1 ≤ n := by exact_mod_cast hi
    have hji' : ((j : ℕ) : ℤ) ≤ i := by exact_mod_cast hji
    nlinarith [sq_nonneg (2 * ((n : ℤ) - j) - 1)]
  have hle : a ≤ (j : ℕ) * n := by
    have : (j : ℕ) + 1 ≤ 2 * n := by omega
    nlinarith
  omega

/-- **Algorithm 1.2.3 overwrites `y` with `y + Ax`** when `A` is symmetric and `Avec` stores its
lower triangle as in (1.2.2), `A.vec(j n − j(j+1)/2 + i) = a_ij` for `j ≤ i`. The first inner loop
reads `a_ji = a_ij` by symmetry. -/
theorem algorithm_1_2_3_spec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (Avec : Fin (n * (n + 1) / 2) → ℝ)
    (hvec : ∀ (i j : Fin n) (h : j ≤ i),
      Avec ⟨packedIndex n i j, packedIndex_lt h⟩ = A i j)
    (x y : Fin n → ℝ) :
    Id.run (algorithm_1_2_3 pure Avec x y) = y + A *ᵥ x := by
  have hentry : ∀ i j : Fin n, j ≤ i →
      packedEntry Avec (packedIndex n i j) = A i j := fun i j h => by
    rw [packedEntry, dite_eq_left (packedIndex_lt h), hvec i j h]
  funext i
  unfold algorithm_1_2_3
  rw [List.idRun_foldlM, List.foldl_apply_of_pi _ (fun j i b => b + A i j * x j)
    (fun y j i => ?_), List.foldl_add_eq_add_sum_map, Pi.add_apply, ← Fin.sum_univ_def]
  · rfl
  · -- the two inner loops write the entries below and from `j` on, once each
    have h₁ := idRun_foldlM_update_apply
      (fun (i : Fin n) (b : ℝ) => (pure (b + packedEntry Avec (packedIndex n j i) * x j) : Id ℝ))
      _ ((List.nodup_finRange n).filter (fun i => decide (i < j)))
    have h₂ := idRun_foldlM_update_apply
      (fun (i : Fin n) (b : ℝ) => (pure (b + packedEntry Avec (packedIndex n i j) * x j) : Id ℝ))
      _ ((List.nodup_finRange n).filter (fun i => decide (j ≤ i)))
    simp only [pure_bind] at h₁ h₂
    simp only [Id.run_bind, pure_bind]
    refine (h₂ _ i).trans ?_
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, Id.run_pure]
    rw [h₁]
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, Id.run_pure]
    rcases lt_or_ge i j with hij | hij
    · rw [ite_eq_right (not_le.2 hij), ite_eq_left hij, hentry j i hij.le, hA.apply i j]
    · rw [ite_eq_left hij, ite_eq_right (not_lt.2 hij), hentry i j hij]

/-! ### Permutation matrices (§1.2.8–1.2.10) -/

/-- **§1.2.10**: for `P = I_n(v,:) = v.permMatrix ℝ`, "`y = Px ⇒ y_i = x_{v_i}`" and
"`y = Pᵀx ⇒ y(v) = x`", i.e. `Pᵀ x = x ∘ v⁻¹`. -/
theorem permutation_mulVec {n : ℕ} (v : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    v.permMatrix ℝ *ᵥ x = x ∘ v ∧ (v.permMatrix ℝ)ᵀ *ᵥ x = x ∘ v.symm := by
  refine ⟨Matrix.permMatrix_mulVec v, ?_⟩
  rw [Matrix.transpose_permMatrix, Matrix.permMatrix_mulVec]
  rfl

/-- **§1.2.10**: "the inverse of a permutation matrix is its transpose": `PᵀP = PPᵀ = I`. -/
theorem permutation_transpose_mul_self {n : ℕ} (v : Equiv.Perm (Fin n)) :
    (v.permMatrix ℝ)ᵀ * v.permMatrix ℝ = 1 ∧ v.permMatrix ℝ * (v.permMatrix ℝ)ᵀ = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul,
    mul_inv_cancel, inv_mul_cancel, Matrix.permMatrix_one]
  exact ⟨rfl, rfl⟩

/-- **§1.2.10**: for `P = I_m(v,:)` and `Q = I_n(w,:)`, `PAQᵀ = A(v, w)`; and
`I_n(v,:) · I_n(w,:) = I_n(w(v),:)`, the composite `w(v)` being `i ↦ w (v i)`, `v.trans w`. -/
theorem permutation_mul_mul_transpose {m n : ℕ} (v : Equiv.Perm (Fin m))
    (w : Equiv.Perm (Fin n)) (A : Matrix (Fin m) (Fin n) ℝ) :
    v.permMatrix ℝ * A * (w.permMatrix ℝ)ᵀ = A.submatrix v w ∧
      ∀ v' w' : Equiv.Perm (Fin m),
        v'.permMatrix ℝ * w'.permMatrix ℝ = Equiv.Perm.permMatrix ℝ (v'.trans w') := by
  refine ⟨?_, fun v' w' => (Matrix.permMatrix_mul w' v').symm⟩
  rw [Matrix.transpose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  rfl

/-! ### Three famous permutation matrices (§1.2.11) -/

/-- **§1.2.11, the exchange permutation**: `ℰ_n = I_n(v,:)` with `v = n:−1:1`, i.e. the permutation
matrix of `Fin.revPerm`, "turns vectors upside down": `ℰ_n x = x ∘ rev`. -/
theorem exchange_eq_permMatrix_rev (n : ℕ) :
    (Matrix.exchange n : Matrix (Fin n) (Fin n) ℝ) =
        (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix ℝ ∧
      ∀ x : Fin n → ℝ, Matrix.exchange n *ᵥ x = x ∘ Fin.rev :=
  ⟨Matrix.exchange_eq_permMatrix n, fun x => funext fun i => Matrix.exchange_mulVec_apply x i⟩

/-- **§1.2.11**: "no change results if a vector is turned upside down twice and thus
`ℰ_nᵀ ℰ_n = ℰ_n² = I_n`". -/
theorem exchange_mul_self (n : ℕ) :
    (Matrix.exchange n : Matrix (Fin n) (Fin n) ℝ)ᵀ * Matrix.exchange n = 1 ∧
      (Matrix.exchange n : Matrix (Fin n) (Fin n) ℝ) * Matrix.exchange n = 1 := by
  rw [Matrix.transpose_exchange]
  exact ⟨Matrix.exchange_mul_exchange, Matrix.exchange_mul_exchange⟩

/-- **§1.2.11, the downshift permutation** `𝒟_n`, which "pushes the components of a vector down one
notch with wraparound": `(𝒟_n x)_0 = x_{n−1}`, `(𝒟_n x)_i = x_{i−1}` (`downshift_mulVec`), as the
book's displayed `𝒟_4`. The book's formula `𝒟_n = I_n(v,:)` with `v = [(2:n) 1]` gives the
*upshift* `𝒟_nᵀ` instead (`transpose_downshift`); the definition follows the display and the
name. It is the backbone's `Matrix.downshift`, `I_n(v,:)` for `v = [n, 1:n−1]`. -/
def downshift (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.downshift n

/-- The downshift pushes a vector down: `𝒟_n x = x ∘ (finRotate n)⁻¹`. -/
theorem downshift_mulVec {n : ℕ} (x : Fin n → ℝ) : downshift n *ᵥ x = x ∘ (finRotate n).symm :=
  Matrix.downshift_mulVec x

/-- `𝒟_nᵀ = I_n(v,:)` for `v = [(2:n) 1]`, the upshift. -/
theorem transpose_downshift (n : ℕ) : (downshift n)ᵀ = (finRotate n).permMatrix ℝ := by
  rw [downshift, Matrix.downshift, Matrix.transpose_permMatrix]
  rfl

/-- **§1.2.11, the mod-`p` perfect shuffle** `𝒫_{p,r}`, `n = pr`:
`(𝒫_{p,r} x)(a p + b) = x(b r + a)`
for `a < r`, `b < p` — the deck `x` cut into `p` piles of `r` cards and reassembled by taking one
card from each pile in turn, `y = [x(1:r:n); x(2:r:n); …; x(r:r:n)]`. Positions are
`finProdFinEquiv (a, b) = a p + b` and `finProdFinEquiv (b, a) = b r + a`. -/
theorem perfectShuffle_mulVec_eq {p r : ℕ} (x : Fin (p * r) → ℝ) (a : Fin r) (b : Fin p) :
    (Matrix.perfectShuffle p r *ᵥ x) (finProdFinEquiv (a, b)) = x (finProdFinEquiv (b, a)) ∧
      ((finProdFinEquiv (a, b) : Fin (r * p)) : ℕ) = a * p + b ∧
      ((finProdFinEquiv (b, a) : Fin (p * r)) : ℕ) = b * r + a := by
  refine ⟨Matrix.perfectShuffle_mulVec_apply p r x b a, ?_, ?_⟩ <;>
    simp only [finProdFinEquiv_apply_val] <;> ring

/-- **(1.2.4)**: `𝒫_{p,r}ᵀ = I_n([(1:p:n) (2:p:n) ⋯ (p:p:n)], :)`, which is `𝒫_{r,p}` by
definition. -/
theorem equation_1_2_4 (p r : ℕ) :
    (Matrix.perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) ℝ)ᵀ =
      Matrix.perfectShuffle r p :=
  Matrix.transpose_perfectShuffle p r

end GolubVanLoan.Chapter01
