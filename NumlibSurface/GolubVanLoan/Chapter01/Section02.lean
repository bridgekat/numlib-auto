/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.Permutation
import NumlibSurface.GolubVanLoan.Chapter01.Section01

/-!
# Golub and Van Loan, Section 1.2: Structure and efficiency

This module formalizes §1.2 of [golub2013matrix], on matrices with structure. A matrix $A$ has lower
bandwidth $p$ if $a_{ij} = 0$ whenever $i > j + p$, and upper bandwidth $q$ if $a_{ij} = 0$ whenever
$j > i + q$. The module states the band terminology of Table 1.2.1 in these terms. It defines
triangular matrix multiplication (Algorithm 1.2.1) and the gaxpys for a band matrix in band storage
and for a symmetric matrix in packed storage (Algorithms 1.2.2–1.2.3), and proves that in exact
arithmetic they compute $C + AB$ and $y + Ax$. It also proves the basic facts of §1.2.10 about
permutation matrices $I_n(v,:)$, and those of §1.2.11 about the exchange permutation
$\mathcal{E}_n$, the downshift permutation $\mathcal{D}_n$ and the perfect shuffle
$\mathcal{P}_{p,r}$, with (1.2.4).

Bandwidth comes from `Numlib.LinearAlgebra.Matrix.Band`, and the exchange, downshift and perfect
shuffle come from `Numlib.LinearAlgebra.Matrix.Permutation`. The programs follow the conventions of
`GolubVanLoan.Chapter01.algorithm_1_1_1` and `Numlib.FloatingPoint.Program`.

## Main definitions

* Algorithm 1.2.1, `GolubVanLoan.Chapter01.algorithm_1_2_1`: triangular matrix multiplication
  $C \leftarrow C + AB$.
* Algorithm 1.2.2, `GolubVanLoan.Chapter01.algorithm_1_2_2`: the band storage gaxpy
  $y \leftarrow y + Ax$.
* Algorithm 1.2.3, `GolubVanLoan.Chapter01.algorithm_1_2_3`: the symmetric storage gaxpy
  $y \leftarrow y + Ax$.
* §1.2.11, `GolubVanLoan.Chapter01.downshift`: the downshift permutation $\mathcal{D}_n$.

## Main results

* Table 1.2.1, `GolubVanLoan.Chapter01.table_1_2_1`: diagonal, triangular, tridiagonal, bidiagonal
  and Hessenberg square matrices are the matrices with the bandwidths of the table.
* Algorithm 1.2.1, `GolubVanLoan.Chapter01.algorithm_1_2_1_spec`: for upper triangular $A$ and $B$,
  in exact arithmetic the algorithm returns $C + AB$.
* Algorithm 1.2.2, `GolubVanLoan.Chapter01.algorithm_1_2_2_spec`: for a band matrix $A$ in band
  storage (1.2.1), in exact arithmetic the algorithm returns $y + Ax$.
* Algorithm 1.2.3, `GolubVanLoan.Chapter01.algorithm_1_2_3_spec`: for a symmetric matrix $A$ in
  packed storage (1.2.2), in exact arithmetic the algorithm returns $y + Ax$.
* §1.2.10, `GolubVanLoan.Chapter01.permutation_mulVec`: for $P = I_n(v,:)$, $(Px)_i = x_{v(i)}$ and
  $P^T x = x \circ v^{-1}$.
* §1.2.10, `GolubVanLoan.Chapter01.permutation_transpose_mul_self`: $P^T P = P P^T = I$.
* §1.2.10, `GolubVanLoan.Chapter01.permutation_mul_mul_transpose`: for $P = I_m(v,:)$ and
  $Q = I_n(w,:)$, $PAQ^T = A(v, w)$.
* §1.2.10, `GolubVanLoan.Chapter01.permMatrix_mul_permMatrix_eq`:
  $I_n(v,:) \, I_n(w,:) = I_n(w(v),:)$.
* §1.2.11, `GolubVanLoan.Chapter01.exchange_eq_permMatrix_rev`: $\mathcal{E}_n$ is the permutation
  matrix of the reversal and turns vectors upside down.
* §1.2.11, `GolubVanLoan.Chapter01.exchange_mul_self`: $\mathcal{E}_n^T \mathcal{E}_n =
  \mathcal{E}_n^2 = I_n$.
* §1.2.11, `GolubVanLoan.Chapter01.perfectShuffle_mulVec_eq`:
  $(\mathcal{P}_{p,r} x)(ap + b) = x(br + a)$.
* Equation (1.2.4), `GolubVanLoan.Chapter01.equation_1_2_4`:
  $\mathcal{P}_{p,r}^T = \mathcal{P}_{r,p}$.

## Conventions

* Indices are 0-based. The band storage (1.2.1) $\mathrm{A.band}(i - j + q + 1, j) = a_{ij}$ reads
  `Aband ⟨i + q - j, _⟩ j = A i j` for $j \le i + q$ and $i \le j + p$. The packed storage (1.2.2)
  $\mathrm{A.vec}((n - j/2)(j - 1) + i) = a_{ij}$ reads
  `Avec ⟨j * n - j * (j + 1) / 2 + i, _⟩ = A i j` for $j \le i$.
* The permutation matrix $I_n(v,:)$ of a permutation $v$ is Mathlib's `v.permMatrix ℝ`, whose row
  $i$ is $e_{v(i)}^T$.
* The exchange $\mathcal{E}_n$, the downshift $\mathcal{D}_n$ and the perfect shuffle
  $\mathcal{P}_{p,r}$ are `Matrix.exchange`, `Matrix.downshift` and `Matrix.perfectShuffle`.

## Implementation notes

* Bandwidth is `Matrix.HasLowerBandwidth` and `Matrix.HasUpperBandwidth` on square matrices. On
  `Fin n` they read $a_{ij} = 0$ whenever $i > j + p$, and $a_{ij} = 0$ whenever $j > i + q$, which
  is the definition of §1.2.1 in 0-based and in 1-based indexing alike
  (`Matrix.hasLowerBandwidth_iff_fin`, `Matrix.hasUpperBandwidth_iff_fin`). The rectangular forms,
  for the $m \times n$ matrices of Table 1.2.1, are `Matrix.HasLowerBandwidthRect` and
  `Matrix.HasUpperBandwidthRect`.
* The storage schemes (1.2.1) and (1.2.2) are not objects of their own. Each one is a hypothesis of
  the specification of its algorithm, which relates the stored array to the matrix. The programs
  read the arrays through `GolubVanLoan.Chapter01.bandEntry` and
  `GolubVanLoan.Chapter01.packedEntry`, whose values outside the stored range are arbitrary and are
  never read.
* The integer index arithmetic of the source ($\alpha_1, \alpha_2, \beta_1, \beta_2$ in Algorithm
  1.2.2, and the positions in the packed array in Algorithm 1.2.3) is done in `ℕ` and is not
  rounded. In Algorithm 1.2.2 it becomes a filter on the index list of the loop.
* The exact specifications are proved in exact arithmetic (`M := Id`). The loops are fused into
  updates of single entries (`Matrix.foldlM_updateRow_entrywise`, `Matrix.foldlM_updateRow_update`),
  a loop that writes one entry per step over a list without duplicates is evaluated entry by entry,
  and a loop that acts on every entry independently is interchanged with the entry
  (`List.foldl_apply_of_pi`).
* In Table 1.2.1, a matrix is lower Hessenberg when its transpose is upper Hessenberg, since the
  library has no separate predicate for lower Hessenberg matrices.

## Deviations from the source

* **Algorithm 1.2.1** (generalization). The source takes $C$ upper triangular; the specification
  holds for every $C$. See `GolubVanLoan.Chapter01.algorithm_1_2_1_spec`.
* **§1.2.11, the downshift** (typo). The source's formula $\mathcal{D}_n = I_n(v,:)$ with
  $v = [(2{:}n)\ 1]$ gives the upshift $\mathcal{D}_n^T$; the definition follows the displayed
  $\mathcal{D}_4$ and the name. See `GolubVanLoan.Chapter01.downshift`.

## Not formalized

* **The flop sums of §1.2.4.** Operation counts are out of scope for the library.
* **Diagonal scaling, §1.2.6.** Mathlib supplies it as `Matrix.diagonal_mul` and
  `Matrix.mul_diagonal`.
* **The prose definitions of symmetric, skew-symmetric, Hermitian and skew-Hermitian matrices.**
  Mathlib supplies them, for example as `Matrix.IsSymm` and `Matrix.IsHermitian`.
* **The example (1.2.3).**
* **The index vectors of §1.2.9.** They are maps on `Fin n`.
* **The operation count $2n(p + q + 1)$ after Algorithm 1.2.2.** Operation counts are out of scope
  for the library.
* **Table 1.2.1 for rectangular matrices.** The table is stated for square matrices only, where the
  triangular, bidiagonal and Hessenberg predicates are defined.
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter01

/-! ### Table 1.2.1: band terminology -/

/-- **Table 1.2.1** of [golub2013matrix] (band terminology). Let $A \in \mathbb{R}^{n \times n}$.
Then $A$ is diagonal, upper triangular, lower triangular, tridiagonal, upper bidiagonal, lower
bidiagonal, upper Hessenberg or lower Hessenberg if and only if it has, respectively, the lower
and upper bandwidths
$$(0, 0),\ (0, n - 1),\ (n - 1, 0),\ (1, 1),\ (0, 1),\ (1, 0),\ (1, n - 1),\ (n - 1, 1).$$

The source's table is for $m \times n$ matrices. The rows are stated for square matrices, where
the triangular, bidiagonal and Hessenberg predicates of Mathlib and of the backbone are defined.
A matrix is lower Hessenberg here when its transpose $A^T$ is upper Hessenberg. -/
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
      Matrix.hasLowerBandwidth_transpose_iff]
    exact ⟨fun h => ⟨hlow, h⟩, And.right⟩

/-! ### Algorithms 1.2.1–1.2.3 -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 1.2.1** of [golub2013matrix] (triangular matrix multiplication). "Given upper
triangular matrices $A, B, C \in \mathbb{R}^{n \times n}$, this algorithm overwrites $C$ with
$C + AB$":
```
for i = 1:n
    for j = i:n
        for k = i:j
            C(i,j) = C(i,j) + A(i,k) B(k,j)
        end
    end
end
```
The program computes $c_{ij} \leftarrow \mathrm{fl}(c_{ij} + \mathrm{fl}(a_{ik} b_{kj}))$ in
this loop order.

The ranges $j = i{:}n$ and $k = i{:}j$ are filtered index lists. -/
def algorithm_1_2_1 {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun C i =>
    ((List.finRange n).filter (i ≤ ·)).foldlM (fun C j =>
      ((List.finRange n).filter (fun k => i ≤ k ∧ k ≤ j)).foldlM (fun C k => do
        let p ← rnd (A i k * B k j)
        let c ← rnd (C i j + p)
        pure (C.updateRow i (Function.update (C i) j c))) C) C) C

/-- The entry $\mathrm{A.band}(i - j + q + 1, j)$ of the band storage (1.2.1), which is
`Aband ⟨i + q - j, _⟩ j` in 0-based indices. Below the band, where $i > j + p$, the value is
$0$. Above the band, where $j > i + q$, the subtraction in `ℕ` truncates to $0$ and the value is
the unrelated entry `Aband 0 j`. Algorithm 1.2.2 reads only entries inside the band. -/
def bandEntry {p q n : ℕ} (Aband : Matrix (Fin (p + q + 1)) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  if h : (i : ℕ) + q - j < p + q + 1 then Aband ⟨i + q - j, h⟩ j else 0

/-- **Algorithm 1.2.2** of [golub2013matrix] (band storage gaxpy). "Suppose
$A \in \mathbb{R}^{n \times n}$ has lower bandwidth $p$ and upper bandwidth $q$ and is stored in
the $\mathrm{A.band}$ format (1.2.1). If $x, y \in \mathbb{R}^n$, then this algorithm overwrites
$y$ with $y + Ax$":
```
for j = 1:n
    α₁ = max(1, j − q), α₂ = min(n, j + p)
    β₁ = max(1, q + 2 − j), β₂ = β₁ + α₂ − α₁
    y(α₁:α₂) = y(α₁:α₂) + A.band(β₁:β₂, j) x(j)
end
```
The program computes $y_i \leftarrow \mathrm{fl}(y_i + \mathrm{fl}(a_{ij} x_j))$ in this loop
order, where $a_{ij}$ is read from the band storage.

The rows $\alpha_1{:}\alpha_2$ are the indices $i$ with $j \le i + q$ and $i \le j + p$, and
$\mathrm{A.band}(\beta_1{:}\beta_2, j)$ lists their entries `Aband ⟨i + q - j, _⟩ j`. -/
def algorithm_1_2_2 {n : ℕ} (p q : ℕ) (Aband : Matrix (Fin (p + q + 1)) (Fin n) ℝ)
    (x y : Fin n → ℝ) : M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (y : Fin n → ℝ) (j : Fin n) =>
    ((List.finRange n).filter (fun (i : Fin n) => (j : ℕ) ≤ i + q ∧ (i : ℕ) ≤ j + p)).foldlM
      (fun (y : Fin n → ℝ) (i : Fin n) => do
      let t ← rnd (bandEntry Aband i j * x j)
      let s ← rnd (y i + t)
      pure (Function.update y i s)) y) y

/-- The position $jn - j(j+1)/2 + i$ of $a_{ij}$, for $j \le i$, in the packed storage (1.2.2), in
0-based indices. It is the source's $(n - j/2)(j - 1) + i$ with $i$ and $j$ replaced by $i + 1$
and $j + 1$, minus one. -/
def packedIndex (n : ℕ) (i j : Fin n) : ℕ :=
  (j : ℕ) * n - (j : ℕ) * ((j : ℕ) + 1) / 2 + (i : ℕ)

/-- The entry $\mathrm{A.vec}(k)$ of the packed symmetric storage (1.2.2), in 0-based indices, and
$0$ for $k$ outside the array. Algorithm 1.2.3 reads only inside the array. -/
def packedEntry {n : ℕ} (Avec : Fin (n * (n + 1) / 2) → ℝ) (k : ℕ) : ℝ :=
  if h : k < n * (n + 1) / 2 then Avec ⟨k, h⟩ else 0

/-- **Algorithm 1.2.3** of [golub2013matrix] (symmetric storage gaxpy). "Suppose
$A \in \mathbb{R}^{n \times n}$ is symmetric and stored in the $\mathrm{A.vec}$ style (1.2.2).
If $x, y \in \mathbb{R}^n$, then this algorithm overwrites $y$ with $y + Ax$":
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
The program computes $y_i \leftarrow \mathrm{fl}(y_i + \mathrm{fl}(a_{ij} x_j))$ in this loop
order, where $a_{ij}$ is read from the packed storage.

In 0-based indices the positions are $in - i(i+1)/2 + j$ and $jn - j(j+1)/2 + i$. They are
computed in `ℕ`, as integer arithmetic, and are not rounded. -/
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

/-- The loop over the row $i$ of Algorithm 1.2.1 after fusion: for each $j \ge i$, the shortened
inner product $\sum_{k=i}^{j} a_{ik} b_{kj}$ accumulated onto $c_{ij}$. -/
private def triangularRow {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (row : Fin n → ℝ) : M (Fin n → ℝ) :=
  ((List.finRange n).filter (i ≤ ·)).foldlM (fun row j => do
    let c ← dotAccum rnd ((List.finRange n).filter (fun k => i ≤ k ∧ k ≤ j)) (A i)
      (fun k => B k j) (row j)
    pure (Function.update row j c)) row

/-- Algorithm 1.2.1 is a loop that writes one row per step. -/
private theorem algorithm_1_2_1_eq {M : Type → Type} [Monad M] [LawfulMonad M] (rnd : ℝ → M ℝ)
    {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) :
    algorithm_1_2_1 rnd A B C = (List.finRange n).foldlM (fun C i => do
      let row ← triangularRow rnd A B i (C i); pure (C.updateRow i row)) C := by
  unfold algorithm_1_2_1
  congr 1
  funext C i
  rw [triangularRow, ← Matrix.foldlM_updateRow_entrywise i (fun j c =>
    dotAccum rnd ((List.finRange n).filter (fun k => i ≤ k ∧ k ≤ j)) (A i) (fun k => B k j) c)]
  congr 1
  funext C j
  have := Matrix.foldlM_updateRow_update i j
    (fun k c => do let p ← rnd (A i k * B k j); rnd (c + p))
    ((List.finRange n).filter (fun k => i ≤ k ∧ k ≤ j)) C
  simp only [bind_assoc] at this
  exact this

/-- **Algorithm 1.2.1** of [golub2013matrix], exact correctness. Let
$A, B \in \mathbb{R}^{n \times n}$ be upper triangular, and let $C \in \mathbb{R}^{n \times n}$.
In exact arithmetic, Algorithm 1.2.1 returns $C + AB$.

**Generalization.** The source takes $C$ upper triangular as well. The statement does not need
it.

For $i \le j$ the shortened inner product $\sum_{k=i}^{j} a_{ik} b_{kj}$ is $(AB)_{ij}$, because
$a_{ik} b_{kj} = 0$ whenever $k < i$ or $j < k$. The entries with $j < i$ are not changed, and
there $(AB)_{ij} = 0$. -/
theorem algorithm_1_2_1_spec {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) :
    Id.run (algorithm_1_2_1 pure A B C) = C + A * B := by
  rw [algorithm_1_2_1_eq]
  ext i j
  rw [Matrix.idRun_foldlM_updateRow_apply _ _ (List.nodup_finRange n),
    ite_eq_left (List.mem_finRange i), triangularRow,
    List.idRun_foldlM_update_apply _ _ ((List.nodup_finRange n).filter _),
    Matrix.add_apply, Matrix.mul_apply]
  split_ifs with hij
  · rw [dotAccum_id, List.sum_map_filter_finRange (fun k => i ≤ k ∧ k ≤ j),
      Finset.sum_filter]
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

/-- **Algorithm 1.2.2** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
have lower bandwidth $p$ and upper bandwidth $q$, and let the array $\mathrm{A.band} \in
\mathbb{R}^{(p+q+1) \times n}$ store $A$ in the format (1.2.1):
$\mathrm{A.band}(i + q - j, j) = a_{ij}$ (0-based) whenever $j \le i + q$ and $i \le j + p$. Let
$x, y \in \mathbb{R}^n$. In exact arithmetic, Algorithm 1.2.2 returns $y + Ax$.

The proof is as for Algorithm 1.1.4. The terms of $(Ax)_i$ outside the band are zero by the
bandwidths. -/
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
  · have := List.idRun_foldlM_update_apply
      (fun (i : Fin n) (b : ℝ) => (pure (b + bandEntry Aband i j * x j) : Id ℝ))
      _ ((List.nodup_finRange n).filter
        (fun (i : Fin n) => decide ((j : ℕ) ≤ i + q ∧ (i : ℕ) ≤ j + p))) y i
    simp only [pure_bind] at this ⊢
    refine this.trans ?_
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, Id.run_pure]
    split_ifs <;> simp

/-- For $j \le i$, the position $jn - j(j+1)/2 + i$ of $a_{ij}$ in the packed storage (1.2.2) is
less than $n(n+1)/2$, the length of the array. -/
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

/-- **Algorithm 1.2.3** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, and let the array $\mathrm{A.vec} \in \mathbb{R}^{n(n+1)/2}$ store its lower
triangle as in (1.2.2): $\mathrm{A.vec}(jn - j(j+1)/2 + i) = a_{ij}$ (0-based) for $j \le i$.
Let $x, y \in \mathbb{R}^n$. In exact arithmetic, Algorithm 1.2.3 returns $y + Ax$.

The first inner loop reads $a_{ji} = a_{ij}$ by symmetry. -/
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
    have h₁ := List.idRun_foldlM_update_apply
      (fun (i : Fin n) (b : ℝ) => (pure (b + packedEntry Avec (packedIndex n j i) * x j) : Id ℝ))
      _ ((List.nodup_finRange n).filter (fun i => decide (i < j)))
    have h₂ := List.idRun_foldlM_update_apply
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

/-- **§1.2.10** of [golub2013matrix], action on vectors. Let $v$ be a permutation of
$\{1, \dots, n\}$, let $P = I_n(v,:)$, and let $x \in \mathbb{R}^n$. Then $y = Px$ has
$y_i = x_{v(i)}$, and $y = P^T x$ has $y(v) = x$, that is,
$$Px = x \circ v, \qquad P^T x = x \circ v^{-1}.$$

The matrix $P$ is `v.permMatrix ℝ`. -/
theorem permutation_mulVec {n : ℕ} (v : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    v.permMatrix ℝ *ᵥ x = x ∘ v ∧ (v.permMatrix ℝ)ᵀ *ᵥ x = x ∘ v.symm := by
  refine ⟨Matrix.permMatrix_mulVec v, ?_⟩
  rw [Matrix.transpose_permMatrix, Matrix.permMatrix_mulVec]
  rfl

/-- **§1.2.10** of [golub2013matrix]: "the inverse of a permutation matrix is its transpose". For
every permutation $v$ of $\{1, \dots, n\}$ and $P = I_n(v,:)$,
$$P^T P = P P^T = I.$$
-/
theorem permutation_transpose_mul_self {n : ℕ} (v : Equiv.Perm (Fin n)) :
    (v.permMatrix ℝ)ᵀ * v.permMatrix ℝ = 1 ∧ v.permMatrix ℝ * (v.permMatrix ℝ)ᵀ = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul,
    mul_inv_cancel, inv_mul_cancel, Matrix.permMatrix_one]
  exact ⟨rfl, rfl⟩

/-- **§1.2.10** of [golub2013matrix], permuting rows and columns. Let $v$ and $w$ be permutations of
$\{1, \dots, m\}$ and $\{1, \dots, n\}$, let $P = I_m(v,:)$ and $Q = I_n(w,:)$, and let
$A \in \mathbb{R}^{m \times n}$. Then
$$P A Q^T = A(v, w),$$
the matrix with entries $a_{v(i), w(j)}$. -/
theorem permutation_mul_mul_transpose {m n : ℕ} (v : Equiv.Perm (Fin m))
    (w : Equiv.Perm (Fin n)) (A : Matrix (Fin m) (Fin n) ℝ) :
    v.permMatrix ℝ * A * (w.permMatrix ℝ)ᵀ = A.submatrix v w := by
  rw [Matrix.transpose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  rfl

/-- **§1.2.10** of [golub2013matrix], products of permutation matrices. For permutations $v$ and $w$
of $\{1, \dots, n\}$,
$$I_n(v,:) \, I_n(w,:) = I_n(w(v),:),$$
where $w(v)$ is the composite permutation $i \mapsto w(v(i))$.

The composite $w(v)$ is `v.trans w`. -/
theorem permMatrix_mul_permMatrix_eq {n : ℕ} (v w : Equiv.Perm (Fin n)) :
    v.permMatrix ℝ * w.permMatrix ℝ = Equiv.Perm.permMatrix ℝ (v.trans w) :=
  (Matrix.permMatrix_mul w v).symm

/-! ### Three famous permutation matrices (§1.2.11) -/

/-- **§1.2.11** of [golub2013matrix], the exchange permutation. The exchange matrix $\mathcal{E}_n$
is $I_n(v,:)$ with $v = n{:}{-1}{:}1$, the permutation matrix of the reversal
$i \mapsto n + 1 - i$, and it "turns vectors upside down": for every $x \in \mathbb{R}^n$,
$(\mathcal{E}_n x)_i = x_{n+1-i}$.

The reversal is `Fin.revPerm`, which maps $i$ to $n - 1 - i$ in 0-based indices. -/
theorem exchange_eq_permMatrix_rev (n : ℕ) :
    (Matrix.exchange n : Matrix (Fin n) (Fin n) ℝ) =
        (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix ℝ ∧
      ∀ x : Fin n → ℝ, Matrix.exchange n *ᵥ x = x ∘ Fin.rev :=
  ⟨Matrix.exchange_eq_permMatrix n, fun x => funext fun i => Matrix.exchange_mulVec_apply x i⟩

/-- **§1.2.11** of [golub2013matrix]: "no change results if a vector is turned upside down twice and
thus $\mathcal{E}_n^T \mathcal{E}_n = \mathcal{E}_n^2 = I_n$". That is,
$\mathcal{E}_n^T \mathcal{E}_n = I_n$ and $\mathcal{E}_n \mathcal{E}_n = I_n$. -/
theorem exchange_mul_self (n : ℕ) :
    (Matrix.exchange n : Matrix (Fin n) (Fin n) ℝ)ᵀ * Matrix.exchange n = 1 ∧
      (Matrix.exchange n : Matrix (Fin n) (Fin n) ℝ) * Matrix.exchange n = 1 := by
  rw [Matrix.transpose_exchange]
  exact ⟨Matrix.exchange_mul_exchange, Matrix.exchange_mul_exchange⟩

/-- **§1.2.11** of [golub2013matrix], the downshift permutation. The downshift
$\mathcal{D}_n \in \mathbb{R}^{n \times n}$ "pushes the components of a vector down one notch
with wraparound": $(\mathcal{D}_n x)_1 = x_n$ and $(\mathcal{D}_n x)_i = x_{i-1}$ for $i > 1$
(`GolubVanLoan.Chapter01.downshift_mulVec`), as in the displayed $\mathcal{D}_4$ of the source.
It is $I_n(v,:)$ for $v = [n, 1{:}n{-}1]$.

**Typo.** The source's formula $\mathcal{D}_n = I_n(v,:)$ with $v = [(2{:}n)\ 1]$ gives the
upshift $\mathcal{D}_n^T$ instead (`GolubVanLoan.Chapter01.transpose_downshift`). The definition
follows the displayed $\mathcal{D}_4$ and the name.

The definition is the backbone's `Matrix.downshift`. -/
def downshift (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.downshift n

/-- The downshift pushes a vector down one place with wraparound:
$\mathcal{D}_n x = x \circ \rho^{-1}$, where $\rho$ is the cyclic rotation $i \mapsto i + 1$ of
the indices (`finRotate n`). -/
theorem downshift_mulVec {n : ℕ} (x : Fin n → ℝ) : downshift n *ᵥ x = x ∘ (finRotate n).symm :=
  Matrix.downshift_mulVec x

/-- The transpose of the downshift is the upshift: $\mathcal{D}_n^T = I_n(v,:)$ for
$v = [(2{:}n)\ 1]$, the permutation matrix of the cyclic rotation $i \mapsto i + 1$
(`finRotate n`). -/
theorem transpose_downshift (n : ℕ) : (downshift n)ᵀ = (finRotate n).permMatrix ℝ := by
  rw [downshift, Matrix.downshift, Matrix.transpose_permMatrix]
  rfl

/-- **§1.2.11** of [golub2013matrix], the mod-$p$ perfect shuffle. Let $n = pr$ and
$x \in \mathbb{R}^n$. The perfect shuffle $\mathcal{P}_{p,r}$ cuts the deck $x$ into $p$ piles
of $r$ cards and reassembles it by taking one card from each pile in turn, $y = [x(1{:}r{:}n);
x(2{:}r{:}n); \dots; x(r{:}r{:}n)]$. In 0-based positions, for $a < r$ and $b < p$,
$$(\mathcal{P}_{p,r} x)(ap + b) = x(br + a).$$

The positions are `finProdFinEquiv (a, b)`, with value $ap + b$, and `finProdFinEquiv (b, a)`,
with value $br + a$; the statement also records these two values. -/
theorem perfectShuffle_mulVec_eq {p r : ℕ} (x : Fin (p * r) → ℝ) (a : Fin r) (b : Fin p) :
    (Matrix.perfectShuffle p r *ᵥ x) (finProdFinEquiv (a, b)) = x (finProdFinEquiv (b, a)) ∧
      ((finProdFinEquiv (a, b) : Fin (r * p)) : ℕ) = a * p + b ∧
      ((finProdFinEquiv (b, a) : Fin (p * r)) : ℕ) = b * r + a := by
  refine ⟨Matrix.perfectShuffle_mulVec_apply p r x b a, ?_, ?_⟩ <;>
    simp only [finProdFinEquiv_apply_val] <;> ring

/-- **Equation (1.2.4)** of [golub2013matrix]. For all $p$ and $r$, the transpose of the perfect
shuffle is
$$\mathcal{P}_{p,r}^T = \mathcal{P}_{r,p}.$$
The source writes the right side as $I_n([(1{:}p{:}n)\ (2{:}p{:}n)\ \cdots\ (p{:}p{:}n)], :)$,
which is $\mathcal{P}_{r,p}$ by definition. -/
theorem equation_1_2_4 (p r : ℕ) :
    (Matrix.perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) ℝ)ᵀ =
      Matrix.perfectShuffle r p :=
  Matrix.transpose_perfectShuffle p r

end GolubVanLoan.Chapter01
