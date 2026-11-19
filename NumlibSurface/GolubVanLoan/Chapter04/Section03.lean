/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.Substitution
import Numlib.LinearAlgebra.Matrix.Band
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.LU.Pivoting
import Numlib.LinearAlgebra.Matrix.Rank
import NumlibSurface.GolubVanLoan.Chapter04.Section02

/-!
# Golub and Van Loan, Section 4.3: Banded systems

This module formalizes §4.3 of [golub2013matrix]. A matrix $A \in \mathbb{R}^{n \times n}$ has upper
bandwidth $q$ if $a_{ij} = 0$ whenever $j > i + q$, and lower bandwidth $p$ if $a_{ij} = 0$ whenever
$i > j + p$. Theorem 4.3.1 says that the LU factorization preserves the band: $U$ has upper
bandwidth $q$ and $L$ has lower bandwidth $p$. Theorem 4.3.2 says that with partial pivoting the
upper bandwidth of $U$ grows to at most $p + q$, and Theorem 4.3.3 bounds the ranks of the
off-diagonal blocks of $A^{-1}$ by the bandwidths of $A$.

The module defines band Gaussian elimination, band forward substitution and band back substitution
(Algorithms 4.3.1–4.3.3), Hessenberg LU with partial pivoting (Algorithm 4.3.4), band Cholesky
(Algorithm 4.3.5) and the solver for symmetric positive definite tridiagonal systems (Algorithm
4.3.6) as programs, and proves their exact correctness. The proofs specialize
`Numlib.LinearAlgebra.Matrix.Band`, `Numlib.LinearAlgebra.Matrix.LU`,
`Numlib.LinearAlgebra.Matrix.LU.Pivoting`, `Numlib.LinearAlgebra.Matrix.Cholesky`,
`Numlib.LinearAlgebra.Matrix.Rank` and `Numlib.Direct.Substitution`.

## Main definitions

* Algorithm 4.3.1, `GolubVanLoan.Chapter04.algorithm_4_3_1`: band Gaussian elimination.
* Algorithm 4.3.2, `GolubVanLoan.Chapter04.algorithm_4_3_2`: band forward substitution.
* Algorithm 4.3.3, `GolubVanLoan.Chapter04.algorithm_4_3_3`: band back substitution.
* Algorithm 4.3.4, `GolubVanLoan.Chapter04.algorithm_4_3_4`: Hessenberg LU, with its pass
  `GolubVanLoan.Chapter04.hessenbergLUStep`.
* Algorithm 4.3.5, `GolubVanLoan.Chapter04.algorithm_4_3_5`: band Cholesky.
* Algorithm 4.3.6, `GolubVanLoan.Chapter04.algorithm_4_3_6`: the symmetric, tridiagonal, positive
  definite system solver.
* §4.3.8, `GolubVanLoan.Chapter04.blockSplit`: the partition of the indices into square diagonal
  blocks of sizes $k$ and $n - k$.

## Main results

* Theorem 4.3.1, `GolubVanLoan.Chapter04.theorem_4_3_1`: the factors of $A = LU$ inherit the
  bandwidths of $A$, also stated for each factor in `GolubVanLoan.Chapter04.theorem_4_3_1_a` and
  `GolubVanLoan.Chapter04.theorem_4_3_1_b`.
* Algorithm 4.3.1, `GolubVanLoan.Chapter04.algorithm_4_3_1_spec`: the exact run holds the LU
  factorization.
* Algorithms 4.3.2 and 4.3.3, `GolubVanLoan.Chapter04.algorithm_4_3_2_spec` and
  `GolubVanLoan.Chapter04.algorithm_4_3_3_spec`: the exact runs solve the band triangular systems.
* Theorem 4.3.2, `GolubVanLoan.Chapter04.theorem_4_3_2`: with partial pivoting, $U$ has upper
  bandwidth $p + q$, and the Gauss vectors have at most $p$ nonzero entries.
* Algorithm 4.3.4, `GolubVanLoan.Chapter04.algorithm_4_3_4_spec` and
  `GolubVanLoan.Chapter04.algorithm_4_3_4_spec_abs_le_one`: the exact run is Gaussian elimination
  with partial pivoting, and its multipliers are bounded by one.
* Algorithm 4.3.5, `GolubVanLoan.Chapter04.algorithm_4_3_5_spec`: the exact run is the Cholesky
  factor, which has the lower bandwidth of $A$.
* §4.3.6, `GolubVanLoan.Chapter04.tridiagonal_ldlt`: the $LDL^T$ factorization of a symmetric
  tridiagonal matrix.
* Algorithm 4.3.6, `GolubVanLoan.Chapter04.algorithm_4_3_6_spec`: the exact run solves the
  tridiagonal system.
* Theorem 4.3.3, `GolubVanLoan.Chapter04.theorem_4_3_3`: $\operatorname{rank}(X_{21}) \le p$ and
  $\operatorname{rank}(X_{12}) \le q$ for $X = A^{-1}$.
* §4.3.8, `GolubVanLoan.Chapter04.rank_inv_offDiag_eq`: $\operatorname{rank}(X_{21}) =
  \operatorname{rank}(A_{21})$ and $\operatorname{rank}(X_{12}) = \operatorname{rank}(A_{12})$.

## Conventions

* Matrices are real, `A : Matrix (Fin n) (Fin n) ℝ`, and indices are 0-based.
* Upper bandwidth $q$ is `Matrix.HasUpperBandwidth A q`, and lower bandwidth $p$ is
  `Matrix.HasLowerBandwidth A p`. On `Fin n` they mean $a_{ij} = 0$ whenever $j > i + q$, and
  $a_{ij} = 0$ whenever $i > j + p$ (`Matrix.hasUpperBandwidth_iff_fin`).
* The loop bounds $\min(k + p, n)$ and $\max(1, j - q)$ of the source are conditions on the index in
  the filtered index lists of the programs.
* "$A(1{:}k, 1{:}k)$ is nonsingular for $k = 1{:}n-1$" is `∀ k, IsUnit
  (A.strictLeadingPrincipalSubmatrix k)`.
* The packed LU output is read as in Chapter 3: $L$ is `GolubVanLoan.Chapter03.packedL F` and $U$ is
  `GolubVanLoan.Chapter03.packedU F`.
* Tridiagonal matrices are `Matrix.tridiagonalOf`, with diagonal, subdiagonal and superdiagonal,
  and, for the Thomas recurrences, `Matrix.tridiagonalOfNat` of sequences indexed by `ℕ`.

## Implementation notes

* The algorithms follow the algorithm conventions of `NumlibSurface.GolubVanLoan`: every product,
  difference, quotient and square root passes through the rounding hook `rnd`, and comparisons are
  exact.
* The exact specifications are proved in the monad `Id` with `rnd := pure`, by loop invariants on
  the folds (`List.foldl_finRange_induction`, `List.foldl_update_of_nodup`). The source gives no
  rounding analysis in this section.
* Theorem 4.3.3 is proved through the nullity theorem (`Matrix.rank_inv_toBlocks₂₁`), which also
  gives the equality of ranks that the source attributes to Strang and Nguyen. So the limit argument
  of the source (Problem P4.3.11) is not needed.

## Deviations from the source

* **Correction.** The combined band theorem requires nonsingular proper leading blocks for the lower
  factor. See `GolubVanLoan.Chapter04.theorem_4_3_1`.
* **Reading.** Band Gaussian elimination uses a final empty step and totalized division. See
  `GolubVanLoan.Chapter04.algorithm_4_3_1`, `GolubVanLoan.Chapter04.bandGEStepId`.
* **Reading.** The band forward-substitution program is defined before imposing its structural
  hypotheses. See `GolubVanLoan.Chapter04.algorithm_4_3_2`.
* **Reading.** Band back substitution totalizes division at zero diagonal entries. See
  `GolubVanLoan.Chapter04.algorithm_4_3_3`.
* **Reading.** Band Cholesky totalizes the column update and its square-root division. See
  `GolubVanLoan.Chapter04.algorithm_4_3_5`, `GolubVanLoan.Chapter04.bandCholStepId`.
* **Generalization.** The tridiagonal factorization requires just the nonzero pivots used as
  divisors. See `GolubVanLoan.Chapter04.tridiagonal_ldlt`.
* **Correction.** The exact forward substitution in the tridiagonal solver uses the previous
  right-hand-side entry. See `GolubVanLoan.Chapter04.algorithm_4_3_6_id`.
* **Reading.** The Hessenberg LU program includes a final unused pivot flag. See
  `GolubVanLoan.Chapter04.hessenbergLUStep`, `GolubVanLoan.Chapter04.algorithm_4_3_4`.
* **Reading.** The exact Hessenberg specification compares only flags at actual pivot steps. See
  `GolubVanLoan.Chapter04.algorithm_4_3_4_spec`.
* **Theorem 4.3.1** (correction). The statement about $L$ is false without the nonsingularity of the
  leading principal submatrices: $\begin{bmatrix} 0 & 1 \\ 0 & 2 \end{bmatrix} = \begin{bmatrix} 1 &
  0 \\ \beta & 1 \end{bmatrix} \begin{bmatrix} 0 & 1 \\ 0 & 2 - \beta \end{bmatrix}$ for every
  $\beta$. The library adds this hypothesis for $L$. See `GolubVanLoan.Chapter04.theorem_4_3_1_b`.
* **Algorithm 4.3.1** (reading). "Assuming it exists" is read as the nonsingularity of the leading
  principal submatrices $A(1{:}k, 1{:}k)$, $k = 1{:}n-1$. See
  `GolubVanLoan.Chapter04.algorithm_4_3_1_spec`.
* **Theorem 4.3.2** (generalization). The source assumes that $A$ is nonsingular. The library does
  not need this hypothesis. See `GolubVanLoan.Chapter04.theorem_4_3_2`.
* **Algorithm 4.3.6** (typo). The second loop prints $b(k) = b(k) - \beta(k-1) \cdot \beta(k-1)$.
  The forward solve $Ly = b$ is $b(k) = b(k) - \beta(k-1) \cdot b(k-1)$, which the program does. See
  `GolubVanLoan.Chapter04.algorithm_4_3_6`.

## Not formalized

* **§4.3.7, vectorization.**
* **§4.3.9, banded inverses.**
* **Band storage.**
* **Flop counts.**
* **The band $LDL^T$ factorization.** The source leaves it to the reader.
-/

open FloatingPoint Matrix Finset

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### Loop lemmas in exact arithmetic -/

/-- A sum over the indices $k < j + 1$ with $k < i$ splits into the sum over $k < j$ with $k < i$
and the term $k = j$ if $j < i$. -/
private theorem sum_filter_val_lt_succ (f : Fin n → ℝ) (i j : Fin n) :
    ∑ k ∈ univ.filter (fun k : Fin n => (k : ℕ) < j + 1 ∧ k < i), f k =
      ∑ k ∈ univ.filter (fun k : Fin n => (k : ℕ) < j ∧ k < i), f k + if j < i then f j else 0 := by
  have hterm : (if j < i then f j else 0) =
      ∑ k : Fin n, if k = j then (if j < i then f j else 0) else 0 := by simp
  rw [Finset.sum_filter, Finset.sum_filter, hterm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = j
  · subst hk
    by_cases hki : k < i <;> simp [hki]
  · have hk' : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
    have : ((k : ℕ) < j + 1) ↔ (k : ℕ) < j := by omega
    simp [this, hk]

/-- A sum over the indices $k \ge j$ with $k > i$ splits into the sum over $k \ge j + 1$ with
$k > i$ and the term $k = j$ if $i < j$. -/
private theorem sum_filter_le_val_split (f : Fin n → ℝ) (i j : Fin n) :
    ∑ k ∈ univ.filter (fun k : Fin n => (j : ℕ) ≤ k ∧ i < k), f k =
      ∑ k ∈ univ.filter (fun k : Fin n => (j : ℕ) + 1 ≤ k ∧ i < k), f k +
        if i < j then f j else 0 := by
  have hterm : (if i < j then f j else 0) =
      ∑ k : Fin n, if k = j then (if i < j then f j else 0) else 0 := by simp
  rw [Finset.sum_filter, Finset.sum_filter, hterm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = j
  · subst hk
    by_cases hki : i < k <;> simp [hki]
  · have hk' : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
    have : ((j : ℕ) ≤ k) ↔ (j : ℕ) + 1 ≤ k := by omega
    simp [this, hk]

/-! ### §4.3.1 Band LU factorization -/

/-- **Theorem 4.3.1** of [golub2013matrix], the upper factor. Let
$A, L, U \in \mathbb{R}^{n \times n}$, where $A = LU$ is an LU factorization of $A$. If $A$ has
upper bandwidth $q$, then $U$ has upper bandwidth $q$.

No further hypothesis is needed. The factorization is `Matrix.IsLU A L U`. -/
theorem theorem_4_3_1_a {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U) {q : ℕ}
    (hq : A.HasUpperBandwidth q) : U.HasUpperBandwidth q :=
  h.hasUpperBandwidth hq

/-- **Theorem 4.3.1** of [golub2013matrix], the lower factor. Let
$A, L, U \in \mathbb{R}^{n \times n}$, where $A = LU$ is an LU factorization of $A$, and assume
that $A(1{:}k, 1{:}k)$ is nonsingular for $k = 1{:}n-1$. If $A$ has lower bandwidth $p$, then
$L$ has lower bandwidth $p$.

**Correction.** The source does not assume the nonsingularity of the leading principal
submatrices, but its proof divides by the pivot $\alpha$. The hypothesis is necessary: for every
$\beta$,
$$\begin{bmatrix} 0 & 1 \\ 0 & 2 \end{bmatrix} = \begin{bmatrix} 1 & 0 \\ \beta & 1
  \end{bmatrix} \begin{bmatrix} 0 & 1 \\ 0 & 2 - \beta \end{bmatrix},$$
and the left side is upper triangular, so it has lower bandwidth $0$, while the lower factor has
lower bandwidth $0$ only for $\beta = 0$.

The factorization is `Matrix.IsLU A L U`, and the hypothesis is `∀ k, IsUnit
(A.strictLeadingPrincipalSubmatrix k)`. -/
theorem theorem_4_3_1_b {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) {p : ℕ}
    (hp : A.HasLowerBandwidth p) : L.HasLowerBandwidth p :=
  h.hasLowerBandwidth hA hp

/-- **Theorem 4.3.1** of [golub2013matrix]. Let $A, L, U \in \mathbb{R}^{n \times n}$, where
$A = LU$ is an LU factorization of $A$, and assume that $A(1{:}k, 1{:}k)$ is nonsingular for
$k = 1{:}n-1$. If $A$ has upper bandwidth $q$ and lower bandwidth $p$, then $U$ has upper
bandwidth $q$ and $L$ has lower bandwidth $p$.

**Correction.** The source does not assume the nonsingularity of the leading principal
submatrices. Without it the statement about $L$ fails; see
`GolubVanLoan.Chapter04.theorem_4_3_1_b`. The statement about $U$ holds without it
(`GolubVanLoan.Chapter04.theorem_4_3_1_a`).

**Correction.** The upper-bandwidth conclusion holds for any LU factors. For the lower factor Lean
requires invertible proper leading principal blocks. Existence of some LU factorization alone
permits arbitrary multipliers in a column with zero pivot.
-/
theorem theorem_4_3_1 {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) {p q : ℕ}
    (hp : A.HasLowerBandwidth p) (hq : A.HasUpperBandwidth q) :
    U.HasUpperBandwidth q ∧ L.HasLowerBandwidth p :=
  ⟨theorem_4_3_1_a h hq, theorem_4_3_1_b h hA hp⟩

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.3.1** of [golub2013matrix] (band Gaussian elimination). Given
$A \in \mathbb{R}^{n \times n}$ with upper bandwidth $q$ and lower bandwidth $p$, the algorithm
computes the factorization $A = LU$, assuming it exists. $A(i, j)$ is overwritten by $L(i, j)$
if $i > j$ and by $U(i, j)$ otherwise.
```
for k = 1:n−1
    for i = k+1:min{k+p, n}
        A(i, k) = A(i, k)/A(k, k)
    end
    for j = k+1:min{k+q, n}
        for i = k+1:min{k+p, n}
            A(i, j) = A(i, j) − A(i, k) · A(k, j)
        end
    end
end
```

The program runs the passes for $k = 1, \dots, n$; the last pass does nothing, because its index
lists are empty. Every quotient, product and difference is rounded.

**Reading.** Lean adds a final empty elimination step, uses a rounding argument and totalizes
division at zero pivots. Its exact factorization theorem assumes invertible proper leading blocks.
-/
noncomputable def algorithm_4_3_1 (p q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) => do
    let A ← ((List.finRange n).filter (fun i : Fin n => k < i ∧ (i : ℕ) ≤ k + p)).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
        let l ← rnd (A i k / A k k)
        pure (A.updateRow i (Function.update (A i) k l))) A
    ((List.finRange n).filter (fun j : Fin n => k < j ∧ (j : ℕ) ≤ k + q)).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => k < i ∧ (i : ℕ) ≤ k + p)).foldlM
          (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
            let t ← rnd (A i k * A k j)
            let a ← rnd (A i j - t)
            pure (A.updateRow i (Function.update (A i) j a))) A) A) A

/-- **Algorithm 4.3.2** of [golub2013matrix] (band forward substitution). Let
$L \in \mathbb{R}^{n \times n}$ be a unit lower triangular matrix with lower bandwidth $p$.
Given $b \in \mathbb{R}^n$, the algorithm overwrites $b$ with the solution to $Lx = b$.
```
for j = 1:n
    for i = j+1:min{j+p, n}
        b(i) = b(i) − L(i, j) · b(j)
    end
end
```

This is the column-oriented Algorithm 3.1.3 restricted to the band. It has no division, because
$L$ has a unit diagonal.

**Reading.** The loop is defined for any supplied matrix with the selected band. The source assumes
a unit lower triangular input of that bandwidth, which Lean uses in the exact correctness theorem.
-/
def algorithm_4_3_2 (p : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (b : Fin n → ℝ) (j : Fin n) =>
    ((List.finRange n).filter (fun i : Fin n => j < i ∧ (i : ℕ) ≤ j + p)).foldlM
      (fun (b : Fin n → ℝ) (i : Fin n) => do
        let t ← rnd (L i j * b j)
        let v ← rnd (b i - t)
        pure (Function.update b i v)) b) b

/-- **Algorithm 4.3.3** of [golub2013matrix] (band back substitution). Let
$U \in \mathbb{R}^{n \times n}$ be a nonsingular upper triangular matrix with upper bandwidth
$q$. Given $b \in \mathbb{R}^n$, the algorithm overwrites $b$ with the solution to $Ux = b$.
```
for j = n:−1:1
    b(j) = b(j)/U(j, j)
    for i = max{1, j−q}:j−1
        b(i) = b(i) − U(i, j) · b(j)
    end
end
```

**Reading.** Lean performs the displayed band updates even if the supplied diagonal contains zeros,
using totalized division. Its correctness theorem retains the source's nonzero pivots and upper
bandwidth.
-/
noncomputable def algorithm_4_3_3 (q : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).reverse.foldlM (fun (b : Fin n → ℝ) (j : Fin n) => do
    let v ← rnd (b j / U j j)
    ((List.finRange n).filter (fun i : Fin n => i < j ∧ (j : ℕ) ≤ i + q)).foldlM
      (fun (b : Fin n → ℝ) (i : Fin n) => do
        let t ← rnd (U i j * b j)
        let w ← rnd (b i - t)
        pure (Function.update b i w)) (Function.update b j v)) b

/-- **Algorithm 4.3.5** of [golub2013matrix] (band Cholesky). Given a symmetric positive definite
$A \in \mathbb{R}^{n \times n}$ with bandwidth $p$, the algorithm computes a lower triangular
matrix $G$ with lower bandwidth $p$ such that $A = GG^T$. For all $i \ge j$, $G(i, j)$
overwrites $A(i, j)$.
```
for j = 1:n
    for k = max(1, j−p):j−1
        λ = min(k+p, n)
        A(j:λ, j) = A(j:λ, j) − A(j, k) · A(j:λ, k)
    end
    λ = min(j+p, n)
    A(j:λ, j) = A(j:λ, j)/sqrt(A(j, j))
end
```

The square root is computed once per column and rounded, and the whole column
$A(j{:}\lambda, j)$, diagonal included, is divided by it. This is the operation order of
Algorithm 4.2.1.

**Reading.** The packed program is defined outside the source's SPD and bandwidth hypotheses. It
uses rounded dot-product updates and divides by a totalized square root. The exact factorization
theorem retains the structural hypotheses.
-/
noncomputable def algorithm_4_3_5 (p : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) => do
    let A ← ((List.finRange n).filter (fun k : Fin n => k < j ∧ (j : ℕ) ≤ k + p)).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p)).foldlM
          (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
            let t ← rnd (A j k * A i k)
            let a ← rnd (A i j - t)
            pure (A.updateRow i (Function.update (A i) j a))) A) A
    let s ← rnd (Real.sqrt (A j j))
    ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ j + p)).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
        let g ← rnd (A i j / s)
        pure (A.updateRow i (Function.update (A i) j g))) A) A

end Programs

/-! ### §4.3.2 Band triangular system solving -/

/-- In exact arithmetic, Algorithm 4.3.2 is the fold that subtracts $\ell_{ij} b_j$ from $b_i$ for
$j = 1, \dots, n$ and $j < i \le j + p$. -/
private theorem algorithm_4_3_2_id (p : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_4_3_2 pure p L b) =
      (List.finRange n).foldl (fun (b : Fin n → ℝ) (j : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => j < i ∧ (i : ℕ) ≤ j + p)).foldl
          (fun (b : Fin n → ℝ) (i : Fin n) => Function.update b i (b i - L i j * b j)) b) b := by
  simp only [algorithm_4_3_2, pure_bind, List.foldlM_pure]
  rfl

/-- **Algorithm 4.3.2** of [golub2013matrix], exact correctness. Let $L \in \mathbb{R}^{n \times n}$
be unit lower triangular with lower bandwidth $p$, and let $b \in \mathbb{R}^n$. Then the vector
$x$ computed by Algorithm 4.3.2 in exact arithmetic satisfies $Lx = b$.

The updates that the band loop skips are products with the zero entries $\ell_{ij}$,
$i > j + p$. -/
theorem algorithm_4_3_2_spec {p : ℕ} {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsUnitLowerTriangular) (hp : L.HasLowerBandwidth p) (b : Fin n → ℝ) :
    L *ᵥ Id.run (algorithm_4_3_2 pure p L b) = b := by
  have hp' := hasLowerBandwidth_iff_fin.1 hp
  rw [algorithm_4_3_2_id]
  have key := List.foldl_finRange_induction (f := fun (b : Fin n → ℝ) (j : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => j < i ∧ (i : ℕ) ≤ j + p)).foldl
          (fun (b : Fin n → ℝ) (i : Fin n) => Function.update b i (b i - L i j * b j)) b)
    (init := b)
    (fun c s => ∀ i, s i = b i - ∑ k ∈ univ.filter (fun k : Fin n => (k : ℕ) < c ∧ k < i),
      L i k * s k)
    (fun i => by simp)
    (fun j s hs i => by
      set l := (List.finRange n).filter (fun i : Fin n => j < i ∧ (i : ℕ) ≤ j + p) with hl
      have hmem : ∀ r, r ∈ l ↔ j < r ∧ (r : ℕ) ≤ j + p := fun r => by simp [hl]
      have hjl : j ∉ l := fun h => lt_irrefl _ ((hmem j).1 h).1
      rw [List.foldl_update_of_nodup ((List.nodup_finRange n).filter _)
        (fun i y => y i - L i j * y j) (fun i _ y y' hy hyi => by rw [hyi, hy j hjl]) s]
      simp only
      have hs' : ∀ k : Fin n, (k : ℕ) < j + 1 →
          (if k ∈ l then s k - L k j * s j else s k) = s k := fun k hk => by
        rw [ite_eq_right fun h => absurd ((hmem k).1 h).1 (not_lt.2 (Fin.le_def.2 (by omega)))]
      rw [Finset.sum_congr rfl fun k hk => by rw [hs' k (mem_filter.1 hk).2.1],
        sum_filter_val_lt_succ, hs i]
      by_cases hi : i ∈ l
      · rw [ite_eq_left hi, ite_eq_left ((hmem i).1 hi).1]
        ring
      · rw [ite_eq_right hi]
        by_cases hji : j < i
        · have hL0 : L i j = 0 := hp' i j (by
            by_contra h
            exact hi ((hmem i).2 ⟨hji, by omega⟩))
          rw [ite_eq_left hji, hL0, zero_mul, add_zero]
        · rw [ite_eq_right hji, add_zero])
  ext i
  rw [mulVec_apply_of_isLowerTriangular hL.isLowerTriangular, hL.diag_eq_one, one_mul, key i]
  have : univ.filter (fun k : Fin n => (k : ℕ) < n ∧ k < i) = univ.filter (· < i) := by
    ext k; simp
  rw [this]
  ring

/-- In exact arithmetic, Algorithm 4.3.3 is the fold along the reversed indices that divides $b_j$
by $u_{jj}$ and then subtracts $u_{ij} b_j$ from $b_i$ for $j - q \le i < j$. -/
private theorem algorithm_4_3_3_id (q : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_4_3_3 pure q U b) =
      (List.finRange n).foldl (fun (b : Fin n → ℝ) (c : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => i < c.rev ∧ (c.rev : ℕ) ≤ i + q)).foldl
          (fun (b' : Fin n → ℝ) (i : Fin n) =>
            Function.update b' i (b' i - U i c.rev * b' c.rev))
          (Function.update b c.rev (b c.rev / U c.rev c.rev))) b := by
  simp only [algorithm_4_3_3, pure_bind, List.foldlM_pure, List.finRange_reverse,
    List.foldlM_map]
  rfl

/-- **Algorithm 4.3.3** of [golub2013matrix], exact correctness. Let $U \in \mathbb{R}^{n \times n}$
be upper triangular with nonzero diagonal entries and upper bandwidth $q$, and let
$b \in \mathbb{R}^n$. Then the vector $x$ computed by Algorithm 4.3.3 in exact arithmetic
satisfies $Ux = b$. -/
theorem algorithm_4_3_3_spec {q : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) (hq : U.HasUpperBandwidth q)
    (b : Fin n → ℝ) : U *ᵥ Id.run (algorithm_4_3_3 pure q U b) = b := by
  have hq' := hasUpperBandwidth_iff_fin.1 hq
  rw [algorithm_4_3_3_id]
  have key := List.foldl_finRange_induction (f := fun (b : Fin n → ℝ) (c : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => i < c.rev ∧ (c.rev : ℕ) ≤ i + q)).foldl
          (fun (b' : Fin n → ℝ) (i : Fin n) =>
            Function.update b' i (b' i - U i c.rev * b' c.rev))
          (Function.update b c.rev (b c.rev / U c.rev c.rev))) (init := b)
    (fun c s => ∀ i : Fin n, (if n - c ≤ (i : ℕ) then U i i * s i else s i) =
      b i - ∑ k ∈ univ.filter (fun k : Fin n => n - c ≤ (k : ℕ) ∧ i < k), U i k * s k)
    (fun i => by
      have : univ.filter (fun k : Fin n => n - 0 ≤ (k : ℕ) ∧ i < k) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun k _ h => by have := k.isLt; omega
      rw [ite_eq_right (by omega), this, Finset.sum_empty, sub_zero])
    (fun c s hs i => by
      have hc := c.isLt
      set j := c.rev with hj
      have hjv : (j : ℕ) = n - (c + 1) := by rw [hj, Fin.val_rev]
      set l := (List.finRange n).filter (fun i : Fin n => i < j ∧ (j : ℕ) ≤ i + q) with hl
      have hmem : ∀ r, r ∈ l ↔ r < j ∧ (j : ℕ) ≤ r + q := fun r => by simp [hl]
      have hjl : j ∉ l := fun h => lt_irrefl _ ((hmem j).1 h).1
      set s₁ := Function.update s j (s j / U j j) with hs₁
      rw [List.foldl_update_of_nodup ((List.nodup_finRange n).filter _)
        (fun i y => y i - U i j * y j) (fun i _ y y' hy hyi => by rw [hyi, hy j hjl]) s₁]
      simp only
      -- entries from `j` on are not rewritten by the saxpy
      have hfin : ∀ k : Fin n, (j : ℕ) ≤ k →
          (if k ∈ l then s₁ k - U k j * s₁ j else s₁ k) = s₁ k := fun k hk => by
        rw [ite_eq_right fun h => absurd ((hmem k).1 h).1 (not_lt.2 (Fin.le_def.2 hk))]
      have hsum : ∑ k ∈ univ.filter (fun k : Fin n => n - (c + 1) ≤ (k : ℕ) ∧ i < k),
          U i k * (if k ∈ l then s₁ k - U k j * s₁ j else s₁ k) =
          ∑ k ∈ univ.filter (fun k : Fin n => n - c ≤ (k : ℕ) ∧ i < k), U i k * s k +
            if i < j then U i j * (s j / U j j) else 0 := by
        rw [Finset.sum_congr rfl fun k hk => by
          rw [hfin k (by rw [hjv]; exact (mem_filter.1 hk).2.1)]]
        rw [← hjv, sum_filter_le_val_split]
        congr 1
        · refine Finset.sum_congr (Finset.filter_congr fun k _ => by omega) fun k hk => ?_
          have hkj : k ≠ j := fun h => by
            rw [h] at hk; have := (mem_filter.1 hk).2.1; omega
          rw [hs₁, Function.update_of_ne hkj]
        · rw [hs₁, Function.update_self]
      rw [hsum]
      by_cases hij : i = j
      · -- the entry just finished
        subst hij
        have hle : n - (c + 1) ≤ (j : ℕ) := by omega
        have hlt : ¬ n - c ≤ (j : ℕ) := by omega
        rw [ite_eq_left hle, hfin j le_rfl, hs₁, Function.update_self, mul_div_cancel₀ _ (hd j),
          ite_eq_right (lt_irrefl j), add_zero]
        have := hs j
        rwa [ite_eq_right hlt] at this
      · rcases lt_or_gt_of_ne hij with hij | hij
        · -- an entry above: updated by the saxpy
          have hle : ¬ n - (c + 1) ≤ (i : ℕ) := by
            have := Fin.lt_def.1 hij; omega
          have hlt : ¬ n - c ≤ (i : ℕ) := by omega
          rw [ite_eq_right hle, ite_eq_left hij, hs₁, Function.update_of_ne hij.ne]
          have := hs i
          rw [ite_eq_right hlt] at this
          by_cases hi : i ∈ l
          · rw [ite_eq_left hi, Function.update_self, this]
            ring
          · rw [ite_eq_right hi, this]
            have hU0 : U i j = 0 := hq' i j (by
              by_contra h
              exact hi ((hmem i).2 ⟨hij, by omega⟩))
            rw [hU0, zero_mul, add_zero]
        · -- an entry below: finished before
          have hle : n - (c + 1) ≤ (i : ℕ) := by have := Fin.lt_def.1 hij; omega
          have hlt : n - c ≤ (i : ℕ) := by have := Fin.lt_def.1 hij; omega
          rw [ite_eq_left hle, hfin i (Fin.le_def.1 hij.le), hs₁, Function.update_of_ne hij.ne',
            ite_eq_right (not_lt.2 hij.le), add_zero]
          have := hs i
          rwa [ite_eq_left hlt] at this)
  ext i
  rw [mulVec_apply_of_isUpperTriangular hU]
  have h := key i
  rw [ite_eq_left (by omega)] at h
  have : univ.filter (fun k : Fin n => n - n ≤ (k : ℕ) ∧ i < k) = univ.filter (i < ·) := by
    ext k; simp
  rw [this] at h
  rw [h]
  ring

/-! ### §4.3.6 Tridiagonal system solving -/

/-- **Section 4.3.6** of [golub2013matrix], the $LDL^T$ factorization of a symmetric tridiagonal
matrix. With 0-based indices, let $A \in \mathbb{R}^{m \times m}$ be the symmetric tridiagonal
matrix with diagonal entries $a_{kk} = a_k$ and off-diagonal entries
$a_{k+1,k} = a_{k,k+1} = e_k$. Define
$$d_0 = a_0, \qquad \ell_k = e_k / d_k, \qquad d_{k+1} = a_{k+1} - \ell_k e_k.$$
If $d_k \neq 0$ for $k = 0, \dots, m - 2$, then $A = LDL^T$, where $L$ is unit lower bidiagonal
with subdiagonal entries $L(k+1, k) = \ell_k$, $k = 0, \dots, m - 2$, and
$D = \operatorname{diag}(d_0, \dots, d_{m-1})$.

The matrix $A$ is `Matrix.tridiagonalOfNat a (fun i => e (i - 1)) e m`. The numbers $d_k$ and
$\ell_k$ are the Thomas recurrences `Matrix.thomasAlpha` and `Matrix.thomasBeta` with equal
off-diagonals, and $L$ is `Matrix.thomasLower`. The hypothesis is on the pivots used as
divisors. The source writes the recurrences with 1-based indices, $d_1 = a_{11}$,
$\ell_{k-1} = a_{k,k-1} / d_{k-1}$ and $d_k = a_{kk} - \ell_{k-1} a_{k,k-1}$, and deduces them
from the equation $A = LDL^T$.

**Generalization.** The source works with symmetric positive definite tridiagonal matrices. For the
factorization identity Lean only requires the actual elimination pivots used as divisors to be
nonzero.
-/
theorem tridiagonal_ldlt (a e : ℕ → ℝ) (m : ℕ)
    (hd : ∀ i, i + 1 < m → thomasAlpha a (fun i => e (i - 1)) e i ≠ 0) :
    IsLDM (tridiagonalOfNat a (fun i => e (i - 1)) e m) (thomasLower a (fun i => e (i - 1)) e m)
      (diagonal fun i => thomasAlpha a (fun i => e (i - 1)) e i)
      (thomasLower a (fun i => e (i - 1)) e m) := by
  have h := isLU_tridiagonal_thomas a (fun i => e (i - 1)) e hd
  have hU : diagonal (fun i : Fin m => thomasAlpha a (fun i => e (i - 1)) e i) *
      (thomasLower a (fun i => e (i - 1)) e m)ᵀ = thomasUpper a (fun i => e (i - 1)) e m := by
    ext i j
    rw [diagonal_mul, transpose_apply]
    simp only [thomasLower, thomasUpper, of_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
      by_cases h1 : (i : ℕ) + 1 = j
      · rw [ite_eq_left h1, ite_eq_left h1, ← h1, thomasBeta_succ, Nat.add_sub_cancel,
          mul_div_cancel₀ _ (hd i (by omega))]
      · rw [ite_eq_right h1, ite_eq_right h1, mul_zero]
  exact ⟨h.isUnitLowerTriangular, isDiag_diagonal _, h.isUnitLowerTriangular,
    by rw [Matrix.mul_assoc, hU, h.mul_eq]⟩

/-- Let $A \in \mathbb{R}^{m \times m}$ be a symmetric tridiagonal matrix as in
`GolubVanLoan.Chapter04.tridiagonal_ldlt`. If $A$ is positive definite, then all the pivots
$d_1, \dots, d_m$ are positive.

The leading blocks are positive definite and have the $LDL^T$ factorizations with the leading
pivots. -/
theorem thomasAlpha_pos_of_posDef (a e : ℕ → ℝ) (m : ℕ)
    (hA : (tridiagonalOfNat a (fun i => e (i - 1)) e m).PosDef) :
    ∀ i, i < m → 0 < thomasAlpha a (fun i => e (i - 1)) e i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hsub : tridiagonalOfNat a (fun i => e (i - 1)) e (i + 1) =
      (tridiagonalOfNat a (fun i => e (i - 1)) e m).submatrix (Fin.castLE hi) (Fin.castLE hi) := by
    ext r c
    simp [tridiagonalOfNat]
  have hP : (tridiagonalOfNat a (fun i => e (i - 1)) e (i + 1)).PosDef := by
    rw [hsub]
    exact hA.submatrix (Fin.castLE_injective hi)
  have hL := tridiagonal_ldlt a e (i + 1) fun j hj => (ih j (by omega) (by omega)).ne'
  have hL' : IsLDM (tridiagonalOfNat a (fun i => e (i - 1)) e (i + 1))
      (thomasLower a (fun i => e (i - 1)) e (i + 1))
      (diagonal fun i : Fin (i + 1) => thomasAlpha a (fun i => e (i - 1)) e i)
      (thomasLower a (fun i => e (i - 1)) e (i + 1))ᴴᵀ := by
    rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
  have := hL'.posDef_iff.1 hP (Fin.last i)
  simpa using this

/-- The sequence indexed by `ℕ` of a vector, zero past its end. -/
private def natSeq {N : ℕ} (v : Fin N → ℝ) : ℕ → ℝ := fun i => if h : i < N then v ⟨i, h⟩ else 0

@[simp]
private theorem natSeq_val {N : ℕ} (v : Fin N → ℝ) (i : Fin N) : natSeq v i = v i := by
  simp [natSeq]

/-- The unit lower bidiagonal factor applied to a vector: $(Lx)_0 = x_0$. -/
private theorem thomasLower_mulVec_zero {N : ℕ} (a b c : ℕ → ℝ) (x : Fin (N + 1) → ℝ) :
    (thomasLower a b c (N + 1) *ᵥ x) 0 = x 0 := by
  rw [mulVec, dotProduct, Finset.sum_eq_single 0 (fun r _ hr => ?_) (by simp)]
  · simp [thomasLower]
  · simp [thomasLower, Ne.symm hr]

/-- The unit lower bidiagonal factor applied to a vector: $(Lx)_{k+1} = x_{k+1} + \ell_k x_k$. -/
private theorem thomasLower_mulVec_succ {N : ℕ} (a b c : ℕ → ℝ) (x : Fin (N + 1) → ℝ)
    (k : Fin N) :
    (thomasLower a b c (N + 1) *ᵥ x) k.succ =
      x k.succ + thomasBeta a b c (k + 1) * x k.castSucc := by
  rw [mulVec, dotProduct, Fintype.sum_eq_add k.succ k.castSucc (Fin.castSucc_lt_succ (i := k)).ne'
    (fun r hr => ?_)]
  · simp [thomasLower, (Fin.castSucc_lt_succ (i := k)).ne']
  · have h2 : (r : ℕ) ≠ k := fun h => hr.2 (Fin.ext (by simp [h]))
    simp [thomasLower, Ne.symm hr.1, h2]

/-- The transposed factor applied to a vector: $(L^T x)_N = x_N$. -/
private theorem thomasLower_transpose_mulVec_last {N : ℕ} (a b c : ℕ → ℝ)
    (x : Fin (N + 1) → ℝ) : ((thomasLower a b c (N + 1))ᵀ *ᵥ x) (Fin.last N) = x (Fin.last N) := by
  rw [mulVec, dotProduct, Finset.sum_eq_single (Fin.last N) (fun r _ hr => ?_) (by simp)]
  · simp [thomasLower]
  · have : ¬ ((N : ℕ) + 1 = r) := by omega
    simp [thomasLower, hr, this]

/-- The transposed factor applied to a vector: $(L^T x)_k = x_k + \ell_k x_{k+1}$ for $k < N$. -/
private theorem thomasLower_transpose_mulVec_castSucc {N : ℕ} (a b c : ℕ → ℝ)
    (x : Fin (N + 1) → ℝ) (k : Fin N) :
    ((thomasLower a b c (N + 1))ᵀ *ᵥ x) k.castSucc =
      x k.castSucc + thomasBeta a b c (k + 1) * x k.succ := by
  rw [mulVec, dotProduct, Fintype.sum_eq_add k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)).ne
    (fun r hr => ?_)]
  · simp [thomasLower, (Fin.castSucc_lt_succ (i := k)).ne']
  · have h1 : ¬ (k : ℕ) + 1 = r := fun h => hr.2 (Fin.ext (by simp; omega))
    simp [thomasLower, hr.1, h1]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.3.6** of [golub2013matrix] (symmetric, tridiagonal, positive definite system
solver). Given an $n \times n$ symmetric, tridiagonal, positive definite matrix $A$ and
$b \in \mathbb{R}^n$, the algorithm overwrites $b$ with the solution to $Ax = b$. The diagonal
of $A$ is stored in $\alpha(1{:}n)$ and the superdiagonal in $\beta(1{:}n-1)$.
```
for k = 2:n
    t = β(k−1), β(k−1) = t/α(k−1), α(k) = α(k) − t · β(k−1)
end
for k = 2:n
    b(k) = b(k) − β(k−1) · b(k−1)
end
b(n) = b(n)/α(n)
for k = n−1:−1:1
    b(k) = b(k)/α(k) − β(k) · b(k+1)
end
```

**Typo.** The source prints the second loop as $b(k) = b(k) - \beta(k-1) \cdot \beta(k-1)$. The
forward solve $Ly = b$ is $b(k) = b(k) - \beta(k-1) \cdot b(k-1)$, and the program does this.

With $n = N + 1$, the diagonal is `α : Fin (N + 1) → ℝ` and the superdiagonal is
`β : Fin N → ℝ`. -/
noncomputable def algorithm_4_3_6 {N : ℕ} (α : Fin (N + 1) → ℝ) (β : Fin N → ℝ)
    (b : Fin (N + 1) → ℝ) : M (Fin (N + 1) → ℝ) := do
  let s ← (List.finRange N).foldlM
    (fun (s : (Fin (N + 1) → ℝ) × (Fin N → ℝ)) (k : Fin N) => do
      let l ← rnd (s.2 k / s.1 k.castSucc)
      let t ← rnd (s.2 k * l)
      let d ← rnd (s.1 k.succ - t)
      pure (Function.update s.1 k.succ d, Function.update s.2 k l)) (α, β)
  let y ← (List.finRange N).foldlM (fun (y : Fin (N + 1) → ℝ) (k : Fin N) => do
      let t ← rnd (s.2 k * y k.castSucc)
      let v ← rnd (y k.succ - t)
      pure (Function.update y k.succ v)) b
  let z ← rnd (y (Fin.last N) / s.1 (Fin.last N))
  (List.finRange N).reverse.foldlM (fun (x : Fin (N + 1) → ℝ) (k : Fin N) => do
      let q ← rnd (x k.castSucc / s.1 k.castSucc)
      let t ← rnd (s.2 k * x k.succ)
      let v ← rnd (q - t)
      pure (Function.update x k.castSucc v)) (Function.update y (Fin.last N) z)

end Programs

/-- In exact arithmetic, Algorithm 4.3.6 is three folds: the factorization loop, the forward solve,
and the back solve after the division of the last entry.

**Correction.** The forward-substitution update uses the previous right-hand-side entry times the
current subdiagonal multiplier. The source instead prints that multiplier squared.
-/
private theorem algorithm_4_3_6_id {N : ℕ} (α : Fin (N + 1) → ℝ) (β : Fin N → ℝ)
    (b : Fin (N + 1) → ℝ) :
    Id.run (algorithm_4_3_6 pure α β b) =
      (fun s : (Fin (N + 1) → ℝ) × (Fin N → ℝ) =>
        (fun y : Fin (N + 1) → ℝ =>
          (List.finRange N).foldl (fun (x : Fin (N + 1) → ℝ) (c : Fin N) =>
            Function.update x c.rev.castSucc
              (x c.rev.castSucc / s.1 c.rev.castSucc - s.2 c.rev * x c.rev.succ))
            (Function.update y (Fin.last N) (y (Fin.last N) / s.1 (Fin.last N))))
        ((List.finRange N).foldl (fun (y : Fin (N + 1) → ℝ) (k : Fin N) =>
          Function.update y k.succ (y k.succ - s.2 k * y k.castSucc)) b))
      ((List.finRange N).foldl (fun (s : (Fin (N + 1) → ℝ) × (Fin N → ℝ)) (k : Fin N) =>
        (Function.update s.1 k.succ (s.1 k.succ - s.2 k * (s.2 k / s.1 k.castSucc)),
          Function.update s.2 k (s.2 k / s.1 k.castSucc))) (α, β)) := by
  simp only [algorithm_4_3_6, pure_bind, List.foldlM_pure, List.finRange_reverse,
    List.foldlM_map]
  rfl

/-- **Algorithm 4.3.6** of [golub2013matrix], exact correctness. Let $\alpha \in \mathbb{R}^{N+1}$
and $\beta \in \mathbb{R}^N$, and suppose that the symmetric tridiagonal matrix $A$ with
diagonal $\alpha$ and off-diagonals $\beta$ is positive definite. Then for every
$b \in \mathbb{R}^{N+1}$, the vector $x$ computed by Algorithm 4.3.6 in exact arithmetic
satisfies $Ax = b$.

The matrix $A$ is `Matrix.tridiagonalOf β α β`. The first loop computes the $d_k$ and $\ell_k$
of `GolubVanLoan.Chapter04.tridiagonal_ldlt`, the second solves $Ly = b$, and the last two steps
solve $DL^T x = y$ in the combined form $x_k = y_k / d_k - \ell_k x_{k+1}$. The proof ends with
`GolubVanLoan.Chapter04.ldlt_solve`. -/
theorem algorithm_4_3_6_spec {N : ℕ} (α : Fin (N + 1) → ℝ) (β : Fin N → ℝ)
    (hA : (tridiagonalOf β α β).PosDef) (b : Fin (N + 1) → ℝ) :
    tridiagonalOf β α β *ᵥ Id.run (algorithm_4_3_6 pure α β b) = b := by
  set a := natSeq α with ha
  set e := natSeq β with he
  have hT : tridiagonalOf β α β = tridiagonalOfNat a (fun i => e (i - 1)) e (N + 1) := by
    rw [tridiagonalOfNat_eq_tridiagonalOf]
    congr 1 <;> funext i <;> simp [ha, he]
  set d : Fin (N + 1) → ℝ := fun i => thomasAlpha a (fun i => e (i - 1)) e i with hd
  set ℓ : Fin N → ℝ := fun k => thomasBeta a (fun i => e (i - 1)) e (k + 1) with hℓ
  have hpos : ∀ i, 0 < d i := fun i =>
    thomasAlpha_pos_of_posDef a e (N + 1) (hT ▸ hA) i i.isLt
  have hℓ' : ∀ k : Fin N, ℓ k = β k / d k.castSucc := fun k => by
    simp [hℓ, hd, thomasBeta_succ, he]
  -- the first loop computes the pivots and the multipliers
  have h1 := List.foldl_finRange_induction
    (f := fun (s : (Fin (N + 1) → ℝ) × (Fin N → ℝ)) (k : Fin N) =>
      (Function.update s.1 k.succ (s.1 k.succ - s.2 k * (s.2 k / s.1 k.castSucc)),
        Function.update s.2 k (s.2 k / s.1 k.castSucc))) (init := (α, β))
    (fun c s => (∀ i : Fin (N + 1), s.1 i = if (i : ℕ) ≤ c then d i else α i) ∧
      ∀ k : Fin N, s.2 k = if (k : ℕ) < c then ℓ k else β k)
    ⟨fun i => by
      change α i = if (i : ℕ) ≤ 0 then d i else α i
      rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
      · have : i = 0 := Fin.ext hi
        subst this
        simp [hd, ha, natSeq]
      · rw [ite_eq_right (by omega)],
     fun k => by simp⟩
    (fun k s hs => by
      obtain ⟨hs1, hs2⟩ := hs
      have hk2 : s.2 k = β k := by rw [hs2, ite_eq_right (lt_irrefl _)]
      have hk1 : s.1 k.castSucc = d k.castSucc := by rw [hs1, ite_eq_left (by simp)]
      have hk1' : s.1 k.succ = α k.succ := by rw [hs1, ite_eq_right (by simp)]
      refine ⟨fun i => ?_, fun k' => ?_⟩
      · dsimp only
        by_cases hik : i = k.succ
        · subst hik
          rw [Function.update_self, ite_eq_left (by simp), hk1', hk2, hk1]
          have ha1 : a ((k : ℕ) + 1) = α k.succ := by
            simp only [ha, natSeq, dite_eq_left (Nat.succ_lt_succ k.isLt)]
            rfl
          have he1 : e (k : ℕ) = β k := by rw [he, natSeq_val]
          simp only [hd, Fin.val_succ, Fin.val_castSucc, thomasAlpha_succ, thomasBeta_succ,
            Nat.add_sub_cancel, ha1, he1]
          ring
        · rw [Function.update_of_ne hik, hs1]
          have : (i : ℕ) ≠ k + 1 := fun h => hik (Fin.ext (by simp [h]))
          by_cases hi : (i : ℕ) ≤ k
          · rw [ite_eq_left hi, ite_eq_left (by omega)]
          · rw [ite_eq_right hi, ite_eq_right (by omega)]
      · dsimp only
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self, ite_eq_left (by omega), hk2, hk1, hℓ']
        · rw [Function.update_of_ne hk, hs2]
          have : (k' : ℕ) ≠ k := fun h => hk (Fin.ext h)
          by_cases hk' : (k' : ℕ) < k
          · rw [ite_eq_left hk', ite_eq_left (by omega)]
          · rw [ite_eq_right hk', ite_eq_right (by omega)])
  have hs : (List.finRange N).foldl (fun (s : (Fin (N + 1) → ℝ) × (Fin N → ℝ)) (k : Fin N) =>
      (Function.update s.1 k.succ (s.1 k.succ - s.2 k * (s.2 k / s.1 k.castSucc)),
        Function.update s.2 k (s.2 k / s.1 k.castSucc))) (α, β) = (d, ℓ) := by
    refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
    · rw [h1.1 i, ite_eq_left (by omega)]
    · rw [h1.2 k, ite_eq_left k.isLt]
  rw [algorithm_4_3_6_id, hs]
  dsimp only
  -- the second loop solves `L y = b`
  set y := (List.finRange N).foldl (fun (y : Fin (N + 1) → ℝ) (k : Fin N) =>
    Function.update y k.succ (y k.succ - ℓ k * y k.castSucc)) b with hy
  have h2 := List.foldl_finRange_induction (f := fun (y : Fin (N + 1) → ℝ) (k : Fin N) =>
      Function.update y k.succ (y k.succ - ℓ k * y k.castSucc)) (init := b)
    (fun c y => y 0 = b 0 ∧ (∀ k : Fin N, (k : ℕ) < c → y k.succ + ℓ k * y k.castSucc = b k.succ) ∧
      ∀ k : Fin N, c ≤ (k : ℕ) → y k.succ = b k.succ)
    ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl⟩
    (fun k y hy => by
      obtain ⟨hy0, hy1, hy2⟩ := hy
      refine ⟨by rw [Function.update_of_ne (Fin.succ_ne_zero k).symm]; exact hy0,
        fun k' hk' => ?_, fun k' hk' => ?_⟩
      · by_cases hkk : k' = k
        · subst hkk
          rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_succ (i := k')).ne,
            hy2 k' le_rfl]
          ring
        · have hlt : (k' : ℕ) < k := by
            have : (k' : ℕ) ≠ k := fun h => hkk (Fin.ext h); omega
          rw [Function.update_of_ne (fun h => hkk (Fin.succ_injective _ h)),
            Function.update_of_ne (fun h => by
              have := congrArg Fin.val h; simp at this; omega)]
          exact hy1 k' hlt
      · have hkk : k' ≠ k := fun h => by rw [h] at hk'; omega
        rw [Function.update_of_ne (fun h => hkk (Fin.succ_injective _ h))]
        exact hy2 k' (by omega))
  have hLy : thomasLower a (fun i => e (i - 1)) e (N + 1) *ᵥ y = b := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [thomasLower_mulVec_zero]; exact h2.1
    · rw [thomasLower_mulVec_succ]; exact h2.2.1 k k.isLt
  -- the last two loops solve `D Lᵀ x = y`
  have h3 := List.foldl_finRange_induction (f := fun (x : Fin (N + 1) → ℝ) (c : Fin N) =>
      Function.update x c.rev.castSucc
        (x c.rev.castSucc / d c.rev.castSucc - ℓ c.rev * x c.rev.succ))
    (init := Function.update y (Fin.last N) (y (Fin.last N) / d (Fin.last N)))
    (fun c x => x (Fin.last N) = y (Fin.last N) / d (Fin.last N) ∧
      (∀ k : Fin N, N - c ≤ (k : ℕ) →
        x k.castSucc = y k.castSucc / d k.castSucc - ℓ k * x k.succ) ∧
      ∀ k : Fin N, (k : ℕ) < N - c → x k.castSucc = y k.castSucc)
    ⟨by rw [Function.update_self], fun k hk => absurd k.isLt (by omega),
      fun k _ => by rw [Function.update_of_ne (Fin.castSucc_lt_last k).ne]⟩
    (fun c x hx => by
      obtain ⟨hx0, hx1, hx2⟩ := hx
      have hcv : (c.rev : ℕ) = N - 1 - c := by rw [Fin.val_rev]; omega
      refine ⟨by rw [Function.update_of_ne (Fin.castSucc_lt_last _).ne']; exact hx0,
        fun k hk => ?_, fun k hk => ?_⟩
      · by_cases hkk : k = c.rev
        · subst hkk
          rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_succ).ne',
            hx2 _ (by omega)]
        · have hk' : N - c ≤ (k : ℕ) := by
            have : (k : ℕ) ≠ c.rev := fun h => hkk (Fin.ext h); omega
          rw [Function.update_of_ne (fun h => hkk (Fin.castSucc_injective _ h)),
            Function.update_of_ne (fun h => by
              have := congrArg Fin.val h; simp at this; omega)]
          exact hx1 k hk'
      · have hkk : k ≠ c.rev := fun h => by rw [h] at hk; omega
        rw [Function.update_of_ne (fun h => hkk (Fin.castSucc_injective _ h))]
        exact hx2 k (by omega))
  set x := (List.finRange N).foldl (fun (x : Fin (N + 1) → ℝ) (c : Fin N) =>
      Function.update x c.rev.castSucc
        (x c.rev.castSucc / d c.rev.castSucc - ℓ c.rev * x c.rev.succ))
    (Function.update y (Fin.last N) (y (Fin.last N) / d (Fin.last N))) with hx
  have hLx : (thomasLower a (fun i => e (i - 1)) e (N + 1))ᵀ *ᵥ x = fun i => y i / d i := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [thomasLower_transpose_mulVec_last]; exact h3.1
    · rw [thomasLower_transpose_mulVec_castSucc, h3.2.1 k (by omega)]
      simp only [hℓ]
      ring
  have hDy : diagonal d *ᵥ (fun i => y i / d i) = y := by
    funext i
    rw [mulVec_diagonal, mul_div_cancel₀ _ (hpos i).ne']
  rw [hT]
  exact ldlt_solve (tridiagonal_ldlt a e (N + 1) fun i hi => (hpos ⟨i, by omega⟩).ne') hLy hDy hLx

/-! ### §4.3.3 Band Gaussian elimination with pivoting -/

/-- **Theorem 4.3.2** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ have lower bandwidth
$p$ and upper bandwidth $q$. Suppose that Gaussian elimination with partial pivoting computes
Gauss transformations $M_j = I - \alpha^{(j)} e_j^T$ and permutations $P_1, \dots, P_{n-1}$ such
that $M_{n-1} P_{n-1} \cdots M_1 P_1 A = U$ is upper triangular. Then $U$ has upper bandwidth
$p + q$, and $\alpha^{(j)}_i = 0$ whenever $i \le j$ or $i > j + p$.

**Generalization.** The source assumes that $A$ is nonsingular. The theorem does not need this
hypothesis.

Gaussian elimination with partial pivoting is `Matrix.gemPivotStage A Matrix.partialPivotRow`,
and $U$ is its stage $n$. The Gauss vector of stage $k$ is column $k$ of
`Matrix.elimMultipliers` of the stage-$k$ matrix after the interchange of stage $k$
(`Matrix.gemPivotSwap`). The indices are 0-based, so the condition reads $i \le k$ or
$i > k + p$ for stage $k$. -/
theorem theorem_4_3_2 {A : Matrix (Fin n) (Fin n) ℝ} {p q : ℕ} (hp : A.HasLowerBandwidth p)
    (hq : A.HasUpperBandwidth q) :
    (gemPivotStage A partialPivotRow n).1.HasUpperBandwidth (p + q) ∧
      ∀ (k : ℕ) (hk : k < n) (i : Fin n), (i : ℕ) ≤ k ∨ k + p < i → ∀ j,
        elimMultipliers ((gemPivotStage A partialPivotRow k).1.submatrix
          (gemPivotSwap A partialPivotRow k hk) id) ⟨k, hk⟩ i j = 0 :=
  ⟨gemPivotStage_partialPivotRow_hasUpperBandwidth hp hq,
    fun _ hk _ hi j => gemPivotStage_partialPivotRow_multiplier_eq_zero hp hq hk hi j⟩

/-! ### §4.3.4 Hessenberg LU -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One pass $k$ of Algorithm 4.3.4 of [golub2013matrix] on the state $(H, \mathrm{piv})$. For
$k + 1 < n$, the pass is
```
if |H(k, k)| < |H(k+1, k)|
    piv(k) = 1; H(k, k:n) ↔ H(k+1, k:n)
else
    piv(k) = 0
end
if H(k, k) ≠ 0
    τ = H(k+1, k)/H(k, k)
    H(k+1, k+1:n) = H(k+1, k+1:n) − τ · H(k, k+1:n)
    H(k+1, k) = τ
end
```

The interchange of the two row segments and the comparisons are exact. The last pass, $k = n$,
does nothing.

**Reading.** The full-length encoding includes a final zero pivot flag with no elimination. The
source records the first $n-1$ flags. The exact correctness result supplies the Hessenberg
hypothesis separately.
-/
noncomputable def hessenbergLUStep (s : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ)) (k : Fin n) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ)) :=
  if h : (k : ℕ) + 1 < n then
    let k₁ : Fin n := ⟨k + 1, h⟩
    let s : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ) :=
      if |s.1 k k| < |s.1 k₁ k| then
        (Matrix.of fun i j => if k ≤ j ∧ i = k then s.1 k₁ j
          else if k ≤ j ∧ i = k₁ then s.1 k j else s.1 i j, Function.update s.2 k 1)
      else (s.1, Function.update s.2 k 0)
    if s.1 k k ≠ 0 then do
      let τ ← rnd (s.1 k₁ k / s.1 k k)
      let r ← ((List.finRange n).filter (k < ·)).foldlM
        (fun (r : Fin n → ℝ) (j : Fin n) => do
          let t ← rnd (τ * s.1 k j)
          let v ← rnd (r j - t)
          pure (Function.update r j v)) (s.1 k₁)
      pure (s.1.updateRow k₁ (Function.update r k τ), s.2)
    else pure s
  else pure s

/-- **Algorithm 4.3.4** of [golub2013matrix] (Hessenberg LU). Given an upper Hessenberg matrix
$H \in \mathbb{R}^{n \times n}$, the algorithm computes the upper triangular matrix
$M_{n-1} P_{n-1} \cdots M_1 P_1 H = U$, where each $P_k$ is a permutation and each $M_k$ is a
Gauss transformation whose entries are bounded by unity. $H(i, k)$ is overwritten with $U(i, k)$
if $i \le k$ and by $-[M_k]_{k+1,k}$ if $i = k + 1$. An integer vector $\mathrm{piv}(1{:}n-1)$
encodes the permutations: if $P_k = I$, then $\mathrm{piv}(k) = 0$, and if $P_k$ interchanges
rows $k$ and $k + 1$, then $\mathrm{piv}(k) = 1$.

The program runs the passes `GolubVanLoan.Chapter04.hessenbergLUStep` for $k = 1, \dots, n$ on
the state $(H, \mathrm{piv})$, with $\mathrm{piv} = 0$ at the start. The last pass does nothing.

**Reading.** The full-length encoding includes a final zero pivot flag with no elimination. The
source records the first $n-1$ flags. The exact correctness result supplies the Hessenberg
hypothesis separately.
-/
noncomputable def algorithm_4_3_4 (H : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ)) :=
  (List.finRange n).foldlM (hessenbergLUStep rnd) (H, 0)

end Programs

/-- The loop invariant of Algorithm 4.3.4 after $c$ passes. On and above the diagonal, and in the
columns from $c$ on, the state is the matrix of stage $c$ of Gaussian elimination with partial
pivoting. The stored multipliers of the passes before $c$ are bounded by one, the recorded
interchanges are those of partial pivoting, and the stored multipliers are those of partial
pivoting. -/
private def HessInv (H : Matrix (Fin n) (Fin n) ℝ) (c : ℕ)
    (s : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ)) : Prop :=
  (∀ i j : Fin n, (c ≤ (j : ℕ) ∨ i ≤ j) → s.1 i j = (gemPivotStage H partialPivotRow c).1 i j) ∧
  (∀ (k : Fin n) (hk : (k : ℕ) + 1 < n), (k : ℕ) < c → |s.1 ⟨k + 1, hk⟩ k| ≤ 1) ∧
  (∀ (k : Fin n) (hk : (k : ℕ) + 1 < n), (k : ℕ) < c →
    (s.2 k = 1 ↔ partialPivotRow (gemPivotStage H partialPivotRow k).1 k = ⟨k + 1, hk⟩)) ∧
  (∀ (k : Fin n) (hk : (k : ℕ) + 1 < n), (k : ℕ) < c →
    s.1 ⟨k + 1, hk⟩ k = elimMultipliers ((gemPivotStage H partialPivotRow k).1.submatrix
      (gemPivotSwap H partialPivotRow k k.isLt) id) k ⟨k + 1, hk⟩ k)

/-- Stage $k + 1$ of Gaussian elimination with partial pivoting, for a pivot index $k$ in `Fin n`,
is the elimination step at $k$ applied to stage $k$ after its interchange. -/
private theorem gemPivotStage_succ_fin (H : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    (gemPivotStage H partialPivotRow ((k : ℕ) + 1)).1 =
      elimStep ((gemPivotStage H partialPivotRow k).1.submatrix
        (Equiv.swap k (partialPivotRow (gemPivotStage H partialPivotRow k).1 k)) id) k := by
  rw [gemPivotStage_succ_of_lt H partialPivotRow k.isLt]
  rfl

/-- One pass of Algorithm 4.3.4 keeps the loop invariant. -/
private theorem hessInv_step {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsUpperHessenberg)
    (k : Fin n) (s : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ)) (hs : HessInv H k s) :
    HessInv H (k + 1) (Id.run (hessenbergLUStep pure s k)) := by
  obtain ⟨S, piv⟩ := s
  obtain ⟨hS, hmul, hpiv, hτs⟩ := hs
  simp only at hS hmul hpiv hτs
  set G := (gemPivotStage H partialPivotRow k).1 with hG
  have hG' := gemPivotStage_succ_fin H k
  rw [← hG] at hG'
  set r := partialPivotRow G k with hr
  have hkr : k ≤ r := le_partialPivotRow G k
  -- below the subdiagonal the pivot column of stage `k` is still that of `H`
  have hcol : ∀ i : Fin n, (k : ℕ) + 1 < i → G i k = 0 := fun i hi => by
    rw [hG, (gemPivotStage_partialPivotRow_isUpperHessenberg_invariant hH k).1 i k (by omega)]
    exact hH i k ⟨⟨k + 1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simp; omega)⟩
  have hrle : (r : ℕ) ≤ k + 1 := partialPivotRow_le_succ G k hcol
  unfold hessenbergLUStep
  by_cases hk : (k : ℕ) + 1 < n
  swap
  · -- the last pass does nothing, and neither does the last stage
    rw [dite_eq_right hk]
    have hrk : r = k := le_antisymm (Fin.le_def.2 (by have := r.isLt; omega)) hkr
    have hGk : (gemPivotStage H partialPivotRow ((k : ℕ) + 1)).1 = G := by
      ext i j
      rw [hG', hrk, Equiv.swap_self, Equiv.coe_refl, submatrix_id_id,
        elimStep_apply_of_not_lt _ fun h => by have := Fin.lt_def.1 h; omega]
    refine ⟨fun i j hij => ?_, fun k' hk' hlt => ?_, fun k' hk' hlt => ?_,
      fun k' hk' hlt => ?_⟩
    · rw [hGk]
      exact hS i j (hij.imp (fun h => by have := j.isLt; omega) id)
    · exact hmul k' hk' (by omega)
    · exact hpiv k' hk' (by omega)
    · exact hτs k' hk' (by omega)
  rw [dite_eq_left hk]
  set k₁ : Fin n := ⟨k + 1, hk⟩ with hk₁
  have hkk₁ : k < k₁ := Fin.lt_def.2 (by simp [hk₁])
  have hSk : S k k = G k k := hS k k (Or.inr le_rfl)
  have hSk₁ : S k₁ k = G k₁ k := hS k₁ k (Or.inl le_rfl)
  -- the pivot row of partial pivoting is `k₁` exactly when the book interchanges
  have hswap_iff : r = k₁ ↔ |G k k| < |G k₁ k| := by
    constructor
    · intro hrk₁
      by_contra hle
      have hmax : ∀ r', k ≤ r' → ‖G r' k‖ ≤ ‖G k k‖ := fun r' hr' => by
        rcases eq_or_lt_of_le hr' with rfl | hr'
        · exact le_rfl
        · rcases eq_or_lt_of_le (Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 hr')) :
            k₁ ≤ r') with rfl | hr''
          · simpa [Real.norm_eq_abs] using not_lt.1 hle
          · rw [hcol r' (Fin.lt_def.1 hr''), norm_zero]
            exact norm_nonneg _
      have := partialPivotRow_le G k le_rfl hmax
      rw [← hr, hrk₁] at this
      exact absurd this (not_le.2 hkk₁)
    · intro hlt
      refine Fin.ext (le_antisymm hrle (Nat.succ_le_of_lt (lt_of_le_of_ne (Fin.le_def.1 hkr)
        fun h => ?_)))
      have hrk : r = k := Fin.ext h.symm
      have := norm_apply_le_partialPivotRow G k hkk₁.le
      rw [← hr, hrk, Real.norm_eq_abs, Real.norm_eq_abs] at this
      exact absurd hlt (not_lt.2 this)
  -- the interchanged matrix of stage `k`
  set Mx := G.submatrix (Equiv.swap k r) id with hMx
  have hMk : |Mx k₁ k| ≤ |Mx k k| := by
    have h1 := norm_apply_le_partialPivotRow G k hkk₁.le
    have h2 := norm_apply_le_partialPivotRow G k (le_refl k)
    rw [← hr, Real.norm_eq_abs, Real.norm_eq_abs] at h1 h2
    simp only [hMx, submatrix_apply, id, Equiv.swap_apply_left]
    rcases (show r = k ∨ r = k₁ from by
      rcases eq_or_lt_of_le hkr with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Fin.ext (le_antisymm hrle (Nat.succ_le_of_lt (Fin.lt_def.1 h)))))
      with h | h
    · rw [h, Equiv.swap_self, Equiv.refl_apply]
      rw [h] at h1
      exact h1
    · rw [h, Equiv.swap_apply_right]
      rw [h] at h2
      exact h2
  -- the row interchange of the program realizes `Mx` on the relevant entries
  set s₁ : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ) :=
    if |S k k| < |S k₁ k| then
      (Matrix.of fun i j => if k ≤ j ∧ i = k then S k₁ j
        else if k ≤ j ∧ i = k₁ then S k j else S i j, Function.update piv k 1)
    else (S, Function.update piv k 0) with hs₁
  have hS₁ : ∀ i j : Fin n, ((k : ℕ) ≤ j ∨ i ≤ j) → s₁.1 i j = Mx i j := by
    intro i j hij
    by_cases hsw : |S k k| < |S k₁ k|
    · have hrk₁ : r = k₁ := hswap_iff.2 (by rwa [← hSk, ← hSk₁])
      simp only [hs₁, ite_eq_left hsw, of_apply, hMx, submatrix_apply, id, hrk₁]
      by_cases hik : i = k
      · subst i
        have hkj : k ≤ j := hij.elim Fin.le_def.2 id
        rw [ite_eq_left ⟨hkj, rfl⟩, Equiv.swap_apply_left]
        exact hS _ _ (Or.inl (Fin.le_def.1 hkj))
      · by_cases hik₁ : i = k₁
        · subst hik₁
          have hkj : k ≤ j := hij.elim Fin.le_def.2 fun h => hkk₁.le.trans h
          rw [ite_eq_right fun h => hik h.2, ite_eq_left ⟨hkj, rfl⟩, Equiv.swap_apply_right]
          exact hS _ _ (Or.inl (Fin.le_def.1 hkj))
        · rw [ite_eq_right fun h => hik h.2, ite_eq_right fun h => hik₁ h.2,
            Equiv.swap_apply_of_ne_of_ne hik hik₁]
          exact hS i j (hij.imp id id)
    · have hrk : r = k := by
        by_contra h
        exact hsw (by rw [hSk, hSk₁]; exact hswap_iff.1 (by
          rcases eq_or_lt_of_le hkr with h' | h'
          · exact absurd h'.symm h
          · exact Fin.ext (le_antisymm hrle (Nat.succ_le_of_lt (Fin.lt_def.1 h')))))
      simp only [hs₁, ite_eq_right hsw, hMx, submatrix_apply, id, hrk, Equiv.swap_self,
        Equiv.refl_apply]
      exact hS i j hij
  have hpiv₁ : s₁.2 = Function.update piv k (if r = k₁ then 1 else 0) := by
    by_cases hsw : |S k k| < |S k₁ k|
    · rw [hs₁, ite_eq_left hsw, ite_eq_left (hswap_iff.2 (by rwa [← hSk, ← hSk₁]))]
    · rw [hs₁, ite_eq_right hsw, ite_eq_right fun h => hsw (by rw [hSk, hSk₁]; exact hswap_iff.1 h)]
  have hlow₁ : ∀ i j : Fin n, j < k → s₁.1 i j = S i j := fun i j hj => by
    by_cases hsw : |S k k| < |S k₁ k|
    · simp only [hs₁, ite_eq_left hsw, of_apply]
      rw [ite_eq_right fun h => absurd h.1 (not_le.2 hj),
        ite_eq_right fun h => absurd h.1 (not_le.2 hj)]
    · simp only [hs₁, ite_eq_right hsw]
  -- the new stage
  have hG'apply : ∀ i j : Fin n,
      (gemPivotStage H partialPivotRow ((k : ℕ) + 1)).1 i j =
        Mx i j - if k < i then Mx i k * (Mx k k)⁻¹ * Mx k j else 0 := fun i j => by
    rw [hG', elimStep_apply]
  have hMcol : ∀ i : Fin n, k < i → i ≠ k₁ → Mx i k = 0 := fun i hki hik₁ => by
    have hi : (k : ℕ) + 1 < i := by
      have h1 := Fin.lt_def.1 hki
      have h2 : (i : ℕ) ≠ k + 1 := fun h => hik₁ (Fin.ext (by simp [hk₁, h]))
      omega
    simp only [hMx, submatrix_apply, id]
    rw [Equiv.swap_apply_of_ne_of_ne (ne_of_gt hki) (fun h => by
      have := Fin.le_def.1 (h ▸ le_refl i); rw [h] at hi; omega), hcol i hi]
  have hmulk : ∀ (k' : Fin n) (hk' : (k' : ℕ) + 1 < n), (k' : ℕ) < k →
      (⟨(k' : ℕ) + 1, hk'⟩ : Fin n) ≠ k₁ := fun k' hk' hlt h => by
    have := congrArg Fin.val h
    simp [hk₁] at this
    omega
  dsimp only
  rw [← hs₁]
  by_cases hp : s₁.1 k k ≠ 0
  · rw [ite_eq_left hp]
    simp only [pure_bind, List.foldlM_pure, Id.run_pure]
    rw [List.foldl_update_of_nodup ((List.nodup_finRange n).filter _)
      (fun j y => y j - s₁.1 k₁ k / s₁.1 k k * s₁.1 k j) (fun j _ y y' _ hyj => by rw [hyj])]
    set τ := s₁.1 k₁ k / s₁.1 k k with hτ
    have hmem : ∀ j, j ∈ (List.finRange n).filter (k < ·) ↔ k < j := fun j => by simp
    refine ⟨fun i j hij => ?_, fun k' hk' hlt => ?_, fun k' hk' hlt => ?_,
      fun k' hk' hlt => ?_⟩
    · rw [hG'apply]
      by_cases hik₁ : i = k₁
      · subst hik₁
        have hkj : k < j := by
          rcases hij with h | h
          · exact Fin.lt_def.2 (by omega)
          · exact lt_of_lt_of_le hkk₁ h
        simp only [updateRow_self]
        rw [Function.update_of_ne (ne_of_gt hkj), ite_eq_left ((hmem j).2 hkj), ite_eq_left hkk₁,
          hτ, hS₁ _ _ (Or.inl (Fin.le_def.1 hkj.le)), hS₁ _ _ (Or.inl (Fin.le_def.1 hkj.le)),
          hS₁ _ _ (Or.inl le_rfl), hS₁ _ _ (Or.inl le_rfl)]
        ring
      · simp only [updateRow_ne hik₁]
        rw [hS₁ i j (hij.imp (fun h => by omega) id)]
        by_cases hki : k < i
        · rw [ite_eq_left hki, hMcol i hki hik₁]
          ring
        · rw [ite_eq_right hki, sub_zero]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · simp only [updateRow_ne (hmulk k' hk' hlt)]
        rw [hlow₁ _ _ (Fin.lt_def.2 hlt)]
        exact hmul k' hk' hlt
      · have hk'k : k' = k := Fin.ext heq
        subst k'
        rw [show (⟨(k : ℕ) + 1, hk'⟩ : Fin n) = k₁ from rfl]
        dsimp only
        rw [updateRow_self, Function.update_self, hτ, abs_div, hS₁ k₁ k (Or.inl le_rfl),
          hS₁ k k (Or.inl le_rfl)]
        exact div_le_one_of_le₀ hMk (abs_nonneg _)
    · rw [hpiv₁]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · rw [Function.update_of_ne (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)]
        exact hpiv k' hk' hlt
      · have hk'k : k' = k := Fin.ext heq
        subst k'
        rw [Function.update_self, ← hr]
        by_cases h : r = k₁ <;> simp [h, hk₁]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · simp only [updateRow_ne (hmulk k' hk' hlt)]
        rw [hlow₁ _ _ (Fin.lt_def.2 hlt)]
        exact hτs k' hk' hlt
      · have hk'k : k' = k := Fin.ext heq
        subst k'
        rw [show (⟨(k : ℕ) + 1, hk'⟩ : Fin n) = k₁ from rfl]
        dsimp only
        rw [updateRow_self, Function.update_self, hτ, hS₁ k₁ k (Or.inl le_rfl),
          hS₁ k k (Or.inl le_rfl), elimMultipliers_apply, ite_eq_left ⟨hkk₁, rfl⟩, div_eq_mul_inv]
        rfl
  · rw [ite_eq_right hp]
    simp only [Id.run_pure]
    push Not at hp
    have hMkk : Mx k k = 0 := by rw [← hS₁ _ _ (Or.inl le_rfl), hp]
    refine ⟨fun i j hij => ?_, fun k' hk' hlt => ?_, fun k' hk' hlt => ?_,
      fun k' hk' hlt => ?_⟩
    · rw [hG'apply, hMkk, _root_.inv_zero, hS₁ i j (hij.imp (fun h => by omega) id)]
      simp
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · rw [hlow₁ _ _ (Fin.lt_def.2 hlt)]
        exact hmul k' hk' hlt
      · have hk'k : k' = k := Fin.ext heq
        subst k'
        rw [hS₁ _ _ (Or.inl le_rfl)]
        rw [hMkk, abs_zero] at hMk
        linarith
    · rw [hpiv₁]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · rw [Function.update_of_ne (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)]
        exact hpiv k' hk' hlt
      · have hk'k : k' = k := Fin.ext heq
        subst k'
        rw [Function.update_self, ← hr]
        by_cases h : r = k₁ <;> simp [h, hk₁]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · rw [hlow₁ _ _ (Fin.lt_def.2 hlt)]
        exact hτs k' hk' hlt
      · have hk'k : k' = k := Fin.ext heq
        subst k'
        rw [show (⟨(k : ℕ) + 1, hk'⟩ : Fin n) = k₁ from rfl, hS₁ _ _ (Or.inl le_rfl)]
        rw [hMkk, abs_zero] at hMk
        rw [abs_nonpos_iff.1 hMk, elimMultipliers_apply, ite_eq_left ⟨hkk₁, rfl⟩]
        change (0 : ℝ) = Mx k₁ k * (Mx k k)⁻¹
        rw [hMkk, _root_.inv_zero, mul_zero]

/-- The loop invariant of Algorithm 4.3.4 holds after its $n$ passes. -/
private theorem hessInv_run {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsUpperHessenberg) :
    HessInv H n (Id.run (algorithm_4_3_4 pure H)) := by
  have key := List.foldl_finRange_induction (f := fun s k => Id.run (hessenbergLUStep pure s k))
    (init := (H, 0))
    (HessInv H) ⟨fun _ _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun k s hs => hessInv_step hH k s hs)
  rw [algorithm_4_3_4, List.idRun_foldlM]
  exact key

/-- **Algorithm 4.3.4** of [golub2013matrix], exact correctness. Let $H \in \mathbb{R}^{n \times n}$
be upper Hessenberg, and let $(F, \mathrm{piv})$ be the output of Algorithm 4.3.4 in exact
arithmetic. Then:
* on and above the diagonal, $F$ agrees with the upper factor $U$ of Gaussian elimination with
  partial pivoting;
* for $k + 1 < n$, $\mathrm{piv}(k) = 1$ if and only if partial pivoting interchanges rows $k$
  and $k + 1$ at stage $k$;
* for $k + 1 < n$, the entry $F(k+1, k)$ is the multiplier $\tau = -[M_k]_{k+1,k}$ of stage $k$.

Gaussian elimination with partial pivoting is `Matrix.gemPivotStage H Matrix.partialPivotRow`.
The multiplier is the entry $(k+1, k)$ of `Matrix.elimMultipliers` of the stage-$k$ matrix after
its interchange, and it is $0$ when the pivot vanishes. The indices are 0-based. The bound
$|F(k+1, k)| \le 1$ is `GolubVanLoan.Chapter04.algorithm_4_3_4_spec_abs_le_one`.

**Reading.** The correctness statement identifies the packed upper entries, pivot flags and stored
multipliers with exact partial pivoting. It leaves the final unused flag outside the comparison,
matching the shorter pivot list in the source.
-/
theorem algorithm_4_3_4_spec {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsUpperHessenberg) :
    (∀ i j : Fin n, i ≤ j →
      (Id.run (algorithm_4_3_4 pure H)).1 i j = (gemPivotStage H partialPivotRow n).1 i j) ∧
    (∀ (k : Fin n) (hk : (k : ℕ) + 1 < n),
      ((Id.run (algorithm_4_3_4 pure H)).2 k = 1 ↔
        partialPivotRow (gemPivotStage H partialPivotRow k).1 k = ⟨k + 1, hk⟩)) ∧
    ∀ (k : Fin n) (hk : (k : ℕ) + 1 < n),
      (Id.run (algorithm_4_3_4 pure H)).1 ⟨k + 1, hk⟩ k =
        elimMultipliers ((gemPivotStage H partialPivotRow k).1.submatrix
          (gemPivotSwap H partialPivotRow k k.isLt) id) k ⟨k + 1, hk⟩ k := by
  obtain ⟨h1, -, h3, h4⟩ := hessInv_run hH
  exact ⟨fun i j hij => h1 i j (Or.inr hij), fun k hk => h3 k hk k.isLt,
    fun k hk => h4 k hk k.isLt⟩

/-- **Algorithm 4.3.4** of [golub2013matrix], the bound on the multipliers. Let
$H \in \mathbb{R}^{n \times n}$ be upper Hessenberg, and let $(F, \mathrm{piv})$ be the output
of Algorithm 4.3.4 in exact arithmetic. Then $|F(k+1, k)| \le 1$ for every $k$ with $k + 1 < n$.

This is the claim of the source that each $M_k$ is a Gauss transformation whose entries are
bounded by unity. -/
theorem algorithm_4_3_4_spec_abs_le_one {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsUpperHessenberg) (k : Fin n) (hk : (k : ℕ) + 1 < n) :
    |(Id.run (algorithm_4_3_4 pure H)).1 ⟨k + 1, hk⟩ k| ≤ 1 := by
  exact (hessInv_run hH).2.1 k hk k.isLt

/-! ### §4.3.5 Band Cholesky -/

/-- A loop that writes column $j$ of a matrix, one row per step, in exact arithmetic. Let $l$ be a
duplicate-free list of rows, and suppose that step $i$ replaces the entry $(i, j)$ by a value
$h_i(A)$ that depends only on the entry $(i, j)$ and on the entries outside the written ones.
Then the loop replaces every entry $(i, j)$, $i \in l$, by $h_i$ of the initial matrix, and
keeps the other entries. -/
theorem foldl_updateRow_col {l : List (Fin n)} (hl : l.Nodup) (j : Fin n)
    (h : Fin n → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hh : ∀ i ∈ l, ∀ A A' : Matrix (Fin n) (Fin n) ℝ,
      (∀ r c, ¬ (c = j ∧ r ∈ l) → A r c = A' r c) → A i j = A' i j → h i A = h i A')
    (A : Matrix (Fin n) (Fin n) ℝ) :
    l.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        A.updateRow i (Function.update (A i) j (h i A))) A =
      of fun r c => if c = j ∧ r ∈ l then h r A else A r c := by
  have hhom := List.foldl_hom (Function.uncurry : Matrix (Fin n) (Fin n) ℝ → Fin n × Fin n → ℝ)
    (g₁ := fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
      A.updateRow i (Function.update (A i) j (h i A)))
    (g₂ := fun y i => Function.update y (i, j) (h i (of (Function.curry y)))) (l := l)
    (init := A) fun B i => (Matrix.uncurry_updateRow_update B i j _).symm
  ext r c
  have key := congrFun hhom (r, c)
  change _ = (l.foldl _ A) r c at key
  rw [← key, of_apply]
  by_cases hrc : c = j ∧ r ∈ l
  · obtain ⟨rfl, hr⟩ := hrc
    rw [ite_eq_left ⟨rfl, hr⟩]
    refine List.foldl_update_apply_of_pairwise (fun i => (i, c)) (fun i y => h i (of
      (Function.curry y))) (hl.pairwise_of_forall_ne fun a ha b hb hab => ⟨fun e => hab
        (congrArg Prod.fst e), fun y y' hy => hh b hb _ _ (fun r' c' hrc' => hy (r', c')
          fun e => by cases e; exact hrc' ⟨rfl, ha⟩)
        (hy (b, c) fun e => hab (congrArg Prod.fst e).symm)⟩) _ hr
  · rw [ite_eq_right hrc]
    exact List.foldl_update_apply_of_forall_ne _ _ (fun i hi (e : (i, j) = (r, c)) => by
      cases e; exact hrc ⟨rfl, hi⟩) _

/-- The first phase of column $j$ of Algorithm 4.3.5 in exact arithmetic. The updates
$A(j{:}\lambda, j) = A(j{:}\lambda, j) - A(j, k) \cdot A(j{:}\lambda, k)$ over the columns $k$
of a duplicate-free list that does not contain $j$ subtract from each entry $(r, j)$, $r \ge j$,
the products $a_{jk} a_{rk}$ of the columns $k$ with $r \le k + p$. -/
private theorem bandChol_phase1 (j : Fin n) (p : ℕ) :
    ∀ (K : List (Fin n)), K.Nodup → (∀ k ∈ K, k ≠ j) → ∀ S : Matrix (Fin n) (Fin n) ℝ,
    K.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p)).foldl
          (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
            A.updateRow i (Function.update (A i) j (A i j - A j k * A i k))) A) S =
      of fun r c => if c = j ∧ j ≤ r then
        S r j - ∑ k ∈ K.toFinset, (if (r : ℕ) ≤ k + p then S j k * S r k else 0) else S r c := by
  intro K
  induction K with
  | nil =>
    intro _ _ S
    ext r c
    simp only [List.foldl_nil, of_apply, List.toFinset_nil, Finset.sum_empty, sub_zero]
    split_ifs with h
    · rw [h.1]
    · rfl
  | cons k K ih =>
    intro hnd hK S
    rcases List.nodup_cons.1 hnd with ⟨hkK, hnd'⟩
    have hkj : k ≠ j := hK k List.mem_cons_self
    have hmem : ∀ r, r ∈ (List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p) ↔
        j ≤ r ∧ (r : ℕ) ≤ k + p := fun r => by simp
    rw [List.foldl_cons]
    set S₁ := ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p)).foldl
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        A.updateRow i (Function.update (A i) j (A i j - A j k * A i k))) S with hS₁
    have h1 := foldl_updateRow_col
      (l := (List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p))
      ((List.nodup_finRange n).filter _) j
      (fun i A => A i j - A j k * A i k)
      (fun i _ A A' hA hij => by
        rw [hij, hA j k fun h => hkj h.1, hA i k fun h => hkj h.1]) S
    rw [← hS₁] at h1
    have hS₁c : ∀ r c, ¬ (c = j ∧ j ≤ r) → S₁ r c = S r c := fun r c h => by
      rw [h1, of_apply, ite_eq_right fun h' => h ⟨h'.1, ((hmem r).1 h'.2).1⟩]
    have hS₁j : ∀ r, j ≤ r →
        S₁ r j = S r j - if (r : ℕ) ≤ k + p then S j k * S r k else 0 := fun r hjr => by
      rw [h1, of_apply]
      by_cases hrk : (r : ℕ) ≤ k + p
      · rw [ite_eq_left ⟨rfl, (hmem r).2 ⟨hjr, hrk⟩⟩, ite_eq_left hrk]
      · rw [ite_eq_right fun h' => hrk ((hmem r).1 h'.2).2, ite_eq_right hrk, sub_zero]
    rw [ih hnd' (fun k' hk' => hK k' (List.mem_cons_of_mem _ hk'))]
    ext r c
    simp only [of_apply]
    by_cases hc : c = j ∧ j ≤ r
    · rw [ite_eq_left hc, ite_eq_left hc]
      rw [Finset.sum_congr rfl fun k' hk' => by
        have hk'j : k' ≠ j := hK k' (List.mem_cons_of_mem _ (List.mem_toFinset.1 hk'))
        rw [hS₁c j k' fun h => hk'j h.1, hS₁c r k' fun h => hk'j h.1]]
      rw [List.toFinset_cons, Finset.sum_insert fun h => hkK (List.mem_toFinset.1 h),
        hS₁j r hc.2]
      ring
    · rw [ite_eq_right hc, ite_eq_right hc, hS₁c r c hc]

/-- One column step of Algorithm 4.3.5 in exact arithmetic.

**Reading.** The packed program is defined outside the source's SPD and bandwidth hypotheses. It
uses rounded dot-product updates and divides by a totalized square root. The exact factorization
theorem retains the structural hypotheses.
-/
private noncomputable def bandCholStepId (p : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (fun B : Matrix (Fin n) (Fin n) ℝ =>
      ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ j + p)).foldl
        (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
          C.updateRow i (Function.update (C i) j (C i j / Real.sqrt (B j j)))) B)
    (((List.finRange n).filter (fun k : Fin n => k < j ∧ (j : ℕ) ≤ k + p)).foldl
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p)).foldl
          (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
            A.updateRow i (Function.update (A i) j (A i j - A j k * A i k))) A) A)

/-- In exact arithmetic, Algorithm 4.3.5 is the fold of its column steps. -/
private theorem algorithm_4_3_5_id (p : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_3_5 pure p A) = (List.finRange n).foldl (bandCholStepId p) A := by
  simp only [algorithm_4_3_5, pure_bind, List.foldlM_pure]
  rfl

/-- **Algorithm 4.3.5** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive definite with lower bandwidth $p$, and let $G$ be the lower triangle of
the output of Algorithm 4.3.5 in exact arithmetic. Then $G$ is the Cholesky factor
`Matrix.cholesky A`, $G$ has lower bandwidth $p$, and $A = GG^T$.

The source notes that $G$ has the same lower bandwidth as $A$, by Theorem 4.3.1. The band loops
skip only products with a zero factor $g_{jk}$ ($j > k + p$) or $g_{rk}$ ($r > k + p$), so each
column follows the Cholesky recurrence (4.2.9). The lower triangle of the output `F` is
`F - F.strictUpper`. -/
theorem algorithm_4_3_5_spec {p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hp : A.HasLowerBandwidth p) :
    Id.run (algorithm_4_3_5 pure p A) - (Id.run (algorithm_4_3_5 pure p A)).strictUpper =
        cholesky A ∧ (cholesky A).HasLowerBandwidth p ∧
      A = (Id.run (algorithm_4_3_5 pure p A) - (Id.run (algorithm_4_3_5 pure p A)).strictUpper) *
        (Id.run (algorithm_4_3_5 pure p A) - (Id.run (algorithm_4_3_5 pure p A)).strictUpper)ᵀ := by
  have hGp := cholesky_hasLowerBandwidth hA hp
  have hGb := hasLowerBandwidth_iff_fin.1 hGp
  have hAb := hasLowerBandwidth_iff_fin.1 hp
  set G := cholesky A with hG
  have key := List.foldl_finRange_induction (f := bandCholStepId p) (init := A)
    (fun c S => (∀ i j : Fin n, c ≤ (j : ℕ) → S i j = A i j) ∧
      ∀ i j : Fin n, (j : ℕ) < c → j ≤ i → S i j = G i j)
    ⟨fun _ _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun j S hS => by
      obtain ⟨hSA, hSG⟩ := hS
      unfold bandCholStepId
      set K := (List.finRange n).filter (fun k : Fin n => k < j ∧ (j : ℕ) ≤ k + p) with hK
      have hKmem : ∀ k, k ∈ K ↔ k < j ∧ (j : ℕ) ≤ k + p := fun k => by simp [hK]
      rw [bandChol_phase1 j p K ((List.nodup_finRange n).filter _)
        (fun k hk => ne_of_lt ((hKmem k).1 hk).1) S]
      set B := of fun r c => if c = j ∧ j ≤ r then
        S r j - ∑ k ∈ K.toFinset, (if (r : ℕ) ≤ k + p then S j k * S r k else 0) else S r c
        with hB
      beta_reduce
      rw [foldl_updateRow_col ((List.nodup_finRange n).filter _) j
        (fun i C => C i j / Real.sqrt (B j j)) (fun i _ C C' _ hij => by rw [hij]) B]
      -- the entries of column `j` before the division
      have hBr : ∀ r : Fin n, j ≤ r →
          B r j = A r j - ∑ k ∈ univ.filter (· < j), G r k * G j k := by
        intro r hjr
        rw [hB, of_apply, ite_eq_left ⟨rfl, hjr⟩, hSA r j le_rfl]
        congr 1
        have hKf : K.toFinset = univ.filter (fun k : Fin n => k < j ∧ (j : ℕ) ≤ k + p) := by
          ext k; simp [hKmem]
        rw [hKf, Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hkj : k < j
        · rw [hSG j k hkj hkj.le, hSG r k hkj (hkj.le.trans hjr)]
          by_cases hjk : (j : ℕ) ≤ k + p
          · rw [ite_eq_left ⟨hkj, hjk⟩, ite_eq_left hkj]
            by_cases hrk : (r : ℕ) ≤ k + p
            · rw [ite_eq_left hrk, mul_comm]
            · rw [ite_eq_right hrk, hGb r k (by omega), zero_mul]
          · rw [ite_eq_right fun h => hjk h.2, ite_eq_left hkj, hGb j k (by omega), mul_zero]
        · rw [ite_eq_right fun h => hkj h.1, ite_eq_right hkj]
      have hGjj : G j j = Real.sqrt (B j j) := by
        rw [hG, cholesky_apply_self, hBr j le_rfl]
        simp [Real.norm_eq_abs, sq, hG]
      refine ⟨fun i c hc => ?_, fun i c hc hci => ?_⟩
      · have hcj : c ≠ j := fun h => by rw [h] at hc; omega
        rw [of_apply, ite_eq_right fun h => hcj h.1, hB, of_apply, ite_eq_right fun h => hcj h.1]
        exact hSA i c (by omega)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
        · have hcj : c ≠ j := fun h => by rw [h] at hc; omega
          rw [of_apply, ite_eq_right fun h => hcj h.1, hB, of_apply,
            ite_eq_right fun h => hcj h.1]
          exact hSG i c hc hci
        · have hcj : c = j := Fin.ext hc
          subst c
          rw [of_apply]
          by_cases hij : (i : ℕ) ≤ j + p
          · rw [ite_eq_left ⟨rfl, by simp [hci, hij]⟩]
            rcases eq_or_lt_of_le hci with rfl | hji
            · rw [Real.div_sqrt, hGjj]
            · rw [hG, cholesky_apply_of_lt A hji, ← hG, hGjj, hBr i hci]
              simp
          · rw [ite_eq_right fun h => hij (of_decide_eq_true (List.mem_filter.1 h.2).2).2,
              hBr i hci, hAb i j (by omega), hGb i j (by omega)]
            rw [Finset.sum_eq_zero fun k hk => by
              rw [hGb i k (by have := Fin.lt_def.1 (mem_filter.1 hk).2; omega), zero_mul]]
            ring)
  have hlow : (List.finRange n).foldl (bandCholStepId p) A -
      ((List.finRange n).foldl (bandCholStepId p) A).strictUpper = G := by
    ext i k
    rw [Matrix.sub_apply]
    rcases le_or_gt k i with hki | hik
    · rw [key.2 i k k.isLt hki]
      simp [strictUpper, not_lt.2 hki]
    · simp [strictUpper, hik, hG, cholesky_apply_of_gt A hik]
  rw [algorithm_4_3_5_id, hlow]
  exact ⟨rfl, hGp, (cholesky_mul_transpose hA).symm⟩

/-! ### Exact correctness of band Gaussian elimination -/

/-- One pass $k$ of Algorithm 4.3.1 in exact arithmetic.

**Reading.** Lean adds a final empty elimination step, uses a rounding argument and totalizes
division at zero pivots. Its exact factorization theorem assumes invertible proper leading blocks.
-/
private noncomputable def bandGEStepId (p q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((List.finRange n).filter (fun j : Fin n => k < j ∧ (j : ℕ) ≤ k + q)).foldl
    (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) =>
      ((List.finRange n).filter (fun i : Fin n => k < i ∧ (i : ℕ) ≤ k + p)).foldl
        (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
          A.updateRow i (Function.update (A i) j (A i j - A i k * A k j))) A)
    (((List.finRange n).filter (fun i : Fin n => k < i ∧ (i : ℕ) ≤ k + p)).foldl
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        A.updateRow i (Function.update (A i) k (A i k / A k k))) A)

/-- In exact arithmetic, Algorithm 4.3.1 is the fold of its passes. -/
private theorem algorithm_4_3_1_id (p q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_3_1 pure p q A) = (List.finRange n).foldl (bandGEStepId p q) A := by
  simp only [algorithm_4_3_1, pure_bind, List.foldlM_pure]
  rfl

/-- The rank-one update of a pass $k$ of Algorithm 4.3.1 in exact arithmetic, over a list $J$ of
columns and a list $I$ of rows that do not contain $k$, subtracts $s_{rk} s_{kc}$ from the
entries $(r, c)$ with $r \in I$ and $c \in J$. -/
private theorem bandGE_update (k : Fin n) {I : List (Fin n)} (hI : I.Nodup) (hkI : k ∉ I) :
    ∀ (J : List (Fin n)), J.Nodup → k ∉ J → ∀ S : Matrix (Fin n) (Fin n) ℝ,
    J.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) =>
      I.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        A.updateRow i (Function.update (A i) j (A i j - A i k * A k j))) A) S =
      of fun r c => if c ∈ J ∧ r ∈ I then S r c - S r k * S k c else S r c := by
  intro J
  induction J with
  | nil => intro _ _ S; ext r c; simp
  | cons j J ih =>
    intro hJ hkJ S
    rcases List.nodup_cons.1 hJ with ⟨hjJ, hJ'⟩
    have hkj : k ≠ j := fun e => hkJ (e ▸ List.mem_cons_self)
    rw [List.foldl_cons, foldl_updateRow_col hI j (fun i A => A i j - A i k * A k j)
      (fun i _ A A' hA hij => by
        rw [hij, hA i k fun h => hkj h.1, hA k j fun h => hkI h.2]) S,
      ih hJ' (fun h => hkJ (List.mem_cons_of_mem _ h))]
    ext r c
    simp only [of_apply]
    have e1 : ∀ r', (if k = j ∧ r' ∈ I then S r' j - S r' k * S k j else S r' k) = S r' k :=
      fun r' => by rw [ite_eq_right fun h => hkj h.1]
    have e2 : ∀ c', (if c' = j ∧ k ∈ I then S k j - S k k * S k j else S k c') = S k c' :=
      fun c' => by rw [ite_eq_right fun h => hkI h.2]
    simp only [e1, e2]
    by_cases hcj : c = j <;> by_cases hr : r ∈ I <;> simp [hcj, hr, hjJ]

/-- The stages of Gaussian elimination keep the band. If the pivots used as divisors are nonzero,
then every stage of Gaussian elimination on $A$ has the lower bandwidth $p$ and the upper
bandwidth $q$ of $A$. This is the induction of the proof of Theorem 4.3.1. -/
private theorem gemStage_band {A : Matrix (Fin n) (Fin n) ℝ} {p q : ℕ}
    (hpiv : ∀ (m : ℕ) (hm : m < n), m + 1 < n → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0)
    (hp : ∀ i j : Fin n, (j : ℕ) + p < i → A i j = 0)
    (hq : ∀ i j : Fin n, (i : ℕ) + q < j → A i j = 0) (k : ℕ) :
    (∀ i j : Fin n, (j : ℕ) + p < i → gemStage A k i j = 0) ∧
      ∀ i j : Fin n, (i : ℕ) + q < j → gemStage A k i j = 0 := by
  induction k with
  | zero => exact ⟨hp, hq⟩
  | succ k ih =>
    obtain ⟨ihp, ihq⟩ := ih
    by_cases hk : k < n
    swap
    · rw [gemStage_succ_of_le A (not_lt.1 hk)]
      exact ⟨ihp, ihq⟩
    rw [gemStage_succ_of_lt A hk]
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · rw [elimStep_apply, ihp i j hij, zero_sub, neg_eq_zero]
      split_ifs with hki
      · by_cases hik : k + p < (i : ℕ)
        · rw [ihp i ⟨k, hk⟩ hik, zero_mul, zero_mul]
        · have hjk : (j : ℕ) < k := by omega
          rw [gemStage_apply_eq_zero_of_lt A (fun m hm _ hmn => hpiv m hm hmn) hjk
            (Fin.lt_def.2 hjk), mul_zero]
      · rfl
    · rw [elimStep_apply, ihq i j hij, zero_sub, neg_eq_zero]
      split_ifs with hki
      · rw [ihq ⟨k, hk⟩ j (by have := Fin.lt_def.1 hki; simp only at this ⊢; omega), mul_zero]
      · rfl

/-- **Algorithm 4.3.1** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
have lower bandwidth $p$ and upper bandwidth $q$, and assume that $A(1{:}k, 1{:}k)$ is
nonsingular for $k = 1{:}n-1$. Let $F$ be the output of Algorithm 4.3.1 in exact arithmetic.
Then the unit lower triangular $L$ stored below the diagonal of $F$ and the upper triangular $U$
stored on and above it form the LU factorization $A = LU$.

**Reading.** The source says "assuming it exists". This is read as the nonsingularity of the
leading principal submatrices that are used as pivots. It is stronger than the existence of an
LU factorization, and it is the hypothesis under which Gaussian elimination without pivoting
runs to completion.

The factors are `GolubVanLoan.Chapter03.packedL F` and `GolubVanLoan.Chapter03.packedU F`, and
the conclusion is `Matrix.IsLU`. The band loops perform exactly the operations of Gaussian
elimination on the entries that can be nonzero: the stages keep the band, so the multipliers and
updates that are skipped are zero. The result is the multiplier matrix `Matrix.gemLower A` and
the last stage `Matrix.gemStage A n`. -/
theorem algorithm_4_3_1_spec {p q : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hp : A.HasLowerBandwidth p) (hq : A.HasUpperBandwidth q)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    IsLU A (Chapter03.packedL (Id.run (algorithm_4_3_1 pure p q A)))
      (Chapter03.packedU (Id.run (algorithm_4_3_1 pure p q A))) := by
  have hpiv := (gemStage_pivots_ne_zero_iff A).2 hA
  have hb := gemStage_band hpiv (hasLowerBandwidth_iff_fin.1 hp) (hasUpperBandwidth_iff_fin.1 hq)
  have hz : ∀ (k : ℕ) (i j : Fin n), (j : ℕ) < k → j < i → gemStage A k i j = 0 :=
    fun k i j hjk hji =>
      gemStage_apply_eq_zero_of_lt A (fun m hm _ hmn => hpiv m hm hmn) hjk hji
  have key := List.foldl_finRange_induction (f := bandGEStepId p q) (init := A)
    (fun c S => ∀ i j : Fin n, S i j =
      if j < i ∧ (j : ℕ) < c then gemStage A j i j / gemStage A j j j else gemStage A c i j)
    (fun i j => by simp)
    (fun k S hS i j => by
      unfold bandGEStepId
      set I := (List.finRange n).filter (fun i : Fin n => k < i ∧ (i : ℕ) ≤ k + p) with hI
      set J := (List.finRange n).filter (fun j : Fin n => k < j ∧ (j : ℕ) ≤ k + q) with hJ
      have hImem : ∀ r, r ∈ I ↔ k < r ∧ (r : ℕ) ≤ k + p := fun r => by simp [hI]
      have hJmem : ∀ r, r ∈ J ↔ k < r ∧ (r : ℕ) ≤ k + q := fun r => by simp [hJ]
      have hIn : I.Nodup := (List.nodup_finRange n).filter _
      have hJn : J.Nodup := (List.nodup_finRange n).filter _
      have hkI : k ∉ I := fun h => lt_irrefl _ ((hImem k).1 h).1
      have hkJ : k ∉ J := fun h => lt_irrefl _ ((hJmem k).1 h).1
      rw [foldl_updateRow_col hIn k (fun i A => A i k / A k k)
        (fun i _ A A' hA' hik => by rw [hik, hA' k k fun h => hkI h.2]) S]
      generalize hS₁ : (of fun r c => if c = k ∧ r ∈ I then S r k / S k k else S r c :
        Matrix (Fin n) (Fin n) ℝ) = S₁
      rw [bandGE_update k hIn hkI J hJn hkJ S₁, of_apply]
      have hS₁k : ∀ r, S₁ r k = if r ∈ I then S r k / S k k else S r k := fun r => by
        rw [← hS₁, of_apply]
        by_cases hr : r ∈ I
        · rw [ite_eq_left (show k = k ∧ r ∈ I from ⟨rfl, hr⟩), ite_eq_left hr]
        · rw [ite_eq_right (show ¬ (k = k ∧ r ∈ I) from fun h => hr h.2), ite_eq_right hr]
      have hS₁c : ∀ r c, c ≠ k → S₁ r c = S r c := fun r c hc => by
        rw [← hS₁, of_apply, ite_eq_right (show ¬ (c = k ∧ r ∈ I) from fun h => hc h.1)]
      have hSG : ∀ r c : Fin n, ¬ (c < r ∧ (c : ℕ) < k) → S r c = gemStage A k r c :=
        fun r c h => by rw [hS r c, ite_eq_right h]
      have hSkk : S k k = gemStage A k k k := hSG k k fun h => lt_irrefl _ h.1
      have hSik : ∀ r, S r k = gemStage A k r k := fun r => hSG r k fun h => lt_irrefl _ h.2
      have hG' : gemStage A ((k : ℕ) + 1) i j =
          gemStage A k i j - if k < i then
            gemStage A k i k * (gemStage A k k k)⁻¹ * gemStage A k k j else 0 := by
        rw [gemStage_succ_of_lt A k.isLt, elimStep_apply]
      rcases lt_trichotomy j k with hjk | hjk | hkj
      · -- a finished column
        have hjJ : j ∉ J := fun h => absurd ((hJmem j).1 h).1 (not_lt.2 hjk.le)
        have h1 : (j : ℕ) < k := Fin.lt_def.1 hjk
        rw [ite_eq_right (show ¬ (j ∈ J ∧ i ∈ I) from fun h => hjJ h.1),
          hS₁c i j (ne_of_lt hjk), hS i j]
        by_cases hji : j < i
        · rw [ite_eq_left (show j < i ∧ (j : ℕ) < k from ⟨hji, h1⟩),
            ite_eq_left (show j < i ∧ (j : ℕ) < k + 1 from ⟨hji, by omega⟩)]
        · rw [ite_eq_right (show ¬ (j < i ∧ (j : ℕ) < k) from fun h => hji h.1),
            ite_eq_right (show ¬ (j < i ∧ (j : ℕ) < k + 1) from fun h => hji h.1), hG',
            hz k k j h1 hjk, mul_zero]
          simp
      · -- the pivot column
        subst j
        rw [ite_eq_right (show ¬ (k ∈ J ∧ i ∈ I) from fun h => hkJ h.1), hS₁k i]
        by_cases hki : k < i
        · rw [ite_eq_left (show k < i ∧ (k : ℕ) < k + 1 from ⟨hki, Nat.lt_succ_self _⟩)]
          by_cases hi : i ∈ I
          · rw [ite_eq_left hi, hSik, hSkk]
          · have hip : (k : ℕ) + p < i := by
              have := (hImem i).not.1 hi
              have := Fin.lt_def.1 hki
              omega
            rw [ite_eq_right hi, hSik, (hb k).1 i k hip, zero_div]
        · have hi : i ∉ I := fun h => hki ((hImem i).1 h).1
          rw [ite_eq_right (show ¬ (k < i ∧ (k : ℕ) < k + 1) from fun h => hki h.1),
            ite_eq_right hi, hSik, hG', ite_eq_right hki, sub_zero]
      · -- a column to the right
        have hjk' : j ≠ k := ne_of_gt hkj
        have hno : ¬ (j < i ∧ (j : ℕ) < k + 1) := fun h => by
          have := Fin.lt_def.1 hkj; omega
        have hSij : S i j = gemStage A k i j :=
          hSG i j fun h => absurd h.2 (by have := Fin.lt_def.1 hkj; omega)
        have hSkj : S k j = gemStage A k k j := hSG k j fun h => absurd h.1 (not_lt.2 hkj.le)
        rw [ite_eq_right hno, hG']
        by_cases hij : j ∈ J ∧ i ∈ I
        · have hki : k < i := ((hImem i).1 hij.2).1
          rw [ite_eq_left hij, hS₁c i j hjk', hS₁k i, ite_eq_left hij.2, hS₁c k j hjk', hSik,
            hSkk, hSkj, hSij, ite_eq_left hki]
          ring
        · rw [ite_eq_right hij, hS₁c i j hjk', hSij]
          by_cases hki : k < i
          · rw [ite_eq_left hki]
            by_cases hi : i ∈ I
            · have hjq : (k : ℕ) + q < j := by
                have := (hJmem j).not.1 fun h => hij ⟨h, hi⟩
                have := Fin.lt_def.1 hkj
                omega
              rw [(hb k).2 k j hjq, mul_zero, sub_zero]
            · have hip : (k : ℕ) + p < i := by
                have := (hImem i).not.1 hi
                have := Fin.lt_def.1 hki
                omega
              rw [(hb k).1 i k hip, zero_mul, zero_mul, sub_zero]
          · rw [ite_eq_right hki, sub_zero])
  rw [Chapter03.packedL, Chapter03.packedU, algorithm_4_3_1_id]
  have hL : 1 + ((List.finRange n).foldl (bandGEStepId p q) A).strictLower = gemLower A := by
    ext i j
    by_cases hji : j < i
    · simp [strictLower, gemLower, hji, key i j, one_apply_ne (ne_of_gt hji)]
    · simp [strictLower, gemLower, hji, Matrix.one_apply]
  have hU : (List.finRange n).foldl (bandGEStepId p q) A -
      ((List.finRange n).foldl (bandGEStepId p q) A).strictLower = gemStage A n := by
    ext i j
    by_cases hji : j < i
    · simp only [Matrix.sub_apply, strictLower, of_apply, ite_eq_left hji, sub_self]
      exact (hz n i j j.isLt hji).symm
    · simp [strictLower, hji, key i j]
  rw [hL, hU]
  exact isLU_gemLower_gemStage A hpiv

/-! ### §4.3.8 The inverse of a band matrix -/

/-- For $k \le n$, the partition $\{0, \dots, k-1\} \cup \{k, \dots, n-1\}$ of the indices of an
$n \times n$ matrix into square diagonal blocks of sizes $k$ and $n - k$, as the equivalence
`Fin k ⊕ Fin (n - k) ≃ Fin n`. -/
def blockSplit {k : ℕ} (hk : k ≤ n) : Fin k ⊕ Fin (n - k) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hk))

@[simp]
private theorem blockSplit_inl {k : ℕ} (hk : k ≤ n) (a : Fin k) :
    ((blockSplit hk (Sum.inl a) : Fin n) : ℕ) = a := by
  simp [blockSplit]

@[simp]
private theorem blockSplit_inr {k : ℕ} (hk : k ≤ n) (a : Fin (n - k)) :
    ((blockSplit hk (Sum.inr a) : Fin n) : ℕ) = k + a := by
  simp [blockSplit]

/-- A matrix whose rows from $p$ on vanish has rank at most $p$. -/
private theorem rank_le_of_rows_eq_zero {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ) (p : ℕ)
    (h : ∀ i : Fin m, p ≤ (i : ℕ) → ∀ j, B i j = 0) : B.rank ≤ p := by
  classical
  have hB : B = diagonal (fun i : Fin m => if (i : ℕ) < p then (1 : ℝ) else 0) * B := by
    ext i j
    rw [diagonal_mul]
    split_ifs with hi
    · rw [one_mul]
    · rw [zero_mul, h i (not_lt.1 hi)]
  rw [hB]
  refine (rank_mul_le_left _ _).trans ?_
  rw [rank_diagonal]
  calc Fintype.card {i : Fin m // (if (i : ℕ) < p then (1 : ℝ) else 0) ≠ 0}
      ≤ Fintype.card (Fin p) := by
        refine Fintype.card_le_of_injective (fun i => ⟨i.1, ?_⟩) fun a b hab => ?_
        · by_contra h'
          exact i.2 (ite_eq_right h')
        · exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val hab))
    _ = p := Fintype.card_fin p

/-- A matrix whose columns from $q$ on vanish has rank at most $q$. -/
private theorem rank_le_of_cols_eq_zero {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ) (q : ℕ)
    (h : ∀ j : Fin k, q ≤ (j : ℕ) → ∀ i, B i j = 0) : B.rank ≤ q := by
  rw [← rank_transpose]
  exact rank_le_of_rows_eq_zero Bᵀ q fun j hj i => h j hj i

/-- **Theorem 4.3.3** of [golub2013matrix], with (4.3.1) and (4.3.2). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, with lower bandwidth $p$ and upper bandwidth
$q$, and partition
$$A = \begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix}$$
with square diagonal blocks $A_{11} \in \mathbb{R}^{k \times k}$ and $A_{22}$, $k \le n$. If
$X = A^{-1} = \begin{bmatrix} X_{11} & X_{12} \\ X_{21} & X_{22} \end{bmatrix}$ is partitioned
conformably, then
$$\operatorname{rank}(X_{21}) \le p, \qquad (4.3.1)$$
$$\operatorname{rank}(X_{12}) \le q. \qquad (4.3.2)$$

The partition is `GolubVanLoan.Chapter04.blockSplit`. The proof uses the nullity theorem,
$\operatorname{rank}(X_{21}) = \operatorname{rank}(A_{21})$, so the limit argument of the source
(Problem P4.3.11) is not needed. -/
theorem theorem_4_3_3 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {p q : ℕ}
    (hp : A.HasLowerBandwidth p) (hq : A.HasUpperBandwidth q) {k : ℕ} (hk : k ≤ n) :
    (A⁻¹.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₂₁.rank ≤ p ∧
      (A⁻¹.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₁₂.rank ≤ q := by
  have hp' := hasLowerBandwidth_iff_fin.1 hp
  have hq' := hasUpperBandwidth_iff_fin.1 hq
  have hB : IsUnit (A.submatrix (blockSplit hk) (blockSplit hk)) :=
    (isUnit_submatrix_equiv _ _).2 hA
  have hinv : A⁻¹.submatrix (blockSplit hk) (blockSplit hk) =
      (A.submatrix (blockSplit hk) (blockSplit hk))⁻¹ := by
    rw [inv_submatrix_equiv]
  rw [hinv, rank_inv_toBlocks₂₁ hB, rank_inv_toBlocks₁₂ hB]
  refine ⟨rank_le_of_rows_eq_zero _ p fun i hi j => ?_,
    rank_le_of_cols_eq_zero _ q fun j hj i => ?_⟩
  · simp only [toBlocks₂₁, of_apply, submatrix_apply]
    exact hp' _ _ (by simp; omega)
  · simp only [toBlocks₁₂, of_apply, submatrix_apply]
    exact hq' _ _ (by simp; omega)

/-- **Section 4.3.8** of [golub2013matrix], the equality of ranks. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular and let $k \le n$. If $A$ and $X = A^{-1}$ are
partitioned as in Theorem 4.3.3, with square diagonal blocks of sizes $k$ and $n - k$, then
$$\operatorname{rank}(A_{21}) = \operatorname{rank}(X_{21}), \qquad
  \operatorname{rank}(A_{12}) = \operatorname{rank}(X_{12}).$$

The source says that this can be shown and attributes it to Strang and Nguyen. It is the nullity
theorem, and it needs no band structure. -/
theorem rank_inv_offDiag_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {k : ℕ}
    (hk : k ≤ n) :
    (A⁻¹.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₂₁.rank =
        (A.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₂₁.rank ∧
      (A⁻¹.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₁₂.rank =
        (A.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₁₂.rank := by
  have hB : IsUnit (A.submatrix (blockSplit hk) (blockSplit hk)) :=
    (isUnit_submatrix_equiv _ _).2 hA
  rw [← inv_submatrix_equiv]
  exact ⟨rank_inv_toBlocks₂₁ hB, rank_inv_toBlocks₁₂ hB⟩

end GolubVanLoan.Chapter04
