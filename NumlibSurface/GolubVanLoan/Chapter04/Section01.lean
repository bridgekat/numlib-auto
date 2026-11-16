/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.FloatingPoint.LU
import Numlib.FloatingPoint.Program
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.LU
import NumlibSurface.GolubVanLoan.Chapter02.Section03
import NumlibSurface.GolubVanLoan.Chapter03.Section02

/-!
# Golub and Van Loan, Section 4.1: Diagonal dominance and symmetry

This module formalizes §4.1 of [golub2013matrix]. A matrix $A \in \mathbb{R}^{n \times n}$ is column
diagonally dominant if $\sum_{i \neq j} |a_{ij}| \le |a_{jj}|$ for every column $j$. Theorem 4.1.1
says that a nonsingular column diagonally dominant matrix has an LU factorization without pivoting
with $|\ell_{ij}| \le 1$, and Theorem 4.1.2 bounds $\|A^{-1}\|_1$ by $1/\delta$ when every column is
dominant with margin $\delta > 0$. Theorem 4.1.3 says that a symmetric matrix whose leading
principal submatrices $A(1{:}k, 1{:}k)$, $k = 1{:}n-1$, are nonsingular has a unique factorization
$A = LDL^T$ with $L$ unit lower triangular and $D$ diagonal. Then $Ax = b$ is solved in three steps
$Lz = b$, $Dy = z$, $L^T x = y$.

Algorithm 4.1.1 computes the $LDL^T$ factorization. The module gives it as a program with a rounding
bridge into the relation `FloatingPoint.RoundsLDL` and an exact specification, and proves the
backward error bound (4.1.4) of the solve. The proofs specialize
`Numlib.LinearAlgebra.Matrix.DiagDominant`, `Numlib.LinearAlgebra.Matrix.LU` and
`Numlib.FloatingPoint.LU`, with the run calculus of `Numlib.FloatingPoint.Program`.

## Main definitions

* Algorithm 4.1.1, `GolubVanLoan.Chapter04.algorithm_4_1_1`: the $LDL^T$ factorization of a
  symmetric matrix, overwriting $A$.
* §4.1.2, `GolubVanLoan.Chapter04.solveLDLT`: the three-step solve $Lz = b$, $Dy = z$, $L^T x = y$
  with a packed factor.

## Main results

* Theorem 4.1.1, `GolubVanLoan.Chapter04.theorem_4_1_1`: a nonsingular column diagonally dominant
  matrix has an LU factorization with $|\ell_{ij}| \le 1$.
* (4.1.2), `GolubVanLoan.Chapter04.equation_4_1_2`: the first step of Gaussian elimination in block
  form.
* Theorem 4.1.2, `GolubVanLoan.Chapter04.theorem_4_1_2`: column dominance with margin $\delta > 0$
  gives a nonsingular $A$ with $\|A^{-1}\|_1 \le 1/\delta$.
* Theorem 4.1.3, `GolubVanLoan.Chapter04.theorem_4_1_3`: existence and uniqueness of the $LDL^T$
  factorization.
* §4.1.2, `GolubVanLoan.Chapter04.ldlt_solve`: the three-step solve solves $Ax = b$.
* Algorithm 4.1.1, `GolubVanLoan.Chapter04.algorithm_4_1_1_rounds` and
  `GolubVanLoan.Chapter04.algorithm_4_1_1_spec`: every run computes a factorization in the sense of
  `FloatingPoint.RoundsLDL`, and the exact run computes $A = LDL^T$.
* (4.1.4), `GolubVanLoan.Chapter04.equation_4_1_4`: the computed solution satisfies
  $(A + E)\hat x = b$ with $|E| \le \gamma_{3n+2} |\hat L| |\hat D| |\hat L^T|$.

## Conventions

* Indices are 0-based. The hypothesis "$A(1{:}k, 1{:}k)$ is nonsingular for $k = 1{:}n-1$" is `∀ k,
  IsUnit (A.strictLeadingPrincipalSubmatrix k)`, over the orders $0, \dots, n - 1$; the block of
  order $0$ is empty.
* Row and column diagonal dominance (4.1.1) are `Matrix.IsDiagDominant` and
  `Matrix.IsColDiagDominant`, with the norm $|\cdot|$ on $\mathbb{R}$. The margin $\delta$ of
  (4.1.3) is a hypothesis.
* The factorization $A = LDL^T$ is `Matrix.IsLDM A L D L`.
* The source states the first-order bound $|E| \le nu(2|A| + 4|\hat L||\hat D||\hat L^T|) + O(u^2)$
  in (4.1.4). The theorem states the rigorous bound $|E| \le \gamma_{3n+2} |\hat L||\hat D||\hat
  L^T|$, which implies the printed one to first order for $n \ge 2$, since
  $\gamma_{3n+2} = (3n + 2)u + O(u^2)$ and $3n + 2 \le 4n$.

## Implementation notes

* Algorithm 4.1.1 follows the algorithm conventions of `NumlibSurface.GolubVanLoan`: every product
  and difference passes through the rounding hook `rnd`. The inner products
  $A(j, 1{:}j-1) \cdot v(1{:}j-1)$ and $A(j{+}1{:}n, 1{:}j-1) \cdot v(1{:}j-1)$ are running
  differences from the entry of $A$ (`FloatingPoint.runningDiff`), which is the operation order of
  `FloatingPoint.RoundsLDL`.
* The packed output $F$ holds $L$ strictly below the diagonal and $D$ on it. Its unit lower factor
  is `GolubVanLoan.Chapter03.packedL F`, which is $I$ plus the strict lower triangle of $F$, and its
  diagonal factor is `Matrix.diagonal F.diag`.
* The solve `GolubVanLoan.Chapter04.solveLDLT` uses the column-oriented substitutions of Chapter 3,
  Algorithms 3.1.3 and 3.1.4, with a rounded division by the pivots between them.

## Deviations from the source

* **Algorithm 4.1.1** (reading). The source assumes that $A$ has an LU factorization. The
  specification assumes the hypothesis of Theorem 4.1.3, nonsingular leading principal submatrices
  of orders $1, \dots, n-1$. See `GolubVanLoan.Chapter04.algorithm_4_1_1_spec`.
* **References to "Algorithm 4.1.2"** (typo). The source refers twice to an "Algorithm 4.1.2"; it
  means Algorithm 4.1.1. See `GolubVanLoan.Chapter04.algorithm_4_1_1`.

## Not formalized

* **Operation counts.**
-/

open FloatingPoint Matrix Finset

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### §4.1.1 Diagonal dominance -/

/-- **Theorem 4.1.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular and
column diagonally dominant. Then $A$ has an LU factorization $A = LU$, and the entries of
$L = (\ell_{ij})$ satisfy $|\ell_{ij}| \le 1$.

Column diagonal dominance is the weak condition $\sum_{i \neq j} |a_{ij}| \le |a_{jj}|$,
`Matrix.IsColDiagDominant`, and the factorization is `Matrix.IsLU`. The proof of the source
writes a strict inequality in one step of its chain under this weak hypothesis; the backbone
proof uses the weak inequality. -/
theorem theorem_4_1_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hdom : A.IsColDiagDominant) : ∃ L U, IsLU A L U ∧ ∀ i j, |L i j| ≤ 1 := by
  simpa only [Real.norm_eq_abs] using exists_isLU_of_isColDiagDominant hA hdom

/-- **Equation (4.1.2)** of [golub2013matrix], the first step of Gaussian elimination in block form.
Let $\alpha \in \mathbb{R}$ with $\alpha \neq 0$, let $v, w \in \mathbb{R}^n$ and let
$C \in \mathbb{R}^{n \times n}$. Then
$$\begin{bmatrix} \alpha & w^T \\ v & C \end{bmatrix} = \begin{bmatrix} 1 & 0 \\ v/\alpha & I_n
  \end{bmatrix} \begin{bmatrix} 1 & 0 \\ 0 & B \end{bmatrix} \begin{bmatrix} \alpha & w^T \\ 0 &
  I_n \end{bmatrix}, \qquad B = C - \frac{1}{\alpha} v w^T.$$

The matrices of order $n + 1$ are indexed by `Fin 1 ⊕ Fin n`. -/
theorem equation_4_1_2 {α : ℝ} (hα : α ≠ 0) (w v : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    fromBlocks (of fun _ _ => α) (replicateRow (Fin 1) w) (replicateCol (Fin 1) v) C =
      fromBlocks 1 0 (replicateCol (Fin 1) (α⁻¹ • v)) 1 *
        fromBlocks 1 0 0 (C - α⁻¹ • vecMulVec v w) *
        fromBlocks (of fun _ _ => α) (replicateRow (Fin 1) w) 0 1 := by
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · ext i j
    simp [Matrix.mul_apply]
    field_simp
  · ext i j
    simp [Matrix.mul_apply, vecMulVec_apply]

/-- **Theorem 4.1.2** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and $\delta > 0$,
and assume that every column $j$ satisfies
$$\delta \le |a_{jj}| - \sum_{i \neq j} |a_{ij}|.$$
Then $A$ is nonsingular and $\|A^{-1}\|_1 \le 1/\delta$.

The source defines $\delta = \min_j (|a_{jj}| - \sum_{i \neq j} |a_{ij}|)$ in (4.1.3) and
assumes $\delta > 0$. The theorem takes any positive lower bound $\delta$ on these column
margins. The norm $\|\cdot\|_1$ is `Matrix.lpOpNorm 1`. -/
theorem theorem_4_1_2 {A : Matrix (Fin n) (Fin n) ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hA : ∀ j, δ ≤ |A j j| - ∑ i ∈ univ.erase j, |A i j|) :
    IsUnit A ∧ lpOpNorm 1 A⁻¹ ≤ 1 / δ := by
  have hA' : ∀ j, δ ≤ ‖A j j‖ - ∑ i ∈ univ.erase j, ‖A i j‖ := by
    simpa only [Real.norm_eq_abs] using hA
  have hu : IsUnit A := IsStrictColDiagDominant.isUnit fun j => by linarith [hA' j]
  refine ⟨hu, ?_⟩
  rw [GolubVanLoan.Chapter02.equation_2_3_9]
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [Real.iSup_of_isEmpty]
    positivity
  refine ciSup_le fun j => ?_
  have hx := mul_sum_norm_le_sum_norm_mulVec_of_colDiagDominantMargin (A := A) hA'
    (A⁻¹ *ᵥ Pi.single j 1)
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).1 hu), one_mulVec] at hx
  have h1 : ∑ i, |(Pi.single j (1 : ℝ) : Fin n → ℝ) i| = 1 := by
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
    simp
  have h2 : ∀ i, (A⁻¹ *ᵥ Pi.single j 1) i = A⁻¹ i j := fun i => by
    simp [mulVec, dotProduct, Pi.single_apply]
  simp only [h2, Real.norm_eq_abs] at hx
  rw [h1] at hx
  rw [le_div_iff₀ hδ, mul_comm]
  exact hx

/-! ### §4.1.2 Symmetry and the $LDL^T$ factorization -/

/-- **Theorem 4.1.3** of [golub2013matrix] ($LDL^T$ factorization). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, and let $A(1{:}k, 1{:}k)$ be nonsingular for
$k = 1{:}n-1$. Then there exist a unit lower triangular $L$ and a diagonal $D$ with
$$A = LDL^T,$$
and the pair $(L, D)$ is unique.

The factorization is `Matrix.IsLDM A L D L`. -/
theorem theorem_4_1_3 {A : Matrix (Fin n) (Fin n) ℝ} (hs : A.IsSymm)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    ∃! LD : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ, IsLDM A LD.1 LD.2 LD.1 := by
  obtain ⟨⟨L, D, M⟩, h, huniq⟩ := existsUnique_isLDM hA
  have hML : M = L := h.eq_of_isSymm hs hA
  subst hML
  refine ⟨(M, D), h, fun LD h' => ?_⟩
  have := huniq (LD.1, LD.2, LD.1) h'
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.1 this.2.1

/-- **Section 4.1.2** of [golub2013matrix], the three-step solve. Let $A = LDL^T$ with $L$ unit
lower triangular and $D$ diagonal, and let $b, z, y, x \in \mathbb{R}^n$. If $Lz = b$, $Dy = z$
and $L^T x = y$, then $Ax = b$, because $Ax = L(D(L^T x)) = L(Dy) = Lz = b$. -/
theorem ldlt_solve {A L D : Matrix (Fin n) (Fin n) ℝ} (h : IsLDM A L D L) {b z y x : Fin n → ℝ}
    (hz : L *ᵥ z = b) (hy : D *ᵥ y = z) (hx : Lᵀ *ᵥ x = y) : A *ᵥ x = b := by
  rw [← h.mul_eq, ← mulVec_mulVec, ← mulVec_mulVec, hx, hy, hz]

/-! ### Algorithm 4.1.1 -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.1.1** of [golub2013matrix] (LDLT). If $A \in \mathbb{R}^{n \times n}$ is symmetric
and has an LU factorization, then the algorithm computes a unit lower triangular matrix $L$ and
a diagonal matrix $D = \operatorname{diag}(d_1, \dots, d_n)$ so that $A = LDL^T$. The entry
$a_{ij}$ is overwritten with $\ell_{ij}$ if $i > j$ and with $d_i$ if $i = j$.
```
for j = 1:n
    for i = 1:j−1
        v(i) = A(j, i) A(i, i)
    end
    A(j, j) = A(j, j) − A(j, 1:j−1) · v(1:j−1)
    A(j+1:n, j) = (A(j+1:n, j) − A(j+1:n, 1:j−1) · v(1:j−1)) / A(j, j)
end
```

The inner products are running differences from the entry of $A$ (`FloatingPoint.runningDiff`).
The column $A(j{+}1{:}n, j)$ is computed entry by entry, since its entries are independent. -/
noncomputable def algorithm_4_1_1 (A : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) => do
    let v ← ((List.finRange n).filter (· < j)).foldlM (fun (v : Fin n → ℝ) (i : Fin n) => do
      let p ← rnd (A j i * A i i)
      pure (Function.update v i p)) 0
    let d ← runningDiff rnd ((List.finRange n).filter (· < j)) (A j) v (A j j)
    ((List.finRange n).filter (j < ·)).foldlM (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
      let t ← runningDiff rnd ((List.finRange n).filter (· < j)) (B i) v (B i j)
      let l ← rnd (t / d)
      pure (B.updateRow i (Function.update (B i) j l)))
      (A.updateRow j (Function.update (A j) j d))) A

end Programs

/-- A loop that writes one entry of column $j$ per row. Let $l$ be a list of rows without
duplicates, and consider the loop over $l$ whose step $i$ replaces the entry $(i, j)$ of the
current matrix by a result of `h i` applied to the current row $i$. Then $S'$ is a result of the
loop from $S$ if and only if every row of $S'$ off the list equals that row of $S$, and every
row $i$ on the list is row $i$ of $S$ with entry $j$ replaced by some result of `h i` on row $i$
of $S$. -/
theorem mem_run_foldlM_updateRow_iff {m k : ℕ} {l : List (Fin m)} (hl : l.Nodup) (j : Fin k)
    (h : Fin m → (Fin k → ℝ) → SetM ℝ) (S S' : Matrix (Fin m) (Fin k) ℝ) :
    S' ∈ (l.foldlM (fun (B : Matrix (Fin m) (Fin k) ℝ) (i : Fin m) => do
        let x ← h i (B i)
        pure (B.updateRow i (Function.update (B i) j x))) S).run ↔
      (∀ i, i ∉ l → S' i = S i) ∧
        ∀ i ∈ l, ∃ x ∈ (h i (S i)).run, S' i = Function.update (S i) j x := by
  have key := SetM.mem_run_foldlM_update_of_nodup
    (fun (i : Fin m) (r : Fin k → ℝ) (_ : Fin m → Fin k → ℝ) =>
      (do let x ← h i r; pure (Function.update r j x) : SetM (Fin k → ℝ))) l hl
    (fun _ _ _ _ _ _ => rfl) S S'
  simp only [bind_assoc, pure_bind, SetM.mem_run_bind, SetM.mem_run_pure] at key
  exact key

/-- The indices below $j$, in increasing order. This is the order of the inner products
$A(j, 1{:}j-1) \cdot v(1{:}j-1)$ in the factorizations of this chapter. -/
abbrev below (j : Fin n) : List (Fin n) := (List.finRange n).filter (· < j)

/-- An index $k$ lies in `GolubVanLoan.Chapter04.below j` if and only if $k < j$. -/
theorem mem_below {j k : Fin n} : k ∈ below j ↔ k < j := by simp [below]

/-- The list `GolubVanLoan.Chapter04.below j` has no duplicates. -/
theorem nodup_below (j : Fin n) : (below j).Nodup := (List.nodup_finRange n).filter _

section Bridge

variable (fp : RoundingModel ℝ)


/-- Column $j$ of the packed state $S$ is a finished column of Algorithm 4.1.1: with rounded
products $v_k = \mathrm{fl}(\ell_{jk} d_k)$, the pivot is the running difference of $a_{jj}$,
and each entry below it is a rounded quotient of a running difference of $a_{ij}$ by the pivot. -/
private def ColDone (A S : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : Prop :=
  ∃ v : Fin n → ℝ, (∀ k ∈ below j, fp.Rounds (S j k * S k k) (v k)) ∧
    RoundsRunningDiff fp (below j) (S j) v (A j j) (S j j) ∧
    ∀ i, j < i → ∃ t, RoundsRunningDiff fp (below j) (S i) v (A i j) t ∧
      fp.Rounds (t / S j j) (S i j)

/-- A finished column stays finished when the state changes only in columns to its right. -/
private theorem ColDone.congr {A S S' : Matrix (Fin n) (Fin n) ℝ} {j : Fin n}
    (h : ColDone fp A S j) (hS : ∀ i k, k ≤ j → S' i k = S i k) : ColDone fp A S' j := by
  obtain ⟨v, hv, hd, hcol⟩ := h
  refine ⟨v, fun k hk => ?_, ?_, fun i hi => ?_⟩
  · have hkj := le_of_lt (mem_below.1 hk)
    rw [hS j k hkj, hS k k hkj]
    exact hv k hk
  · rw [hS j j le_rfl]
    exact hd.congr (fun k hk => hS j k (le_of_lt (mem_below.1 hk))) fun _ _ => rfl
  · obtain ⟨t, ht, hl⟩ := hcol i hi
    refine ⟨t, ht.congr (fun k hk => hS i k (le_of_lt (mem_below.1 hk))) fun _ _ => rfl, ?_⟩
    rw [hS i j le_rfl, hS j j le_rfl]
    exact hl

/-- The loop invariant of Algorithm 4.1.1 after $c$ columns: the columns from $c$ on still hold $A$,
and the columns before $c$ are finished. -/
private def Inv (A : Matrix (Fin n) (Fin n) ℝ) (c : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i k : Fin n, c ≤ k.val → S i k = A i k) ∧ ∀ j : Fin n, j.val < c → ColDone fp A S j

/-- One column step of Algorithm 4.1.1 keeps the loop invariant. -/
private theorem inv_step (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Inv fp A j S) (S' : Matrix (Fin n) (Fin n) ℝ)
    (hS' : S' ∈ ((do
      let v ← (below j).foldlM (fun (v : Fin n → ℝ) (i : Fin n) => do
        let p ← fp.round (S j i * S i i)
        pure (Function.update v i p)) 0
      let d ← runningDiff fp.round (below j) (S j) v (S j j)
      ((List.finRange n).filter (j < ·)).foldlM
        (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
          let t ← runningDiff fp.round (below j) (B i) v (B i j)
          let l ← fp.round (t / d)
          pure (B.updateRow i (Function.update (B i) j l)))
        (S.updateRow j (Function.update (S j) j d))) : SetM _).run) :
    Inv fp A (j + 1) S' := by
  obtain ⟨hA, hdone⟩ := hS
  simp only [SetM.mem_run_bind] at hS'
  obtain ⟨v, hv, d, hd, hS'⟩ := hS'
  -- the products `v`
  have hv' : ∀ k ∈ below j, fp.Rounds (S j k * S k k) (v k) := by
    have := (SetM.mem_run_foldlM_update_of_nodup
      (fun (i : Fin n) (_ : ℝ) (_ : Fin n → ℝ) => fp.round (S j i * S i i)) (below j)
      (nodup_below j)
      (fun _ _ _ _ _ _ => rfl) 0 v).1 hv
    exact fun k hk => this.2 k hk
  have hd' : RoundsRunningDiff fp (below j) (S j) v (S j j) d :=
    (mem_run_runningDiff_iff (nodup_below j)).1 hd
  -- the column loop writes row `i > j` of the matrix once
  set S₁ := S.updateRow j (Function.update (S j) j d) with hS₁
  have hcol := (mem_run_foldlM_updateRow_iff ((List.nodup_finRange n).filter _) j
    (fun i r => do let t ← runningDiff fp.round (below j) r v (r j); fp.round (t / d)) S₁ S').1
    (by simpa only [bind_assoc] using hS')
  obtain ⟨hout, hin⟩ := hcol
  have hmemgt : ∀ i, i ∈ (List.finRange n).filter (j < ·) ↔ j < i := fun i => by simp
  -- entries outside column `j`, and column `j` above the diagonal, are unchanged
  have hrowj : S' j = Function.update (S j) j d := by
    rw [hout j (by simp), hS₁, updateRow_self]
  have hother : ∀ i k, k ≠ j → S' i k = S i k := by
    intro i k hk
    by_cases hi : j < i
    · obtain ⟨x, -, hr⟩ := hin i ((hmemgt i).2 hi)
      rw [hr, Function.update_of_ne hk, hS₁, updateRow_ne (ne_of_gt hi)]
    · rw [hout i (fun h => hi ((hmemgt i).1 h))]
      by_cases hij : i = j
      · subst hij
        rw [hS₁, updateRow_self, Function.update_of_ne hk]
      · rw [hS₁, updateRow_ne hij]
  refine ⟨fun i k hk => ?_, fun j' hj' => ?_⟩
  · have hkj : k ≠ j := fun h => by rw [h] at hk; simp at hk
    rw [hother i k hkj]
    exact hA i k (by omega)
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | hj'
    · -- an earlier column: unchanged
      refine (hdone j' hj').congr fp fun i k hk => hother i k ?_
      intro h
      rw [h] at hk
      exact absurd (Fin.lt_def.1 (lt_of_le_of_lt hk (Fin.lt_def.2 hj'))) (lt_irrefl _)
    · -- the column just computed
      have hjj : j' = j := Fin.ext hj'
      subst hjj
      have hdiag : S' j' j' = d := by rw [hrowj, Function.update_self]
      have hSjj : S j' j' = A j' j' := hA j' j' le_rfl
      refine ⟨v, fun k hk => ?_, ?_, fun i hi => ?_⟩
      · have hk' := ne_of_lt (mem_below.1 hk)
        rw [hother j' k hk', hother k k hk']
        exact hv' k hk
      · rw [hdiag, ← hSjj]
        exact hd'.congr (fun k hk => hother j' k (ne_of_lt (mem_below.1 hk))) fun _ _ => rfl
      · obtain ⟨l, hx, hr⟩ := hin i ((hmemgt i).2 hi)
        simp only [SetM.mem_run_bind, RoundingModel.mem_run_round] at hx
        obtain ⟨t, ht, hl⟩ := hx
        have hS₁i : S₁ i = S i := by rw [hS₁, updateRow_ne (ne_of_gt hi)]
        rw [hS₁i] at ht hr
        refine ⟨t, ?_, ?_⟩
        · have ht' := (mem_run_runningDiff_iff (nodup_below j')).1 ht
          rw [hA i j' le_rfl] at ht'
          exact ht'.congr (fun k hk => hother i k (ne_of_lt (mem_below.1 hk))) fun _ _ => rfl
        · rw [hdiag, hr, Function.update_self]
          exact hl

/-- **Algorithm 4.1.1** of [golub2013matrix], rounding bridge. Let $A \in \mathbb{R}^{n \times n}$
be arbitrary. For every packed matrix $F$ that Algorithm 4.1.1 can compute in the rounding model
`fp`, the factors $\hat L$ and $\hat D$ stored in $F$ form a computed $LDL^T$ factorization of
$A$ in the operation order of the algorithm: $\hat L$ is unit lower triangular, $\hat D$ is
diagonal, each pivot $\hat d_j$ is a running difference of $a_{jj}$ and rounded products
$\hat\ell_{jk} v_k$ with $v_k = \mathrm{fl}(\hat\ell_{jk} \hat d_k)$, $k < j$, and each
$\hat\ell_{ij}$, $j < i$, is a rounding of $t / \hat d_j$ for a running difference $t$ of
$a_{ij}$ and rounded products $\hat\ell_{ik} v_k$, $k < j$.

The relation is `FloatingPoint.RoundsLDL fp A (GolubVanLoan.Chapter03.packedL F)
(Matrix.diagonal F.diag)`. It needs no hypothesis on $A$. -/
theorem algorithm_4_1_1_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ F ∈ (algorithm_4_1_1 fp.round A).run,
      RoundsLDL fp A (Chapter03.packedL F) (diagonal F.diag) := by
  have hfin := SetM.forall_mem_run_foldlM_finRange (Inv fp A)
    ⟨fun _ _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    (fun j S hS S' hS' => inv_step fp A j S hS S' hS')
  intro F hF
  obtain ⟨-, hdone⟩ := hfin F hF
  have hL : ∀ i k, k < i → Chapter03.packedL F i k = F i k := fun i k hki =>
    Chapter03.packedL_apply_of_lt F hki
  choose v hv hd hcol using fun j : Fin n => hdone j j.isLt
  refine ⟨fun i k hik => ?_, fun i => ?_, isDiag_diagonal _, ⟨of fun j k => v j k, ?_, ?_, ?_⟩⟩
  · exact Chapter03.packedL_apply_of_lt' F hik
  · exact Chapter03.packedL_apply_self F i
  · intro j k hkj
    rw [hL j k hkj, diagonal_apply_eq, diag_apply]
    exact hv j k (mem_below.2 hkj)
  · intro j
    obtain ⟨p, hp, hs⟩ := hd j
    refine ⟨below j, nodup_below j, fun k => mem_below, p, fun k hk => ?_, ?_⟩
    · rw [hL j k (mem_below.1 hk)]
      exact hp k hk
    · rwa [diagonal_apply_eq, diag_apply]
  · intro i j hji
    obtain ⟨t, ⟨p, hp, hs⟩, hl⟩ := hcol j i hji
    refine ⟨below j, t, nodup_below j, fun k => mem_below, ⟨p, fun k hk => ?_, hs⟩, ?_⟩
    · rw [hL i k (lt_trans (mem_below.1 hk) hji)]
      exact hp k hk
    · rw [diagonal_apply_eq, diag_apply, hL i j hji]
      exact hl

end Bridge

/-- The exact run of Algorithm 4.1.1 is one of its runs in the exact rounding model. -/
private theorem algorithm_4_1_1_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_1_1 pure A) ∈ (algorithm_4_1_1 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_4_1_1, runningDiff, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- In the exact model, a computed $LDL^T$ factorization reproduces $A$ on and below the diagonal
wherever the pivot of the column is used as a divisor. -/
private theorem mul_mul_transpose_apply_of_roundsLDL_exact {A L D : Matrix (Fin n) (Fin n) ℝ}
    (h : RoundsLDL (RoundingModel.exact ℝ) A L D) {i k : Fin n} (hki : k ≤ i)
    (hd : k < i → D k k ≠ 0) : (L * D * Lᵀ) i k = A i k := by
  obtain ⟨V, hV, hpiv, hcol⟩ := h.exists_rounds
  have hV' : ∀ j k, k < j → V j k = L j k * D k k := fun j k hkj => hV j k hkj
  rw [mul_mul_transpose_apply_of_isDiag h.lower_apply_eq_zero h.isDiag, min_eq_right hki,
    sum_filter_le_eq_add]
  have hsum : ∀ j, ∀ o : List (Fin n), o.Nodup → (∀ t, t ∈ o ↔ t < k) → ∀ p : Fin n → ℝ,
      (∀ t ∈ o, (RoundingModel.exact ℝ).Rounds (L j t * V k t) (p t)) →
      ∑ t ∈ o.toFinset, p t = ∑ t ∈ univ.filter (· < k), L j t * D t t * L k t := by
    intro j o hnd ho p hp
    have hset : o.toFinset = univ.filter (· < k) := by ext t; simp [ho]
    rw [hset]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htk := (mem_filter.1 ht).2
    rw [hp t ((ho t).2 htk), hV' k t htk]
    ring
  rcases eq_or_lt_of_le hki with rfl | hki'
  · obtain ⟨o, hnd, ho, p, hp, hs⟩ := hpiv k
    rw [(roundsSumFrom_exact_map_neg_iff hnd).1 hs, hsum k o hnd ho p hp, h.lower_diag, mul_one,
      one_mul]
    ring
  · obtain ⟨o, t, hnd, ho, ⟨p, hp, hs⟩, hl⟩ := hcol i k hki'
    rw [RoundingModel.exact_rounds_iff] at hl
    rw [hl, (roundsSumFrom_exact_map_neg_iff hnd).1 hs, hsum i o hnd ho p hp, h.lower_diag,
      mul_one, div_mul_cancel₀ _ (hd hki')]
    ring

/-- In the exact model, the pivots used as divisors in a computed $LDL^T$ factorization of a
symmetric matrix with nonsingular leading principal submatrices are nonzero. -/
private theorem roundsLDL_exact_diag_ne_zero {A L D : Matrix (Fin n) (Fin n) ℝ}
    (h : RoundsLDL (RoundingModel.exact ℝ) A L D) (hs : A.IsSymm)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    ∀ j i : Fin n, j < i → D j j ≠ 0 := by
  have hLu : L.IsUnitLowerTriangular :=
    ⟨fun i k hik => h.lower_apply_eq_zero i k (OrderDual.toDual_lt_toDual.1 hik), h.lower_diag⟩
  have hB : IsLDM (L * D * Lᵀ) L D L := ⟨hLu, h.isDiag, hLu, rfl⟩
  have hsymm : (L * D * Lᵀ).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, h.isDiag.isSymm.eq,
      Matrix.mul_assoc]
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  intro i hji
  have hk : j.val + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt hji) i.isLt
  have key : ∀ a b : Fin n, b ≤ a → a.val < j.val + 1 → (L * D * Lᵀ) a b = A a b :=
    fun a b hba ha => mul_mul_transpose_apply_of_roundsLDL_exact h hba fun hba' =>
      ih b (Fin.lt_def.2 (by have := Fin.lt_def.1 hba'; omega)) a hba'
  have hsub : A.strictLeadingPrincipalSubmatrix ⟨j.val + 1, hk⟩ =
      (L * D * Lᵀ).strictLeadingPrincipalSubmatrix ⟨j.val + 1, hk⟩ := by
    ext a b
    have ha : a.1.val < j.val + 1 := Fin.lt_def.1 a.2
    have hb : b.1.val < j.val + 1 := Fin.lt_def.1 b.2
    simp only [strictLeadingPrincipalSubmatrix, toBlock_apply]
    rcases le_total b.1 a.1 with hba | hab
    · exact (key a b hba ha).symm
    · rw [hsymm.apply b.1 a.1, key b a hab hb]
      exact hs.apply b.1 a.1
  have hdet := isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1 (hA ⟨j.val + 1, hk⟩))
  rw [hsub, hB.isLU.det_strictLeadingPrincipalSubmatrix, Finset.prod_ne_zero_iff] at hdet
  have hj := hdet j (mem_filter.2 ⟨mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩)
  have hDL : (D * Lᵀ) j j = D j j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j (fun t _ htj => by rw [h.isDiag htj.symm,
      zero_mul]) (by simp), transpose_apply, h.lower_diag, mul_one]
  rwa [hDL] at hj

/-- **Algorithm 4.1.1** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, with $A(1{:}k, 1{:}k)$ nonsingular for $k = 1{:}n-1$. Let $F$ be the output of
Algorithm 4.1.1 on $A$ in exact arithmetic, let $L$ be the unit lower triangular matrix stored
strictly below the diagonal of $F$, and let $D$ be the diagonal of $F$. Then
$$A = LDL^T,$$
the factorization of Theorem 4.1.3.

**Reading.** The source assumes that $A$ has an LU factorization. The theorem assumes instead
the hypothesis of Theorem 4.1.3. This is stronger, since a singular matrix may have an LU
factorization, and it is the hypothesis under which the derivation of the algorithm in the
source divides by the pivots $d_j$, $j < n$.

The factors are `GolubVanLoan.Chapter03.packedL F` and `Matrix.diagonal F.diag`. The proof reads
the bridge `GolubVanLoan.Chapter04.algorithm_4_1_1_rounds` at the exact model, once the pivots
used as divisors are known to be nonzero; by induction, the leading block of order $j + 1$ of
$LDL^T$ is that of $A$, whose determinant is $d_1 \cdots d_{j+1}$. -/
theorem algorithm_4_1_1_spec {A : Matrix (Fin n) (Fin n) ℝ} (hs : A.IsSymm)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    IsLDM A (Chapter03.packedL (Id.run (algorithm_4_1_1 pure A)))
      (diagonal (Id.run (algorithm_4_1_1 pure A)).diag)
      (Chapter03.packedL (Id.run (algorithm_4_1_1 pure A))) := by
  have h := algorithm_4_1_1_rounds (RoundingModel.exact ℝ) A _ (algorithm_4_1_1_mem_exact A)
  have hpiv := roundsLDL_exact_diag_ne_zero h hs hA
  have hLu : (Chapter03.packedL (Id.run (algorithm_4_1_1 pure A))).IsUnitLowerTriangular :=
    ⟨fun i k hik => h.lower_apply_eq_zero i k (OrderDual.toDual_lt_toDual.1 hik), h.lower_diag⟩
  refine ⟨hLu, h.isDiag, hLu, ?_⟩
  have hsymm : (Chapter03.packedL (Id.run (algorithm_4_1_1 pure A)) *
      diagonal (Id.run (algorithm_4_1_1 pure A)).diag *
      (Chapter03.packedL (Id.run (algorithm_4_1_1 pure A)))ᵀ).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, h.isDiag.isSymm.eq,
      Matrix.mul_assoc]
  ext i k
  rcases le_total k i with hki | hik
  · exact mul_mul_transpose_apply_of_roundsLDL_exact h hki fun hki' => hpiv k i hki'
  · rw [hsymm.apply k i,
      mul_mul_transpose_apply_of_roundsLDL_exact h hik fun hik' => hpiv i k hik']
    exact (hs.apply k i).symm

/-! ### (4.1.4): the backward error of the $LDL^T$ solve -/

section Solve

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Section 4.1.2** of [golub2013matrix], the solve stage of (4.1.4) with a packed $LDL^T$ factor
$F$, the output of Algorithm 4.1.1: solve $Lz = b$, then $Dy = z$, then $L^T x = y$, where $L$
is the unit lower triangular matrix stored strictly below the diagonal of $F$ and $D$ is the
diagonal of $F$.

The system $Lz = b$ is solved by Algorithm 3.1.3, the diagonal system by the rounded quotients
$y_i = \mathrm{fl}(z_i / f_{ii})$, and $L^T x = y$ by Algorithm 3.1.4. The factor $L$ is
`GolubVanLoan.Chapter03.packedL F`. -/
noncomputable def solveLDLT (F : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : M (Fin n → ℝ) := do
  let z ← Chapter03.algorithm_3_1_3 rnd (Chapter03.packedL F) b
  let y ← (List.finRange n).foldlM (fun (y : Fin n → ℝ) (i : Fin n) => do
    let yi ← rnd (y i / F i i)
    pure (Function.update y i yi)) z
  Chapter03.algorithm_3_1_4 rnd (Chapter03.packedL F)ᵀ y

end Solve

/-- **Equation (4.1.4)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric and
$b \in \mathbb{R}^n$, and let the unit roundoff satisfy $(3n + 2)u < 1$. Let $F$ be a packed
matrix computed by Algorithm 4.1.1 from $A$ with every diagonal entry $f_{jj}$ nonzero, and let
$\hat L$ and $\hat D$ be the unit lower triangular and the diagonal factors stored in $F$. Then
every solution $\hat x$ computed from $F$ and $b$ by the three-step solve
`GolubVanLoan.Chapter04.solveLDLT` satisfies $(A + E)\hat x = b$ for some
$E \in \mathbb{R}^{n \times n}$ with
$$|E| \le \gamma_{3n+2} |\hat L| |\hat D| |\hat L^T|$$
entrywise.

The source states that the solution computed via Algorithm 4.1.1 and the triangular solvers of
§3.1 satisfies $(A + E)\hat x = b$ with $|E| \le nu(2|A| + 4|\hat L||\hat D||\hat L^T|) +
O(u^2)$. The rigorous bound implies it to first order for $n \ge 2$, since
$\gamma_{3n+2} = (3n + 2)u + O(u^2)$ and $3n + 2 \le 4n$. The factors are
`GolubVanLoan.Chapter03.packedL F` and `Matrix.diagonal F.diag`. -/
theorem equation_4_1_4 {fp : RoundingModel ℝ} (hn : ((3 * n + 2 : ℕ) : ℝ) * fp.u < 1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (b : Fin n → ℝ) :
    ∀ F ∈ (algorithm_4_1_1 fp.round A).run, (∀ j, F j j ≠ 0) →
      ∀ x ∈ (solveLDLT fp.round F b).run,
        ∃ E : Matrix (Fin n) (Fin n) ℝ, (A + E) *ᵥ x = b ∧
          E.abs ≤ₑ gamma fp.u (3 * n + 2) • ((Chapter03.packedL F).abs *
            (diagonal F.diag).abs * (Chapter03.packedL F)ᵀ.abs) := by
  intro F hF hd x hx
  have hu : fp.u < 1 := by
    have h1 : (1 : ℝ) * fp.u ≤ ((3 * n + 2 : ℕ) : ℝ) * fp.u :=
      mul_le_mul_of_nonneg_right (by norm_cast; omega) fp.u_nonneg
    linarith
  simp only [solveLDLT, SetM.mem_run_bind] at hx
  obtain ⟨z, hz, y, hy, hx⟩ := hx
  have hy' := (SetM.mem_run_foldlM_update_of_nodup (fun (i : Fin n) (c : ℝ) _ =>
    fp.round (c / F i i)) (List.finRange n) (List.nodup_finRange n)
    (fun _ _ _ _ _ _ => rfl) z y).1 hy
  have hyr : ∀ i, fp.Rounds (z i / (diagonal F.diag) i i) (y i) := fun i => by
    rw [diagonal_apply_eq, diag_apply]
    exact RoundingModel.mem_run_round.1 (hy'.2 i (List.mem_finRange i))
  obtain ⟨E, hE, hAx⟩ := exists_roundsLDL_solve_eq hu (by simpa using hn) hA
    (algorithm_4_1_1_rounds fp A F hF) (fun j => by rw [diagonal_apply_eq, diag_apply]; exact hd j)
    (Chapter03.algorithm_3_1_3_rounds fp _ b z hz) hyr
    (Chapter03.algorithm_3_1_4_rounds fp _ y x hx)
  exact ⟨E, hAx, by simpa using hE⟩

end GolubVanLoan.Chapter04
