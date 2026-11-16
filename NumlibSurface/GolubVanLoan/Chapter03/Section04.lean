/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter03.Section03

/-!
# Golub and Van Loan, Section 3.4: Pivoting

This module formalizes §3.4 of [golub2013matrix], Gaussian elimination with row and column
interchanges. An interchange permutation $\Pi$ is the identity with two rows swapped, and a pivot
vector $\mathrm{piv}$ encodes a product $P = \Pi_{n-1} \cdots \Pi_1$ of interchanges. Partial
pivoting applies $A \leftarrow M_k \Pi_k A$ at step $k$, where $\Pi_k$ brings the entry of largest
modulus in column $k$ at or below the diagonal to the pivot position and $M_k$ is a Gauss
transformation. It computes $PA = LU$ with $|\ell_{ij}| \le 1$ for every $A$ ((3.4.1)–(3.4.5)). The
module defines the outer product and the gaxpy LU with partial pivoting (Algorithms 3.4.1 and
3.4.2), each with a rounding bridge into `FloatingPoint.RoundsLU` for $PA$ and an exact
specification, and the solves that follow them. It proves the componentwise backward error (3.4.6)
of the solve and its normwise forms (3.4.7) and (3.4.9), and studies the growth factor $\rho$
(3.4.8), which is at most $2^{n-1}$. On an example that needs no interchange, the entries grow by
the factor $2^{n-1}$ relative to $\max_{i,j} |a_{ij}|$.

Complete pivoting (Algorithm 3.4.3) computes $PAQ^T = LU$ with interchanges of rows and columns. The
module proves Wilkinson's bound (3.4.10) on the entries of the stages, and that complete pivoting
reveals the rank: after $r = \operatorname{rank} A$ steps the trailing block vanishes. Rook pivoting
(§3.4.7) chooses an entry that is maximal in its row and in its column; the module proves that the
rook scan terminates and computes $PAQ = LU$. The module also treats underdetermined systems
(3.4.11) and the solves with several right-hand sides (3.4.12) and with a power of $A$ (3.4.13). The
exact statements specialize `Numlib.LinearAlgebra.Matrix.LU.Pivoting`, and the rounding statements
specialize `Numlib.FloatingPoint.LU`.

## Main definitions

* §3.4.1, `GolubVanLoan.Chapter03.interchange`: the interchange permutation matrix $\Pi$ of two
  indices.
* §3.4.1, `GolubVanLoan.Chapter03.pivPerm`: the permutation $P = \Pi_{n-1} \cdots \Pi_1$ encoded by
  a pivot vector.
* §3.4.1, `GolubVanLoan.Chapter03.applyPiv`: the loop that overwrites $x$ with $Px$.
* (3.4.1), `GolubVanLoan.Chapter03.partialPivotStage`: the matrix $M_k \Pi_k \cdots M_1 \Pi_1 A$
  after $k$ steps of partial pivoting.
* §3.4.3, `GolubVanLoan.Chapter03.pivotedGaussTransformation`: the matrix $\tilde M_k = P' M_k P'^T$
  of (3.4.5).
* Algorithm 3.4.1, `GolubVanLoan.Chapter03.algorithm_3_4_1`: outer product LU with partial pivoting.
* §3.4.3, `GolubVanLoan.Chapter03.solvePLU` and `GolubVanLoan.Chapter03.solveGEPP`: the solves
  $Ly = Pb$, $Ux = y$ after Algorithm 3.4.1.
* Algorithm 3.4.2, `GolubVanLoan.Chapter03.algorithm_3_4_2`: gaxpy LU with partial pivoting.
* (3.4.8), `GolubVanLoan.Chapter03.growthFactorStages`: the growth factor $\rho$ of partial
  pivoting.
* §3.4.5, `GolubVanLoan.Chapter03.growthExample`: the matrix with growth factor $2^{n-1}$.
* Algorithm 3.4.3, `GolubVanLoan.Chapter03.algorithm_3_4_3`: outer product LU with complete
  pivoting.
* §3.4.6, `GolubVanLoan.Chapter03.solvePLUQ` and `GolubVanLoan.Chapter03.solveGECP`: the solves
  $Lz = Pb$, $Uy = z$, $x = Q^T y$ after Algorithm 3.4.3.
* §3.4.7, `GolubVanLoan.Chapter03.rookPivotSearch` and `GolubVanLoan.Chapter03.rookPivot`: the rook
  scan and the rook pivoting strategy.
* (3.4.12), `GolubVanLoan.Chapter03.solveMultipleRHS`: the solve of $AX = B$ column by column.
* (3.4.13), `GolubVanLoan.Chapter03.solvePowerSystem`: the solve of $A^k x = b$ without forming
  $A^k$.

## Main results

* §3.4.1, `GolubVanLoan.Chapter03.applyPiv_eq`: the forward loop computes $Px$ and the reverse loop
  computes $P^T x$.
* (3.4.1)–(3.4.2), `GolubVanLoan.Chapter03.equation_3_4_2`: each step of partial pivoting is
  $A \leftarrow M_k \Pi_k A$, and the last stage is upper triangular.
* (3.4.3), `GolubVanLoan.Chapter03.equation_3_4_3`: partial pivoting computes $PA = LU$ with
  $|\ell_{ij}| \le 1$ for every $A$.
* (3.4.4), `GolubVanLoan.Chapter03.equation_3_4_4`: $\tilde M_{n-1} \cdots \tilde M_1 PA = U$, where
  $\tilde M_k$ is the Gauss transformation of elimination without pivoting on $PA$.
* (3.4.5), `GolubVanLoan.Chapter03.equation_3_4_5`: $P' M_k P'^T$ is a Gauss transformation with the
  permuted Gauss vector.
* Algorithm 3.4.1, `GolubVanLoan.Chapter03.algorithm_3_4_1_rounds`,
  `GolubVanLoan.Chapter03.algorithm_3_4_1_spec` and
  `GolubVanLoan.Chapter03.algorithm_3_4_1_eq_gemPivotStage`: every run computes LU factors of $PA$
  in the sense of `FloatingPoint.RoundsLU`, the exact run computes $PA = LU$ with
  $|\ell_{ij}| \le 1$, and the exact run is the backbone's partial pivoting recurrence.
* §3.4.3, `GolubVanLoan.Chapter03.solveGEPP_spec`: for nonsingular $A$ the exact solve gives
  $Ax = b$.
* Algorithm 3.4.2, `GolubVanLoan.Chapter03.algorithm_3_4_2_rounds` and
  `GolubVanLoan.Chapter03.algorithm_3_4_2_spec`: the same for the gaxpy version.
* (3.4.6), `GolubVanLoan.Chapter03.equation_3_4_6` and
  `GolubVanLoan.Chapter03.equation_3_4_6_gaxpy`: the computed solution satisfies $(A + E)\hat x = b$
  with $|E| \le \gamma_{3n} P^T |\hat L| |\hat U|$.
* (3.4.7), `GolubVanLoan.Chapter03.equation_3_4_7` and
  `GolubVanLoan.Chapter03.equation_3_4_7_gaxpy`: $\|E\|_\infty \le n(1 + u)\gamma_{3n} \|\hat
  U\|_\infty$.
* (3.4.8), `GolubVanLoan.Chapter03.growthFactorStages_eq`: $\rho$ in terms of the backbone's growth
  factor of $PA$.
* (3.4.9), `GolubVanLoan.Chapter03.equation_3_4_9` and
  `GolubVanLoan.Chapter03.equation_3_4_9_gaxpy`: if $|\hat u_{ij}| \le \rho \|A\|_\infty$, then
  $\|E\|_\infty \le n^2 (1 + u)\gamma_{3n} \rho \|A\|_\infty$.
* §3.4.5, `GolubVanLoan.Chapter03.growthFactor_le_two_pow`: the growth factor of partial pivoting is
  at most $2^{n-1}$.
* §3.4.5, `GolubVanLoan.Chapter03.growthExample_isLU` and
  `GolubVanLoan.Chapter03.growthExample_noInterchange`: the example matrix has $u_{nn} = 2^{n-1}$,
  needs no interchange, and has the growth factor `Matrix.growthFactor` equal to $2^{n-1}$.
* Algorithm 3.4.3, `GolubVanLoan.Chapter03.algorithm_3_4_3_spec`: the exact run computes
  $PAQ^T = LU$ with $|\ell_{ij}| \le 1$ and $|u_{ij}| \le |u_{ii}|$.
* §3.4.6, `GolubVanLoan.Chapter03.solveGECP_spec`: for nonsingular $A$ the exact solve with complete
  pivoting gives $Ax = b$.
* (3.4.10), `GolubVanLoan.Chapter03.equation_3_4_10`: Wilkinson's bound on the entries of the stages
  of complete pivoting.
* §3.4.6, `GolubVanLoan.Chapter03.completePivoting_rank` and
  `GolubVanLoan.Chapter03.completePivoting_rank_factorization`: complete pivoting reveals the rank.
* §3.4.7, `GolubVanLoan.Chapter03.rookPivotSearch_spec`,
  `GolubVanLoan.Chapter03.isRookPivot_rookPivot` and `GolubVanLoan.Chapter03.rookPivoting_isLU`: the
  rook scan terminates at a rook pivot, and rook pivoting computes $PAQ = LU$ with
  $|\ell_{ij}| \le 1$ and $|u_{ij}| \le |u_{ii}|$.
* (3.4.11), `GolubVanLoan.Chapter03.equation_3_4_11`: a matrix of full row rank has a factorization
  $PAQ^T = L[U_1 \mid U_2]$ with $U_1$ nonsingular.
* §3.4.8, `GolubVanLoan.Chapter03.underdetermined_solve`: this factorization gives a solution of
  $Ax = b$ for every choice of $z_2$.
* (3.4.12), `GolubVanLoan.Chapter03.equation_3_4_12`: the multiple right-hand side solve gives
  $AX = B$, and $A^{-1}$ for $B = I$.
* (3.4.13), `GolubVanLoan.Chapter03.equation_3_4_13`: the power solve gives $A^k x = b$.

## Conventions

* Indices are 0-based. In this section the source's $A^{(k)}$ is the matrix after $k$ steps,
  `GolubVanLoan.Chapter03.partialPivotStage A k`; in (3.2.3) it was the matrix after $k - 1$ steps.
* A row permutation $\sigma$ acts as `A.submatrix σ id = σ.permMatrix ℝ * A`, so that
  $(PA)_{ij} = a_{\sigma(i) j}$. The source's $P = \Pi_{n-1} \cdots \Pi_1$ encoded by $\mathrm{piv}$
  is `(GolubVanLoan.Chapter03.pivPerm piv).permMatrix ℝ`. The pivot vector has $n$ entries; the last
  step $k = n$ is a trivial interchange.
* The $\infty$-norm of a matrix is the scoped `Matrix.Norms.Operator` norm.
* The source states first-order bounds. The theorems state rigorous bounds with
  $\gamma_k = ku/(1 - ku)$, which imply the printed bounds to first order. The relational rounding
  model bounds a computed multiplier of partial pivoting by $1 + u$, not by $1$, so
  $\|\hat L\|_\infty \le n(1 + u)$ replaces $\|\hat L\|_\infty \le n$.
* A computed quantity is an element of the run set of its program in the rounding model `fp`, with
  the hook `fp.round`. The hypotheses of a rounding theorem are about the values that the programs
  return, such as nonzero returned pivots.

## Implementation notes

* The pivot search of Algorithm 3.4.1 is the backbone's `Matrix.partialPivotRow`: the first row at
  or below $k$ that maximizes $|a_{ik}|$. It compares exact absolute values of the entries that the
  program holds, so it is a step of the program without rounding. The guard `if A(k,k) ≠ 0` of the
  source is kept.
* The rounding bridge of Algorithm 3.4.1 follows the invariant `GolubVanLoan.Chapter03.LUStageInv`
  of Algorithm 3.2.1 for $A$ with its rows permuted by the interchanges so far. An interchange at
  step $k$ permutes only rows at or after $k$, and it moves the finished multipliers of those rows
  together with their trailing entries (`GolubVanLoan.Chapter03.pivStageInv_submatrix`). In the
  exact model a zero pivot comes with a zero column, and the skipped update is then an update; so
  the exact specification holds for every $A$, and it is read off the same invariant.
* The search of complete pivoting is `Matrix.completePivotEntry`, which makes no canonical choice
  among the maximizing entries. Algorithm 3.4.3 has an exact specification and no rounding bridge.
* The `while` loop of the rook scan is a loop over a fuel parameter with a flag that records the
  exit.

## Deviations from the source

* **(3.4.8)** (correction). The source defines the growth factor on the computed stages
  $\hat A^{(k)}$. The definition uses the exact stages, since only these admit bounds. See
  `GolubVanLoan.Chapter03.growthFactorStages`.
* **(3.4.9)** (reading). The source's $\rho$ bounds the computed $\hat U$ through
  $|\hat u_{ij}| \le \rho \|A\|_\infty$. The theorem takes this bound as a hypothesis, with any
  $\rho \ge 0$. See `GolubVanLoan.Chapter03.equation_3_4_9`.
* **(3.4.10)** (correction). The source prints the bound with $k$ in place of $k + 1$, which is
  false for $k = 1$ when $A^{(k)}$ is the matrix after $k$ steps. See
  `GolubVanLoan.Chapter03.equation_3_4_10`.

## Not formalized

* **The average-case growth $n^{2/3}$ and the statement "$\rho = 10$".** They are heuristics with no
  rigorous reading.
* **The reliability of rook pivoting.** The claim that rook pivoting has the same level of
  reliability as complete pivoting is a heuristic.
* **The backward stability of complete pivoting (§3.4.6, §3.4.10).** Algorithm 3.4.3 has an exact
  specification only.
* **Example 3 of the "LU mentality" and the vocabulary of §3.4.10.**
* **The algorithm of P3.4.5 behind (3.4.11).** The factorization (3.4.11) is proved from the
  specification.
* **Operation counts.**
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter03

/-! ### Interchange permutations and the `piv` encoding (§3.4.1) -/

section Piv

variable {n : ℕ}

/-- **Section 3.4.1** of [golub2013matrix], the interchange permutation. For indices $k$ and $l$,
the **interchange permutation** $\Pi$ is the identity with rows $k$ and $l$ swapped. Then
$\Pi A$ is $A$ with rows $k$ and $l$ interchanged, and $A\Pi$ is $A$ with columns $k$ and $l$
interchanged.

The matrix is `(Equiv.swap k l).permMatrix ℝ`. -/
noncomputable def interchange (k l : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (Equiv.swap k l).permMatrix ℝ

/-- The permutation of the first $k$ interchanges encoded by $\mathrm{piv}$: $\operatorname{swap}(0,
\mathrm{piv}(0)) \cdots \operatorname{swap}(k-1, \mathrm{piv}(k-1))$. Steps $j \ge n$ add no
interchange. -/
def pivPermUpTo (piv : Fin n → Fin n) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | k + 1 =>
    if h : k < n then pivPermUpTo piv k * Equiv.swap ⟨k, h⟩ (piv ⟨k, h⟩) else pivPermUpTo piv k

/-- **Section 3.4.1** of [golub2013matrix], the permutation encoded by a pivot vector. If
$P = \Pi_m \cdots \Pi_1$ and each $\Pi_k$ is the identity with rows $k$ and $\mathrm{piv}(k)$
interchanged, then $\mathrm{piv}$ **encodes** $P$. For $\mathrm{piv} : \{0, \dots, n-1\} \to
\{0, \dots, n-1\}$, the permutation is
$$\operatorname{swap}(0, \mathrm{piv}(0)) \cdots \operatorname{swap}(n-1, \mathrm{piv}(n-1)),$$
and its permutation matrix is the product of the interchange matrices in the reverse order.

`Matrix.permMatrix_mul` reverses the order of a product, so `(pivPerm piv).permMatrix ℝ` is
$\Pi_{n-1} \cdots \Pi_0$ in 0-based indices. -/
def pivPerm (piv : Fin n → Fin n) : Equiv.Perm (Fin n) :=
  pivPermUpTo piv n

/-- The permutation of the first $k$ interchanges depends only on the first $k$ entries of
$\mathrm{piv}$. -/
theorem pivPermUpTo_congr {piv piv' : Fin n → Fin n} {k : ℕ}
    (h : ∀ j : Fin n, (j : ℕ) < k → piv j = piv' j) : pivPermUpTo piv k = pivPermUpTo piv' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pivPermUpTo]
    split_ifs with hk
    · rw [ih fun j hj => h j (by omega), h ⟨k, hk⟩ (by simp)]
    · exact ih fun j hj => h j (by omega)

/-- The permutation of the first $k + 1$ interchanges is that of the first $k$, followed by
$\operatorname{swap}(k, \mathrm{piv}(k))$. -/
theorem pivPermUpTo_succ {piv : Fin n → Fin n} (k : Fin n) :
    pivPermUpTo piv (k + 1) = pivPermUpTo piv k * Equiv.swap k (piv k) := by
  simp [pivPermUpTo, k.2]

/-- **Section 3.4.1** of [golub2013matrix], the loop `for k = 1:m, x(k) ↔ x(piv(k))`, which
overwrites $x$ with $Px$. -/
def applyPiv (piv : Fin n → Fin n) (x : Fin n → ℝ) : Fin n → ℝ :=
  (List.finRange n).foldl (fun x k => x ∘ Equiv.swap k (piv k)) x

/-- **Section 3.4.1** of [golub2013matrix], the loop `for k = m:-1:1, x(k) ↔ x(piv(k))`, which
overwrites $x$ with $P^T x$. -/
def applyPivRev (piv : Fin n → Fin n) (x : Fin n → ℝ) : Fin n → ℝ :=
  (List.finRange n).reverse.foldl (fun x k => x ∘ Equiv.swap k (piv k)) x

/-- A fold over `List.finRange n` is a fold over `List.range n`. -/
private theorem foldl_finRange_eq_foldl_range {β : Type*} (f : β → Fin n → β) (b : β) :
    (List.finRange n).foldl f b =
      (List.range n).foldl (fun b k => if h : k < n then f b ⟨k, h⟩ else b) b := by
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]
  congr 1
  funext b k
  simp [k.2]

/-- A right fold over `List.finRange n` is a right fold over `List.range n`. -/
private theorem foldr_finRange_eq_foldr_range {β : Type*} (f : Fin n → β → β) (b : β) :
    (List.finRange n).foldr f b =
      (List.range n).foldr (fun k b => if h : k < n then f ⟨k, h⟩ b else b) b := by
  rw [← List.map_coe_finRange_eq_range, List.foldr_map]
  congr 1
  funext k b
  simp [k.2]

/-- **Section 3.4.1** of [golub2013matrix]. Let $\mathrm{piv}$ encode $P$, and let
$x \in \mathbb{R}^n$. Then the forward loop overwrites $x$ with $Px$, and the reverse loop
overwrites $x$ with
$$P^T x = \Pi_1 \cdots \Pi_m x.$$

The reverse loop computes $P^T x$ because each $\Pi_k$ is symmetric. The two loops are
`GolubVanLoan.Chapter03.applyPiv` and `GolubVanLoan.Chapter03.applyPivRev`. -/
theorem applyPiv_eq (piv : Fin n → Fin n) (x : Fin n → ℝ) :
    applyPiv piv x = (pivPerm piv).permMatrix ℝ *ᵥ x ∧
      applyPivRev piv x = ((pivPerm piv).permMatrix ℝ)ᵀ *ᵥ x := by
  have hfwd : ∀ k ≤ n, ∀ y : Fin n → ℝ, (List.range k).foldl
      (fun y k => if h : k < n then y ∘ Equiv.swap ⟨k, h⟩ (piv ⟨k, h⟩) else y) y =
      y ∘ pivPermUpTo piv k := by
    intro k hk
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      simp only [show k < n by omega, ↓reduceDIte, pivPermUpTo, Equiv.Perm.coe_mul]
      rfl
  have hrev : ∀ k ≤ n, ∀ y : Fin n → ℝ, (List.range k).foldr
      (fun k y => if h : k < n then y ∘ Equiv.swap ⟨k, h⟩ (piv ⟨k, h⟩) else y) y =
      y ∘ ⇑(pivPermUpTo piv k)⁻¹ := by
    intro k hk
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih (by omega)]
      simp only [show k < n by omega, ↓reduceDIte, pivPermUpTo, _root_.mul_inv_rev,
        Equiv.swap_inv, Equiv.Perm.coe_mul]
      rfl
  refine ⟨?_, ?_⟩
  · rw [applyPiv, foldl_finRange_eq_foldl_range, hfwd n le_rfl, permMatrix_mulVec]
    rfl
  · rw [applyPivRev, List.foldl_reverse, foldr_finRange_eq_foldr_range, hrev n le_rfl,
      mulVec_transpose, vecMul_permMatrix]
    rfl

end Piv

/-! ### Partial pivoting (§3.4.2–3.4.3) -/

section Partial

variable {n : ℕ}

/-- **Equation (3.4.1)** of [golub2013matrix], partial pivoting as a sequence of matrices. For
$A \in \mathbb{R}^{n \times n}$, the matrix after $k$ steps of Gaussian elimination with partial
pivoting is
$$A^{(k)} = M_k \Pi_k \cdots M_1 \Pi_1 A,$$
computed in exact arithmetic.

It is the backbone's pivoted stage `(Matrix.gemPivotStage A Matrix.partialPivotRow k).1`. For
$k \ge n$ it is the last stage. -/
noncomputable abbrev partialPivotStage (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (gemPivotStage A partialPivotRow k).1

/-- **Equations (3.4.1)–(3.4.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and let
$A^{(k)}$ be the matrix after $k$ steps of partial pivoting. For every step $k$, let $\Pi_k$ be
the interchange of $k$ with the first row $r \ge k$ that maximizes $|a^{(k)}_{rk}|$, and let
$M_k = I - \tau e_k^T$ be the Gauss transformation whose Gauss vector $\tau$ is formed from
column $k$ of $\Pi_k A^{(k)}$. Then
$$A^{(k+1)} = M_k \Pi_k A^{(k)},$$
and the last matrix $A^{(n)} = M_{n-1} \Pi_{n-1} \cdots M_1 \Pi_1 A$ is upper triangular.

The theorem holds for every $A$. A zero pivot comes with a zero column below it; the Gauss
vector is then zero, by the convention $x / 0 = 0$, and $M_k = I$. The row $r$ is
`Matrix.partialPivotRow`, and the Gauss transformation is
`GolubVanLoan.Chapter03.gaussTransformation` of `GolubVanLoan.Chapter03.gaussVector`. -/
theorem equation_3_4_2 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ k : Fin n, partialPivotStage A (k + 1) =
      gaussTransformation (gaussVector
          (fun i => (interchange k (partialPivotRow (partialPivotStage A k) k) *
            partialPivotStage A k) i k) k) k *
        (interchange k (partialPivotRow (partialPivotStage A k) k) * partialPivotStage A k)) ∧
      (partialPivotStage A n).IsUpperTriangular := by
  refine ⟨fun k => ?_, (gemPivotStage_partialPivotRow_permMatrix_mul_isLU A).isUpperTriangular⟩
  rw [gaussTransformation_gaussVector_eq_gaussTransform]
  exact gemPivotStage_succ_fst_eq_gaussTransform_mul A partialPivotRow k.2

/-- **Equation (3.4.3)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be arbitrary.
Partial pivoting computes
$$PA = LU,$$
where $P = \Pi_{n-1} \cdots \Pi_1$ is the permutation matrix of the interchanges, $U = A^{(n)}$
is upper triangular, and $L$ is unit lower triangular with $|\ell_{ij}| \le 1$ for all $i, j$.

The permutation is `(Matrix.gemPivotStage A Matrix.partialPivotRow n).2`, and $L$ is
`Matrix.gemLower` of $PA$, the matrix of multipliers of elimination without pivoting on $PA$. -/
theorem equation_3_4_3 (A : Matrix (Fin n) (Fin n) ℝ) :
    IsLU ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A)
        (gemLower ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A))
        (partialPivotStage A n) ∧
      ∀ i j, |gemLower ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) i j| ≤ 1 :=
  ⟨gemPivotStage_partialPivotRow_permMatrix_mul_isLU A,
    fun i j => gemPivotStage_partialPivotRow_norm_gemLower_le_one A i j⟩

end Partial

/-! ### The invariant of elimination under row interchanges -/

section Invariant

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- A finished multiplier of partial pivoting in the rounding model `fp`: there are an order of the
indices $r < j$, roundings $p_r$ of the products $s_{ir} s_{rj}$, and a running difference $t$
of $a_{ij}$ and the $p_r$, such that $|t| \le |s_{jj}|$ and $s_{ij}$ is a rounding of
$t / s_{jj}$. -/
def LULowerEntryDom (fp : RoundingModel ℝ) (A S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Prop :=
  ∃ (o : List (Fin n)) (p : Fin n → ℝ) (t : ℝ), o.Nodup ∧ (∀ r, r ∈ o ↔ r < j) ∧
    (∀ r ∈ o, fp.Rounds (S i r * S r j) (p r)) ∧
    RoundsSumFrom fp (A i j) (o.map fun r => -p r) t ∧ |t| ≤ |S j j| ∧
    fp.Rounds (t / S j j) (S i j)

/-- The invariant of elimination with partial pivoting after $k$ steps: the invariant
`GolubVanLoan.Chapter03.LUStageInv` of Algorithm 3.2.1, and every entry $s_{ij}$ with $j < k$
and $j < i$ is a finished multiplier dominated by its pivot
(`GolubVanLoan.Chapter03.LULowerEntryDom`). -/
def PivStageInv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  LUStageInv fp A k S ∧ ∀ i j : Fin n, (j : ℕ) < k → j < i → LULowerEntryDom fp A S i j

/-- Interchanging rows at or after $k$ keeps the invariant after $k$ steps. Let $\tau$ be a
permutation that fixes the indices before $k$ and maps the indices from $k$ on among themselves.
If $S$ satisfies the invariant after $k$ steps for $A$, then $S$ with its rows permuted by
$\tau$ satisfies it for $A$ with its rows permuted by $\tau$. The finished rows do not move, and
a row at or after $k$ carries its multipliers and its trailing entries along. -/
theorem pivStageInv_submatrix {A S : Matrix (Fin n) (Fin n) ℝ} {k : ℕ} {τ : Equiv.Perm (Fin n)}
    (hfix : ∀ r : Fin n, (r : ℕ) < k → τ r = r) (hmap : ∀ i : Fin n, k ≤ (i : ℕ) → k ≤ (τ i : ℕ))
    (h : PivStageInv fp A k S) :
    PivStageInv fp (A.submatrix τ id) k (S.submatrix τ id) := by
  obtain ⟨hS, hD⟩ := h
  -- the row `τ i` sits above column `j < k` exactly when `i` does
  have hlt : ∀ (i j : Fin n), (j : ℕ) < k → j < i → j < τ i := fun i j hj hji => by
    by_cases hi : (i : ℕ) < k
    · rw [hfix i hi]; exact hji
    · exact Fin.lt_def.2 (lt_of_lt_of_le hj (hmap i (not_lt.1 hi)))
  refine ⟨fun i j => ⟨fun hi hij => ?_, fun hj hji => ?_, fun hi hj => ?_⟩,
    fun i j hj hji => ?_⟩
  · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).1 hi hij
    refine ⟨o, p, hnd, ho, fun r hr => ?_, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, id, hfix i hi, hfix r (by omega)]
      exact hp r hr
    · simp only [submatrix_apply, id, hfix i hi]
      exact hsum
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hx⟩ := (hS (τ i) j).2.1 hj (hlt i j hj hji)
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, id, hfix r (by omega)]
      exact hp r hr
    · simp only [submatrix_apply, id, hfix j hj]
      exact hx
  · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS (τ i) j).2.2 (hmap i hi) hj
    refine ⟨o, p, hnd, ho, fun r hr => ?_, hsum⟩
    simp only [submatrix_apply, id, hfix r ((ho r).1 hr)]
    exact hp r hr
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hdom, hx⟩ := hD (τ i) j hj (hlt i j hj hji)
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, id, hfix r (by omega)]
      exact hp r hr
    · simp only [submatrix_apply, id, hfix j hj]
      exact hdom
    · simp only [submatrix_apply, id, hfix j hj]
      exact hx

/-- One elimination step keeps the invariant. Let $S$ satisfy the invariant after $k$ steps, and let
the pivot dominate its column, $|s_{ik}| \le |s_{kk}|$ for $i \ge k$. Let $S'$ agree with $S$
except in the rows $i > k$ and the columns $j \ge k$, let $s'_{ik}$ be a rounding of
$s_{ik} / s_{kk}$ for $i > k$, and let $s'_{ij}$ be a rounding of $s_{ij} - p$ for a rounding
$p$ of $s'_{ik} s'_{kj}$, for $i, j > k$. Then $S'$ satisfies the invariant after $k + 1$ steps. -/
theorem pivStageInv_step {A S S' : Matrix (Fin n) (Fin n) ℝ} (k : Fin n)
    (hS : PivStageInv fp A k S) (hdom : ∀ i : Fin n, k ≤ i → |S i k| ≤ |S k k|)
    (hunch : ∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → S' i j = S i j)
    (hdiv : ∀ i, k < i → fp.Rounds (S i k / S k k) (S' i k))
    (hupd : ∀ i j, k < i → k < j →
      ∃ p, fp.Rounds (S' i k * S' k j) p ∧ fp.Rounds (S i j - p) (S' i j)) :
    PivStageInv fp A (k + 1) S' := by
  obtain ⟨hS₁, hS₂⟩ := hS
  refine ⟨luStageInv_step A k hS₁ hunch hdiv hupd, fun i j hj hji => ?_⟩
  have hrow : ∀ i j : Fin n, (i : ℕ) ≤ k → S' i j = S i j := fun i j hi =>
    hunch i j fun h => absurd (Fin.lt_def.1 h.1) (not_lt.2 hi)
  have hcol : ∀ i j : Fin n, (j : ℕ) < k → S' i j = S i j := fun i j hj =>
    hunch i j fun h => h.2.elim (fun h' => absurd (h' ▸ hj) (lt_irrefl _))
      fun h' => absurd (Fin.lt_def.1 h') (not_lt.2 hj.le)
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hd, hx⟩ := hS₂ i j hj hji
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_, ?_⟩
    · have hrj := Fin.lt_def.1 ((ho r).1 hr)
      rw [hcol i r (by omega), hcol r j hj]
      exact hp r hr
    · rw [hcol j j hj]
      exact hd
    · rw [hcol i j hj, hcol j j hj]
      exact hx
  · have hjk : j = k := Fin.ext hj
    subst hjk
    obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS₁ i j).2.2 (Fin.le_def.1 hji.le) le_rfl
    refine ⟨o, p, S i j, hnd, fun r => (ho r).trans Fin.lt_def.symm, fun r hr => ?_, hsum, ?_,
      ?_⟩
    · have hrj := (ho r).1 hr
      rw [hcol i r hrj, hrow r j hrj.le]
      exact hp r hr
    · rw [hrow j j le_rfl]
      exact hdom i hji.le
    · rw [hrow j j le_rfl]
      exact hdiv i hji

/-- A zero pivot whose column vanishes below it. Let $S$ satisfy the invariant after $k$ steps, let
the pivot dominate its column, and let $s_{kk} = 0$. If the model rounds every value to itself,
as the exact model does, or $k$ is the last index, then $S$ satisfies the invariant after
$k + 1$ steps: the skipped update is an update. -/
theorem pivStageInv_step_of_zero {A S : Matrix (Fin n) (Fin n) ℝ} (k : Fin n)
    (hS : PivStageInv fp A k S) (hdom : ∀ i : Fin n, k ≤ i → |S i k| ≤ |S k k|)
    (hzero : S k k = 0) (hrefl : (∀ x, fp.Rounds x x) ∨ ¬ (k : ℕ) + 1 < n) :
    PivStageInv fp A (k + 1) S := by
  have hcol : ∀ i : Fin n, k ≤ i → S i k = 0 := fun i hi => by
    have := hdom i hi
    rw [hzero, abs_zero] at this
    exact abs_nonpos_iff.1 this
  refine pivStageInv_step k hS hdom (fun _ _ _ => rfl) (fun i hi => ?_) (fun i j hi _ => ?_)
  · rcases hrefl with hrefl | hrefl
    · rw [hcol i hi.le, hzero, zero_div]
      exact hrefl 0
    · exact absurd (by have := Fin.lt_def.1 hi; omega) hrefl
  · rcases hrefl with hrefl | hrefl
    · refine ⟨S i k * S k j, hrefl _, ?_⟩
      rw [hcol i hi.le, zero_mul, sub_zero]
      exact hrefl _
    · exact absurd (by have := Fin.lt_def.1 hi; omega) hrefl

end Invariant

/-! ### Algorithm 3.4.1 (Outer Product LU with Partial Pivoting) -/

section Algorithm341

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.4.1** of [golub2013matrix] (Outer Product LU with Partial Pivoting). The algorithm
computes the factorization $PA = LU$, where $P$ is a permutation matrix encoded by
$\mathrm{piv}(1{:}n-1)$, $L$ is unit lower triangular with $|\ell_{ij}| \le 1$, and $U$ is upper
triangular. For $i = 1{:}n$, $A(i, i{:}n)$ is overwritten by $U(i, i{:}n)$ and $A(i{+}1{:}n, i)$
is overwritten by $L(i{+}1{:}n, i)$.
```
for k = 1:n-1
    Determine μ with k ≤ μ ≤ n so |A(μ,k)| = ‖A(k:n,k)‖_∞
    piv(k) = μ
    A(k,:) ↔ A(μ,:)
    if A(k,k) ≠ 0
        ρ = k+1:n
        A(ρ,k) = A(ρ,k)/A(k,k)
        A(ρ,ρ) = A(ρ,ρ) - A(ρ,k) A(k,ρ)
    end
end
```
The program returns the packed matrix and the pivot vector.

The search is `Matrix.partialPivotRow`, the first maximizing row, with exact comparisons. The
updates are `GolubVanLoan.Chapter03.outerProductStep`, the step of Algorithm 3.2.1. The state is
the pair of the matrix and $\mathrm{piv}$, with $\mathrm{piv}$ initially the identity. The last
step $k = n$ is a trivial interchange with empty updates. -/
noncomputable def algorithm_3_4_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) :=
  (List.finRange n).foldlM (fun (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) k =>
    if st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id k k ≠ 0 then do
      let A ← outerProductStep rnd k (st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id)
      pure (A, Function.update st.2 k (partialPivotRow st.1 k))
    else
      pure (st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id,
        Function.update st.2 k (partialPivotRow st.1 k))) (A, fun k => k)

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- The invariant of Algorithm 3.4.1 after $k$ steps on the state $(S, \mathrm{piv})$: either $S$
satisfies `GolubVanLoan.Chapter03.PivStageInv` for $A$ with its rows permuted by the first $k$
interchanges, or the model does not round every value to itself and a returned pivot $s_{jj}$
with $j < k$ and $j + 1 < n$ is zero. -/
def Alg341Inv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) : Prop :=
  PivStageInv fp (A.submatrix (pivPermUpTo st.2 k) id) k st.1 ∨
    ((∃ j : Fin n, (j : ℕ) < k ∧ (j : ℕ) + 1 < n ∧ st.1 j j = 0) ∧ ¬ ∀ x, fp.Rounds x x)

/-- One step of Algorithm 3.4.1 keeps its invariant `GolubVanLoan.Chapter03.Alg341Inv`. -/
theorem alg341Inv_step (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) (hst : Alg341Inv fp A k st)
    (st' : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n))
    (hst' : st' ∈ (if st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id k k ≠ 0 then do
      let A ← outerProductStep fp.round k
        (st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id)
      pure (A, Function.update st.2 k (partialPivotRow st.1 k))
    else
      pure (st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id,
        Function.update st.2 k (partialPivotRow st.1 k)) : SetM _).run) :
    Alg341Inv fp A (k + 1) st' := by
  obtain ⟨S, piv⟩ := st
  dsimp only at hst hst'
  set μ := partialPivotRow S k with hμ
  set S₀ := S.submatrix (Equiv.swap k μ) id with hS₀
  have hkμ : k ≤ μ := le_partialPivotRow S k
  have hfix : ∀ r : Fin n, (r : ℕ) < k → Equiv.swap k μ r = r := fun r hr =>
    Equiv.swap_apply_of_ne_of_ne (fun h => by rw [h] at hr; exact lt_irrefl _ hr)
      fun h => by rw [h] at hr; exact absurd (Fin.le_def.1 hkμ) (not_le.2 hr)
  have hmap : ∀ i : Fin n, (k : ℕ) ≤ i → (k : ℕ) ≤ (Equiv.swap k μ i : ℕ) := fun i hi => by
    rcases eq_or_ne i k with rfl | hik
    · rw [Equiv.swap_apply_left]; exact hkμ
    rcases eq_or_ne i μ with rfl | hiμ
    · rw [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hik hiμ]; exact hi
  -- the permutation after the step
  have hperm : pivPermUpTo (Function.update piv k μ) (k + 1) =
      pivPermUpTo piv k * Equiv.swap k μ := by
    rw [pivPermUpTo_succ, Function.update_self,
      pivPermUpTo_congr (piv := Function.update piv k μ) (piv' := piv) (k := k)
        fun j hj => Function.update_of_ne (fun h => by rw [h] at hj; exact lt_irrefl _ hj) _ _]
  have hsub : (A.submatrix (pivPermUpTo piv k) id).submatrix (Equiv.swap k μ) id =
      A.submatrix (pivPermUpTo (Function.update piv k μ) (k + 1)) id := by
    rw [hperm, submatrix_submatrix, Equiv.Perm.coe_mul]
    rfl
  -- the interchanged pivot dominates its column
  have hdom : ∀ i : Fin n, k ≤ i → |S₀ i k| ≤ |S₀ k k| := fun i hi => by
    simp only [hS₀, submatrix_apply, id, Equiv.swap_apply_left]
    have := norm_apply_le_partialPivotRow S k (r := Equiv.swap k μ i)
      (Fin.le_def.2 (hmap i (Fin.le_def.1 hi)))
    simpa only [Real.norm_eq_abs] using this
  -- rows before `k` are not touched
  have hrows : ∀ S' : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → S' i j = S₀ i j) →
      ∀ j : Fin n, (j : ℕ) < k → S' j j = S j j := fun S' hS' j hj => by
    rw [hS' j j fun h => absurd (Fin.lt_def.1 h.1) (by omega), hS₀, submatrix_apply, id,
      hfix j hj]
  rcases hst with hgood | ⟨⟨j, hj, hjn, hj0⟩, hnrefl⟩
  · have hgood₀ : PivStageInv fp (A.submatrix (pivPermUpTo (Function.update piv k μ) (k + 1)) id)
        k S₀ := hsub ▸ pivStageInv_submatrix hfix hmap hgood
    split_ifs at hst' with h0
    · rw [SetM.mem_run_bind] at hst'
      obtain ⟨S', hS', hst'⟩ := hst'
      rw [SetM.mem_run_pure] at hst'
      subst hst'
      obtain ⟨h₁, h₂, h₃⟩ := mem_run_outerProductStep k hS'
      exact Or.inl (pivStageInv_step k hgood₀ hdom h₁ h₂ h₃)
    · rw [SetM.mem_run_pure] at hst'
      subst hst'
      have h0' : S₀ k k = 0 := not_not.1 h0
      by_cases hc : (∀ x, fp.Rounds x x) ∨ ¬ (k : ℕ) + 1 < n
      · exact Or.inl (pivStageInv_step_of_zero k hgood₀ hdom h0' hc)
      · obtain ⟨hc₁, hc₂⟩ := not_or.1 hc
        exact Or.inr ⟨⟨k, by simp, not_not.1 hc₂, h0'⟩, hc₁⟩
  · refine Or.inr ⟨⟨j, by omega, hjn, ?_⟩, hnrefl⟩
    split_ifs at hst' with h0
    · rw [SetM.mem_run_bind] at hst'
      obtain ⟨S', hS', hst'⟩ := hst'
      rw [SetM.mem_run_pure] at hst'
      subst hst'
      change S' j j = 0
      rw [hrows S' (mem_run_outerProductStep k hS').1 j hj]
      exact hj0
    · rw [SetM.mem_run_pure] at hst'
      subst hst'
      change S₀ j j = 0
      rw [hrows S₀ (fun _ _ _ => rfl) j hj]
      exact hj0

/-- Every run of Algorithm 3.4.1 satisfies the invariant `GolubVanLoan.Chapter03.Alg341Inv` after
all $n$ steps. -/
theorem alg341Inv_of_mem_run (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, Alg341Inv fp A n out :=
  SetM.forall_mem_run_foldlM_finRange (Alg341Inv fp A)
    (Or.inl ⟨luStageInv_zero _, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun k st hst st' hst' => alg341Inv_step A k st hst st' hst'

/-- A multiplier that is dominated by its pivot in the sense of
`GolubVanLoan.Chapter03.LULowerEntryDom` has modulus at most $1 + u$. -/
theorem abs_le_one_add_of_lowerEntryDom {A S : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n}
    (h : LULowerEntryDom fp A S i j) : |S i j| ≤ 1 + fp.u := by
  obtain ⟨-, -, t, -, -, -, -, hd, hx⟩ := h
  have h1 : |t / S j j| ≤ 1 := abs_div_le_one_of_abs_le hd
  have h2 := fp.abs_sub_le hx
  have h3 : |S i j| ≤ |S i j - t / S j j| + |t / S j j| := by
    simpa using abs_add_le (S i j - t / S j j) (t / S j j)
  nlinarith [fp.u_nonneg, abs_nonneg (t / S j j)]

/-- **Algorithm 3.4.1** of [golub2013matrix], rounding bridge. Let $A \in \mathbb{R}^{n \times n}$.
For every output $(F, \mathrm{piv})$ of Algorithm 3.4.1 in the rounding model `fp` whose
returned pivots $f_{jj}$, $j + 1 < n$, are nonzero, let $P$ be the permutation matrix encoded by
$\mathrm{piv}$ and let $\hat L$ and $\hat U$ be the factors stored in $F$. Then $\hat L$ and
$\hat U$ form a computed LU factorization of $PA$ in the sense of `FloatingPoint.RoundsLU`, and
$$|\hat\ell_{ij}| \le 1 + u \quad \text{for all } i, j.$$

The computed factors of partial pivoting are the computed factors of elimination without
pivoting on $PA$ ([higham2002accuracy] §9.3). The relational model bounds a rounded quotient of
modulus at most one by $1 + u$, not by $1$. The factors are `GolubVanLoan.Chapter03.packedL F`
and `GolubVanLoan.Chapter03.packedU F`, and $PA$ is `A.submatrix (pivPerm piv) id`. -/
theorem algorithm_3_4_1_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, (∀ j : Fin n, (j : ℕ) + 1 < n → out.1 j j ≠ 0) →
      RoundsLU fp (A.submatrix (pivPerm out.2) id) (packedL out.1) (packedU out.1) ∧
        ∀ i j, |packedL out.1 i j| ≤ 1 + fp.u := by
  intro out hout hpiv
  rcases alg341Inv_of_mem_run A out hout with ⟨hS, hD⟩ | ⟨⟨j, -, hjn, hj0⟩, -⟩
  · refine ⟨roundsLU_of_luStageInv hS, fun i j => ?_⟩
    rcases lt_trichotomy j i with hji | rfl | hij
    · rw [packedL_apply_of_lt _ hji]
      exact abs_le_one_add_of_lowerEntryDom (hD i j j.2 hji)
    · rw [packedL_apply_self, abs_one]
      linarith [fp.u_nonneg]
    · rw [packedL_apply_of_lt' _ hij, abs_zero]
      linarith [fp.u_nonneg]
  · exact absurd hj0 (hpiv j hjn)

/-- **Algorithm 3.4.1** of [golub2013matrix], existence of runs. If the rounding model `fp` is
total, that is, every real number has at least one rounding, then for every $A$ the run set of
Algorithm 3.4.1 is nonempty.

So the bridge and the bounds built on it are not vacuous. Every step of the program is a bind of
`fp.round` or `pure`. -/
theorem algorithm_3_4_1_run_nonempty (hfp : fp.IsTotal) (A : Matrix (Fin n) (Fin n) ℝ) :
    (algorithm_3_4_1 fp.round A).run.Nonempty := by
  have hstep : ∀ (k : Fin n) (B : Matrix (Fin n) (Fin n) ℝ),
      (outerProductStep fp.round k B).run.Nonempty := fun k B => by
    refine SetM.run_bind_nonempty (SetM.run_foldlM_nonempty (fun _ _ _ =>
      SetM.run_bind_nonempty (RoundingModel.run_round_nonempty hfp _) fun _ _ =>
        ⟨_, SetM.mem_run_pure.2 rfl⟩) _) fun _ _ => SetM.run_foldlM_nonempty (fun _ _ _ =>
      SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
        (RoundingModel.run_round_nonempty hfp _) fun _ _ => SetM.run_bind_nonempty
          (RoundingModel.run_round_nonempty hfp _) fun _ _ => ⟨_, SetM.mem_run_pure.2 rfl⟩) _) _
  refine SetM.run_foldlM_nonempty (fun st k _ => ?_) _
  split_ifs
  · exact SetM.run_bind_nonempty (hstep k _) fun _ _ => ⟨_, SetM.mem_run_pure.2 rfl⟩
  · exact ⟨_, SetM.mem_run_pure.2 rfl⟩

/-- The exact run of Algorithm 3.4.1 is one of its runs in the exact rounding model. -/
private theorem algorithm_3_4_1_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_3_4_1 pure A) ∈ (algorithm_3_4_1 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_4_1, outerProductStep, pure_bind, ite_pure, List.foldlM_pure,
    SetM.mem_run_pure]
  rfl

/-- The exact factors of a finished invariant. In the exact model, if $F$ satisfies the invariant of
partial pivoting after $n$ steps for $A$, then $A = LU$ with $L$ and $U$ the factors stored in
$F$, and $|\ell_{ij}| \le 1$ for all $i, j$. A zero pivot has a zero numerator. -/
theorem isLU_of_pivStageInv_exact {A F : Matrix (Fin n) (Fin n) ℝ}
    (h : PivStageInv (RoundingModel.exact ℝ) A n F) :
    IsLU A (packedL F) (packedU F) ∧ ∀ i j, |packedL F i j| ≤ 1 := by
  obtain ⟨hS, hD⟩ := h
  have hR := roundsLU_of_luStageInv hS
  -- the entries of the product
  have hU : ∀ i j : Fin n, i ≤ j →
      F i j = A i j - ∑ r ∈ Finset.univ.filter (· < i), F i r * F r j := by
    intro i j hij
    obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).1 i.2 hij
    have hset : o.toFinset = Finset.univ.filter (· < i) := by ext r; simp [ho]
    rw [(roundsSumFrom_exact_map_neg_iff hnd).1 hsum, hset]
    congr 1
    exact Finset.sum_congr rfl fun r hr => hp r ((ho r).2 (Finset.mem_filter.1 hr).2)
  have hL : ∀ i j : Fin n, j < i →
      F i j * F j j = A i j - ∑ r ∈ Finset.univ.filter (· < j), F i r * F r j ∧ |F i j| ≤ 1 := by
    intro i j hji
    obtain ⟨o, p, t, hnd, ho, hp, hsum, hd, hx⟩ := hD i j j.2 hji
    have hset : o.toFinset = Finset.univ.filter (· < j) := by ext r; simp [ho]
    have ht : t = A i j - ∑ r ∈ Finset.univ.filter (· < j), F i r * F r j := by
      rw [(roundsSumFrom_exact_map_neg_iff hnd).1 hsum, hset]
      congr 1
      exact Finset.sum_congr rfl fun r hr => hp r ((ho r).2 (Finset.mem_filter.1 hr).2)
    rw [RoundingModel.exact_rounds_iff] at hx
    refine ⟨?_, by rw [hx]; exact abs_div_le_one_of_abs_le hd⟩
    rw [← ht, hx]
    rcases eq_or_ne (F j j) 0 with h0 | h0
    · rw [h0, abs_zero] at hd
      rw [h0, mul_zero, abs_nonpos_iff.1 hd]
    · exact div_mul_cancel₀ _ h0
  refine ⟨⟨hR.isLU_mul.isUnitLowerTriangular, hR.isLU_mul.isUpperTriangular, ?_⟩,
    fun i j => ?_⟩
  · ext i j
    rw [hR.isLU_mul.apply_eq_sum]
    rcases le_or_gt i j with hij | hji
    · have hsum : ∑ r ∈ Finset.univ.filter (· < i), packedL F i r * packedU F r j =
          ∑ r ∈ Finset.univ.filter (· < i), F i r * F r j :=
        Finset.sum_congr rfl fun r hr => by
          have hr' := (Finset.mem_filter.1 hr).2
          rw [packedL_apply_of_lt _ hr', packedU_apply_of_le _ (hr'.le.trans hij)]
      rw [min_eq_left hij, Matrix.sum_filter_le_eq_add, packedL_apply_self, one_mul,
        packedU_apply_of_le _ hij, hsum, hU i j hij]
      ring
    · have hsum : ∑ r ∈ Finset.univ.filter (· < j), packedL F i r * packedU F r j =
          ∑ r ∈ Finset.univ.filter (· < j), F i r * F r j :=
        Finset.sum_congr rfl fun r hr => by
          have hr' := (Finset.mem_filter.1 hr).2
          rw [packedL_apply_of_lt _ (hr'.trans hji), packedU_apply_of_le _ hr'.le]
      rw [min_eq_right hji.le, Matrix.sum_filter_le_eq_add, packedL_apply_of_lt _ hji,
        packedU_apply_of_le _ le_rfl, hsum, (hL i j hji).1]
      ring
  · rcases lt_trichotomy j i with hji | rfl | hij
    · rw [packedL_apply_of_lt _ hji]
      exact (hL i j hji).2
    · rw [packedL_apply_self, abs_one]
    · rw [packedL_apply_of_lt' _ hij, abs_zero]
      exact zero_le_one

/-- **Algorithm 3.4.1** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
be arbitrary, and let $(F, \mathrm{piv})$ be the output of Algorithm 3.4.1 in exact arithmetic.
Let $P$ be the permutation matrix encoded by $\mathrm{piv}$, $L$ the unit lower triangular
matrix stored below the diagonal of $F$, and $U$ the upper triangular matrix stored on and above
it. Then
$$PA = LU, \qquad |\ell_{ij}| \le 1 \text{ for all } i, j.$$

The source notes that Algorithm 3.4.1 always runs to completion; the theorem has no hypothesis
on $A$. The factors are `GolubVanLoan.Chapter03.packedL F` and
`GolubVanLoan.Chapter03.packedU F`. The proof reads the invariant of the bridge at the exact
model. -/
theorem algorithm_3_4_1_spec (A : Matrix (Fin n) (Fin n) ℝ) :
    IsLU ((pivPerm (Id.run (algorithm_3_4_1 pure A)).2).permMatrix ℝ * A)
        (packedL (Id.run (algorithm_3_4_1 pure A)).1)
        (packedU (Id.run (algorithm_3_4_1 pure A)).1) ∧
      ∀ i j, |packedL (Id.run (algorithm_3_4_1 pure A)).1 i j| ≤ 1 := by
  rcases alg341Inv_of_mem_run A _ (algorithm_3_4_1_mem_exact A) with h | ⟨-, hn⟩
  · rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    exact isLU_of_pivStageInv_exact h
  · exact absurd (fun x => rfl) hn

end Algorithm341

/-! ### Solving after Algorithm 3.4.1 (§3.4.3) and the LU mentality (§3.4.9) -/

section Solve

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Section 3.4.3** of [golub2013matrix], the solve after Algorithm 3.4.1: solve $Ly = Pb$ for $y$
and $Ux = y$ for $x$. Given the packed factor $F$, the pivot vector $\mathrm{piv}$ and $b$, the
program returns $x$.

The vector $b$ is overwritten by $Pb$ with the loop `GolubVanLoan.Chapter03.applyPiv`, which
does no arithmetic. Then the row-oriented substitutions of §3.1, Algorithms 3.1.1 and 3.1.2,
solve with the packed factors; these are the solves of Theorem 3.3.2. Algorithm 3.1.1 performs
the division by the unit diagonal of $L$, as the source writes it. -/
noncomputable def solvePLU {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (piv : Fin n → Fin n)
    (b : Fin n → ℝ) : M (Fin n → ℝ) := do
  let y ← algorithm_3_1_1 rnd (packedL F) (applyPiv piv b)
  algorithm_3_1_2 rnd (packedU F) y

/-- Gaussian elimination with partial pivoting followed by the solve: Algorithm 3.4.1 on $A$, then
`GolubVanLoan.Chapter03.solvePLU` with $b$. -/
noncomputable def solveGEPP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let out ← algorithm_3_4_1 rnd A
  solvePLU rnd out.1 out.2 b

/-- **Equation (3.4.12)** of [golub2013matrix], the multiple right-hand side problem $AX = B$ for
$B \in \mathbb{R}^{n \times p}$: compute $PA = LU$ by Algorithm 3.4.1; then for $k = 1{:}p$,
solve $Ly = Pb_k$ and then $Ux_k = y$. The program returns $X = [x_1, \dots, x_p]$. With $B = I$
the output approximates $A^{-1}$. -/
noncomputable def solveMultipleRHS {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) : M (Matrix (Fin n) (Fin p) ℝ) := do
  let out ← algorithm_3_4_1 rnd A
  (List.finRange p).foldlM (fun (X : Matrix (Fin n) (Fin p) ℝ) k => do
    let x ← solvePLU rnd out.1 out.2 (fun i => B i k)
    pure (X.updateCol k x)) B

/-- **Equation (3.4.13)** of [golub2013matrix], the solve of $A^k x = b$ without forming $A^k$:
compute $PA = LU$ by Algorithm 3.4.1; then for $j = 1{:}k$, overwrite $b$ with the solution of
$Ly = Pb$, and then overwrite $b$ with the solution of $Ux = b$. The program returns the last
$b$. -/
noncomputable def solvePowerSystem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (b : Fin n → ℝ) : M (Fin n → ℝ) := do
  let out ← algorithm_3_4_1 rnd A
  (List.range k).foldlM (fun b _ => solvePLU rnd out.1 out.2 b) b

variable {n : ℕ}

/-- Let $A \in \mathbb{R}^{n \times n}$ be nonsingular and $b \in \mathbb{R}^n$. In exact
arithmetic, the solve `GolubVanLoan.Chapter03.solvePLU` with the output of Algorithm 3.4.1 on
$A$ returns $x$ with $Ax = b$. -/
theorem solvePLU_id_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (b : Fin n → ℝ) :
    A *ᵥ Id.run (solvePLU pure (Id.run (algorithm_3_4_1 pure A)).1
      (Id.run (algorithm_3_4_1 pure A)).2 b) = b := by
  obtain ⟨hLU, -⟩ := algorithm_3_4_1_spec A
  set out := Id.run (algorithm_3_4_1 pure A)
  have hd : ∀ i, packedU out.1 i i ≠ 0 := by
    have hPA : IsUnit ((pivPerm out.2).permMatrix ℝ * A) := (isUnit_permMatrix _).mul hA
    intro i hi
    have hdet : ((pivPerm out.2).permMatrix ℝ * A).det = 0 := by
      rw [hLU.det_eq_prod_diag]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    exact ((isUnit_iff_isUnit_det _).1 hPA).ne_zero hdet
  have h := mulVec_luSolve_permMatrix b hLU hd
  change A *ᵥ Id.run (algorithm_3_1_2 pure (packedU out.1)
    (Id.run (algorithm_3_1_1 pure (packedL out.1) (applyPiv out.2 b)))) = b
  rw [algorithm_3_1_1_eq_forwardSubst, algorithm_3_1_2_eq_backSubst, (applyPiv_eq _ _).1]
  exact h

/-- **Section 3.4.3** of [golub2013matrix], exact correctness of the solve. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular and $b \in \mathbb{R}^n$. In exact arithmetic,
Gaussian elimination with partial pivoting followed by $Ly = Pb$ and $Ux = y$ returns $x$ with
$$Ax = b.$$
-/
theorem solveGEPP_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (b : Fin n → ℝ) :
    A *ᵥ Id.run (solveGEPP pure A b) = b :=
  solvePLU_id_eq hA b

/-- **Equation (3.4.12)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular
and $B \in \mathbb{R}^{n \times p}$. In exact arithmetic, the output $X$ of the multiple
right-hand side procedure satisfies
$$AX = B,$$
and for $B = I$ the output is $A^{-1}$. -/
theorem equation_3_4_12 {p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (B : Matrix (Fin n) (Fin p) ℝ) :
    A * Id.run (solveMultipleRHS pure A B) = B ∧
      Id.run (solveMultipleRHS pure A (1 : Matrix (Fin n) (Fin n) ℝ)) = A⁻¹ := by
  have key : ∀ {p : ℕ} (B : Matrix (Fin n) (Fin p) ℝ),
      A * Id.run (solveMultipleRHS pure A B) = B := by
    intro p B
    set out := Id.run (algorithm_3_4_1 pure A)
    change A * Id.run ((List.finRange p).foldlM (fun (X : Matrix (Fin n) (Fin p) ℝ) k => do
      let x ← solvePLU pure out.1 out.2 (fun i => B i k)
      pure (X.updateCol k x)) B) = B
    rw [List.idRun_foldlM]
    ext i k
    rw [Matrix.mul_apply]
    have hcol : ∀ j, (List.finRange p).foldl (fun X k => Id.run (do
        let x ← solvePLU pure out.1 out.2 (fun i => B i k)
        pure (X.updateCol k x) : Id _)) B j k =
        Id.run (solvePLU pure out.1 out.2 (fun i => B i k)) j := fun j => by
      exact (Matrix.foldl_updateCol_apply
        (fun k _ => Id.run (solvePLU pure out.1 out.2 (fun i => B i k)))
        (List.nodup_finRange p) B j k).trans (ite_eq_left (List.mem_finRange k))
    simp only [hcol]
    exact congrFun (solvePLU_id_eq hA (fun i => B i k)) i
  exact ⟨key B, (inv_eq_right_inv (key 1)).symm⟩

/-- **Equation (3.4.13)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular,
$k \in \mathbb{N}$ and $b \in \mathbb{R}^n$. In exact arithmetic, the output $x$ of
`GolubVanLoan.Chapter03.solvePowerSystem` satisfies
$$A^k x = b.$$
-/
theorem equation_3_4_13 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (k : ℕ) (b : Fin n → ℝ) :
    A ^ k *ᵥ Id.run (solvePowerSystem pure A k b) = b := by
  set out := Id.run (algorithm_3_4_1 pure A)
  have hstep : ∀ c : Fin n → ℝ, A *ᵥ Id.run (solvePLU pure out.1 out.2 c) = c :=
    fun c => solvePLU_id_eq hA c
  change A ^ k *ᵥ Id.run ((List.range k).foldlM (fun b _ => solvePLU pure out.1 out.2 b) b) = b
  rw [List.idRun_foldlM]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ,
      ← mulVec_mulVec, hstep, ih]

end Solve

/-! ### The backward error of the solve (§3.4.5) -/

section Backward

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- The backward error of the solve with computed factors of a row-permuted matrix. Let $u < 1$ and
$3nu < 1$, let $\sigma$ be a permutation with permutation matrix $P$, and let $\hat L$, $\hat U$
be a computed LU factorization of $PA$ in the sense of `FloatingPoint.RoundsLU`, with every
$\hat u_{jj}$ nonzero. If $\hat y$ is computed by Algorithm 3.1.1 from $\hat L$ and $Pb$, and
$\hat x$ by Algorithm 3.1.2 from $\hat U$ and $\hat y$, then there is $E$ with
$(A + E)\hat x = b$ and $|E| \le \gamma_{3n} P^T |\hat L| |\hat U|$ entrywise.

This is Theorem 3.3.2 for the system $(PA)x = Pb$, which is Theorem 9.4 of [higham2002accuracy].
It serves both partial pivoting algorithms, 3.4.1 and 3.4.2. Here $Pb$ is `b ∘ σ`, and $P^T M$
is `M.submatrix σ.symm id`. -/
theorem exists_backward_error_of_roundsLU (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    {A L U : Matrix (Fin n) (Fin n) ℝ} {σ : Equiv.Perm (Fin n)}
    (hR : RoundsLU fp (A.submatrix σ id) L U) (hpiv : ∀ j, U j j ≠ 0) {b y x : Fin n → ℝ}
    (hy : y ∈ (algorithm_3_1_1 fp.round L (b ∘ σ)).run)
    (hx : x ∈ (algorithm_3_1_2 fp.round U y).run) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, (A + E) *ᵥ x = b ∧
      E.abs ≤ₑ gamma fp.u (3 * n) • (L.abs * U.abs).submatrix σ.symm id := by
  obtain ⟨E', hE', hAx⟩ := exists_roundsLU_solveDot_eq hu (by simpa using hn) hR hpiv
    (algorithm_3_1_1_rounds fp _ _ y hy) (algorithm_3_1_2_rounds fp _ y x hx)
  refine ⟨E'.submatrix σ.symm id, funext fun i => ?_, fun i j => ?_⟩
  · have h := congrFun hAx (σ.symm i)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
    rw [← h]
    simp only [mulVec, dotProduct, Matrix.add_apply, submatrix_apply, id, Equiv.apply_symm_apply]
  · simpa [Matrix.abs, smul_eq_mul] using hE' (σ.symm i) j

/-- **Equation (3.4.6)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$, and let the unit roundoff satisfy $u < 1$ and $3nu < 1$. Let
$(F, \mathrm{piv})$ be an output of Algorithm 3.4.1 on $A$ whose diagonal entries $f_{jj}$ are
all nonzero, let $P$ be the permutation matrix encoded by $\mathrm{piv}$, and let $\hat L$ and
$\hat U$ be the factors stored in $F$. Then every solution $\hat x$ computed from $F$,
$\mathrm{piv}$ and $b$ by the solve $Ly = Pb$, $Ux = y$ satisfies $(A + E)\hat x = b$ for some
$E \in \mathbb{R}^{n \times n}$ with
$$|E| \le \gamma_{3n} P^T |\hat L| |\hat U|$$
entrywise.

The source prints the first-order bound $|E| \le nu(2|A| + 4P^T|\hat L||\hat U|) + O(u^2)$,
which the rigorous bound implies. The permutation involves no rounding. The matrix $P^T M$ is
$M$ with its rows permuted back, `M.submatrix (pivPerm piv).symm id`. The proof applies
`GolubVanLoan.Chapter03.algorithm_3_4_1_rounds` and
`GolubVanLoan.Chapter03.exists_backward_error_of_roundsLU`. -/
theorem equation_3_4_6 (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, (∀ j, out.1 j j ≠ 0) →
      ∀ x ∈ (solvePLU fp.round out.1 out.2 b).run, ∃ E : Matrix (Fin n) (Fin n) ℝ,
        (A + E) *ᵥ x = b ∧ E.abs ≤ₑ gamma fp.u (3 * n) •
          ((packedL out.1).abs * (packedU out.1).abs).submatrix (pivPerm out.2).symm id := by
  intro out hout hpiv x hx
  obtain ⟨hR, -⟩ := algorithm_3_4_1_rounds A out hout fun j _ => hpiv j
  rw [solvePLU, SetM.mem_run_bind] at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [(applyPiv_eq _ _).1, permMatrix_mulVec] at hy
  exact exists_backward_error_of_roundsLU hu hn hR
    (fun j => by rw [packedU_apply_of_le _ le_rfl]; exact hpiv j) hy hx

end Backward

/-! ### Complete pivoting (§3.4.6) -/

section Complete

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- Interchanging rows and columns at or after $k$ keeps the invariant of partial pivoting after $k$
steps. Let $\tau$ and $\rho$ be permutations that fix the indices before $k$ and map the indices
from $k$ on among themselves. If $S$ satisfies the invariant after $k$ steps for $A$, then $S$
with rows permuted by $\tau$ and columns permuted by $\rho$ satisfies it for $A$ with the same
rows and columns permuted. -/
theorem pivStageInv_submatrix₂ {A S : Matrix (Fin n) (Fin n) ℝ} {k : ℕ}
    {τ ρ : Equiv.Perm (Fin n)}
    (hfix : ∀ r : Fin n, (r : ℕ) < k → τ r = r) (hmap : ∀ i : Fin n, k ≤ (i : ℕ) → k ≤ (τ i : ℕ))
    (hfix' : ∀ r : Fin n, (r : ℕ) < k → ρ r = r)
    (hmap' : ∀ i : Fin n, k ≤ (i : ℕ) → k ≤ (ρ i : ℕ))
    (h : PivStageInv fp A k S) :
    PivStageInv fp (A.submatrix τ ρ) k (S.submatrix τ ρ) := by
  obtain ⟨hS, hD⟩ := h
  have hlt : ∀ (i j : Fin n), (j : ℕ) < k → j < i → j < τ i := fun i j hj hji => by
    by_cases hi : (i : ℕ) < k
    · rw [hfix i hi]; exact hji
    · exact Fin.lt_def.2 (lt_of_lt_of_le hj (hmap i (not_lt.1 hi)))
  have hle : ∀ (i j : Fin n), (i : ℕ) < k → i ≤ j → i ≤ ρ j := fun i j hi hij => by
    by_cases hj : (j : ℕ) < k
    · rw [hfix' j hj]; exact hij
    · exact Fin.le_def.2 (le_trans hi.le (hmap' j (not_lt.1 hj)))
  refine ⟨fun i j => ⟨fun hi hij => ?_, fun hj hji => ?_, fun hi hj => ?_⟩,
    fun i j hj hji => ?_⟩
  · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i (ρ j)).1 hi (hle i j hi hij)
    refine ⟨o, p, hnd, ho, fun r hr => ?_, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, hfix i hi, hfix r (by omega), hfix' r (by omega)]
      exact hp r hr
    · simp only [submatrix_apply, hfix i hi]
      exact hsum
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hx⟩ := (hS (τ i) j).2.1 hj (hlt i j hj hji)
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, ?_, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, hfix r (by omega), hfix' r (by omega), hfix' j hj]
      exact hp r hr
    · simp only [submatrix_apply, hfix' j hj]
      exact hsum
    · simp only [submatrix_apply, hfix j hj, hfix' j hj]
      exact hx
  · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS (τ i) (ρ j)).2.2 (hmap i hi) (hmap' j hj)
    refine ⟨o, p, hnd, ho, fun r hr => ?_, hsum⟩
    simp only [submatrix_apply, hfix r ((ho r).1 hr), hfix' r ((ho r).1 hr)]
    exact hp r hr
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hdom, hx⟩ := hD (τ i) j hj (hlt i j hj hji)
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, ?_, ?_, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, hfix r (by omega), hfix' r (by omega), hfix' j hj]
      exact hp r hr
    · simp only [submatrix_apply, hfix' j hj]
      exact hsum
    · simp only [submatrix_apply, hfix j hj, hfix' j hj]
      exact hdom
    · simp only [submatrix_apply, hfix j hj, hfix' j hj]
      exact hx

/-- The rows of $U$ finished by complete pivoting are dominated by their diagonal entry:
$|s_{ij}| \le |s_{ii}|$ for $i < k$ and $j \ge i$. -/
def RowDom (k : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, (i : ℕ) < k → i ≤ j → |S i j| ≤ |S i i|

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One step $k$ of Algorithm 3.4.3: the search for an entry of maximal modulus in the trailing
block (`Matrix.completePivotEntry`, with exact comparisons), the row and column interchanges,
and, if the new pivot is nonzero, the updates of Algorithm 3.2.1. -/
noncomputable def completePivotingStep {n : ℕ} (k : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n)) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n)) :=
  if st.1.submatrix (Equiv.swap k (completePivotEntry st.1 k).1)
      (Equiv.swap k (completePivotEntry st.1 k).2) k k ≠ 0 then do
    let S ← outerProductStep rnd k (st.1.submatrix (Equiv.swap k (completePivotEntry st.1 k).1)
      (Equiv.swap k (completePivotEntry st.1 k).2))
    pure (S, Function.update st.2.1 k (completePivotEntry st.1 k).1,
      Function.update st.2.2 k (completePivotEntry st.1 k).2)
  else
    pure (st.1.submatrix (Equiv.swap k (completePivotEntry st.1 k).1)
        (Equiv.swap k (completePivotEntry st.1 k).2),
      Function.update st.2.1 k (completePivotEntry st.1 k).1,
      Function.update st.2.2 k (completePivotEntry st.1 k).2)

/-- **Algorithm 3.4.3** of [golub2013matrix] (Outer Product LU with Complete Pivoting). The
algorithm computes the factorization $PAQ^T = LU$, where $P$ is a permutation matrix encoded by
$\mathrm{rowpiv}(1{:}n-1)$, $Q$ is a permutation matrix encoded by $\mathrm{colpiv}(1{:}n-1)$,
$L$ is unit lower triangular with $|\ell_{ij}| \le 1$, and $U$ is upper triangular.
```
for k = 1:n-1
    Determine μ with k ≤ μ ≤ n and λ with k ≤ λ ≤ n so
        |A(μ,λ)| = max{|A(i,j)| : i = k:n, j = k:n}
    rowpiv(k) = μ;  A(k,1:n) ↔ A(μ,1:n)
    colpiv(k) = λ;  A(1:n,k) ↔ A(1:n,λ)
    if A(k,k) ≠ 0
        ρ = k+1:n
        A(ρ,k) = A(ρ,k)/A(k,k)
        A(ρ,ρ) = A(ρ,ρ) - A(ρ,k) A(k,ρ)
    end
end
```
The program returns the packed matrix, $\mathrm{rowpiv}$ and $\mathrm{colpiv}$.

Both pivot vectors are initially the identity. Each step is
`GolubVanLoan.Chapter03.completePivotingStep`. -/
noncomputable def algorithm_3_4_3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n)) :=
  (List.finRange n).foldlM (fun st k => completePivotingStep rnd k st) (A, fun k => k, fun k => k)

/-- The invariant of Algorithm 3.4.3 after $k$ steps on the state
$(S, \mathrm{rowpiv}, \mathrm{colpiv})$: $S$ satisfies `GolubVanLoan.Chapter03.PivStageInv` for
$A$ with its rows and columns permuted by the first $k$ interchanges, and its finished rows are
dominated by their diagonal entries (`GolubVanLoan.Chapter03.RowDom`). -/
def Alg343Inv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n)) : Prop :=
  PivStageInv fp (A.submatrix (pivPermUpTo st.2.1 k) (pivPermUpTo st.2.2 k)) k st.1 ∧
    RowDom k st.1

/-- The interchange of $k$ with an index $\mu \ge k$ fixes the indices before $k$ and maps the
indices from $k$ on among themselves. -/
theorem swap_fix_and_map {k μ : Fin n} (hkμ : k ≤ μ) :
    (∀ r : Fin n, (r : ℕ) < k → Equiv.swap k μ r = r) ∧
      ∀ i : Fin n, (k : ℕ) ≤ i → (k : ℕ) ≤ (Equiv.swap k μ i : ℕ) := by
  refine ⟨fun r hr => Equiv.swap_apply_of_ne_of_ne (fun h => by rw [h] at hr; exact lt_irrefl _ hr)
      fun h => by rw [h] at hr; exact absurd (Fin.le_def.1 hkμ) (not_le.2 hr), fun i hi => ?_⟩
  rcases eq_or_ne i k with rfl | hik
  · rw [Equiv.swap_apply_left]; exact hkμ
  rcases eq_or_ne i μ with rfl | hiμ
  · rw [Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne hik hiμ]; exact hi

/-- After setting $\mathrm{piv}(k) = \mu$, the permutation of the first $k + 1$ interchanges is that
of the first $k$, followed by $\operatorname{swap}(k, \mu)$. -/
theorem pivPermUpTo_update (piv : Fin n → Fin n) (k μ : Fin n) :
    pivPermUpTo (Function.update piv k μ) (k + 1) = pivPermUpTo piv k * Equiv.swap k μ := by
  rw [pivPermUpTo_succ, Function.update_self,
    pivPermUpTo_congr (piv := Function.update piv k μ) (piv' := piv) (k := k)
      fun j hj => Function.update_of_ne (fun h => by rw [h] at hj; exact lt_irrefl _ hj) _ _]

/-- In a model that rounds every value to itself, one step of Algorithm 3.4.3 keeps its invariant
`GolubVanLoan.Chapter03.Alg343Inv`. -/
theorem alg343Inv_step (hrefl : ∀ x, fp.Rounds x x) (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n))
    (hst : Alg343Inv fp A k st) (st' : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n))
    (hst' : st' ∈ (completePivotingStep fp.round k st).run) :
    Alg343Inv fp A (k + 1) st' := by
  obtain ⟨S, rp, cp⟩ := st
  obtain ⟨hgood, hrow⟩ := hst
  rw [completePivotingStep] at hst'
  dsimp only at hst' hgood hrow
  have hpiv := isCompletePivot_completePivotEntry S k
  set μ := (completePivotEntry S k).1 with hμ
  set ν := (completePivotEntry S k).2 with hν
  set S₀ := S.submatrix (Equiv.swap k μ) (Equiv.swap k ν) with hS₀
  obtain ⟨hfix, hmap⟩ := swap_fix_and_map (k := k) hpiv.1
  obtain ⟨hfix', hmap'⟩ := swap_fix_and_map (k := k) hpiv.2.1
  have hsub : (A.submatrix (pivPermUpTo rp k) (pivPermUpTo cp k)).submatrix (Equiv.swap k μ)
      (Equiv.swap k ν) = A.submatrix (pivPermUpTo (Function.update rp k μ) (k + 1))
        (pivPermUpTo (Function.update cp k ν) (k + 1)) := by
    rw [pivPermUpTo_update, pivPermUpTo_update, submatrix_submatrix, Equiv.Perm.coe_mul,
      Equiv.Perm.coe_mul]
  have hgood₀ : PivStageInv fp (A.submatrix (pivPermUpTo (Function.update rp k μ) (k + 1))
      (pivPermUpTo (Function.update cp k ν) (k + 1))) k S₀ :=
    hsub ▸ pivStageInv_submatrix₂ hfix hmap hfix' hmap' hgood
  -- the interchanged pivot dominates the trailing block
  have hmax : ∀ i j : Fin n, k ≤ i → k ≤ j → |S₀ i j| ≤ |S₀ k k| := fun i j hi hj => by
    simp only [hS₀, submatrix_apply, Equiv.swap_apply_left]
    have := hpiv.2.2 (Equiv.swap k μ i) (Equiv.swap k ν j)
      (Fin.le_def.2 (hmap i (Fin.le_def.1 hi))) (Fin.le_def.2 (hmap' j (Fin.le_def.1 hj)))
    simpa only [Real.norm_eq_abs] using this
  have hdom : ∀ i : Fin n, k ≤ i → |S₀ i k| ≤ |S₀ k k| := fun i hi => hmax i k hi le_rfl
  have hrow₀ : RowDom k S₀ := fun i j hi hij => by
    simp only [hS₀, submatrix_apply, hfix i hi]
    rw [hfix' i hi]
    refine hrow i _ hi ?_
    by_cases hj : (j : ℕ) < k
    · rw [hfix' j hj]; exact hij
    · exact Fin.le_def.2 (le_trans hi.le (hmap' j (not_lt.1 hj)))
  -- the new row `k` and the old rows are unchanged by the step
  have hrow' : ∀ S' : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → S' i j = S₀ i j) → RowDom (k + 1) S' :=
    fun S' hS' i j hi hij => by
      have hi' : ¬ (k < i) := fun h => by have := Fin.lt_def.1 h; omega
      rw [hS' i j fun h => hi' h.1, hS' i i fun h => hi' h.1]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact hrow₀ i j hi hij
      · have hik : i = k := Fin.ext hi
        subst hik
        exact hmax i j le_rfl hij
  split_ifs at hst' with h0
  · rw [SetM.mem_run_bind] at hst'
    obtain ⟨S', hS', hst'⟩ := hst'
    rw [SetM.mem_run_pure] at hst'
    subst hst'
    obtain ⟨h₁, h₂, h₃⟩ := mem_run_outerProductStep k hS'
    exact ⟨pivStageInv_step k hgood₀ hdom h₁ h₂ h₃, hrow' S' h₁⟩
  · rw [SetM.mem_run_pure] at hst'
    subst hst'
    exact ⟨pivStageInv_step_of_zero k hgood₀ hdom (not_not.1 h0) (Or.inl hrefl),
      hrow' S₀ fun _ _ _ => rfl⟩

/-- The exact run of Algorithm 3.4.3 is one of its runs in the exact rounding model. -/
private theorem algorithm_3_4_3_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_3_4_3 pure A) ∈ (algorithm_3_4_3 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_4_3, completePivotingStep, outerProductStep, pure_bind, ite_pure,
    List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- **Algorithm 3.4.3** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
be arbitrary, and let $(F, \mathrm{rowpiv}, \mathrm{colpiv})$ be the output of Algorithm 3.4.3
in exact arithmetic. Let $P$ and $Q$ be the permutation matrices encoded by $\mathrm{rowpiv}$
and $\mathrm{colpiv}$, $L$ the unit lower triangular matrix stored below the diagonal of $F$,
and $U$ the upper triangular matrix stored on and above it. Then
$$PAQ^T = LU, \qquad |\ell_{ij}| \le 1, \qquad |u_{ij}| \le |u_{ii}| \text{ for all } i, j.$$

The bound $|u_{ij}| \le |u_{ii}|$ is the property of P3.4.2. The source writes $PAQ^T$ in
Algorithm 3.4.3 and $PAQ$ in §3.4.7. Here $P$ is `(pivPerm rowpiv).permMatrix ℝ`, $Q^T$ is
`((pivPerm colpiv)⁻¹).permMatrix ℝ`, and the factors are `GolubVanLoan.Chapter03.packedL F` and
`GolubVanLoan.Chapter03.packedU F`. -/
theorem algorithm_3_4_3_spec (A : Matrix (Fin n) (Fin n) ℝ) :
    IsLU ((pivPerm (Id.run (algorithm_3_4_3 pure A)).2.1).permMatrix ℝ * A *
          ((pivPerm (Id.run (algorithm_3_4_3 pure A)).2.2)⁻¹).permMatrix ℝ)
        (packedL (Id.run (algorithm_3_4_3 pure A)).1)
        (packedU (Id.run (algorithm_3_4_3 pure A)).1) ∧
      (∀ i j, |packedL (Id.run (algorithm_3_4_3 pure A)).1 i j| ≤ 1) ∧
      ∀ i j, |packedU (Id.run (algorithm_3_4_3 pure A)).1 i j| ≤
        |packedU (Id.run (algorithm_3_4_3 pure A)).1 i i| := by
  have hinv := SetM.forall_mem_run_foldlM_finRange (Alg343Inv (RoundingModel.exact ℝ) A)
    ⟨⟨luStageInv_zero _, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun k st hst st' hst' => alg343Inv_step (fun _ => rfl) A k st hst st' hst') _
    (algorithm_3_4_3_mem_exact A)
  obtain ⟨hgood, hrow⟩ := hinv
  obtain ⟨hLU, hL⟩ := isLU_of_pivStageInv_exact hgood
  refine ⟨by rw [permMatrix_mul_mul_permMatrix]; exact hLU, hL, fun i j => ?_⟩
  rcases le_or_gt i j with hij | hji
  · rw [packedU_apply_of_le _ hij, packedU_apply_of_le _ le_rfl]
    exact hrow i j i.2 hij
  · rw [packedU_apply_of_lt _ hji, abs_zero]
    exact abs_nonneg _

/-- **Section 3.4.6** of [golub2013matrix], the solve after Algorithm 3.4.3: Step 1, solve $Lz = Pb$
for $z$; Step 2, solve $Uy = z$ for $y$; Step 3, set $x = Q^T y$. Given the packed factor $F$,
$\mathrm{rowpiv}$, $\mathrm{colpiv}$ and $b$, the program returns $x$.

The solves are the row-oriented substitutions of §3.1, and the permutations are the loops
`GolubVanLoan.Chapter03.applyPiv` and `GolubVanLoan.Chapter03.applyPivRev`. -/
noncomputable def solvePLUQ {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (rowpiv colpiv : Fin n → Fin n)
    (b : Fin n → ℝ) : M (Fin n → ℝ) := do
  let z ← algorithm_3_1_1 rnd (packedL F) (applyPiv rowpiv b)
  let y ← algorithm_3_1_2 rnd (packedU F) z
  pure (applyPivRev colpiv y)

/-- Gaussian elimination with complete pivoting followed by the solve: Algorithm 3.4.3 on $A$, then
`GolubVanLoan.Chapter03.solvePLUQ` with $b$. -/
noncomputable def solveGECP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let out ← algorithm_3_4_3 rnd A
  solvePLUQ rnd out.1 out.2.1 out.2.2 b

/-- **Section 3.4.6** of [golub2013matrix], exact correctness of the solve with complete pivoting.
Let $A \in \mathbb{R}^{n \times n}$ be nonsingular and $b \in \mathbb{R}^n$. In exact
arithmetic, Algorithm 3.4.3 followed by Steps 1–3 returns $x$ with
$$Ax = b.$$
-/
theorem solveGECP_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (b : Fin n → ℝ) :
    A *ᵥ Id.run (solveGECP pure A b) = b := by
  obtain ⟨hLU, -, -⟩ := algorithm_3_4_3_spec A
  set out := Id.run (algorithm_3_4_3 pure A)
  set σ := pivPerm out.2.1
  set ρ := pivPerm out.2.2
  rw [permMatrix_mul_mul_permMatrix] at hLU
  have hB : IsUnit (A.submatrix σ ρ) := by
    rw [← permMatrix_mul_mul_permMatrix]
    exact ((isUnit_permMatrix _).mul hA).mul (isUnit_permMatrix _)
  have hd : ∀ i, packedU out.1 i i ≠ 0 := by
    intro i hi
    have hdet : (A.submatrix σ ρ).det = 0 := by
      rw [hLU.det_eq_prod_diag]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    exact ((isUnit_iff_isUnit_det _).1 hB).ne_zero hdet
  have hLd : ∀ i, packedL out.1 i i ≠ 0 := fun i => by
    rw [hLU.isUnitLowerTriangular.diag_eq_one]; exact one_ne_zero
  change A *ᵥ applyPivRev out.2.2 (Id.run (algorithm_3_1_2 pure (packedU out.1)
    (Id.run (algorithm_3_1_1 pure (packedL out.1) (applyPiv out.2.1 b))))) = b
  set z := Id.run (algorithm_3_1_1 pure (packedL out.1) (applyPiv out.2.1 b))
  set y := Id.run (algorithm_3_1_2 pure (packedU out.1) z)
  have hz : packedL out.1 *ᵥ z = b ∘ σ := by
    rw [algorithm_3_1_1_spec hLU.isUnitLowerTriangular.isLowerTriangular hLd,
      (applyPiv_eq _ _).1, permMatrix_mulVec]
  have hy : packedU out.1 *ᵥ y = z := algorithm_3_1_2_spec hLU.isUpperTriangular hd z
  have hBy : A.submatrix σ ρ *ᵥ y = b ∘ σ := by
    rw [← hLU.mul_eq, ← mulVec_mulVec, hy, hz]
  rw [(applyPiv_eq _ _).2, mulVec_transpose, vecMul_permMatrix]
  funext i
  have := congrFun hBy (σ.symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  rw [← this]
  simp only [mulVec, dotProduct, submatrix_apply, Equiv.apply_symm_apply]
  exact (Fintype.sum_equiv ρ _ _ fun j => by simp [ρ]).symm

/-- **Section 3.4.6** of [golub2013matrix], rank revelation. Let $A \in \mathbb{R}^{n \times n}$
have rank $r$, and let $A^{(k)}$ be the matrix after $k$ steps of Gaussian elimination with
complete pivoting in exact arithmetic. Then
$$a^{(r)}_{ij} = 0 \quad \text{for all } i, j \ge r,$$
and for every $k < r$ the pivot that complete pivoting chooses in $A^{(k)}$ is nonzero.

The source says that at the beginning of step $r + 1$, $A(r{+}1{:}n, r{+}1{:}n) = 0$; with
0-based indices this is the block of rows and columns from $r$ on after $r$ steps. The stages
are the backbone's recurrence `Matrix.gemFullPivotStage A Matrix.completePivotEntry`. -/
theorem completePivoting_rank (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ} (hr : A.rank = r) :
    (∀ i j : Fin n, r ≤ (i : ℕ) → r ≤ (j : ℕ) →
        (gemFullPivotStage A completePivotEntry r).1 i j = 0) ∧
      ∀ (k : ℕ) (hk : k < n), k < r →
        (gemFullPivotStage A completePivotEntry k).1
          (completePivotEntry (gemFullPivotStage A completePivotEntry k).1 ⟨k, hk⟩).1
          (completePivotEntry (gemFullPivotStage A completePivotEntry k).1 ⟨k, hk⟩).2 ≠ 0 :=
  gemFullPivotStage_trailing_eq_zero_of_rank A isCompletePivot_completePivotEntry hr

/-- A zero pivot of complete pivoting comes with a zero trailing block: after $k$ steps, a zero
diagonal entry at $p < k$ makes every entry in the rows and columns from $p$ on vanish. -/
private def ZeroPivInv (k : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ p : Fin n, (p : ℕ) < k → S p p = 0 → ∀ i j : Fin n, p ≤ i → p ≤ j → S i j = 0

/-- One step of Algorithm 3.4.3 keeps `ZeroPivInv`. -/
private theorem zeroPivInv_step (k : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n))
    (hst : ZeroPivInv k st.1)
    (st' : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n))
    (hst' : st' ∈ (completePivotingStep fp.round k st).run) :
    ZeroPivInv (k + 1) st'.1 := by
  obtain ⟨S, rp, cp⟩ := st
  rw [completePivotingStep] at hst'
  dsimp only at hst' hst
  have hpiv := isCompletePivot_completePivotEntry S k
  set μ := (completePivotEntry S k).1 with hμ
  set ν := (completePivotEntry S k).2 with hν
  set S₀ := S.submatrix (Equiv.swap k μ) (Equiv.swap k ν) with hS₀
  obtain ⟨hfix, hmap⟩ := swap_fix_and_map (k := k) hpiv.1
  obtain ⟨hfix', hmap'⟩ := swap_fix_and_map (k := k) hpiv.2.1
  have hpres : ∀ (τ : Equiv.Perm (Fin n)), (∀ r : Fin n, (r : ℕ) < k → τ r = r) →
      (∀ i : Fin n, (k : ℕ) ≤ i → (k : ℕ) ≤ (τ i : ℕ)) →
      ∀ p i : Fin n, (p : ℕ) ≤ k → p ≤ i → p ≤ τ i := fun τ hf hm p i hp hi => by
    by_cases hik : (i : ℕ) < k
    · rw [hf i hik]; exact hi
    · exact Fin.le_def.2 (hp.trans (hm i (not_lt.1 hik)))
  have hmax : ∀ i j : Fin n, k ≤ i → k ≤ j → |S₀ i j| ≤ |S₀ k k| := fun i j hi hj => by
    simp only [hS₀, submatrix_apply, Equiv.swap_apply_left]
    have := hpiv.2.2 (Equiv.swap k μ i) (Equiv.swap k ν j)
      (Fin.le_def.2 (hmap i (Fin.le_def.1 hi))) (Fin.le_def.2 (hmap' j (Fin.le_def.1 hj)))
    simpa only [Real.norm_eq_abs] using this
  have hZ₀ : ZeroPivInv (k + 1) S₀ := by
    intro p hp hpp i j hi hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp
    · have hSp : S p p = 0 := by
        simpa only [hS₀, submatrix_apply, hfix p hp, hfix' p hp] using hpp
      exact hst p hp hSp _ _ (hpres _ hfix hmap p i hp.le hi) (hpres _ hfix' hmap' p j hp.le hj)
    · have hpk : p = k := Fin.ext hp
      subst hpk
      have := hmax i j hi hj
      rw [hpp, abs_zero] at this
      exact abs_nonpos_iff.1 this
  split_ifs at hst' with h0
  · rw [SetM.mem_run_bind] at hst'
    obtain ⟨S', hS', hst'⟩ := hst'
    rw [SetM.mem_run_pure] at hst'
    subst hst'
    obtain ⟨h₁, -, -⟩ := mem_run_outerProductStep k hS'
    change ZeroPivInv ((k : ℕ) + 1) S'
    intro p hp hpp
    have hpk : ¬ k < p := fun h => by have := Fin.lt_def.1 h; omega
    rw [h₁ p p fun h => hpk h.1] at hpp
    exact absurd (hZ₀ p hp hpp k k (Fin.le_def.2 (Nat.lt_succ_iff.1 hp))
      (Fin.le_def.2 (Nat.lt_succ_iff.1 hp))) h0
  · rw [SetM.mem_run_pure] at hst'
    subst hst'
    exact hZ₀

/-- The number of indices $i$ of `Fin n` below $p \le n$ is $p$. -/
private theorem card_subtype_val_lt {p : ℕ} (hp : p ≤ n) :
    Fintype.card {i : Fin n // (i : ℕ) < p} = p := by
  rw [Fintype.card_congr (β := Fin p)
    ⟨fun i => ⟨i.1, i.2⟩, fun j => ⟨Fin.castLE hp j, j.2⟩, fun _ => rfl, fun _ => rfl⟩,
    Fintype.card_fin]

/-- An upper triangular matrix whose first $p$ diagonal entries are nonzero and whose rows from $p$
on vanish has rank $p$. -/
private theorem rank_eq_of_upperTriangular {U : Matrix (Fin n) (Fin n) ℝ} {p : ℕ} (hp : p ≤ n)
    (hU : U.IsUpperTriangular) (hd : ∀ i : Fin n, (i : ℕ) < p → U i i ≠ 0)
    (hz : ∀ i j : Fin n, p ≤ (i : ℕ) → U i j = 0) : U.rank = p := by
  refine le_antisymm ?_ ?_
  · have hDU : diagonal (fun i : Fin n => if (i : ℕ) < p then (1 : ℝ) else 0) * U = U := by
      ext i j
      rw [diagonal_mul]
      split_ifs with hi
      · rw [one_mul]
      · rw [zero_mul, hz i j (not_lt.1 hi)]
    rw [← hDU]
    refine (rank_mul_le_left _ _).trans ?_
    rw [rank_diagonal]
    refine le_of_eq ((Fintype.card_congr (Equiv.subtypeEquivRight fun i => ?_)).trans
      (card_subtype_val_lt hp))
    split_ifs with h <;> simp [h]
  · have hsub : (U.submatrix (Fin.castLE hp) (Fin.castLE hp)).IsUpperTriangular :=
      fun i j hij => hU (show Fin.castLE hp j < Fin.castLE hp i from hij)
    have hdet : IsUnit (U.submatrix (Fin.castLE hp) (Fin.castLE hp)) := by
      rw [isUnit_iff_isUnit_det, det_of_isUpperTriangular hsub]
      exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hd _ i.2)
    have := rank_submatrix_le U (Fin.castLE hp) (Fin.castLE hp)
    rwa [rank_of_isUnit _ hdet, Fintype.card_fin] at this

/-- **Section 3.4.6** of [golub2013matrix], rank revelation by complete pivoting, in factored form.
Let $A \in \mathbb{R}^{n \times n}$ have rank $r$, and let $L$ and $U$ be the factors of
$PAQ^T = LU$ computed by Algorithm 3.4.3 in exact arithmetic. Then
$$u_{ij} = 0 \text{ for } i \ge r, \qquad \ell_{ij} = \delta_{ij} \text{ for } j \ge r, \qquad
  u_{ii} \neq 0 \text{ for } i < r.$$
That is,
$$PAQ^T = \begin{bmatrix} L_{11} & 0 \\ L_{21} & I_{n-r} \end{bmatrix} \begin{bmatrix} U_{11} &
  U_{12} \\ 0 & 0 \end{bmatrix}$$
with $L_{11}$ and $U_{11}$ of order $r$ and $U_{11}$ nonsingular.

The factors are those of `GolubVanLoan.Chapter03.algorithm_3_4_3_spec`. -/
theorem completePivoting_rank_factorization (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ i j : Fin n, A.rank ≤ (i : ℕ) → packedU (Id.run (algorithm_3_4_3 pure A)).1 i j = 0) ∧
      (∀ i j : Fin n, A.rank ≤ (j : ℕ) →
        packedL (Id.run (algorithm_3_4_3 pure A)).1 i j = if i = j then 1 else 0) ∧
      ∀ i : Fin n, (i : ℕ) < A.rank → packedU (Id.run (algorithm_3_4_3 pure A)).1 i i ≠ 0 := by
  set F := (Id.run (algorithm_3_4_3 pure A)).1 with hF
  have hZ : ZeroPivInv n F :=
    SetM.forall_mem_run_foldlM_finRange (fun k st => ZeroPivInv k st.1)
      (fun _ h => absurd h (Nat.not_lt_zero _))
      (fun k st hst st' hst' => zeroPivInv_step (fp := RoundingModel.exact ℝ) k st hst st' hst')
      _ (algorithm_3_4_3_mem_exact A)
  obtain ⟨hLU, -, -⟩ := algorithm_3_4_3_spec A
  -- the first zero pivot, or `n`
  have hex : ∃ m, m = n ∨ ∃ h : m < n, F ⟨m, h⟩ ⟨m, h⟩ = 0 := ⟨n, Or.inl rfl⟩
  classical
  set p := Nat.find hex with hpdef
  have hpn : p ≤ n := Nat.find_min' hex (Or.inl rfl)
  have hd : ∀ i : Fin n, (i : ℕ) < p → F i i ≠ 0 := fun i hi h0 =>
    Nat.find_min hex hi (Or.inr ⟨i.2, h0⟩)
  have hblock : ∀ i j : Fin n, p ≤ (i : ℕ) → p ≤ (j : ℕ) → F i j = 0 := by
    intro i j hi hj
    rcases Nat.find_spec hex with h | ⟨hp, h0⟩
    · have := i.2; omega
    · exact hZ ⟨p, hp⟩ hp h0 i j (Fin.le_def.2 hi) (Fin.le_def.2 hj)
  have hUz : ∀ i j : Fin n, p ≤ (i : ℕ) → packedU F i j = 0 := fun i j hi => by
    rcases le_or_gt i j with hij | hji
    · rw [packedU_apply_of_le _ hij]
      exact hblock i j hi (hi.trans (Fin.le_def.1 hij))
    · exact packedU_apply_of_lt _ hji
  have hUd : ∀ i : Fin n, (i : ℕ) < p → packedU F i i ≠ 0 := fun i hi => by
    rw [packedU_apply_of_le _ le_rfl]; exact hd i hi
  have hrank : A.rank = p := by
    have hL : IsUnit (packedL F).det := by
      rw [det_of_isLowerTriangular _ hLU.isUnitLowerTriangular.isLowerTriangular]
      simp [packedL_apply_self]
    have h1 := hLU.mul_eq
    have h2 : ((pivPerm (Id.run (algorithm_3_4_3 pure A)).2.1).permMatrix ℝ * A *
        ((pivPerm (Id.run (algorithm_3_4_3 pure A)).2.2)⁻¹).permMatrix ℝ).rank = A.rank := by
      rw [rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1
          (isUnit_permMatrix _)),
        rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 (isUnit_permMatrix _))]
    rw [← h2, ← h1, rank_mul_eq_right_of_isUnit_det _ _ hL]
    exact rank_eq_of_upperTriangular hpn hLU.isUpperTriangular hUd hUz
  rw [hrank]
  refine ⟨hUz, fun i j hj => ?_, hUd⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [packedL_apply_of_lt' _ hij, ite_eq_right hij.ne]
  · rw [packedL_apply_self, ite_eq_left rfl]
  · rw [packedL_apply_of_lt _ hji, ite_eq_right hji.ne']
    exact hblock i j (hj.trans (Fin.le_def.1 hji.le)) hj

/-- The bound of (3.4.10) holds for every entry of the matrix after $k$ steps of complete pivoting,
and the entries below the diagonal in the eliminated columns are zero. -/
private theorem frozen_aux (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    (∀ i j : Fin n, |(gemFullPivotStage A completePivotEntry k).1 i j| ≤
        wilkinsonGrowthBound (k + 1) * A.supAbs) ∧
      ∀ i j : Fin n, (j : ℕ) < k → j < i →
        (gemFullPivotStage A completePivotEntry k).1 i j = 0 := by
  induction k with
  | zero =>
    refine ⟨fun i j => ?_, fun _ j h => absurd h (Nat.not_lt_zero _)⟩
    exact abs_gemFullPivotStage_le_wilkinson A isCompletePivot_completePivotEntry
      (Nat.zero_lt_of_lt i.2) (Nat.zero_le _) (Nat.zero_le _)
  | succ k ih =>
    obtain ⟨hb, hz⟩ := ih
    have hW : wilkinsonGrowthBound (k + 1) * A.supAbs ≤
        wilkinsonGrowthBound (k + 1 + 1) * A.supAbs :=
      mul_le_mul_of_nonneg_right (wilkinsonGrowthBound_mono (by omega)) (supAbs_nonneg A)
    have hnn : 0 ≤ wilkinsonGrowthBound (k + 1 + 1) * A.supAbs :=
      mul_nonneg (wilkinsonGrowthBound_nonneg _) (supAbs_nonneg A)
    by_cases hk : k < n
    · rw [gemFullPivotStage_succ_of_lt A _ hk]
      dsimp only
      set S := (gemFullPivotStage A completePivotEntry k).1 with hS
      set K : Fin n := ⟨k, hk⟩
      have hpiv := isCompletePivot_completePivotEntry S K
      set μ := (completePivotEntry S K).1
      set ν := (completePivotEntry S K).2
      have hR : gemFullPivotRowSwap A completePivotEntry k hk = Equiv.swap K μ := rfl
      have hC : gemFullPivotColSwap A completePivotEntry k hk = Equiv.swap K ν := rfl
      rw [hR, hC]
      obtain ⟨hfix, hmap⟩ := swap_fix_and_map (k := K) hpiv.1
      obtain ⟨hfix', hmap'⟩ := swap_fix_and_map (k := K) hpiv.2.1
      set S' := S.submatrix (Equiv.swap K μ) (Equiv.swap K ν) with hS'
      -- the pivot dominates column `k` below it
      have hcolk : ∀ i : Fin n, K ≤ i → |S' i K| ≤ |S' K K| := fun i hi => by
        simp only [hS', submatrix_apply, Equiv.swap_apply_left]
        simpa only [Real.norm_eq_abs, Equiv.swap_apply_left] using hpiv.2.2 _ _
          (Fin.le_def.2 (hmap i (Fin.le_def.1 hi))) (Fin.le_def.2 (hmap' K le_rfl))
      -- the eliminated columns stay zero below the diagonal after the interchanges
      have hz' : ∀ i j : Fin n, (j : ℕ) < k → j < i → S' i j = 0 := fun i j hj hji => by
        simp only [hS', submatrix_apply, hfix' j hj]
        refine hz _ j hj ?_
        by_cases hik : (i : ℕ) < k
        · rw [hfix i hik]; exact hji
        · exact Fin.lt_def.2 (lt_of_lt_of_le hj (hmap i (not_lt.1 hik)))
      have hb' : ∀ i j : Fin n, |S' i j| ≤ wilkinsonGrowthBound (k + 1) * A.supAbs :=
        fun i j => hb _ _
      -- the new column `k` vanishes below the pivot
      have hcol0 : ∀ i : Fin n, K < i → elimStep S' K i K = 0 := fun i hi => by
        rw [elimStep_apply_of_lt _ hi]
        by_cases h0 : S' K K = 0
        · have := hcolk i hi.le
          rw [h0, abs_zero] at this
          rw [abs_nonpos_iff.1 this, h0]
          simp
        · field_simp
          ring
      have hzero : ∀ i j : Fin n, (j : ℕ) < k + 1 → j < i → elimStep S' K i j = 0 := by
        intro i j hj hji
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · by_cases hki : K < i
          · rw [elimStep_apply_of_lt _ hki, hz' i j hj hji,
              hz' K j hj (Fin.lt_def.2 (by simpa [K] using hj))]
            ring
          · rw [elimStep_apply_of_not_lt _ hki]
            exact hz' i j hj hji
        · have hjK : j = K := Fin.ext hj
          subst hjK
          exact hcol0 i hji
      refine ⟨fun i j => ?_, hzero⟩
      by_cases hki : K < i
      · by_cases hkj : k + 1 ≤ (j : ℕ)
        · have := abs_gemFullPivotStage_le_wilkinson A isCompletePivot_completePivotEntry
            (k := k + 1) (lt_of_le_of_lt (Fin.lt_def.1 hki) i.2) (Fin.lt_def.1 hki) hkj
            (i := i) (j := j)
          rwa [gemFullPivotStage_succ_of_lt A _ hk, hR, hC] at this
        · by_cases hji : j < i
          · rw [hzero i j (by omega) hji, abs_zero]; exact hnn
          · exact absurd (lt_of_le_of_lt (by omega : (j : ℕ) ≤ k) (Fin.lt_def.1 hki))
              (fun h => hji (Fin.lt_def.2 h))
      · rw [elimStep_apply_of_not_lt _ hki]
        exact (hb' i j).trans hW
    · rw [gemFullPivotStage_succ_of_le A _ (not_lt.1 hk)]
      refine ⟨fun i j => (hb i j).trans hW, fun i j hj hji => hz i j ?_ hji⟩
      have := j.2
      omega

/-- **Equation (3.4.10)** of [golub2013matrix] (Wilkinson's bound for complete pivoting). Let
$A \in \mathbb{R}^{n \times n}$ and $k \in \mathbb{N}$, and let $A^{(k)}$ be the matrix after
$k$ steps of Gaussian elimination with complete pivoting in exact arithmetic. Then for all
$i, j$
$$|a^{(k)}_{ij}| \le f(k + 1) \max_{p,q} |a_{pq}|, \qquad f(m) = m^{1/2} \left(2 \cdot 3^{1/2}
  \cdots m^{1/(m-1)}\right)^{1/2}.$$

**Correction.** The source prints the bound with $f(k)$ in place of $f(k + 1)$. This is false
for $k = 1$: for $A = \begin{bmatrix} 1 & 1 \\ 1 & -1 \end{bmatrix}$ one step produces an entry
of modulus $2 > 1 = f(1)$. With the indexing of (3.2.3), where $A^{(k)}$ is the matrix after
$k - 1$ steps, the printed form is right.

The function $f$ is `Matrix.wilkinsonGrowthBound`. The largest modulus of an entry of $A$ is
`Matrix.supAbs A`. On the trailing block the bound is Wilkinson's theorem
`Matrix.abs_gemFullPivotStage_le_wilkinson`.
An entry outside the trailing block is either an eliminated entry, which is zero because a zero
pivot of complete pivoting comes with a zero column, or in a row frozen at an earlier step,
where the smaller bound holds (`Matrix.wilkinsonGrowthBound_mono`). -/
theorem equation_3_4_10 (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (i j : Fin n) :
    |(gemFullPivotStage A completePivotEntry k).1 i j| ≤
      wilkinsonGrowthBound (k + 1) * A.supAbs :=
  (frozen_aux A k).1 i j

end Complete

/-! ### The exact run of Algorithm 3.4.1 is the backbone's recurrence -/

section Simulation341

variable {n : ℕ}

/-- The partial pivoting row of column $k$ depends only on the entries of column $k$ from row $k$
on. -/
private theorem partialPivotRow_congr {M M' : Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (h : ∀ r, k ≤ r → M r k = M' r k) : partialPivotRow M k = partialPivotRow M' k := by
  refine le_antisymm (partialPivotRow_le M k (le_partialPivotRow M' k) fun r' hr' => ?_)
    (partialPivotRow_le M' k (le_partialPivotRow M k) fun r' hr' => ?_)
  · rw [h r' hr', h _ (le_partialPivotRow M' k)]
    exact norm_apply_le_partialPivotRow M' k hr'
  · rw [← h r' hr', ← h _ (le_partialPivotRow M k)]
    exact norm_apply_le_partialPivotRow M k hr'

/-- Gaussian elimination without pivoting commutes with a permutation of the rows that fixes the
indices before the stage. -/
private theorem gemStage_submatrix_of_forall_lt (B : Matrix (Fin n) (Fin n) ℝ)
    {τ : Equiv.Perm (Fin n)} {c : ℕ} (hτ : ∀ i : Fin n, (i : ℕ) < c → τ i = i) :
    gemStage (B.submatrix τ id) c = (gemStage B c).submatrix τ id := by
  induction c with
  | zero => rfl
  | succ c ih =>
    by_cases hc : c < n
    · rw [gemStage_succ_of_lt _ hc, gemStage_succ_of_lt _ hc, ih fun i hi => hτ i (by omega)]
      exact elimStep_submatrix_of_forall_le _ fun i hi => hτ i (by
        have : (i : ℕ) ≤ c := Fin.le_def.1 hi; omega)
    · rw [gemStage_succ_of_le _ (not_lt.1 hc), gemStage_succ_of_le _ (not_lt.1 hc),
        ih fun i hi => hτ i (by omega)]

/-- The stages of elimination without pivoting on $A$ with the first $m$ interchanges of partial
pivoting applied are the pivoted stages with their rows permuted by the interchanges
$c, \dots, m - 1$. -/
private theorem gemStage_submatrix_gemPivotStage (A : Matrix (Fin n) (Fin n) ℝ) {m : ℕ}
    (hm : m ≤ n) {c : ℕ} (hc : c ≤ m) :
    gemStage (A.submatrix (gemPivotStage A partialPivotRow m).2 id) c =
      (gemPivotStage A partialPivotRow c).1.submatrix
        ((gemPivotStage A partialPivotRow c).2⁻¹ * (gemPivotStage A partialPivotRow m).2) id := by
  have hpiv : ∀ (M : Matrix (Fin n) (Fin n) ℝ) k, k ≤ partialPivotRow M k :=
    fun M k => le_partialPivotRow M k
  induction m generalizing c with
  | zero =>
    obtain rfl : c = 0 := by omega
    simp
  | succ m ih =>
    have hmn : m < n := by omega
    have hσ : (gemPivotStage A partialPivotRow (m + 1)).2 =
        (gemPivotStage A partialPivotRow m).2 * gemPivotSwap A partialPivotRow m hmn := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hmn]
    have hsub : A.submatrix (gemPivotStage A partialPivotRow (m + 1)).2 id =
        (A.submatrix (gemPivotStage A partialPivotRow m).2 id).submatrix
          (gemPivotSwap A partialPivotRow m hmn) id := by
      rw [hσ, submatrix_submatrix, Equiv.Perm.coe_mul]
      rfl
    have hfix : ∀ i : Fin n, (i : ℕ) < m → gemPivotSwap A partialPivotRow m hmn i = i :=
      fun i hi => by
        have := gemPivotStage_snd_inv_mul_apply A partialPivotRow hpiv (Nat.le_succ m) hi
        rwa [hσ, ← mul_assoc, inv_mul_cancel, one_mul] at this
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hc) with hc' | hc'
    · rw [hsub, gemStage_submatrix_of_forall_lt _ fun i hi => hfix i (by omega),
        ih (by omega) (by omega), submatrix_submatrix, hσ, ← mul_assoc]
      rfl
    · subst hc'
      rw [gemStage_succ_of_lt _ hmn, hsub,
        gemStage_submatrix_of_forall_lt _ fun i hi => hfix i hi, ih (by omega) le_rfl,
        inv_mul_cancel, gemPivotStage_succ_of_lt A partialPivotRow hmn]
      simp only [Equiv.Perm.coe_one, submatrix_id_id, inv_mul_cancel]

/-- The simulation invariant of Algorithm 3.4.1 in exact arithmetic after $k$ steps: the
interchanges are those of the backbone's recurrence, the rows and columns from $k$ on hold the
pivoted stage, and the finished multipliers are those of elimination without pivoting on the
matrix with the interchanges so far applied. -/
private def Sim341 (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) : Prop :=
  pivPermUpTo st.2 k = (gemPivotStage A partialPivotRow k).2 ∧
    ∀ i c : Fin n, st.1 i c = if (c : ℕ) < k ∧ c < i then
      gemLower (A.submatrix (gemPivotStage A partialPivotRow k).2 id) i c
      else (gemPivotStage A partialPivotRow k).1 i c

/-- One step of Algorithm 3.4.1 in the exact model keeps the simulation invariant. -/
private theorem sim341_step (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) (hst : Sim341 A k st)
    (st' : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n))
    (hst' : st' ∈ (if st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id k k ≠ 0 then do
      let A ← outerProductStep (RoundingModel.exact ℝ).round k
        (st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id)
      pure (A, Function.update st.2 k (partialPivotRow st.1 k))
    else
      pure (st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id,
        Function.update st.2 k (partialPivotRow st.1 k)) : SetM _).run) :
    Sim341 A (k + 1) st' := by
  obtain ⟨S, piv⟩ := st
  obtain ⟨hperm, hent⟩ := hst
  dsimp only at hst' hperm hent
  set Gk := (gemPivotStage A partialPivotRow k).1 with hGk
  have hcolk : ∀ r : Fin n, S r k = Gk r k := fun r => by
    rw [hent r k, ite_eq_right fun h => lt_irrefl _ h.1]
  have hμ : partialPivotRow S k = partialPivotRow Gk k :=
    partialPivotRow_congr fun r _ => hcolk r
  rw [hμ] at hst'
  set μ := partialPivotRow Gk k with hμdef
  set τ := Equiv.swap k μ with hτ
  have hkμ : k ≤ μ := le_partialPivotRow Gk k
  obtain ⟨hfix, hmap⟩ := swap_fix_and_map (k := k) hkμ
  have hswap : gemPivotSwap A partialPivotRow k k.2 = τ := rfl
  have hG1 : gemPivotStage A partialPivotRow ((k : ℕ) + 1) =
      (elimStep (Gk.submatrix τ id) k, (gemPivotStage A partialPivotRow k).2 * τ) := by
    rw [gemPivotStage_succ_of_lt A partialPivotRow k.2, hswap]
  have hperm' : pivPermUpTo (Function.update piv k μ) ((k : ℕ) + 1) =
      (gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2 := by
    rw [pivPermUpTo_update, hperm, hG1]
  -- the multipliers of the matrix with the interchanges so far applied
  set B := A.submatrix (gemPivotStage A partialPivotRow k).2 id with hB
  set B' := A.submatrix (gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2 id with hB'
  have hBB' : B' = B.submatrix τ id := by
    rw [hB', hB, hG1, submatrix_submatrix, Equiv.Perm.coe_mul]
    rfl
  have hlowold : ∀ i c : Fin n, (c : ℕ) < k → c < i →
      gemLower B' i c = gemLower B (τ i) c := fun i c hc hci => by
    have hci' : c < τ i := by
      by_cases hik : (i : ℕ) < k
      · rw [hfix i hik]; exact hci
      · exact Fin.lt_def.2 (lt_of_lt_of_le hc (hmap i (not_lt.1 hik)))
    have hs : gemStage B' c = (gemStage B c).submatrix τ id := by
      rw [hBB']
      exact gemStage_submatrix_of_forall_lt B fun r hr => hfix r (by omega)
    simp only [gemLower, of_apply, hci, hci', ↓reduceIte, hs, submatrix_apply, id]
    rw [hfix c hc]
  have hlowk : ∀ i : Fin n, k < i → gemLower B' i k = Gk (τ i) k / Gk (τ k) k := fun i hi => by
    have hs : gemStage B' k = Gk.submatrix τ id := by
      rw [hB', gemStage_submatrix_gemPivotStage A (by have := k.2; omega) (Nat.le_succ _), hG1]
      congr 1
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    simp only [gemLower, of_apply, hi, ↓reduceIte, hs, submatrix_apply, id]
  -- the column `k` below the pivot, in the zero-pivot case
  have hzero : Gk (τ k) k = 0 → ∀ i : Fin n, k ≤ i → Gk (τ i) k = 0 := fun h0 i hi => by
    have := norm_apply_le_partialPivotRow Gk k (r := τ i) (Fin.le_def.2 (hmap i (Fin.le_def.1 hi)))
    rw [← hμdef, show μ = τ k from (Equiv.swap_apply_left k μ).symm, h0, norm_zero] at this
    exact norm_le_zero_iff.1 this
  have hS₀ : ∀ i c : Fin n, S.submatrix τ id i c = S (τ i) c := fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · split_ifs at hst' with h0
    · rw [SetM.mem_run_bind] at hst'
      obtain ⟨S', -, hst'⟩ := hst'
      rw [SetM.mem_run_pure] at hst'
      subst hst'
      exact hperm'
    · rw [SetM.mem_run_pure] at hst'
      subst hst'
      exact hperm'
  -- the entries
  have hmain : ∀ S' : Matrix (Fin n) (Fin n) ℝ,
      (∀ i c, ¬ (k < i ∧ (c = k ∨ k < c)) → S' i c = S (τ i) c) →
      (∀ i, k < i → S' i k = Gk (τ i) k / Gk (τ k) k) →
      (∀ i c, k < i → k < c → S' i c = Gk (τ i) c - S' i k * Gk (τ k) c) →
      ∀ i c : Fin n, S' i c = if (c : ℕ) < (k : ℕ) + 1 ∧ c < i then gemLower B' i c
        else (gemPivotStage A partialPivotRow ((k : ℕ) + 1)).1 i c := by
    intro S' h₁ h₂ h₃ i c
    rw [hG1]
    dsimp only
    by_cases hki : k < i
    · rcases lt_trichotomy c k with hck | rfl | hkc
      · rw [ite_eq_left ⟨by have := Fin.lt_def.1 hck; omega, hck.trans hki⟩,
          h₁ i c fun h => h.2.elim (fun h' => absurd h' (ne_of_lt hck))
            fun h' => absurd hck (not_lt.2 h'.le),
          hlowold i c (Fin.lt_def.1 hck) (hck.trans hki)]
        have hci : c < τ i := by
          by_cases hik : (i : ℕ) < k
          · exact absurd hki (not_lt.2 (Fin.le_def.2 hik.le))
          · exact Fin.lt_def.2 (lt_of_lt_of_le (Fin.lt_def.1 hck) (hmap i (not_lt.1 hik)))
        rw [hent (τ i) c, ite_eq_left ⟨Fin.lt_def.1 hck, hci⟩]
      · rw [ite_eq_left ⟨Nat.lt_succ_self _, hki⟩, h₂ i hki, hlowk i hki]
      · rw [ite_eq_right fun h => absurd (Fin.lt_def.1 hkc) (by omega), h₃ i c hki hkc,
          h₂ i hki, elimStep_apply_of_lt _ hki]
        simp only [submatrix_apply, id]
        ring
    · rw [h₁ i c fun h => hki h.1]
      have hτi : ∀ c : Fin n, c < i → c < τ i := fun c hci => by
        rcases lt_or_eq_of_le (not_lt.1 hki) with hik | rfl
        · rw [hfix i (Fin.lt_def.1 hik)]; exact hci
        · rw [Equiv.swap_apply_left]; exact lt_of_lt_of_le hci hkμ
      by_cases hc : (c : ℕ) < (k : ℕ) + 1 ∧ c < i
      · have hck : (c : ℕ) < k := lt_of_lt_of_le (Fin.lt_def.1 hc.2) (Fin.le_def.1 (not_lt.1 hki))
        rw [ite_eq_left hc, hlowold i c hck hc.2, hent (τ i) c, ite_eq_left ⟨hck, hτi c hc.2⟩]
      · rw [ite_eq_right hc, elimStep_apply_of_not_lt _ hki, submatrix_apply, id, hent (τ i) c,
          ite_eq_right fun h => ?_]
        rcases lt_or_eq_of_le (not_lt.1 hki) with hik | rfl
        · rw [hfix i (Fin.lt_def.1 hik)] at h; exact hc ⟨by omega, h.2⟩
        · exact hc ⟨by have := h.1; omega, Fin.lt_def.2 h.1⟩
  split_ifs at hst' with h0
  · rw [SetM.mem_run_bind] at hst'
    obtain ⟨S', hS', hst'⟩ := hst'
    rw [SetM.mem_run_pure] at hst'
    subst hst'
    obtain ⟨h₁, h₂, h₃⟩ := mem_run_outerProductStep k hS'
    simp only [RoundingModel.exact_rounds_iff] at h₂ h₃
    refine hmain S' (fun i c h => h₁ i c h) (fun i hi => ?_) fun i c hi hc => ?_
    · rw [h₂ i hi]
      simp only [submatrix_apply, id, hcolk]
    · obtain ⟨p, hp, hx⟩ := h₃ i c hi hc
      rw [hx, hp, h₁ k c fun h => lt_irrefl _ h.1]
      simp only [submatrix_apply, id]
      rw [hent (τ i) c, ite_eq_right fun h => absurd (Fin.lt_def.2 h.1) (not_lt.2 hc.le),
        hent (τ k) c, ite_eq_right fun h => absurd (Fin.lt_def.2 h.1) (not_lt.2 hc.le)]
  · rw [SetM.mem_run_pure] at hst'
    subst hst'
    have h0' : Gk (τ k) k = 0 := by
      have := not_not.1 h0
      rwa [submatrix_apply, id, hcolk] at this
    refine hmain _ (fun _ _ _ => rfl) (fun i hi => ?_) fun i c hi hc => ?_
    · simp only [submatrix_apply, id, hcolk, h0', div_zero]
      exact hzero h0' i hi.le
    · simp only [submatrix_apply, id, hcolk, hzero h0' i hi.le, zero_mul, sub_zero]
      rw [hent (τ i) c, ite_eq_right fun h => absurd (Fin.lt_def.2 h.1) (not_lt.2 hc.le)]

/-- **Algorithm 3.4.1** of [golub2013matrix], the exact run is the backbone's partial pivoting
recurrence. Let $A \in \mathbb{R}^{n \times n}$ and let $(F, \mathrm{piv})$ be the output of
Algorithm 3.4.1 in exact arithmetic. Then the permutation encoded by $\mathrm{piv}$ is the
permutation of `Matrix.gemPivotStage A Matrix.partialPivotRow` after $n$ steps, the upper factor
stored in $F$ is the last stage $A^{(n)}$, and the unit lower factor stored in $F$ is the matrix
of multipliers of elimination without pivoting on $PA$.

The search of the program is `Matrix.partialPivotRow`, so the interchanges agree, and the stored
multipliers move with their rows. The factors are `GolubVanLoan.Chapter03.packedU F` and
`GolubVanLoan.Chapter03.packedL F`, and the matrix of multipliers is `Matrix.gemLower`. -/
theorem algorithm_3_4_1_eq_gemPivotStage (A : Matrix (Fin n) (Fin n) ℝ) :
    pivPerm (Id.run (algorithm_3_4_1 pure A)).2 = (gemPivotStage A partialPivotRow n).2 ∧
      packedU (Id.run (algorithm_3_4_1 pure A)).1 = (gemPivotStage A partialPivotRow n).1 ∧
      packedL (Id.run (algorithm_3_4_1 pure A)).1 =
        gemLower ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) := by
  obtain ⟨hperm, hent⟩ := SetM.forall_mem_run_foldlM_finRange (Sim341 A)
    ⟨rfl, fun i c => by simp⟩ (fun k st hst st' hst' => sim341_step A k st hst st' hst') _
    (algorithm_3_4_1_mem_exact A)
  have hU := (equation_3_4_2 A).2
  refine ⟨hperm, ?_, ?_⟩
  · ext i c
    rcases le_or_gt i c with hic | hci
    · rw [packedU_apply_of_le _ hic, hent i c, ite_eq_right fun h => absurd h.2 (not_lt.2 hic)]
    · rw [packedU_apply_of_lt _ hci]
      exact (hU hci).symm
  · rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    ext i c
    rcases lt_trichotomy c i with hci | rfl | hic
    · rw [packedL_apply_of_lt _ hci, hent i c, ite_eq_left ⟨c.2, hci⟩]
    · rw [packedL_apply_self]
      simp [gemLower]
    · rw [packedL_apply_of_lt' _ hic]
      simp [gemLower, not_lt.2 hic.le, hic.ne]

end Simulation341

/-! ### The growth factor (§3.4.5) -/

section Growth

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- **Equation (3.4.8)** of [golub2013matrix], the growth factor. Let
$A \in \mathbb{R}^{n \times n}$, and let $A^{(0)} = A, A^{(1)}, \dots, A^{(n)}$ be the stages
$A^{(k)} = M_k \Pi_k \cdots M_1 \Pi_1 A$ of Gaussian elimination with partial pivoting in exact
arithmetic. The **growth factor** is
$$\rho = \frac{\max_{i,j,k} |a^{(k)}_{ij}|}{\|A\|_\infty}.$$

**Correction.** The source defines $\rho$ on the computed stages $\hat A^{(k)}$. The definition
uses the exact stages, since only these admit bounds ([higham2002accuracy], after Theorem 9.5).

The denominator is $\|A\|_\infty$, as in the source; Wilkinson's growth factor and the
backbone's `Matrix.growthFactor` divide by $\max |a_{ij}|$. For $A = 0$ the value is $0$, by the
convention $x / 0 = 0$. -/
noncomputable def growthFactorStages (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (⨆ k : Fin (n + 1), (partialPivotStage A k).supAbs) / ‖A‖

/-- **Equation (3.4.8)** of [golub2013matrix] and the backbone's growth factor. Let
$A \in \mathbb{R}^{n \times n}$ and let $P$ be the permutation matrix of partial pivoting on
$A$. Then
$$\rho = g(PA) \frac{\max_{i,j} |a_{ij}|}{\|A\|_\infty}, \qquad \rho \le g(PA),$$
where $g$ is the growth factor `Matrix.growthFactor` of elimination without pivoting.

The stages of elimination without pivoting on $PA$ are the pivoted stages with their rows
permuted. The inequality holds because $\max |a_{ij}| \le \|A\|_\infty$. -/
theorem growthFactorStages_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    growthFactorStages A = growthFactor ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) *
        A.supAbs / ‖A‖ ∧
      growthFactorStages A ≤
        growthFactor ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) := by
  set B := (gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A with hB
  have hpiv : ∀ (M : Matrix (Fin n) (Fin n) ℝ) k, k ≤ partialPivotRow M k :=
    fun M k => le_partialPivotRow M k
  -- the stages of `B` are the pivoted stages with permuted rows
  have hstage : ∀ k : ℕ, (gemStage B k).supAbs = (partialPivotStage A k).supAbs := fun k => by
    rw [hB, gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A partialPivotRow hpiv k,
      supAbs_submatrix_equiv]
  have hBA : B.supAbs = A.supAbs := by
    rw [hB, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, supAbs_submatrix_equiv]
  set X := ⨆ k : Fin (n + 1), (partialPivotStage A k).supAbs with hX
  set Y := ⨆ p : Fin n × Fin n × Fin n, |gemStage B p.1 p.2.1 p.2.2| with hY
  have hXnn : 0 ≤ X := Real.iSup_nonneg fun k => supAbs_nonneg _
  have hYnn : 0 ≤ Y := Real.iSup_nonneg fun _ => abs_nonneg _
  have hbddX : BddAbove (Set.range fun k : Fin (n + 1) => (partialPivotStage A k).supAbs) :=
    (Set.finite_range _).bddAbove
  have hbddY : BddAbove (Set.range fun p : Fin n × Fin n × Fin n =>
      |gemStage B p.1 p.2.1 p.2.2|) := (Set.finite_range _).bddAbove
  have hXY : X = Y := by
    refine le_antisymm (ciSup_le fun k => ?_) ?_
    · rw [← hstage]
      refine supAbs_le hYnn fun i j => ?_
      rcases lt_or_ge (k : ℕ) n with hk | hk
      · exact le_ciSup hbddY (⟨k, hk⟩, i, j)
      · rw [gemStage_apply_of_le B (le_refl (i : ℕ)) (i.2.le.trans hk)]
        exact le_ciSup hbddY (i, i, j)
    · rcases isEmpty_or_nonempty (Fin n) with hn | hn
      · rw [hY, Real.iSup_of_isEmpty]
        exact hXnn
      refine ciSup_le fun p => ?_
      refine (abs_apply_le_supAbs _ _ _).trans ?_
      rw [hstage]
      exact le_ciSup hbddX (⟨p.1, by omega⟩ : Fin (n + 1))
  have heq : growthFactorStages A = growthFactor B * A.supAbs / ‖A‖ := by
    rw [growthFactorStages, ← hX, hXY]
    rcases eq_or_ne A.supAbs 0 with h0 | h0
    · have hA : A = 0 := supAbs_eq_zero_iff.1 h0
      have hB0 : B = 0 := by rw [hB, hA, Matrix.mul_zero]
      have hY0 : Y = 0 := by
        rw [hY]
        simp [hB0, gemStage_zero_matrix]
      rw [hY0, h0, mul_zero]
    · rw [growthFactor, hBA, div_mul_cancel₀ _ h0]
  refine ⟨heq, ?_⟩
  rw [heq]
  rcases eq_or_ne ‖A‖ 0 with hA | hA
  · rw [hA, div_zero]
    exact growthFactor_nonneg _
  · rw [mul_div_assoc]
    refine mul_le_of_le_one_right (growthFactor_nonneg _) ?_
    exact div_le_one_of_le₀ (supAbs_le_linfty_opNorm A) (norm_nonneg _)

/-- **Section 3.4.5** of [golub2013matrix], the upper half of "$\rho$ can be as large as $2^{n-1}$".
Let $A \in \mathbb{R}^{n \times n}$ and let $P$ be the permutation matrix of partial pivoting on
$A$. Then
$$g(PA) \le 2^{n-1}, \qquad \rho \le 2^{n-1},$$
where $g$ is the growth factor `Matrix.growthFactor` and $\rho$ is the growth factor (3.4.8).

The proof follows the argument of P3.4.1. -/
theorem growthFactor_le_two_pow (A : Matrix (Fin n) (Fin n) ℝ) :
    growthFactor ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) ≤ 2 ^ (n - 1) ∧
      growthFactorStages A ≤ 2 ^ (n - 1) :=
  ⟨growthFactor_le_two_pow_of_partialPivotRow A,
    (growthFactorStages_eq A).2.trans (growthFactor_le_two_pow_of_partialPivotRow A)⟩

end Growth

/-! ### Normwise backward errors (§3.4.5) -/

section Normwise

open scoped Matrix.Norms.Operator

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- Let $E, L, U \in \mathbb{R}^{n \times n}$, let $P$ be a permutation matrix and $\gamma \ge 0$.
If $|E| \le \gamma P^T |L| |U|$ entrywise, then $\|E\|_\infty \le \gamma \|L\|_\infty
\|U\|_\infty$. -/
theorem linfty_opNorm_le_of_equation_3_4_6 {E L U : Matrix (Fin n) (Fin n) ℝ}
    {σ : Equiv.Perm (Fin n)} {γ : ℝ} (hγ : 0 ≤ γ)
    (hE : E.abs ≤ₑ γ • (L.abs * U.abs).submatrix σ.symm id) : ‖E‖ ≤ γ * (‖L‖ * ‖U‖) := by
  refine (linfty_opNorm_le_of_abs_le_smul_submatrix hγ _ hE).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hγ
  calc ‖L.abs * U.abs‖ ≤ ‖L.abs‖ * ‖U.abs‖ := linfty_opNorm_mul _ _
    _ = ‖L‖ * ‖U‖ := by rw [linfty_opNorm_abs, linfty_opNorm_abs]

/-- Let $E, L, U \in \mathbb{R}^{n \times n}$, let $P$ be a permutation matrix and $\gamma \ge 0$.
If $|E| \le \gamma P^T |L| |U|$ entrywise and $|\ell_{ij}| \le 1 + u$ for all $i, j$, then
$\|E\|_\infty \le n(1 + u)\gamma \|U\|_\infty$. -/
theorem linfty_opNorm_le_of_backward_error {E L U : Matrix (Fin n) (Fin n) ℝ}
    {σ : Equiv.Perm (Fin n)} {γ : ℝ} (hγ : 0 ≤ γ)
    (hE : E.abs ≤ₑ γ • (L.abs * U.abs).submatrix σ.symm id) (hL : ∀ i j, |L i j| ≤ 1 + fp.u) :
    ‖E‖ ≤ n * (1 + fp.u) * γ * ‖U‖ := by
  have hL' : ‖L‖ ≤ n * (1 + fp.u) := by
    have h := linfty_opNorm_le_card_mul_of_abs_le (by linarith [fp.u_nonneg]) hL
    rwa [Fintype.card_fin] at h
  refine (linfty_opNorm_le_of_equation_3_4_6 hγ hE).trans ?_
  calc γ * (‖L‖ * ‖U‖) ≤ γ * ((n * (1 + fp.u)) * ‖U‖) := by gcongr
    _ = n * (1 + fp.u) * γ * ‖U‖ := by ring

/-- Let $A, E, L, U \in \mathbb{R}^{n \times n}$, let $P$ be a permutation matrix, and let
$\gamma, \rho \ge 0$. If $|E| \le \gamma P^T |L| |U|$ entrywise, $|\ell_{ij}| \le 1 + u$ and
$|u_{ij}| \le \rho \|A\|_\infty$ for all $i, j$, then $\|E\|_\infty \le n^2 (1 + u)\gamma\rho
\|A\|_\infty$. -/
theorem linfty_opNorm_le_of_backward_error_growth {A E L U : Matrix (Fin n) (Fin n) ℝ}
    {σ : Equiv.Perm (Fin n)} {γ ρ : ℝ} (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ)
    (hE : E.abs ≤ₑ γ • (L.abs * U.abs).submatrix σ.symm id) (hL : ∀ i j, |L i j| ≤ 1 + fp.u)
    (hU : ∀ i j, |U i j| ≤ ρ * ‖A‖) :
    ‖E‖ ≤ (n : ℝ) ^ 2 * (1 + fp.u) * γ * ρ * ‖A‖ := by
  have hU' : ‖U‖ ≤ n * (ρ * ‖A‖) := by
    have h := linfty_opNorm_le_card_mul_of_abs_le (mul_nonneg hρ (norm_nonneg _)) hU
    rwa [Fintype.card_fin] at h
  refine (linfty_opNorm_le_of_backward_error hγ hE hL).trans ?_
  calc (n : ℝ) * (1 + fp.u) * γ * ‖U‖ ≤ n * (1 + fp.u) * γ * (n * (ρ * ‖A‖)) :=
        mul_le_mul_of_nonneg_left hU'
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (by linarith [fp.u_nonneg])) hγ)
    _ = (n : ℝ) ^ 2 * (1 + fp.u) * γ * ρ * ‖A‖ := by ring

/-- **Equation (3.4.7)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$, and let $u < 1$ and $3nu < 1$. Let $(F, \mathrm{piv})$ be an output of
Algorithm 3.4.1 on $A$ whose diagonal entries $f_{jj}$ are all nonzero, and let $\hat U$ be the
upper factor stored in $F$. Then every solution $\hat x$ computed from $F$, $\mathrm{piv}$ and
$b$ by the solve $Ly = Pb$, $Ux = y$ satisfies $(A + E)\hat x = b$ for some
$E \in \mathbb{R}^{n \times n}$ with
$$\|E\|_\infty \le n(1 + u)\gamma_{3n} \|\hat U\|_\infty.$$

The computed multipliers are at most $1 + u$ in modulus, so $\|\hat L\|_\infty \le n(1 + u)$.
The source prints the first-order bound $\|E\|_\infty \le nu(2\|A\|_\infty + 4n\|\hat
U\|_\infty) + O(u^2)$, which the rigorous bound implies. -/
theorem equation_3_4_7 (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, (∀ j, out.1 j j ≠ 0) →
      ∀ x ∈ (solvePLU fp.round out.1 out.2 b).run, ∃ E : Matrix (Fin n) (Fin n) ℝ,
        (A + E) *ᵥ x = b ∧ ‖E‖ ≤ n * (1 + fp.u) * gamma fp.u (3 * n) * ‖packedU out.1‖ := by
  intro out hout hpiv x hx
  obtain ⟨E, hAx, hE⟩ := equation_3_4_6 hu hn A b out hout hpiv x hx
  exact ⟨E, hAx, linfty_opNorm_le_of_backward_error (gamma_nonneg fp.u_nonneg hn) hE
    (algorithm_3_4_1_rounds A out hout fun j _ => hpiv j).2⟩

/-- **Equation (3.4.9)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$, let $u < 1$ and $3nu < 1$, and let $\rho \ge 0$. Let $(F, \mathrm{piv})$
be an output of Algorithm 3.4.1 on $A$ whose diagonal entries $f_{jj}$ are all nonzero, and
assume that the computed upper factor satisfies $|\hat u_{ij}| \le \rho \|A\|_\infty$ for all
$i, j$. Then every solution $\hat x$ computed from $F$, $\mathrm{piv}$ and $b$ by the solve
$Ly = Pb$, $Ux = y$ satisfies $(A + E)\hat x = b$ for some $E \in \mathbb{R}^{n \times n}$ with
$$\|E\|_\infty \le n^2 (1 + u)\gamma_{3n} \rho \|A\|_\infty.$$

**Reading.** In the source, $\rho$ is the growth factor of the computed stages, and the
derivation uses $|\hat u_{ij}| \le \rho \|A\|_\infty$. The theorem makes this bound a
hypothesis, which turns what Higham calls an "illicit manoeuvre" into an assumption. The growth
factor `GolubVanLoan.Chapter03.growthFactorStages` is defined on the exact stages and does not
bound the computed $\hat U$, so it cannot be used for $\rho$ here.

The source prints $\|E\|_\infty \le 6n^3 \rho \|A\|_\infty u + O(u^2)$. Since
$n^2 \gamma_{3n} = 3n^3 u + O(u^2)$, the theorem gives this bound with the better constant $3$. -/
theorem equation_3_4_9 (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, (∀ j, out.1 j j ≠ 0) →
      (∀ i j, |packedU out.1 i j| ≤ ρ * ‖A‖) →
      ∀ x ∈ (solvePLU fp.round out.1 out.2 b).run, ∃ E : Matrix (Fin n) (Fin n) ℝ,
        (A + E) *ᵥ x = b ∧ ‖E‖ ≤ (n : ℝ) ^ 2 * (1 + fp.u) * gamma fp.u (3 * n) * ρ * ‖A‖ := by
  intro out hout hpiv hU x hx
  obtain ⟨E, hAx, hE⟩ := equation_3_4_6 hu hn A b out hout hpiv x hx
  exact ⟨E, hAx, linfty_opNorm_le_of_backward_error_growth (gamma_nonneg fp.u_nonneg hn) hρ hE
    (algorithm_3_4_1_rounds A out hout fun j _ => hpiv j).2 hU⟩

end Normwise

/-! ### The gaxpy version with pivoting (§3.4.4), the growth example, and rook pivoting (§3.4.7) -/

section MorePivoting

variable {n : ℕ}

/-- The first index $i \ge k$ that maximizes $|v_i|$, with exact comparisons. It is
`Matrix.partialPivotRow` of the matrix whose every column is $v$. -/
noncomputable def firstMaxIndex (v : Fin n → ℝ) (k : Fin n) : Fin n :=
  partialPivotRow (of fun i (_ : Fin n) => v i) k

/-- The first maximizing index of $v$ from $k$ on lies at or after $k$, and $|v_i| \le |v_\mu|$ for
every $i \ge k$, where $\mu$ is that index. -/
theorem firstMaxIndex_spec (v : Fin n → ℝ) (k : Fin n) :
    k ≤ firstMaxIndex v k ∧ ∀ i, k ≤ i → |v i| ≤ |v (firstMaxIndex v k)| := by
  refine ⟨le_partialPivotRow _ k, fun i hi => ?_⟩
  have := norm_apply_le_partialPivotRow (of fun i (_ : Fin n) => v i) k hi
  simp only [of_apply, Real.norm_eq_abs] at this
  exact this

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.4.2** of [golub2013matrix] (Gaxpy LU with Partial Pivoting). Initialize $L$ to the
identity and $U$ to the zero matrix.
```
for j = 1:n
    if j = 1
        v = A(:,1)
    else
        ã = Π_{j-1} ⋯ Π_1 A(:,j)
        Solve L(1:j-1,1:j-1) z = ã(1:j-1) for z ∈ ℝ^{j-1}
        U(1:j-1,j) = z,  v(j:n) = ã(j:n) - L(j:n,1:j-1) · z
    end
    Determine μ with j ≤ μ ≤ n so |v(μ)| = ‖v(j:n)‖_∞ and set piv(j) = μ
    v(j) ↔ v(μ),  L(j,1:j-1) ↔ L(μ,1:j-1),  U(j,j) = v(j)
    if v(j) ≠ 0
        L(j+1:n,j) = v(j+1:n)/v(j)
    end
end
```
The program returns $(L, U, \mathrm{piv})$.

The interchanges recorded so far are applied to $A(:, j)$ by the loop
`GolubVanLoan.Chapter03.applyPiv`; the entries of $\mathrm{piv}$ from $j$ on are still the
identity. The triangular solve and the gaxpy are `GolubVanLoan.Chapter03.gaxpyColumn`, the
column computation of Algorithm 3.2.2. The search is `GolubVanLoan.Chapter03.firstMaxIndex`. -/
noncomputable def algorithm_3_4_2 (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) :=
  (List.finRange n).foldlM
    (fun (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) j => do
      let v ← gaxpyColumn rnd st.1 (applyPiv st.2.2 fun i => A i j) j
      if v (Equiv.swap j (firstMaxIndex v j) j) ≠ 0 then do
        let L ← ((List.finRange n).filter (j < ·)).foldlM
          (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
            let l ← rnd (v (Equiv.swap j (firstMaxIndex v j) i) /
              v (Equiv.swap j (firstMaxIndex v j) j))
            pure (L.updateRow i (Function.update (L i) j l)))
          (of fun i c => if c < j then st.1 (Equiv.swap j (firstMaxIndex v j) i) c else st.1 i c)
        pure (L, st.2.1.updateCol j (fun i => if i ≤ j then v (Equiv.swap j (firstMaxIndex v j) i)
          else 0), Function.update st.2.2 j (firstMaxIndex v j))
      else
        pure (of fun i c => if c < j then st.1 (Equiv.swap j (firstMaxIndex v j) i) c else st.1 i c,
          st.2.1.updateCol j (fun i => if i ≤ j then v (Equiv.swap j (firstMaxIndex v j) i) else 0),
          Function.update st.2.2 j (firstMaxIndex v j))) (1, 0, fun k => k)

section Alg342Bridge

variable {fp : RoundingModel ℝ}

/-- The domination of the multipliers of partial pivoting in the finished columns before $j$: for
each $\ell_{ic}$ with $c < j$ and $c < i$, the running difference $t$ of $b_{ic}$ and the
rounded products $\ell_{ir} u_{rc}$, $r < c$, satisfies $|t| \le |u_{cc}|$, and $\ell_{ic}$ is a
rounding of $t / u_{cc}$. -/
def GaxpyDom (fp : RoundingModel ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (j : ℕ)
    (L U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i c : Fin n, (c : ℕ) < j → c < i → ∃ (o : List (Fin n)) (t : ℝ), o.Nodup ∧
    (∀ r, r ∈ o ↔ r < c) ∧ RoundsRunningDiff fp o (L i) (fun r => U r c) (B i c) t ∧
    |t| ≤ |U c c| ∧ fp.Rounds (t / U c c) (L i c)

/-- The invariant of Algorithm 3.4.2 after the columns before $j$, for the matrix $B$ with its rows
permuted by the interchanges so far: the invariant `GolubVanLoan.Chapter03.GaxpyInv` of
Algorithm 3.2.2 for $B$, and the domination of the multipliers
`GolubVanLoan.Chapter03.GaxpyDom`. -/
def Alg342Core (fp : RoundingModel ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (j : ℕ)
    (L U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  GaxpyInv fp B j (L, U) ∧ GaxpyDom fp B j L U

/-- The invariant of Algorithm 3.4.2 after $j$ columns on the state $(L, U, \mathrm{piv})$: either
`GolubVanLoan.Chapter03.Alg342Core` holds for $A$ with its rows permuted by the first $j$
interchanges and $\mathrm{piv}$ is the identity from $j$ on, or the model does not round every
value to itself and a returned pivot $u_{cc}$ with $c < j$ and $c + 1 < n$ is zero. -/
def Alg342Inv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (j : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) : Prop :=
  (Alg342Core fp (A.submatrix (pivPermUpTo st.2.2 j) id) j st.1 st.2.1 ∧
      ∀ c : Fin n, j ≤ (c : ℕ) → st.2.2 c = c) ∨
    ((∃ c : Fin n, (c : ℕ) < j ∧ (c : ℕ) + 1 < n ∧ st.2.1 c c = 0) ∧ ¬ ∀ x, fp.Rounds x x)

/-- If $\mathrm{piv}(c) = c$ for every $c \ge j$ and $j \le n$, then the loop
`GolubVanLoan.Chapter03.applyPiv` applies the first $j$ interchanges: it maps $x$ to
$x \circ \sigma$, where $\sigma$ is the permutation of the first $j$ interchanges. -/
theorem applyPiv_eq_comp_pivPermUpTo {piv : Fin n → Fin n} {j : ℕ}
    (h : ∀ c : Fin n, j ≤ (c : ℕ) → piv c = c) (hj : j ≤ n) (x : Fin n → ℝ) :
    applyPiv piv x = x ∘ pivPermUpTo piv j := by
  have hup : ∀ m, j ≤ m → pivPermUpTo piv m = pivPermUpTo piv j := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      simp only [pivPermUpTo]
      split_ifs with hmn
      · rw [h ⟨m, hmn⟩ hm, Equiv.swap_self, ← Equiv.Perm.one_def, mul_one, ih]
      · exact ih
  rw [(applyPiv_eq piv x).1, permMatrix_mulVec, pivPerm, hup n hj]

/-- The $L$ of the interchanged rows: in the finished columns before $j$, row $i$ is row
$\sigma(i)$, which is the interchange $L(j, 1{:}j-1) \leftrightarrow L(\mu, 1{:}j-1)$ of the
source. -/
private abbrev swapFinished (L : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  of fun i c => if c < j then L (σ i) c else L i c

/-- Interchanging rows at or after $j$ keeps the invariant of Algorithm 3.2.2. Let $\sigma$ be a
permutation that fixes the indices before $j$ and maps the indices from $j$ on among themselves.
If $(L, U)$ satisfies `GolubVanLoan.Chapter03.GaxpyInv` after $j$ columns for $B$, then it
satisfies it for $B$ with its rows permuted by $\sigma$, after the finished columns of $L$ are
permuted with them. -/
theorem gaxpyInv_submatrix {B L U : Matrix (Fin n) (Fin n) ℝ} {j : Fin n} {σ : Equiv.Perm (Fin n)}
    (hfix : ∀ i, i < j → σ i = i) (hmap : ∀ i, j ≤ i → j ≤ σ i) (h : GaxpyInv fp B j (L, U)) :
    GaxpyInv fp (B.submatrix σ id) j (swapFinished L j σ, U) := by
  obtain ⟨hU, hL, hLid, hU0, hLlow, hLdiag, hUup⟩ := h
  dsimp only at hU hL hLid hU0 hLlow hLdiag hUup
  refine ⟨fun i c hc hic => ?_, fun i c hc hci => ?_, fun i c hc => ?_, hU0,
    fun i c hic => ?_, fun i => ?_, hUup⟩
  · have hij : i < j := lt_of_le_of_lt hic (Fin.lt_def.2 hc)
    obtain ⟨o, hnd, ho, hrd⟩ := hU i c hc hic
    refine ⟨o, hnd, ho, ?_⟩
    simp only [submatrix_apply, id, hfix i hij]
    exact hrd.congr (fun r hr => by simp [((ho r).1 hr).trans hij, hfix i hij]) fun _ _ => rfl
  · have hc' : c < j := Fin.lt_def.2 hc
    have hcσ : c < σ i := by
      by_cases hij : i < j
      · rw [hfix i hij]; exact hci
      · exact lt_of_lt_of_le hc' (hmap i (not_lt.1 hij))
    obtain ⟨o, t, hnd, ho, hrd, hx⟩ := hL (σ i) c hc hcσ
    refine ⟨o, t, hnd, ho, hrd.congr (fun r hr => by simp [((ho r).1 hr).trans hc'])
      fun _ _ => rfl, ?_⟩
    simpa [hc'] using hx
  · have hcj : ¬ c < j := fun h => absurd (Fin.lt_def.1 h) (not_lt.2 hc)
    simp only [of_apply, hcj, ↓reduceIte]
    exact hLid i c hc
  · by_cases hcj : c < j
    · simp only [of_apply, hcj, ↓reduceIte, hfix i (hic.trans hcj)]
      exact hLlow i c hic
    · simp only [of_apply, hcj, ↓reduceIte]
      exact hLlow i c hic
  · by_cases hij : i < j
    · simp only [of_apply, hij, ↓reduceIte, hfix i hij]
      exact hLdiag i
    · simp only [of_apply, hij, ↓reduceIte]
      exact hLdiag i

/-- Interchanging rows at or after $j$ keeps the domination `GolubVanLoan.Chapter03.GaxpyDom` of the
finished multipliers, with the finished columns of $L$ permuted with the rows. -/
theorem gaxpyDom_submatrix {B L U : Matrix (Fin n) (Fin n) ℝ} {j : Fin n} {σ : Equiv.Perm (Fin n)}
    (hfix : ∀ i, i < j → σ i = i) (hmap : ∀ i, j ≤ i → j ≤ σ i) (h : GaxpyDom fp B j L U) :
    GaxpyDom fp (B.submatrix σ id) j (swapFinished L j σ) U := by
  intro i c hc hci
  have hc' : c < j := Fin.lt_def.2 hc
  have hcσ : c < σ i := by
    by_cases hij : i < j
    · rw [hfix i hij]; exact hci
    · exact lt_of_lt_of_le hc' (hmap i (not_lt.1 hij))
  obtain ⟨o, t, hnd, ho, hrd, hdom, hx⟩ := h (σ i) c hc hcσ
  refine ⟨o, t, hnd, ho, hrd.congr (fun r hr => by simp [((ho r).1 hr).trans hc'])
    fun _ _ => rfl, hdom, ?_⟩
  simpa [hc'] using hx

/-- The column $v$ of the gaxpy, interchanged: entry $i$ of $v \circ \sigma$ is the running
difference of row $\sigma(i)$, over the same indices $r < \min(i, j)$, against the interchanged
$L$. -/
private theorem gaxpyColumn_rounds_swap {B L : Matrix (Fin n) (Fin n) ℝ} {j : Fin n}
    {σ : Equiv.Perm (Fin n)} (hfix : ∀ i, i < j → σ i = i) (hmap : ∀ i, j ≤ i → j ≤ σ i)
    {v : Fin n → ℝ} (hv : v ∈ (gaxpyColumn fp.round L (fun i => B i j) j).run) (i : Fin n) :
    RoundsRunningDiff fp ((List.finRange n).filter (fun r => r < i ∧ r < j))
      (swapFinished L j σ i) (v ∘ σ) (B.submatrix σ id i j) ((v ∘ σ) i) := by
  have h := gaxpyColumn_rounds L (fun i => B i j) j v hv (σ i)
  have hfilt : (List.finRange n).filter (fun r => r < σ i ∧ r < j) =
      (List.finRange n).filter (fun r => r < i ∧ r < j) := by
    refine List.filter_congr fun r _ => ?_
    simp only [decide_eq_decide]
    by_cases hij : i < j
    · rw [hfix i hij]
    · exact ⟨fun h => ⟨lt_of_lt_of_le h.2 (not_lt.1 hij), h.2⟩,
        fun h => ⟨lt_of_lt_of_le h.2 (hmap i (not_lt.1 hij)), h.2⟩⟩
  rw [hfilt] at h
  exact h.congr (fun r hr => by simp [(by simpa using hr : r < i ∧ r < j).2])
    fun r hr => by simp [hfix r (by simpa using hr : r < i ∧ r < j).2]

/-- One column of Algorithm 3.4.2 keeps its invariant `GolubVanLoan.Chapter03.Alg342Inv`: the column
step `GolubVanLoan.Chapter03.gaxpyInv_succ` of Algorithm 3.2.2 for the interchanged matrix,
together with the domination of the new multipliers by the pivot $|v(\mu)|$. -/
theorem alg342Inv_step (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n))
    (hst : Alg342Inv fp A j st)
    (st' : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n))
    (hst' : st' ∈ (do
      let v ← gaxpyColumn fp.round st.1 (applyPiv st.2.2 fun i => A i j) j
      if v (Equiv.swap j (firstMaxIndex v j) j) ≠ 0 then do
        let L ← ((List.finRange n).filter (j < ·)).foldlM
          (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
            let l ← fp.round (v (Equiv.swap j (firstMaxIndex v j) i) /
              v (Equiv.swap j (firstMaxIndex v j) j))
            pure (L.updateRow i (Function.update (L i) j l)))
          (of fun i c => if c < j then st.1 (Equiv.swap j (firstMaxIndex v j) i) c else st.1 i c)
        pure (L, st.2.1.updateCol j (fun i => if i ≤ j then v (Equiv.swap j (firstMaxIndex v j) i)
          else 0), Function.update st.2.2 j (firstMaxIndex v j))
      else
        pure (of fun i c => if c < j then st.1 (Equiv.swap j (firstMaxIndex v j) i) c else st.1 i c,
          st.2.1.updateCol j (fun i => if i ≤ j then v (Equiv.swap j (firstMaxIndex v j) i) else 0),
          Function.update st.2.2 j (firstMaxIndex v j)) : SetM _).run) :
    Alg342Inv fp A (j + 1) st' := by
  obtain ⟨L, U, piv⟩ := st
  dsimp only at hst hst'
  rw [SetM.mem_run_bind] at hst'
  obtain ⟨v, hv, hst'⟩ := hst'
  set μ := firstMaxIndex v j with hμ
  set σ := Equiv.swap j μ with hσ
  obtain ⟨hjμ, hvmax⟩ := firstMaxIndex_spec v j
  obtain ⟨hfix, hmap⟩ := swap_fix_and_map (k := j) hjμ
  set U' := U.updateCol j (fun i => if i ≤ j then v (σ i) else 0) with hU'
  have hU'o : ∀ i c, c ≠ j → U' i c = U i c := fun i c hc => by simp [hU', hc]
  have hU'j : ∀ i, U' i j = if i ≤ j then v (σ i) else 0 := fun i => by simp [hU']
  rcases hst with ⟨⟨hG, hD⟩, hpiv⟩ | ⟨⟨c, hc, hcn, hc0⟩, hnrefl⟩
  swap
  · -- a zero pivot was already returned
    refine Or.inr ⟨⟨c, by omega, hcn, ?_⟩, hnrefl⟩
    have hcj : c ≠ j := fun h => by rw [h] at hc; exact lt_irrefl _ hc
    split_ifs at hst' with h0
    · rw [SetM.mem_run_bind] at hst'
      obtain ⟨L', -, hst'⟩ := hst'
      rw [SetM.mem_run_pure] at hst'
      subst hst'
      change U' c c = 0
      rw [hU'o c c hcj]
      exact hc0
    · rw [SetM.mem_run_pure] at hst'
      subst hst'
      change U' c c = 0
      rw [hU'o c c hcj]
      exact hc0
  dsimp only at hpiv
  set π := pivPermUpTo piv j with hπ
  set B := A.submatrix π id with hB
  have hx₀ : applyPiv piv (fun i => A i j) = fun i => B i j := by
    rw [applyPiv_eq_comp_pivPermUpTo hpiv j.2.le]
    rfl
  rw [hx₀] at hv
  have hσfix : ∀ i : Fin n, i < j → σ i = i := fun i hi => hfix i (Fin.lt_def.1 hi)
  have hσmap : ∀ i : Fin n, j ≤ i → j ≤ σ i := fun i hi => Fin.le_def.2 (hmap i (Fin.le_def.1 hi))
  have hσj : σ j = μ := Equiv.swap_apply_left j μ
  have hB' : A.submatrix (pivPermUpTo (Function.update piv j μ) (j + 1)) id =
      B.submatrix σ id := by
    rw [pivPermUpTo_update, hB, submatrix_submatrix, Equiv.Perm.coe_mul]
    rfl
  have hpiv' : ∀ c : Fin n, (j : ℕ) + 1 ≤ (c : ℕ) → Function.update piv j μ c = c := fun c hc => by
    rw [Function.update_of_ne (fun h => by rw [h] at hc; omega)]
    exact hpiv c (by omega)
  -- the invariant for the interchanged matrix, before the new column
  have hG₀ := gaxpyInv_submatrix hσfix hσmap hG
  have hD₀ := gaxpyDom_submatrix hσfix hσmap hD
  have hv₀ := gaxpyColumn_rounds_swap hσfix hσmap hv
  -- the new invariant, given the new column `j` of `L`
  have hcore : ∀ L' : Matrix (Fin n) (Fin n) ℝ,
      (∀ i c, ¬ (j < i ∧ c = j) → L' i c = swapFinished L j σ i c) →
      (∀ i, j < i → fp.Rounds (v (σ i) / v (σ j)) (L' i j)) →
      Alg342Core fp (B.submatrix σ id) (j + 1) L' U' := by
    intro L' hL'o hL'j
    refine ⟨gaxpyInv_succ hG₀ hv₀ hL'o hL'j, fun i c hc hci => ?_⟩
    have hLc : ∀ r, r ≠ j → L' i r = swapFinished L j σ i r := fun r hr =>
      hL'o i r fun h => hr h.2
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
    · have hc' : c < j := Fin.lt_def.2 hc
      obtain ⟨o, t, hnd, ho, hrd, hdom, hx⟩ := hD₀ i c hc hci
      refine ⟨o, t, hnd, ho, hrd.congr (fun r hr => hLc r (ne_of_lt (((ho r).1 hr).trans hc')))
        fun r hr => hU'o r c (ne_of_lt hc'), ?_, ?_⟩
      · rw [hU'o c c (ne_of_lt hc')]; exact hdom
      · rw [hU'o c c (ne_of_lt hc'), hLc c (ne_of_lt hc')]; exact hx
    · have hcj : c = j := Fin.ext hc
      subst hcj
      obtain ⟨o, hnd, ho, hrd⟩ := gaxpy_newCol_lower hci (hv₀ i) (fun r hr => hLc r (ne_of_lt hr)) U
      refine ⟨o, v (σ i), hnd, ho, hrd, ?_, ?_⟩
      · rw [hU'j c, ite_eq_left le_rfl, hσj]
        exact hvmax _ (Fin.le_def.1 (hσmap i hci.le))
      · rw [hU'j c, ite_eq_left le_rfl]
        exact hL'j i hci
  split_ifs at hst' with h0
  · rw [SetM.mem_run_bind] at hst'
    obtain ⟨L', hL', hst'⟩ := hst'
    rw [SetM.mem_run_pure] at hst'
    subst hst'
    obtain ⟨hL'o, hL'j⟩ := mem_run_multipliers (v := v ∘ σ) hL'
    refine Or.inl ⟨?_, hpiv'⟩
    rw [hB']
    exact hcore L' hL'o hL'j
  · rw [SetM.mem_run_pure] at hst'
    subst hst'
    have h0' : v (σ j) = 0 := not_not.1 h0
    by_cases hc : (∀ x, fp.Rounds x x) ∨ ¬ (j : ℕ) + 1 < n
    · refine Or.inl ⟨?_, hpiv'⟩
      rw [hB']
      refine hcore _ (fun _ _ _ => rfl) fun i hi => ?_
      have hvi : v (σ i) = 0 := by
        have := hvmax _ (Fin.le_def.1 (hσmap i hi.le))
        rw [← hμ, ← hσj, h0', abs_zero] at this
        exact abs_nonpos_iff.1 this
      have hLij : swapFinished L j σ i j = 0 := by
        simp only [of_apply, lt_irrefl, ↓reduceIte]
        exact (hG.2.2.1 i j le_rfl).trans (ite_eq_right (ne_of_gt hi))
      change fp.Rounds (v (σ i) / v (σ j)) (swapFinished L j σ i j)
      rw [hLij, hvi, zero_div]
      rcases hc with hc | hc
      · exact hc 0
      · exact absurd (by have := Fin.lt_def.1 hi; have := i.2; omega) hc
    · obtain ⟨hc₁, hc₂⟩ := not_or.1 hc
      refine Or.inr ⟨⟨j, by simp, not_not.1 hc₂, ?_⟩, hc₁⟩
      change U' j j = 0
      rw [hU'j j, ite_eq_left le_rfl]
      exact h0'

/-- Every run of Algorithm 3.4.2 satisfies the invariant `GolubVanLoan.Chapter03.Alg342Inv` after
all $n$ columns. -/
theorem alg342Inv_of_mem_run (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ out ∈ (algorithm_3_4_2 fp.round A).run, Alg342Inv fp A n out :=
  SetM.forall_mem_run_foldlM_finRange (Alg342Inv fp A)
    (Or.inl ⟨⟨gaxpyInv_zero _, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩, fun _ _ => rfl⟩)
    fun j st hst st' hst' => alg342Inv_step A j st hst st' hst'

/-- The finished invariant of Algorithm 3.4.2, read on the packed matrix of $L$ and $U$: if
`GolubVanLoan.Chapter03.Alg342Core` holds after $n$ columns, then the packed matrix with $L$
below the diagonal and $U$ on and above it satisfies `GolubVanLoan.Chapter03.PivStageInv` after
$n$ steps, and its packed factors are $L$ and $U$. -/
theorem pivStageInv_of_alg342Core {B L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Alg342Core fp B n L U) :
    PivStageInv fp B n (of fun i c => if c < i then L i c else U i c) ∧
      packedL (of fun i c => if c < i then L i c else U i c) = L ∧
      packedU (of fun i c => if c < i then L i c else U i c) = U := by
  obtain ⟨⟨hU, hL, -, -, hLlow, hLdiag, hUup⟩, hD⟩ := h
  dsimp only at hU hL hLlow hLdiag hUup
  set S : Matrix (Fin n) (Fin n) ℝ := of fun i c => if c < i then L i c else U i c with hS
  have hSl : ∀ i c : Fin n, c < i → S i c = L i c := fun i c h => by simp [hS, h]
  have hSu : ∀ i c : Fin n, i ≤ c → S i c = U i c := fun i c h => by simp [hS, not_lt.2 h]
  refine ⟨⟨fun i j => ⟨fun _ hij => ?_, fun _ hji => ?_, fun hi _ => absurd i.2 (not_lt.2 hi)⟩,
    fun i j _ hji => ?_⟩, ?_, ?_⟩
  · obtain ⟨o, hnd, ho, p, hp, hsum⟩ := hU i j j.2 hij
    refine ⟨o, p, hnd, ho, fun r hr => ?_, ?_⟩
    · have hri := (ho r).1 hr
      rw [hSl i r hri, hSu r j (hri.le.trans hij)]
      exact hp r hr
    · rw [hSu i j hij]; exact hsum
  · obtain ⟨o, t, hnd, ho, ⟨p, hp, hsum⟩, hx⟩ := hL i j j.2 hji
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_⟩
    · have hrj := (ho r).1 hr
      rw [hSl i r (hrj.trans hji), hSu r j hrj.le]
      exact hp r hr
    · rw [hSu j j le_rfl, hSl i j hji]; exact hx
  · obtain ⟨o, t, hnd, ho, ⟨p, hp, hsum⟩, hd, hx⟩ := hD i j j.2 hji
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_, ?_⟩
    · have hrj := (ho r).1 hr
      rw [hSl i r (hrj.trans hji), hSu r j hrj.le]
      exact hp r hr
    · rw [hSu j j le_rfl]; exact hd
    · rw [hSu j j le_rfl, hSl i j hji]; exact hx
  · ext i c
    rcases lt_trichotomy c i with hci | rfl | hic
    · rw [packedL_apply_of_lt _ hci, hSl i c hci]
    · rw [packedL_apply_self, hLdiag]
    · rw [packedL_apply_of_lt' _ hic, hLlow i c hic]
  · ext i c
    rcases le_or_gt i c with hic | hci
    · rw [packedU_apply_of_le _ hic, hSu i c hic]
    · rw [packedU_apply_of_lt _ hci, hUup i c hci]

/-- **Algorithm 3.4.2** of [golub2013matrix], rounding bridge. Let $A \in \mathbb{R}^{n \times n}$.
For every output $(\hat L, \hat U, \mathrm{piv})$ of Algorithm 3.4.2 in the rounding model `fp`
whose returned pivots $\hat u_{jj}$, $j + 1 < n$, are nonzero, let $P$ be the permutation matrix
encoded by $\mathrm{piv}$. Then $\hat L$ and $\hat U$ form a computed LU factorization of $PA$
in the sense of `FloatingPoint.RoundsLU`, and
$$|\hat\ell_{ij}| \le 1 + u \quad \text{for all } i, j.$$

The proof is the gaxpy bridge `GolubVanLoan.Chapter03.algorithm_3_2_2_rounds` for $A$ with its
rows permuted by the recorded interchanges, which move the finished rows of $L$ together with
the rows of $A$. -/
theorem algorithm_3_4_2_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ out ∈ (algorithm_3_4_2 fp.round A).run,
      (∀ j : Fin n, (j : ℕ) + 1 < n → out.2.1 j j ≠ 0) →
      RoundsLU fp (A.submatrix (pivPerm out.2.2) id) out.1 out.2.1 ∧
        ∀ i j, |out.1 i j| ≤ 1 + fp.u := by
  intro out hout hpiv
  rcases alg342Inv_of_mem_run A out hout with ⟨h, -⟩ | ⟨⟨j, -, hjn, hj0⟩, -⟩
  · obtain ⟨⟨hS, hD⟩, hL, hU⟩ := pivStageInv_of_alg342Core h
    have hR := roundsLU_of_luStageInv hS
    rw [hL, hU] at hR
    refine ⟨hR, fun i j => ?_⟩
    rw [← hL]
    rcases lt_trichotomy j i with hji | rfl | hij
    · rw [packedL_apply_of_lt _ hji]
      exact abs_le_one_add_of_lowerEntryDom (hD i j j.2 hji)
    · rw [packedL_apply_self, abs_one]
      linarith [fp.u_nonneg]
    · rw [packedL_apply_of_lt' _ hij, abs_zero]
      linarith [fp.u_nonneg]
  · exact absurd hj0 (hpiv j hjn)

/-- The exact run of Algorithm 3.4.2 is one of its runs in the exact rounding model. -/
private theorem algorithm_3_4_2_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_3_4_2 pure A) ∈ (algorithm_3_4_2 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_4_2, gaxpyColumn, runningDiff, pure_bind, ite_pure, List.foldlM_pure,
    SetM.mem_run_pure]
  rfl

/-- **Algorithm 3.4.2** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
be arbitrary, and let $(L, U, \mathrm{piv})$ be the output of Algorithm 3.4.2 in exact
arithmetic, with $P$ the permutation matrix encoded by $\mathrm{piv}$. Then
$$PA = LU, \qquad |\ell_{ij}| \le 1 \text{ for all } i, j,$$
with $L$ unit lower triangular and $U$ upper triangular.

The theorem has no hypothesis on $A$: a zero pivot comes with a zero $v(j{:}n)$, and the skipped
division is then the division $0/0 = 0$. The proof reads the invariant of the bridge at the
exact model. -/
theorem algorithm_3_4_2_spec (A : Matrix (Fin n) (Fin n) ℝ) :
    IsLU ((pivPerm (Id.run (algorithm_3_4_2 pure A)).2.2).permMatrix ℝ * A)
        (Id.run (algorithm_3_4_2 pure A)).1 (Id.run (algorithm_3_4_2 pure A)).2.1 ∧
      ∀ i j, |(Id.run (algorithm_3_4_2 pure A)).1 i j| ≤ 1 := by
  rcases alg342Inv_of_mem_run A _ (algorithm_3_4_2_mem_exact A) with ⟨h, -⟩ | ⟨-, hn⟩
  · obtain ⟨hP, hL, hU⟩ := pivStageInv_of_alg342Core h
    have := isLU_of_pivStageInv_exact hP
    rw [hL, hU] at this
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    exact this
  · exact absurd (fun x => rfl) hn

end Alg342Bridge

/-! ### The backward error of the gaxpy version (§3.4.5) -/

section Alg342Backward

variable {fp : RoundingModel ℝ}

/-- **Equation (3.4.6)** of [golub2013matrix], for Algorithm 3.4.2. The source states (3.4.6) for
$\hat P$, $\hat L$, $\hat U$ "as produced by the above algorithms". Let
$A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$, and let $u < 1$ and $3nu < 1$. Let
$(\hat L, \hat U, \mathrm{piv})$ be an output of Algorithm 3.4.2 on $A$ whose diagonal entries
$\hat u_{jj}$ are all nonzero, and let $P$ be the permutation matrix encoded by $\mathrm{piv}$.
If $\hat y$ is computed by Algorithm 3.1.1 from $\hat L$ and $Pb$, and $\hat x$ by Algorithm
3.1.2 from $\hat U$ and $\hat y$, then $(A + E)\hat x = b$ for some
$E \in \mathbb{R}^{n \times n}$ with
$$|E| \le \gamma_{3n} P^T |\hat L| |\hat U|$$
entrywise.

The vector $Pb$ is computed exactly by `GolubVanLoan.Chapter03.applyPiv`. The proof applies
`GolubVanLoan.Chapter03.algorithm_3_4_2_rounds` and
`GolubVanLoan.Chapter03.exists_backward_error_of_roundsLU`. -/
theorem equation_3_4_6_gaxpy (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ out ∈ (algorithm_3_4_2 fp.round A).run, (∀ j, out.2.1 j j ≠ 0) →
      ∀ y ∈ (algorithm_3_1_1 fp.round out.1 (applyPiv out.2.2 b)).run,
      ∀ x ∈ (algorithm_3_1_2 fp.round out.2.1 y).run, ∃ E : Matrix (Fin n) (Fin n) ℝ,
        (A + E) *ᵥ x = b ∧ E.abs ≤ₑ gamma fp.u (3 * n) •
          (out.1.abs * out.2.1.abs).submatrix (pivPerm out.2.2).symm id := by
  intro out hout hpiv y hy x hx
  obtain ⟨hR, -⟩ := algorithm_3_4_2_rounds A out hout fun j _ => hpiv j
  rw [(applyPiv_eq _ _).1, permMatrix_mulVec] at hy
  exact exists_backward_error_of_roundsLU hu hn hR hpiv hy hx

section Normwise

open scoped Matrix.Norms.Operator

/-- **Equation (3.4.7)** of [golub2013matrix], for Algorithm 3.4.2. Under the hypotheses of
`GolubVanLoan.Chapter03.equation_3_4_6_gaxpy`, the computed solution satisfies
$(A + E)\hat x = b$ for some $E \in \mathbb{R}^{n \times n}$ with
$$\|E\|_\infty \le n(1 + u)\gamma_{3n} \|\hat U\|_\infty.$$
-/
theorem equation_3_4_7_gaxpy (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ out ∈ (algorithm_3_4_2 fp.round A).run, (∀ j, out.2.1 j j ≠ 0) →
      ∀ y ∈ (algorithm_3_1_1 fp.round out.1 (applyPiv out.2.2 b)).run,
      ∀ x ∈ (algorithm_3_1_2 fp.round out.2.1 y).run, ∃ E : Matrix (Fin n) (Fin n) ℝ,
        (A + E) *ᵥ x = b ∧ ‖E‖ ≤ n * (1 + fp.u) * gamma fp.u (3 * n) * ‖out.2.1‖ := by
  intro out hout hpiv y hy x hx
  obtain ⟨E, hAx, hE⟩ := equation_3_4_6_gaxpy hu hn A b out hout hpiv y hy x hx
  exact ⟨E, hAx, linfty_opNorm_le_of_backward_error (gamma_nonneg fp.u_nonneg hn) hE
    (algorithm_3_4_2_rounds A out hout fun j _ => hpiv j).2⟩

/-- **Equation (3.4.9)** of [golub2013matrix], for Algorithm 3.4.2. Let $\rho \ge 0$. Under the
hypotheses of `GolubVanLoan.Chapter03.equation_3_4_6_gaxpy`, if the computed $\hat U$ satisfies
$|\hat u_{ij}| \le \rho \|A\|_\infty$ for all $i, j$, then the computed solution satisfies
$(A + E)\hat x = b$ for some $E \in \mathbb{R}^{n \times n}$ with
$$\|E\|_\infty \le n^2 (1 + u)\gamma_{3n} \rho \|A\|_\infty.$$

**Reading.** As in `GolubVanLoan.Chapter03.equation_3_4_9`, the bound on the computed $\hat U$,
which the source derives from the growth factor, is a hypothesis. -/
theorem equation_3_4_9_gaxpy (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ out ∈ (algorithm_3_4_2 fp.round A).run, (∀ j, out.2.1 j j ≠ 0) →
      (∀ i j, |out.2.1 i j| ≤ ρ * ‖A‖) →
      ∀ y ∈ (algorithm_3_1_1 fp.round out.1 (applyPiv out.2.2 b)).run,
      ∀ x ∈ (algorithm_3_1_2 fp.round out.2.1 y).run, ∃ E : Matrix (Fin n) (Fin n) ℝ,
        (A + E) *ᵥ x = b ∧ ‖E‖ ≤ (n : ℝ) ^ 2 * (1 + fp.u) * gamma fp.u (3 * n) * ρ * ‖A‖ := by
  intro out hout hpiv hU y hy x hx
  obtain ⟨E, hAx, hE⟩ := equation_3_4_6_gaxpy hu hn A b out hout hpiv y hy x hx
  exact ⟨E, hAx, linfty_opNorm_le_of_backward_error_growth (gamma_nonneg fp.u_nonneg hn) hρ hE
    (algorithm_3_4_2_rounds A out hout fun j _ => hpiv j).2 hU⟩

end Normwise

end Alg342Backward

/-- **Section 3.4.5** of [golub2013matrix], the matrix of the $2^{n-1}$ example. The matrix
$A \in \mathbb{R}^{n \times n}$ has $a_{ij} = 1$ if $i = j$ or $j = n$, $a_{ij} = -1$ if $i > j$
and $j < n$, and $a_{ij} = 0$ otherwise.

With 0-based indices the last column is $j = n - 1$. -/
noncomputable def growthExample (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if i = j ∨ (j : ℕ) = n - 1 then 1 else if j < i then -1 else 0

/-- **Section 3.4.7** of [golub2013matrix], the rook scan in the trailing block from $k$ on:
```
μ = k, λ = k, τ = |a_μλ|, s = 0
while τ < ‖A(k:n,λ)‖_∞ ∨ τ < ‖A(μ,k:n)‖_∞
    if mod(s,2) = 0
        Update μ so that |a_μλ| = ‖A(k:n,λ)‖_∞ with k ≤ μ ≤ n.
    else
        Update λ so that |a_μλ| = ‖A(μ,k:n)‖_∞ with k ≤ λ ≤ n.
    end
    s = s + 1
end
```
The function returns $(\mu, \lambda)$.

The `while` loop is a loop of at most `fuel` passes with a flag that records the exit. The
updates choose the first maximizing index (`GolubVanLoan.Chapter03.firstMaxIndex`). The
comparisons are exact, and nothing is rounded. -/
noncomputable def rookPivotSearch (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (fuel : ℕ) :
    Fin n × Fin n :=
  let st := (List.range fuel).foldl (fun (st : Fin n × Fin n × ℕ × Bool) _ =>
    if st.2.2.2 then st
    else if |A st.1 st.2.1| < |A (firstMaxIndex (fun i => A i st.2.1) k) st.2.1| ∨
        |A st.1 st.2.1| < |A st.1 (firstMaxIndex (fun j => A st.1 j) k)| then
      if st.2.2.1 % 2 = 0 then (firstMaxIndex (fun i => A i st.2.1) k, st.2.1, st.2.2.1 + 1, false)
      else (st.1, firstMaxIndex (fun j => A st.1 j) k, st.2.2.1 + 1, false)
    else (st.1, st.2.1, st.2.2.1, true)) (k, k, 0, false)
  (st.1, st.2.1)

/-- One pass of the `while` loop of the rook scan, on the state $(\mu, \lambda, s, \mathrm{done})$.
-/
private noncomputable def rookPass (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n)
    (st : Fin n × Fin n × ℕ × Bool) : Fin n × Fin n × ℕ × Bool :=
  if st.2.2.2 then st
  else if |A st.1 st.2.1| < |A (firstMaxIndex (fun i => A i st.2.1) k) st.2.1| ∨
      |A st.1 st.2.1| < |A st.1 (firstMaxIndex (fun j => A st.1 j) k)| then
    if st.2.2.1 % 2 = 0 then (firstMaxIndex (fun i => A i st.2.1) k, st.2.1, st.2.2.1 + 1, false)
    else (st.1, firstMaxIndex (fun j => A st.1 j) k, st.2.2.1 + 1, false)
  else (st.1, st.2.1, st.2.2.1, true)

/-- The rook condition at $(\mu, \lambda)$: in the trailing block from $k$ on, $|a_{\mu\lambda}|$ is
maximal in its column and in its row. -/
private def IsRookEntry (A : Matrix (Fin n) (Fin n) ℝ) (k μ l : Fin n) : Prop :=
  k ≤ μ ∧ k ≤ l ∧ (∀ i, k ≤ i → |A i l| ≤ |A μ l|) ∧ ∀ j, k ≤ j → |A μ j| ≤ |A μ l|

/-- The number of entries of the trailing block from $k$ on whose modulus exceeds $\tau$. -/
private noncomputable def rookPotential (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (τ : ℝ) : ℕ :=
  ((Finset.Ici k ×ˢ Finset.Ici k).filter fun p : Fin n × Fin n => τ < |A p.1 p.2|).card

private theorem rookPotential_lt_card (A : Matrix (Fin n) (Fin n) ℝ) {k μ l : Fin n}
    (hμ : k ≤ μ) (hl : k ≤ l) :
    rookPotential A k |A μ l| < (n - k) ^ 2 := by
  have hcard : (Finset.Ici k ×ˢ Finset.Ici k).card = (n - k) ^ 2 := by
    rw [Finset.card_product, Fin.card_Ici, sq]
  rw [← hcard]
  refine Finset.card_lt_card (Finset.filter_ssubset.2 ⟨(μ, l), ?_, lt_irrefl _⟩)
  simp [hμ, hl]

private theorem rookPotential_lt (A : Matrix (Fin n) (Fin n) ℝ) {k μ l : Fin n}
    (hμ : k ≤ μ) (hl : k ≤ l) {τ : ℝ} (hτ : τ < |A μ l|) :
    rookPotential A k |A μ l| < rookPotential A k τ := by
  refine Finset.card_lt_card ⟨fun p hp => ?_, ?_⟩
  · simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hτ.trans hp.2⟩
  intro h
  have hmem : (μ, l) ∈ Finset.Ici k ×ˢ Finset.Ici k := by simp [hμ, hl]
  have := h (Finset.mem_filter.2 ⟨hmem, hτ⟩)
  exact lt_irrefl _ (Finset.mem_filter.1 this).2

/-- The invariant of the rook scan after $t$ passes. -/
private def RookInv (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (t : ℕ)
    (st : Fin n × Fin n × ℕ × Bool) : Prop :=
  k ≤ st.1 ∧ k ≤ st.2.1 ∧ (st.2.2.2 = true → IsRookEntry A k st.1 st.2.1) ∧
    (st.2.2.2 = false → st.2.2.1 = t ∧ (1 ≤ t → rookPotential A k |A st.1 st.2.1| + t ≤ (n - k) ^ 2)
      ∧ (t % 2 = 1 → ∀ i, k ≤ i → |A i st.2.1| ≤ |A st.1 st.2.1|)
      ∧ (t % 2 = 0 → 1 ≤ t → ∀ j, k ≤ j → |A st.1 j| ≤ |A st.1 st.2.1|))

private theorem rookInv_pass (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (t : ℕ)
    (st : Fin n × Fin n × ℕ × Bool) (h : RookInv A k t st) :
    RookInv A k (t + 1) (rookPass A k st) := by
  obtain ⟨μ, l, s, d⟩ := st
  obtain ⟨hμ, hl, hdone, hrun⟩ := h
  simp only at hμ hl hdone hrun
  cases d with
  | true => exact ⟨hμ, hl, hdone, fun h => by simp [rookPass] at h⟩
  | false =>
    obtain ⟨rfl, hpot, hcol, hrow⟩ := hrun rfl
    obtain ⟨hcμ, hcmax⟩ := firstMaxIndex_spec (fun i => A i l) k
    obtain ⟨hrl, hrmax⟩ := firstMaxIndex_spec (fun j => A μ j) k
    by_cases hv : |A μ l| < |A (firstMaxIndex (fun i => A i l) k) l| ∨
        |A μ l| < |A μ (firstMaxIndex (fun j => A μ j) k)|
    · by_cases hs : s % 2 = 0
      · simp only [rookPass, Bool.false_eq_true, ↓reduceIte, hv, hs]
        refine ⟨hcμ, hl, fun h => by simp at h, fun _ => ⟨rfl, fun _ => ?_, fun _ => hcmax,
          fun h => by omega⟩⟩
        dsimp only
        rcases Nat.eq_zero_or_pos s with rfl | hs0
        · have := rookPotential_lt_card A hcμ hl
          omega
        · have hc : |A μ l| < |A (firstMaxIndex (fun i => A i l) k) l| := by
            rcases hv with hv | hv
            · exact hv
            · exact absurd (hrow hs hs0 _ hrl) (not_le.2 hv)
          have := rookPotential_lt A hcμ hl hc
          have := hpot hs0
          omega
      · simp only [rookPass, Bool.false_eq_true, ↓reduceIte, hv, hs]
        have hs1 : s % 2 = 1 := by omega
        have hs0 : 1 ≤ s := by omega
        refine ⟨hμ, hrl, fun h => by simp at h, fun _ => ⟨rfl, fun _ => ?_, fun h => by omega,
          fun _ _ => hrmax⟩⟩
        have hr : |A μ l| < |A μ (firstMaxIndex (fun j => A μ j) k)| := by
          rcases hv with hv | hv
          · exact absurd (hcol hs1 _ hcμ) (not_le.2 hv)
          · exact hv
        dsimp only
        have := rookPotential_lt A hμ hrl hr
        have := hpot hs0
        omega
    · simp only [rookPass, Bool.false_eq_true, ↓reduceIte, hv]
      rw [not_or, not_lt, not_lt] at hv
      refine ⟨hμ, hl, fun _ => ⟨hμ, hl, fun i hi => (hcmax i hi).trans hv.1,
        fun j hj => (hrmax j hj).trans hv.2⟩, fun h => by simp at h⟩

/-- The state after `t` passes satisfies the invariant. -/
private theorem rookInv_foldl (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (t : ℕ) :
    RookInv A k t ((List.range t).foldl (fun st _ => rookPass A k st) (k, k, 0, false)) := by
  induction t with
  | zero =>
    exact ⟨le_rfl, le_rfl, fun h => by simp at h, fun _ => ⟨rfl, fun h => by omega,
      fun h => by omega, fun _ h => by omega⟩⟩
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact rookInv_pass A k t _ ih

/-- **Section 3.4.7** of [golub2013matrix], termination and correctness of the rook scan. Let
$A \in \mathbb{R}^{n \times n}$, let $k$ be an index, and let the number of passes be at least
$(n - k)^2 + 1$. Then the rook scan from $(k, k)$ returns $(\mu, \lambda)$ with
$\mu, \lambda \ge k$ and
$$|a_{i\lambda}| \le |a_{\mu\lambda}| \text{ for all } i \ge k, \qquad |a_{\mu j}| \le
  |a_{\mu\lambda}| \text{ for all } j \ge k.$$

The source notes that "the value of $\tau$ is monotone increasing and that ensures termination".
Every pass after the first strictly increases $\tau = |a_{\mu\lambda}|$ or exits. So after
$(n - k)^2 + 1$ passes, the number of entries of the trailing block plus one, the loop has
exited, and on exit $|a_{\mu\lambda}|$ is maximal in its column and in its row of the trailing
block. -/
theorem rookPivotSearch_spec (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) {fuel : ℕ}
    (hfuel : (n - k) ^ 2 + 1 ≤ fuel) :
    k ≤ (rookPivotSearch A k fuel).1 ∧ k ≤ (rookPivotSearch A k fuel).2 ∧
      (∀ i, k ≤ i → |A i (rookPivotSearch A k fuel).2| ≤
        |A (rookPivotSearch A k fuel).1 (rookPivotSearch A k fuel).2|) ∧
      ∀ j, k ≤ j → |A (rookPivotSearch A k fuel).1 j| ≤
        |A (rookPivotSearch A k fuel).1 (rookPivotSearch A k fuel).2| := by
  have hprog : rookPivotSearch A k fuel =
      (((List.range fuel).foldl (fun st _ => rookPass A k st) (k, k, 0, false)).1,
        ((List.range fuel).foldl (fun st _ => rookPass A k st) (k, k, 0, false)).2.1) := rfl
  rw [hprog]
  obtain ⟨-, -, hdone, hrun⟩ := rookInv_foldl A k fuel
  cases hd : ((List.range fuel).foldl (fun st _ => rookPass A k st) (k, k, 0, false)).2.2.2 with
  | true => exact hdone hd
  | false =>
    have := ((hrun hd).2.1) (by omega)
    omega

/-- **Section 3.4.7** of [golub2013matrix], the rook pivoting strategy: the rook scan
`GolubVanLoan.Chapter03.rookPivotSearch` from $(k, k)$ with $(n - k)^2 + 1$ passes, which are
enough for the loop to exit (`GolubVanLoan.Chapter03.rookPivotSearch_spec`). -/
noncomputable def rookPivot (M : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Fin n × Fin n :=
  rookPivotSearch M k ((n - k) ^ 2 + 1)

/-- **Section 3.4.7** of [golub2013matrix]. The rook scan is a rook pivoting strategy in the sense
of the backbone: for every matrix and every $k$, `GolubVanLoan.Chapter03.rookPivot` returns
indices at or after $k$ whose entry is maximal in modulus in its column and in its row of the
trailing block. This is `Matrix.IsRookPivot`. -/
theorem isRookPivot_rookPivot : IsRookPivot (rookPivot (n := n)) :=
  fun A k => by
    simpa only [Real.norm_eq_abs, rookPivot] using rookPivotSearch_spec A k le_rfl

/-- **Section 3.4.7** of [golub2013matrix], rook pivoting computes the factorization $PAQ = LU$. Let
$A \in \mathbb{R}^{n \times n}$ be arbitrary. Gaussian elimination with the rook strategy, in
exact arithmetic, gives permutation matrices $P$ and $Q$ with
$$PAQ = LU, \qquad |\ell_{ij}| \le 1, \qquad |u_{ij}| \le |u_{ii}| \text{ for all } i, j,$$
where $U$ is the last stage of the elimination and $L$ is the unit lower triangular matrix of
multipliers of elimination without pivoting on $PAQ$.

The bound $|u_{ij}| \le |u_{ii}|$ answers the question of P3.4.2. There is no hypothesis on $A$:
the column maximality makes a zero pivot come with a zero column. The elimination is
`Matrix.gemFullPivotStage A GolubVanLoan.Chapter03.rookPivot`, $P$ and $Q$ are the permutation
matrices of the accumulated row interchanges and of the inverse of the accumulated column
interchanges, and $L$ is `Matrix.gemLower` of $PAQ$. -/
theorem rookPivoting_isLU (A : Matrix (Fin n) (Fin n) ℝ) :
    IsLU ((gemFullPivotStage A rookPivot n).2.1.permMatrix ℝ * A *
          ((gemFullPivotStage A rookPivot n).2.2)⁻¹.permMatrix ℝ)
        (gemLower ((gemFullPivotStage A rookPivot n).2.1.permMatrix ℝ * A *
          ((gemFullPivotStage A rookPivot n).2.2)⁻¹.permMatrix ℝ))
        (gemFullPivotStage A rookPivot n).1 ∧
      (∀ i j, |gemLower ((gemFullPivotStage A rookPivot n).2.1.permMatrix ℝ * A *
          ((gemFullPivotStage A rookPivot n).2.2)⁻¹.permMatrix ℝ) i j| ≤ 1) ∧
      ∀ i j, |(gemFullPivotStage A rookPivot n).1 i j| ≤
        |(gemFullPivotStage A rookPivot n).1 i i| := by
  simpa only [Real.norm_eq_abs] using
    gemFullPivotStage_permMatrix_mul_mul_permMatrix_isLU A isRookPivot_rookPivot

end MorePivoting

/-! ### The factorization of the growth example (§3.4.5) -/

section GrowthExample

variable {n : ℕ}

/-- The unit lower factor of the growth example: ones on the diagonal, $-1$ below it, and zero above
it. -/
noncomputable def growthExampleL (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if i = j then 1 else if j < i then -1 else 0

/-- The upper factor of the growth example: the identity except the last column, whose entry in row
$i$ is $2^i$ (0-based). -/
noncomputable def growthExampleU (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (j : ℕ) = n - 1 then 2 ^ (i : ℕ) else if i = j then 1 else 0

/-- $\sum_{r < i} 2^r = 2^i - 1$ for an index $i$ of `Fin n`. -/
private theorem sum_filter_lt_two_pow (i : Fin n) :
    ∑ r ∈ Finset.univ.filter (· < i), (2 : ℝ) ^ (r : ℕ) = 2 ^ (i : ℕ) - 1 := by
  have h : (Finset.univ.filter (· < i)).map Fin.valEmbedding = Finset.range i := by
    ext t
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨r, hr, rfl⟩; exact hr
    · intro ht; exact ⟨⟨t, by omega⟩, Fin.lt_def.2 ht, rfl⟩
  have := Finset.sum_map (Finset.univ.filter (· < i)) Fin.valEmbedding fun t => (2 : ℝ) ^ t
  rw [h] at this
  rw [show ∑ r ∈ Finset.univ.filter (· < i), (2 : ℝ) ^ (r : ℕ) =
    ∑ t ∈ Finset.range i, (2 : ℝ) ^ t from this.symm, geom_sum_eq (by norm_num)]
  ring

/-- **Section 3.4.5** of [golub2013matrix], the factorization of the $2^{n-1}$ example. The growth
example $A$ satisfies $A = LU$, where $L$ is unit lower triangular with $-1$ below the diagonal
and $U$ is the identity except its last column, whose entry in row $i$ is $2^{i-1}$. In
particular, for $n \ge 1$,
$$u_{nn} = 2^{n-1}.$$

The factors are `GolubVanLoan.Chapter03.growthExampleL` and
`GolubVanLoan.Chapter03.growthExampleU`, with 0-based entries $u_{i,n-1} = 2^i$. -/
theorem growthExample_isLU :
    IsLU (growthExample n) (growthExampleL n) (growthExampleU n) ∧
      ∀ h : 0 < n, growthExampleU n ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = 2 ^ (n - 1) := by
  refine ⟨⟨⟨fun i j hij => ?_, fun i => by simp [growthExampleL]⟩, fun i j hij => ?_, ?_⟩,
    fun h => by simp [growthExampleU]⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [growthExampleL, hij'.ne, not_lt.2 hij'.le]
  · dsimp only [id] at hij
    have hjn : (j : ℕ) ≠ n - 1 := by have := Fin.lt_def.1 hij; have := i.2; omega
    simp [growthExampleU, hjn, (ne_of_lt hij).symm]
  · ext i j
    rw [Matrix.mul_apply]
    by_cases hj : (j : ℕ) = n - 1
    · have hA : growthExample n i j = 1 := by simp [growthExample, hj]
      rw [hA]
      simp only [growthExampleL, growthExampleU, of_apply, hj, ↓reduceIte]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [ite_true, one_mul]
      have hrest : ∑ r ∈ Finset.univ.erase i,
          (if i = r then (1 : ℝ) else if r < i then -1 else 0) * 2 ^ (r : ℕ) =
          -∑ r ∈ Finset.univ.filter (· < i), (2 : ℝ) ^ (r : ℕ) := by
        rw [← Finset.sum_neg_distrib]
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i) (· < i)]
        have h1 : (Finset.univ.erase i).filter (· < i) = Finset.univ.filter (· < i) := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
          exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
        rw [h1, Finset.sum_eq_zero (s := (Finset.univ.erase i).filter fun r => ¬ r < i), add_zero]
        · refine Finset.sum_congr rfl fun r hr => ?_
          have hr' := (Finset.mem_filter.1 hr).2
          simp [hr'.ne', hr']
        · intro r hr
          obtain ⟨hr₁, hr₂⟩ := Finset.mem_filter.1 hr
          have hri : i ≠ r := fun h => (Finset.mem_erase.1 hr₁).1 h.symm
          simp [hri, hr₂]
      rw [hrest, sum_filter_lt_two_pow]
      ring
    · have hA : growthExample n i j = growthExampleL n i j := by
        simp [growthExample, growthExampleL, hj]
      rw [hA]
      simp only [growthExampleU, of_apply, hj, ↓reduceIte, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp

/-- The stage $A^{(k)}$ of elimination on the growth example: last column $2^{\min(i, k)}$, $1$ on
the diagonal, $-1$ below it in the columns $k, \dots, n - 2$, and $0$ elsewhere. -/
private noncomputable def growthStage (n k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (j : ℕ) = n - 1 then 2 ^ min (i : ℕ) k else if i = j then 1
    else if (j : ℕ) < i ∧ k ≤ (j : ℕ) then -1 else 0

private theorem growthStage_zero : growthStage n 0 = growthExample n := by
  ext i j
  simp only [growthStage, growthExample, of_apply, zero_le, and_true,
    Fin.lt_def]
  by_cases hj : (j : ℕ) = n - 1
  · simp [hj]
  · by_cases hij : i = j
    · simp [hij]
    · simp [hj, hij]

private theorem elimStep_growthStage {k : ℕ} (hk : k < n) :
    elimStep (growthStage n k) ⟨k, hk⟩ = growthStage n (k + 1) := by
  ext i j
  rw [elimStep_apply]
  by_cases hki : k < (i : ℕ)
  · rw [ite_eq_left (Fin.lt_def.2 hki)]
    have hkn : k ≠ n - 1 := by have := i.2; omega
    have h1 : growthStage n k i ⟨k, hk⟩ = -1 := by
      simp only [growthStage, of_apply, hkn, ite_false, Fin.ext_iff]
      rw [ite_eq_right (by omega), ite_eq_left ⟨hki, le_rfl⟩]
    have h2 : growthStage n k ⟨k, hk⟩ ⟨k, hk⟩ = 1 := by
      simp [growthStage, hkn]
    rw [h1, h2]
    simp only [growthStage, of_apply, Fin.ext_iff]
    by_cases hj : (j : ℕ) = n - 1
    · simp only [hj, ite_true, min_self]
      rw [min_eq_right hki.le, min_eq_right (by omega : k + 1 ≤ (i : ℕ)), pow_succ]
      ring
    · simp only [hj, ite_false]
      by_cases hjk : (j : ℕ) = k
      · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, ite_eq_left hjk.symm,
          ite_eq_right (by omega), ite_eq_right (by omega)]
        ring
      · rw [ite_eq_right (Ne.symm hjk), ite_eq_right (by omega : ¬ ((j : ℕ) < k ∧ k ≤ (j : ℕ)))]
        by_cases hij : (i : ℕ) = j
        · simp [hij]
        · rw [ite_eq_right hij, ite_eq_right hij]
          by_cases hc : (j : ℕ) < i ∧ k ≤ (j : ℕ)
          · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, by omega⟩]; ring
          · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, by omega⟩)]; ring
  · rw [ite_eq_right (fun h => hki (Fin.lt_def.1 h)), sub_zero]
    simp only [growthStage, of_apply]
    rw [min_eq_left (by omega : (i : ℕ) ≤ k), min_eq_left (by omega : (i : ℕ) ≤ k + 1)]
    rw [ite_eq_right (fun h : (j : ℕ) < i ∧ k ≤ (j : ℕ) => by omega),
      ite_eq_right (fun h : (j : ℕ) < i ∧ k + 1 ≤ (j : ℕ) => by omega)]

private theorem gemStage_growthExample {k : ℕ} (hk : k ≤ n) :
    gemStage (growthExample n) k = growthStage n k := by
  induction k with
  | zero => exact growthStage_zero.symm
  | succ k ih =>
    rw [gemStage_succ_of_lt _ (by omega), ih (by omega), elimStep_growthStage]

/-- On a stage of the growth example, the first maximizing row of column $k$ is $k$. -/
private theorem partialPivotRow_growthStage {k : ℕ} (hk : k < n) :
    partialPivotRow (growthStage n k) ⟨k, hk⟩ = ⟨k, hk⟩ := by
  refine le_antisymm (partialPivotRow_le _ _ le_rfl fun r hr => ?_) (le_partialPivotRow _ _)
  rcases eq_or_lt_of_le hr with rfl | hlt
  · exact le_rfl
  have hlt' : k < (r : ℕ) := Fin.lt_def.1 hlt
  have hkn : k ≠ n - 1 := by have := r.2; omega
  simp only [growthStage, of_apply, hkn, ite_false]
  split_ifs <;> norm_num

private theorem gemPivotStage_growthExample {k : ℕ} (hk : k ≤ n) :
    gemPivotStage (growthExample n) partialPivotRow k = (growthStage n k, 1) := by
  induction k with
  | zero => rw [gemPivotStage_zero, growthStage_zero]
  | succ k ih =>
    rw [gemPivotStage_succ_of_lt _ _ (by omega), gemPivotSwap, ih (by omega)]
    simp only [partialPivotRow_growthStage (show k < n by omega), Equiv.swap_self,
      ← Equiv.Perm.one_def, Equiv.Perm.coe_one, mul_one, submatrix_id_id, elimStep_growthStage]

private theorem abs_growthStage_le (k : ℕ) (i j : Fin n) :
    |growthStage n k i j| ≤ 2 ^ (n - 1) := by
  simp only [growthStage, of_apply]
  have h1 : (1 : ℝ) ≤ 2 ^ (n - 1) := one_le_pow₀ (by norm_num)
  split_ifs
  · rw [abs_of_pos (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (by have := i.2; omega)
  · simpa using h1
  · simpa using h1
  · simp

/-- **Section 3.4.5** of [golub2013matrix], no interchanges on the growth example. Gaussian
elimination with partial pivoting on the growth example performs no interchange: the accumulated
permutation of `Matrix.gemPivotStage (GolubVanLoan.Chapter03.growthExample n)
Matrix.partialPivotRow` is the identity. Its growth factor `Matrix.growthFactor` is $2^{n-1}$
for $n \ge 1$.

The stage $A^{(k)}$ has last column $2^{\min(i, k)}$, the entry $u_{nn} = 2^{n-1}$ is the
largest, and the entries of $A$ are at most $1$ in modulus. -/
theorem growthExample_noInterchange :
    (gemPivotStage (growthExample n) partialPivotRow n).2 = 1 ∧
      (0 < n → growthFactor (growthExample n) = 2 ^ (n - 1)) := by
  refine ⟨by rw [gemPivotStage_growthExample le_rfl], fun hn => ?_⟩
  have hsup : (growthExample n).supAbs = 1 := by
    refine le_antisymm (supAbs_le zero_le_one fun i j => ?_) ?_
    · simp only [growthExample, of_apply]
      split_ifs <;> simp
    · have : |growthExample n ⟨0, hn⟩ ⟨0, hn⟩| = 1 := by simp [growthExample]
      rw [← this]
      exact le_ciSup (f := fun p : Fin n × Fin n => |growthExample n p.1 p.2|)
        (Set.finite_range _).bddAbove (⟨0, hn⟩, ⟨0, hn⟩)
  have : Nonempty (Fin n × Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩)⟩
  unfold growthFactor
  rw [hsup, div_one]
  refine le_antisymm (ciSup_le fun p => ?_) ?_
  · rw [gemStage_growthExample p.1.2.le]
    exact abs_growthStage_le _ _ _
  · have hl : |gemStage (growthExample n) (n - 1) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩| =
        2 ^ (n - 1) := by
      rw [gemStage_growthExample (by omega)]
      simp [growthStage]
    rw [← hl]
    exact le_ciSup (f := fun p : Fin n × Fin n × Fin n => |gemStage (growthExample n) p.1 p.2.1
      p.2.2|) (Set.finite_range _).bddAbove (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩,
        ⟨n - 1, by omega⟩)

end GrowthExample

/-! ### Underdetermined systems (§3.4.8) -/

section Underdetermined

variable {m p : ℕ}

/-- For $U_1 \in \mathbb{R}^{m \times m}$, $U_2 \in \mathbb{R}^{m \times p}$, $z_1 \in \mathbb{R}^m$
and $z_2 \in \mathbb{R}^p$, the block matrix $[U_1 \mid U_2]$ applied to $[z_1; z_2]$ is
$U_1 z_1 + U_2 z_2$. -/
theorem fromCols_submatrix_mulVec_append (U₁ : Matrix (Fin m) (Fin m) ℝ)
    (U₂ : Matrix (Fin m) (Fin p) ℝ) (z₁ : Fin m → ℝ) (z₂ : Fin p → ℝ) :
    (fromCols U₁ U₂).submatrix id finSumFinEquiv.symm *ᵥ Fin.append z₁ z₂ =
      U₁ *ᵥ z₁ + U₂ *ᵥ z₂ := by
  funext i
  simp only [mulVec, dotProduct, submatrix_apply, id, Fin.sum_univ_add, Pi.add_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl,
    fromCols_apply_inr, Fin.append_left, Fin.append_right]

/-- **Equation (3.4.11)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with $n = m + p$
and $\operatorname{rank} A = m$. Then there are permutation matrices $P$ and $Q$, a unit lower
triangular $L \in \mathbb{R}^{m \times m}$, a nonsingular upper triangular
$U_1 \in \mathbb{R}^{m \times m}$ and $U_2 \in \mathbb{R}^{m \times p}$ with
$$PAQ^T = L \begin{bmatrix} U_1 & U_2 \end{bmatrix}.$$

The source assumes $m < n$; the theorem also allows $p = 0$. The matrix $PAQ^T$ is
`A.submatrix σ ρ` for two permutations of the rows and the columns.
The block matrix $[U_1 \mid U_2]$ is `fromCols U₁ U₂`, read on `Fin (m + p)`. The proof works
with the specification: $m$ independent columns are moved first, and their square block has a
pivoted LU factorization. -/
theorem equation_3_4_11 (A : Matrix (Fin m) (Fin (m + p)) ℝ) (hA : A.rank = m) :
    ∃ (σ : Equiv.Perm (Fin m)) (ρ : Equiv.Perm (Fin (m + p))) (L U₁ : Matrix (Fin m) (Fin m) ℝ)
      (U₂ : Matrix (Fin m) (Fin p) ℝ), L.IsUnitLowerTriangular ∧ U₁.IsUpperTriangular ∧
        IsUnit U₁ ∧ A.submatrix σ ρ = L * (fromCols U₁ U₂).submatrix id finSumFinEquiv.symm := by
  classical
  obtain ⟨c, hc⟩ := exists_linearIndependent_col A hA
  have hinj : Function.Injective c := hc.injective.of_comp
  let e : {x // x ∈ Set.range (Fin.castAdd p : Fin m → Fin (m + p))} ≃ {x // x ∈ Set.range c} :=
    (Equiv.ofInjective _ (Fin.castAdd_injective m p)).symm.trans (Equiv.ofInjective c hinj)
  let ρ : Equiv.Perm (Fin (m + p)) := e.extendSubtype
  have hρ : ∀ k, ρ (Fin.castAdd p k) = c k := fun k => by
    have h := e.extendSubtype_apply_of_mem (Fin.castAdd p k) ⟨k, rfl⟩
    rw [h]
    simp [e, Equiv.ofInjective_symm_apply]
  let B : Matrix (Fin m) (Fin m) ℝ := of fun i k => A i (c k)
  have hcol : B.col = A.col ∘ c := by funext k i; rfl
  have hB : IsUnit B := linearIndependent_col_iff_isUnit.1 (hcol ▸ hc)
  obtain ⟨σ, L, U₁, hLU, -⟩ := exists_permMatrix_mul_isLU B
  have hU₁ : IsUnit U₁ := by
    have hPB : IsUnit (L * U₁) := hLU.mul_eq ▸ (isUnit_permMatrix σ).mul hB
    rw [isUnit_iff_isUnit_det] at hPB ⊢
    rw [det_mul] at hPB
    exact isUnit_of_mul_isUnit_right hPB
  have hLu : IsUnit L := hLU.isUnitLowerTriangular.isUnit
  have hLd : IsUnit L.det := (isUnit_iff_isUnit_det _).1 hLu
  refine ⟨σ, ρ, L, U₁, L⁻¹ * of fun i k => A (σ i) (ρ (Fin.natAdd m k)),
    hLU.isUnitLowerTriangular, hLU.isUpperTriangular, hU₁, ?_⟩
  ext i j
  induction j using Fin.addCases with
  | left k =>
    have h := congrFun (congrFun hLU.mul_eq i) k
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul] at h
    simp only [submatrix_apply, id, hρ, Matrix.mul_apply, finSumFinEquiv_symm_apply_castAdd,
      fromCols_apply_inl]
    rw [← Matrix.mul_apply, h]
    rfl
  | right k =>
    have hX : L * (L⁻¹ * of fun i k => A (σ i) (ρ (Fin.natAdd m k))) =
        of fun i k => A (σ i) (ρ (Fin.natAdd m k)) := by
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ hLd, Matrix.one_mul]
    have h := congrFun (congrFun hX i) k
    simp only [submatrix_apply, id, Matrix.mul_apply, finSumFinEquiv_symm_apply_natAdd,
      fromCols_apply_inr]
    simp only [Matrix.mul_apply] at h
    rw [h]
    rfl

/-- **Section 3.4.8** of [golub2013matrix], Steps 1–3 of the solution of an underdetermined system.
Let $A \in \mathbb{R}^{m \times (m+p)}$ and let $PAQ^T = L[U_1 \mid U_2]$ with $L$ unit lower
triangular and $U_1$ nonsingular, as in (3.4.11). Let $b \in \mathbb{R}^m$ and
$z_2 \in \mathbb{R}^p$. Let $y$ solve $Ly = Pb$, let $z_1$ solve $U_1 z_1 = y - U_2 z_2$, and
let $x = Q^T [z_1; z_2]$. Then
$$Ax = b.$$

The source derives this from $Ax = b \iff L(U_1 z_1 + U_2 z_2) = c$ with $c = Pb$ and
$[z_1; z_2] = Qx$, and notes that $z_2 = 0$ is a natural choice. In Lean, $Pb$ is `b ∘ σ`, and
$x$ is `Fin.append z₁ z₂ ∘ ρ.symm`. -/
theorem underdetermined_solve {A : Matrix (Fin m) (Fin (m + p)) ℝ} {σ : Equiv.Perm (Fin m)}
    {ρ : Equiv.Perm (Fin (m + p))} {L U₁ : Matrix (Fin m) (Fin m) ℝ} {U₂ : Matrix (Fin m) (Fin p) ℝ}
    (hL : L.IsUnitLowerTriangular) (hU₁ : IsUnit U₁)
    (hA : A.submatrix σ ρ = L * (fromCols U₁ U₂).submatrix id finSumFinEquiv.symm)
    (b : Fin m → ℝ) (z₂ : Fin p → ℝ) :
    A *ᵥ (Fin.append (U₁⁻¹ *ᵥ (L⁻¹ *ᵥ (b ∘ σ) - U₂ *ᵥ z₂)) z₂ ∘ ρ.symm) = b := by
  have hLd : IsUnit L.det := (isUnit_iff_isUnit_det _).1 hL.isUnit
  have hUd : IsUnit U₁.det := (isUnit_iff_isUnit_det _).1 hU₁
  set z := Fin.append (U₁⁻¹ *ᵥ (L⁻¹ *ᵥ (b ∘ σ) - U₂ *ᵥ z₂)) z₂
  have hz : A.submatrix σ ρ *ᵥ z = b ∘ σ := by
    rw [hA, ← mulVec_mulVec, fromCols_submatrix_mulVec_append, mulVec_mulVec,
      mul_nonsing_inv _ hUd, one_mulVec, sub_add_cancel, mulVec_mulVec, mul_nonsing_inv _ hLd,
      one_mulVec]
  funext i
  have h := congrFun hz (σ.symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
  rw [← h]
  simp only [mulVec, dotProduct, submatrix_apply, Equiv.apply_symm_apply, Function.comp_apply]
  exact (Fintype.sum_equiv ρ _ _ fun j => by simp).symm

end Underdetermined

/-! ### Where is $L$? (§3.4.3) -/

section WhereIsL

variable {n : ℕ}

/-- Conjugating a Gauss transformation by a permutation that fixes the indices up to $k$ gives the
Gauss transformation of the permuted Gauss vector: if $P$ is the permutation matrix of such a
permutation, then $P(I - \tau e_k^T)P^T = I - (P\tau)e_k^T$. -/
theorem permMatrix_mul_gaussTransformation_mul_transpose {ρ : Equiv.Perm (Fin n)} {k : Fin n}
    (hρ : ∀ r, r ≤ k → ρ r = r) (τ : Fin n → ℝ) :
    ρ.permMatrix ℝ * gaussTransformation τ k * (ρ.permMatrix ℝ)ᵀ =
      gaussTransformation (ρ.permMatrix ℝ *ᵥ τ) k :=
  permMatrix_mul_one_sub_vecMulVec_single_mul_transpose (hρ k le_rfl) τ

/-- **Equation (3.4.5)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$, let $k$ be an
index, and let $\tau \in \mathbb{R}^n$ with $\tau_i = 0$ for $i \le k$. Let $P'$ be the
permutation matrix of the interchanges of partial pivoting on $A$ after step $k$. Then
$P'(I - \tau e_k^T)P'^T$ is a Gauss transformation at $k$, and
$$P'(I - \tau e_k^T)P'^T = I - \tilde\tau e_k^T, \qquad \tilde\tau = P'\tau.$$
In particular this holds for the Gauss transformation $M_k$ of step $k$, which gives
$\tilde M_k = P' M_k P'^T$.

The source writes $P' = \Pi_{n-1} \cdots \Pi_{k+1}$. In Lean, $P'$ is the permutation matrix of
$\sigma_{k+1}^{-1} \sigma_n$, where $\sigma_j$ is the permutation of
`Matrix.gemPivotStage A Matrix.partialPivotRow` after $j$ steps; this permutation fixes the
indices up to $k$. -/
theorem equation_3_4_5 (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (τ : Fin n → ℝ)
    (hτ : ∀ i, i ≤ k → τ i = 0) :
    IsGaussTransformation (((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
        (gemPivotStage A partialPivotRow n).2).permMatrix ℝ * gaussTransformation τ k *
        (((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
          (gemPivotStage A partialPivotRow n).2).permMatrix ℝ)ᵀ) k ∧
      ((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
          (gemPivotStage A partialPivotRow n).2).permMatrix ℝ * gaussTransformation τ k *
          (((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
            (gemPivotStage A partialPivotRow n).2).permMatrix ℝ)ᵀ =
        gaussTransformation (((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
          (gemPivotStage A partialPivotRow n).2).permMatrix ℝ *ᵥ τ) k := by
  have hfix : ∀ r, r ≤ k → ((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
      (gemPivotStage A partialPivotRow n).2) r = r := fun r hr =>
    gemPivotStage_snd_inv_mul_apply A partialPivotRow (fun M k => le_partialPivotRow M k)
      (Nat.succ_le_of_lt k.2) (Nat.lt_succ_of_le (Fin.le_def.1 hr))
  have heq := permMatrix_mul_gaussTransformation_mul_transpose hfix τ
  refine ⟨⟨_, fun i hi => ?_, heq⟩, heq⟩
  rw [permMatrix_mulVec, Function.comp_apply, hfix i hi]
  exact hτ i hi

/-- **Section 3.4.3** of [golub2013matrix], the matrix $\tilde M_k = P' M_k P'^T$ of (3.4.5). Here
$M_k$ is the Gauss transformation of step $k$ of partial pivoting on $A$, as in (3.4.2), and
$P'$ is the permutation matrix of the later interchanges.

In Lean, $P'$ is the permutation matrix of $\sigma_{k+1}^{-1} \sigma_n$, where $\sigma_j$ is the
permutation of `Matrix.gemPivotStage A Matrix.partialPivotRow` after $j$ steps. -/
noncomputable def pivotedGaussTransformation (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
      (gemPivotStage A partialPivotRow n).2).permMatrix ℝ *
    gaussTransformation (gaussVector
      (fun i => (interchange k (partialPivotRow (partialPivotStage A k) k) *
        partialPivotStage A k) i k) k) k *
    (((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
      (gemPivotStage A partialPivotRow n).2).permMatrix ℝ)ᵀ

/-- **Equation (3.4.4)** of [golub2013matrix], the answer of the source to "where is $L$?". Let
$A \in \mathbb{R}^{n \times n}$, let $P$ be the permutation matrix of partial pivoting on $A$,
and let $(PA)^{(k)}$ be the stages of elimination without pivoting on $PA$. Then for every step
$k$,
$$\tilde M_k (PA)^{(k)} = (PA)^{(k+1)},$$
so each $\tilde M_k$ is the Gauss transformation of step $k$ of elimination without pivoting on
$PA$, and
$$\tilde M_{n-1} \cdots \tilde M_1 PA = U,$$
where $U$ is the last stage of partial pivoting.

Hence $L = (\tilde M_{n-1} \cdots \tilde M_1)^{-1}$ is the unit lower factor of $PA$, whose
columns are the permuted multipliers (`GolubVanLoan.Chapter03.equation_3_4_5`). The matrices
$\tilde M_k$ are `GolubVanLoan.Chapter03.pivotedGaussTransformation`, and the stages are
`Matrix.gemStage`. -/
theorem equation_3_4_4 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ k : Fin n, pivotedGaussTransformation A k *
        gemStage ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) k =
      gemStage ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) (k + 1)) ∧
      (List.finRange n).foldl (fun B k => pivotedGaussTransformation A k * B)
          ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) =
        partialPivotStage A n := by
  have hpiv : ∀ (M : Matrix (Fin n) (Fin n) ℝ) k, k ≤ partialPivotRow M k :=
    fun M k => le_partialPivotRow M k
  have hsub : ∀ (σ : Equiv.Perm (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ),
      B.submatrix σ id = σ.permMatrix ℝ * B := fun σ B => by
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  have hstep : ∀ k : Fin n, pivotedGaussTransformation A k *
      gemStage ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) k =
      gemStage ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) (k + 1) := by
    intro k
    have hσ : (gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2 =
        (gemPivotStage A partialPivotRow k).2 *
          Equiv.swap k (partialPivotRow (partialPivotStage A k) k) := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow k.2]
      rfl
    have hρ : (gemPivotStage A partialPivotRow k).2⁻¹ * (gemPivotStage A partialPivotRow n).2 =
        Equiv.swap k (partialPivotRow (partialPivotStage A k) k) *
          ((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
            (gemPivotStage A partialPivotRow n).2) := by
      rw [hσ]
      group
    have h3 : (gemPivotStage A partialPivotRow ((k : ℕ) + 1)).1 =
        gaussTransformation (gaussVector
          (fun i => (interchange k (partialPivotRow (partialPivotStage A k) k) *
            partialPivotStage A k) i k) k) k *
          (interchange k (partialPivotRow (partialPivotStage A k) k) * partialPivotStage A k) :=
      (equation_3_4_2 A).1 k
    have hPP : ∀ ρ : Equiv.Perm (Fin n), (ρ.permMatrix ℝ)ᵀ * ρ.permMatrix ℝ = 1 := fun ρ => by
      rw [transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
    rw [gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A partialPivotRow hpiv k,
      gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A partialPivotRow hpiv ((k : ℕ) + 1),
      hsub, hsub, h3, hρ, permMatrix_mul]
    simp only [pivotedGaussTransformation, interchange, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.transpose _), hPP, Matrix.one_mul]
  refine ⟨hstep, ?_⟩
  have hfold : ∀ m ≤ n, ((List.finRange n).take m).foldl
      (fun B k => pivotedGaussTransformation A k * B)
      ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) =
      gemStage ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [List.take_succ_eq_append_getElem (by simpa using hm), List.foldl_append,
        List.foldl_cons, List.foldl_nil, ih (by omega)]
      have hget : (List.finRange n)[m]'(by simpa using hm) = ⟨m, hm⟩ := by simp
      rw [hget]
      exact hstep ⟨m, hm⟩
  rw [← List.take_length (l := List.finRange n), List.length_finRange, hfold n le_rfl,
    gemStage_permMatrix_mul_card A partialPivotRow hpiv]

end WhereIsL

end GolubVanLoan.Chapter03
