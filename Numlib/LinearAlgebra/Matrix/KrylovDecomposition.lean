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
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Numlib.Data.Fin.Sum
import Numlib.Data.Matrix.Mul
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg

/-!
# Krylov and Arnoldi decompositions, and the implicit Q theorem

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $A \in \mathbb{K}^{n \times n}$. A
**Krylov decomposition** of $A$, in the sense of Stewart, is an identity
$$A Q = Q B + r b^T$$
in which $Q \in \mathbb{K}^{n \times m}$ has orthonormal columns $q_i$, the residual
$r \in \mathbb{K}^n$ is orthogonal to them, and $B \in \mathbb{K}^{m \times m}$ and
$b \in \mathbb{K}^m$ are arbitrary. An **Arnoldi decomposition** is the case in which $B = H$ is
upper Hessenberg and $b = e_k$ is the last unit vector, as in the definition after (10.5.2) in
§10.5.1 of [golub2013matrix]. A unitary reduction $Q^H A Q = H$ to Hessenberg form is an Arnoldi
decomposition with zero residual. Its leading $j + 1$ columns form an Arnoldi decomposition with the
residual $h_{j+1,j} q_{j+1}$. The Arnoldi process produces an Arnoldi decomposition at every step
(`Numlib.Krylov.Decomposition`).

The main result is the **implicit Q theorem**: two Arnoldi decompositions of $A$ with the same first
column, the first with unreduced $H$, agree up to a diagonal matrix $D$ with unimodular entries.
This holds for decompositions with any number of columns. The square forms of Theorem 7.4.2 of
[golub2013matrix] follow as corollaries. Columns are indexed from $0$, so that $q_0$ is the first
column and $e_0$ the first unit vector.

## Main definitions

* `Matrix.IsKrylovDecomposition`: $Q^H Q = I$, $Q^H r = 0$ and $A Q = Q B + r b^T$.
* `Matrix.IsArnoldiDecomposition`: a Krylov decomposition with $k + 1$ columns, $B = H$ upper
  Hessenberg and $b = e_k$.

## Main results

* `Matrix.IsKrylovDecomposition.conjTranspose_mul_mul`: the matrix of a Krylov decomposition is the
  compression $B = Q^H A Q$.
* `Matrix.IsKrylovDecomposition.mul_of_conjTranspose_mul_self`: a change of basis $Q \mapsto QU$,
  $B \mapsto U^H B U$ with unitary $U$ gives a Krylov decomposition ([golub2013matrix] (10.5.9) and
  §10.5.4).
* `Matrix.IsKrylovDecomposition.leading`: the leading $j + 1$ columns form a Krylov decomposition,
  whose residual collects what the discarded columns contribute to column $j$. This lemma is behind
  implicit restarting, Krylov–Schur restarting and the square implicit Q theorem.
* `Matrix.IsKrylovDecomposition.leading_of_apply_eq_zero`: truncation across a zero block, with the
  same residual vector and the restricted residual row, as in Krylov–Schur restarting.
* `Matrix.IsArnoldiDecomposition.implicitQ`: the implicit Q theorem for Arnoldi decompositions with
  $k + 1$ columns: $Q' = QD$, $H' = D^H H D$ and $r' = d_k r$ for a unimodular diagonal
  $D = \operatorname{diag}(d)$ with $d_0 = 1$.
* `Matrix.IsArnoldiDecomposition.aeval_mulVec_first`: for a polynomial $p$ of degree at most $k$,
  $p(A) Q e_0 = Q\, p(H) e_0$ ([golub2013matrix] §10.5.3).
* `Matrix.implicitQ_of_apply_eq_zero`, `Matrix.implicitQ`: Theorem 7.4.2 of [golub2013matrix] for
  unitary $Q$ and $V$, in the form of the source with a first vanishing subdiagonal entry, and in
  the unreduced case.
* `Matrix.implicitQ_of_apply_eq_zero_real`, `Matrix.implicitQ_real`: the same for real orthogonal
  $Q$ and $V$, with $D = \operatorname{diag}(\pm 1)$.

## Proof outline

Column $i < k$ of an Arnoldi decomposition gives the recurrence
$$h_{i+1,i} q_{i+1} = A q_i - \sum_{l \le i} h_{li} q_l,$$
as in the proof of Theorem 7.4.2 of [golub2013matrix]. The implicit Q theorem follows by induction
on $i$ from these recurrences for the two decompositions. The square theorems apply it to the
leading columns of the two unitary reductions.

## Implementation notes

* The predicates are matrix statements over `[RCLike 𝕜]`. The predicates for an orthonormal family
  in an inner product space are `Krylov.IsKrylovDecomposition` and `Krylov.IsArnoldiDecomposition`
  of `Numlib.Krylov.Decomposition`. That module proves that the predicates here are their instances
  for `Matrix.toEuclideanLin`.
* An Arnoldi decomposition has $k + 1$ columns, indexed by `Fin (k + 1)`, so that the last unit
  vector `Pi.single (Fin.last k) 1` and the first column `Q *ᵥ Pi.single 0 1` are well typed.
* The implicit Q theorem needs neither a square $Q$ nor a unitary $V^H Q$. The orthonormal columns
  and the Hessenberg shape carry the induction.
-/

open Finset

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Krylov decompositions -/

section Krylov

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A **Krylov decomposition** of $A \in \mathbb{K}^{n \times n}$ is an identity
$$A Q = Q B + r b^T,$$
where $Q \in \mathbb{K}^{n \times m}$ has orthonormal columns ($Q^H Q = I$), the residual
$r \in \mathbb{K}^n$ is orthogonal to the columns of $Q$ ($Q^H r = 0$), and
$B \in \mathbb{K}^{m \times m}$ and $b \in \mathbb{K}^m$ are arbitrary.

The notion is due to Stewart. It follows §10.5.4 of [golub2013matrix]. The term $r b^T$ is
`Matrix.vecMulVec r b`, without complex conjugation. -/
structure IsKrylovDecomposition (A : Matrix n n 𝕜) (Q : Matrix n m 𝕜) (B : Matrix m m 𝕜)
    (r : n → 𝕜) (b : m → 𝕜) : Prop where
  /-- The columns of $Q$ are orthonormal: $Q^H Q = I$. -/
  conjTranspose_mul_self : Qᴴ * Q = 1
  /-- The residual is orthogonal to the columns of $Q$: $Q^H r = 0$. -/
  conjTranspose_mulVec : Qᴴ *ᵥ r = 0
  /-- The decomposition $A Q = Q B + r b^T$. -/
  mul_eq : A * Q = Q * B + vecMulVec r b

namespace IsKrylovDecomposition

variable {A : Matrix n n 𝕜} {Q : Matrix n m 𝕜} {B : Matrix m m 𝕜} {r : n → 𝕜} {b : m → 𝕜}

/-- The columns $q_i$ of $Q$ in a Krylov decomposition are orthonormal: for all $i$ and $j$,
$$q_i^H q_j = \delta_{ij}.$$
-/
theorem star_col_dotProduct_col (h : IsKrylovDecomposition A Q B r b) (i j : m) :
    star (Q.col i) ⬝ᵥ Q.col j = (1 : Matrix m m 𝕜) i j := by
  rw [← h.conjTranspose_mul_self, Matrix.mul_apply]
  rfl

/-- In a Krylov decomposition, the residual is orthogonal to every column of $Q$: $q_i^H r = 0$. -/
theorem star_col_dotProduct_residual (h : IsKrylovDecomposition A Q B r b) (i : m) :
    star (Q.col i) ⬝ᵥ r = 0 :=
  congrFun h.conjTranspose_mulVec i

/-- Column $j$ of a Krylov decomposition $A Q = Q B + r b^T$ reads
$$A q_j = \sum_i b_{ij} q_i + b_j r,$$
where $b_{ij}$ are the entries of $B$ and $b_j$ is the $j$-th entry of $b$. -/
theorem mulVec_col (h : IsKrylovDecomposition A Q B r b) (j : m) :
    A *ᵥ Q.col j = ∑ i, B i j • Q.col i + b j • r := by
  have hc := congrArg (fun M : Matrix n m 𝕜 => M.col j) h.mul_eq
  simp only [col_mul_eq_mulVec_col] at hc
  rw [hc]
  ext x
  simp [Matrix.mul_apply, vecMulVec_apply, Finset.sum_apply, mul_comm]

/-- The entries of the matrix of a Krylov decomposition $A Q = Q B + r b^T$ are those of the
compression of $A$: for all $i$ and $j$,
$$B_{ij} = q_i^H A q_j.$$
-/
theorem apply_eq_star_col_dotProduct (h : IsKrylovDecomposition A Q B r b) (i j : m) :
    B i j = star (Q.col i) ⬝ᵥ (A *ᵥ Q.col j) := by
  rw [h.mulVec_col, dotProduct_add, dotProduct_sum, dotProduct_smul,
    h.star_col_dotProduct_residual]
  simp [dotProduct_smul, h.star_col_dotProduct_col, Matrix.one_apply]

/-- The matrix of a Krylov decomposition $A Q = Q B + r b^T$ is the compression of $A$:
$$Q^H A Q = B.$$
-/
theorem conjTranspose_mul_mul (h : IsKrylovDecomposition A Q B r b) : Qᴴ * A * Q = B := by
  rw [Matrix.mul_assoc, h.mul_eq, Matrix.mul_add, ← Matrix.mul_assoc, h.conjTranspose_mul_self,
    Matrix.one_mul, mul_vecMulVec, h.conjTranspose_mulVec, zero_vecMulVec, add_zero]

/-- **Change of basis.** Let $A Q = Q B + r b^T$ be a Krylov decomposition, and let
$U \in \mathbb{K}^{m \times m}$ satisfy $U^H U = I$. Then
$$A (Q U) = (Q U)(U^H B U) + r (U^T b)^T$$
is a Krylov decomposition.

This is (10.5.9) and §10.5.4 of [golub2013matrix]. The new residual row $(U^T b)^T = b^T U$ is
`b ᵥ* U`. -/
theorem mul_of_conjTranspose_mul_self (h : IsKrylovDecomposition A Q B r b) {U : Matrix m m 𝕜}
    (hU : Uᴴ * U = 1) : IsKrylovDecomposition A (Q * U) (Uᴴ * B * U) r (b ᵥ* U) where
  conjTranspose_mul_self := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, h.conjTranspose_mul_self,
      Matrix.one_mul, hU]
  conjTranspose_mulVec := by
    rw [conjTranspose_mul, ← mulVec_mulVec, h.conjTranspose_mulVec, mulVec_zero]
  mul_eq := by
    have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
    rw [← Matrix.mul_assoc, h.mul_eq, Matrix.add_mul, vecMulVec_mul]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc Q U Uᴴ, hU', Matrix.mul_one]

/-- **Truncation to the leading $j + 1$ columns.** Let $A Q = Q B + r b^T$ be a Krylov decomposition
with $k$ columns $q_0, \dots, q_{k-1}$, and let $j < k$. Suppose that $B_{il} = 0$ whenever
$l < j < i$, and that $b_l = 0$ for $l < j$. Let $Q_j$ consist of the columns $q_0, \dots, q_j$
and let $B_j$ be the leading principal submatrix of $B$ of order $j + 1$. Then
$$A Q_j = Q_j B_j + r' e_j^T, \qquad r' = \sum_{i > j} B_{ij} q_i + b_j r,$$
is a Krylov decomposition, where $e_j$ is the last unit vector of $\mathbb{K}^{j+1}$.

The residual $r'$ collects what the discarded columns contribute to column $j$. For an upper
Hessenberg $B$ the first hypothesis always holds, and $r' = B_{j+1,j} q_{j+1} + b_j r$ when
$j + 1 < k$. The columns $q_0, \dots, q_j$ are `Q.submatrix id (Fin.castLE j.isLt)`. -/
theorem leading {k : ℕ} {Q : Matrix n (Fin k) 𝕜} {B : Matrix (Fin k) (Fin k) 𝕜}
    {b : Fin k → 𝕜} (h : IsKrylovDecomposition A Q B r b) (j : Fin k)
    (hB : ∀ i l : Fin k, l < j → j < i → B i l = 0) (hb : ∀ l : Fin k, l < j → b l = 0) :
    IsKrylovDecomposition A (Q.submatrix id (Fin.castLE j.isLt))
      (B.submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt))
      (∑ i ∈ Ioi j, B i j • Q.col i + b j • r) (Pi.single (Fin.last j) 1) where
  conjTranspose_mul_self := by
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id,
      h.conjTranspose_mul_self, submatrix_one _ (Fin.castLE_injective _)]
  conjTranspose_mulVec := by
    ext a
    change star (Q.col (Fin.castLE j.isLt a)) ⬝ᵥ _ = 0
    rw [dotProduct_add, dotProduct_sum, dotProduct_smul, h.star_col_dotProduct_residual,
      smul_zero, add_zero]
    refine sum_eq_zero fun i hi => ?_
    rw [dotProduct_smul, h.star_col_dotProduct_col, one_apply_ne, smul_zero]
    intro hai
    have hi' := mem_Ioi.1 hi
    rw [← hai, Fin.lt_def, Fin.val_castLE] at hi'
    omega
  mul_eq := by
    ext x a
    have hcol := congrFun (congrFun h.mul_eq x) (Fin.castLE j.isLt a)
    simp only [Matrix.mul_apply, Matrix.add_apply, vecMulVec_apply, submatrix_apply, id] at hcol ⊢
    rw [hcol, Fin.sum_eq_sum_castLE_add_sum_Ioi j (fun i => Q x i * B i (Fin.castLE j.isLt a)),
      add_assoc]
    congr 1
    by_cases ha : a = Fin.last j
    · have hf : Fin.castLE j.isLt (Fin.last j) = j := Fin.ext (by simp)
      rw [ha, Pi.single_eq_same, mul_one, hf, Pi.add_apply, Finset.sum_apply]
      simp [mul_comm]
    · have hlt : Fin.castLE j.isLt a < j := by
        rw [Fin.lt_def, Fin.val_castLE]; exact Fin.val_lt_last ha
      rw [Pi.single_eq_of_ne ha, mul_zero, hb _ hlt, mul_zero, add_zero]
      exact sum_eq_zero fun i hi => by rw [hB i _ hlt (mem_Ioi.1 hi), mul_zero]

/-- **Truncation across a zero block.** Let $A Q = Q B + r b^T$ be a Krylov decomposition with $k$
columns, and let $j < k$. Suppose that $B$ is block upper triangular for the split after index
$j$, that is, $B_{il} = 0$ whenever $l \le j < i$. Let $Q_j$ consist of the columns
$q_0, \dots, q_j$, let $B_j$ be the leading principal submatrix of $B$ of order $j + 1$, and let
$b' = (b_0, \dots, b_j)$. Then
$$A Q_j = Q_j B_j + r b'^T$$
is a Krylov decomposition, with the same residual vector $r$.

This is the truncation step of Krylov–Schur restarting, §10.5.4 of [golub2013matrix]. -/
theorem leading_of_apply_eq_zero {k : ℕ} {Q : Matrix n (Fin k) 𝕜} {B : Matrix (Fin k) (Fin k) 𝕜}
    {b : Fin k → 𝕜} (h : IsKrylovDecomposition A Q B r b) (j : Fin k)
    (hB : ∀ i l : Fin k, l ≤ j → j < i → B i l = 0) :
    IsKrylovDecomposition A (Q.submatrix id (Fin.castLE j.isLt))
      (B.submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt)) r (b ∘ Fin.castLE j.isLt) where
  conjTranspose_mul_self := by
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id,
      h.conjTranspose_mul_self, submatrix_one _ (Fin.castLE_injective _)]
  conjTranspose_mulVec := by
    ext a
    change star (Q.col (Fin.castLE j.isLt a)) ⬝ᵥ r = 0
    exact h.star_col_dotProduct_residual _
  mul_eq := by
    ext x a
    have hcol := congrFun (congrFun h.mul_eq x) (Fin.castLE j.isLt a)
    have ha : Fin.castLE j.isLt a ≤ j := by
      rw [Fin.le_def, Fin.val_castLE]
      exact Nat.lt_succ_iff.1 a.isLt
    simp only [Matrix.mul_apply, Matrix.add_apply, vecMulVec_apply, submatrix_apply, id,
      Function.comp_apply] at hcol ⊢
    have hz : ∑ i ∈ Ioi j, Q x i * B i (Fin.castLE j.isLt a) = 0 :=
      sum_eq_zero fun i hi => by rw [hB i _ ha (mem_Ioi.1 hi), mul_zero]
    rw [hcol, Fin.sum_eq_sum_castLE_add_sum_Ioi j (fun i => Q x i * B i (Fin.castLE j.isLt a)), hz,
      add_zero]

end IsKrylovDecomposition

/-- Let $Q \in \mathbb{K}^{m \times m}$ be unitary. Then, for every $A \in \mathbb{K}^{m \times m}$
and every $b \in \mathbb{K}^m$, the identity $A Q = Q (Q^H A Q) + 0 \cdot b^T$ is a Krylov
decomposition with zero residual. -/
theorem isKrylovDecomposition_of_mem_unitaryGroup {Q : Matrix m m 𝕜}
    (hQ : Q ∈ unitaryGroup m 𝕜) (A : Matrix m m 𝕜) (b : m → 𝕜) :
    IsKrylovDecomposition A Q (star Q * A * Q) 0 b where
  conjTranspose_mul_self := (mem_unitaryGroup_iff').1 hQ
  conjTranspose_mulVec := mulVec_zero _
  mul_eq := by
    rw [zero_vecMulVec, add_zero, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      (mem_unitaryGroup_iff).1 hQ, Matrix.one_mul]

end Krylov

/-! ### Arnoldi decompositions and the implicit Q theorem -/

section Arnoldi

/-- An **Arnoldi decomposition** of $A \in \mathbb{K}^{n \times n}$ with $k + 1$ columns is a Krylov
decomposition
$$A Q = Q H + r e_k^T,$$
where $Q \in \mathbb{K}^{n \times (k+1)}$ has orthonormal columns $q_0, \dots, q_k$, the
residual $r$ is orthogonal to them, $H \in \mathbb{K}^{(k+1) \times (k+1)}$ is upper Hessenberg,
and $e_k$ is the last unit vector of $\mathbb{K}^{k+1}$.

This is the definition after (10.5.2) in §10.5.1 of [golub2013matrix]. The $k$-step
decomposition of the source has $k$ columns, so it is the case of $k - 1$ in place of $k$ here.
The vector $e_k$ is `Pi.single (Fin.last k) 1`. -/
structure IsArnoldiDecomposition {k : ℕ} (A : Matrix n n 𝕜) (Q : Matrix n (Fin (k + 1)) 𝕜)
    (H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜) (r : n → 𝕜) : Prop
    extends IsKrylovDecomposition A Q H r (Pi.single (Fin.last k) 1) where
  /-- The matrix $H$ of an Arnoldi decomposition is upper Hessenberg. -/
  isUpperHessenberg : H.IsUpperHessenberg

/-- Let $A Q = Q B + r b^T$ be a Krylov decomposition with $k$ columns, in which $B$ is upper
Hessenberg. Let $j < k$, and suppose that $b_l = 0$ for $l < j$. Then the leading $j + 1$
columns form an Arnoldi decomposition
$$A Q_j = Q_j B_j + r' e_j^T, \qquad r' = \sum_{i > j} B_{ij} q_i + b_j r,$$
where $Q_j$ consists of the columns $q_0, \dots, q_j$ and $B_j$ is the leading principal
submatrix of $B$ of order $j + 1$.

This is `Matrix.IsKrylovDecomposition.leading` together with the Hessenberg shape of $B_j$. -/
theorem IsKrylovDecomposition.isArnoldiDecomposition_leading {k : ℕ} {A : Matrix n n 𝕜}
    {Q : Matrix n (Fin k) 𝕜} {B : Matrix (Fin k) (Fin k) 𝕜} {r : n → 𝕜} {b : Fin k → 𝕜}
    (h : IsKrylovDecomposition A Q B r b) (hB : B.IsUpperHessenberg) (j : Fin k)
    (hb : ∀ l : Fin k, l < j → b l = 0) :
    IsArnoldiDecomposition A (Q.submatrix id (Fin.castLE j.isLt))
      (B.submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt))
      (∑ i ∈ Ioi j, B i j • Q.col i + b j • r) where
  toIsKrylovDecomposition := h.leading j (fun i l hl hi => hB i l ⟨j, hl, hi⟩) hb
  isUpperHessenberg := hB.submatrix_of_strictMono fun _ _ hab => by
    rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]; exact hab

/-- A unitary reduction to Hessenberg form is an Arnoldi decomposition with zero residual. Let
$Q \in \mathbb{K}^{(N+1) \times (N+1)}$ be unitary, let $A \in \mathbb{K}^{(N+1) \times (N+1)}$,
and suppose that $Q^H A Q$ is upper Hessenberg. Then $A Q = Q (Q^H A Q) + 0 \cdot e_N^T$ is an
Arnoldi decomposition. -/
theorem isArnoldiDecomposition_of_mem_unitaryGroup {N : ℕ}
    {Q : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜} (hQ : Q ∈ unitaryGroup (Fin (N + 1)) 𝕜)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜} (hH : (star Q * A * Q).IsUpperHessenberg) :
    IsArnoldiDecomposition A Q (star Q * A * Q) 0 :=
  ⟨isKrylovDecomposition_of_mem_unitaryGroup hQ A _, hH⟩

namespace IsArnoldiDecomposition

variable {k : ℕ} {A : Matrix n n 𝕜} {Q : Matrix n (Fin (k + 1)) 𝕜}
  {H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜} {r : n → 𝕜}

/-- The **Arnoldi recurrence.** Let $A Q = Q H + r e_k^T$ be an Arnoldi decomposition with columns
$q_0, \dots, q_k$. Then, for every $i < k$,
$$h_{i+1,i} q_{i+1} = A q_i - \sum_{l \le i} h_{li} q_l.$$

This is column $i$ of the decomposition, where the residual does not appear because $i < k$. -/
theorem smul_col_succ (h : IsArnoldiDecomposition A Q H r) (i : Fin k) :
    H i.succ i.castSucc • Q.col i.succ =
      A *ᵥ Q.col i.castSucc - ∑ l ∈ Iic i.castSucc, H l i.castSucc • Q.col l := by
  rw [h.mulVec_col, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne, zero_smul, add_zero,
    ← sum_add_sum_compl (Iic i.castSucc), add_sub_cancel_left]
  rw [sum_eq_single_of_mem i.succ
    (by simp only [mem_compl, mem_Iic, not_le]; exact Fin.castSucc_lt_succ)]
  intro l hl hne
  simp only [mem_compl, mem_Iic, not_le] at hl
  have hsl : i.succ < l := by
    rw [Fin.lt_def] at hl ⊢
    have : (l : ℕ) ≠ i + 1 := fun h' => hne (Fin.ext (by simpa using h'))
    simp only [Fin.val_castSucc] at hl
    simp only [Fin.val_succ]
    omega
  rw [h.isUpperHessenberg l i.castSucc ⟨i.succ, Fin.castSucc_lt_succ, hsl⟩, zero_smul]

/-- The **implicit Q theorem** for Arnoldi decompositions. Let $A Q = Q H + r e_k^T$ and
$A Q' = Q' H' + r' e_k^T$ be two Arnoldi decompositions of the same
$A \in \mathbb{K}^{n \times n}$, each with $k + 1$ columns. Suppose that $H$ is unreduced upper
Hessenberg and that the two decompositions have the same first column, $Q' e_0 = Q e_0$. Then
there is $d \in \mathbb{K}^{k+1}$ with $|d_i| = 1$ for all $i$ and $d_0 = 1$ such that, with
$D = \operatorname{diag}(d)$,
$$Q' = Q D, \qquad H' = D^H H D, \qquad r' = d_k r.$$

This follows Theorem 7.4.2 and §10.5.1 of [golub2013matrix], in the form for $k$-step
decompositions. The proof is by induction on $i$. If $q'_l = d_l q_l$ for $l \le i$, then
$h'_{li} = \bar d_l h_{li} d_i$, and the recurrences of
`Matrix.IsArnoldiDecomposition.smul_col_succ` for $Q$ and $Q'$ give
$h'_{i+1,i} q'_{i+1} = d_i h_{i+1,i} q_{i+1}$. The right side is nonzero, and both $q_{i+1}$ and
$q'_{i+1}$ are unit vectors. -/
theorem implicitQ {Q' : Matrix n (Fin (k + 1)) 𝕜} {H' : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜}
    {r' : n → 𝕜} (h : IsArnoldiDecomposition A Q H r) (h' : IsArnoldiDecomposition A Q' H' r')
    (hH : H.IsUnreducedUpperHessenberg) (h0 : Q' *ᵥ Pi.single 0 1 = Q *ᵥ Pi.single 0 1) :
    ∃ d : Fin (k + 1) → 𝕜, (∀ i, ‖d i‖ = 1) ∧ d 0 = 1 ∧ Q' = Q * diagonal d ∧
      H' = star (diagonal d) * H * diagonal d ∧ r' = d (Fin.last k) • r := by
  set d : Fin (k + 1) → 𝕜 := fun l => star (Q.col l) ⬝ᵥ Q'.col l with hd
  have hq0 : Q'.col 0 = Q.col 0 := by rwa [← mulVec_single_one, ← mulVec_single_one]
  have hd0 : d 0 = 1 := by
    simp only [hd]
    rw [hq0, h.star_col_dotProduct_col, one_apply_eq]
  have key : ∀ t : ℕ, ∀ l : Fin (k + 1), (l : ℕ) ≤ t →
      Q'.col l = d l • Q.col l ∧ star (d l) * d l = 1 := by
    intro t
    induction t with
    | zero =>
      intro l hl
      obtain rfl : l = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [hd0, one_smul, star_one, one_mul]
      exact ⟨hq0, rfl⟩
    | succ t ih =>
      intro l hl
      rcases Nat.lt_or_ge (l : ℕ) (t + 1) with hlt | hge
      · exact ih l (by omega)
      have htk : t < k := by omega
      set i : Fin k := ⟨t, htk⟩ with hi
      obtain rfl : l = i.succ := Fin.ext (by simp [hi]; omega)
      have ihc : ∀ l ∈ Iic i.castSucc, Q'.col l = d l • Q.col l ∧ star (d l) * d l = 1 :=
        fun l hl => ih l (by
          have := Fin.le_def.1 (mem_Iic.1 hl); simp only [Fin.val_castSucc] at this; omega)
      obtain ⟨hqc, hdc⟩ := ihc i.castSucc (mem_Iic.2 le_rfl)
      -- the coefficients of the second decomposition
      have hH' : ∀ l ∈ Iic i.castSucc,
          H' l i.castSucc = star (d l) * d i.castSucc * H l i.castSucc := by
        intro l hl
        rw [h'.apply_eq_star_col_dotProduct, h.apply_eq_star_col_dotProduct, (ihc l hl).1, hqc,
          star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          mul_assoc]
      have hsum : ∑ l ∈ Iic i.castSucc, H' l i.castSucc • Q'.col l =
          d i.castSucc • ∑ l ∈ Iic i.castSucc, H l i.castSucc • Q.col l := by
        rw [smul_sum]
        refine sum_congr rfl fun l hl => ?_
        rw [hH' l hl, (ihc l hl).1, smul_smul, smul_smul]
        congr 1
        calc star (d l) * d i.castSucc * H l i.castSucc * d l
            = d i.castSucc * H l i.castSucc * (star (d l) * d l) := by ring
          _ = d i.castSucc * H l i.castSucc := by rw [(ihc l hl).2, mul_one]
      have hrec : H' i.succ i.castSucc • Q'.col i.succ =
          (d i.castSucc * H i.succ i.castSucc) • Q.col i.succ := by
        rw [h'.smul_col_succ, hsum, hqc, mulVec_smul, ← smul_sub, ← h.smul_col_succ, smul_smul]
      have hc0 : d i.castSucc * H i.succ i.castSucc ≠ 0 := by
        refine mul_ne_zero (fun h0 => ?_) (hH.apply_succ_castSucc_ne_zero i)
        rw [h0, mul_zero] at hdc
        exact zero_ne_one hdc
      -- dot the recurrence with `q_{i+1}`
      have hdot : H' i.succ i.castSucc * d i.succ = d i.castSucc * H i.succ i.castSucc := by
        have := congrArg (star (Q.col i.succ) ⬝ᵥ ·) hrec
        simp only [dotProduct_smul, smul_eq_mul, h.star_col_dotProduct_col, one_apply_eq,
          mul_one] at this
        exact this
      have hH'0 : H' i.succ i.castSucc ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hdot
        exact hc0 hdot.symm
      have hq : Q'.col i.succ = d i.succ • Q.col i.succ := by
        rw [← hdot, ← smul_smul] at hrec
        exact smul_right_injective _ hH'0 hrec
      refine ⟨hq, ?_⟩
      have := h'.star_col_dotProduct_col i.succ i.succ
      rw [hq, star_smul, smul_dotProduct, dotProduct_smul, h.star_col_dotProduct_col,
        one_apply_eq, smul_eq_mul, smul_eq_mul, mul_one] at this
      exact this
  have hcol : ∀ l, Q'.col l = d l • Q.col l := fun l => (key l l le_rfl).1
  have hunit : ∀ l, star (d l) * d l = 1 := fun l => (key l l le_rfl).2
  have hQ' : Q' = Q * diagonal d := by
    ext x l
    rw [mul_diagonal]
    have := congrFun (hcol l) x
    simpa [mul_comm] using this
  have hH' : H' = star (diagonal d) * H * diagonal d := by
    rw [← h'.conjTranspose_mul_mul, ← h.conjTranspose_mul_mul, hQ', conjTranspose_mul,
      star_eq_conjTranspose]
    simp only [Matrix.mul_assoc]
  refine ⟨d, fun l => CStarRing.norm_of_mem_unitary (Unitary.mem_iff_star_mul_self.2 (hunit l)),
    hd0, hQ', hH', ?_⟩
  -- the residuals
  have hDD : diagonal d * star (diagonal d) = 1 := by
    rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext l
    rw [Pi.star_apply, mul_comm]
    exact hunit l
  have hr : vecMulVec r' (Pi.single (Fin.last k) 1) =
      vecMulVec r (Pi.single (Fin.last k) 1) * diagonal d := by
    rw [eq_sub_of_add_eq' h'.mul_eq.symm, eq_sub_of_add_eq' h.mul_eq.symm, hQ', hH',
      Matrix.sub_mul]
    congr 1
    · rw [Matrix.mul_assoc]
    · simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc Q (diagonal d) (star (diagonal d)), hDD, Matrix.mul_one]
  rw [vecMulVec_mul, single_vecMul_diagonal, one_mul] at hr
  ext x
  have := congrFun (congrFun hr x) (Fin.last k)
  simpa [vecMulVec_apply, mul_comm] using this

/-- Let $A Q = Q H + r e_k^T$ be an Arnoldi decomposition with $k + 1$ columns. Then, for every
$i \le k$,
$$A^i q_0 = Q H^i e_0.$$

The residual term does not reach $H^i e_0$, because $H^i e_0$ is supported on the first $i + 1$
coordinates. -/
theorem pow_mulVec_first [DecidableEq n] (h : IsArnoldiDecomposition A Q H r) {i : ℕ}
    (hi : i ≤ k) : A ^ i *ᵥ (Q *ᵥ Pi.single 0 1) = Q *ᵥ (H ^ i *ᵥ Pi.single 0 1) := by
  induction i with
  | zero => rw [pow_zero, pow_zero, one_mulVec, one_mulVec]
  | succ i ih =>
    have hlast : (H ^ i *ᵥ Pi.single 0 1) (Fin.last k) = 0 :=
      h.isUpperHessenberg.pow_mulVec_single_zero_apply_of_lt (by simp only [Fin.val_last]; omega)
    calc A ^ (i + 1) *ᵥ (Q *ᵥ Pi.single 0 1) = A *ᵥ (A ^ i *ᵥ (Q *ᵥ Pi.single 0 1)) := by
          rw [pow_succ', ← mulVec_mulVec]
      _ = A *ᵥ (Q *ᵥ (H ^ i *ᵥ Pi.single 0 1)) := by rw [ih (by omega)]
      _ = (A * Q) *ᵥ (H ^ i *ᵥ Pi.single 0 1) := mulVec_mulVec _ _ _
      _ = Q *ᵥ (H *ᵥ (H ^ i *ᵥ Pi.single 0 1)) := by
          rw [h.mul_eq, add_mulVec, vecMulVec_mulVec, single_one_dotProduct, hlast,
            MulOpposite.op_zero, zero_smul, add_zero]
          exact (mulVec_mulVec _ Q H).symm
      _ = Q *ᵥ (H ^ (i + 1) *ᵥ Pi.single 0 1) := by rw [pow_succ', ← mulVec_mulVec]

/-- **Polynomial filtering of the first column.** Let $A Q = Q H + r e_k^T$ be an Arnoldi
decomposition with $k + 1$ columns, and let $p$ be a polynomial over $\mathbb{K}$ of degree at
most $k$. Then
$$p(A)\, Q e_0 = Q\, p(H) e_0.$$

This is the identity of §10.5.3 of [golub2013matrix]:
"$(A - \mu I) Q_c e_1 = Q_c (H_c - \mu I) e_1$ … and so $q_+ = p(A) q_1$". The source indexes
from $1$. -/
theorem aeval_mulVec_first [DecidableEq n] (h : IsArnoldiDecomposition A Q H r)
    {p : Polynomial 𝕜} (hp : p.natDegree ≤ k) :
    Polynomial.aeval A p *ᵥ (Q *ᵥ Pi.single 0 1) =
      Q *ᵥ (Polynomial.aeval H p *ᵥ Pi.single 0 1) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, sum_mulVec, sum_mulVec,
    mulVec_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [smul_mulVec, smul_mulVec, mulVec_smul,
    h.pow_mulVec_first (by have := mem_range.1 hi; omega)]

end IsArnoldiDecomposition

end Arnoldi

/-! ### The square implicit Q theorems -/

section Square

variable {N : ℕ} {A Q V : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜}

/-- The **implicit Q theorem**, unreduced case. Let $A, Q, V \in \mathbb{K}^{(N+1) \times (N+1)}$,
and let $Q$ and $V$ be unitary with the same first column, $V e_0 = Q e_0$. Suppose that
$H = Q^H A Q$ is unreduced upper Hessenberg and that $G = V^H A V$ is upper Hessenberg. Then
there is $d \in \mathbb{K}^{N+1}$ with $|d_i| = 1$ for all $i$ and $d_0 = 1$ such that, with
$D = \operatorname{diag}(d)$,
$$V = Q D, \qquad G = D^H H D.$$

This is Theorem 7.4.2 of [golub2013matrix] and the remark after it, which says that $G$ and $H$
are "essentially equal". The proof specializes `Matrix.IsArnoldiDecomposition.implicitQ` to the
two reductions, which are Arnoldi decompositions with zero residual. -/
theorem implicitQ (hQ : Q ∈ unitaryGroup (Fin (N + 1)) 𝕜) (hV : V ∈ unitaryGroup (Fin (N + 1)) 𝕜)
    (hH : (star Q * A * Q).IsUnreducedUpperHessenberg) (hG : (star V * A * V).IsUpperHessenberg)
    (h0 : V.col 0 = Q.col 0) :
    ∃ d : Fin (N + 1) → 𝕜, (∀ i, ‖d i‖ = 1) ∧ d 0 = 1 ∧ V = Q * diagonal d ∧
      star V * A * V = star (diagonal d) * (star Q * A * Q) * diagonal d := by
  obtain ⟨d, hd1, hd0, hVQ, hGH, -⟩ :=
    (isArnoldiDecomposition_of_mem_unitaryGroup hQ hH.1).implicitQ
      (isArnoldiDecomposition_of_mem_unitaryGroup hV hG) hH
      (by rw [mulVec_single_one, mulVec_single_one, h0])
  exact ⟨d, hd1, hd0, hVQ, hGH⟩

/-- **Theorem 7.4.2** of [golub2013matrix] (**implicit Q theorem**). Let
$A, Q, V \in \mathbb{K}^{(N+1) \times (N+1)}$, and let $Q$ and $V$ be unitary with the same
first column, $V e_0 = Q e_0$. Suppose that $H = Q^H A Q$ and $G = V^H A V$ are upper
Hessenberg. Let $k \le N$, and suppose that $h_{i+1,i} \neq 0$ for all $i < k$. Then:

(a) for every $i \le k$, there is $c \in \mathbb{K}$ with $|c| = 1$ and $v_i = c q_i$;

(b) $|g_{i+1,i}| = |h_{i+1,i}|$ for every $i < k$;

(c) if $k < N$ and $h_{k+1,k} = 0$, then $g_{k+1,k} = 0$.

The source takes $k$ to be the first index with $h_{k+1,k} = 0$, and indexes from $1$. Here $k$
is any index up to which the subdiagonal of $H$ is nonzero, and the vanishing of $h_{k+1,k}$ is
the hypothesis of (c). The proof applies `Matrix.IsKrylovDecomposition.leading` to the two
reductions. Their leading $k + 1$ columns are Arnoldi decompositions with the residuals
$h_{k+1,k} q_{k+1}$ and $g_{k+1,k} v_{k+1}$, and `Matrix.IsArnoldiDecomposition.implicitQ`
compares them. -/
theorem implicitQ_of_apply_eq_zero (hQ : Q ∈ unitaryGroup (Fin (N + 1)) 𝕜)
    (hV : V ∈ unitaryGroup (Fin (N + 1)) 𝕜) (hH : (star Q * A * Q).IsUpperHessenberg)
    (hG : (star V * A * V).IsUpperHessenberg) (h0 : V.col 0 = Q.col 0) {k : ℕ} (hk : k ≤ N)
    (hsub : ∀ i : Fin N, (i : ℕ) < k → (star Q * A * Q) i.succ i.castSucc ≠ 0) :
    (∀ i : Fin (N + 1), (i : ℕ) ≤ k → ∃ c : 𝕜, ‖c‖ = 1 ∧ V.col i = c • Q.col i) ∧
      (∀ i : Fin N, (i : ℕ) < k →
        ‖(star V * A * V) i.succ i.castSucc‖ = ‖(star Q * A * Q) i.succ i.castSucc‖) ∧
      (∀ i : Fin N, (i : ℕ) = k → (star Q * A * Q) i.succ i.castSucc = 0 →
        (star V * A * V) i.succ i.castSucc = 0) := by
  set j : Fin (N + 1) := ⟨k, by omega⟩ with hj
  have hKQ := isKrylovDecomposition_of_mem_unitaryGroup hQ A 0
  have hKV := isKrylovDecomposition_of_mem_unitaryGroup hV A 0
  have hAQ := hKQ.isArnoldiDecomposition_leading hH j fun _ _ => rfl
  have hAV := hKV.isArnoldiDecomposition_leading hG j fun _ _ => rfl
  have hunred : ((star Q * A * Q).submatrix (Fin.castLE j.isLt)
      (Fin.castLE j.isLt)).IsUnreducedUpperHessenberg := by
    refine isUnreducedUpperHessenberg_iff_succ.2 ⟨hAQ.isUpperHessenberg, fun i => ?_⟩
    have hik : (i : ℕ) < k := i.isLt
    have h1 : Fin.castLE j.isLt i.succ = (⟨i, by omega⟩ : Fin N).succ := Fin.ext (by simp)
    have h2 : Fin.castLE j.isLt i.castSucc = (⟨i, by omega⟩ : Fin N).castSucc :=
      Fin.ext (by simp)
    rw [submatrix_apply, h1, h2]
    exact hsub _ hik
  have hfirst : V.submatrix id (Fin.castLE j.isLt) *ᵥ Pi.single 0 1 =
      Q.submatrix id (Fin.castLE j.isLt) *ᵥ Pi.single 0 1 := by
    rw [mulVec_single_one, mulVec_single_one]
    ext x
    have := congrFun h0 x
    simpa using this
  obtain ⟨d, hd1, -, hVQ, hGH, hr⟩ := hAQ.implicitQ hAV hunred hfirst
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi hz => ?_⟩
  · -- (a)
    refine ⟨d ⟨i, by simp [hj]; omega⟩, hd1 _, ?_⟩
    ext x
    have := congrFun (congrFun hVQ x) ⟨i, by simp [hj]; omega⟩
    rw [mul_diagonal] at this
    simpa [mul_comm] using this
  · -- (b)
    set a : Fin j := ⟨i, by simpa [hj] using hi⟩
    have := congrFun (congrFun hGH a.succ) a.castSucc
    rw [star_diagonal_mul_mul_diagonal_apply] at this
    have h1 : Fin.castLE j.isLt a.succ = i.succ := Fin.ext (by simp [a])
    have h2 : Fin.castLE j.isLt a.castSucc = i.castSucc := Fin.ext (by simp [a])
    simp only [submatrix_apply, h1, h2] at this
    rw [this, norm_mul, norm_mul, norm_star, hd1, hd1, one_mul, mul_one]
  · -- (c)
    have hjc : j = i.castSucc := Fin.ext (by simp [hj, hi])
    have hrQ : ∑ l ∈ Ioi j, (star Q * A * Q) l j • Q.col l +
        (0 : Fin (N + 1) → 𝕜) j • (0 : Fin (N + 1) → 𝕜) = 0 := by
      rw [smul_zero, add_zero]
      refine sum_eq_zero fun l hl => ?_
      rcases eq_or_ne l i.succ with rfl | hne
      · rw [hjc, hz, zero_smul]
      · have hl' := mem_Ioi.1 hl
        have hsl : i.succ < l := by
          rw [Fin.lt_def] at hl' ⊢
          have : (l : ℕ) ≠ i + 1 := fun h' => hne (Fin.ext (by simpa using h'))
          simp only [hj] at hl'
          simp only [Fin.val_succ]
          omega
        rw [hH l j ⟨i.succ, by rw [hjc]; exact Fin.castSucc_lt_succ, hsl⟩, zero_smul]
    rw [hrQ, smul_zero] at hr
    have hdot := congrArg (star (V.col i.succ) ⬝ᵥ ·) hr
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, hKV.star_col_dotProduct_col,
      hKV.star_col_dotProduct_residual, mul_zero, add_zero, Matrix.one_apply] at hdot
    rw [sum_eq_single_of_mem i.succ (mem_Ioi.2 (by rw [hjc]; exact Fin.castSucc_lt_succ))
      (fun l _ hne => by rw [ite_eq_right_iff.2 fun h' => absurd h'.symm hne, mul_zero]),
      hjc] at hdot
    simpa using hdot

variable {A Q V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}

/-- The implicit Q theorem for real orthogonal matrices, unreduced case. Let
$A, Q, V \in \mathbb{R}^{(N+1) \times (N+1)}$, and let $Q$ and $V$ be orthogonal with the same
first column, $V e_0 = Q e_0$. Suppose that $Q^T A Q$ is unreduced upper Hessenberg and that
$V^T A V$ is upper Hessenberg. Then there is $d \in \mathbb{R}^{N+1}$ with $d_i = \pm 1$ for all
$i$ and $d_0 = 1$ such that, with $D = \operatorname{diag}(d)$,
$$V = Q D, \qquad V^T A V = D (Q^T A Q) D.$$
-/
theorem implicitQ_real (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hV : V ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hH : (Qᵀ * A * Q).IsUnreducedUpperHessenberg)
    (hG : (Vᵀ * A * V).IsUpperHessenberg) (h0 : V.col 0 = Q.col 0) :
    ∃ d : Fin (N + 1) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧ d 0 = 1 ∧ V = Q * diagonal d ∧
      Vᵀ * A * V = diagonal d * (Qᵀ * A * Q) * diagonal d := by
  rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose] at hH hG
  obtain ⟨d, hd1, hd0, hVQ, hGH⟩ := implicitQ hQ hV hH hG h0
  refine ⟨d, fun i => ?_, hd0, hVQ, ?_⟩
  · have := hd1 i
    rwa [Real.norm_eq_abs, abs_eq zero_le_one] at this
  · simp only [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose, hGH]
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, diagonal_transpose]

/-- **Theorem 7.4.2** of [golub2013matrix], for real orthogonal matrices. Let
$A, Q, V \in \mathbb{R}^{(N+1) \times (N+1)}$, and let $Q$ and $V$ be orthogonal with the same
first column, $V e_0 = Q e_0$. Suppose that $H = Q^T A Q$ and $G = V^T A V$ are upper
Hessenberg. Let $k \le N$, and suppose that $h_{i+1,i} \neq 0$ for all $i < k$. Then:

(a) $v_i = q_i$ or $v_i = -q_i$ for every $i \le k$;

(b) $|g_{i+1,i}| = |h_{i+1,i}|$ for every $i < k$;

(c) if $k < N$ and $h_{k+1,k} = 0$, then $g_{k+1,k} = 0$.

Theorem 8.3.2 of [golub2013matrix] is the instance of this theorem for symmetric tridiagonal
matrices. The source indexes from $1$. -/
theorem implicitQ_of_apply_eq_zero_real (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hV : V ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hH : (Qᵀ * A * Q).IsUpperHessenberg)
    (hG : (Vᵀ * A * V).IsUpperHessenberg) (h0 : V.col 0 = Q.col 0) {k : ℕ} (hk : k ≤ N)
    (hsub : ∀ i : Fin N, (i : ℕ) < k → (Qᵀ * A * Q) i.succ i.castSucc ≠ 0) :
    (∀ i : Fin (N + 1), (i : ℕ) ≤ k → V.col i = Q.col i ∨ V.col i = -Q.col i) ∧
      (∀ i : Fin N, (i : ℕ) < k →
        |(Vᵀ * A * V) i.succ i.castSucc| = |(Qᵀ * A * Q) i.succ i.castSucc|) ∧
      (∀ i : Fin N, (i : ℕ) = k → (Qᵀ * A * Q) i.succ i.castSucc = 0 →
        (Vᵀ * A * V) i.succ i.castSucc = 0) := by
  simp only [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose] at hH hG hsub ⊢
  obtain ⟨ha, hb, hc⟩ := implicitQ_of_apply_eq_zero hQ hV hH hG h0 hk hsub
  refine ⟨fun i hi => ?_, fun i hi => ?_, hc⟩
  · obtain ⟨c, hc1, hVc⟩ := ha i hi
    rw [Real.norm_eq_abs, abs_eq zero_le_one] at hc1
    rcases hc1 with rfl | rfl
    · exact Or.inl (by rw [hVc, one_smul])
    · exact Or.inr (by rw [hVc, neg_one_smul])
  · have := hb i hi
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this

end Square

end Matrix
