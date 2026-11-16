/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Data.Fin.Sum
import Numlib.FloatingPoint.LU
import NumlibSurface.GolubVanLoan.Chapter03.Section01

/-!
# Golub and Van Loan, Section 3.2: The LU factorization

This module formalizes §3.2 of [golub2013matrix], Gaussian elimination as the factorization $A = LU$
of $A \in \mathbb{R}^{n \times n}$, with $L$ unit lower triangular and $U$ upper triangular. A Gauss
transformation is a matrix $M_k = I_n - \tau e_k^T$ whose Gauss vector $\tau$ vanishes in its first
$k$ components. Gaussian elimination applies the Gauss transformations $M_1, \dots, M_{n-1}$ that
zero the subdiagonal columns one after the other, so that $M_{n-1} \cdots M_1 A = U$ and
$L = M_1^{-1} \cdots M_{n-1}^{-1}$ ((3.2.3)–(3.2.7)). Theorem 3.2.1 says that the factorization
exists if the leading principal submatrices $A(1{:}k, 1{:}k)$ are nonsingular for
$k = 1, \dots, n-1$, that it is then unique, and that $\det A = u_{11} \cdots u_{nn}$.

The module defines the outer product LU (Algorithm 3.2.1) and the gaxpy LU (Algorithm 3.2.2) as
programs, with rounding bridges into the relation `FloatingPoint.RoundsLU` of
`Numlib.FloatingPoint.LU` and exact specifications. It also treats the rounding of one Gauss
transformation (§3.2.3), the rectangular LU factorization and its outer product algorithm (§3.2.10,
(3.2.8)), the block factorization through the Schur complement (3.2.9), and the recursive and
nonrecursive block LU Algorithms 3.2.3 and 3.2.4. The exact statements specialize the backbone
modules `Numlib.LinearAlgebra.Matrix.LU` and `Numlib.LinearAlgebra.Matrix.LU.Elimination`.

## Main definitions

* §3.2.1, `GolubVanLoan.Chapter03.gaussVector`: the Gauss vector $\tau$ of $v$ at $k$, with
  $\tau_i = v_i / v_k$ below $k$.
* (3.2.2), `GolubVanLoan.Chapter03.gaussTransformation`: the matrix $M_k = I_n - \tau e_k^T$.
* §3.2.1, `GolubVanLoan.Chapter03.IsGaussTransformation`: $M = I_n - \tau e_k^T$ with
  $\tau_1 = \dots = \tau_k = 0$.
* §3.2.2, `GolubVanLoan.Chapter03.gaussUpdate`: the computed Gauss vector and the computed product
  $M_k C$.
* (3.2.3), `GolubVanLoan.Chapter03.gaussStage`: the matrices $A^{(k)}$ of Gaussian elimination.
* §3.2.4, `GolubVanLoan.Chapter03.pivot`: the pivots $a_{kk}^{(k)}$.
* §3.2.8, `GolubVanLoan.Chapter03.packedL` and `GolubVanLoan.Chapter03.packedU`: the factors $L$ and
  $U$ stored in one packed matrix.
* Algorithm 3.2.1, `GolubVanLoan.Chapter03.algorithm_3_2_1`: outer product LU.
* Algorithm 3.2.2, `GolubVanLoan.Chapter03.algorithm_3_2_2`: gaxpy LU, with its column computation
  `GolubVanLoan.Chapter03.gaxpyColumn`.
* (3.2.8), `GolubVanLoan.Chapter03.tallOuterProductLU`: outer product LU of a tall matrix, with the
  factors `GolubVanLoan.Chapter03.tallPackedL` and `GolubVanLoan.Chapter03.tallPackedU`.
* Algorithm 3.2.3, `GolubVanLoan.Chapter03.algorithm_3_2_3`: recursive block LU.
* Algorithm 3.2.4, `GolubVanLoan.Chapter03.algorithm_3_2_4`: nonrecursive block LU.

## Main results

* (3.2.1), `GolubVanLoan.Chapter03.equation_3_2_1`: if $A = LU$, $Ly = b$ and $Ux = y$, then
  $Ax = b$.
* §3.2.1, `GolubVanLoan.Chapter03.gaussTransformation_gaussVector_mulVec` and
  `GolubVanLoan.Chapter03.isUnitLowerTriangular_gaussTransformation`: the Gauss transformation of
  $v$ zeroes $v$ below $k$, and every Gauss transformation is unit lower triangular.
* §3.2.2, `GolubVanLoan.Chapter03.gaussTransformation_mul`: $M_k C = C - \tau C(k, :)$ is an outer
  product update.
* §3.2.3, `GolubVanLoan.Chapter03.gaussVector_rounding` and
  `GolubVanLoan.Chapter03.gaussUpdate_rounding`: the computed Gauss vector has relative error at
  most $u$, and the computed $M_k C$ is $M_k C + E$ with $|E| \le u|C| + \gamma_3 |\tau| |C(k,:)|$.
* (3.2.3), `GolubVanLoan.Chapter03.equation_3_2_3`: $A^{(k+1)} = M_k A^{(k)}$.
* (3.2.4)–(3.2.5), `GolubVanLoan.Chapter03.equation_3_2_4`: with nonzero pivots, the last stage is
  upper triangular and $A = LU$ with $L$ the matrix of multipliers.
* (3.2.5), `GolubVanLoan.Chapter03.equation_3_2_5`: $M_1^{-1} \cdots M_{n-1}^{-1}$ is the matrix of
  multipliers.
* §3.2.5, `GolubVanLoan.Chapter03.gaussTransformation_inv`:
  $(I_n - \tau e_k^T)^{-1} = I_n + \tau e_k^T$.
* Theorem 3.2.1, `GolubVanLoan.Chapter03.theorem_3_2_1`,
  `GolubVanLoan.Chapter03.theorem_3_2_1_unique` and `GolubVanLoan.Chapter03.theorem_3_2_1_det`:
  existence, uniqueness and the determinant of the LU factorization.
* (3.2.6), `GolubVanLoan.Chapter03.equation_3_2_6`: the leading principal minors are products of
  pivots.
* (3.2.7), `GolubVanLoan.Chapter03.equation_3_2_7`: column $k$ of $L$ holds the multipliers of step
  $k$.
* §3.2.7, `GolubVanLoan.Chapter03.outerProduct_decomposition`: the first step of elimination as a
  block decomposition.
* Algorithm 3.2.1, `GolubVanLoan.Chapter03.algorithm_3_2_1_rounds` and
  `GolubVanLoan.Chapter03.algorithm_3_2_1_spec`: every run computes an LU factorization in the sense
  of `FloatingPoint.RoundsLU`, and the exact run computes $A = LU$.
* Algorithm 3.2.2, `GolubVanLoan.Chapter03.algorithm_3_2_2_rounds` and
  `GolubVanLoan.Chapter03.algorithm_3_2_2_spec`: the same for the gaxpy LU.
* §3.2.10, `GolubVanLoan.Chapter03.rectangularLU_exists`: existence of the rectangular LU
  factorization.
* (3.2.8), `GolubVanLoan.Chapter03.equation_3_2_8`: the exact outer product LU of a tall matrix
  computes its rectangular LU factorization.
* (3.2.9), `GolubVanLoan.Chapter03.equation_3_2_9`: the block factorization through the Schur
  complement $A_{22} - A_{21} A_{11}^{-1} A_{12}$.
* §3.2.11, `GolubVanLoan.Chapter03.blockLU_of_schur`: an LU factorization of the Schur complement
  gives an LU factorization of $A$.
* Algorithm 3.2.3, `GolubVanLoan.Chapter03.algorithm_3_2_3_spec`: the exact recursive block LU
  computes $A = LU$.
* Algorithm 3.2.4, `GolubVanLoan.Chapter03.algorithm_3_2_4_spec`: the exact nonrecursive block LU
  computes $A = LU$.

## Conventions

* Indices are 0-based. The source's step $k = 1{:}n-1$ is `k : Fin n`, with an empty last step. Its
  $A^{(k)}$, the matrix after $k - 1$ steps in (3.2.3), is `gaussStage A (k - 1)`, which is
  `Matrix.gemStage A (k - 1)`. Its hypothesis "$A(1{:}k, 1{:}k)$ is nonsingular for $k = 1{:}n-1$"
  is `∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0`, where the block of order $0$ is
  empty.
* The source's first-order bound $|E| \le 3u(|C| + |\tau| |C(k,:)|) + O(u^2)$ of §3.2.3 is stated in
  the rigorous form $|E| \le u|C| + \gamma_3 |\tau| |C(k,:)|$, which implies it because
  $\gamma_3 = 3u + O(u^2)$.
* In Algorithms 3.2.2–3.2.4 the unit lower triangular solves do not divide by the unit diagonal, and
  the level-3 updates $B - LX$ are computed entrywise as running differences
  (`FloatingPoint.runningDiff`).

## Implementation notes

* The Gauss transformation built from column $k$ of a matrix is the backbone's
  `Matrix.gaussTransform`
  (`GolubVanLoan.Chapter03.gaussTransformation_gaussVector_eq_gaussTransform`). Through this
  identity, (3.2.3)–(3.2.7) are the backbone's statements about `Matrix.gemStage` and
  `Matrix.gemLower`.
* Algorithm 3.2.1 is a program in the algorithm conventions of `NumlibSurface.GolubVanLoan`. It
  overwrites the matrix entry by entry, by `Matrix.updateRow A i (Function.update (A i) j a)`, and
  its packed output $F$ is read by `packedL F = 1 + F.strictLower` and
  `packedU F = F - F.strictLower`. Its bridge `GolubVanLoan.Chapter03.algorithm_3_2_1_rounds` puts
  every run in the rounding model into `FloatingPoint.RoundsLU`, and the exact specification is read
  off the bridge at the exact model (`FloatingPoint.roundsLU_exact_iff`).
* The loops write one matrix entry per step and read only entries outside the positions that the
  loop writes. `SetM.mem_run_foldlM_updateRow_update_of_nodup` gives the run set of such a loop
  entry by entry.
* The bridge of Algorithm 3.2.2 uses the invariant `GolubVanLoan.Chapter03.GaxpyInv` and the column
  step `GolubVanLoan.Chapter03.gaxpyInv_succ`, which Algorithm 3.4.2 shares.
* The exact correctness of (3.2.8) is proved by a simulation of Algorithm 3.2.1 on the bordered
  square matrix $[A \mid [0; I]]$. The exact correctness of Algorithm 3.2.3 is proved by strong
  induction on $n$ through `GolubVanLoan.Chapter03.blockLU_of_schur`. Algorithm 3.2.4 takes its
  blocks by `Fin.divNat`, and its exact correctness is proved with the invariant that the entries
  with $\min(i, j) < kr$ hold the finished factors and the other entries hold Schur complement
  values.

## Deviations from the source

* **§3.2.5, the inverse of a Gauss transformation** (generalization). The source states
  $M_k^{-1} = I_n + \tau e_k^T$ for a Gauss transformation. The theorem needs only $\tau_k = 0$. See
  `GolubVanLoan.Chapter03.gaussTransformation_inv`.
* **Algorithm 3.2.3** (correction). The source assumes that $A$ has an LU factorization. This does
  not exclude a zero pivot, for example $A = \begin{bmatrix} 0 & 1 \\ 0 & 1 \end{bmatrix}$, and the
  algorithm then fails. The specification assumes that $A(1{:}k, 1{:}k)$ is nonsingular for
  $k = 1, \dots, n-1$. See `GolubVanLoan.Chapter03.algorithm_3_2_3_spec`.
* **Algorithm 3.2.4** (correction). The same hypothesis replaces "$A$ has an LU factorization". See
  `GolubVanLoan.Chapter03.algorithm_3_2_4_spec`.

## Not formalized

* **Operation counts and level-3 fractions.** Operation counts are out of scope for the library.
* **The Problems of §3.2.** Problems are out of scope for the library.
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter03

/-! ### Gauss transformations (§3.2.1–3.2.2) -/

section Gauss

variable {n : ℕ}

/-- **Equation (3.2.1)** of [golub2013matrix]. Let $A, L, U \in \mathbb{R}^{n \times n}$ with
$A = LU$, and let $b, y, x \in \mathbb{R}^n$ with $Ly = b$ and $Ux = y$. Then $Ax = b$.

The source says that the solution of $Ax = b$ is then found by a two-step triangular solve
process. -/
theorem equation_3_2_1 {A L U : Matrix (Fin n) (Fin n) ℝ} (hA : A = L * U) {b y x : Fin n → ℝ}
    (hy : L *ᵥ y = b) (hx : U *ᵥ x = y) : A *ᵥ x = b := by
  rw [hA, ← mulVec_mulVec, hx, hy]

/-- **Section 3.2.1** of [golub2013matrix], the Gauss vector. For $v \in \mathbb{R}^n$ and an index
$k$, the **Gauss vector** $\tau \in \mathbb{R}^n$ of $v$ at $k$ has
$$\tau_i = v_i / v_k \quad (i > k), \qquad \tau_i = 0 \quad (i \le k).$$

Indices are 0-based. If $v_k = 0$, then $\tau = 0$, by the convention $x / 0 = 0$. -/
noncomputable def gaussVector (v : Fin n → ℝ) (k : Fin n) : Fin n → ℝ :=
  fun i => if k < i then v i / v k else 0

/-- **Equation (3.2.2)** of [golub2013matrix]. For $\tau \in \mathbb{R}^n$ and an index $k$, the
matrix
$$M_k = I_n - \tau e_k^T.$$

The outer product $\tau e_k^T$ is `vecMulVec τ (Pi.single k 1)`. The definition has no condition
on $\tau$; `GolubVanLoan.Chapter03.IsGaussTransformation` adds it. -/
noncomputable def gaussTransformation (τ : Fin n → ℝ) (k : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  1 - vecMulVec τ (Pi.single k 1)

/-- **Section 3.2.1** of [golub2013matrix], definition of a Gauss transformation. A matrix
$M \in \mathbb{R}^{n \times n}$ is a **Gauss transformation** at $k$ if $M = I_n - \tau e_k^T$
for some $\tau \in \mathbb{R}^n$ whose first $k$ components are zero. The components of $\tau$
below $k$ are the **multipliers**, and $\tau$ is the **Gauss vector**.

Indices are 0-based, so the condition is $\tau_i = 0$ for $i \le k$. -/
def IsGaussTransformation (M : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Prop :=
  ∃ τ : Fin n → ℝ, (∀ i, i ≤ k → τ i = 0) ∧ M = gaussTransformation τ k

/-- The entry $(i, j)$ of $M_k = I_n - \tau e_k^T$ is $\delta_{ij} - \tau_i$ if $j = k$, and
$\delta_{ij}$ otherwise. -/
theorem gaussTransformation_apply (τ : Fin n → ℝ) (k i j : Fin n) :
    gaussTransformation τ k i j =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j - if j = k then τ i else 0 := by
  simp [gaussTransformation, vecMulVec_apply, Pi.single_apply]

/-- **Section 3.2.2** of [golub2013matrix]. Let $\tau \in \mathbb{R}^n$, let $k$ be an index and let
$C \in \mathbb{R}^{n \times r}$. Then
$$M_k C = (I_n - \tau e_k^T) C = C - \tau C(k, :)$$
is an outer product update. If moreover $\tau_i = 0$ for $i \le k$, then the rows $i \le k$ of
$M_k C$ are those of $C$. -/
theorem gaussTransformation_mul {r : ℕ} (τ : Fin n → ℝ) (k : Fin n)
    (C : Matrix (Fin n) (Fin r) ℝ) :
    gaussTransformation τ k * C = C - vecMulVec τ (C k) ∧
      ((∀ i, i ≤ k → τ i = 0) → ∀ i, i ≤ k → (gaussTransformation τ k * C) i = C i) := by
  have h : gaussTransformation τ k * C = C - vecMulVec τ (C k) := by
    ext i j
    simp [gaussTransformation, Matrix.mul_apply, vecMulVec_apply, Pi.single_apply, sub_mul,
      Finset.sum_sub_distrib, Matrix.one_apply, ite_mul]
  refine ⟨h, fun hτ i hi => ?_⟩
  rw [h]
  ext j
  simp [vecMulVec_apply, hτ i hi]

/-- A Gauss transformation applied to a vector: $(I_n - \tau e_k^T) v = v - v_k \tau$ for
$v \in \mathbb{R}^n$. -/
theorem gaussTransformation_mulVec (τ : Fin n → ℝ) (k : Fin n) (v : Fin n → ℝ) :
    gaussTransformation τ k *ᵥ v = fun i => v i - τ i * v k := by
  ext i
  simp [gaussTransformation, mulVec, dotProduct, vecMulVec_apply, Pi.single_apply, sub_mul,
    Finset.sum_sub_distrib, Matrix.one_apply, ite_mul]

/-- **Section 3.2.1** of [golub2013matrix], the display after (3.2.2). Let $v \in \mathbb{R}^n$ with
$v_k \neq 0$, and let $\tau$ be the Gauss vector of $v$ at $k$. Then $M_k = I_n - \tau e_k^T$
zeroes the components of $v$ below $k$ and keeps the others:
$$(M_k v)_i = v_i \quad (i \le k), \qquad (M_k v)_i = 0 \quad (i > k).$$
-/
theorem gaussTransformation_gaussVector_mulVec {v : Fin n → ℝ} {k : Fin n} (hv : v k ≠ 0) :
    gaussTransformation (gaussVector v k) k *ᵥ v = fun i => if i ≤ k then v i else 0 := by
  ext i
  rw [gaussTransformation_mulVec]
  by_cases hik : i ≤ k
  · simp [gaussVector, not_lt.2 hik, hik]
  · have hki : k < i := not_le.1 hik
    simp [gaussVector, hki, hik, div_mul_cancel₀ _ hv]

/-- **Section 3.2.1** of [golub2013matrix]. Every Gauss transformation
$M \in \mathbb{R}^{n \times n}$ is unit lower triangular. -/
theorem isUnitLowerTriangular_gaussTransformation {M : Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hM : IsGaussTransformation M k) : M.IsUnitLowerTriangular := by
  obtain ⟨τ, hτ, rfl⟩ := hM
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [gaussTransformation_apply, one_apply_ne hij'.ne]
    split_ifs with hjk
    · rw [hτ i (hjk ▸ hij'.le), sub_zero]
    · rw [sub_zero]
  · rw [gaussTransformation_apply, one_apply_eq]
    split_ifs with hik
    · rw [hτ i hik.le, sub_zero]
    · rw [sub_zero]

/-- **Section 3.2.5** of [golub2013matrix], the inverse of a Gauss transformation. Let
$\tau \in \mathbb{R}^n$ with $\tau_k = 0$. Then
$$(I_n - \tau e_k^T)(I_n + \tau e_k^T) = I_n, \qquad (I_n - \tau e_k^T)^{-1} = I_n + \tau
  e_k^T.$$

**Generalization.** The source states the inverse for a Gauss transformation, whose first $k$
components of $\tau$ vanish. The proof needs only $\tau_k = 0$, because then
$(\tau e_k^T)^2 = \tau (e_k^T \tau) e_k^T = 0$.

The matrix $I_n + \tau e_k^T$ is written as `gaussTransformation (-τ) k`. -/
theorem gaussTransformation_inv {τ : Fin n → ℝ} {k : Fin n} (hτ : τ k = 0) :
    gaussTransformation τ k * gaussTransformation (-τ) k = 1 ∧
      (gaussTransformation τ k)⁻¹ = gaussTransformation (-τ) k := by
  have h : gaussTransformation τ k * gaussTransformation (-τ) k = 1 := by
    rw [(gaussTransformation_mul τ k _).1]
    ext i j
    by_cases hij : i = j <;> by_cases hjk : j = k <;>
      simp [gaussTransformation, vecMulVec_apply, Matrix.one_apply, hτ, hij, hjk, eq_comm (a := k)]
  exact ⟨h, inv_eq_right_inv h⟩

/-- The Gauss transformation built from column $k$ of $M \in \mathbb{R}^{n \times n}$, that is
$I_n - \tau e_k^T$ with $\tau$ the Gauss vector of $M(:, k)$ at $k$, is the backbone's Gaussian
transformation `Matrix.gaussTransform M k`.

The backbone matrix performs one elimination step: its product with $M$ is `Matrix.elimStep M k`
(`Matrix.gaussTransform_mul`). Through this identity, (3.2.3)–(3.2.7) are statements of the
backbone. -/
theorem gaussTransformation_gaussVector_eq_gaussTransform (M : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) :
    gaussTransformation (gaussVector (fun i => M i k) k) k = gaussTransform M k := by
  ext i j
  simp only [gaussTransformation_apply, gaussTransform, elimMultipliers, Matrix.sub_apply,
    of_apply, gaussVector]
  by_cases hj : j = k
  · subst hj
    by_cases hi : j < i <;> simp [hi, div_eq_mul_inv]
  · simp [hj]

end Gauss

/-! ### Rounding a Gauss transformation (§3.2.3) -/

section GaussUpdate

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Section 3.2.2** of [golub2013matrix], the application of a computed Gauss transformation. Let
$v \in \mathbb{R}^n$, an index $k$ and $C \in \mathbb{R}^{n \times r}$ be given. The program
computes the Gauss vector $\hat\tau_i = \mathrm{fl}(v_i / v_k)$ for $i > k$, with
$\hat\tau_i = 0$ for $i \le k$, and then updates $C$ row by row,
```
for i = k+1:n
    C(i,:) = C(i,:) - τ_i · C(k,:)
end
```
entrywise as $c_{ij} \leftarrow \mathrm{fl}(c_{ij} - \mathrm{fl}(\hat\tau_i c_{kj}))$. It
returns the pair $(\hat\tau, \mathrm{fl}((I_n - \hat\tau e_k^T) C))$. -/
noncomputable def gaussUpdate {n r : ℕ} (v : Fin n → ℝ) (k : Fin n)
    (C : Matrix (Fin n) (Fin r) ℝ) : M ((Fin n → ℝ) × Matrix (Fin n) (Fin r) ℝ) := do
  let τ ← ((List.finRange n).filter (k < ·)).foldlM (fun (τ : Fin n → ℝ) i => do
    let t ← rnd (v i / v k)
    pure (Function.update τ i t)) 0
  let C ← ((List.finRange n).filter (k < ·)).foldlM (fun (C : Matrix (Fin n) (Fin r) ℝ) i =>
    (List.finRange r).foldlM (fun (C : Matrix (Fin n) (Fin r) ℝ) j => do
      let p ← rnd (τ i * C k j)
      let c ← rnd (C i j - p)
      pure (C.updateRow i (Function.update (C i) j c))) C) C
  pure (τ, C)

variable {fp : RoundingModel ℝ} {n r : ℕ}

/-- The run set of `GolubVanLoan.Chapter03.gaussUpdate`, entry by entry. Every output
$(\hat\tau, \hat C)$ in the rounding model `fp` has $\hat\tau_i = 0$ for $i \le k$ and
$\hat\tau_i$ a rounding of $v_i / v_k$ for $i > k$; the rows $i \le k$ of $\hat C$ are those of
$C$, and for $i > k$ each $\hat c_{ij}$ is a rounding of $c_{ij} - p$ for some rounding $p$ of
$\hat\tau_i c_{kj}$. -/
theorem mem_run_gaussUpdate {v : Fin n → ℝ} {k : Fin n} {C : Matrix (Fin n) (Fin r) ℝ}
    {out : (Fin n → ℝ) × Matrix (Fin n) (Fin r) ℝ} (h : out ∈ (gaussUpdate fp.round v k C).run) :
    (∀ i, ¬ k < i → out.1 i = 0) ∧ (∀ i, k < i → fp.Rounds (v i / v k) (out.1 i)) ∧
      (∀ i j, ¬ k < i → out.2 i j = C i j) ∧
      ∀ i j, k < i → ∃ p, fp.Rounds (out.1 i * C k j) p ∧ fp.Rounds (C i j - p) (out.2 i j) := by
  simp only [gaussUpdate, SetM.mem_run_bind, SetM.mem_run_pure] at h
  obtain ⟨τ, hτ, C', hC', rfl⟩ := h
  dsimp only
  have hnd : ((List.finRange n).filter (k < ·)).Nodup := (List.nodup_finRange n).filter _
  have hmem : ∀ i, i ∈ (List.finRange n).filter (k < ·) ↔ k < i := fun i => by simp
  obtain ⟨hτ₁, hτ₂⟩ := (SetM.mem_run_foldlM_update_of_nodup
    (fun a _ (_ : Fin n → ℝ) => fp.round (v a / v k)) _ hnd (fun _ _ _ _ _ _ => rfl) 0 τ).1 hτ
  have hflat := List.foldlM_foldlM_eq_foldlM_flatMap ((List.finRange n).filter (k < ·))
    (fun _ => List.finRange r) (fun (C : Matrix (Fin n) (Fin r) ℝ) i j => (do
      let p ← fp.round (τ i * C k j)
      let c ← fp.round (C i j - p)
      pure (C.updateRow i (Function.update (C i) j c)) : SetM _)) C
  beta_reduce at hflat
  rw [hflat] at hC'
  have hl : ((((List.finRange n).filter (k < ·)).flatMap fun a =>
      (List.finRange r).map (a, ·))).Nodup :=
    List.nodup_flatMap.2 ⟨fun a _ => (List.nodup_finRange r).map fun _ _ h => (Prod.mk.inj h).2,
      hnd.imp fun {a b} hab => List.disjoint_left.2 fun {x} hxa hxb => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.1 hxa
        obtain ⟨_, _, h⟩ := List.mem_map.1 hxb
        exact hab (Prod.mk.inj h).1.symm⟩
  have hlmem : ∀ i j, (i, j) ∈ (((List.finRange n).filter (k < ·)).flatMap fun a =>
      (List.finRange r).map (a, ·)) ↔ k < i := fun i j => by simp
  have key := SetM.mem_run_foldlM_updateRow_update_of_nodup _ hl
    (fun a x (C : Matrix (Fin n) (Fin r) ℝ) => fp.round (τ a.1 * C k a.2) >>= fun p =>
      fp.round (x - p))
    (fun a _ x A A' hA => by
      rw [hA k a.2 fun h => lt_irrefl k ((hlmem k a.2).1 h)]) C C'
  simp only [bind_assoc] at key
  obtain ⟨hC₁, hC₂⟩ := key.1 hC'
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hi => ?_, fun i j hi => ?_⟩
  · rw [hτ₁ i fun h => hi ((hmem i).1 h)]
    rfl
  · exact hτ₂ i ((hmem i).2 hi)
  · exact hC₁ i j fun h => hi ((hlmem i j).1 h)
  · obtain ⟨p, hp, hc⟩ := SetM.mem_run_bind.1 (hC₂ (i, j) ((hlmem i j).2 hi))
    exact ⟨p, hp, hc⟩

/-- **Section 3.2.3** of [golub2013matrix], the computed Gauss vector. Let $v \in \mathbb{R}^n$, an
index $k$ and $C \in \mathbb{R}^{n \times r}$ be given, and let $\tau$ be the exact Gauss vector
of $v$ at $k$. For every output of `GolubVanLoan.Chapter03.gaussUpdate` in the rounding model
`fp`, the computed Gauss vector $\hat\tau$ satisfies, for every $i$,
$$|\hat\tau_i - \tau_i| \le u |\tau_i|.$$

The source writes this as $\hat\tau = \tau + e$ with $|e| \le u|\tau|$. Each component is one
rounded division, so the bound has no $O(u^2)$ term. -/
theorem gaussVector_rounding (v : Fin n → ℝ) (k : Fin n) (C : Matrix (Fin n) (Fin r) ℝ) :
    ∀ out ∈ (gaussUpdate fp.round v k C).run,
      ∀ i, |out.1 i - gaussVector v k i| ≤ fp.u * |gaussVector v k i| := by
  intro out hout i
  obtain ⟨h₁, h₂, -, -⟩ := mem_run_gaussUpdate hout
  by_cases hi : k < i
  · simp only [gaussVector, hi, ↓reduceIte]
    exact fp.abs_sub_le (h₂ i hi)
  · simp [gaussVector, hi, h₁ i hi]

/-- For three relative errors $|\delta_0|, |\delta_1|, |\delta_2| \le u$ with $u \ge 0$ and
$3u < 1$, $|(1 + \delta_0)(1 + \delta_1)(1 + \delta_2) - 1| \le \gamma_3$. -/
private theorem abs_three_mul_sub_one_le {u δ₀ δ₁ δ₂ : ℝ} (hu : 0 ≤ u) (h3 : 3 * u < 1)
    (h₀ : |δ₀| ≤ u) (h₁ : |δ₁| ≤ u) (h₂ : |δ₂| ≤ u) :
    |(1 + δ₀) * (1 + δ₁) * (1 + δ₂) - 1| ≤ gamma u 3 := by
  have h := abs_prod_one_add_sub_one_le_gamma (n := 3) hu (by norm_num; linarith)
    (δ := ![δ₀, δ₁, δ₂]) (fun i => by fin_cases i <;> simpa) (ρ := fun _ => 1)
    (fun _ => Or.inl rfl)
  simpa [Fin.prod_univ_three] using h

/-- **Section 3.2.3** of [golub2013matrix], the rounding of a Gauss transformation update. Let
$v \in \mathbb{R}^n$, an index $k$ and $C \in \mathbb{R}^{n \times r}$ be given, let $\tau$ be
the exact Gauss vector of $v$ at $k$, and let the unit roundoff $u$ satisfy $3u < 1$. For every
output $(\hat\tau, \hat C)$ of `GolubVanLoan.Chapter03.gaussUpdate` in the rounding model `fp`,
there is $E \in \mathbb{R}^{n \times r}$ with
$$\hat C = (I_n - \tau e_k^T) C + E, \qquad |e_{ij}| \le u |c_{ij}| + \gamma_3 |\tau_i|
  |c_{kj}|,$$
and $e_{ij} = 0$ for $i \le k$.

The source prints $|E| \le 3u(|C| + |\tau| |C(k,:)|) + O(u^2)$, which follows because $u \le 3u$
and $\gamma_3 = 3u + O(u^2)$. For $i > k$ the entry is $\hat c_{ij} = (c_{ij} - \tau_i (1 +
\delta_0) c_{kj} (1 + \delta_1))(1 + \delta_2)$, so $e_{ij} = \delta_2 c_{ij} - \tau_i c_{kj}
((1 + \delta_0)(1 + \delta_1)(1 + \delta_2) - 1)$. -/
theorem gaussUpdate_rounding (h3 : 3 * fp.u < 1) (v : Fin n → ℝ) (k : Fin n)
    (C : Matrix (Fin n) (Fin r) ℝ) :
    ∀ out ∈ (gaussUpdate fp.round v k C).run, ∃ E : Matrix (Fin n) (Fin r) ℝ,
      out.2 = gaussTransformation (gaussVector v k) k * C + E ∧
      (∀ i j, |E i j| ≤ fp.u * |C i j| + gamma fp.u 3 * (|gaussVector v k i| * |C k j|)) ∧
      ∀ i j, i ≤ k → E i j = 0 := by
  intro out hout
  obtain ⟨-, h₂, h₃, h₄⟩ := mem_run_gaussUpdate hout
  have hmul := (gaussTransformation_mul (gaussVector v k) k C).1
  have hτk : ∀ i, ¬ k < i → gaussVector v k i = 0 := fun i hi => by simp [gaussVector, hi]
  refine ⟨out.2 - gaussTransformation (gaussVector v k) k * C, by abel, fun i j => ?_,
    fun i j hi => ?_⟩
  · rw [hmul, Matrix.sub_apply, Matrix.sub_apply, vecMulVec_apply]
    by_cases hi : k < i
    · obtain ⟨p, hp, hc⟩ := h₄ i j hi
      obtain ⟨δ₀, hδ₀, ht⟩ := (h₂ i hi).exists_delta
      obtain ⟨δ₁, hδ₁, hp'⟩ := hp.exists_delta
      obtain ⟨δ₂, hδ₂, hc'⟩ := hc.exists_delta
      have hγ := abs_three_mul_sub_one_le fp.u_nonneg h3 hδ₀ hδ₁ hδ₂
      have hτi : gaussVector v k i = v i / v k := by simp [gaussVector, hi]
      have heq : out.2 i j - (C i j - gaussVector v k i * C k j) =
          C i j * δ₂ - gaussVector v k i * C k j * ((1 + δ₀) * (1 + δ₁) * (1 + δ₂) - 1) := by
        rw [hc', hp', ht, hτi]
        ring
      rw [heq]
      calc |C i j * δ₂ - gaussVector v k i * C k j * ((1 + δ₀) * (1 + δ₁) * (1 + δ₂) - 1)|
          ≤ |C i j * δ₂| + |gaussVector v k i * C k j *
              ((1 + δ₀) * (1 + δ₁) * (1 + δ₂) - 1)| := abs_sub _ _
        _ ≤ fp.u * |C i j| + gamma fp.u 3 * (|gaussVector v k i| * |C k j|) := by
            have e1 : |C i j| * |δ₂| ≤ fp.u * |C i j| := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right hδ₂ (abs_nonneg _)
            have e2 : |gaussVector v k i| * |C k j| * |(1 + δ₀) * (1 + δ₁) * (1 + δ₂) - 1| ≤
                gamma fp.u 3 * (|gaussVector v k i| * |C k j|) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right hγ (by positivity)
            rw [abs_mul, abs_mul, abs_mul]
            exact add_le_add e1 e2
    · rw [h₃ i j hi, hτk i hi]
      have : 0 ≤ fp.u * |C i j| + gamma fp.u 3 * (|(0 : ℝ)| * |C k j|) := by
        rw [abs_zero, zero_mul, mul_zero, add_zero]
        exact mul_nonneg fp.u_nonneg (abs_nonneg _)
      simpa using this
  · rw [Matrix.sub_apply, h₃ i j (not_lt.2 hi), (gaussTransformation_mul (gaussVector v k) k C).2
      (fun i hi => hτk i (not_lt.2 hi)) i hi, sub_self]

end GaussUpdate

/-! ### Gaussian elimination as a factorization (§3.2.4–3.2.6) -/

section Elimination

variable {n : ℕ}

/-- **Equation (3.2.3)** of [golub2013matrix], the matrices of Gaussian elimination. For
$A \in \mathbb{R}^{n \times n}$ and $k \in \mathbb{N}$, `gaussStage A k` is the matrix after $k$
steps of Gaussian elimination, which is `Matrix.gemStage A k`.

The source's $A^{(k+1)} = M_k A^{(k)}$, with $A^{(1)} = A$, is 1-based, so its $A^{(k+1)}$ is
`gaussStage A k`. Beyond $n$ steps the stage does not change. -/
noncomputable abbrev gaussStage (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  gemStage A k

/-- **Equation (3.2.3)** of [golub2013matrix], one step of Gaussian elimination. For
$A \in \mathbb{R}^{n \times n}$ and every index $k$, let $\tau^{(k)}$ be the Gauss vector of
column $k$ of $A^{(k)}$ at $k$, so that $\tau_i^{(k)} = a_{ik}^{(k)} / a_{kk}^{(k)}$ for
$i > k$, and let $M_k = I_n - \tau^{(k)} e_k^T$. Then
$$A^{(k+1)} = M_k A^{(k)}.$$

Here $A^{(k)}$ is the stage after $k$ steps (0-based). The statement has no pivot hypothesis: at
a zero pivot the multipliers are $0$ by the convention $x / 0 = 0$, and both sides equal
$A^{(k)}$. -/
theorem equation_3_2_3 (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    gaussStage A (k + 1) =
      gaussTransformation (gaussVector (fun i => gaussStage A k i k) k) k * gaussStage A k := by
  rw [gaussTransformation_gaussVector_eq_gaussTransform]
  exact gemStage_succ_eq_gaussTransform_mul A k.2

/-- **Section 3.2.4** of [golub2013matrix], the pivots. The **pivot** of step $k$ of Gaussian
elimination on $A \in \mathbb{R}^{n \times n}$ is $a_{kk}^{(k)}$, the diagonal entry $(k, k)$ of
the stage after $k$ steps (0-based). -/
noncomputable def pivot (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  gaussStage A k k k

/-- The pivots of the steps $k$ with $k + 1 < n$ are nonzero if and only if, for every $m$ with
$m + 1 < n$, the entry $(m, m)$ of `Matrix.gemStage A m` is nonzero; this is the pivot
hypothesis in the form of the backbone. -/
theorem pivot_ne_zero_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ k : Fin n, (k : ℕ) + 1 < n → pivot A k ≠ 0) ↔
      ∀ (m : ℕ) (hm : m < n), m + 1 < n → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0 :=
  ⟨fun h m hm hmn => h ⟨m, hm⟩ hmn, fun h k hk => h k k.2 hk⟩

/-- **Equations (3.2.4)–(3.2.5)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$, and
assume that no zero pivots are encountered in (3.2.3), that is, the pivots of the steps
$1, \dots, n-1$ are nonzero. Then the last stage $U = A^{(n)}$, which is $M_{n-1} \cdots M_1 A$
by (3.2.3), is upper triangular, and
$$A = LU$$
with $L = M_1^{-1} \cdots M_{n-1}^{-1}$ the unit lower triangular matrix of multipliers.

The matrix $L$ is the backbone's `Matrix.gemLower A`, and $U$ is `gaussStage A n`. The last
pivot divides nothing and may vanish. -/
theorem equation_3_2_4 {A : Matrix (Fin n) (Fin n) ℝ}
    (hpiv : ∀ k : Fin n, (k : ℕ) + 1 < n → pivot A k ≠ 0) :
    IsLU A (gemLower A) (gaussStage A n) :=
  isLU_gemLower_gemStage A ((pivot_ne_zero_iff A).1 hpiv)

/-- The inverse of the Gauss transformation built from column $k$ of $M \in \mathbb{R}^{n \times n}$
is the backbone's unipotent factor `Matrix.elimMul M k`. -/
theorem inv_gaussTransformation_gaussVector (M : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    (gaussTransformation (gaussVector (fun i => M i k) k) k)⁻¹ = elimMul M k := by
  rw [gaussTransformation_gaussVector_eq_gaussTransform]
  exact inv_eq_left_inv (elimMul_mul_gaussTransform M k)

/-- **Equation (3.2.5)** of [golub2013matrix], with §3.2.6. Let $A \in \mathbb{R}^{n \times n}$, and
let $M_k$ be the Gauss transformation of step $k$ of (3.2.3). Then
$$M_1^{-1} \cdots M_{n-1}^{-1} = I_n + \sum_k \tau^{(k)} e_k^T,$$
the matrix of multipliers `Matrix.gemLower A`.

The product is the ordered product over all $n$ steps; the last factor is the identity. The
statement has no pivot hypothesis. -/
theorem equation_3_2_5 (A : Matrix (Fin n) (Fin n) ℝ) :
    ((List.finRange n).map fun k : Fin n =>
      (gaussTransformation (gaussVector (fun i => gaussStage A k i k) k) k)⁻¹).prod =
      gemLower A := by
  let F : ℕ → Matrix (Fin n) (Fin n) ℝ := fun k =>
    if h : k < n then elimMul (gemStage A k) ⟨k, h⟩ else 1
  have hmap : ((List.finRange n).map fun k : Fin n =>
      (gaussTransformation (gaussVector (fun i => gaussStage A k i k) k) k)⁻¹) =
      (List.range n).map F := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply, F, k.2, ↓reduceDIte]
    exact inv_gaussTransformation_gaussVector _ k
  have key : ∀ k ≤ n, ((List.range k).map F).prod = gemLowerStage A k := by
    intro k hk
    induction k with
    | zero => simp [gemLowerStage_zero]
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih (by omega), List.map_singleton,
        List.prod_singleton, gemLowerStage_succ A (by omega)]
      simp only [F, show k < n by omega, ↓reduceDIte]
  rw [hmap, key n le_rfl, gemLowerStage_of_le A le_rfl]

/-- **Theorem 3.2.1** of [golub2013matrix] (LU factorization), existence. Let
$A \in \mathbb{R}^{n \times n}$ with $\det(A(1{:}k, 1{:}k)) \neq 0$ for $k = 1, \dots, n-1$.
Then there exist a unit lower triangular $L \in \mathbb{R}^{n \times n}$ and an upper triangular
$U \in \mathbb{R}^{n \times n}$ with $A = LU$.

The hypothesis is on `A.strictLeadingPrincipalSubmatrix k` for `k : Fin n`, which has order $k$
(0-based); the block of order $0$ is empty. The conclusion is `Matrix.IsLU A L U`. -/
theorem theorem_3_2_1 {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) :
    ∃ L U, IsLU A L U :=
  exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix fun k =>
    (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))

/-- **Theorem 3.2.1** of [golub2013matrix], uniqueness. Let $A \in \mathbb{R}^{n \times n}$ with
$\det(A(1{:}k, 1{:}k)) \neq 0$ for $k = 1, \dots, n-1$, and let $A$ be nonsingular. If
$A = L_1 U_1$ and $A = L_2 U_2$ are two LU factorizations, then $L_1 = L_2$ and $U_1 = U_2$.

The hypothesis on the leading submatrices alone suffices (`Matrix.IsLU.unique`); the
nonsingularity of $A$ is kept because the source states it. -/
theorem theorem_3_2_1_unique {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) (_hdet : A.det ≠ 0)
    {L₁ U₁ L₂ U₂ : Matrix (Fin n) (Fin n) ℝ} (h₁ : IsLU A L₁ U₁) (h₂ : IsLU A L₂ U₂) :
    L₁ = L₂ ∧ U₁ = U₂ :=
  h₁.unique h₂ fun k => (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))

/-- **Theorem 3.2.1** of [golub2013matrix], determinant. If $A = LU$ with
$L \in \mathbb{R}^{n \times n}$ unit lower triangular and $U \in \mathbb{R}^{n \times n}$ upper
triangular, then
$$\det A = u_{11} \cdots u_{nn}.$$
-/
theorem theorem_3_2_1_det {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U) :
    A.det = ∏ i, U i i :=
  h.det_eq_prod_diag

/-- **Equation (3.2.6)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and let $k$ be an
index such that the pivots of the steps before $k$ are nonzero. Then the leading principal minor
of order $k + 1$ is the product of the leading diagonal entries of the stage after $k$ steps:
$$\det(A(1{:}k{+}1, 1{:}k{+}1)) = \prod_{i \le k} a_{ii}^{(k)}.$$

The indices are 0-based. Since row $i$ does not change after step $i$, these diagonal entries
are the pivots of the steps $0, \dots, k$. -/
theorem equation_3_2_6 {A : Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hpiv : ∀ m : Fin n, m < k → pivot A m ≠ 0) :
    (A.leadingPrincipalSubmatrix k).det = ∏ i : {i // i ≤ k}, gaussStage A k i i := by
  have h := isLU_leadingPrincipalSubmatrix_gemStage A k.2
    fun m hm hmk _ => hpiv ⟨m, hm⟩ (Fin.lt_def.2 hmk)
  simp only [Fin.eta] at h
  convert h.det_eq_prod_diag using 2
  all_goals rfl

/-- **Equation (3.2.7)** of [golub2013matrix]. The $k$-th column of $L$ is defined by the
multipliers that arise in the $k$-th step of (3.2.3): for $A \in \mathbb{R}^{n \times n}$ and
indices $k < i$,
$$\ell_{ik} = \tau_i^{(k)},$$
where $L$ is the matrix of multipliers `Matrix.gemLower A` and $\tau^{(k)}$ is the Gauss vector
of column $k$ of $A^{(k)}$ at $k$. -/
theorem equation_3_2_7 (A : Matrix (Fin n) (Fin n) ℝ) {i k : Fin n} (hki : k < i) :
    gemLower A i k = gaussVector (fun i => gaussStage A k i k) k i := by
  simp [gemLower, gaussVector, hki]

end Elimination

/-! ### The packed factors -/

section Packed

variable {n : ℕ}

/-- **Section 3.2.8** of [golub2013matrix], the packed lower factor. For
$F \in \mathbb{R}^{n \times n}$, `packedL F` is $I_n$ plus the strictly lower triangular part of
$F$: the unit lower triangular matrix $L$ with $\ell_{ij} = f_{ij}$ for $i > j$.

The source says that $A(i{+}1{:}n, i)$ is overwritten by $L(i{+}1{:}n, i)$. -/
def packedL (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := 1 + F.strictLower

/-- **Section 3.2.8** of [golub2013matrix], the packed upper factor. For
$F \in \mathbb{R}^{n \times n}$, `packedU F` is $F$ minus its strictly lower triangular part:
the upper triangular matrix $U$ with $u_{ij} = f_{ij}$ for $i \le j$.

The source says that $A(i, i{:}n)$ is overwritten by $U(i, i{:}n)$. -/
def packedU (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := F - F.strictLower

variable (F : Matrix (Fin n) (Fin n) ℝ)

/-- Below the diagonal, the packed lower factor has the entries of the packed matrix:
$\ell_{ij} = f_{ij}$ for $j < i$. -/
theorem packedL_apply_of_lt {i j : Fin n} (h : j < i) : packedL F i j = F i j := by
  simp [packedL, h, h.ne']

/-- The packed lower factor has unit diagonal. -/
theorem packedL_apply_self (i : Fin n) : packedL F i i = 1 := by
  simp [packedL]

/-- The packed lower factor vanishes above the diagonal: $\ell_{ij} = 0$ for $i < j$. -/
theorem packedL_apply_of_lt' {i j : Fin n} (h : i < j) : packedL F i j = 0 := by
  simp [packedL, h.ne, not_lt.2 h.le]

/-- On and above the diagonal, the packed upper factor has the entries of the packed matrix:
$u_{ij} = f_{ij}$ for $i \le j$. -/
theorem packedU_apply_of_le {i j : Fin n} (h : i ≤ j) : packedU F i j = F i j := by
  simp [packedU, not_lt.2 h]

/-- The packed upper factor vanishes below the diagonal: $u_{ij} = 0$ for $j < i$. -/
theorem packedU_apply_of_lt {i j : Fin n} (h : j < i) : packedU F i j = 0 := by
  simp [packedU, h]

end Packed

/-! ### Algorithm 3.2.1 (Outer Product LU) -/

section Algorithm321

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One step $k$ of the outer product LU on $A \in \mathbb{R}^{n \times n}$. With
$\rho = \{k+1, \dots, n\}$, the program computes
$a_{ik} \leftarrow \mathrm{fl}(a_{ik} / a_{kk})$ for $i \in \rho$, and then the outer product
update $A(\rho, \rho) = A(\rho, \rho) - A(\rho, k) A(k, \rho)$ row by row, as $a_{ij} \leftarrow
\mathrm{fl}(a_{ij} - \mathrm{fl}(a_{ik} a_{kj}))$.

This is the body of the loop of Algorithm 3.2.1, and the pivoting Algorithms 3.4.1 and 3.4.3
share it. -/
noncomputable def outerProductStep {n : ℕ} (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) := do
  let A ← ((List.finRange n).filter (k < ·)).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) i => do
    let l ← rnd (A i k / A k k)
    pure (A.updateRow i (Function.update (A i) k l))) A
  ((List.finRange n).filter (k < ·)).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) i =>
    ((List.finRange n).filter (k < ·)).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) j => do
      let p ← rnd (A i k * A k j)
      let a ← rnd (A i j - p)
      pure (A.updateRow i (Function.update (A i) j a))) A) A

/-- **Algorithm 3.2.1** of [golub2013matrix] (outer product LU). Suppose that
$A \in \mathbb{R}^{n \times n}$ has the property that $A(1{:}k, 1{:}k)$ is nonsingular for
$k = 1{:}n-1$. The algorithm computes the factorization $A = LU$, where $L$ is unit lower
triangular and $U$ is upper triangular. For $i = 1{:}n-1$, $A(i, i{:}n)$ is overwritten by
$U(i, i{:}n)$ while $A(i{+}1{:}n, i)$ is overwritten by $L(i{+}1{:}n, i)$.
```
for k = 1:n-1
    ρ = k+1:n
    A(ρ,k) = A(ρ,k)/A(k,k)
    A(ρ,ρ) = A(ρ,ρ) - A(ρ,k)·A(k,ρ)
end
```
The program runs the step `GolubVanLoan.Chapter03.outerProductStep` for $k = 1, \dots, n$; the
last step is empty.

The outer product update is carried out row by row, the $kij$ form of §3.2.9, and every
quotient, product and difference is rounded. The program has no hypothesis on $A$. The factors
are read from the output by `GolubVanLoan.Chapter03.packedL` and
`GolubVanLoan.Chapter03.packedU`. -/
noncomputable def algorithm_3_2_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun A k => outerProductStep rnd k A) A

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- The run set of one step $k$ of the outer product LU. For every output $S'$ of
`GolubVanLoan.Chapter03.outerProductStep` on $S$ in the rounding model `fp`: every entry
$(i, j)$ outside the rows $i > k$ and the columns $j \ge k$ is unchanged; for $i > k$, $s'_{ik}$
is a rounding of $s_{ik} / s_{kk}$; and for $i > k$ and $j > k$, $s'_{ij}$ is a rounding of
$s_{ij} - p$ for some rounding $p$ of $s'_{ik} s'_{kj}$. -/
theorem mem_run_outerProductStep (k : Fin n) {S S' : Matrix (Fin n) (Fin n) ℝ}
    (h : S' ∈ (outerProductStep fp.round k S).run) :
    (∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → S' i j = S i j) ∧
      (∀ i, k < i → fp.Rounds (S i k / S k k) (S' i k)) ∧
      ∀ i j, k < i → k < j →
        ∃ p, fp.Rounds (S' i k * S' k j) p ∧ fp.Rounds (S i j - p) (S' i j) := by
  rw [outerProductStep, SetM.mem_run_bind] at h
  obtain ⟨S₁, h₁, h₂⟩ := h
  have hnd : ((List.finRange n).filter (k < ·)).Nodup := (List.nodup_finRange n).filter _
  have hmem : ∀ i, i ∈ (List.finRange n).filter (k < ·) ↔ k < i := fun i => by simp
  -- the division loop
  have hdiv : ((List.finRange n).filter (k < ·)).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) i => do
        let l ← fp.round (A i k / A k k)
        pure (A.updateRow i (Function.update (A i) k l))) S =
      (((List.finRange n).filter (k < ·)).map (·, k)).foldlM
        (fun (A : Matrix (Fin n) (Fin n) ℝ) a => do
          let x ← (fun (_ : Fin n × Fin n) x (A : Matrix (Fin n) (Fin n) ℝ) =>
            fp.round (x / A k k)) a (A a.1 a.2) A
          pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) S := by
    rw [List.foldlM_map]
  have hl₁ : (((List.finRange n).filter (k < ·)).map (·, k)).Nodup :=
    hnd.map fun _ _ h => (Prod.mk.inj h).1
  have hl₁mem : ∀ i j, (i, j) ∈ ((List.finRange n).filter (k < ·)).map (·, k) ↔
      k < i ∧ j = k := fun i j => by
    simp only [List.mem_map, hmem, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨ha, rfl⟩
    · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl, rfl⟩
  rw [hdiv] at h₁
  obtain ⟨hS₁, hS₁'⟩ := (SetM.mem_run_foldlM_updateRow_update_of_nodup _ hl₁
    (fun _ x (A : Matrix (Fin n) (Fin n) ℝ) => fp.round (x / A k k))
    (fun a _ x A A' hA => by
      rw [hA k k fun h => lt_irrefl k ((hl₁mem k k).1 h).1]) S S₁).1 h₁
  -- the update loop
  have hflat := List.foldlM_foldlM_eq_foldlM_flatMap ((List.finRange n).filter (k < ·))
    (fun _ => (List.finRange n).filter (k < ·)) (fun (A : Matrix (Fin n) (Fin n) ℝ) i j => (do
      let p ← fp.round (A i k * A k j)
      let a ← fp.round (A i j - p)
      pure (A.updateRow i (Function.update (A i) j a)) : SetM _)) S₁
  beta_reduce at hflat
  rw [hflat] at h₂
  have hl₂ : ((((List.finRange n).filter (k < ·)).flatMap fun a =>
      ((List.finRange n).filter (k < ·)).map (a, ·))).Nodup :=
    List.nodup_flatMap.2 ⟨fun a _ => hnd.map fun _ _ h => (Prod.mk.inj h).2,
      hnd.imp fun {a b} hab => List.disjoint_left.2 fun {x} hxa hxb => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.1 hxa
        obtain ⟨_, _, h⟩ := List.mem_map.1 hxb
        exact hab (Prod.mk.inj h).1.symm⟩
  have hl₂mem : ∀ i j, (i, j) ∈ (((List.finRange n).filter (k < ·)).flatMap fun a =>
      ((List.finRange n).filter (k < ·)).map (a, ·)) ↔ k < i ∧ k < j := fun i j => by
    simp only [List.mem_flatMap, List.mem_map, hmem, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, b, hb, rfl, rfl⟩; exact ⟨ha, hb⟩
    · rintro ⟨hi, hj⟩; exact ⟨i, hi, j, hj, rfl, rfl⟩
  have key := SetM.mem_run_foldlM_updateRow_update_of_nodup _ hl₂
    (fun a x (A : Matrix (Fin n) (Fin n) ℝ) => fp.round (A a.1 k * A k a.2) >>= fun p =>
      fp.round (x - p))
    (fun a _ x A A' hA => by
      rw [hA a.1 k fun h => lt_irrefl k ((hl₂mem a.1 k).1 h).2,
        hA k a.2 fun h => lt_irrefl k ((hl₂mem k a.2).1 h).1]) S₁ S'
  simp only [bind_assoc] at key
  obtain ⟨hS', hS''⟩ := key.1 h₂
  have hS'k : ∀ i, S' i k = S₁ i k := fun i => hS' i k fun h => lt_irrefl k ((hl₂mem i k).1 h).2
  have hS'r : ∀ j, S' k j = S₁ k j := fun j => hS' k j fun h => lt_irrefl k ((hl₂mem k j).1 h).1
  refine ⟨fun i j hij => ?_, fun i hi => ?_, fun i j hi hj => ?_⟩
  · rw [hS' i j fun h => hij ⟨((hl₂mem i j).1 h).1, Or.inr ((hl₂mem i j).1 h).2⟩,
      hS₁ i j fun h => hij ⟨((hl₁mem i j).1 h).1, Or.inl ((hl₁mem i j).1 h).2⟩]
  · rw [hS'k]
    exact hS₁' (i, k) ((hl₁mem i k).2 ⟨hi, rfl⟩)
  · obtain ⟨p, hp, hc⟩ := SetM.mem_run_bind.1 (hS'' (i, j) ((hl₂mem i j).2 ⟨hi, hj⟩))
    refine ⟨p, by rw [hS'k, hS'r]; exact hp, ?_⟩
    rw [← hS₁ i j fun h => hj.ne' ((hl₁mem i j).1 h).2]
    exact hc

/-- Entry $(i, j)$, $i \le j$, of a packed matrix $S$ is a finished upper entry for $A$ if $s_{ij}$
is obtained from $a_{ij}$ by subtracting roundings of the products $s_{ir} s_{rj}$, $r < i$, one
after the other in some order, with one rounding per subtraction. -/
def LUUpperEntry (fp : RoundingModel ℝ) (A S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ∃ (o : List (Fin n)) (p : Fin n → ℝ), o.Nodup ∧ (∀ r, r ∈ o ↔ r < i) ∧
    (∀ r ∈ o, fp.Rounds (S i r * S r j) (p r)) ∧
    RoundsSumFrom fp (A i j) (o.map fun r => -p r) (S i j)

/-- Entry $(i, j)$, $j < i$, of a packed matrix $S$ is a finished lower entry for $A$ if $s_{ij}$ is
a rounding of $t / s_{jj}$, where $t$ is obtained from $a_{ij}$ by subtracting roundings of the
products $s_{ir} s_{rj}$, $r < j$, one after the other in some order, with one rounding per
subtraction. -/
def LULowerEntry (fp : RoundingModel ℝ) (A S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ∃ (o : List (Fin n)) (p : Fin n → ℝ) (t : ℝ), o.Nodup ∧ (∀ r, r ∈ o ↔ r < j) ∧
    (∀ r ∈ o, fp.Rounds (S i r * S r j) (p r)) ∧
    RoundsSumFrom fp (A i j) (o.map fun r => -p r) t ∧ fp.Rounds (t / S j j) (S i j)

/-- Entry $(i, j)$ of a packed matrix $S$ is a trailing entry after $k$ steps for $A$ if $s_{ij}$ is
obtained from $a_{ij}$ by subtracting roundings of the products $s_{ir} s_{rj}$, $r < k$, one
after the other in some order, with one rounding per subtraction. -/
def LUTrailingEntry (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ∃ (o : List (Fin n)) (p : Fin n → ℝ), o.Nodup ∧ (∀ r : Fin n, r ∈ o ↔ (r : ℕ) < k) ∧
    (∀ r ∈ o, fp.Rounds (S i r * S r j) (p r)) ∧
    RoundsSumFrom fp (A i j) (o.map fun r => -p r) (S i j)

/-- The invariant of Algorithm 3.2.1 after $k$ steps: the entries $(i, j)$ with $i < k$ and
$i \le j$ are finished upper entries, the entries with $j < k$ and $j < i$ are finished lower
entries, and the entries with $i, j \ge k$ are trailing entries after $k$ steps. -/
def LUStageInv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, ((i : ℕ) < k → i ≤ j → LUUpperEntry fp A S i j) ∧
    ((j : ℕ) < k → j < i → LULowerEntry fp A S i j) ∧
    (k ≤ (i : ℕ) → k ≤ (j : ℕ) → LUTrailingEntry fp A k S i j)

/-- One step of Algorithm 3.2.1 keeps the invariant. If $S$ satisfies the invariant after $k$ steps
and $S'$ is related to $S$ as in `GolubVanLoan.Chapter03.mem_run_outerProductStep`, then $S'$
satisfies the invariant after $k + 1$ steps. -/
theorem luStageInv_step (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n)
    {S S' : Matrix (Fin n) (Fin n) ℝ} (hS : LUStageInv fp A k S)
    (hunch : ∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → S' i j = S i j)
    (hdiv : ∀ i, k < i → fp.Rounds (S i k / S k k) (S' i k))
    (hupd : ∀ i j, k < i → k < j →
      ∃ p, fp.Rounds (S' i k * S' k j) p ∧ fp.Rounds (S i j - p) (S' i j)) :
    LUStageInv fp A (k + 1) S' := by
  -- entries in the rows up to `k`, and in the columns before `k`, are unchanged
  have hrow : ∀ i j : Fin n, (i : ℕ) ≤ k → S' i j = S i j := fun i j hi =>
    hunch i j fun h => absurd (Fin.lt_def.1 h.1) (not_lt.2 hi)
  have hcol : ∀ i j : Fin n, (j : ℕ) < k → S' i j = S i j := fun i j hj =>
    hunch i j fun h => h.2.elim (fun h' => absurd (h' ▸ hj) (lt_irrefl _))
      fun h' => absurd (Fin.lt_def.1 h') (not_lt.2 hj.le)
  intro i j
  refine ⟨fun hi hij => ?_, fun hj hji => ?_, fun hi hj => ?_⟩
  · -- a finished entry of `U`
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).1 hi hij
      refine ⟨o, p, hnd, ho, fun r hr => ?_, ?_⟩
      · have hri := Fin.lt_def.1 ((ho r).1 hr)
        rw [hrow i r (by omega), hrow r j (by omega)]
        exact hp r hr
      · rw [hrow i j (by omega)]
        exact hsum
    · have hik : i = k := Fin.ext hi
      subst hik
      obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).2.2 le_rfl (Fin.le_def.1 hij)
      refine ⟨o, p, hnd, fun r => (ho r).trans Fin.lt_def.symm, fun r hr => ?_, ?_⟩
      · have hri := (ho r).1 hr
        rw [hrow i r le_rfl, hrow r j (by omega)]
        exact hp r hr
      · rw [hrow i j le_rfl]
        exact hsum
  · -- a finished entry of `L`
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · obtain ⟨o, p, t, hnd, ho, hp, hsum, hx⟩ := (hS i j).2.1 hj hji
      refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_⟩
      · have hrj := Fin.lt_def.1 ((ho r).1 hr)
        rw [hcol i r (by omega), hcol r j hj]
        exact hp r hr
      · rw [hcol i j hj, hcol j j hj]
        exact hx
    · have hjk : j = k := Fin.ext hj
      subst hjk
      obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).2.2 (Fin.le_def.1 hji.le) le_rfl
      refine ⟨o, p, S i j, hnd, fun r => (ho r).trans Fin.lt_def.symm, fun r hr => ?_, hsum, ?_⟩
      · have hrj := (ho r).1 hr
        rw [hcol i r hrj, hrow r j hrj.le]
        exact hp r hr
      · rw [hrow j j le_rfl]
        exact hdiv i hji
  · -- the trailing block receives one more subtraction
    have hki : k < i := Fin.lt_def.2 (by omega)
    have hkj : k < j := Fin.lt_def.2 (by omega)
    obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).2.2 (by omega) (by omega)
    obtain ⟨q, hq, hq'⟩ := hupd i j hki hkj
    have hko : k ∉ o := fun h => lt_irrefl (k : ℕ) ((ho k).1 h)
    refine ⟨o ++ [k], Function.update p k q,
      hnd.append (List.nodup_singleton _) (List.disjoint_singleton.2 hko), fun r => ?_,
      fun r hr => ?_, ?_⟩
    · rw [List.mem_append, ho r, List.mem_singleton, Fin.ext_iff]
      omega
    · rcases List.mem_append.1 hr with hr | hr
      · have hrk := (ho r).1 hr
        rw [Function.update_of_ne (fun h => by subst h; exact lt_irrefl _ hrk), hcol i r hrk,
          hrow r j hrk.le]
        exact hp r hr
      · rw [List.mem_singleton.1 hr, Function.update_self]
        exact hq
    · rw [List.map_append, List.map_singleton, Function.update_self]
      have hmap : (o.map fun r => -Function.update p k q r) = o.map fun r => -p r := by
        refine List.map_congr_left fun r hr => ?_
        rw [Function.update_of_ne (fun h : r = k => hko (h ▸ hr))]
      rw [hmap, roundsSumFrom_append_singleton]
      exact ⟨S i j, hsum, by rw [← sub_eq_add_neg]; exact hq'⟩

/-- Before the first step the invariant holds: nothing is finished, and every entry of $A$ is a
trailing entry after $0$ steps. -/
theorem luStageInv_zero (A : Matrix (Fin n) (Fin n) ℝ) : LUStageInv fp A 0 A := fun _ _ =>
  ⟨fun h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.not_lt_zero _),
    fun _ _ => ⟨[], fun _ => 0, List.nodup_nil, fun r => by simp, by simp, .nil _⟩⟩

/-- If a packed matrix $F$ satisfies the invariant of Algorithm 3.2.1 after $n$ steps, then every
entry is finished, and the factors `packedL F` and `packedU F` form a computed LU factorization
of $A$ in the sense of `FloatingPoint.RoundsLU`. -/
theorem roundsLU_of_luStageInv {A F : Matrix (Fin n) (Fin n) ℝ} (hinv : LUStageInv fp A n F) :
    RoundsLU fp A (packedL F) (packedU F) := by
  refine ⟨fun i j hij => packedL_apply_of_lt' F hij, packedL_apply_self F,
    fun i j hij => packedU_apply_of_lt F hij, fun i j hij => ?_, fun i j hij => ?_⟩
  · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hinv i j).1 i.2 hij
    refine ⟨o, hnd, ho, p, fun r hr => ?_, ?_⟩
    · beta_reduce
      have hri := (ho r).1 hr
      rw [packedL_apply_of_lt F hri, packedU_apply_of_le F (hri.le.trans hij)]
      exact hp r hr
    · rw [packedU_apply_of_le F hij]
      exact hsum
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hx⟩ := (hinv i j).2.1 j.2 hij
    refine ⟨o, t, hnd, ho, ⟨p, fun r hr => ?_, hsum⟩, ?_⟩
    · beta_reduce
      have hrj := (ho r).1 hr
      rw [packedL_apply_of_lt F (hrj.trans hij), packedU_apply_of_le F hrj.le]
      exact hp r hr
    · rw [packedL_apply_of_lt F hij, packedU_apply_of_le F le_rfl]
      exact hx

/-- **Algorithm 3.2.1** of [golub2013matrix], rounding bridge. Let $A \in \mathbb{R}^{n \times n}$
be arbitrary. For every packed matrix $F$ that Algorithm 3.2.1 can compute in the rounding model
`fp`, the factors $\hat L$ and $\hat U$ stored in $F$ form a computed LU factorization of $A$:
$\hat L$ is unit lower triangular and $\hat U$ is upper triangular; for $i \le j$, $\hat u_{ij}$
is obtained from $a_{ij}$ by subtracting roundings of the products $\hat\ell_{ir} \hat u_{rj}$,
$r < i$, one after the other in some order, with one rounding per subtraction; and for $j < i$,
$\hat\ell_{ij}$ is a rounding of $t / \hat u_{jj}$ with $t$ obtained in the same way from
$a_{ij}$ over $r < j$.

The relation is `FloatingPoint.RoundsLU fp A (packedL F) (packedU F)`. It needs no hypothesis on
$A$: a zero pivot gives quotients $x / 0 = 0$, which the relation also allows. The invariant
after $k$ steps is `GolubVanLoan.Chapter03.LUStageInv`: the rows and columns before $k$ are
finished entries of the Doolittle recurrence, and the trailing block holds the running
differences over $r < k$. -/
theorem algorithm_3_2_1_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ F ∈ (algorithm_3_2_1 fp.round A).run, RoundsLU fp A (packedL F) (packedU F) := by
  intro F hF
  have hinv := SetM.forall_mem_run_foldlM_finRange (LUStageInv fp A) (luStageInv_zero A)
    (fun k S hS S' hS' => by
      obtain ⟨h₁, h₂, h₃⟩ := mem_run_outerProductStep k hS'
      exact luStageInv_step A k hS h₁ h₂ h₃) F hF
  exact roundsLU_of_luStageInv hinv

/-- The exact run of Algorithm 3.2.1 is one of its runs in the exact rounding model. -/
private theorem algorithm_3_2_1_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_3_2_1 pure A) ∈ (algorithm_3_2_1 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_2_1, outerProductStep, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- In exact arithmetic, for every $A \in \mathbb{R}^{n \times n}$, the factors stored in the output
of Algorithm 3.2.1 are the Doolittle factors `Matrix.luLower A` and `Matrix.luUpper A`. -/
theorem algorithm_3_2_1_packed_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    packedL (Id.run (algorithm_3_2_1 pure A)) = A.luLower ∧
      packedU (Id.run (algorithm_3_2_1 pure A)) = A.luUpper :=
  roundsLU_exact_iff.1 (algorithm_3_2_1_rounds A _ (algorithm_3_2_1_mem_exact A))

/-- **Algorithm 3.2.1** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{n \times n}$
with $A(1{:}k, 1{:}k)$ nonsingular for $k = 1, \dots, n-1$. In exact arithmetic, the factors $L$
and $U$ stored in the output of Algorithm 3.2.1 form the LU factorization $A = LU$, with $L$
unit lower triangular and $U$ upper triangular.

The proof reads the result off `GolubVanLoan.Chapter03.algorithm_3_2_1_rounds` at the exact
model. -/
theorem algorithm_3_2_1_spec {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) :
    IsLU A (packedL (Id.run (algorithm_3_2_1 pure A)))
      (packedU (Id.run (algorithm_3_2_1 pure A))) := by
  obtain ⟨hL, hU⟩ := algorithm_3_2_1_packed_eq A
  rw [hL, hU]
  exact isLU_luLower_luUpper A fun k => (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))

end Algorithm321

/-! ### Rectangular and block LU (§3.2.10–3.2.11) -/

section Rectangular

/-- **Section 3.2.10** of [golub2013matrix], existence of the rectangular LU factorization. Let
$A \in \mathbb{R}^{n \times r}$ and $p = \min\{n, r\}$. If $A(1{:}k, 1{:}k)$ is nonsingular for
$k = 1, \dots, p$, then there are a unit lower trapezoidal $L \in \mathbb{R}^{n \times p}$ and
an upper trapezoidal $U \in \mathbb{R}^{p \times r}$ with $A = LU$.

The conclusion is `Matrix.IsRectLU A L U`: $\ell_{ij} = 0$ for $i < j$, $\ell_{ii} = 1$, and
$u_{ij} = 0$ for $j < i$. -/
theorem rectangularLU_exists {n r : ℕ} {A : Matrix (Fin n) (Fin r) ℝ}
    (hA : ∀ k (hk : k + 1 ≤ min n r),
      (A.submatrix (Fin.castLE (hk.trans (min_le_left _ _)))
        (Fin.castLE (hk.trans (min_le_right _ _)))).det ≠ 0) :
    ∃ L U, IsRectLU (P := min n r) A L U :=
  exists_isRectLU_of_forall_det_ne_zero hA

end Rectangular

/-! ### Block LU and the Schur complement (§3.2.11) -/

section BlockLU

variable {r s : ℕ}

/-- **Equation (3.2.9)** of [golub2013matrix], the Schur complement. Let $A_{11}, L_{11}, U_{11} \in
\mathbb{R}^{r \times r}$, $A_{12}, U_{12} \in \mathbb{R}^{r \times s}$,
$A_{21}, L_{21} \in \mathbb{R}^{s \times r}$ and $A_{22} \in \mathbb{R}^{s \times s}$, with
$$\begin{bmatrix} A_{11} \\ A_{21} \end{bmatrix} = \begin{bmatrix} L_{11} \\ L_{21}
  \end{bmatrix} U_{11}, \qquad L_{11} U_{12} = A_{12}.$$
Then, with $\tilde A = A_{22} - L_{21} U_{12}$,
$$\begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix} = \begin{bmatrix} L_{11} & 0
  \\ L_{21} & I \end{bmatrix} \begin{bmatrix} I & 0 \\ 0 & \tilde A \end{bmatrix}
  \begin{bmatrix} U_{11} & U_{12} \\ 0 & I \end{bmatrix}.$$
If moreover $L_{11}$ is unit lower triangular and $U_{11}$ is nonsingular, then
$\tilde A = A_{22} - A_{21} A_{11}^{-1} A_{12}$, the Schur complement of $A_{11}$ in $A$.

The block matrices are `Matrix.fromBlocks` over `Fin r ⊕ Fin s`. -/
theorem equation_3_2_9 {A₁₁ L₁₁ U₁₁ : Matrix (Fin r) (Fin r) ℝ} {A₁₂ U₁₂ : Matrix (Fin r) (Fin s) ℝ}
    {A₂₁ L₂₁ : Matrix (Fin s) (Fin r) ℝ} (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (h₁₁ : A₁₁ = L₁₁ * U₁₁) (h₂₁ : A₂₁ = L₂₁ * U₁₁) (h₁₂ : L₁₁ * U₁₂ = A₁₂) :
    fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ =
        fromBlocks L₁₁ 0 L₂₁ 1 * fromBlocks 1 0 0 (A₂₂ - L₂₁ * U₁₂) * fromBlocks U₁₁ U₁₂ 0 1 ∧
      (L₁₁.IsUnitLowerTriangular → IsUnit U₁₁ →
        A₂₂ - L₂₁ * U₁₂ = A₂₂ - A₂₁ * A₁₁⁻¹ * A₁₂) := by
  refine ⟨?_, fun hL hU => ?_⟩
  · rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero,
      zero_add, h₁₁, h₂₁, h₁₂]
    congr 1
    abel
  · have hLd : IsUnit L₁₁.det := (isUnit_iff_isUnit_det _).1 hL.isUnit
    have hUd : IsUnit U₁₁.det := (isUnit_iff_isUnit_det _).1 hU
    rw [h₁₁, h₂₁, ← h₁₂, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L₁₁⁻¹ L₁₁, nonsing_inv_mul _ hLd, Matrix.one_mul,
      ← Matrix.mul_assoc U₁₁ U₁₁⁻¹, mul_nonsing_inv _ hUd, Matrix.one_mul]

/-- The entry $(i, j)$ of a $2 \times 2$ block matrix read on `Fin (r + s)` through `finSumFinEquiv`
is the entry of the block matrix at the pair of block indices that corresponds to $(i, j)$. -/
theorem reindex_fromBlocks_apply {α : Type*} (A₁₁ : Matrix (Fin r) (Fin r) α)
    (A₁₂ : Matrix (Fin r) (Fin s) α) (A₂₁ : Matrix (Fin s) (Fin r) α)
    (A₂₂ : Matrix (Fin s) (Fin s) α) (i j : Fin (r + s)) :
    reindex finSumFinEquiv finSumFinEquiv (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) i j =
      fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) :=
  rfl

/-- **Section 3.2.11** of [golub2013matrix], block LU through the Schur complement. Let
$A_{11} = L_{11} U_{11}$ be an LU factorization in $\mathbb{R}^{r \times r}$, let
$A_{21} = L_{21} U_{11}$ and $L_{11} U_{12} = A_{12}$, and let $\tilde A = A_{22} - L_{21}
U_{12} = L_{22} U_{22}$ be an LU factorization in $\mathbb{R}^{s \times s}$. Then
$$A = \begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix} = \begin{bmatrix} L_{11}
  & 0 \\ L_{21} & L_{22} \end{bmatrix} \begin{bmatrix} U_{11} & U_{12} \\ 0 & U_{22}
  \end{bmatrix}$$
is the LU factorization of $A$.

The three block matrices are read on `Fin (r + s)` through `finSumFinEquiv`. This is the step of
the recursion of Algorithm 3.2.3. -/
theorem blockLU_of_schur {A₁₁ L₁₁ U₁₁ : Matrix (Fin r) (Fin r) ℝ}
    {A₁₂ U₁₂ : Matrix (Fin r) (Fin s) ℝ} {A₂₁ L₂₁ : Matrix (Fin s) (Fin r) ℝ}
    {A₂₂ L₂₂ U₂₂ : Matrix (Fin s) (Fin s) ℝ} (h₁₁ : IsLU A₁₁ L₁₁ U₁₁) (h₂₁ : A₂₁ = L₂₁ * U₁₁)
    (h₁₂ : L₁₁ * U₁₂ = A₁₂) (h₂₂ : IsLU (A₂₂ - L₂₁ * U₁₂) L₂₂ U₂₂) :
    IsLU (reindex finSumFinEquiv finSumFinEquiv (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂))
      (reindex finSumFinEquiv finSumFinEquiv (fromBlocks L₁₁ 0 L₂₁ L₂₂))
      (reindex finSumFinEquiv finSumFinEquiv (fromBlocks U₁₁ U₁₂ 0 U₂₂)) := by
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [reindex_fromBlocks_apply]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩ <;>
      rcases finSumFinEquiv_symm_cases j with ⟨hj, hj'⟩ | ⟨hj, hj'⟩ <;> rw [hi', hj']
    · exact h₁₁.isUnitLowerTriangular.isLowerTriangular
        (OrderDual.toDual_lt_toDual.2 (Fin.lt_def.2 (Fin.lt_def.1 hij')))
    · rfl
    · exact (by have := Fin.lt_def.1 hij'; omega : False).elim
    · exact h₂₂.isUnitLowerTriangular.isLowerTriangular (OrderDual.toDual_lt_toDual.2
        (Fin.lt_def.2 (show (i : ℕ) - r < j - r by have := Fin.lt_def.1 hij'; omega)))
  · rw [reindex_fromBlocks_apply]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩ <;> rw [hi']
    · exact h₁₁.isUnitLowerTriangular.diag_eq_one _
    · exact h₂₂.isUnitLowerTriangular.diag_eq_one _
  · dsimp only [id] at hij
    rw [reindex_fromBlocks_apply]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩ <;>
      rcases finSumFinEquiv_symm_cases j with ⟨hj, hj'⟩ | ⟨hj, hj'⟩ <;> rw [hi', hj']
    · exact h₁₁.isUpperTriangular (Fin.lt_def.2 (Fin.lt_def.1 hij))
    · exact (by have := Fin.lt_def.1 hij; omega : False).elim
    · rfl
    · exact h₂₂.isUpperTriangular
        (Fin.lt_def.2 (show (j : ℕ) - r < i - r by have := Fin.lt_def.1 hij; omega))
  · rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
    congr 1
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, h₁₁.mul_eq, h₂₂.mul_eq, h₁₂, ← h₂₁,
      add_sub_cancel]

end BlockLU

/-! ### The outer product point of view (§3.2.7) -/

section OuterProduct

variable {s : ℕ}

/-- **Section 3.2.7** of [golub2013matrix], the outer product point of view. Let
$\alpha \in \mathbb{R}$ with $\alpha \neq 0$, let $w, z \in \mathbb{R}^s$ and
$B \in \mathbb{R}^{s \times s}$, and let $A = \begin{bmatrix} \alpha & w^T \\ z & B
\end{bmatrix}$. Then the first step of Gaussian elimination is the decomposition
$$A = \begin{bmatrix} 1 & 0 \\ z/\alpha & I \end{bmatrix} \begin{bmatrix} 1 & 0 \\ 0 & B -
  zw^T/\alpha \end{bmatrix} \begin{bmatrix} \alpha & w^T \\ 0 & I \end{bmatrix},$$
and if $B - zw^T/\alpha = L_1 U_1$ is an LU factorization, then
$$A = \begin{bmatrix} 1 & 0 \\ z/\alpha & L_1 \end{bmatrix} \begin{bmatrix} \alpha & w^T \\ 0 &
  U_1 \end{bmatrix}$$
is the LU factorization of $A$.

The first identity is over `Fin 1 ⊕ Fin s`, and the factorization is read on `Fin (1 + s)`
through `finSumFinEquiv`. This is the case $r = 1$ of (3.2.9) and of
`GolubVanLoan.Chapter03.blockLU_of_schur`. -/
theorem outerProduct_decomposition {α : ℝ} (hα : α ≠ 0) (w z : Fin s → ℝ)
    (B : Matrix (Fin s) (Fin s) ℝ) :
    fromBlocks (of fun _ _ => α : Matrix (Fin 1) (Fin 1) ℝ) (of fun _ j => w j)
        (of fun i _ => z i) B =
      fromBlocks 1 0 (of fun i _ => z i / α) 1 *
          fromBlocks 1 0 0 (B - of fun i j => z i * w j / α) *
        fromBlocks (of fun _ _ => α) (of fun _ j => w j) 0 1 ∧
      ∀ L₁ U₁ : Matrix (Fin s) (Fin s) ℝ, IsLU (B - of fun i j => z i * w j / α) L₁ U₁ →
        IsLU (reindex finSumFinEquiv finSumFinEquiv (fromBlocks (of fun _ _ => α : Matrix (Fin 1)
            (Fin 1) ℝ) (of fun _ j => w j) (of fun i _ => z i) B))
          (reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 (of fun i _ => z i / α) L₁))
          (reindex finSumFinEquiv finSumFinEquiv
            (fromBlocks (of fun _ _ => α) (of fun _ j => w j) 0 U₁)) := by
  have h₁₁ : (of fun _ _ => α : Matrix (Fin 1) (Fin 1) ℝ) = 1 * of fun _ _ => α :=
    (Matrix.one_mul _).symm
  have h₂₁ : (of fun i _ => z i : Matrix (Fin s) (Fin 1) ℝ) =
      (of fun i _ => z i / α) * (of fun _ _ => α : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [Matrix.mul_apply, div_mul_cancel₀ _ hα]
  have h₁₂ : (1 : Matrix (Fin 1) (Fin 1) ℝ) * (of fun _ j => w j : Matrix (Fin 1) (Fin s) ℝ) =
      of fun _ j => w j := Matrix.one_mul _
  have hmul : (of fun i (_ : Fin 1) => z i / α) * (of fun (_ : Fin 1) j => w j) =
      (of fun i j => z i * w j / α : Matrix (Fin s) (Fin s) ℝ) := by
    ext i j
    simp [Matrix.mul_apply]
    ring
  refine ⟨?_, fun L₁ U₁ h => ?_⟩
  · have := (equation_3_2_9 B h₁₁ h₂₁ h₁₂).1
    rwa [hmul] at this
  · have h₁ : IsLU (of fun _ _ => α : Matrix (Fin 1) (Fin 1) ℝ) 1 (of fun _ _ => α) :=
      ⟨isUnitLowerTriangular_one, fun i j hij => (lt_irrefl i (Subsingleton.elim j i ▸ hij)).elim,
        Matrix.one_mul _⟩
    exact blockLU_of_schur h₁ h₂₁ h₁₂ (by rwa [hmul])

end OuterProduct

/-! ### Algorithm 3.2.2 (Gaxpy LU) and the rectangular outer product LU (3.2.8) -/

section Gaxpy

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.2.2** of [golub2013matrix], the column of the gaxpy LU. Let
$L \in \mathbb{R}^{n \times n}$, let $\tilde a \in \mathbb{R}^n$ be column $j$ of $A$, and let
$j$ be an index. The algorithm solves $L(1{:}j{-}1, 1{:}j{-}1) z = \tilde a(1{:}j{-}1)$ and
forms $v(j{:}n) = \tilde a(j{:}n) - L(j{:}n, 1{:}j{-}1) z$, in one loop over the rows: for each
$i$ in increasing order, $v_i$ is obtained from $\tilde a_i$ by subtracting
$\mathrm{fl}(\ell_{ir} v_r)$ for $r < \min(i, j)$ in increasing order, with one rounding per
subtraction.

For $i < j$ this is the row-oriented unit lower triangular solve, which does not divide by the
unit diagonal; for $i \ge j$ it is the gaxpy. Both read the solved $z = v(1{:}j{-}1)$. Each
$v_i$ is `FloatingPoint.runningDiff`. Algorithm 3.4.2 shares this program. -/
noncomputable def gaxpyColumn {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (ã : Fin n → ℝ) (j : Fin n) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (v : Fin n → ℝ) i => do
    let vi ← runningDiff rnd ((List.finRange n).filter (fun r => r < i ∧ r < j)) (L i) v (ã i)
    pure (Function.update v i vi)) ã

/-- **Algorithm 3.2.2** of [golub2013matrix] (gaxpy LU). Suppose that
$A \in \mathbb{R}^{n \times n}$ has the property that $A(1{:}k, 1{:}k)$ is nonsingular for
$k = 1{:}n-1$. The algorithm computes the factorization $A = LU$, where $L$ is unit lower
triangular and $U$ is upper triangular. It initializes $L$ to the identity and $U$ to the zero
matrix.
```
for j = 1:n
    if j = 1
        v = A(:,1)
    else
        ã = A(:,j)
        Solve L(1:j-1,1:j-1) · z = ã(1:j-1) for z ∈ ℝ^{j-1}.
        U(1:j-1,j) = z,  v(j:n) = ã(j:n) - L(j:n,1:j-1) · z
    end
    U(j,j) = v(j),  L(j+1:n,j) = v(j+1:n)/v(j)
end
```
For each column $j$ the program computes $v$ by `GolubVanLoan.Chapter03.gaxpyColumn`, sets
$\ell_{ij} \leftarrow \mathrm{fl}(v_i / v_j)$ for $i > j$, and sets column $j$ of $U$ to $v_i$
for $i \le j$ and to $0$ below.

The state is the pair $(L, U)$. The unit lower triangular solve and the gaxpy are both running
differences, without division by the unit diagonal. The program has no hypothesis on $A$. -/
noncomputable def algorithm_3_2_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) j => do
    let v ← gaxpyColumn rnd st.1 (fun i => A i j) j
    let L ← ((List.finRange n).filter (j < ·)).foldlM (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
      let l ← rnd (v i / v j)
      pure (L.updateRow i (Function.update (L i) j l))) st.1
    pure (L, st.2.updateCol j fun i => if i ≤ j then v i else 0)) (1, 0)

/-- **Equation (3.2.8)** of [golub2013matrix], outer product LU of a tall matrix. Let
$A \in \mathbb{R}^{n \times r}$ with $r \le n$. Algorithm 3.2.1 is modified as follows:
```
for k = 1:r
    ρ = k+1:n
    A(ρ,k) = A(ρ,k)/A(k,k)
    if k < r
        μ = k+1:r
        A(ρ,μ) = A(ρ,μ) - A(ρ,k) · A(k,μ)
    end
end
```
Upon completion, $A$ is overwritten by the strictly lower triangular part of
$L \in \mathbb{R}^{n \times r}$ and the upper triangular part of
$U \in \mathbb{R}^{r \times r}$.

The program computes $a_{ik} \leftarrow \mathrm{fl}(a_{ik} / a_{kk})$ for $i > k$, and then
$a_{ij} \leftarrow \mathrm{fl}(a_{ij} - \mathrm{fl}(a_{ik} a_{kj}))$ for $i > k$ and
$k < j \le r$, row by row. The guard $k < r$ of the source is the emptiness of $\mu$. The
factors are read by `GolubVanLoan.Chapter03.tallPackedL` and
`GolubVanLoan.Chapter03.tallPackedU`. -/
noncomputable def tallOuterProductLU {n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin n) (Fin r) ℝ) :
    M (Matrix (Fin n) (Fin r) ℝ) :=
  (List.finRange r).foldlM (fun (A : Matrix (Fin n) (Fin r) ℝ) k => do
    let A ← ((List.finRange n).filter (Fin.castLE hrn k < ·)).foldlM
      (fun (A : Matrix (Fin n) (Fin r) ℝ) i => do
        let l ← rnd (A i k / A (Fin.castLE hrn k) k)
        pure (A.updateRow i (Function.update (A i) k l))) A
    ((List.finRange n).filter (Fin.castLE hrn k < ·)).foldlM
      (fun (A : Matrix (Fin n) (Fin r) ℝ) i =>
        ((List.finRange r).filter (k < ·)).foldlM (fun (A : Matrix (Fin n) (Fin r) ℝ) j => do
          let p ← rnd (A i k * A (Fin.castLE hrn k) j)
          let a ← rnd (A i j - p)
          pure (A.updateRow i (Function.update (A i) j a))) A) A) A

end Gaxpy

/-! ### Recursive block LU (Algorithm 3.2.3) -/

section BlockLUAlgorithm

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.2.3** of [golub2013matrix] (recursive block LU). Suppose that
$A \in \mathbb{R}^{n \times n}$ has an LU factorization and $r$ is a positive integer. The
algorithm computes a unit lower triangular $L \in \mathbb{R}^{n \times n}$ and an upper
triangular $U \in \mathbb{R}^{n \times n}$ with $A = LU$.
```
function [L, U] = BlockLU(A, n, r)
if n ≤ r
    Compute the LU factorization A = LU using (say) Algorithm 3.2.1.
else
    Use (3.2.8) to compute the LU factorization A(:,1:r) = [L₁₁; L₂₁] U₁₁.
    Solve L₁₁ U₁₂ = A(1:r, r+1:n) for U₁₂.
    Ã = A(r+1:n, r+1:n) - L₂₁ U₁₂
    [L₂₂, U₂₂] = BlockLU(Ã, n - r, r)
    L = [L₁₁ 0; L₂₁ L₂₂],  U = [U₁₁ U₁₂; 0 U₂₂]
end
```
For $n \le r$ the program runs Algorithm 3.2.1. Otherwise it runs (3.2.8) on the first $r$
columns, solves $L_{11} U_{12} = A_{12}$ column by column by the unit lower triangular solve
`GolubVanLoan.Chapter03.unitForwardSubstColOn`, computes each entry of
$\tilde A = A_{22} - L_{21} U_{12}$ as a running difference, calls itself on $\tilde A$, and
assembles the blocks.

The recursion is on $n$, and the split `Fin n ≃ Fin r ⊕ Fin (n - r)` is `finSumFinEquiv`
followed by `finCongr`. The unit solve is Algorithm 3.1.3 without the division by the unit
diagonal. The running differences (`FloatingPoint.runningDiff`) follow the order of the level-3
update of (3.1.4); the source does not analyse the rounding of its level-3 product. -/
noncomputable def algorithm_3_2_3 (r : ℕ) (hr : 0 < r) :
    (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
  | n, A =>
    if h : n ≤ r then do
      let F ← algorithm_3_2_1 rnd A
      pure (packedL F, packedU F)
    else do
      let e : Fin r ⊕ Fin (n - r) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
      let F ← tallOuterProductLU rnd (le_of_lt (not_le.1 h)) (fun i k => A i (e (Sum.inl k)))
      let L₁₁ : Matrix (Fin r) (Fin r) ℝ := of fun i k =>
        if k < i then F (e (Sum.inl i)) k else if i = k then 1 else 0
      let L₂₁ : Matrix (Fin (n - r)) (Fin r) ℝ := of fun i k => F (e (Sum.inr i)) k
      let U₁₁ : Matrix (Fin r) (Fin r) ℝ := of fun i k => if i ≤ k then F (e (Sum.inl i)) k else 0
      let U₁₂ ← (List.finRange (n - r)).foldlM (fun (U₁₂ : Matrix (Fin r) (Fin (n - r)) ℝ) c => do
        let col ← unitForwardSubstColOn rnd (List.finRange r) L₁₁
          (fun i => A (e (Sum.inl i)) (e (Sum.inr c)))
        pure (U₁₂.updateCol c col)) 0
      let Ã ← (List.finRange (n - r)).foldlM (fun (Ã : Matrix (Fin (n - r)) (Fin (n - r)) ℝ) i =>
        (List.finRange (n - r)).foldlM (fun (Ã : Matrix (Fin (n - r)) (Fin (n - r)) ℝ) j => do
          let a ← runningDiff rnd (List.finRange r) (L₂₁ i) (fun k => U₁₂ k j)
            (A (e (Sum.inr i)) (e (Sum.inr j)))
          pure (Ã.updateRow i (Function.update (Ã i) j a))) Ã) 0
      let LU₂₂ ← algorithm_3_2_3 r hr (n - r) Ã
      pure (reindex e e (fromBlocks L₁₁ 0 L₂₁ LU₂₂.1), reindex e e (fromBlocks U₁₁ U₁₂ 0 LU₂₂.2))
  termination_by n => n
  decreasing_by omega

end BlockLUAlgorithm

/-! ### The bridge of Algorithm 3.2.2 -/

section GaxpyBridge

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- The run set of `GolubVanLoan.Chapter03.gaxpyColumn`. For every output $v$ in the rounding model
`fp` and every $i$, $v_i$ is obtained from $\tilde a_i$ by subtracting roundings of the products
$\ell_{ir} v_r$, $r < \min(i, j)$, in increasing order, with one rounding per subtraction; the
$v_r$ are the entries of the output itself. -/
theorem gaxpyColumn_rounds (L : Matrix (Fin n) (Fin n) ℝ) (ã : Fin n → ℝ) (j : Fin n) :
    ∀ v ∈ (gaxpyColumn fp.round L ã j).run, ∀ i, RoundsRunningDiff fp
      ((List.finRange n).filter (fun r => r < i ∧ r < j)) (L i) v (ã i) (v i) := by
  intro v hv
  have key := SetM.forall_mem_run_foldlM_update_of_nodup (List.nodup_finRange n)
    (fun i (s : Fin n → ℝ) =>
      runningDiff fp.round ((List.finRange n).filter (fun r => r < i ∧ r < j)) (L i) s (ã i))
    (fun i s x => RoundsRunningDiff fp ((List.finRange n).filter (fun r => r < i ∧ r < j))
      (L i) s (ã i) x) ã ?_ ?_ v hv
  · exact fun i => key i (List.mem_finRange i)
  · rintro p i q - s - x hx
    exact (mem_run_runningDiff_iff ((List.nodup_finRange n).filter _)).1 hx
  · rintro p i q hl s s' x hss hx
    refine hx.congr (fun _ _ => rfl) fun r hr => (hss r ?_).symm
    have hri : r < i := (by simpa using hr : r < i ∧ r < j).1
    exact List.mem_prefix_of_pairwise (List.pairwise_lt_finRange n) hl
      (List.mem_finRange r) (ne_of_lt hri) (lt_asymm hri)

/-- The invariant of Algorithm 3.2.2 after the first $j$ columns, for a state $(L, U)$. In each
column $c < j$, the entries $u_{ic}$, $i \le c$, are running differences of $a_{ic}$ over
$r < i$, and the entries $\ell_{ic}$, $c < i$, are roundings of $t / u_{cc}$ with $t$ a running
difference of $a_{ic}$ over $r < c$, as in `FloatingPoint.RoundsLU`. The columns $c \ge j$ of
$L$ and $U$ are those of the identity and of the zero matrix. Moreover $L$ is unit lower
triangular and $U$ is upper triangular. -/
def GaxpyInv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (j : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i c : Fin n, (c : ℕ) < j → i ≤ c → ∃ o : List (Fin n), o.Nodup ∧ (∀ r, r ∈ o ↔ r < i) ∧
    RoundsRunningDiff fp o (st.1 i) (fun r => st.2 r c) (A i c) (st.2 i c)) ∧
  (∀ i c : Fin n, (c : ℕ) < j → c < i → ∃ (o : List (Fin n)) (t : ℝ), o.Nodup ∧
    (∀ r, r ∈ o ↔ r < c) ∧ RoundsRunningDiff fp o (st.1 i) (fun r => st.2 r c) (A i c) t ∧
    fp.Rounds (t / st.2 c c) (st.1 i c)) ∧
  (∀ i c : Fin n, j ≤ (c : ℕ) → st.1 i c = if i = c then 1 else 0) ∧
  (∀ i c : Fin n, j ≤ (c : ℕ) → st.2 i c = 0) ∧
  (∀ i c : Fin n, i < c → st.1 i c = 0) ∧ (∀ i, st.1 i i = 1) ∧
  (∀ i c : Fin n, c < i → st.2 i c = 0)

/-- Before the first column the invariant of Algorithm 3.2.2 holds for $(L, U) = (I, 0)$. -/
theorem gaxpyInv_zero (A : Matrix (Fin n) (Fin n) ℝ) : GaxpyInv fp A 0 (1, 0) :=
  ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _),
    fun i c _ => by simp [Matrix.one_apply], fun _ _ _ => rfl,
    fun i c h => by simp [h.ne],
    fun i => by simp, fun _ _ _ => rfl⟩

/-- A new entry $\ell_{ij}$, $j < i$, of the gaxpy LU. If $v_i$ is a running difference of $a_{ij}$
over $r < \min(i, j) = j$ against row $i$ of $L$ and $v$, and $L'$ agrees with $L$ in row $i$ on
the columns $r < j$, then $v_i$ is a running difference of $a_{ij}$ over $r < j$ against row $i$
of $L'$ and the new column $j$ of $U$. -/
theorem gaxpy_newCol_lower {A L L' : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (hji : j < i)
    {v : Fin n → ℝ} (hvi : RoundsRunningDiff fp
      ((List.finRange n).filter (fun r => r < i ∧ r < j)) (L i) v (A i j) (v i))
    (hLc : ∀ r, r < j → L' i r = L i r) (U : Matrix (Fin n) (Fin n) ℝ) :
    ∃ o : List (Fin n), o.Nodup ∧ (∀ r, r ∈ o ↔ r < j) ∧ RoundsRunningDiff fp o (L' i)
      (fun r => U.updateCol j (fun i => if i ≤ j then v i else 0) r j) (A i j) (v i) := by
  refine ⟨_, (List.nodup_finRange n).filter _, fun r => ?_, hvi.congr (fun r hr => ?_)
    fun r hr => ?_⟩
  · simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨h.trans hji, h⟩⟩
  · exact hLc r (by simpa using hr : r < i ∧ r < j).2
  · rw [updateCol_self, ite_eq_left (by simpa using hr : r < i ∧ r < j).2.le]

/-- One column of the gaxpy LU keeps its invariant. Let $(L, U)$ satisfy the invariant after $j$
columns, let $v$ satisfy, for every $i$, that $v_i$ is a running difference of $a_{ij}$ over
$r < \min(i, j)$ against row $i$ of $L$ and $v$, and let $L'$ differ from $L$ only in the
entries $\ell'_{ij}$, $i > j$, each a rounding of $v_i / v_j$. Then $L'$ and $U$ with column $j$
replaced by $v$ on the rows $i \le j$ and by $0$ below satisfy the invariant after $j + 1$
columns.

Algorithms 3.2.2 and 3.4.2 share this step. -/
theorem gaxpyInv_succ {A L U : Matrix (Fin n) (Fin n) ℝ} {j : Fin n}
    (hst : GaxpyInv fp A j (L, U)) {v : Fin n → ℝ}
    (hv : ∀ i, RoundsRunningDiff fp ((List.finRange n).filter (fun r => r < i ∧ r < j)) (L i) v
      (A i j) (v i))
    {L' : Matrix (Fin n) (Fin n) ℝ} (hL'o : ∀ i c, ¬ (j < i ∧ c = j) → L' i c = L i c)
    (hL'j : ∀ i, j < i → fp.Rounds (v i / v j) (L' i j)) :
    GaxpyInv fp A (j + 1) (L', U.updateCol j fun i => if i ≤ j then v i else 0) := by
  obtain ⟨hU, hL, hLid, hU0, hLlow, hLdiag, hUup⟩ := hst
  dsimp only at hU hL hLid hU0 hLlow hLdiag hUup
  have hLc : ∀ i c, c ≠ j → L' i c = L i c := fun i c hc => hL'o i c fun h => hc h.2
  set U' := U.updateCol j fun i => if i ≤ j then v i else 0 with hU'
  have hU'o : ∀ i c, c ≠ j → U' i c = U i c := fun i c hc => by
    simp [hU', hc]
  have hU'j : ∀ i, U' i j = if i ≤ j then v i else 0 := fun i => by simp [hU']
  -- the columns before `j` are unchanged, and so are their products
  have hcol : ∀ i c r : Fin n, c < j → r ≤ c → L' i r = L i r ∧ U' r c = U r c :=
    fun i c r hc hr => ⟨hLc i r (ne_of_lt (lt_of_le_of_lt hr hc)), hU'o r c (ne_of_lt hc)⟩
  dsimp only [GaxpyInv]
  refine ⟨fun i c hc hic => ?_, fun i c hc hci => ?_, fun i c hc => ?_, fun i c hc => ?_,
    fun i c hic => ?_, fun i => ?_, fun i c hci => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
    · have hc' : c < j := Fin.lt_def.2 hc
      obtain ⟨o, hnd, ho, hrd⟩ := hU i c hc hic
      refine ⟨o, hnd, ho, ?_⟩
      rw [hU'o i c (ne_of_lt hc')]
      exact hrd.congr (fun r hr => (hcol i c r hc' (((ho r).1 hr).le.trans hic)).1)
        fun r hr => (hcol i c r hc' (((ho r).1 hr).le.trans hic)).2
    · have hcj : c = j := Fin.ext hc
      subst hcj
      refine ⟨(List.finRange n).filter (fun r => r < i ∧ r < c), (List.nodup_finRange n).filter _,
        fun r => ?_, ?_⟩
      · simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        exact ⟨And.left, fun h => ⟨h, lt_of_lt_of_le h hic⟩⟩
      · rw [hU'j i, ite_eq_left hic]
        refine (hv i).congr (fun r hr => hLc i r (ne_of_lt (by simpa using hr : r < i ∧ r < c).2))
          fun r hr => ?_
        rw [hU'j r, ite_eq_left (by simpa using hr : r < i ∧ r < c).2.le]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
    · have hc' : c < j := Fin.lt_def.2 hc
      obtain ⟨o, t, hnd, ho, hrd, hx⟩ := hL i c hc hci
      refine ⟨o, t, hnd, ho, hrd.congr (fun r hr => (hcol i c r hc' ((ho r).1 hr).le).1)
        fun r hr => (hcol i c r hc' ((ho r).1 hr).le).2, ?_⟩
      rw [hU'o c c (ne_of_lt hc'), hLc i c (ne_of_lt hc')]
      exact hx
    · have hcj : c = j := Fin.ext hc
      subst hcj
      obtain ⟨o, hnd, ho, hrd⟩ := gaxpy_newCol_lower hci (hv i)
        (fun r hr => hLc i r (ne_of_lt hr)) U
      refine ⟨o, v i, hnd, ho, hrd, ?_⟩
      rw [hU'j c, ite_eq_left le_rfl]
      exact hL'j i hci
  · have hcj : c ≠ j := fun h => by rw [h] at hc; exact absurd hc (by simp)
    rw [hLc i c hcj]
    exact hLid i c (by omega)
  · have hcj : c ≠ j := fun h => by rw [h] at hc; exact absurd hc (by simp)
    rw [hU'o i c hcj]
    exact hU0 i c (by omega)
  · by_cases hcj : c = j
    · subst hcj
      rw [hL'o i c fun h => lt_asymm h.1 hic]
      exact hLlow i c hic
    · rw [hLc i c hcj]
      exact hLlow i c hic
  · rw [hL'o i i fun ⟨h1, h2⟩ => by subst h2; exact lt_irrefl _ h1]
    exact hLdiag i
  · by_cases hcj : c = j
    · subst hcj
      rw [hU'j i, ite_eq_right (not_le.2 hci)]
    · rw [hU'o i c hcj]
      exact hUup i c hci

/-- The multiplier loop of Algorithms 3.2.2 and 3.4.2. Every output $L'$ of the loop that writes
$\ell_{ij} = \mathrm{fl}(v_i / v_j)$ for $i > j$ into $L_0$, in the rounding model `fp`, agrees
with $L_0$ outside these entries, and each $\ell'_{ij}$, $i > j$, is a rounding of $v_i / v_j$. -/
theorem mem_run_multipliers {j : Fin n} {v : Fin n → ℝ} {L₀ L' : Matrix (Fin n) (Fin n) ℝ}
    (h : L' ∈ (((List.finRange n).filter (j < ·)).foldlM
      (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
        let l ← fp.round (v i / v j)
        pure (L.updateRow i (Function.update (L i) j l))) L₀).run) :
    (∀ i c, ¬ (j < i ∧ c = j) → L' i c = L₀ i c) ∧ ∀ i, j < i → fp.Rounds (v i / v j) (L' i j) := by
  have hL'eq : ((List.finRange n).filter (j < ·)).foldlM
      (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
        let l ← fp.round (v i / v j)
        pure (L.updateRow i (Function.update (L i) j l))) L₀ =
      (((List.finRange n).filter (j < ·)).map (·, j)).foldlM
        (fun (L : Matrix (Fin n) (Fin n) ℝ) a => do
          let x ← (fun (a : Fin n × Fin n) (_ : ℝ) (_ : Matrix (Fin n) (Fin n) ℝ) =>
            fp.round (v a.1 / v j)) a (L a.1 a.2) L
          pure (L.updateRow a.1 (Function.update (L a.1) a.2 x))) L₀ := by
    rw [List.foldlM_map]
  have hnd₁ : ((List.finRange n).filter (j < ·)).Nodup := (List.nodup_finRange n).filter _
  have hl₁ : (((List.finRange n).filter (j < ·)).map (·, j)).Nodup :=
    hnd₁.map fun _ _ h => (Prod.mk.inj h).1
  have hl₁mem : ∀ i c, (i, c) ∈ ((List.finRange n).filter (j < ·)).map (·, j) ↔
      j < i ∧ c = j := fun i c => by
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨ha, rfl⟩
    · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl, rfl⟩
  rw [hL'eq] at h
  obtain ⟨hL'₁, hL'₂⟩ := (SetM.mem_run_foldlM_updateRow_update_of_nodup _ hl₁
    (fun a _ (_ : Matrix (Fin n) (Fin n) ℝ) => fp.round (v a.1 / v j))
    (fun _ _ _ _ _ _ => rfl) L₀ L').1 h
  exact ⟨fun i c hic => hL'₁ i c fun hm => hic ((hl₁mem i c).1 hm),
    fun i hi => hL'₂ (i, j) ((hl₁mem i j).2 ⟨hi, rfl⟩)⟩

/-- One column step of Algorithm 3.2.2 in the rounding model maps every state that satisfies the
invariant after $j$ columns to states that satisfy it after $j + 1$ columns. -/
theorem gaxpyInv_step (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (hst : GaxpyInv fp A j st)
    (st' : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (hst' : st' ∈ (do
      let v ← gaxpyColumn fp.round st.1 (fun i => A i j) j
      let L ← ((List.finRange n).filter (j < ·)).foldlM
        (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
          let l ← fp.round (v i / v j)
          pure (L.updateRow i (Function.update (L i) j l))) st.1
      pure (L, st.2.updateCol j fun i => if i ≤ j then v i else 0) : SetM _).run) :
    GaxpyInv fp A (j + 1) st' := by
  obtain ⟨L, U⟩ := st
  rw [SetM.mem_run_bind] at hst'
  obtain ⟨v, hv, hst'⟩ := hst'
  rw [SetM.mem_run_bind] at hst'
  obtain ⟨L', hL', hst'⟩ := hst'
  rw [SetM.mem_run_pure] at hst'
  subst hst'
  obtain ⟨hL'o, hL'j⟩ := mem_run_multipliers hL'
  exact gaxpyInv_succ hst (gaxpyColumn_rounds L _ j v hv) hL'o hL'j

/-- **Algorithm 3.2.2** of [golub2013matrix], rounding bridge. Let $A \in \mathbb{R}^{n \times n}$
be arbitrary. Every pair $(\hat L, \hat U)$ that Algorithm 3.2.2 can compute in the rounding
model `fp` is a computed LU factorization of $A$ in the sense of `FloatingPoint.RoundsLU`: for
$i \le j$, $\hat u_{ij}$ is the running difference of $a_{ij}$ over $r < i$, and for $j < i$,
$\hat\ell_{ij}$ is the running difference of $a_{ij}$ over $r < j$ divided by $\hat u_{jj}$ with
one rounding.

The entries $\hat u_{ij}$ with $i < j$ come from the unit triangular solve, the entry
$\hat u_{jj}$ and the entries $\hat\ell_{ij}$ from the gaxpy. The bridge needs no hypothesis on
$A$. -/
theorem algorithm_3_2_2_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ out ∈ (algorithm_3_2_2 fp.round A).run, RoundsLU fp A out.1 out.2 := by
  intro out hout
  obtain ⟨hU, hL, -, -, hLlow, hLdiag, hUup⟩ := SetM.forall_mem_run_foldlM_finRange
    (GaxpyInv fp A) (gaxpyInv_zero A) (fun j st hst st' hst' => gaxpyInv_step A j st hst st' hst')
    out hout
  exact ⟨hLlow, hLdiag, hUup, fun i j hij => hU i j j.2 hij, fun i j hji => hL i j j.2 hji⟩

/-- The exact run of Algorithm 3.2.2 is one of its runs in the exact rounding model. -/
private theorem algorithm_3_2_2_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_3_2_2 pure A) ∈ (algorithm_3_2_2 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_2_2, gaxpyColumn, runningDiff, pure_bind, List.foldlM_pure,
    SetM.mem_run_pure]
  rfl

/-- **Algorithm 3.2.2** of [golub2013matrix], exact correctness. For every
$A \in \mathbb{R}^{n \times n}$, the exact output $(L, U)$ of Algorithm 3.2.2 is the pair of
Doolittle factors (`Matrix.luLower A`, `Matrix.luUpper A`). If moreover $A(1{:}k, 1{:}k)$ is
nonsingular for $k = 1, \dots, n-1$, then $A = LU$ is the LU factorization of $A$.

The proof reads the result off `GolubVanLoan.Chapter03.algorithm_3_2_2_rounds` at the exact
model. -/
theorem algorithm_3_2_2_spec (A : Matrix (Fin n) (Fin n) ℝ) :
    (Id.run (algorithm_3_2_2 pure A)).1 = A.luLower ∧
      (Id.run (algorithm_3_2_2 pure A)).2 = A.luUpper ∧
      ((∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) →
        IsLU A (Id.run (algorithm_3_2_2 pure A)).1 (Id.run (algorithm_3_2_2 pure A)).2) := by
  obtain ⟨hL, hU⟩ := roundsLU_exact_iff.1 (algorithm_3_2_2_rounds A _ (algorithm_3_2_2_mem_exact A))
  refine ⟨hL, hU, fun hA => ?_⟩
  rw [hL, hU]
  exact isLU_luLower_luUpper A fun k => (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))

end GaxpyBridge

/-! ### The rectangular outer product LU (3.2.8): exact semantics -/

section TallLU

/-- One step $k$ of (3.2.8): the multipliers of column $k$ below the pivot row, then the update of
the columns $k+1, \dots, r$ in the rows below the pivot row. -/
private noncomputable def tallOuterProductStep {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    {n r : ℕ} (hrn : r ≤ n) (k : Fin r) (A : Matrix (Fin n) (Fin r) ℝ) :
    M (Matrix (Fin n) (Fin r) ℝ) := do
  let A ← ((List.finRange n).filter (Fin.castLE hrn k < ·)).foldlM
    (fun (A : Matrix (Fin n) (Fin r) ℝ) i => do
      let l ← rnd (A i k / A (Fin.castLE hrn k) k)
      pure (A.updateRow i (Function.update (A i) k l))) A
  ((List.finRange n).filter (Fin.castLE hrn k < ·)).foldlM
    (fun (A : Matrix (Fin n) (Fin r) ℝ) i =>
      ((List.finRange r).filter (k < ·)).foldlM (fun (A : Matrix (Fin n) (Fin r) ℝ) j => do
        let p ← rnd (A i k * A (Fin.castLE hrn k) j)
        let a ← rnd (A i j - p)
        pure (A.updateRow i (Function.update (A i) j a))) A) A

variable {n r : ℕ}

private theorem tallOuterProductLU_eq_foldlM {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (hrn : r ≤ n) (A : Matrix (Fin n) (Fin r) ℝ) :
    tallOuterProductLU rnd hrn A =
      (List.finRange r).foldlM (fun A k => tallOuterProductStep rnd hrn k A) A :=
  rfl

/-- The run set of one step of (3.2.8), as `GolubVanLoan.Chapter03.mem_run_outerProductStep` for
Algorithm 3.2.1: the multipliers below the pivot row are rounded quotients, the entries right of
column $k$ below the pivot row receive one rounded update, and every other entry is unchanged. -/
private theorem mem_run_tallOuterProductStep {fp : RoundingModel ℝ} (hrn : r ≤ n) (k : Fin r)
    {S S' : Matrix (Fin n) (Fin r) ℝ} (h : S' ∈ (tallOuterProductStep fp.round hrn k S).run) :
    (∀ i j, ¬ (Fin.castLE hrn k < i ∧ (j = k ∨ k < j)) → S' i j = S i j) ∧
      (∀ i, Fin.castLE hrn k < i → fp.Rounds (S i k / S (Fin.castLE hrn k) k) (S' i k)) ∧
      ∀ i j, Fin.castLE hrn k < i → k < j →
        ∃ p, fp.Rounds (S' i k * S' (Fin.castLE hrn k) j) p ∧ fp.Rounds (S i j - p) (S' i j) := by
  set K := Fin.castLE hrn k with hK
  rw [tallOuterProductStep, SetM.mem_run_bind] at h
  obtain ⟨S₁, h₁, h₂⟩ := h
  have hnd : ((List.finRange n).filter (K < ·)).Nodup := (List.nodup_finRange n).filter _
  have hndc : ((List.finRange r).filter (k < ·)).Nodup := (List.nodup_finRange r).filter _
  have hmem : ∀ i, i ∈ (List.finRange n).filter (K < ·) ↔ K < i := fun i => by simp
  have hmemc : ∀ j, j ∈ (List.finRange r).filter (k < ·) ↔ k < j := fun j => by simp
  -- the division loop
  have hdiv : ((List.finRange n).filter (K < ·)).foldlM
      (fun (A : Matrix (Fin n) (Fin r) ℝ) i => do
        let l ← fp.round (A i k / A K k)
        pure (A.updateRow i (Function.update (A i) k l))) S =
      (((List.finRange n).filter (K < ·)).map (·, k)).foldlM
        (fun (A : Matrix (Fin n) (Fin r) ℝ) a => do
          let x ← (fun (_ : Fin n × Fin r) x (A : Matrix (Fin n) (Fin r) ℝ) =>
            fp.round (x / A K k)) a (A a.1 a.2) A
          pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) S := by
    rw [List.foldlM_map]
  have hl₁ : (((List.finRange n).filter (K < ·)).map (·, k)).Nodup :=
    hnd.map fun _ _ h => (Prod.mk.inj h).1
  have hl₁mem : ∀ i j, (i, j) ∈ ((List.finRange n).filter (K < ·)).map (·, k) ↔
      K < i ∧ j = k := fun i j => by
    simp only [List.mem_map, hmem, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨ha, rfl⟩
    · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl, rfl⟩
  rw [hdiv] at h₁
  obtain ⟨hS₁, hS₁'⟩ := (SetM.mem_run_foldlM_updateRow_update_of_nodup _ hl₁
    (fun _ x (A : Matrix (Fin n) (Fin r) ℝ) => fp.round (x / A K k))
    (fun a _ x A A' hA => by
      rw [hA K k fun h => lt_irrefl K ((hl₁mem K k).1 h).1]) S S₁).1 h₁
  -- the update loop
  have hflat := List.foldlM_foldlM_eq_foldlM_flatMap ((List.finRange n).filter (K < ·))
    (fun _ => (List.finRange r).filter (k < ·)) (fun (A : Matrix (Fin n) (Fin r) ℝ) i j => (do
      let p ← fp.round (A i k * A K j)
      let a ← fp.round (A i j - p)
      pure (A.updateRow i (Function.update (A i) j a)) : SetM _)) S₁
  beta_reduce at hflat
  rw [hflat] at h₂
  have hl₂ : ((((List.finRange n).filter (K < ·)).flatMap fun a =>
      ((List.finRange r).filter (k < ·)).map (a, ·))).Nodup :=
    List.nodup_flatMap.2 ⟨fun a _ => hndc.map fun _ _ h => (Prod.mk.inj h).2,
      hnd.imp fun {a b} hab => List.disjoint_left.2 fun {x} hxa hxb => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.1 hxa
        obtain ⟨_, _, h⟩ := List.mem_map.1 hxb
        exact hab (Prod.mk.inj h).1.symm⟩
  have hl₂mem : ∀ i j, (i, j) ∈ (((List.finRange n).filter (K < ·)).flatMap fun a =>
      ((List.finRange r).filter (k < ·)).map (a, ·)) ↔ K < i ∧ k < j := fun i j => by
    simp only [List.mem_flatMap, List.mem_map, hmem, hmemc, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, b, hb, rfl, rfl⟩; exact ⟨ha, hb⟩
    · rintro ⟨hi, hj⟩; exact ⟨i, hi, j, hj, rfl, rfl⟩
  have key := SetM.mem_run_foldlM_updateRow_update_of_nodup _ hl₂
    (fun a x (A : Matrix (Fin n) (Fin r) ℝ) => fp.round (A a.1 k * A K a.2) >>= fun p =>
      fp.round (x - p))
    (fun a _ x A A' hA => by
      rw [hA a.1 k fun h => lt_irrefl k ((hl₂mem a.1 k).1 h).2,
        hA K a.2 fun h => lt_irrefl K ((hl₂mem K a.2).1 h).1]) S₁ S'
  simp only [bind_assoc] at key
  obtain ⟨hS', hS''⟩ := key.1 h₂
  have hS'k : ∀ i, S' i k = S₁ i k := fun i => hS' i k fun h => lt_irrefl k ((hl₂mem i k).1 h).2
  have hS'r : ∀ j, S' K j = S₁ K j := fun j => hS' K j fun h => lt_irrefl K ((hl₂mem K j).1 h).1
  refine ⟨fun i j hij => ?_, fun i hi => ?_, fun i j hi hj => ?_⟩
  · rw [hS' i j fun h => hij ⟨((hl₂mem i j).1 h).1, Or.inr ((hl₂mem i j).1 h).2⟩,
      hS₁ i j fun h => hij ⟨((hl₁mem i j).1 h).1, Or.inl ((hl₁mem i j).1 h).2⟩]
  · rw [hS'k]
    exact hS₁' (i, k) ((hl₁mem i k).2 ⟨hi, rfl⟩)
  · obtain ⟨p, hp, hc⟩ := SetM.mem_run_bind.1 (hS'' (i, j) ((hl₂mem i j).2 ⟨hi, hj⟩))
    refine ⟨p, by rw [hS'k, hS'r]; exact hp, ?_⟩
    rw [← hS₁ i j fun h => hj.ne' ((hl₁mem i j).1 h).2]
    exact hc

/-- One exact step of (3.2.8), entry by entry. -/
private theorem tallOuterProductStep_exact (hrn : r ≤ n) (k : Fin r)
    (S : Matrix (Fin n) (Fin r) ℝ) :
    (∀ i j, ¬ (Fin.castLE hrn k < i ∧ (j = k ∨ k < j)) →
        Id.run (tallOuterProductStep pure hrn k S) i j = S i j) ∧
      (∀ i, Fin.castLE hrn k < i →
        Id.run (tallOuterProductStep pure hrn k S) i k = S i k / S (Fin.castLE hrn k) k) ∧
      ∀ i j, Fin.castLE hrn k < i → k < j →
        Id.run (tallOuterProductStep pure hrn k S) i j = S i j -
          Id.run (tallOuterProductStep pure hrn k S) i k *
            Id.run (tallOuterProductStep pure hrn k S) (Fin.castLE hrn k) j := by
  have hmem : Id.run (tallOuterProductStep pure hrn k S) ∈
      (tallOuterProductStep (RoundingModel.exact ℝ).round hrn k S).run := by
    rw [RoundingModel.round_exact]
    simp only [tallOuterProductStep, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
    rfl
  obtain ⟨h₁, h₂, h₃⟩ := mem_run_tallOuterProductStep hrn k hmem
  refine ⟨h₁, fun i hi => h₂ i hi, fun i j hi hj => ?_⟩
  obtain ⟨p, hp, hq⟩ := h₃ i j hi hj
  rw [RoundingModel.exact_rounds_iff] at hp hq
  rw [hq, hp]

/-- One exact step of Algorithm 3.2.1, entry by entry. -/
private theorem outerProductStep_exact (k : Fin n) (S : Matrix (Fin n) (Fin n) ℝ) :
    (∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → Id.run (outerProductStep pure k S) i j = S i j) ∧
      (∀ i, k < i → Id.run (outerProductStep pure k S) i k = S i k / S k k) ∧
      ∀ i j, k < i → k < j →
        Id.run (outerProductStep pure k S) i j = S i j -
          Id.run (outerProductStep pure k S) i k * Id.run (outerProductStep pure k S) k j := by
  have hmem : Id.run (outerProductStep pure k S) ∈
      (outerProductStep (RoundingModel.exact ℝ).round k S).run := by
    rw [RoundingModel.round_exact]
    simp only [outerProductStep, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
    rfl
  obtain ⟨h₁, h₂, h₃⟩ := mem_run_outerProductStep k hmem
  refine ⟨h₁, fun i hi => h₂ i hi, fun i j hi hj => ?_⟩
  obtain ⟨p, hp, hq⟩ := h₃ i j hi hj
  rw [RoundingModel.exact_rounds_iff] at hp hq
  rw [hq, hp]

/-- The square matrix $[A \mid [0; I]]$ that borders a tall $A \in \mathbb{R}^{n \times r}$: its
first $r$ columns are those of $A$, and its last $n - r$ columns are those of the identity. -/
private def tallBorder (A : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if h : (j : ℕ) < r then A i ⟨j, h⟩ else if i = j then 1 else 0

/-- In exact arithmetic, the steps $k < r$ of Algorithm 3.2.1 on a square matrix act on its first
$r$ columns as the steps of (3.2.8) on a tall matrix that holds these columns, and the steps
$k \ge r$ do not change these columns. -/
private theorem foldl_outerProductStep_castLE (hrn : r ≤ n) (l : List (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (T : Matrix (Fin n) (Fin r) ℝ)
    (hST : ∀ i j, S i (Fin.castLE hrn j) = T i j) (i : Fin n) (j : Fin r) :
    l.foldl (fun S k => Id.run (outerProductStep pure k S)) S i (Fin.castLE hrn j) =
      (l.filterMap fun k : Fin n => if h : (k : ℕ) < r then some (⟨k, h⟩ : Fin r) else none).foldl
        (fun T k => Id.run (tallOuterProductStep pure hrn k T)) T i j := by
  induction l generalizing S T with
  | nil => exact hST i j
  | cons k l ih =>
    rw [List.foldl_cons, List.filterMap_cons]
    obtain ⟨h₁, h₂, h₃⟩ := outerProductStep_exact k S
    by_cases hk : (k : ℕ) < r
    · rw [dite_eq_left hk]
      simp only [List.foldl_cons]
      refine ih _ _ fun i j => ?_
      set k' : Fin r := ⟨k, hk⟩
      have hkk : Fin.castLE hrn k' = k := Fin.ext rfl
      obtain ⟨g₁, g₂, g₃⟩ := tallOuterProductStep_exact hrn k' T
      rw [hkk] at g₁ g₂ g₃
      have hjk : Fin.castLE hrn j = k ↔ j = k' := by
        rw [← hkk]; exact (Fin.castLE_injective hrn).eq_iff
      have hlt : k < Fin.castLE hrn j ↔ k' < j := by
        rw [← hkk]; exact Fin.castLE_lt_castLE_iff hrn
      have hST' : ∀ i, S i k = T i k' := fun i => hkk ▸ hST i k'
      by_cases hij : k < i ∧ (Fin.castLE hrn j = k ∨ k < Fin.castLE hrn j)
      · rcases hij with ⟨hi, hj | hj⟩
        · obtain rfl : j = k' := hjk.1 hj
          rw [hkk, h₂ i hi, g₂ i hi, hST' i, hST' k]
        · rw [h₃ i _ hi hj, g₃ i j hi (hlt.1 hj), h₂ i hi, g₂ i hi,
            h₁ k _ fun h => lt_irrefl _ h.1, g₁ k j fun h => lt_irrefl _ h.1, hST, hST, hST' i,
            hST' k]
      · rw [h₁ i _ hij, g₁ i j fun h => hij ⟨h.1, h.2.imp (fun h' => hjk.2 h') hlt.2⟩, hST]
    · rw [dite_eq_right hk]
      refine ih _ _ fun i j => ?_
      have hjr : ((Fin.castLE hrn j : Fin n) : ℕ) < r := by simp
      rw [h₁ i _ fun h => ?_, hST]
      rcases h.2 with h | h
      · exact hk (by rw [← h]; exact hjr)
      · exact hk (lt_trans (Fin.lt_def.1 h) hjr)

/-- If the leading blocks of $A \in \mathbb{R}^{n \times r}$ of order at most $r$ are nonsingular,
then the strict leading principal submatrices of the bordered matrix $[A \mid [0; I]]$ are
nonsingular. -/
private theorem tallBorder_det_ne_zero (hrn : r ≤ n) {A : Matrix (Fin n) (Fin r) ℝ}
    (hA : ∀ k (hk : k ≤ r), (A.submatrix (Fin.castLE (hk.trans hrn)) (Fin.castLE hk)).det ≠ 0)
    (k : Fin n) : ((tallBorder A).strictLeadingPrincipalSubmatrix k).det ≠ 0 := by
  let e : Fin k ≃ {i : Fin n // i < k} :=
    { toFun := fun a => ⟨⟨a, by omega⟩, Fin.lt_def.2 a.2⟩
      invFun := fun i => ⟨i.1, Fin.lt_def.1 i.2⟩
      left_inv := fun a => rfl
      right_inv := fun i => rfl }
  rw [← det_submatrix_equiv_self e]
  by_cases hkr : (k : ℕ) ≤ r
  · convert hA k hkr using 2
    ext a b
    simp only [submatrix_apply, strictLeadingPrincipalSubmatrix, toBlock_apply, tallBorder, e,
      Equiv.coe_fn_mk, of_apply]
    rw [dite_eq_left (by omega)]
    rfl
  · let e₂ : Fin r ⊕ Fin (k - r) ≃ Fin k := finSumFinEquiv.trans (finCongr (by omega))
    rw [← det_submatrix_equiv_self e₂, ← fromBlocks_toBlocks (submatrix _ e₂ e₂)]
    have h₁₂ : ((((tallBorder A).strictLeadingPrincipalSubmatrix k).submatrix e e).submatrix
        e₂ e₂).toBlocks₁₂ = 0 := by
      ext a b
      simp only [toBlocks₁₂, submatrix_apply, strictLeadingPrincipalSubmatrix, toBlock_apply,
        tallBorder, e, e₂, Equiv.coe_fn_mk, of_apply, Equiv.trans_apply, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, finCongr_apply,
        Matrix.zero_apply]
      rw [dite_eq_right (by simp),
        ite_eq_right (by intro h; have := congrArg Fin.val h; simp at this; omega)]
    have h₂₂ : ((((tallBorder A).strictLeadingPrincipalSubmatrix k).submatrix e e).submatrix
        e₂ e₂).toBlocks₂₂ = 1 := by
      ext a b
      simp only [toBlocks₂₂, submatrix_apply, strictLeadingPrincipalSubmatrix, toBlock_apply,
        tallBorder, e, e₂, Equiv.coe_fn_mk, of_apply, Equiv.trans_apply,
        finSumFinEquiv_apply_right, finCongr_apply, Matrix.one_apply]
      rw [dite_eq_right (by simp)]
      by_cases hab : a = b
      · subst hab; simp
      · rw [ite_eq_right hab, ite_eq_right]
        intro h
        exact hab (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
    have h₁₁ : ((((tallBorder A).strictLeadingPrincipalSubmatrix k).submatrix e e).submatrix
        e₂ e₂).toBlocks₁₁ = A.submatrix (Fin.castLE (le_rfl.trans hrn)) (Fin.castLE le_rfl) := by
      ext a b
      simp only [toBlocks₁₁, submatrix_apply, strictLeadingPrincipalSubmatrix, toBlock_apply,
        tallBorder, e, e₂, Equiv.coe_fn_mk, of_apply, Equiv.trans_apply,
        finSumFinEquiv_apply_left, finCongr_apply]
      rw [dite_eq_left (by simp)]
      rfl
    rw [h₁₂, h₂₂, h₁₁, det_fromBlocks_zero₁₂, det_one, mul_one]
    exact hA r le_rfl

/-- **Equation (3.2.8)** of [golub2013matrix], the lower factor. For
$F \in \mathbb{R}^{n \times r}$, `tallPackedL F` is the unit lower trapezoidal
$L \in \mathbb{R}^{n \times r}$ with $\ell_{ik} = f_{ik}$ for $i > k$, $\ell_{kk} = 1$ and
$\ell_{ik} = 0$ for $i < k$. -/
def tallPackedL (F : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin n) (Fin r) ℝ :=
  of fun i k => if (k : ℕ) < i then F i k else if (i : ℕ) = k then 1 else 0

/-- **Equation (3.2.8)** of [golub2013matrix], the upper factor. For $F \in \mathbb{R}^{n \times r}$
with $r \le n$, `tallPackedU F` is the upper triangular $U \in \mathbb{R}^{r \times r}$ with
$u_{ik} = f_{ik}$ for $i \le k$ and $u_{ik} = 0$ for $i > k$: the upper triangular part of the
first $r$ rows of $F$. -/
def tallPackedU (hrn : r ≤ n) (F : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  of fun i k => if i ≤ k then F (Fin.castLE hrn i) k else 0

/-- **Equation (3.2.8)** of [golub2013matrix], exact correctness. Let
$A \in \mathbb{R}^{n \times r}$ with $r \le n$, and let $A(1{:}k, 1{:}k)$ be nonsingular for
$k = 1, \dots, r$. Then the exact output of (3.2.8) holds a rectangular LU factorization
$A = LU$, with $L \in \mathbb{R}^{n \times r}$ unit lower trapezoidal and
$U \in \mathbb{R}^{r \times r}$ upper triangular.

The factors are `GolubVanLoan.Chapter03.tallPackedL` and `GolubVanLoan.Chapter03.tallPackedU` of
the output, and the conclusion is `Matrix.IsRectLU`. The hypothesis also covers the empty block
of order $0$. The proof borders $A$ to the square matrix $[A \mid [0; I]]$, whose strict leading
principal submatrices are nonsingular. In exact arithmetic, Algorithm 3.2.1 performs the
operations of (3.2.8) on the first $r$ columns of this matrix, and its LU factorization
(`GolubVanLoan.Chapter03.algorithm_3_2_1_spec`), restricted to these columns, is $A = LU$. -/
theorem equation_3_2_8 (hrn : r ≤ n) {A : Matrix (Fin n) (Fin r) ℝ}
    (hA : ∀ k (hk : k ≤ r), (A.submatrix (Fin.castLE (hk.trans hrn)) (Fin.castLE hk)).det ≠ 0) :
    IsRectLU A (tallPackedL (Id.run (tallOuterProductLU pure hrn A)))
      (tallPackedU hrn (Id.run (tallOuterProductLU pure hrn A))) := by
  set F := Id.run (tallOuterProductLU pure hrn A) with hF
  set G := Id.run (algorithm_3_2_1 pure (tallBorder A)) with hG
  have hBA : ∀ i j, tallBorder A i (Fin.castLE hrn j) = A i j := fun i j => by
    simp [tallBorder]
  have hGF : ∀ i j, G i (Fin.castLE hrn j) = F i j := fun i j => by
    have h := foldl_outerProductStep_castLE hrn (List.finRange n) (tallBorder A) A hBA i j
    rw [List.filterMap_finRange_of_le hrn] at h
    rw [hG, hF, tallOuterProductLU_eq_foldlM, algorithm_3_2_1, List.idRun_foldlM,
      List.idRun_foldlM]
    exact h
  have hLU := algorithm_3_2_1_spec (tallBorder_det_ne_zero hrn hA)
  rw [← hG] at hLU
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hij => ?_, ?_⟩
  · simp only [tallPackedL, of_apply]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [tallPackedL, of_apply]
    rw [ite_eq_right (by omega), ite_eq_left hij]
  · simp only [tallPackedU, of_apply]
    rw [ite_eq_right (by rw [Fin.le_def]; omega)]
  · ext i j
    have h := congrFun (congrFun hLU.mul_eq i) (Fin.castLE hrn j)
    rw [hBA, Matrix.mul_apply] at h
    rw [Matrix.mul_apply, ← h]
    refine Fintype.sum_of_injective (Fin.castLE hrn) (Fin.castLE_injective hrn) _ _
      (fun t ht => ?_) (fun t => ?_)
    · have htr : r ≤ (t : ℕ) := by
        by_contra hcon
        exact ht ⟨⟨t, by omega⟩, Fin.ext rfl⟩
      rw [packedU_apply_of_lt G (Fin.lt_def.2 (by simp; omega)), mul_zero]
    · congr 1
      · simp only [tallPackedL, of_apply]
        by_cases hti : (t : ℕ) < i
        · rw [ite_eq_left hti, packedL_apply_of_lt G (Fin.lt_def.2 (by simpa using hti)), hGF]
        · rw [ite_eq_right hti]
          by_cases hit : (i : ℕ) = t
          · rw [ite_eq_left hit, show Fin.castLE hrn t = i from Fin.ext (by simp [hit]),
              packedL_apply_self]
          · rw [ite_eq_right hit, packedL_apply_of_lt' G (Fin.lt_def.2 (by simp; omega))]
      · simp only [tallPackedU, of_apply]
        by_cases htj : t ≤ j
        · rw [ite_eq_left htj, packedU_apply_of_le G ((Fin.castLE_le_castLE_iff hrn).2 htj), hGF]
        · rw [ite_eq_right htj,
            packedU_apply_of_lt G ((Fin.castLE_lt_castLE_iff hrn).2 (not_le.1 htj))]

end TallLU

/-! ### Algorithm 3.2.3: exact semantics -/

section BlockLUSpec

/-- A double loop that writes entry $(i, j)$ with a value $g_{ij}$ fixed in advance sets the listed
entries to these values and keeps the others. -/
private theorem foldl_foldl_updateEntry_const {m q : ℕ} (g : Fin m → Fin q → ℝ)
    (R : List (Fin m)) (C : List (Fin q)) (X₀ : Matrix (Fin m) (Fin q) ℝ) (i : Fin m)
    (j : Fin q) :
    R.foldl (fun (X : Matrix (Fin m) (Fin q) ℝ) i =>
        C.foldl (fun (X : Matrix (Fin m) (Fin q) ℝ) j =>
          X.updateRow i (Function.update (X i) j (g i j))) X) X₀ i j =
      if i ∈ R ∧ j ∈ C then g i j else X₀ i j :=
  congrFun (congrFun (List.foldl_foldl_update_update_eq_ite g R C X₀) i) j

/-- An LU factorization of a block matrix read on `Fin (r + s)` through `finSumFinEquiv` stays an LU
factorization after the cast of `Fin (r + s)` to `Fin n`, which is an order isomorphism. -/
private theorem isLU_reindex_finSumFinEquiv_trans {r s n : ℕ} (h : r + s = n)
    {A L U : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ}
    (hLU : IsLU (reindex finSumFinEquiv finSumFinEquiv A) (reindex finSumFinEquiv finSumFinEquiv L)
      (reindex finSumFinEquiv finSumFinEquiv U)) :
    IsLU (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) A)
      (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) L)
      (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) U) := by
  rw [← isBlockLU_id_iff, isBlockLU_reindex_iff] at hLU ⊢
  exact (isBlockLU_comp_iff (f := finCongr h) (b := id ∘ finSumFinEquiv)
    (fun a b hab => hab)).2 hLU

/-- **Algorithm 3.2.3** of [golub2013matrix], exact correctness. Let $r > 0$ and let
$A \in \mathbb{R}^{n \times n}$ with $A(1{:}k, 1{:}k)$ nonsingular for $k = 1, \dots, n-1$. Then
the exact output $(L, U)$ of the recursive block LU is the LU factorization $A = LU$, with $L$
unit lower triangular and $U$ upper triangular.

**Correction.** The source assumes only that $A$ has an LU factorization. This does not exclude
a zero pivot: $A = \begin{bmatrix} 0 & 1 \\ 0 & 1 \end{bmatrix} = \begin{bmatrix} 1 & 0 \\ 1 & 1
\end{bmatrix} \begin{bmatrix} 0 & 1 \\ 0 & 0 \end{bmatrix}$ has an LU factorization, but the
elimination divides by the pivot $a_{11} = 0$. The theorem assumes that the leading principal
submatrices of orders $1, \dots, n-1$ are nonsingular.

The proof is by strong induction on $n$. The block column is factored by (3.2.8)
(`GolubVanLoan.Chapter03.equation_3_2_8`), and $U_{12}$ solves $L_{11} U_{12} = A_{12}$
(`GolubVanLoan.Chapter03.unitForwardSubstColOn_id_eq`,
`GolubVanLoan.Chapter03.algorithm_3_1_3_spec`). The strict leading blocks of
$\tilde A = A_{22} - L_{21} U_{12}$ are nonsingular, because by (3.2.9) their determinants times
$\det U_{11}$ are those of $A$. The factors are assembled by
`GolubVanLoan.Chapter03.blockLU_of_schur`. -/
theorem algorithm_3_2_3_spec (r : ℕ) (hr : 0 < r) {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) :
    IsLU A (Id.run (algorithm_3_2_3 pure r hr n A)).1
      (Id.run (algorithm_3_2_3 pure r hr n A)).2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [algorithm_3_2_3]
  by_cases h : n ≤ r
  · rw [dite_eq_left h]
    exact algorithm_3_2_1_spec hA
  rw [dite_eq_right h]
  have hrn : r ≤ n := by omega
  have hrs : r + (n - r) = n := by omega
  set e : Fin r ⊕ Fin (n - r) ≃ Fin n := finSumFinEquiv.trans (finCongr hrs) with he
  set A₁ : Matrix (Fin n) (Fin r) ℝ := fun i k => A i (e (Sum.inl k)) with hA₁
  set F := Id.run (tallOuterProductLU pure hrn A₁) with hF
  set L₁₁ : Matrix (Fin r) (Fin r) ℝ :=
    of fun i k => if k < i then F (e (Sum.inl i)) k else if i = k then 1 else 0 with hL₁₁
  set L₂₁ : Matrix (Fin (n - r)) (Fin r) ℝ := of fun i k => F (e (Sum.inr i)) k with hL₂₁
  set U₁₁ : Matrix (Fin r) (Fin r) ℝ :=
    of fun i k => if i ≤ k then F (e (Sum.inl i)) k else 0 with hU₁₁
  set U₁₂ : Matrix (Fin r) (Fin (n - r)) ℝ := Id.run ((List.finRange (n - r)).foldlM
    (fun (U₁₂ : Matrix (Fin r) (Fin (n - r)) ℝ) c => do
      let col ← unitForwardSubstColOn pure (List.finRange r) L₁₁
        (fun i => A (e (Sum.inl i)) (e (Sum.inr c)))
      pure (U₁₂.updateCol c col)) 0) with hU₁₂
  set Ã : Matrix (Fin (n - r)) (Fin (n - r)) ℝ := Id.run ((List.finRange (n - r)).foldlM
    (fun (Ã : Matrix (Fin (n - r)) (Fin (n - r)) ℝ) i =>
      (List.finRange (n - r)).foldlM (fun (Ã : Matrix (Fin (n - r)) (Fin (n - r)) ℝ) j => do
        let a ← runningDiff pure (List.finRange r) (L₂₁ i) (fun k => U₁₂ k j)
          (A (e (Sum.inr i)) (e (Sum.inr j)))
        pure (Ã.updateRow i (Function.update (Ã i) j a))) Ã) 0) with hÃ
  set LU₂₂ := Id.run (algorithm_3_2_3 pure r hr (n - r) Ã) with hLU₂₂
  change IsLU A (reindex e e (fromBlocks L₁₁ 0 L₂₁ LU₂₂.1))
    (reindex e e (fromBlocks U₁₁ U₁₂ 0 LU₂₂.2))
  -- the blocks of `A`
  set A₁₁ : Matrix (Fin r) (Fin r) ℝ := A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl) with hA₁₁
  set A₁₂ : Matrix (Fin r) (Fin (n - r)) ℝ := A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr) with hA₁₂
  set A₂₁ : Matrix (Fin (n - r)) (Fin r) ℝ := A.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl) with hA₂₁
  set A₂₂ : Matrix (Fin (n - r)) (Fin (n - r)) ℝ := A.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
    with hA₂₂
  have hval_l : ∀ i : Fin r, ((e (Sum.inl i) : Fin n) : ℕ) = i := fun i => by simp [he]
  have hval_r : ∀ i : Fin (n - r), ((e (Sum.inr i) : Fin n) : ℕ) = r + i := fun i => by simp [he]
  -- (3.2.8) on the block column
  have hA₁det : ∀ k (hk : k ≤ r),
      (A₁.submatrix (Fin.castLE (hk.trans hrn)) (Fin.castLE hk)).det ≠ 0 := by
    intro k hk
    have hkn : k < n := by omega
    have h1 : A₁.submatrix (Fin.castLE (hk.trans hrn)) (Fin.castLE hk) =
        A.submatrix (Fin.castLE (⟨k, hkn⟩ : Fin n).isLt.le)
          (Fin.castLE (⟨k, hkn⟩ : Fin n).isLt.le) := by
      ext a b
      rfl
    rw [h1, ← det_strictLeadingPrincipalSubmatrix_castLE]
    exact hA ⟨k, hkn⟩
  have hRect := equation_3_2_8 hrn hA₁det
  rw [← hF] at hRect
  have hmul : ∀ i j, A i (e (Sum.inl j)) =
      ∑ t, tallPackedL F i t * tallPackedU hrn F t j := fun i j => by
    rw [← Matrix.mul_apply, hRect.mul_eq]
  have hL₁₁' : ∀ i t, L₁₁ i t = tallPackedL F (e (Sum.inl i)) t := fun i t => by
    simp only [hL₁₁, tallPackedL, of_apply, hval_l, Fin.lt_def, Fin.ext_iff]
  have hL₂₁' : ∀ i t, L₂₁ i t = tallPackedL F (e (Sum.inr i)) t := fun i t => by
    simp only [hL₂₁, tallPackedL, of_apply, hval_r]
    rw [ite_eq_left (by omega)]
  have hU₁₁' : U₁₁ = tallPackedU hrn F := by
    ext i k
    simp only [hU₁₁, tallPackedU, of_apply]
    congr 2
  have h₁₁mul : A₁₁ = L₁₁ * U₁₁ := by
    ext i j
    rw [hA₁₁, submatrix_apply, Function.comp_apply, Function.comp_apply, hmul, Matrix.mul_apply,
        hU₁₁']
    simp only [hL₁₁']
  have h₂₁ : A₂₁ = L₂₁ * U₁₁ := by
    ext i j
    rw [hA₂₁, submatrix_apply, Function.comp_apply, Function.comp_apply, hmul, Matrix.mul_apply,
        hU₁₁']
    simp only [hL₂₁']
  have hL₁₁unit : L₁₁.IsUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      simp only [hL₁₁, of_apply]
      rw [ite_eq_right (not_lt.2 hij'.le), ite_eq_right hij'.ne]
    · simp [hL₁₁]
  have hU₁₁upper : U₁₁.IsUpperTriangular := fun i j hij => by
    simp only [hU₁₁, of_apply]
    rw [ite_eq_right (not_le.2 (show j < i from hij))]
  have h₁₁ : IsLU A₁₁ L₁₁ U₁₁ := ⟨hL₁₁unit, hU₁₁upper, h₁₁mul.symm⟩
  -- the multiple right-hand side solve
  have hU₁₂' : ∀ i c, U₁₂ i c =
      Id.run (algorithm_3_1_3 pure L₁₁ (fun i => A (e (Sum.inl i)) (e (Sum.inr c)))) i := by
    intro i c
    rw [hU₁₂, List.idRun_foldlM]
    refine ((Matrix.foldl_updateCol_apply (fun c _ => Id.run (unitForwardSubstColOn pure
      (List.finRange r) L₁₁ (fun i => A (e (Sum.inl i)) (e (Sum.inr c)))))
      (List.nodup_finRange (n - r)) 0 i c).trans (ite_eq_left (List.mem_finRange c))).trans ?_
    rw [unitForwardSubstColOn_id_eq (L := L₁₁) (fun j _ => by rw [hL₁₁unit.diag_eq_one]),
      forwardSubstColOn_finRange]
  have h₁₂ : L₁₁ * U₁₂ = A₁₂ := by
    ext i c
    have hsol := algorithm_3_1_3_spec hL₁₁unit.isLowerTriangular
      (fun i => by rw [hL₁₁unit.diag_eq_one]; exact one_ne_zero)
      (fun i => A (e (Sum.inl i)) (e (Sum.inr c)))
    have := congrFun hsol i
    rw [mulVec, dotProduct] at this
    rw [Matrix.mul_apply, hA₁₂, submatrix_apply, Function.comp_apply, Function.comp_apply, ← this]
    simp only [hU₁₂']
  -- the Schur complement
  have hÃ' : Ã = A₂₂ - L₂₁ * U₁₂ := by
    ext i j
    rw [hÃ, List.idRun_foldlM]
    simp only [List.idRun_foldlM, Id.run_bind, Id.run_pure, runningDiff_id]
    rw [foldl_foldl_updateEntry_const (fun i j => A (e (Sum.inr i)) (e (Sum.inr j)) -
      ((List.finRange r).map fun k => L₂₁ i k * U₁₂ k j).sum),
      ite_eq_left ⟨List.mem_finRange i, List.mem_finRange j⟩]
    simp [hA₂₂, Matrix.mul_apply, Fin.sum_univ_def]
  -- the strict leading blocks of `Ã`
  have hdetU : U₁₁.det ≠ 0 := by
    have h1 := hA ⟨r, by omega⟩
    rw [det_strictLeadingPrincipalSubmatrix_castLE] at h1
    have h2 : A.submatrix (Fin.castLE (⟨r, by omega⟩ : Fin n).isLt.le)
        (Fin.castLE (⟨r, by omega⟩ : Fin n).isLt.le) = A₁₁ := by
      ext a b
      simp only [submatrix_apply, hA₁₁, Function.comp_apply]
      congr 1
    rw [h2, h₁₁mul, det_mul, h₁₁.isUnitLowerTriangular.det_eq_one, one_mul] at h1
    exact h1
  have hÃdet : ∀ k : Fin (n - r), (Ã.strictLeadingPrincipalSubmatrix k).det ≠ 0 := by
    intro k
    have hk : (k : ℕ) ≤ n - r := k.isLt.le
    have hp : r + k < n := by omega
    set c : Fin k → Fin (n - r) := Fin.castLE hk with hc
    have h9 := (equation_3_2_9 (A₂₂.submatrix c c) (A₁₂ := A₁₂.submatrix id c)
      (A₂₁ := A₂₁.submatrix c id) (L₂₁ := L₂₁.submatrix c id) (U₁₂ := U₁₂.submatrix id c)
      h₁₁mul (by rw [h₂₁]; rfl) (by rw [← h₁₂]; rfl)).1
    have hblk : (A.submatrix (Fin.castLE (⟨r + k, hp⟩ : Fin n).isLt.le)
        (Fin.castLE (⟨r + k, hp⟩ : Fin n).isLt.le)).submatrix finSumFinEquiv finSumFinEquiv =
        fromBlocks A₁₁ (A₁₂.submatrix id c) (A₂₁.submatrix c id) (A₂₂.submatrix c c) := by
      ext (a | a) (b | b) <;>
        simp only [submatrix_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
          fromBlocks_apply₂₂, hA₁₁, hA₁₂, hA₂₁, hA₂₂, Function.comp_apply, id] <;>
        congr 1
    have h1 := hA ⟨r + k, hp⟩
    rw [det_strictLeadingPrincipalSubmatrix_castLE, ← det_submatrix_equiv_self finSumFinEquiv,
      hblk, h9, det_mul, det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂,
      det_fromBlocks_zero₂₁, h₁₁.isUnitLowerTriangular.det_eq_one, det_one, det_one, one_mul,
      one_mul, one_mul, mul_one] at h1
    have h3 : A₂₂.submatrix c c - L₂₁.submatrix c id * U₁₂.submatrix id c =
        Ã.submatrix (Fin.castLE k.isLt.le) (Fin.castLE k.isLt.le) := by
      rw [hÃ']
      ext a b
      simp [Matrix.mul_apply, hc]
    rw [h3] at h1
    rw [det_strictLeadingPrincipalSubmatrix_castLE]
    exact left_ne_zero_of_mul h1
  -- assembly
  have h₂₂ : IsLU (A₂₂ - L₂₁ * U₁₂) LU₂₂.1 LU₂₂.2 := by
    rw [← hÃ']
    exact ih (n - r) (by omega) hÃdet
  have hAe : A = reindex e e (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) := by
    ext i j
    rw [reindex_apply, submatrix_apply]
    rcases hi : e.symm i with i' | i' <;> rcases hj : e.symm j with j' | j' <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, hA₁₁, hA₁₂, hA₂₁, hA₂₂, submatrix_apply, Function.comp_apply] <;>
      rw [← hi, ← hj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [hAe, he]
  exact isLU_reindex_finSumFinEquiv_trans hrs (blockLU_of_schur h₁₁ h₂₁ h₁₂ h₂₂)

end BlockLUSpec

/-! ### Algorithm 3.2.4 (Nonrecursive Block LU) -/

section NonrecursiveBlockLU

section Program

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.2.4** of [golub2013matrix] (nonrecursive block LU). Suppose that
$A \in \mathbb{R}^{n \times n}$ has an LU factorization and $r$ is a positive integer. The
algorithm computes a unit lower triangular $L \in \mathbb{R}^{n \times n}$ and an upper
triangular $U \in \mathbb{R}^{n \times n}$ with $A = LU$.
```
for k = 1:N
    Rectangular Gaussian elimination:  [A_kk; …; A_Nk] = [L_kk; …; L_Nk] U_kk
    Multiple right hand side solve:    L_kk [U_{k,k+1} | … | U_kN] = [A_{k,k+1} | … | A_kN]
    Level-3 updates:                   A_ij = A_ij - L_ik U_kj,  i = k+1:N, j = k+1:N
end
```
Here $n = Nr$, and block $k$ consists of $r$ consecutive indices: the block of an index $i$ is
`i.divNat`. The program overwrites $A$ in place, and its blocks are index lists of the full
matrix. The rectangular elimination (3.2.8) of the block column is, for each pivot $p$ of block
$k$, the outer product step of Algorithm 3.2.1 with its update restricted to the columns of
block $k$. The multiple right-hand side solve is the unit lower triangular solve
`GolubVanLoan.Chapter03.unitForwardSubstColOn` on the rows of block $k$, column by column,
against the unit lower triangular $L_{kk}$ stored below the diagonal of $A_{kk}$. The level-3
update computes each entry $a_{ij} - L_{ik}(i, :) \cdot U_{kj}(:, j)$ as a running difference
over the indices of block $k$.

The source writes $n = Nr$ "for clarity". The unit solve is Algorithm 3.1.3 without the division
by the unit diagonal, and the running differences (`FloatingPoint.runningDiff`) follow the order
of (3.1.4). The factors are read from the output by `GolubVanLoan.Chapter03.packedL` and
`GolubVanLoan.Chapter03.packedU`. -/
noncomputable def algorithm_3_2_4 {N r : ℕ} (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) :
    M (Matrix (Fin (N * r)) (Fin (N * r)) ℝ) :=
  (List.finRange N).foldlM (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) k => do
    -- rectangular Gaussian elimination on the block column `A(k:N, k)`
    let A ← ((List.finRange (N * r)).filter fun i => i.divNat = k).foldlM
      (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) p => do
        let A ← ((List.finRange (N * r)).filter (p < ·)).foldlM
          (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i => do
            let l ← rnd (A i p / A p p)
            pure (A.updateRow i (Function.update (A i) p l))) A
        ((List.finRange (N * r)).filter (p < ·)).foldlM
          (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
            ((List.finRange (N * r)).filter fun j => j.divNat = k ∧ p < j).foldlM
              (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) j => do
                let q ← rnd (A i p * A p j)
                let a ← rnd (A i j - q)
                pure (A.updateRow i (Function.update (A i) j a))) A) A) A
    -- multiple right-hand side solve with the unit lower triangular `L_kk`
    let A ← ((List.finRange (N * r)).filter fun c => k < c.divNat).foldlM
      (fun (B : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) c => do
        let x ← unitForwardSubstColOn rnd ((List.finRange (N * r)).filter fun i => i.divNat = k)
          (of fun i j => if j < i then A i j else if i = j then 1 else 0) fun i => B i c
        pure (B.updateCol c x)) A
    -- level-3 updates
    ((List.finRange (N * r)).filter fun i => k < i.divNat).foldlM
      (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
        ((List.finRange (N * r)).filter fun j => k < j.divNat).foldlM
          (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) j => do
            let a ← runningDiff rnd ((List.finRange (N * r)).filter fun t => t.divNat = k) (A i)
              (fun t => A t j) (A i j)
            pure (A.updateRow i (Function.update (A i) j a))) A) A) A

end Program

section Exact

variable {n : ℕ}

/-- The trailing values after the pivots below $P$: $a_{ij} - \sum_{t < P} \ell_{it} u_{tj}$. -/
private def schurRest (A L U : Matrix (Fin n) (Fin n) ℝ) (P : ℕ) (i j : Fin n) : ℝ :=
  A i j - ∑ t : Fin n, if (t : ℕ) < P then L i t * U t j else 0

/-- The factors $L$ and $U$ packed in one matrix: $U$ on and above the diagonal, $L$ below it. -/
private def packLU (L U : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if j < i then L i j else U i j

section Schur

variable {A L U : Matrix (Fin n) (Fin n) ℝ} (hLU : IsLU A L U)
include hLU

private theorem schurRest_eq (P : ℕ) (i j : Fin n) :
    schurRest A L U P i j = ∑ t : Fin n, if P ≤ (t : ℕ) then L i t * U t j else 0 := by
  rw [schurRest, ← hLU.mul_eq, Matrix.mul_apply, sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : (t : ℕ) < P
  · rw [ite_eq_right (by omega), ite_eq_left h, zero_add]
  · rw [ite_eq_left (by omega), ite_eq_right h, add_zero]

private theorem schurRest_row (p j : Fin n) : schurRest A L U p p j = U p j := by
  rw [schurRest_eq hLU, Finset.sum_eq_single p]
  · rw [ite_eq_left le_rfl, hLU.isUnitLowerTriangular.diag_eq_one, one_mul]
  · intro t _ htp
    by_cases h : (p : ℕ) ≤ t
    · rw [ite_eq_left h, hLU.isUnitLowerTriangular.isLowerTriangular
        (OrderDual.toDual_lt_toDual.2 (lt_of_le_of_ne (Fin.le_def.2 h) (Ne.symm htp))),
        zero_mul]
    · rw [ite_eq_right h]
  · simp

private theorem schurRest_col (p i : Fin n) : schurRest A L U p i p = L i p * U p p := by
  rw [schurRest_eq hLU, Finset.sum_eq_single p]
  · rw [ite_eq_left le_rfl]
  · intro t _ htp
    by_cases h : (p : ℕ) ≤ t
    · rw [ite_eq_left h, hLU.isUpperTriangular
        (show p < t from lt_of_le_of_ne (Fin.le_def.2 h) (Ne.symm htp)), mul_zero]
    · rw [ite_eq_right h]
  · simp

omit hLU in
private theorem schurRest_succ (p : Fin n) (i j : Fin n) :
    schurRest A L U (p + 1) i j = schurRest A L U p i j - L i p * U p j := by
  rw [schurRest, schurRest, sub_sub, ← Finset.sum_erase_add _ _ (Finset.mem_univ p),
    ← Finset.sum_erase_add (s := Finset.univ) (a := p) _ (Finset.mem_univ p),
    ite_eq_left (Nat.lt_succ_self _), ite_eq_right (lt_irrefl _), add_zero]
  congr 2
  refine Finset.sum_congr rfl fun t ht => ?_
  have htp : (t : ℕ) ≠ p := fun h => (Finset.mem_erase.1 ht).1 (Fin.ext h)
  by_cases h : (t : ℕ) < p
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

end Schur

/-! ### Loops of Algorithm 3.2.4 in exact arithmetic -/

/-- The division loop of the block column elimination divides the listed rows of column $p$ by the
pivot $s_{pp}$ and keeps every other entry. -/
private theorem foldl_divCol_apply (p : Fin n) {R : List (Fin n)} (hR : R.Nodup) (hpR : p ∉ R)
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    R.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
        S.updateRow i (Function.update (S i) p (S i p / S p p))) S i j =
      if j = p ∧ i ∈ R then S i p / S p p else S i j := by
  have hh : ∀ y y' : Fin n → Fin n → ℝ, (∀ a b, ¬ (a ∈ R ∧ b ∈ [p]) → y a b = y' a b) →
      ∀ i ∈ R, ∀ j ∈ [p], y i j = y' i j → y i p / y p p = y' i p / y' p p := by
    intro y y' hy i _ j hj hij
    obtain rfl := List.mem_singleton.1 hj
    rw [hij, hy j j fun h => hpR h.1]
  refine (congrFun (congrFun (List.foldl_foldl_update_update_of_nodup hR (List.nodup_singleton p)
    (fun S i _ => S i p / S p p) hh S) i) j).trans ?_
  simp only [List.mem_singleton, and_comm]

/-- A double loop that subtracts from each listed entry $(i, j)$ a quantity $g(S)_{ij}$ that reads
only entries outside the listed block writes every listed entry once, from its initial value. -/
private theorem foldl_foldl_sub_apply {R C : List (Fin n)} (hR : R.Nodup) (hC : C.Nodup)
    (g : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n → ℝ)
    (hg : ∀ S S' : Matrix (Fin n) (Fin n) ℝ, (∀ a b, ¬ (a ∈ R ∧ b ∈ C) → S a b = S' a b) →
      ∀ i j, g S i j = g S' i j)
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    R.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
        C.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) j =>
        S.updateRow i (Function.update (S i) j (S i j - g S i j))) S) S i j =
      if i ∈ R ∧ j ∈ C then S i j - g S i j else S i j :=
  congrFun (congrFun (List.foldl_foldl_update_update_of_nodup hR hC (fun S i j => S i j - g S i j)
    (fun y y' hy i _ j _ hij => by rw [hij, hg y y' hy]) S) i) j

/-- Two solutions of the same lower triangular system on a sorted index list agree on the list: if
$\sum_{j \in o} \ell_{ij} y_j = \sum_{j \in o} \ell_{ij} z_j$ for all $i \in o$ and
$\ell_{ii} \neq 0$ on $o$, then $y_i = z_i$ for all $i \in o$. -/
private theorem eq_on_of_sum_eq {o : List (Fin n)} (ho : o.Pairwise (· < ·))
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular) (hd : ∀ i ∈ o, L i i ≠ 0)
    {y z : Fin n → ℝ}
    (h : ∀ i ∈ o, (o.map fun j => L i j * y j).sum = (o.map fun j => L i j * z j).sum) :
    ∀ i ∈ o, y i = z i := by
  have hnd : o.Nodup := ho.imp ne_of_lt
  suffices H : ∀ m : ℕ, ∀ i ∈ o, (i : ℕ) = m → y i = z i from fun i hi => H i i hi rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro i hi him
  have key : ∑ j ∈ o.toFinset, L i j * (y j - z j) = 0 := by
    rw [Finset.sum_congr rfl fun j _ => mul_sub (L i j) (y j) (z j), Finset.sum_sub_distrib,
      List.sum_toFinset _ hnd, List.sum_toFinset _ hnd, h i hi, sub_self]
  rw [Finset.sum_eq_single i] at key
  · exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (hd i hi))
  · intro j hj hji
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · rw [ih j (him ▸ Fin.lt_def.1 hlt) j (List.mem_toFinset.1 hj) rfl, sub_self, mul_zero]
    · rw [hL (OrderDual.toDual_lt_toDual.2 hgt), zero_mul]
  · intro h
    exact absurd (List.mem_toFinset.2 hi) h

/-- One pivot $p$ of the block column elimination of Algorithm 3.2.4, in exact arithmetic: if the
columns of the block hold the finished factors where $\min(i, j) < p$ and the trailing values
$a_{ij} - \sum_{t < p} \ell_{it} u_{tj}$ elsewhere, then after the division and the update
restricted to the block they do so with $p + 1$, and the other columns are not changed. -/
private theorem elimStep {A L U : Matrix (Fin n) (Fin n) ℝ} (hLU : IsLU A L U)
    (hpiv : ∀ p i : Fin n, p < i → U p p ≠ 0) (B : Fin n → Prop) [DecidablePred B] (p : Fin n)
    (hp : B p) (S₀ E : Matrix (Fin n) (Fin n) ℝ)
    (hE : ∀ i j, E i j = if B j then (if ((min i j : Fin n) : ℕ) < p then packLU L U i j
      else schurRest A L U p i j) else S₀ i j) (i j : Fin n) :
    ((List.finRange n).filter (p < ·)).foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
        ((List.finRange n).filter fun j => B j ∧ p < j).foldl
          (fun (S : Matrix (Fin n) (Fin n) ℝ) j =>
            S.updateRow i (Function.update (S i) j (S i j - S i p * S p j))) S)
      (((List.finRange n).filter (p < ·)).foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
        S.updateRow i (Function.update (S i) p (S i p / S p p))) E) i j =
    if B j then (if ((min i j : Fin n) : ℕ) < p + 1 then packLU L U i j
      else schurRest A L U (p + 1) i j) else S₀ i j := by
  set R := (List.finRange n).filter (p < ·) with hR
  set C := (List.finRange n).filter fun j => B j ∧ p < j with hC
  have hmemR : ∀ i, i ∈ R ↔ p < i := fun i => by simp [hR]
  have hmemC : ∀ j, j ∈ C ↔ B j ∧ p < j := fun j => by simp [hC]
  have hpR : p ∉ R := fun h => lt_irrefl p ((hmemR p).1 h)
  have hpC : p ∉ C := fun h => lt_irrefl p ((hmemC p).1 h).2
  set E₁ := R.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
    S.updateRow i (Function.update (S i) p (S i p / S p p))) E with hE₁def
  have hE₁ : ∀ i j, E₁ i j = if j = p ∧ i ∈ R then E i p / E p p else E i j := fun i j =>
    foldl_divCol_apply p ((List.nodup_finRange n).filter _) hpR E i j
  rw [foldl_foldl_sub_apply ((List.nodup_finRange n).filter _) ((List.nodup_finRange n).filter _)
    (fun S i j => S i p * S p j) (fun S S' hSS' i j => by
      rw [hSS' i p fun h => hpC h.2, hSS' p j fun h => hpR h.1]) E₁ i j]
  -- the entries of `E` the step reads
  have hEpp : E p p = U p p := by
    rw [hE, ite_eq_left hp, ite_eq_right (by simp), schurRest_row hLU]
  have hEip : ∀ i, p < i → E i p = L i p * U p p := fun i hi => by
    rw [hE, ite_eq_left hp, ite_eq_right (by simp [Fin.val_min, le_of_lt (Fin.lt_def.1 hi)]),
      schurRest_col hLU]
  have hEpj : ∀ j, B j → p ≤ j → E p j = U p j := fun j hj hpj => by
    rw [hE, ite_eq_left hj, ite_eq_right (by simp [Fin.val_min, Fin.le_def.1 hpj]),
      schurRest_row hLU]
  have hE₁ip : ∀ i, p < i → E₁ i p = L i p := fun i hi => by
    rw [hE₁, ite_eq_left ⟨rfl, (hmemR i).2 hi⟩, hEip i hi, hEpp,
      mul_div_cancel_right₀ _ (hpiv p i hi)]
  by_cases hij : i ∈ R ∧ j ∈ C
  · rw [ite_eq_left hij]
    have hi := (hmemR i).1 hij.1
    obtain ⟨hBj, hj⟩ := (hmemC j).1 hij.2
    have hi' := Fin.lt_def.1 hi
    have hj' := Fin.lt_def.1 hj
    have hmin : ¬ ((min i j : Fin n) : ℕ) < p + 1 := by
      simp only [Fin.val_min]; omega
    have hEij : E i j = schurRest A L U p i j := by
      rw [hE, ite_eq_left hBj, ite_eq_right (by simp only [Fin.val_min]; omega)]
    have hE₁ij : E₁ i j = schurRest A L U p i j := by
      rw [hE₁, ite_eq_right (fun h => ne_of_gt hj h.1), hEij]
    have hE₁pj : E₁ p j = U p j := by
      rw [hE₁, ite_eq_right (fun h => hpR h.2), hEpj j hBj hj.le]
    rw [hE₁ij, hE₁ip i hi, hE₁pj, ite_eq_left hBj, ite_eq_right hmin, schurRest_succ]
  · rw [ite_eq_right hij, hE₁]
    by_cases hjp : j = p ∧ i ∈ R
    · rw [ite_eq_left hjp]
      obtain ⟨rfl, hi⟩ := hjp
      have hi' := (hmemR i).1 hi
      have hi'' := Fin.lt_def.1 hi'
      rw [hEip i hi', hEpp, mul_div_cancel_right₀ _ (hpiv j i hi'), ite_eq_left hp,
        ite_eq_left (by simp only [Fin.val_min]; omega)]
      simp only [packLU, of_apply]
      rw [ite_eq_left hi']
    · rw [ite_eq_right hjp, hE]
      by_cases hBj : B j
      · simp only [hBj, ↓reduceIte]
        by_cases hlt : ((min i j : Fin n) : ℕ) < p
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt]
          have hmin : ((min i j : Fin n) : ℕ) = p := by
            by_contra hne
            have hgt : (p : ℕ) < i ∧ (p : ℕ) < j := by
              simp only [Fin.val_min] at hlt hne; omega
            exact hij ⟨(hmemR i).2 (Fin.lt_def.2 hgt.1),
              (hmemC j).2 ⟨hBj, Fin.lt_def.2 hgt.2⟩⟩
          rw [ite_eq_left (by omega)]
          by_cases hip : (i : ℕ) = p
          · obtain rfl : i = p := Fin.ext hip
            have hij' : (i : ℕ) ≤ j := by simp only [Fin.val_min] at hmin; omega
            rw [schurRest_row hLU]
            simp only [packLU, of_apply]
            rw [ite_eq_right (not_lt.2 (Fin.le_def.2 hij'))]
          · exfalso
            simp only [Fin.val_min] at hmin
            exact hjp ⟨Fin.ext (by omega), (hmemR i).2 (Fin.lt_def.2 (by omega))⟩
      · simp only [hBj, ↓reduceIte]

/-- Removing the pivots of one block from the trailing values: the trailing values after $K + r$
pivots are those after $K$ pivots minus $\sum_{t} \ell_{it} u_{tj}$ over the indices $t$ of the
block $K \le t < K + r$. -/
private theorem schurRest_add_block {A L U : Matrix (Fin n) (Fin n) ℝ} (K r : ℕ)
    (B : Fin n → Prop) [DecidablePred B] (hB : ∀ t : Fin n, B t ↔ K ≤ (t : ℕ) ∧ (t : ℕ) < K + r)
    (i j : Fin n) :
    schurRest A L U (K + r) i j =
      schurRest A L U K i j - ∑ t : Fin n, if B t then L i t * U t j else 0 := by
  rw [schurRest, schurRest, sub_sub, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h1 : (t : ℕ) < K
  · rw [ite_eq_left (by omega), ite_eq_left h1, ite_eq_right (by rw [hB]; omega), add_zero]
  · by_cases h2 : (t : ℕ) < K + r
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left (by rw [hB]; omega), zero_add]
    · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (by rw [hB]; omega), add_zero]

/-- **Algorithm 3.2.4** of [golub2013matrix], exact correctness. Let $n = Nr$ and let
$A \in \mathbb{R}^{n \times n}$ with $A(1{:}k, 1{:}k)$ nonsingular for $k = 1, \dots, n-1$. In
exact arithmetic, the factors $L$ and $U$ stored in the output of the nonrecursive block LU form
the LU factorization $A = LU$, with $L$ unit lower triangular and $U$ upper triangular.

**Correction.** The source assumes only that $A$ has an LU factorization, which does not exclude
a zero pivot (see `GolubVanLoan.Chapter03.algorithm_3_2_3_spec`). The theorem assumes that the
leading principal submatrices of orders $1, \dots, n-1$ are nonsingular.

The factors are `GolubVanLoan.Chapter03.packedL` and `GolubVanLoan.Chapter03.packedU` of the
output. The proof uses an invariant over the block steps: after the blocks before $k$, the
entries with $\min(i, j) < kr$ hold the finished factors, and the other entries hold
$a_{ij} - \sum_{t < kr} \ell_{it} u_{tj}$, the Schur complement of the leading block of order
$kr$ (`GolubVanLoan.Chapter03.equation_3_2_9`). Within a step, the block column is finished
pivot by pivot, the block row by the unit lower triangular solve, whose solution is unique, and
the trailing block receives the contributions of the block. -/
theorem algorithm_3_2_4_spec {N r : ℕ} {A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ}
    (hA : ∀ k : Fin (N * r), (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) :
    IsLU A (packedL (Id.run (algorithm_3_2_4 pure A)))
      (packedU (Id.run (algorithm_3_2_4 pure A))) := by
  obtain ⟨L, U, hLU⟩ := exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix (A := A)
    fun k => (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))
  have hpiv : ∀ p i : Fin (N * r), p < i → U p p ≠ 0 := fun p i hpi =>
    hLU.diag_upper_ne_zero_of_lt ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA i))) hpi
  have hLlow : ∀ i j : Fin (N * r), i < j → L i j = 0 := fun i j h =>
    hLU.isUnitLowerTriangular.isLowerTriangular (OrderDual.toDual_lt_toDual.2 h)
  have hpL : packedL (packLU L U) = L := by
    ext i j
    rcases lt_trichotomy j i with h | rfl | h
    · rw [packedL_apply_of_lt _ h]
      simp only [packLU, of_apply]
      rw [ite_eq_left h]
    · rw [packedL_apply_self, hLU.isUnitLowerTriangular.diag_eq_one]
    · rw [packedL_apply_of_lt' _ h, hLlow i j h]
  have hpU : packedU (packLU L U) = U := by
    ext i j
    by_cases h : i ≤ j
    · rw [packedU_apply_of_le _ h]
      simp only [packLU, of_apply]
      rw [ite_eq_right (not_lt.2 h)]
    · rw [packedU_apply_of_lt _ (not_le.1 h), hLU.isUpperTriangular (not_le.1 h)]
  suffices hout : Id.run (algorithm_3_2_4 pure A) = packLU L U by
    rw [hout, hpL, hpU]
    exact hLU
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  · subst hr0
    ext i j
    exact absurd i.isLt (by simp)
  set T := packLU L U with hT
  -- the program in exact arithmetic
  set Elim : Fin N → Matrix (Fin (N * r)) (Fin (N * r)) ℝ → Matrix (Fin (N * r)) (Fin (N * r)) ℝ :=
    fun k S => ((List.finRange (N * r)).filter fun i => i.divNat = k).foldl
      (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) p =>
        ((List.finRange (N * r)).filter (p < ·)).foldl
          (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
            ((List.finRange (N * r)).filter fun j => j.divNat = k ∧ p < j).foldl
              (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) j =>
                S.updateRow i (Function.update (S i) j (S i j - S i p * S p j))) S)
          (((List.finRange (N * r)).filter (p < ·)).foldl
            (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
              S.updateRow i (Function.update (S i) p (S i p / S p p))) S)) S with hElim
  set Y : Fin N → Matrix (Fin (N * r)) (Fin (N * r)) ℝ → (Fin (N * r) → ℝ) → Fin (N * r) → ℝ :=
    fun k E v => Id.run (unitForwardSubstColOn pure
      ((List.finRange (N * r)).filter fun i => i.divNat = k)
      (of fun i j => if j < i then E i j else if i = j then 1 else 0) v) with hY
  set Solve : Fin N → Matrix (Fin (N * r)) (Fin (N * r)) ℝ →
      Matrix (Fin (N * r)) (Fin (N * r)) ℝ :=
    fun k E => ((List.finRange (N * r)).filter fun c => k < c.divNat).foldl
      (fun (B : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) c => B.updateCol c (Y k E fun i => B i c))
      E with hSolve
  set Upd : Fin N → Matrix (Fin (N * r)) (Fin (N * r)) ℝ → Matrix (Fin (N * r)) (Fin (N * r)) ℝ :=
    fun k X => ((List.finRange (N * r)).filter fun i => k < i.divNat).foldl
      (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
        ((List.finRange (N * r)).filter fun j => k < j.divNat).foldl
          (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) j =>
            S.updateRow i (Function.update (S i) j (S i j -
              (((List.finRange (N * r)).filter fun t => t.divNat = k).map
                fun t => S i t * S t j).sum))) S) X with hUpd
  have hprog : Id.run (algorithm_3_2_4 pure A) =
      (List.finRange N).foldl (fun S k => Upd k (Solve k (Elim k S))) A := by
    simp only [algorithm_3_2_4, List.idRun_foldlM, Id.run_bind, Id.run_pure, pure_bind,
      runningDiff_id, hElim, hSolve, hUpd, hY]
  rw [hprog]
  have key := List.foldl_prefix_induction (l := List.finRange N) (b := A)
    (fun S k => Upd k (Solve k (Elim k S)))
    (fun (pre : List (Fin N)) (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) => ∀ i j,
      S i j = if (min i j).divNat ∈ pre then T i j else
        A i j - ∑ t : Fin (N * r), if t.divNat ∈ pre then L i t * U t j else 0)
    (fun i j => by simp) ?_
  · ext i j
    simpa using key i j
  rintro pre x post hpq S hS
  set K : ℕ := (x : ℕ) * r with hK
  have hsorted : (pre ++ x :: post).Pairwise (· < ·) := hpq ▸ (List.sortedLT_finRange N).pairwise
  have hblk : ∀ t : Fin (N * r), t.divNat = x ↔ K ≤ (t : ℕ) ∧ (t : ℕ) < K + r := fun t => by
    rw [Fin.ext_iff, Fin.coe_divNat, Nat.div_eq_iff hr]
    omega
  have hlat : ∀ t : Fin (N * r), x < t.divNat ↔ K + r ≤ (t : ℕ) := fun t => by
    rw [Fin.lt_def, Fin.coe_divNat, ← Nat.succ_le_iff, Nat.le_div_iff_mul_le hr, Nat.succ_mul]
  have hmem : ∀ t : Fin (N * r), t.divNat ∈ pre ↔ (t : ℕ) < K := fun t => by
    constructor
    · intro h
      have hlt : t.divNat < x := (List.pairwise_append.1 hsorted).2.2 _ h x List.mem_cons_self
      rw [Fin.lt_def, Fin.coe_divNat, Nat.div_lt_iff_lt_mul hr] at hlt
      exact hlt
    · intro h
      have hlt : t.divNat < x := by
        rw [Fin.lt_def, Fin.coe_divNat, Nat.div_lt_iff_lt_mul hr]
        exact h
      exact List.mem_prefix_of_pairwise (List.sortedLT_finRange N).pairwise hpq
        (List.mem_finRange _) (ne_of_lt hlt) (not_lt.2 hlt.le)
  have hmem' : ∀ t : Fin (N * r), t.divNat ∈ pre ++ [x] ↔ (t : ℕ) < K + r := fun t => by
    rw [List.mem_append, List.mem_singleton, hmem, hblk]
    omega
  have hS' : ∀ i j, S i j = if ((min i j : Fin (N * r)) : ℕ) < K then T i j else
      schurRest A L U K i j := fun i j => by
    rw [hS i j]
    simp only [hmem, schurRest]
  -- phase 1: the block column elimination
  have hbks : ((List.finRange (N * r)).filter fun i => i.divNat = x).Pairwise (· < ·) :=
    (List.sortedLT_finRange _).pairwise.filter _
  have hE : ∀ i j, Elim x S i j = if j.divNat = x then T i j else S i j := by
    have key1 := List.foldl_prefix_induction
      (l := (List.finRange (N * r)).filter fun i => i.divNat = x) (b := S)
      (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) p =>
        ((List.finRange (N * r)).filter (p < ·)).foldl
          (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
            ((List.finRange (N * r)).filter fun j => j.divNat = x ∧ p < j).foldl
              (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) j =>
                S.updateRow i (Function.update (S i) j (S i j - S i p * S p j))) S)
          (((List.finRange (N * r)).filter (p < ·)).foldl
            (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
              S.updateRow i (Function.update (S i) p (S i p / S p p))) S))
      (fun (pre' : List (Fin (N * r))) (E : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) => ∀ i j,
        E i j = if j.divNat = x then
          (if ((min i j : Fin (N * r)) : ℕ) < K ∨ min i j ∈ pre' then T i j else
            A i j - ∑ t : Fin (N * r), if (t : ℕ) < K ∨ t ∈ pre' then L i t * U t j else 0)
          else S i j)
      (fun i j => by
        rw [hS' i j]
        by_cases hj : j.divNat = x <;> simp [hj, schurRest]) ?_
    · intro i j
      rw [hElim]
      simp only
      rw [key1 i j]
      by_cases hj : j.divNat = x
      · rw [ite_eq_left hj, ite_eq_left hj, ite_eq_left]
        by_cases hmK : ((min i j : Fin (N * r)) : ℕ) < K
        · exact Or.inl hmK
        · refine Or.inr (List.mem_filter.2 ⟨List.mem_finRange _, decide_eq_true ?_⟩)
          have hjb := (hblk j).1 hj
          rw [hblk]
          simp only [Fin.val_min] at hmK ⊢
          omega
      · rw [ite_eq_right hj, ite_eq_right hj]
    rintro pre' p post' hpq' E hE'
    have hpb : p ∈ (List.finRange (N * r)).filter fun i => i.divNat = x := by
      rw [hpq']; exact List.mem_append.2 (Or.inr List.mem_cons_self)
    have hp : p.divNat = x := by simpa using hpb
    have hpK := (hblk p).1 hp
    have hmemp : ∀ t : Fin (N * r), ((t : ℕ) < K ∨ t ∈ pre') ↔ (t : ℕ) < p := fun t => by
      constructor
      · rintro (h | h)
        · omega
        · exact Fin.lt_def.1 ((List.pairwise_append.1 (hpq' ▸ hbks)).2.2 _ h p
            List.mem_cons_self)
      · intro h
        by_cases htK : (t : ℕ) < K
        · exact Or.inl htK
        · refine Or.inr (List.mem_prefix_of_pairwise hbks hpq' ?_ (fun e => by subst e; omega)
            (fun h' => by have := Fin.lt_def.1 h'; omega))
          exact List.mem_filter.2 ⟨List.mem_finRange _, decide_eq_true ((hblk t).2 (by omega))⟩
    have hmemp' : ∀ t : Fin (N * r), ((t : ℕ) < K ∨ t ∈ pre' ++ [p]) ↔ (t : ℕ) < p + 1 :=
      fun t => by
        rw [List.mem_append, List.mem_singleton, ← or_assoc, hmemp, Fin.ext_iff]
        omega
    have hEn : ∀ i j, E i j = if j.divNat = x then
        (if ((min i j : Fin (N * r)) : ℕ) < p then T i j else schurRest A L U p i j)
        else S i j := fun i j => by
      rw [hE' i j]
      simp only [hmemp, schurRest]
    intro i j
    rw [elimStep hLU hpiv (fun j => j.divNat = x) p hp S E hEn i j]
    simp only [hmemp', schurRest, ← hT]
  -- phase 2: the multiple right-hand side solve
  set E := Elim x S with hEdef
  have hbk : ∀ t, t ∈ (List.finRange (N * r)).filter (fun i => i.divNat = x) ↔ t.divNat = x :=
    fun t => by simp
  have hlatm : ∀ t, t ∈ (List.finRange (N * r)).filter (fun i => x < i.divNat) ↔ x < t.divNat :=
    fun t => by simp
  have hLk : ∀ i j, i.divNat = x → j.divNat = x →
      (of fun i j => if j < i then E i j else if i = j then 1 else 0 :
        Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i j = L i j := fun i j hi hj => by
    simp only [of_apply]
    rcases lt_trichotomy j i with h | rfl | h
    · rw [ite_eq_left h, hE, ite_eq_left hj]
      simp only [hT, packLU, of_apply]
      rw [ite_eq_left h]
    · rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, hLU.isUnitLowerTriangular.diag_eq_one]
    · rw [ite_eq_right (not_lt.2 h.le), ite_eq_right (ne_of_lt h), hLlow i j h]
  have hYc : ∀ c, x < c.divNat → ∀ i, Y x E (fun i => E i c) i =
      if i.divNat = x then U i c else E i c := by
    intro c hc i
    have hLkl : (of fun i j => if j < i then E i j else if i = j then 1 else 0 :
        Matrix (Fin (N * r)) (Fin (N * r)) ℝ).IsLowerTriangular := fun a b hab => by
      have hab' : a < b := OrderDual.toDual_lt_toDual.1 hab
      simp only [of_apply]
      rw [ite_eq_right (not_lt.2 hab'.le), ite_eq_right (ne_of_lt hab')]
    rw [hY]
    simp only
    rw [unitForwardSubstColOn_id_eq
      (L := of fun i j => if j < i then E i j else if i = j then 1 else 0) (fun a _ => by simp)]
    obtain ⟨h₁, h₂⟩ := forwardSubstColOn_exact hbks hLkl (fun a _ => by simp)
      (fun i => E i c)
    by_cases hi : i.divNat = x
    · rw [ite_eq_left hi]
      refine eq_on_of_sum_eq (y := Id.run (forwardSubstColOn pure
        ((List.finRange (N * r)).filter fun i => i.divNat = x)
        (of fun i j => if j < i then E i j else if i = j then 1 else 0) fun i => E i c))
        (z := fun j => U j c) hbks hLkl
        (fun a _ => by simp) (fun a ha => ?_) i ((hbk i).2 hi)
      refine (h₂ a ha).trans ?_
      have ha' := (hbk a).1 ha
      have hac : a < c := Fin.lt_def.2 (by have := (hblk a).1 ha'; have := (hlat c).1 hc; omega)
      rw [List.map_congr_left fun j hj => by rw [hLk a j ha' ((hbk j).1 hj)],
        List.sum_map_filter_finRange (fun j => j.divNat = x), Finset.sum_filter, hE,
        ite_eq_right (by intro h; rw [h] at hc; exact lt_irrefl x hc), hS', ite_eq_right (by
            simp only [Fin.val_min]; have := (hblk a).1 ha'; have := Fin.lt_def.1 hac; omega),
        schurRest_eq hLU]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : t.divNat = x
      · rw [ite_eq_left ht, ite_eq_left ((hblk t).1 ht).1]
      · rw [ite_eq_right ht]
        by_cases hKt : K ≤ (t : ℕ)
        · rw [ite_eq_left hKt, hLlow a t (Fin.lt_def.2 (by
            have := (hblk a).1 ha'; rw [hblk] at ht; omega)), zero_mul]
        · rw [ite_eq_right hKt]
    · rw [ite_eq_right hi]
      exact h₁ i fun h => hi ((hbk i).1 h)
  have hX : ∀ i c, Solve x E i c =
      if x < c.divNat ∧ i.divNat = x then U i c else E i c := fun i c => by
    rw [hSolve]
    simp only
    rw [Matrix.foldl_updateCol_apply (fun _ => Y x E) ((List.nodup_finRange _).filter _)]
    by_cases hc : x < c.divNat
    · rw [ite_eq_left ((hlatm c).2 hc), hYc c hc i]
      by_cases hi : i.divNat = x
      · rw [ite_eq_left hi, ite_eq_left ⟨hc, hi⟩]
      · rw [ite_eq_right hi, ite_eq_right (by intro h; exact hi h.2)]
    · rw [ite_eq_right (by intro h; exact hc ((hlatm c).1 h)),
        ite_eq_right (by intro h; exact hc h.1)]
  -- phase 3: the level-3 update
  set X := Solve x E with hXdef
  intro i j
  rw [hUpd]
  beta_reduce
  rw [foldl_foldl_sub_apply ((List.nodup_finRange _).filter _) ((List.nodup_finRange _).filter _)
    (fun S i j => (((List.finRange (N * r)).filter fun t => t.divNat = x).map
      fun t => S i t * S t j).sum) (fun S S' hSS' i j => by
        congr 1
        refine List.map_congr_left fun t ht => ?_
        have ht' := (hbk t).1 ht
        have htl : ¬ x < t.divNat := by rw [ht']; exact lt_irrefl x
        rw [hSS' i t fun h => htl ((hlatm t).1 h.2), hSS' t j fun h => htl ((hlatm t).1 h.1)])]
  simp only [hmem', hlatm]
  change _ = if _ then T i j else schurRest A L U (K + r) i j
  have hXbk : ∀ i t, t.divNat = x → X i t = E i t := fun i t ht => by
    rw [hX, ite_eq_right (by intro h; rw [ht] at h; exact lt_irrefl x h.1)]
  by_cases hij : x < i.divNat ∧ x < j.divNat
  · rw [ite_eq_left hij]
    have hi := (hlat i).1 hij.1
    have hj := (hlat j).1 hij.2
    have hix : i.divNat ≠ x := fun h => by rw [h] at hij; exact lt_irrefl x hij.1
    have hjx : j.divNat ≠ x := fun h => by rw [h] at hij; exact lt_irrefl x hij.2
    rw [hX i j, ite_eq_right (by intro h; exact hix h.2), hE i j, ite_eq_right hjx, hS' i j,
      ite_eq_right (by simp only [Fin.val_min]; omega),
      ite_eq_right (by simp only [Fin.val_min]; omega),
      schurRest_add_block K r (fun t => t.divNat = x) hblk]
    congr 1
    rw [List.map_congr_left (g := fun t => L i t * U t j) fun t ht => by
        have ht' := (hbk t).1 ht
        rw [hXbk i t ht', hE i t, ite_eq_left ht', hX t j, ite_eq_left ⟨hij.2, ht'⟩]
        have hti : t < i := Fin.lt_def.2 (by have := (hblk t).1 ht'; omega)
        simp only [hT, packLU, of_apply]
        rw [ite_eq_left hti],
      List.sum_map_filter_finRange (fun t => t.divNat = x), Finset.sum_filter]
  · rw [ite_eq_right hij, hX]
    by_cases hc : x < j.divNat ∧ i.divNat = x
    · rw [ite_eq_left hc]
      have hi := (hblk i).1 hc.2
      have hj := (hlat j).1 hc.1
      rw [ite_eq_left (by simp only [Fin.val_min]; omega)]
      simp only [hT, packLU, of_apply]
      rw [ite_eq_right (not_lt.2 (Fin.le_def.2 (by omega)))]
    · rw [ite_eq_right hc, hE]
      by_cases hj : j.divNat = x
      · rw [ite_eq_left hj, ite_eq_left (by
          have := (hblk j).1 hj; simp only [Fin.val_min]; omega)]
      · rw [ite_eq_right hj, hS']
        have hmK : ((min i j : Fin (N * r)) : ℕ) < K := by
          by_cases hjl : x < j.divNat
          · have hi1 : ¬ x < i.divNat := fun h => hij ⟨h, hjl⟩
            have hi2 : ¬ i.divNat = x := fun h => hc ⟨hjl, h⟩
            rw [hlat] at hi1
            rw [hblk] at hi2
            simp only [Fin.val_min]
            omega
          · rw [hlat] at hjl
            rw [hblk] at hj
            simp only [Fin.val_min]
            omega
        rw [ite_eq_left hmK, ite_eq_left (by omega)]

end Exact

end NonrecursiveBlockLU

end GolubVanLoan.Chapter03
