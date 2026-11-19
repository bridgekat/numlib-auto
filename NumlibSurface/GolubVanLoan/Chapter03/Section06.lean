/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter03.Section02

/-!
# Golub and Van Loan, Section 3.6: Parallel LU

This module formalizes the precise mathematics of §3.6.1 of [golub2013matrix], the block LU
factorization with partial pivoting. Let $A \in \mathbb{R}^{n \times n}$ be partitioned with a
leading block of order $r$. A row permutation $P_1$ and a factorization $P_1 \begin{bmatrix} A_{11}
\\ A_{21} \end{bmatrix} = \begin{bmatrix} L_{11} \\ L_{21} \end{bmatrix} U_{11}$ of the first block
column (3.6.2), the solve $L_{11} U_{12} = \tilde A_{12}$ (3.6.4), and the Schur complement
$A^{new} = \tilde A_{22} - L_{21} U_{12}$ give the partial factorization (3.6.5). A pivoted
factorization $P^{new} A^{new} = L^{new} U^{new}$ of the Schur complement then completes a pivoted
LU factorization $PA = LU$ of $A$. By induction on the block columns, every square matrix has such a
factorization with multipliers of modulus at most $1$. The proofs specialize the LU specifications
`Matrix.IsLU` and `Matrix.IsRectLU` of `Numlib.LinearAlgebra.Matrix.LU`.

## Main results

* (3.6.2), `GolubVanLoan.Chapter03.equation_3_6_2`: a tall block column has a row permutation $P_1$
  with $P_1 W = L U_{11}$, $L$ unit lower trapezoidal with $|\ell_{ij}| \le 1$.
* (3.6.3)–(3.6.5), `GolubVanLoan.Chapter03.equation_3_6_5`: the partial factorization through the
  Schur complement $\tilde A_{22} - L_{21} U_{12}$.
* §3.6.1, `GolubVanLoan.Chapter03.blockLUPivoting`: the pieces assemble into a pivoted block LU
  factorization of $A$.
* §3.6.1, `GolubVanLoan.Chapter03.exists_blockLUPivoting`: every square matrix has a pivoted LU
  factorization built block column by block column, with $|\ell_{ij}| \le 1$.

## Implementation notes

* The source leaves the algorithm as an exercise (P3.6.1), so there is no program. The assembly of
  the factorization from its pieces and the induction on the block columns are theorems.
* A block row or column split is `Fin (r + s)`, read as `Fin r ⊕ Fin s` through `finSumFinEquiv`.

## Deviations from the source

* **Equation (3.6.2)** (reading). The rectangular step states existence with the multiplier
  bound from partial pivoting. See `GolubVanLoan.Chapter03.equation_3_6_2`.
* **Equations (3.6.3)–(3.6.5), and assembly** (generalization). The block identities allow
  arbitrary combined trailing size. The Schur complement identity uses only the stated
  product equations. See `GolubVanLoan.Chapter03.equation_3_6_5` and
  `GolubVanLoan.Chapter03.blockLUPivoting`.
* **§3.6.1, block column induction** (generalization). The source assumes $n = rN$; the last block
  column may be narrower. See `GolubVanLoan.Chapter03.exists_blockLUPivoting`.

## Not formalized

* **The parallel material of §3.6.** The block-cyclic distribution, the processor grids, (3.6.6) and
  the figures state no proposition.
* **Tournament pivoting (§3.6.3).** It states no proposition.
* **The algorithm of P3.6.1.** The source leaves it as an exercise.
-/

open Matrix

namespace GolubVanLoan.Chapter03

variable {r s : ℕ}

/-- **Equation (3.6.2)** of [golub2013matrix]. Let $W \in \mathbb{R}^{(r+s) \times r}$ be a tall
block column. Then there are a permutation matrix $P_1$, a matrix
$L \in \mathbb{R}^{(r+s) \times r}$ and a matrix $U_{11} \in \mathbb{R}^{r \times r}$ with
$$P_1 W = L U_{11},$$
where $L$ is unit lower trapezoidal with $|\ell_{ij}| \le 1$ for all $i, j$ and $U_{11}$ is
upper triangular.

**Reading.** The source obtains the factors by rectangular partial pivoting on its first
block column. The theorem states existence for any tall matrix, with the unit lower
trapezoidal structure and multiplier bound resulting from partial pivoting. -/
theorem equation_3_6_2 (W : Matrix (Fin (r + s)) (Fin r) ℝ) :
    ∃ (σ : Equiv.Perm (Fin (r + s))) (L : Matrix (Fin (r + s)) (Fin r) ℝ)
      (U : Matrix (Fin r) (Fin r) ℝ), IsRectLU (σ.permMatrix ℝ * W) L U ∧ ∀ i j, |L i j| ≤ 1 := by
  obtain ⟨σ, L, U, h, hL⟩ := exists_permMatrix_mul_isRectLU W (by omega)
  exact ⟨σ, L, U, h, fun i j => by simpa only [Real.norm_eq_abs] using hL i j⟩

/-- **Equations (3.6.3)–(3.6.5)** of [golub2013matrix], the partial factorization after Parts A–C.
Let $\tilde A_{11}, L_{11}, U_{11} \in \mathbb{R}^{r \times r}$, $\tilde A_{12}, U_{12} \in
\mathbb{R}^{r \times s}$, $\tilde A_{21}, L_{21} \in \mathbb{R}^{s \times r}$ and
$\tilde A_{22} \in \mathbb{R}^{s \times s}$. If $\tilde A_{11} = L_{11} U_{11}$ and
$\tilde A_{21} = L_{21} U_{11}$ (the block column factorization (3.6.2)) and
$L_{11} U_{12} = \tilde A_{12}$ (the multiple right-hand side solve (3.6.4)), then
$$\begin{bmatrix} \tilde A_{11} & \tilde A_{12} \\ \tilde A_{21} & \tilde A_{22} \end{bmatrix} =
  \begin{bmatrix} L_{11} & 0 \\ L_{21} & I \end{bmatrix} \begin{bmatrix} I & 0 \\ 0 & A^{new}
  \end{bmatrix} \begin{bmatrix} U_{11} & U_{12} \\ 0 & I \end{bmatrix}, \qquad A^{new} = \tilde
  A_{22} - L_{21} U_{12}.$$

**Generalization.** The source uses the blocks of $P_1A$ after the first pivoted step.
The identity holds for any four compatible blocks satisfying the product equations,
with arbitrary trailing size and arbitrary factors. -/
theorem equation_3_6_5 {A₁₁ L₁₁ U₁₁ : Matrix (Fin r) (Fin r) ℝ}
    {A₁₂ U₁₂ : Matrix (Fin r) (Fin s) ℝ} {A₂₁ L₂₁ : Matrix (Fin s) (Fin r) ℝ}
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ) (h₁₁ : A₁₁ = L₁₁ * U₁₁) (h₂₁ : A₂₁ = L₂₁ * U₁₁)
    (h₁₂ : L₁₁ * U₁₂ = A₁₂) :
    fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ =
      fromBlocks L₁₁ 0 L₂₁ 1 * fromBlocks 1 0 0 (A₂₂ - L₂₁ * U₁₂) * fromBlocks U₁₁ U₁₂ 0 1 :=
  (equation_3_2_9 A₂₂ h₁₁ h₂₁ h₁₂).1

/-- **Section 3.6.1** of [golub2013matrix], the assembled pivoted block LU factorization. Let
$A \in \mathbb{R}^{(r+s) \times (r+s)}$ and let $P_1$ be a permutation matrix with
$$P_1 A = \begin{bmatrix} \tilde A_{11} & \tilde A_{12} \\ \tilde A_{21} & \tilde A_{22}
  \end{bmatrix}$$
(3.6.3), where $\tilde A_{11}$ has order $r$. Assume that $\tilde A_{11} = L_{11} U_{11}$ is an
LU factorization, that $\tilde A_{21} = L_{21} U_{11}$ (3.6.2), that
$L_{11} U_{12} = \tilde A_{12}$ (3.6.4), and that $P^{new} A^{new} = L^{new} U^{new}$ is an LU
factorization with a permutation matrix $P^{new}$ of the Schur complement
$A^{new} = \tilde A_{22} - L_{21} U_{12}$ (3.6.5). Let
$$P = \begin{bmatrix} I & 0 \\ 0 & P^{new} \end{bmatrix} P_1, \qquad \tilde L_{21} = P^{new}
  L_{21}.$$
Then $P$ is the permutation matrix of the permutation of $P_1$ followed by $I \oplus P^{new}$,
and
$$PA = \begin{bmatrix} L_{11} & 0 \\ \tilde L_{21} & L^{new} \end{bmatrix} \begin{bmatrix}
  U_{11} & U_{12} \\ 0 & U^{new} \end{bmatrix}$$
is an LU factorization of $PA$.

The permutation of $P$ is `σ₁ * finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r))
σ)`. The block matrices on `Fin r ⊕ Fin s` are read on `Fin (r + s)` through `finSumFinEquiv`,
and an LU factorization is `Matrix.IsLU`.

**Generalization.** The source groups the trailing matrix into equal blocks. The
assembly identity holds for every trailing size. -/
theorem blockLUPivoting {A : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    {σ₁ : Equiv.Perm (Fin (r + s))}
    {Ã₁₁ L₁₁ U₁₁ : Matrix (Fin r) (Fin r) ℝ} {Ã₁₂ U₁₂ : Matrix (Fin r) (Fin s) ℝ}
    {Ã₂₁ L₂₁ : Matrix (Fin s) (Fin r) ℝ} {Ã₂₂ : Matrix (Fin s) (Fin s) ℝ}
    {σ : Equiv.Perm (Fin s)} {L U : Matrix (Fin s) (Fin s) ℝ}
    (hP₁ : σ₁.permMatrix ℝ * A =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks Ã₁₁ Ã₁₂ Ã₂₁ Ã₂₂))
    (h₁₁ : IsLU Ã₁₁ L₁₁ U₁₁) (h₂₁ : Ã₂₁ = L₂₁ * U₁₁) (h₁₂ : L₁₁ * U₁₂ = Ã₁₂)
    (hnew : IsLU (σ.permMatrix ℝ * (Ã₂₂ - L₂₁ * U₁₂)) L U) :
    (σ₁ * finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r)) σ)).permMatrix ℝ =
        reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (σ.permMatrix ℝ)) *
          σ₁.permMatrix ℝ ∧
      IsLU ((σ₁ * finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r)) σ)).permMatrix ℝ *
          A)
        (reindex finSumFinEquiv finSumFinEquiv (fromBlocks L₁₁ 0 (σ.permMatrix ℝ * L₂₁) L))
        (reindex finSumFinEquiv finSumFinEquiv (fromBlocks U₁₁ U₁₂ 0 U)) := by
  have hP :
      (σ₁ * finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r)) σ)).permMatrix ℝ =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (σ.permMatrix ℝ)) *
        σ₁.permMatrix ℝ := by
    rw [permMatrix_mul, permMatrix_permCongr_sumCongr, Matrix.permMatrix_refl]
  refine ⟨hP, ?_⟩
  have hPA :
      (σ₁ * finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r)) σ)).permMatrix ℝ * A =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks Ã₁₁ Ã₁₂ (σ.permMatrix ℝ * Ã₂₁) (σ.permMatrix ℝ * Ã₂₂)) := by
    rw [hP, Matrix.mul_assoc, hP₁, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  rw [hPA]
  refine blockLU_of_schur h₁₁ (by rw [h₂₁, Matrix.mul_assoc]) h₁₂ ?_
  rwa [Matrix.mul_assoc, ← Matrix.mul_sub]

/-- **Section 3.6.1** of [golub2013matrix], the induction on the block columns. Let $r > 0$ be a
block size. Then every $A \in \mathbb{R}^{n \times n}$ has a permutation matrix $P$, a unit
lower triangular $L$ and an upper triangular $U$ with
$$PA = LU, \qquad |\ell_{ij}| \le 1 \text{ for all } i, j.$$

**Generalization.** The source assumes $n = rN$ "for clarity". The theorem holds for every $n$;
the last block column may be narrower than $r$.

The factorization is built block column by block column: (3.6.2) on the first block column, the
solve (3.6.4) for $U_{12}$, the factorization of $A^{new}$ by induction, and the assembly
`GolubVanLoan.Chapter03.blockLUPivoting`. -/
theorem exists_blockLUPivoting {r : ℕ} (hr : 0 < r) :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), ∃ (σ : Equiv.Perm (Fin n))
      (L U : Matrix (Fin n) (Fin n) ℝ), IsLU (σ.permMatrix ℝ * A) L U ∧ ∀ i j, |L i j| ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A
  by_cases hn : n ≤ r
  · obtain ⟨σ, L, U, h, hL⟩ := equation_3_6_2 (r := n) (s := 0) A
    exact ⟨σ, L, U, isRectLU_iff_isLU.1 h, hL⟩
  obtain ⟨s, rfl⟩ : ∃ s, n = r + s := ⟨n - r, by omega⟩
  -- (3.6.2) on the first block column
  obtain ⟨σ₁, L, U₁₁, hRect, hL⟩ :=
    equation_3_6_2 (r := r) (s := s) (fun i k => A i (finSumFinEquiv (Sum.inl k)))
  set Ã := σ₁.permMatrix ℝ * A with hÃ
  set Ã₁₁ : Matrix (Fin r) (Fin r) ℝ := of fun i j =>
    Ã (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) with hÃ₁₁
  set Ã₁₂ : Matrix (Fin r) (Fin s) ℝ := of fun i j =>
    Ã (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) with hÃ₁₂
  set Ã₂₁ : Matrix (Fin s) (Fin r) ℝ := of fun i j =>
    Ã (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) with hÃ₂₁
  set Ã₂₂ : Matrix (Fin s) (Fin s) ℝ := of fun i j =>
    Ã (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) with hÃ₂₂
  set L₁₁ : Matrix (Fin r) (Fin r) ℝ := of fun i k => L (finSumFinEquiv (Sum.inl i)) k with hL₁₁
  set L₂₁ : Matrix (Fin s) (Fin r) ℝ := of fun i k => L (finSumFinEquiv (Sum.inr i)) k with hL₂₁
  have hcol : ∀ i k, Ã i (finSumFinEquiv (Sum.inl k)) = ∑ t, L i t * U₁₁ t k := fun i k => by
    rw [← Matrix.mul_apply, hRect.mul_eq, hÃ, Matrix.mul_apply]
    rfl
  have hL₁₁unit : L₁₁.IsUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hij' : (i : ℕ) < j := Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 hij)
      exact hRect.hasUpperBandwidthRect _ _ (by
        simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, add_zero]; exact hij')
    · exact hRect.apply_eq_one _ _ (by simp)
  have hU₁₁upper : U₁₁.IsUpperTriangular := fun i j hij =>
    hRect.hasLowerBandwidthRect i j (by have := Fin.lt_def.1 (show j < i from hij); omega)
  have h₁₁ : IsLU Ã₁₁ L₁₁ U₁₁ := ⟨hL₁₁unit, hU₁₁upper, by
    ext i j; rw [Matrix.mul_apply, hÃ₁₁, of_apply, hcol]; rfl⟩
  have h₂₁ : Ã₂₁ = L₂₁ * U₁₁ := by
    ext i j; rw [Matrix.mul_apply, hÃ₂₁, of_apply, hcol]; rfl
  -- (3.6.4): the multiple right-hand side solve
  have hdetL : IsUnit L₁₁.det := by rw [hL₁₁unit.det_eq_one]; exact isUnit_one
  set U₁₂ := L₁₁⁻¹ * Ã₁₂ with hU₁₂
  have h₁₂ : L₁₁ * U₁₂ = Ã₁₂ := by
    rw [hU₁₂, ← Matrix.mul_assoc, mul_nonsing_inv _ hdetL, Matrix.one_mul]
  -- the induction hypothesis on `A^{new}`
  obtain ⟨σ, Ln, Un, hnew, hLn⟩ := ih s (by omega) (Ã₂₂ - L₂₁ * U₁₂)
  have hP₁ : σ₁.permMatrix ℝ * A =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks Ã₁₁ Ã₁₂ Ã₂₁ Ã₂₂) := by
    ext i j
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> rfl
  obtain ⟨_, h⟩ := blockLUPivoting hP₁ h₁₁ h₂₁ h₁₂ hnew
  refine ⟨_, _, _, h, fun i j => ?_⟩
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b
  · exact hL _ _
  · simp
  · rw [fromBlocks_apply₂₁, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    exact hL _ _
  · exact hLn _ _

end GolubVanLoan.Chapter03
