/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.Sylvester

/-!
# The fast Poisson solver framework

The discretized Poisson equation on a rectangle, and every separable problem of the same shape, is a
linear system with a Kronecker-sum matrix,
$$(I_{n_2} \otimes A_1 + A_2 \otimes I_{n_1}) \operatorname{vec}(U) = \operatorname{vec}(B),$$
as in [golub2013matrix], §4.8.3–4.8.7, and in Van Loan, *Computational Frameworks for the Fast
Fourier Transform*, §4.3–4.5. Suppose that $A_1 = V \operatorname{diag}(\nu) V^{-1}$ and
$A_2 = W \operatorname{diag}(\mu) W^{-1}$. In the eigenvector bases the system decouples: with
$\tilde U = V^{-1} U W^{-T}$ and $\tilde B = V^{-1} B W^{-T}$ it reads $\operatorname{diag}(\nu)
\tilde U + \tilde U \operatorname{diag}(\mu) = \tilde B$, and it is solved entrywise by $\tilde
u_{ij} = \tilde b_{ij} / (\nu_i + \mu_j)$.

This is the specification against which the fast Poisson solvers (Algorithm 4.8.2 of
[golub2013matrix] and its variants) are proved. These solvers are fast because fast transforms apply
$V$, $W$ and their inverses. The operation counts are not formalized.

## Main results

* `FastPoisson.kroneckerSum_mulVec_vec_eq_iff`: if $\nu_i + \mu_j \neq 0$ for all $i, j$, the
  solution of the Kronecker-sum system is $U = V \tilde U W^T$ with $\tilde u_{ij} = (V^{-1} B
  W^{-T})_{ij} / (\nu_i + \mu_j)$.
* `FastPoisson.isUnit_kroneckerSum`: under the same hypotheses the Kronecker sum is nonsingular.

## Implementation notes

* Nothing is derived again here. The Kronecker sum `A₂ ⊕ₖ A₁` acting on Mathlib's column-major
  `Matrix.vec` is the Sylvester-type map $U \mapsto A_1 U + U A_2^T$, by
  `Matrix.kroneckerSum_mulVec_vec`. The change of basis is `Matrix.sylvesterMap_conj`, and the
  diagonal solve is `Matrix.sylvesterMap_diagonal_eq_iff`, both of
  `Numlib.LinearAlgebra.Matrix.Sylvester`.
* The second-difference matrices $\mathcal{T}^{(DD)}$, $\mathcal{T}^{(DN)}$, $\mathcal{T}^{(NN)}$
  and $\mathcal{T}^{(P)}$ of the model problems are `Matrix.symmTridiagonalToeplitz`,
  `Matrix.secondDifferenceDN`, `Matrix.secondDifferenceNN` and `Matrix.secondDifferencePeriodic` of
  `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`. Their eigensystems are the sine and cosine
  transforms `Matrix.dst1`, `Matrix.dst2` and `Matrix.dct1` of
  `Numlib.Analysis.Fourier.SineCosineTransform`, and the diagonalization of circulant matrices by
  the discrete Fourier transform in `Numlib.Analysis.Fourier.Circulant`.
-/

open scoped Kronecker

namespace FastPoisson

open Matrix

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- The eigenvector change of basis turns $A_1 U + U A_2^T$ into the diagonal Sylvester operator: if
$V^{-1} A_1 V = \operatorname{diag}(\nu)$ and $W^{-1} A_2 W = \operatorname{diag}(\mu)$, then
$V^{-1} (A_1 U + U A_2^T) W^{-T} = \operatorname{diag}(\nu) \tilde U + \tilde U
\operatorname{diag}(\mu)$ with $\tilde U = V^{-1} U W^{-T}$. -/
private theorem sylvesterMap_diagonal_conj {A₁ : Matrix m m K} {A₂ : Matrix n n K}
    {V : Matrix m m K} {W : Matrix n n K} (hV : IsUnit V) (hW : IsUnit W) {ν : m → K}
    {μ : n → K} (hA₁ : V⁻¹ * A₁ * V = diagonal ν) (hA₂ : W⁻¹ * A₂ * W = diagonal μ)
    (U : Matrix m n K) :
    sylvesterMap (diagonal ν) (diagonal (-μ)) (V⁻¹ * U * W⁻¹ᵀ) =
      V⁻¹ * (A₁ * U + U * A₂ᵀ) * W⁻¹ᵀ := by
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det V).mp hV
  have hWd : IsUnit W.det := (isUnit_iff_isUnit_det W).mp hW
  have hWt : IsUnit Wᵀ := (isUnit_iff_isUnit_det _).mpr (by rwa [det_transpose])
  have key := sylvesterMap_conj (isUnit_nonsing_inv_iff.mpr hV) hWt A₁ (-A₂ᵀ) U
  rw [nonsing_inv_nonsing_inv V hVd, hA₁, ← transpose_nonsing_inv] at key
  have h2 : Wᵀ * -A₂ᵀ * W⁻¹ᵀ = diagonal (-μ) := by
    rw [Matrix.mul_neg, Matrix.neg_mul, ← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc,
      hA₂, diagonal_transpose, diagonal_neg]
    rfl
  rw [h2] at key
  rw [key, sylvesterMap_apply, Matrix.mul_neg, sub_neg_eq_add]

/-- The **fast Poisson solver framework**. Let $K$ be a field, let $A_1 \in K^{m \times m}$ and
$A_2 \in K^{n \times n}$, and let $V \in K^{m \times m}$ and $W \in K^{n \times n}$ be
nonsingular with
$$V^{-1} A_1 V = \operatorname{diag}(\nu), \qquad W^{-1} A_2 W = \operatorname{diag}(\mu)$$
for some $\nu \in K^m$ and $\mu \in K^n$. Suppose that $\nu_i + \mu_j \neq 0$ for all $i$ and
$j$. Then for all $U, B \in K^{m \times n}$,
$$(I_n \otimes A_1 + A_2 \otimes I_m) \operatorname{vec}(U) = \operatorname{vec}(B) \iff U = V
  \tilde U W^T, \quad \tilde u_{ij} = \frac{(V^{-1} B W^{-T})_{ij}}{\nu_i + \mu_j}.$$
This is the specification of Algorithm 4.8.2 of [golub2013matrix], §4.8.4, with the
diagonalizations (4.8.13)–(4.8.14).

The map $\operatorname{vec}$ is Mathlib's column-major `Matrix.vec`. The matrix
$I_n \otimes A_1 + A_2 \otimes I_m$ is the Kronecker sum `A₂ ⊕ₖ A₁`, that is,
`Matrix.kroneckerSum A₂ A₁`. -/
theorem kroneckerSum_mulVec_vec_eq_iff {A₁ : Matrix m m K} {A₂ : Matrix n n K}
    {V : Matrix m m K} {W : Matrix n n K} (hV : IsUnit V) (hW : IsUnit W) {ν : m → K}
    {μ : n → K} (hA₁ : V⁻¹ * A₁ * V = diagonal ν) (hA₂ : W⁻¹ * A₂ * W = diagonal μ)
    (hνμ : ∀ i j, ν i + μ j ≠ 0) (U B : Matrix m n K) :
    (A₂ ⊕ₖ A₁) *ᵥ vec U = vec B ↔
      U = V * (of fun i j => (V⁻¹ * B * W⁻¹ᵀ) i j / (ν i + μ j)) * Wᵀ := by
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det V).mp hV
  have hWd : IsUnit W.det := (isUnit_iff_isUnit_det W).mp hW
  have hWW : W⁻¹ᵀ * Wᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv W hWd, transpose_one]
  have hWW' : Wᵀ * W⁻¹ᵀ = 1 := by rw [← transpose_mul, nonsing_inv_mul W hWd, transpose_one]
  have hne : ∀ i j, ν i ≠ (-μ) j := fun i j h => hνμ i j (by rw [h, Pi.neg_apply, neg_add_cancel])
  rw [kroneckerSum_mulVec_vec, vec_inj]
  -- conjugate both sides by the invertible `V⁻¹ · W⁻ᵀ`
  have hconj : ∀ X Y : Matrix m n K, X = Y ↔ V⁻¹ * X * W⁻¹ᵀ = V⁻¹ * Y * W⁻¹ᵀ := by
    intro X Y
    refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
    have := congrArg (fun Z => V * Z * Wᵀ) h
    simp only [← Matrix.mul_assoc, mul_nonsing_inv V hVd, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, hWW, Matrix.mul_one] using this
  rw [hconj, ← sylvesterMap_diagonal_conj hV hW hA₁ hA₂, sylvesterMap_diagonal_eq_iff hne,
    hconj U]
  have hU : V⁻¹ * (V * (of fun i j => (V⁻¹ * B * W⁻¹ᵀ) i j / (ν i + μ j)) * Wᵀ) * W⁻¹ᵀ =
      of fun i j => (V⁻¹ * B * W⁻¹ᵀ) i j / (ν i + μ j) := by
    simp only [← Matrix.mul_assoc, nonsing_inv_mul V hVd, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hWW', Matrix.mul_one]
  rw [hU]
  simp only [Pi.neg_apply, sub_neg_eq_add]

/-- Let $K$ be a field, and let $A_1$, $A_2$, $V$, $W$, $\nu$ and $\mu$ satisfy the hypotheses of
`FastPoisson.kroneckerSum_mulVec_vec_eq_iff`: $V$ and $W$ are nonsingular,
$V^{-1} A_1 V = \operatorname{diag}(\nu)$, $W^{-1} A_2 W = \operatorname{diag}(\mu)$, and
$\nu_i + \mu_j \neq 0$ for all $i$ and $j$. Then the Kronecker sum
$I_n \otimes A_1 + A_2 \otimes I_m$ is nonsingular. -/
theorem isUnit_kroneckerSum {A₁ : Matrix m m K} {A₂ : Matrix n n K}
    {V : Matrix m m K} {W : Matrix n n K} (hV : IsUnit V) (hW : IsUnit W) {ν : m → K}
    {μ : n → K} (hA₁ : V⁻¹ * A₁ * V = diagonal ν) (hA₂ : W⁻¹ * A₂ * W = diagonal μ)
    (hνμ : ∀ i j, ν i + μ j ≠ 0) : IsUnit (A₂ ⊕ₖ A₁) := by
  refine mulVec_surjective_iff_isUnit.mp fun w => ?_
  obtain ⟨B, rfl⟩ := vec_bijective.2 w
  exact ⟨_, (kroneckerSum_mulVec_vec_eq_iff hV hW hA₁ hA₂ hνμ _ B).2 rfl⟩

end FastPoisson
