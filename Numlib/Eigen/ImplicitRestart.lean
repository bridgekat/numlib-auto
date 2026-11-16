/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.QRAlgorithm
import Numlib.LinearAlgebra.Matrix.KrylovDecomposition

/-!
# Implicit restarting of the Arnoldi process

Let $A \in \mathbb{K}^{n \times n}$ with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Implicit
restarting (Sorensen, 1992) compresses an $m$-step Arnoldi decomposition $A Q = Q H + r e_m^T$ to a
$j$-step one whose starting vector is filtered by a polynomial $p(A) = \prod_i (A - \mu_i I)$,
without restarting the Arnoldi process from the beginning. The presentation follows §10.5.2–10.5.4
of [golub2013matrix]. A chain of $p$ shifted QR steps $H_i - \mu_i I = V_i R_i$,
$H_{i+1} = R_i V_i + \mu_i I$ (`Matrix.IsShiftedQrChain` of `Numlib.Eigen.QRAlgorithm`) gives the
change of basis $V = V_0 \cdots V_{p-1}$. The leading $j + 1$ columns of $Q V$ then form an Arnoldi
decomposition, and $p(A) q_1$ is a multiple of its first column.

Krylov–Schur restarting (§10.5.4 of [golub2013matrix], after Stewart, 2001) is the same truncation
applied to a block upper triangular change of basis, such as an ordered Schur form, followed by a
Hessenberg reduction with a prescribed last row.

## Main results

* `Matrix.IsArnoldiDecomposition.implicitRestart`: the leading $j + 1$ columns of
  $Q V_0 \cdots V_{p-1}$ form an Arnoldi decomposition with the leading block of $H_p$.
* `Matrix.IsArnoldiDecomposition.implicitRestart_first`: $p(A) q_1$ is a multiple of the first
  column of $Q V_0 \cdots V_{p-1}$.
* `Matrix.IsArnoldiDecomposition.krylovSchur`: Krylov–Schur restarting, first to a Krylov
  decomposition and then to an Arnoldi decomposition.

## Proof outline

The proofs separate the algebra of the shifted QR chain from its effect on the Arnoldi
decomposition. For the chain, the product identity
`Matrix.prod_mul_prod_reverse_eq_prod_sub_smul_one` is Theorem 10.5.1 of [golub2013matrix]: the
accumulated factor $V$ is unitary with $H_p = V^H H_0 V$, has lower bandwidth $p$ when the $V_i$ are
upper Hessenberg, and carries the filter polynomial in its first column. For the decomposition, the
change of basis `Matrix.IsKrylovDecomposition.mul_of_conjTranspose_mul_self` ((10.5.9)) is followed
by the truncation `Matrix.IsKrylovDecomposition.leading` to the leading $j + 1$ columns. In
Krylov–Schur restarting, the truncation `Matrix.IsKrylovDecomposition.leading_of_apply_eq_zero`
keeps the residual vector and restricts the residual row.

## Implementation notes

* A decomposition with $j + p + 1$ columns is the $m$-step decomposition of the source with
  $m = j + p + 1$. It is truncated to $j + 1$ columns, the $j$ of the source, and $p$ is the number
  of shifts. Columns are indexed from $0$.
* An Arnoldi decomposition is `Matrix.IsArnoldiDecomposition`: $Q$ has orthonormal columns, $r$ is
  orthogonal to them, $H$ is upper Hessenberg and $A Q = Q H + r e_{\mathrm{last}}^T$.
-/

open Finset

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

namespace IsArnoldiDecomposition

variable {A : Matrix n n 𝕜} {r : n → 𝕜}

omit [DecidableEq n] in
/-- **Implicit restart** (§10.5.3 of [golub2013matrix]). Let $A Q = Q H + r e_{\mathrm{last}}^T$ be
an Arnoldi decomposition with $j + p + 1$ columns, with $p \ge 1$. Let
$H_0 = H, H_1, \dots, H_p$ be a chain of $p$ shifted QR steps $H_i - \mu_i I = V_i R_i$,
$H_{i+1} = R_i V_i + \mu_i I$ ((10.5.4)), where each $V_i$ is unitary and upper Hessenberg and
each $R_i$ is upper triangular. Let $V = V_0 \cdots V_{p-1}$ and $W = Q V$, with columns
$w_0, w_1, \dots$. Then the leading $j + 1$ columns of $W$ form an Arnoldi decomposition with
the leading $(j + 1) \times (j + 1)$ block of $H_p$ and the residual
$$r_+ = (H_p)_{j+1, j}\, w_{j+1} + V_{\mathrm{last}, j}\, r.$$

The source writes the residual as $v_{mj} r_c$, which misses the first term. The chain is
`Matrix.IsShiftedQrChain`, and $H_p = V^H H V$ holds by Theorem 10.5.1. -/
theorem implicitRestart {j p : ℕ} {Q : Matrix n (Fin (j + p + 1)) 𝕜}
    {H : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) 𝕜} (h : IsArnoldiDecomposition A Q H r)
    {Hs V R : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) 𝕜} {μ : ℕ → 𝕜}
    (hc : IsShiftedQrChain Hs V R μ p) (h0 : Hs 0 = H)
    (hV : ∀ i < p, V i ∈ unitaryGroup (Fin (j + p + 1)) 𝕜)
    (hVH : ∀ i < p, (V i).IsUpperHessenberg) (hR : ∀ i < p, (R i).IsUpperTriangular)
    (hp : 0 < p) :
    IsArnoldiDecomposition A
      ((Q * ((List.range p).map V).prod).submatrix id
        (Fin.castLE (by omega : j + 1 ≤ j + p + 1)))
      ((Hs p).submatrix (Fin.castLE (by omega : j + 1 ≤ j + p + 1))
        (Fin.castLE (by omega : j + 1 ≤ j + p + 1)))
      (Hs p ⟨j + 1, by omega⟩ ⟨j, by omega⟩ •
          (Q * ((List.range p).map V).prod).col ⟨j + 1, by omega⟩ +
        ((List.range p).map V).prod (Fin.last (j + p)) ⟨j, by omega⟩ • r) := by
  set W := ((List.range p).map V).prod with hW
  obtain ⟨hWu, hHp⟩ := hc.conjTranspose_mul_mul hV
  have hK := h.toIsKrylovDecomposition.mul_of_conjTranspose_mul_self ((mem_unitaryGroup_iff').1 hWu)
  rw [← h0, ← star_eq_conjTranspose, ← hHp, single_one_vecMul] at hK
  have hHess : (Hs p).IsUpperHessenberg :=
    hc.isUpperHessenberg (h0 ▸ h.isUpperHessenberg) hR hVH p le_rfl
  set jj : Fin (j + p + 1) := ⟨j, by omega⟩
  have hb : ∀ l : Fin (j + p + 1), l < jj → W.row (Fin.last (j + p)) l = 0 := by
    intro l hl
    refine IsShiftedQrChain.hasLowerBandwidth_prod hVH _ _ ?_
    rw [card_filter_le_lt_fin, Fin.val_last]
    rw [Fin.lt_def] at hl
    change (l : ℕ) < j at hl
    omega
  have hA := hK.isArnoldiDecomposition_leading hHess jj hb
  have hres : ∑ i ∈ Ioi jj, Hs p i jj • (Q * W).col i + W.row (Fin.last (j + p)) jj • r =
      Hs p ⟨j + 1, by omega⟩ jj • (Q * W).col ⟨j + 1, by omega⟩ + W (Fin.last (j + p)) jj • r := by
    rw [sum_eq_single (⟨j + 1, by omega⟩ : Fin (j + p + 1))]
    · rfl
    · intro i hi hne
      have hi' : j < (i : ℕ) := Fin.lt_def.1 (mem_Ioi.1 hi)
      have hne' : (i : ℕ) ≠ j + 1 := fun h' => hne (Fin.ext h')
      rw [hHess i jj ⟨⟨j + 1, by omega⟩, Fin.lt_def.2 (show j < j + 1 by omega),
        Fin.lt_def.2 (show j + 1 < (i : ℕ) by omega)⟩, zero_smul]
    · intro hnot
      exact absurd (mem_Ioi.2 (Fin.lt_def.2 (show j < j + 1 by omega))) hnot
  rw [hres] at hA
  exact hA

/-- **The restarted starting vector is filtered** (§10.5.3 of [golub2013matrix], $q_+ = p(A) q_1$ up
to a scalar). Let $A Q = Q H + r e_{\mathrm{last}}^T$ be an Arnoldi decomposition with
$j + p + 1$ columns, and let $H_0 = H, \dots, H_p$ be a chain of $p$ shifted QR steps
$H_i - \mu_i I = V_i R_i$, $H_{i+1} = R_i V_i + \mu_i I$ with each $R_i$ upper triangular. Let
$p(X) = \prod_{i < p} (X - \mu_i)$ and $W = Q V_0 \cdots V_{p-1}$. Then
$$p(A)\,(Q e_0) = (R_{p-1} \cdots R_0)_{00}\; W e_0.$$

So the truncated decomposition of `Matrix.IsArnoldiDecomposition.implicitRestart` is the
$(j + 1)$-step Arnoldi decomposition started from $p(A) q_1$ when that vector is nonzero, and
the iteration continues at step $j + 1$. This statement does not need the $V_i$ to be unitary. -/
theorem implicitRestart_first {j p : ℕ} {Q : Matrix n (Fin (j + p + 1)) 𝕜}
    {H : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) 𝕜} (h : IsArnoldiDecomposition A Q H r)
    {Hs V R : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) 𝕜} {μ : ℕ → 𝕜}
    (hc : IsShiftedQrChain Hs V R μ p) (h0 : Hs 0 = H)
    (hR : ∀ i < p, (R i).IsUpperTriangular) :
    Polynomial.aeval A ((List.range p).map fun i => Polynomial.X - Polynomial.C (μ i)).prod *ᵥ
        (Q *ᵥ Pi.single 0 1) =
      ((List.range p).reverse.map R).prod 0 0 •
        ((Q * ((List.range p).map V).prod) *ᵥ Pi.single 0 1) := by
  have hdeg : (((List.range p).map fun i => Polynomial.X - Polynomial.C (μ i)).prod).natDegree ≤
      j + p := by
    refine (Polynomial.natDegree_list_prod_le _).trans ?_
    rw [List.map_map]
    refine (List.sum_le_length_nsmul _ 1 fun x hx => ?_).trans ?_
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (Polynomial.natDegree_X_sub_C_le _)
    · simp
  have haeval : Polynomial.aeval H
      ((List.range p).map fun i => Polynomial.X - Polynomial.C (μ i)).prod =
      ((List.range p).map fun i => Hs 0 - μ i • 1).prod := by
    rw [map_list_prod, List.map_map, h0]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp [Algebra.algebraMap_eq_smul_one]
  have hfirst := hc.mulVec_first hR
  rw [bot_eq_zero] at hfirst
  rw [h.aeval_mulVec_first hdeg, haeval, hfirst, mulVec_smul, mulVec_mulVec]

omit [DecidableEq n] in
/-- **Krylov–Schur restarting** (§10.5.4 of [golub2013matrix], after Stewart, 2001). Let
$A Q = Q H + r e_{\mathrm{last}}^T$ be an Arnoldi decomposition with $k + 1$ columns, let $U$ be
unitary, and let $T = U^H H U$ be block upper triangular for the split after index $j$, that is,
$T_{il} = 0$ for $l \le j < i$. Let $T_{11}$ be the leading $(j + 1) \times (j + 1)$ block of
$T$, and let $u$ be the vector of the first $j + 1$ entries of the last row of $U$.
* (a) The leading $j + 1$ columns of $Q U$ form a Krylov decomposition with the matrix $T_{11}$,
  the same residual $r$, and the residual row $u$.
* (b) Let $Z \in \mathbb{K}^{(j+1) \times (j+1)}$ be unitary and $\tau \in \mathbb{K}$, with
  $Z^H T_{11} Z$ upper Hessenberg and $Z^H \bar{u} = \tau e_{\mathrm{last}}$. Then the leading
  $j + 1$ columns of $Q U$, multiplied by $Z$, form an Arnoldi decomposition with the matrix
  $Z^H T_{11} Z$ and the residual $\bar{\tau} r$.

The block $T$ is an ordered Schur form in the source, but its triangularity is not needed. A
matrix $Z$ as in (b) exists by `Matrix.exists_isUpperHessenberg_conj_lastCol` (P10.5.2 of
[golub2013matrix]) applied to $\bar{u}$. The source writes the residual as $\tau r_m$, where
$\tau$ is real. -/
theorem krylovSchur {k : ℕ} {Q : Matrix n (Fin (k + 1)) 𝕜}
    {H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜} (h : IsArnoldiDecomposition A Q H r)
    {U : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜} (hU : U ∈ unitaryGroup (Fin (k + 1)) 𝕜)
    (j : Fin (k + 1)) (hT : ∀ i l : Fin (k + 1), l ≤ j → j < i → (star U * H * U) i l = 0) :
    IsKrylovDecomposition A ((Q * U).submatrix id (Fin.castLE j.isLt))
        ((star U * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt)) r
        (fun l => U (Fin.last k) (Fin.castLE j.isLt l)) ∧
      ∀ Z ∈ unitaryGroup (Fin (j + 1)) 𝕜, ∀ τ : 𝕜,
        (star Z * (star U * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt) *
          Z).IsUpperHessenberg →
        star Z *ᵥ star (fun l => U (Fin.last k) (Fin.castLE j.isLt l)) =
          Pi.single (Fin.last j) τ →
        IsArnoldiDecomposition A ((Q * U).submatrix id (Fin.castLE j.isLt) * Z)
          (star Z * (star U * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt) * Z)
          (star τ • r) := by
  have hK := h.toIsKrylovDecomposition.mul_of_conjTranspose_mul_self ((mem_unitaryGroup_iff').1 hU)
  rw [single_one_vecMul] at hK
  have ha := hK.leading_of_apply_eq_zero j hT
  refine ⟨ha, fun Z hZ τ hZH hZu => ?_⟩
  have hK' := ha.mul_of_conjTranspose_mul_self ((mem_unitaryGroup_iff').1 hZ)
  have hrow : (U.row (Fin.last k) ∘ Fin.castLE j.isLt) ᵥ* Z = Pi.single (Fin.last j) (star τ) := by
    have := congrArg star hZu
    rw [star_mulVec, star_star, ← star_eq_conjTranspose, star_star, ← Pi.single_star] at this
    exact this
  rw [hrow] at hK'
  have hres : vecMulVec r (Pi.single (Fin.last j) (star τ)) =
      vecMulVec (star τ • r) (Pi.single (Fin.last j) 1) := by
    ext x l
    by_cases hl : l = Fin.last j
    · subst hl
      simp [vecMulVec_apply, mul_comm]
    · simp [vecMulVec_apply, Pi.single_eq_of_ne hl]
  exact ⟨⟨hK'.conjTranspose_mul_self, by rw [mulVec_smul, hK'.conjTranspose_mulVec, smul_zero],
    by rw [← hres]; exact hK'.mul_eq⟩, hZH⟩

end IsArnoldiDecomposition

end Matrix
