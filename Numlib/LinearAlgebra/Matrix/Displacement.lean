/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a file beside `Mathlib.LinearAlgebra.Matrix.Kronecker`.
-/
import Numlib.LinearAlgebra.Matrix.Cauchy
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.Sylvester
import Numlib.LinearAlgebra.Matrix.Toeplitz

/-!
# Displacement structure

Let $F, G, A \in K^{n \times n}$ over a field $K$. The **displacement** of $A$ with respect to the
displacement operators $F$ and $G$ is $FA - AG$, and the **displacement rank** is its rank. The
matrix $A$ has displacement structure when the displacement rank is low; a factorization
$FA - AG = RS^T$ with $R, S \in K^{n \times r}$ is a set of **generators**. The presentation follows
[golub2013matrix] §12.1, after Kailath, Kung and Morf (1979) and Gohberg, Kailath and Olshevsky
(1995).

The module proves that generators determine $A$ when the map $X \mapsto FX - XG$ is injective; that
a Cauchy matrix has displacement $ee^T$ for diagonal operators; that one step of Gaussian
elimination updates the generators explicitly ([golub2013matrix] Theorem 12.1.1, generalized); and
that Toeplitz and Hankel matrices have displacement rank at most $2$ for the cyclic shifts
$Z_1, Z_{-1}$ and at most $4$ for the corner-modified tridiagonal matrices $Y_{00}, Y_{11}$
([golub2013matrix] (12.1.8)–(12.1.11)).

## Main definitions

* `Matrix.displacementRank`: the rank of $FA - AG$, [golub2013matrix] (12.1.2).

## Main results

* `Matrix.eq_of_sylvesterMap_eq`: if $X \mapsto FX - XG$ is injective, two matrices with the same
  generators are equal.
* `Matrix.displacementRank_le_iff_exists`: the displacement rank is at most $r$ if and only if
  generators with $r$ columns exist, [golub2013matrix] (12.1.3).
* `Matrix.sylvesterMap_diagonal_cauchy`, `Matrix.displacementRank_diagonal_cauchy`: the Cauchy
  matrix $(1/(\omega_k - \nu_j))$ has displacement $ee^T$ for $\operatorname{diag}(\omega)$ and
  $\operatorname{diag}(\nu)$, hence displacement rank $1$.
* `Matrix.sylvesterMap_schurComplement`: if the first row of $F$ and the first column of $G$ vanish
  off the corner, the Schur complement after one elimination step has explicitly updated generators.
  `Matrix.sylvesterMap_diagonal_schurComplement` is the diagonal case of [golub2013matrix] Theorem
  12.1.1, and `Matrix.displacementRank_diagonal_schurComplement_le` its consequence for the rank.
* `Matrix.sylvesterMap_cyclicShift_one_neg_one_injective`,
  `Matrix.sylvesterMap_cornerTridiagonal_injective`: the maps $X \mapsto Z_1 X - X Z_{-1}$ and
  $X \mapsto Y_{00} X - X Y_{11}$ are injective.
* `Matrix.sylvesterMap_cyclicShift_toeplitz_apply`, `Matrix.sylvesterMap_cyclicShift_hankel_apply`,
  `Matrix.sylvesterMap_cornerTridiagonal_toeplitz_apply`,
  `Matrix.sylvesterMap_cornerTridiagonal_hankel_apply`: where the displacements of Toeplitz and
  Hankel matrices vanish.
* `Matrix.displacementRank_cyclicShift_toeplitz_le`,
  `Matrix.displacementRank_cyclicShift_hankel_le`,
  `Matrix.displacementRank_cornerTridiagonal_toeplitz_le`,
  `Matrix.displacementRank_cornerTridiagonal_hankel_le`,
  `Matrix.displacementRank_cornerTridiagonal_toeplitz_add_hankel_le`: the rank bounds
  (12.1.8)–(12.1.11) of [golub2013matrix].

## Notation

The displacement operators below are those of [golub2013matrix] §12.1.7.

* $Z_\varphi$: the $\varphi$-cyclic shift `Matrix.cyclicShift n φ` of
  `Numlib.LinearAlgebra.Matrix.Permutation`, with ones on the subdiagonal and $\varphi$ in the top
  right corner.
* $Y_{\gamma\delta}$: the corner-modified tridiagonal matrix `Matrix.cornerTridiagonal n γ δ` of
  `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`, with ones on the two off-diagonals, $\gamma$ at
  the top left and $\delta$ at the bottom right corner.

## Implementation notes

* The displacement $FA - AG$ is the Sylvester operator `Matrix.sylvesterMap F G A` of
  `Numlib.LinearAlgebra.Matrix.Sylvester`. This module adds only its rank.
* [golub2013matrix] puts the nonsingularity of the Sylvester operator into the definition (12.1.2)
  of the displacement rank. Here it is a hypothesis exactly where it is used.
* The support lemmas are stated entrywise. The rank bounds follow from them by the support bound of
  `Numlib.LinearAlgebra.Matrix.Rank`.
* Indices are $0$-based: the first row of the source is row $0$.
-/

open Finset

namespace Matrix

variable {K : Type*} [Field K]

/-! ### The displacement rank -/

section Rank

variable {n : Type*} [Fintype n]

/-- Let $F, G, A \in K^{n \times n}$. The **$\{F, G\}$-displacement rank** of $A$ is the rank of its
displacement $$FA - AG.$$ This is (12.1.2) of [golub2013matrix].

No nonsingularity of the Sylvester operator $X \mapsto FX - XG$ is part of the definition. -/
noncomputable def displacementRank (F G A : Matrix n n K) : ℕ :=
  (sylvesterMap F G A).rank

/-- Let $F, G \in K^{n \times n}$ with $X \mapsto FX - XG$ injective. If $FA - AG = RS^T$ and
$FB - BG = RS^T$ for the same $R, S \in K^{n \times r}$, then $A = B$: **generators determine
the matrix**. This is the remark in [golub2013matrix] §12.1.1 under the condition
$\lambda(F) \cap \lambda(G) = \emptyset$. -/
theorem eq_of_sylvesterMap_eq {F G : Matrix n n K} (hFG : Function.Injective (sylvesterMap F G))
    {A B : Matrix n n K} {r : Type*} [Fintype r] {R S : Matrix n r K}
    (hA : sylvesterMap F G A = R * Sᵀ) (hB : sylvesterMap F G B = R * Sᵀ) : A = B :=
  hFG (hA.trans hB.symm)

end Rank

/-! ### Cauchy matrices -/

/-- Let $\omega, \nu \in K^n$ with $\omega_k \ne \nu_j$ for all $k$ and $j$, and let $C$ be the
Cauchy matrix with entries $c_{kj} = 1/(\omega_k - \nu_j)$. Then $$\operatorname{diag}(\omega)
C - C \operatorname{diag}(\nu) = ee^T,$$ where $e$ is the vector of ones. This is
[golub2013matrix] §12.1.2.

The matrix $C$ is `Matrix.cauchy ω (-ν)`. -/
theorem sylvesterMap_diagonal_cauchy {n : ℕ} {ω ν : Fin n → K} (h : ∀ k j, ω k ≠ ν j) :
    sylvesterMap (diagonal ω) (diagonal ν) (cauchy ω (-ν)) = vecMulVec 1 1 := by
  ext k j
  rw [sylvesterMap_diagonal_apply, cauchy_apply, vecMulVec_apply, Pi.neg_apply, ← sub_eq_add_neg,
    Pi.one_apply, Pi.one_apply, mul_one]
  exact mul_inv_cancel₀ (sub_ne_zero.mpr (h k j))

/-- Let $\omega, \nu \in K^n$ with $n \ge 1$ and $\omega_k \ne \nu_j$ for all $k$ and $j$. Then the
Cauchy matrix $(1/(\omega_k - \nu_j))$ has $\{\operatorname{diag}(\omega),
\operatorname{diag}(\nu)\}$-displacement rank $1$ ([golub2013matrix] §12.1.2).

Its displacement is $ee^T$, by `Matrix.sylvesterMap_diagonal_cauchy`. -/
theorem displacementRank_diagonal_cauchy {n : ℕ} {ω ν : Fin n → K} (h : ∀ k j, ω k ≠ ν j)
    (hn : n ≠ 0) : displacementRank (diagonal ω) (diagonal ν) (cauchy ω (-ν)) = 1 := by
  rw [displacementRank, sylvesterMap_diagonal_cauchy h]
  refine le_antisymm (rank_vecMulVec_le _ _) ?_
  have : NeZero n := ⟨hn⟩
  by_contra h0
  rw [not_le, Nat.lt_one_iff, rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have := congrFun (LinearMap.congr_fun h0 (Pi.single 0 1)) 0
  simp [mulVec, dotProduct] at this

/-! ### The generator update under one elimination step -/

section Schur

variable {N r : ℕ}

/-- **The generator update under one step of Gaussian elimination.** Let
$F, G, A \in K^{(N+1) \times (N+1)}$ and $R, S \in K^{(N+1) \times r}$ with $FA - AG = RS^T$.
Suppose that the first row of $F$ and the first column of $G$ vanish off the corner, and that
$\alpha = a_{11} \ne 0$. Write $$A = \begin{bmatrix} \alpha & g^T \\ f & B \end{bmatrix}$$ and
let $r_1^T$, $s_1^T$ be the first rows of $R$, $S$. Then the Schur complement
$A_1 = B - f g^T / \alpha$ satisfies $F_1 A_1 - A_1 G_1 = R_1 S_1^T$, where $F_1$, $G_1$ are the
trailing $N \times N$ blocks of $F$, $G$ and $$R_1 = R(2{:}, :) - f r_1^T / \alpha, \qquad S_1 =
S(2{:}, :) - g s_1^T / \alpha.$$ This generalizes [golub2013matrix] Theorem 12.1.1.

The source takes $F$ and $G$ diagonal. The corner hypotheses also cover the lower shift and
every pair of a lower and an upper triangular matrix. Indices in Lean are $0$-based, so $\alpha$
is `A 0 0`. -/
theorem sylvesterMap_schurComplement {F G A : Matrix (Fin (N + 1)) (Fin (N + 1)) K}
    {R S : Matrix (Fin (N + 1)) (Fin r) K} (hF : ∀ j : Fin N, F 0 j.succ = 0)
    (hG : ∀ i : Fin N, G i.succ 0 = 0) (h : sylvesterMap F G A = R * Sᵀ) (hα : A 0 0 ≠ 0) :
    sylvesterMap (F.submatrix Fin.succ Fin.succ) (G.submatrix Fin.succ Fin.succ)
        (A.submatrix Fin.succ Fin.succ -
          (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) =
      (R.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) (R 0)) *
        (S.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun j => A 0 j.succ) (S 0))ᵀ := by
  set α := A 0 0 with hαdef
  set a := α⁻¹
  have ha : a * α = 1 := inv_mul_cancel₀ hα
  have E : ∀ p q, (F * A - A * G) p q = ∑ l, R p l * S q l := fun p q => by
    have := congrFun (congrFun h p) q
    simpa only [sylvesterMap_apply, Matrix.mul_apply, transpose_apply] using this
  ext i j
  have e00 : F 0 0 * α - α * G 0 0 = ∑ l, R 0 l * S 0 l := by
    have := E 0 0
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ, hF, hG, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero] at this
    linear_combination this
  have e0j : F 0 0 * A 0 j.succ - (α * G 0 j.succ + ∑ t : Fin N, A 0 t.succ * G t.succ j.succ) =
      ∑ l, R 0 l * S j.succ l := by
    have := E 0 j.succ
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ, hF, zero_mul,
      Finset.sum_const_zero, add_zero] at this
    linear_combination this
  have ei0 : (F i.succ 0 * α + ∑ t : Fin N, F i.succ t.succ * A t.succ 0) - A i.succ 0 * G 0 0 =
      ∑ l, R i.succ l * S 0 l := by
    have := E i.succ 0
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ, hG, mul_zero,
      Finset.sum_const_zero, add_zero] at this
    linear_combination this
  have eij : (F i.succ 0 * A 0 j.succ + ∑ t : Fin N, F i.succ t.succ * A t.succ j.succ) -
      (A i.succ 0 * G 0 j.succ + ∑ t : Fin N, A i.succ t.succ * G t.succ j.succ) =
      ∑ l, R i.succ l * S j.succ l := by
    have := E i.succ j.succ
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ] at this
    linear_combination this
  have hl : sylvesterMap (F.submatrix Fin.succ Fin.succ) (G.submatrix Fin.succ Fin.succ)
      (A.submatrix Fin.succ Fin.succ -
        a • vecMulVec (fun i' : Fin N => A i'.succ 0) fun j' : Fin N => A 0 j'.succ) i j =
      (∑ t : Fin N, F i.succ t.succ * A t.succ j.succ -
          a * A 0 j.succ * ∑ t : Fin N, F i.succ t.succ * A t.succ 0) -
        (∑ t : Fin N, A i.succ t.succ * G t.succ j.succ -
          a * A i.succ 0 * ∑ t : Fin N, A 0 t.succ * G t.succ j.succ) := by
    simp only [sylvesterMap_apply, Matrix.sub_apply, Matrix.mul_apply, submatrix_apply,
      Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    congr 1
    · rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun t _ => by ring
    · rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun t _ => by ring
  have hr : ((R.submatrix Fin.succ id - a • vecMulVec (fun i' : Fin N => A i'.succ 0) (R 0)) *
      (S.submatrix Fin.succ id - a • vecMulVec (fun j' : Fin N => A 0 j'.succ) (S 0))ᵀ) i j =
      ∑ l, R i.succ l * S j.succ l - a * A 0 j.succ * ∑ l, R i.succ l * S 0 l -
        a * A i.succ 0 * ∑ l, R 0 l * S j.succ l +
        a * a * A i.succ 0 * A 0 j.succ * ∑ l, R 0 l * S 0 l := by
    simp only [Matrix.mul_apply, transpose_apply, Matrix.sub_apply, submatrix_apply,
      Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, id]
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by ring
  rw [hl, hr]
  linear_combination eij - a * A 0 j.succ * ei0 - a * A i.succ 0 * e0j +
    a ^ 2 * A i.succ 0 * A 0 j.succ * e00 +
    (F i.succ 0 * A 0 j.succ - A i.succ 0 * G 0 j.succ -
      a * A i.succ 0 * A 0 j.succ * (F 0 0 - G 0 0)) * ha

/-- **Theorem 12.1.1** of [golub2013matrix]. Let $\omega, \nu \in K^{N+1}$,
$\Omega = \operatorname{diag}(\omega)$, $\Lambda = \operatorname{diag}(\nu)$, and let
$A \in K^{(N+1) \times (N+1)}$ and $R, S \in K^{(N+1) \times r}$ with
$\Omega A - A \Lambda = RS^T$ and $\alpha = a_{11} \ne 0$. Then the Schur complement
$A_1 = B - f g^T / \alpha$ satisfies $$\operatorname{diag}(\omega_2, \dots, \omega_{N+1}) A_1 -
A_1 \operatorname{diag}(\nu_2, \dots, \nu_{N+1}) = R_1 S_1^T,$$ with $f$, $g$, $B$, $R_1$ and
$S_1$ as in `Matrix.sylvesterMap_schurComplement`. -/
theorem sylvesterMap_diagonal_schurComplement {ω ν : Fin (N + 1) → K}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) K} {R S : Matrix (Fin (N + 1)) (Fin r) K}
    (h : sylvesterMap (diagonal ω) (diagonal ν) A = R * Sᵀ) (hα : A 0 0 ≠ 0) :
    sylvesterMap (diagonal (ω ∘ Fin.succ)) (diagonal (ν ∘ Fin.succ))
        (A.submatrix Fin.succ Fin.succ -
          (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) =
      (R.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) (R 0)) *
        (S.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun j => A 0 j.succ) (S 0))ᵀ := by
  have hsub : ∀ d : Fin (N + 1) → K,
      (diagonal d).submatrix Fin.succ Fin.succ = diagonal (d ∘ Fin.succ) :=
    fun d => submatrix_diagonal _ _ (Fin.succ_injective _)
  rw [← hsub, ← hsub]
  exact sylvesterMap_schurComplement (fun j => diagonal_apply_ne _ (Fin.succ_ne_zero j).symm)
    (fun i => diagonal_apply_ne _ (Fin.succ_ne_zero i)) h hα

end Schur

/-! ### The cyclic shifts $Z_{\pm 1}$ -/

section CyclicShift

variable {n : ℕ}

/-- Let $K$ have $2 \ne 0$. Then the map $X \mapsto Z_1 X - X Z_{-1}$ on $K^{n \times n}$ is
injective. This is [golub2013matrix] P12.1.1(a), the nonsingularity that (12.1.2) requires for
(12.1.8).

From $Z_1 X = X Z_{-1}$ follows $Z_1^n X = X Z_{-1}^n$, that is, $X = -X$. -/
theorem sylvesterMap_cyclicShift_one_neg_one_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (sylvesterMap (cyclicShift n (1 : K)) (cyclicShift n (-1))) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  rw [sylvesterMap_apply, sub_eq_zero] at hX
  have hsc : SemiconjBy X (cyclicShift n (-1)) (cyclicShift n 1) := hX.symm
  have hpow := (hsc.pow_right n).eq
  rw [cyclicShift_pow_card, cyclicShift_pow_card, one_smul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, neg_one_smul, neg_eq_iff_add_eq_zero, ← two_smul K X] at hpow
  exact (smul_eq_zero.mp hpow).resolve_left h2

/-- Let $T \in K^{n \times n}$ be Toeplitz. Then the displacement $Z_1 T - T Z_{-1}$ is supported on
the first row and the last column: its entry $(i, j)$ is $0$ whenever $i$ is not the first row
and $j$ is not the last column. This is (12.1.8) of [golub2013matrix]. -/
theorem sylvesterMap_cyclicShift_toeplitz_apply {T : Matrix (Fin n) (Fin n) K} (hT : T.IsToeplitz)
    {i j : Fin n} (hi : 0 < (i : ℕ)) (hj : (j : ℕ) + 1 < n) :
    sylvesterMap (cyclicShift n 1) (cyclicShift n (-1)) T i j = 0 := by
  rw [sylvesterMap_apply, Matrix.sub_apply, cyclicShift_mul_apply_of_pos _ _ hi,
    mul_cyclicShift_apply_of_lt _ _ _ hj, sub_eq_zero]
  exact isToeplitz_iff.mp hT _ _ _ _ (by simp only; omega)

/-- Let $H \in K^{n \times n}$ be Hankel. Then the displacement $Z_1^T H - H Z_{-1}$ is supported on
the last row and the last column: its entry $(i, j)$ is $0$ whenever $i$ is not the last row and
$j$ is not the last column. This is (12.1.10) of [golub2013matrix]. -/
theorem sylvesterMap_cyclicShift_hankel_apply {H : Matrix (Fin n) (Fin n) K} (hH : H.IsHankel)
    {i j : Fin n} (hi : (i : ℕ) + 1 < n) (hj : (j : ℕ) + 1 < n) :
    sylvesterMap (cyclicShift n 1)ᵀ (cyclicShift n (-1)) H i j = 0 := by
  obtain ⟨h, rfl⟩ := hH
  rw [sylvesterMap_apply, Matrix.sub_apply, transpose_cyclicShift_mul_apply_of_lt _ _ hi,
    mul_cyclicShift_apply_of_lt _ _ _ hj, hankel_apply, hankel_apply, sub_eq_zero]
  congr 1
  simp only
  omega

end CyclicShift

/-! ### The corner-modified tridiagonal operators $Y_{00}$, $Y_{11}$ -/

section CornerTridiagonal

variable {n : ℕ}

/-- Let $T \in \mathbb{R}^{n \times n}$ be Toeplitz. Then the displacement $Y_{00} T - T Y_{11}$ is
supported on the border: its entry $(i, j)$ is $0$ whenever neither $i$ nor $j$ is the first or
the last index. This is (12.1.9) of [golub2013matrix].

At an interior entry, $t_{i-1,j} + t_{i+1,j} = t_{i,j-1} + t_{i,j+1}$. -/
theorem sylvesterMap_cornerTridiagonal_toeplitz_apply {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsToeplitz) {i j : Fin n} (hi₀ : 0 < (i : ℕ)) (hi : (i : ℕ) + 1 < n)
    (hj₀ : 0 < (j : ℕ)) (hj : (j : ℕ) + 1 < n) :
    sylvesterMap (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) T i j = 0 := by
  rw [sylvesterMap_apply, Matrix.sub_apply, cornerTridiagonal_mul_apply _ _ _ hi₀ hi,
    mul_cornerTridiagonal_apply _ _ _ _ hj₀ hj,
    isToeplitz_iff.mp hT ⟨i - 1, by omega⟩ j i ⟨j + 1, hj⟩ (by simp only; omega),
    isToeplitz_iff.mp hT ⟨i + 1, hi⟩ j i ⟨j - 1, by omega⟩ (by simp only; omega)]
  ring

/-- Let $H \in \mathbb{R}^{n \times n}$ be Hankel. Then the displacement $Y_{00} H - H Y_{11}$ is
supported on the border: its entry $(i, j)$ is $0$ whenever neither $i$ nor $j$ is the first or
the last index. This is (12.1.11) of [golub2013matrix].

At an interior entry, $h_{i-1,j} + h_{i+1,j} = h_{i,j-1} + h_{i,j+1}$. -/
theorem sylvesterMap_cornerTridiagonal_hankel_apply {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHankel) {i j : Fin n} (hi₀ : 0 < (i : ℕ)) (hi : (i : ℕ) + 1 < n)
    (hj₀ : 0 < (j : ℕ)) (hj : (j : ℕ) + 1 < n) :
    sylvesterMap (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) H i j = 0 := by
  obtain ⟨h, rfl⟩ := hH
  rw [sylvesterMap_apply, Matrix.sub_apply, cornerTridiagonal_mul_apply _ _ _ hi₀ hi,
    mul_cornerTridiagonal_apply _ _ _ _ hj₀ hj]
  simp only [hankel_apply]
  rw [show (i : ℕ) - 1 + j = i + (j - 1) by omega, show (i : ℕ) + 1 + j = i + (j + 1) by omega]
  ring

/-- Let $v_1, \dots, v_n \in \mathbb{R}^n$ be pairwise orthogonal and nonzero. A vector
$w \in \mathbb{R}^n$ orthogonal to every $v_k$ is zero. -/
private theorem eq_zero_of_forall_dotProduct_eq_zero {v : Fin n → Fin n → ℝ}
    (horth : ∀ k l, k ≠ l → v k ⬝ᵥ v l = 0) (hpos : ∀ k, v k ⬝ᵥ v k ≠ 0) {w : Fin n → ℝ}
    (hw : ∀ k, v k ⬝ᵥ w = 0) : w = 0 := by
  set V : Matrix (Fin n) (Fin n) ℝ := of v
  have hVV : V * Vᵀ = diagonal fun k => v k ⬝ᵥ v k := by
    ext k l
    rw [Matrix.mul_apply, diagonal_apply]
    change v k ⬝ᵥ v l = _
    split_ifs with h
    · rw [h]
    · exact horth k l h
  have hD : (diagonal fun k => v k ⬝ᵥ v k) * diagonal (fun k => (v k ⬝ᵥ v k)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hpos k)
  have hinv : (Vᵀ * diagonal fun k => (v k ⬝ᵥ v k)⁻¹) * V = 1 := by
    rw [mul_eq_one_comm, ← Matrix.mul_assoc, hVV, hD]
  have hVw : V *ᵥ w = 0 := funext hw
  rw [← one_mulVec w, ← hinv, ← mulVec_mulVec, hVw, mulVec_zero]

/-- For $0 \le k, l < n$, $2 \cos((k+1)\pi/(n+1)) \ne 2 \cos(l\pi/n)$: the eigenvalues of $Y_{00}$
and of $Y_{11}$ are distinct. -/
private theorem cos_ne_cos {k l : Fin n} :
    2 * Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) ≠
      2 * Real.cos ((l : ℕ) * Real.pi / n) := by
  intro h
  have hn : (0 : ℝ) < n := by exact_mod_cast k.pos
  have hk := k.isLt
  have hl := l.isLt
  have h1 : (((k : ℕ) : ℝ) + 1) * Real.pi / ((n : ℝ) + 1) = (l : ℕ) * Real.pi / n := by
    refine Real.injOn_cos ⟨by positivity, ?_⟩ ⟨by positivity, ?_⟩ (by linarith)
    · rw [div_le_iff₀ (by positivity)]
      have : ((k : ℕ) : ℝ) + 1 ≤ n + 1 := by exact_mod_cast (by omega : (k : ℕ) + 1 ≤ n + 1)
      have := mul_le_mul_of_nonneg_right this Real.pi_pos.le
      linarith
    · rw [div_le_iff₀ hn]
      have : ((l : ℕ) : ℝ) ≤ n := by exact_mod_cast hl.le
      have := mul_le_mul_of_nonneg_right this Real.pi_pos.le
      linarith
  have h2 : (((k : ℕ) + 1) * n : ℕ) = ((l : ℕ) * (n + 1) : ℕ) := by
    rw [div_eq_div_iff (by positivity) hn.ne'] at h1
    have h1' : (((k : ℕ) : ℝ) + 1) * n * Real.pi = (l : ℕ) * ((n : ℝ) + 1) * Real.pi := by
      linear_combination h1
    exact_mod_cast mul_right_cancel₀ Real.pi_pos.ne' h1'
  have hdvd : n + 1 ∣ (k + 1) * n := ⟨l, by rw [h2]; ring⟩
  have hcop : Nat.Coprime (n + 1) n := by
    rw [Nat.coprime_self_add_left]
    exact Nat.coprime_one_left n
  have := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_right hdvd)
  omega

/-- The map $X \mapsto Y_{00} X - X Y_{11}$ on $\mathbb{R}^{n \times n}$ is injective. This is
[golub2013matrix] P12.1.1(b), the condition $\lambda(Y_{00}) \cap \lambda(Y_{11}) = \emptyset$
of the source.

The spectra $\{2 \cos((k+1)\pi/(n+1))\}$ and $\{2 \cos(l\pi/n)\}$ are disjoint, and both
matrices have orthogonal eigenbases (the DST-I and DCT-II vectors $s_k$ and $c_l$). So $s_k^T
(Y_{00} X - X Y_{11}) c_l = (\lambda_k - \mu_l) s_k^T X c_l$ forces $X = 0$. -/
theorem sylvesterMap_cornerTridiagonal_injective :
    Function.Injective (sylvesterMap (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  rw [sylvesterMap_apply, sub_eq_zero, cornerTridiagonal_zero_zero] at hX
  have hsymm : (symmTridiagonalToeplitz n 1 0)ᵀ = symmTridiagonalToeplitz n 1 0 := by
    rw [← cornerTridiagonal_zero_zero]
    exact cornerTridiagonal_transpose 0 0
  -- `X c_l = 0` for every DCT-II vector `c_l`
  have hcol : ∀ l : Fin n, X *ᵥ cosineIIVec n l = 0 := by
    intro l
    refine eq_zero_of_forall_dotProduct_eq_zero (v := sineVec n)
      (fun k k' h => by rw [dotProduct_sineVec, ite_eq_right h])
      (fun k => by rw [dotProduct_sineVec, ite_eq_left rfl]; positivity) fun k => ?_
    have e1 : sineVec n k ⬝ᵥ (symmTridiagonalToeplitz n 1 0 *ᵥ (X *ᵥ cosineIIVec n l)) =
        (2 * Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))) *
          (sineVec n k ⬝ᵥ (X *ᵥ cosineIIVec n l)) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hsymm, symmTridiagonalToeplitz_mulVec_sineVec,
        smul_dotProduct, smul_eq_mul]
      ring
    have e2 : sineVec n k ⬝ᵥ (X *ᵥ (cornerTridiagonal n 1 1 *ᵥ cosineIIVec n l)) =
        (2 * Real.cos ((l : ℕ) * Real.pi / n)) * (sineVec n k ⬝ᵥ (X *ᵥ cosineIIVec n l)) := by
      rw [cornerTridiagonal_one_one_mulVec_cosineIIVec, mulVec_smul, dotProduct_smul, smul_eq_mul]
    rw [mulVec_mulVec, hX, ← mulVec_mulVec, e2] at e1
    have := sub_eq_zero.mpr e1
    rw [← sub_mul, mul_eq_zero] at this
    exact this.resolve_left (sub_ne_zero.mpr (cos_ne_cos (k := k) (l := l)).symm)
  -- then every row of `X` is orthogonal to the DCT-II basis
  ext i j
  have hrow : X i = 0 := by
    refine eq_zero_of_forall_dotProduct_eq_zero (v := cosineIIVec n)
      (fun k k' h => by rw [dotProduct_cosineIIVec, ite_eq_right h])
      (fun k => by
        have : (0 : ℝ) < n := by exact_mod_cast k.pos
        rw [dotProduct_cosineIIVec, ite_eq_left rfl]
        split_ifs <;> positivity) fun l => ?_
    rw [dotProduct_comm]
    exact congrFun (hcol l) i
  simpa using congrFun hrow j

end CornerTridiagonal

/-! ### Displacement rank bounds -/

section Bounds

/-- Let $F, G, A \in K^{n \times n}$ and $r \in \mathbb{N}$. The $\{F, G\}$-displacement rank of $A$
is at most $r$ if and only if $FA - AG = RS^T$ for some $R, S \in K^{n \times r}$. So
**generators exist exactly up to the displacement rank**. This is (12.1.3) of [golub2013matrix]. -/
theorem displacementRank_le_iff_exists {n : Type*} [Fintype n] {F G A : Matrix n n K} {r : ℕ} :
    displacementRank F G A ≤ r ↔
      ∃ R S : Matrix n (Fin r) K, sylvesterMap F G A = R * Sᵀ :=
  rank_le_iff_exists_mul_transpose _ r

/-- Let $\omega, \nu \in K^{N+1}$ and let $A \in K^{(N+1) \times (N+1)}$ have
$\{\operatorname{diag}(\omega), \operatorname{diag}(\nu)\}$-displacement rank at most $r$, with
$a_{11} \ne 0$. Then the Schur complement $A_1$ after one elimination step has
$\{\operatorname{diag}(\omega_2, \dots), \operatorname{diag}(\nu_2, \dots)\}$-displacement rank
at most $r$. This is the consequence of Theorem 12.1.1 displayed after its proof in
[golub2013matrix] §12.1.3. -/
theorem displacementRank_diagonal_schurComplement_le {N r : ℕ} {ω ν : Fin (N + 1) → K}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) K}
    (h : displacementRank (diagonal ω) (diagonal ν) A ≤ r) (hα : A 0 0 ≠ 0) :
    displacementRank (diagonal (ω ∘ Fin.succ)) (diagonal (ν ∘ Fin.succ))
      (A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) ≤ r := by
  obtain ⟨R, S, hRS⟩ := displacementRank_le_iff_exists.mp h
  exact displacementRank_le_iff_exists.mpr ⟨_, _, sylvesterMap_diagonal_schurComplement hRS hα⟩

variable {n : ℕ}

/-- A square matrix that vanishes outside row $a$ and column $b$ has rank at most $2$. -/
private theorem rank_le_two_of_forall {A : Matrix (Fin n) (Fin n) K} (a b : Fin n)
    (h : ∀ i j, i ≠ a → j ≠ b → A i j = 0) : A.rank ≤ 2 :=
  (rank_le_card_add_card_of_forall_ne_zero A {a} {b} fun i j hij => by
    by_contra hc
    simp only [Finset.mem_singleton, not_or] at hc
    exact hij (h i j hc.1 hc.2)).trans (by simp)

/-- A square matrix that vanishes outside rows $a, b$ and columns $a, b$ has rank at most $4$. -/
private theorem rank_le_four_of_forall {A : Matrix (Fin n) (Fin n) K} (a b : Fin n)
    (h : ∀ i j, i ≠ a → i ≠ b → j ≠ a → j ≠ b → A i j = 0) : A.rank ≤ 4 := by
  have hc : ({a, b} : Finset (Fin n)).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  refine (rank_le_card_add_card_of_forall_ne_zero A {a, b} {a, b} fun i j hij => ?_).trans
    (by omega)
  by_contra hne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
  exact hij (h i j hne.1.1 hne.1.2 hne.2.1 hne.2.2)

/-- The empty matrix has rank $0$. -/
private theorem rank_fin_zero (A : Matrix (Fin 0) (Fin 0) K) : A.rank = 0 :=
  Nat.le_zero.mp ((rank_le_card_width A).trans (by simp))

/-- A Toeplitz matrix $T \in K^{n \times n}$ has $\{Z_1, Z_{-1}\}$-displacement rank at most $2$.
This is (12.1.8) of [golub2013matrix].

The displacement is supported on the first row and the last column. -/
theorem displacementRank_cyclicShift_toeplitz_le {T : Matrix (Fin n) (Fin n) K}
    (hT : T.IsToeplitz) : displacementRank (cyclicShift n 1) (cyclicShift n (-1)) T ≤ 2 := by
  rcases n with _ | N
  · rw [displacementRank, rank_fin_zero]; omega
  refine rank_le_two_of_forall 0 (Fin.last N) fun i j hi hj => ?_
  have hi' : (i : ℕ) ≠ 0 := fun h' => hi (Fin.ext h')
  have hj' : (j : ℕ) ≠ N := fun h' => hj (Fin.ext h')
  exact sylvesterMap_cyclicShift_toeplitz_apply hT (by omega) (by omega)

/-- A Hankel matrix $H \in K^{n \times n}$ has $\{Z_1^T, Z_{-1}\}$-displacement rank at most $2$.
This is (12.1.10) of [golub2013matrix].

The displacement is supported on the last row and the last column. -/
theorem displacementRank_cyclicShift_hankel_le {H : Matrix (Fin n) (Fin n) K}
    (hH : H.IsHankel) : displacementRank (cyclicShift n 1)ᵀ (cyclicShift n (-1)) H ≤ 2 := by
  rcases n with _ | N
  · rw [displacementRank, rank_fin_zero]; omega
  refine rank_le_two_of_forall (Fin.last N) (Fin.last N) fun i j hi hj => ?_
  have hi' : (i : ℕ) ≠ N := fun h' => hi (Fin.ext h')
  have hj' : (j : ℕ) ≠ N := fun h' => hj (Fin.ext h')
  exact sylvesterMap_cyclicShift_hankel_apply hH (by omega) (by omega)

/-- A real matrix whose $\{Y_{00}, Y_{11}\}$-displacement vanishes off the border has
$\{Y_{00}, Y_{11}\}$-displacement rank at most $4$. -/
private theorem displacementRank_cornerTridiagonal_le_of_border {A : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j : Fin n, 0 < (i : ℕ) → (i : ℕ) + 1 < n → 0 < (j : ℕ) → (j : ℕ) + 1 < n →
      sylvesterMap (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) A i j = 0) :
    displacementRank (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) A ≤ 4 := by
  rcases n with _ | N
  · rw [displacementRank, rank_fin_zero]; omega
  refine rank_le_four_of_forall 0 (Fin.last N) fun i j hi0 hiN hj0 hjN => ?_
  have hi0' : (i : ℕ) ≠ 0 := fun h' => hi0 (Fin.ext h')
  have hiN' : (i : ℕ) ≠ N := fun h' => hiN (Fin.ext h')
  have hj0' : (j : ℕ) ≠ 0 := fun h' => hj0 (Fin.ext h')
  have hjN' : (j : ℕ) ≠ N := fun h' => hjN (Fin.ext h')
  exact h i j (by omega) (by omega) (by omega) (by omega)

/-- A Toeplitz matrix $T \in \mathbb{R}^{n \times n}$ has $\{Y_{00}, Y_{11}\}$-displacement rank at
most $4$. This is (12.1.9) of [golub2013matrix].

The displacement is supported on the border. -/
theorem displacementRank_cornerTridiagonal_toeplitz_le {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsToeplitz) :
    displacementRank (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) T ≤ 4 :=
  displacementRank_cornerTridiagonal_le_of_border fun _ _ hi₀ hi hj₀ hj =>
    sylvesterMap_cornerTridiagonal_toeplitz_apply hT hi₀ hi hj₀ hj

/-- A Hankel matrix $H \in \mathbb{R}^{n \times n}$ has $\{Y_{00}, Y_{11}\}$-displacement rank at
most $4$. This is (12.1.11) of [golub2013matrix]. -/
theorem displacementRank_cornerTridiagonal_hankel_le {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHankel) :
    displacementRank (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) H ≤ 4 :=
  displacementRank_cornerTridiagonal_le_of_border fun _ _ hi₀ hi hj₀ hj =>
    sylvesterMap_cornerTridiagonal_hankel_apply hH hi₀ hi hj₀ hj

/-- Let $T, H \in \mathbb{R}^{n \times n}$ with $T$ Toeplitz and $H$ Hankel. Then $T + H$ has
$\{Y_{00}, Y_{11}\}$-displacement rank at most $4$. This is the display after (12.1.11) in
[golub2013matrix].

The displacement is linear, and both displacements vanish off the border. -/
theorem displacementRank_cornerTridiagonal_toeplitz_add_hankel_le
    {T H : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsToeplitz) (hH : H.IsHankel) :
    displacementRank (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) (T + H) ≤ 4 :=
  displacementRank_cornerTridiagonal_le_of_border fun _ _ hi₀ hi hj₀ hj => by
    rw [map_add, Matrix.add_apply, sylvesterMap_cornerTridiagonal_toeplitz_apply hT hi₀ hi hj₀ hj,
      sylvesterMap_cornerTridiagonal_hankel_apply hH hi₀ hi hj₀ hj, add_zero]

end Bounds

end Matrix
