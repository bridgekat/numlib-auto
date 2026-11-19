/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Projection.Gap
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.CSDecomposition
import NumlibSurface.GolubVanLoan.Chapter02.Section04

/-!
# Golub and Van Loan, Section 2.5: Subspace metrics

This module formalizes §2.5 of [golub2013matrix]. A matrix $P \in \mathbb{R}^{n \times n}$ is the
orthogonal projection onto a subspace $S \subseteq \mathbb{R}^n$ if $\operatorname{ran}(P) = S$,
$P^2 = P$ and $P^T = P$. The module proves the basic facts about orthogonal projections of §2.5.1
(uniqueness, $P = VV^T$ for an orthonormal basis $V$ of $S$, and $vv^T / v^Tv$ for a line), and the
four projections that an SVD of $A$ gives onto $\operatorname{null}(A)$, $\operatorname{ran}(A)$ and
their orthogonal complements (§2.5.2). The distance between two subspaces is
$\operatorname{dist}(S_1, S_2) = \|P_1 - P_2\|_2$ (2.5.1), where $P_i$ is the orthogonal projection
onto $S_i$. Theorem 2.5.1 computes it from orthogonal bases, $\operatorname{dist}(S_1, S_2) =
\|W_1^T Z_2\|_2$, and §2.5.3 shows $0 \le \operatorname{dist} \le 1$ with the cases
$\operatorname{dist} = 0$ and $\operatorname{dist} = 1$. The module ends with the CS decomposition,
in its thin form (Theorem 2.5.2) and its full form (Theorem 2.5.3).

The proofs specialize the backbone module `Numlib.Analysis.InnerProductSpace.Projection.Gap`, the
orthogonal projections of Mathlib (`Submodule.starProjection`, `LinearMap.IsSymmetricProjection`),
the matrix form `Matrix.gap_range_eq_l2_opNorm_conjTranspose_mul` of Theorem 2.5.1, and the backbone
module `Numlib.LinearAlgebra.Matrix.CSDecomposition` (`Matrix.exists_isThinCSD`,
`Matrix.exists_isCSD`).

## Main definitions

* §2.5.1, `GolubVanLoan.Chapter02.IsOrthogonalProjection`: $P$ is the orthogonal projection onto
  $S$.
* Equation (2.5.1), `GolubVanLoan.Chapter02.subspaceDist`: the distance $\operatorname{dist}(S_1,
  S_2) = \|P_1 - P_2\|_2$ between subspaces.

## Main results

* §2.5.1, `GolubVanLoan.Chapter02.IsOrthogonalProjection.iff_toEuclideanLin_eq`: $P$ is the
  orthogonal projection onto $S$ if and only if it acts as the orthogonal projection
  `S.starProjection` of Mathlib.
* §2.5.1, `GolubVanLoan.Chapter02.IsOrthogonalProjection.mem_and_sub_mem_orthogonal`: $Px \in S$ and
  $(I - P)x \in S^\perp$.
* §2.5.1, `GolubVanLoan.Chapter02.norm_sq_sub_mulVec_eq`: the identity $\|(P_1 - P_2)z\|_2^2 = (P_1
  z)^T (I - P_2) z + (P_2 z)^T (I - P_1) z$.
* §2.5.1, `GolubVanLoan.Chapter02.IsOrthogonalProjection.unique`: the orthogonal projection onto a
  subspace is unique.
* §2.5.1, `GolubVanLoan.Chapter02.isOrthogonalProjection_mul_transpose`: $VV^T$ is the orthogonal
  projection onto $\operatorname{ran}(V)$ when $V^T V = I$.
* §2.5.1, `GolubVanLoan.Chapter02.isOrthogonalProjection_vecMulVec`: $vv^T / v^T v$ is the
  orthogonal projection onto $\operatorname{span}\{v\}$.
* §2.5.2, `GolubVanLoan.Chapter02.svd_projections`: the column blocks of the SVD factors give the
  orthogonal projections onto $\operatorname{null}(A)^\perp$, $\operatorname{null}(A)$,
  $\operatorname{ran}(A)$ and $\operatorname{ran}(A)^\perp$.
* Equation (2.5.1), `GolubVanLoan.Chapter02.subspaceDist_eq_lpOpNorm_sub`: $\operatorname{dist}(S_1,
  S_2) = \|P_1 - P_2\|_2$ for the projection matrices.
* Theorem 2.5.1, `GolubVanLoan.Chapter02.theorem_2_5_1`: $\operatorname{dist}(S_1, S_2) = \|W_1^T
  Z_2\|_2 = \|Z_1^T W_2\|_2$.
* §2.5.3, `GolubVanLoan.Chapter02.subspaceDist_mem_Icc`:
  $0 \le \operatorname{dist}(S_1, S_2) \le 1$.
* §2.5.3, `GolubVanLoan.Chapter02.subspaceDist_eq_zero`: $\operatorname{dist}(S_1, S_2) = 0$ if and
  only if $S_1 = S_2$.
* §2.5.3, `GolubVanLoan.Chapter02.subspaceDist_eq_one`: for $\dim S_1 = \dim S_2$,
  $\operatorname{dist}(S_1, S_2) = 1$ if and only if $S_1 \cap S_2^\perp \neq \{0\}$.
* Theorem 2.5.2, `GolubVanLoan.Chapter02.theorem_2_5_2`: the thin CS decomposition.
* Theorem 2.5.3, `GolubVanLoan.Chapter02.theorem_2_5_3`: the CS decomposition.

## Proof outline

Theorem 2.5.1 is not proved by the argument of the source with the blocks $Q_{12}$ and $Q_{21}$ of
$Q = W^T Z$. It applies the backbone formula for the one-sided gap of two subspaces of equal
dimension, `Matrix.gap_range_eq_l2_opNorm_conjTranspose_mul`, once for $(W, Z)$ and once for
$(Z, W)$.

## Conventions

* Subspaces of $\mathbb{R}^n$ are `Submodule ℝ (EuclideanSpace ℝ (Fin n))`. The range
  $\operatorname{ran}(P)$ is `LinearMap.range (Matrix.toEuclideanLin P)`, and
  $\operatorname{span}\{v\}$ is `ℝ ∙ WithLp.toLp 2 v`.
* The column blocks $W(:, 1{:}k)$ and $W(:, k{+}1{:}n)$ of $W \in \mathbb{R}^{n \times n}$ are
  `W.submatrix id` along `Fin.castLE` and along `Fin.cast _ ∘ Fin.natAdd k`.
* The CS decomposition is stated in the block form of the source with `Matrix.fromRows` and
  `Matrix.fromBlocks`. Its diagonal-like blocks are `Matrix.rectDiagonal`,
  `Matrix.shiftedRectDiagonal` and `Matrix.csdUpperRight` of the angles `θ : ℕ → ℝ`, with 0-based
  indices. The first $p$ angles are $0$, which gives the identity blocks.

## Implementation notes

* An orthogonal projection matrix is the predicate `GolubVanLoan.Chapter02.IsOrthogonalProjection P
  S`. It is identified with the orthogonal projection `S.starProjection` of Mathlib by
  `GolubVanLoan.Chapter02.IsOrthogonalProjection.iff_toEuclideanLin_eq`.
* The distance `GolubVanLoan.Chapter02.subspaceDist` is the gap `Submodule.gap` of the backbone, the
  operator norm of the difference of the two orthogonal projections. The source defines the distance
  only for $\dim S_1 = \dim S_2$. The Lean definition applies to every pair of subspaces, and the
  theorems that need equal dimensions have that hypothesis.

## Deviations from the source

* **Section 2.5.1, projection onto a line** (reading). The quotient requires $v \ne 0$.
  See `GolubVanLoan.Chapter02.isOrthogonalProjection_vecMulVec`.
* **Equation (2.5.1) and the bounds in §2.5.3** (generalization). The distance, its matrix
  formula and the bounds $0 \le \operatorname{dist} \le 1$ apply to unequal dimensions too.
  See `GolubVanLoan.Chapter02.subspaceDist`,
  `GolubVanLoan.Chapter02.subspaceDist_eq_lpOpNorm_sub` and
  `GolubVanLoan.Chapter02.subspaceDist_mem_Icc`.
* **Section 2.5.3, $\operatorname{dist}(S_1, S_2) = 0 \Rightarrow S_1 = S_2$** (generalization). The
  source states an implication. The theorem is an equivalence and needs no hypothesis on the
  dimensions. See `GolubVanLoan.Chapter02.subspaceDist_eq_zero`.
* **Section 2.5.3, $\operatorname{dist}(S_1, S_2) = 1 \Rightarrow S_1 \cap S_2^\perp \neq \{0\}$**
  (generalization). The source states an implication. The theorem is an equivalence. See
  `GolubVanLoan.Chapter02.subspaceDist_eq_one`.
* **Theorem 2.5.2** (typo). The right-hand side stacks the rectangular diagonal matrices
  $C_0$ and $S_0$, labeled $C$ and $S$ in the source display.
  See `GolubVanLoan.Chapter02.theorem_2_5_2`.
* **Theorem 2.5.3** (generalization). The decomposition also holds when $m_1 < m_2$.
  See `GolubVanLoan.Chapter02.theorem_2_5_3`.

## Not formalized

* **The two example CS patterns after Theorem 2.5.3.** They are examples.
* **Equation (2.5.2).** It only names $Q = W^T Z$ inside a proof.
-/

open Matrix WithLp

namespace GolubVanLoan.Chapter02

variable {m n k : ℕ}

/-! ### §2.5.1 Orthogonal projections -/

/-- **Section 2.5.1** of [golub2013matrix], definition of an orthogonal projection. A matrix
$P \in \mathbb{R}^{n \times n}$ is the **orthogonal projection** onto a subspace
$S \subseteq \mathbb{R}^n$ if $\operatorname{ran}(P) = S$, $P^2 = P$ and $P^T = P$.

The range is `LinearMap.range (Matrix.toEuclideanLin P)`. -/
structure IsOrthogonalProjection (P : Matrix (Fin n) (Fin n) ℝ)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop where
  /-- The range of $P$ is $S$. -/
  range_eq : LinearMap.range (toEuclideanLin P) = S
  /-- The matrix $P$ is idempotent, $P^2 = P$. -/
  mul_self : P * P = P
  /-- The matrix $P$ is symmetric, $P^T = P$. -/
  transpose_eq : Pᵀ = P

/-- The orthogonal projection of Mathlib onto a subspace $S$ of `EuclideanSpace ℝ (Fin n)` is a
symmetric projection. -/
private theorem isSymmetricProjection_starProjection' (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    (S.starProjection : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _).IsSymmetricProjection :=
  ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap S.isIdempotentElem_starProjection,
    S.starProjection_isSymmetric⟩

/-- **Section 2.5.1** of [golub2013matrix]. A matrix $P \in \mathbb{R}^{n \times n}$ is the
orthogonal projection onto a subspace $S \subseteq \mathbb{R}^n$ if and only if $Px$ is the
orthogonal projection of $x$ onto $S$ for every $x \in \mathbb{R}^n$.

The orthogonal projection of $x$ is `S.starProjection x` of Mathlib, and $P$ acts on
$\mathbb{R}^n$ as `Matrix.toEuclideanLin P`. -/
theorem IsOrthogonalProjection.iff_toEuclideanLin_eq {P : Matrix (Fin n) (Fin n) ℝ}
    {S : Submodule ℝ (EuclideanSpace ℝ (Fin n))} :
    IsOrthogonalProjection P S ↔
      toEuclideanLin P = (S.starProjection : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _) := by
  have hS := isSymmetricProjection_starProjection' S
  have hrange : LinearMap.range (S.starProjection : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _) = S :=
    S.range_starProjection
  constructor
  · rintro ⟨hr, hmul, htr⟩
    have hP : (toEuclideanLin P).IsSymmetricProjection := by
      refine ⟨?_, isSymmetric_toEuclideanLin_iff.2 ?_⟩
      · change toEuclideanLin P ∘ₗ toEuclideanLin P = toEuclideanLin P
        rw [← toEuclideanLin_mul, hmul]
      · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, htr]
    exact hP.ext hS (hr.trans hrange.symm)
  · intro h
    refine ⟨h ▸ hrange, toEuclideanLin.injective ?_, ?_⟩
    · rw [toEuclideanLin_mul, h]
      exact ContinuousLinearMap.IsIdempotentElem.toLinearMap S.isIdempotentElem_starProjection
    · have hH : P.IsHermitian := isSymmetric_toEuclideanLin_iff.1 (h ▸ S.starProjection_isSymmetric)
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at hH
      exact hH

/-- **Section 2.5.1** of [golub2013matrix]. If $P \in \mathbb{R}^{n \times n}$ is the orthogonal
projection onto $S \subseteq \mathbb{R}^n$, then for every $x \in \mathbb{R}^n$,
$$Px \in S, \qquad (I - P)x \in S^\perp.$$

The source says that this is easy to show. -/
theorem IsOrthogonalProjection.mem_and_sub_mem_orthogonal {P : Matrix (Fin n) (Fin n) ℝ}
    {S : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (hP : IsOrthogonalProjection P S)
    (x : EuclideanSpace ℝ (Fin n)) :
    toEuclideanLin P x ∈ S ∧ toEuclideanLin (1 - P) x ∈ Sᗮ := by
  have h := IsOrthogonalProjection.iff_toEuclideanLin_eq.1 hP
  rw [map_sub, toEuclideanLin_one, LinearMap.sub_apply, h]
  exact ⟨S.starProjection_apply_mem x, S.sub_starProjection_mem_orthogonal x⟩

/-- **Section 2.5.1** of [golub2013matrix], the display before (2.5.1). Let
$P_1, P_2 \in \mathbb{R}^{n \times n}$ be the orthogonal projections onto subspaces $S_1$ and
$S_2$ of $\mathbb{R}^n$. Then for every $z \in \mathbb{R}^n$,
$$\|(P_1 - P_2)z\|_2^2 = (P_1 z)^T (I - P_2) z + (P_2 z)^T (I - P_1) z.$$
-/
theorem norm_sq_sub_mulVec_eq {P₁ P₂ : Matrix (Fin n) (Fin n) ℝ}
    {S₁ S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h₁ : IsOrthogonalProjection P₁ S₁)
    (h₂ : IsOrthogonalProjection P₂ S₂) (z : Fin n → ℝ) :
    ‖WithLp.toLp 2 ((P₁ - P₂) *ᵥ z)‖ ^ 2 =
      (P₁ *ᵥ z) ⬝ᵥ ((1 - P₂) *ᵥ z) + (P₂ *ᵥ z) ⬝ᵥ ((1 - P₁) *ᵥ z) := by
  have e₁ := IsOrthogonalProjection.iff_toEuclideanLin_eq.1 h₁
  have e₂ := IsOrthogonalProjection.iff_toEuclideanLin_eq.1 h₂
  have hk : ∀ (P : Matrix (Fin n) (Fin n) ℝ) (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
      toEuclideanLin P = (S.starProjection : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _) →
        S.starProjection (WithLp.toLp 2 z) = WithLp.toLp 2 (P *ᵥ z) := fun P S hPS => by
    rw [← ContinuousLinearMap.coe_coe, ← hPS, toEuclideanLin_toLp]
  have h := S₁.norm_starProjection_sub_apply_sq S₂ (WithLp.toLp 2 z)
  rw [hk P₁ S₁ e₁, hk P₂ S₂ e₂, ← WithLp.toLp_sub, ← WithLp.toLp_sub, ← WithLp.toLp_sub] at h
  rw [sub_mulVec, h, sub_mulVec, sub_mulVec, one_mulVec, EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- **Section 2.5.1** of [golub2013matrix], uniqueness. If $P_1, P_2 \in \mathbb{R}^{n \times n}$
are both the orthogonal projection onto the same subspace $S \subseteq \mathbb{R}^n$, then
$P_1 = P_2$. -/
theorem IsOrthogonalProjection.unique {P₁ P₂ : Matrix (Fin n) (Fin n) ℝ}
    {S : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h₁ : IsOrthogonalProjection P₁ S)
    (h₂ : IsOrthogonalProjection P₂ S) : P₁ = P₂ :=
  toEuclideanLin.injective ((IsOrthogonalProjection.iff_toEuclideanLin_eq.1 h₁).trans
    (IsOrthogonalProjection.iff_toEuclideanLin_eq.1 h₂).symm)

/-- **Section 2.5.1** of [golub2013matrix]. Let $V = [v_1 \mid \dots \mid v_k] \in \mathbb{R}^{n
\times k}$ have orthonormal columns, $V^T V = I$, and let $S = \operatorname{ran}(V)$. Then
$P = VV^T$ is the orthogonal projection onto $S$. -/
theorem isOrthogonalProjection_mul_transpose {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1)
    {S : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (hS : LinearMap.range (toEuclideanLin V) = S) :
    IsOrthogonalProjection (V * Vᵀ) S := by
  have hVVV : V * Vᵀ * V = V := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  refine ⟨le_antisymm ?_ ?_, ?_, ?_⟩
  · rw [← hS, toEuclideanLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rw [← hS]
    calc LinearMap.range (toEuclideanLin V) = LinearMap.range (toEuclideanLin (V * Vᵀ * V)) := by
          rw [hVVV]
      _ ≤ LinearMap.range (toEuclideanLin (V * Vᵀ)) := by
          rw [toEuclideanLin_mul (V * Vᵀ) V]
          exact LinearMap.range_comp_le_range _ _
  · rw [← Matrix.mul_assoc, hVVV]
  · rw [transpose_mul, transpose_transpose]

/-- **Section 2.5.1** of [golub2013matrix]. Let $v \in \mathbb{R}^n$ with $v \neq 0$. Then
$$P = \frac{v v^T}{v^T v}$$
is the orthogonal projection onto $\operatorname{span}\{v\}$.

**Reading.** The source leaves $v \ne 0$ implicit in the quotient $vv^T/(v^Tv)$. -/
theorem isOrthogonalProjection_vecMulVec {v : Fin n → ℝ} (hv : v ≠ 0) :
    IsOrthogonalProjection ((1 / (v ⬝ᵥ v)) • vecMulVec v v) (ℝ ∙ WithLp.toLp 2 v) := by
  have hvv : v ⬝ᵥ v ≠ 0 := by
    intro h
    exact hv (dotProduct_self_eq_zero.1 h)
  have hPv : ((1 / (v ⬝ᵥ v)) • vecMulVec v v) *ᵥ v = v := smul_vecMulVec_mulVec_self hv
  have hPx : ∀ x : Fin n → ℝ,
      ((1 / (v ⬝ᵥ v)) • vecMulVec v v) *ᵥ x = ((1 / (v ⬝ᵥ v)) * (v ⬝ᵥ x)) • v := fun x => by
    rw [smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  refine ⟨le_antisymm ?_ ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [toEuclideanLin_apply, hPx, WithLp.toLp_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨WithLp.toLp 2 v, by rw [toEuclideanLin_toLp, hPv]⟩
  · rw [smul_mul_smul_comm, vecMulVec_mul_vecMulVec]
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  · rw [transpose_smul, transpose_vecMulVec]

/-! ### §2.5.2 SVD-related projections -/

/-- If $W \in \mathbb{R}^{n \times n}$ is orthogonal, the columns of $W$ selected along an injective
map $e$ are orthonormal. -/
private theorem transpose_mul_submatrix_eq_one {k : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W ∈ orthogonalGroup (Fin n) ℝ) {e : Fin k → Fin n} (he : Function.Injective e) :
    (W.submatrix id e)ᵀ * W.submatrix id e = 1 := by
  rw [transpose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
    (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hW]
  exact submatrix_one e he

/-- The map $j \mapsto k + j$ from `Fin (n - k)` to `Fin n`, which selects the trailing column block
$W(:, k{+}1{:}n)$, is injective. -/
private theorem cast_natAdd_injective {k : ℕ} (hk : k ≤ n) :
    Function.Injective (Fin.cast (Nat.add_sub_of_le hk) ∘ Fin.natAdd k : Fin (n - k) → Fin n) :=
  (Fin.cast_injective _).comp (Fin.natAdd_injective _ k)

/-- If $W \in \mathbb{R}^{n \times n}$ is orthogonal and $k \le n$, the ranges of the column blocks
$W(:, 1{:}k)$ and $W(:, k{+}1{:}n)$ are orthogonal complements of each other. -/
private theorem orthogonal_range_castLE_eq {k : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W ∈ orthogonalGroup (Fin n) ℝ) (hk : k ≤ n) :
    (LinearMap.range (toEuclideanLin (W.submatrix id (Fin.castLE hk))))ᗮ =
      LinearMap.range
        (toEuclideanLin (W.submatrix id (Fin.cast (Nat.add_sub_of_le hk) ∘ Fin.natAdd k))) :=
  orthogonal_range_submatrix_eq hW (Fin.castLE_injective hk) (cast_natAdd_injective hk)
    (fun a b h => by
      have := congrArg Fin.val h
      simp only [Function.comp_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_castLE] at this
      omega)
    (Nat.add_sub_of_le hk)

/-- For $k \le n$, the span of the columns $j \ge k$ (0-based) of $W \in \mathbb{R}^{n \times n}$ is
the range of the trailing block $W(:, k{+}1{:}n)$. -/
private theorem span_image_le_eq_range {k : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hk : k ≤ n) :
    Submodule.span ℝ ((fun j => toLp 2 (W.col j)) '' {j : Fin n | k ≤ (j : ℕ)}) =
      LinearMap.range
        (toEuclideanLin (W.submatrix id (Fin.cast (Nat.add_sub_of_le hk) ∘ Fin.natAdd k))) := by
  rw [range_toEuclideanLin_eq_span_col]
  congr 1
  ext v
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : k ≤ (j : ℕ) := hj
    refine ⟨⟨j - k, by have := j.isLt; omega⟩, ?_⟩
    have hjk : (Fin.cast (Nat.add_sub_of_le hk) ∘ Fin.natAdd k) ⟨j - k, by have := j.isLt; omega⟩ =
        j := by
      ext
      simp only [Function.comp_apply, Fin.val_cast, Fin.val_natAdd]
      omega
    ext i
    simp only [col_apply, submatrix_apply, id, hjk]
  · rintro ⟨b, rfl⟩
    exact ⟨Fin.cast (Nat.add_sub_of_le hk) (Fin.natAdd k b), by simp, rfl⟩

/-- For $k \le n$, the span of the columns $j < k$ (0-based) of $W \in \mathbb{R}^{n \times n}$ is
the range of the leading block $W(:, 1{:}k)$. -/
private theorem span_image_lt_eq_range {k : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hk : k ≤ n) :
    Submodule.span ℝ ((fun j => toLp 2 (W.col j)) '' {j : Fin n | (j : ℕ) < k}) =
      LinearMap.range (toEuclideanLin (W.submatrix id (Fin.castLE hk))) := by
  rw [range_toEuclideanLin_eq_span_col]
  congr 1
  ext v
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨Fin.castLE hk b, b.isLt, rfl⟩

/-- **Section 2.5.2** of [golub2013matrix], the projections related to the SVD. Let
$A = U \Sigma V^T$ be an SVD of $A \in \mathbb{R}^{m \times n}$, let
$r = \operatorname{rank}(A)$, and partition $U = [U_r \mid \tilde U_r]$ and
$V = [V_r \mid \tilde V_r]$, where $U_r$ and $V_r$ have $r$ columns. Then
$\operatorname{null}(A)^\perp = \operatorname{ran}(A^T)$, $\operatorname{ran}(A)^\perp =
\operatorname{null}(A^T)$, and
* $V_r V_r^T$ is the orthogonal projection onto $\operatorname{null}(A)^\perp =
  \operatorname{ran}(A^T)$,
* $\tilde V_r \tilde V_r^T$ is the orthogonal projection onto $\operatorname{null}(A)$,
* $U_r U_r^T$ is the orthogonal projection onto $\operatorname{ran}(A)$,
* $\tilde U_r \tilde U_r^T$ is the orthogonal projection onto $\operatorname{ran}(A)^\perp =
  \operatorname{null}(A^T)$.

The proof combines Corollary 2.4.6 with §2.5.1. -/
theorem svd_projections {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) :
    IsOrthogonalProjection (V.submatrix id (Fin.castLE A.rank_le_width) *
        (V.submatrix id (Fin.castLE A.rank_le_width))ᵀ) (LinearMap.ker (toEuclideanLin A))ᗮ ∧
      (LinearMap.ker (toEuclideanLin A))ᗮ = LinearMap.range (toEuclideanLin Aᵀ) ∧
      IsOrthogonalProjection
        (V.submatrix id (Fin.cast (Nat.add_sub_of_le A.rank_le_width) ∘ Fin.natAdd A.rank) *
          (V.submatrix id (Fin.cast (Nat.add_sub_of_le A.rank_le_width) ∘ Fin.natAdd A.rank))ᵀ)
        (LinearMap.ker (toEuclideanLin A)) ∧
      IsOrthogonalProjection (U.submatrix id (Fin.castLE A.rank_le_height) *
        (U.submatrix id (Fin.castLE A.rank_le_height))ᵀ) (LinearMap.range (toEuclideanLin A)) ∧
      IsOrthogonalProjection
        (U.submatrix id (Fin.cast (Nat.add_sub_of_le A.rank_le_height) ∘ Fin.natAdd A.rank) *
          (U.submatrix id (Fin.cast (Nat.add_sub_of_le A.rank_le_height) ∘ Fin.natAdd A.rank))ᵀ)
        (LinearMap.range (toEuclideanLin A))ᗮ ∧
      (LinearMap.range (toEuclideanLin A))ᗮ = LinearMap.ker (toEuclideanLin Aᵀ) := by
  have hσ : ∀ i < min m n, 0 < σ i ↔ i < A.rank := fun i hi => by
    rw [h.singularValues_eq (lt_of_lt_of_le hi (min_le_left _ _))
      (lt_of_lt_of_le hi (min_le_right _ _))]
    have h0 := sortedSingularValues_eq_zero_iff_rank_le A i
    constructor
    · intro hpos
      by_contra hle
      exact hpos.ne' (h0.2 (not_lt.1 hle))
    · intro hlt
      exact lt_of_le_of_ne (A.sortedSingularValues_nonneg i)
        fun heq => absurd (h0.1 heq.symm) (not_le.2 hlt)
  obtain ⟨-, hker, hran⟩ :=
    corollary_2_4_6 h (le_min A.rank_le_height A.rank_le_width) hσ
  have hU := h.mem_unitaryGroup_left
  have hV := h.mem_unitaryGroup_right
  rw [span_image_le_eq_range V A.rank_le_width] at hker
  rw [span_image_lt_eq_range U A.rank_le_height] at hran
  have hVr : LinearMap.range (toEuclideanLin (V.submatrix id (Fin.castLE A.rank_le_width))) =
      (LinearMap.ker (toEuclideanLin A))ᗮ := by
    rw [hker, ← orthogonal_range_castLE_eq hV A.rank_le_width, Submodule.orthogonal_orthogonal]
  have hkerT : (LinearMap.ker (toEuclideanLin A))ᗮ = LinearMap.range (toEuclideanLin Aᵀ) := by
    have h1 := orthogonal_range_eq_ker_transpose Aᵀ
    rw [transpose_transpose] at h1
    rw [← h1, Submodule.orthogonal_orthogonal]
  refine ⟨isOrthogonalProjection_mul_transpose
      (transpose_mul_submatrix_eq_one hV (Fin.castLE_injective _)) hVr, hkerT,
    isOrthogonalProjection_mul_transpose
      (transpose_mul_submatrix_eq_one hV (cast_natAdd_injective A.rank_le_width)) hker.symm,
    isOrthogonalProjection_mul_transpose
      (transpose_mul_submatrix_eq_one hU (Fin.castLE_injective _)) hran.symm,
    isOrthogonalProjection_mul_transpose
      (transpose_mul_submatrix_eq_one hU (cast_natAdd_injective A.rank_le_height)) ?_,
    orthogonal_range_eq_ker_transpose A⟩
  rw [hran, orthogonal_range_castLE_eq hU A.rank_le_height]

/-! ### §2.5.3 Distance between subspaces -/

/-- **Equation (2.5.1)** of [golub2013matrix], the distance between subspaces. For subspaces $S_1$
and $S_2$ of $\mathbb{R}^n$, the **distance** is
$$\operatorname{dist}(S_1, S_2) = \|P_1 - P_2\|_2,$$
where $P_i$ is the orthogonal projection onto $S_i$.

The definition is the gap `Submodule.gap` of the backbone.

**Generalization.** The source defines the distance for $\dim S_1 = \dim S_2$. The same formula
defines the distance in Lean for every pair of subspaces. -/
noncomputable def subspaceDist (S₁ S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  S₁.gap S₂

/-- **Equation (2.5.1)** of [golub2013matrix], with projection matrices. Let
$P_1, P_2 \in \mathbb{R}^{n \times n}$ be the orthogonal projections onto subspaces $S_1$ and
$S_2$ of $\mathbb{R}^n$. Then
$$\operatorname{dist}(S_1, S_2) = \|P_1 - P_2\|_2.$$

**Generalization.** The source defines and uses this formula for equal-dimensional subspaces.
The formula here holds for arbitrary $S_1$ and $S_2$.
-/
theorem subspaceDist_eq_lpOpNorm_sub {P₁ P₂ : Matrix (Fin n) (Fin n) ℝ}
    {S₁ S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h₁ : IsOrthogonalProjection P₁ S₁)
    (h₂ : IsOrthogonalProjection P₂ S₂) : subspaceDist S₁ S₂ = lpOpNorm 2 (P₁ - P₂) := by
  have e₁ := IsOrthogonalProjection.iff_toEuclideanLin_eq.1 h₁
  have e₂ := IsOrthogonalProjection.iff_toEuclideanLin_eq.1 h₂
  rw [subspaceDist, Submodule.gap, lpOpNorm]
  congr 1
  ext x : 1
  change _ = toEuclideanLin (P₁ - P₂) x
  rw [map_sub, LinearMap.sub_apply, e₁, e₂]
  rfl

/-- **Theorem 2.5.1** of [golub2013matrix]. Let $W = [W_1 \mid W_2]$ and $Z = [Z_1 \mid Z_2]$ be
orthogonal matrices in $\mathbb{R}^{n \times n}$, where $W_1$ and $Z_1$ have $k \le n$ columns.
If $S_1 = \operatorname{ran}(W_1)$ and $S_2 = \operatorname{ran}(Z_1)$, then
$$\operatorname{dist}(S_1, S_2) = \|W_1^T Z_2\|_2 = \|Z_1^T W_2\|_2.$$

The proof applies `Matrix.gap_range_eq_l2_opNorm_conjTranspose_mul` twice, with $W$ and $Z$
exchanged and `Submodule.gap_comm`. The column blocks of an orthogonal matrix have orthonormal
columns and complementary ranges (§2.1.5). -/
theorem theorem_2_5_1 {W Z : Matrix (Fin n) (Fin n) ℝ} (hW : W ∈ orthogonalGroup (Fin n) ℝ)
    (hZ : Z ∈ orthogonalGroup (Fin n) ℝ) (hk : k ≤ n) :
    subspaceDist (LinearMap.range (toEuclideanLin (W.submatrix id (Fin.castLE hk))))
        (LinearMap.range (toEuclideanLin (Z.submatrix id (Fin.castLE hk)))) =
      lpOpNorm 2 ((W.submatrix id (Fin.castLE hk))ᵀ *
        Z.submatrix id (Fin.cast (Nat.add_sub_of_le hk) ∘ Fin.natAdd k)) ∧
    subspaceDist (LinearMap.range (toEuclideanLin (W.submatrix id (Fin.castLE hk))))
        (LinearMap.range (toEuclideanLin (Z.submatrix id (Fin.castLE hk)))) =
      lpOpNorm 2 ((Z.submatrix id (Fin.castLE hk))ᵀ *
        W.submatrix id (Fin.cast (Nat.add_sub_of_le hk) ∘ Fin.natAdd k)) := by
  have hcol : ∀ {X : Matrix (Fin n) (Fin n) ℝ}, X ∈ orthogonalGroup (Fin n) ℝ →
      ∀ {l : ℕ} {e : Fin l → Fin n}, Function.Injective e →
        (X.submatrix id e)ᴴ * X.submatrix id e = 1 := fun hX _ _ he => by
    rw [conjTranspose_eq_transpose_of_trivial]
    exact transpose_mul_submatrix_eq_one hX he
  have hgap : ∀ {X Y : Matrix (Fin n) (Fin n) ℝ}, X ∈ orthogonalGroup (Fin n) ℝ →
      Y ∈ orthogonalGroup (Fin n) ℝ →
        subspaceDist (LinearMap.range (toEuclideanLin (X.submatrix id (Fin.castLE hk))))
            (LinearMap.range (toEuclideanLin (Y.submatrix id (Fin.castLE hk)))) =
          lpOpNorm 2 ((X.submatrix id (Fin.castLE hk))ᵀ *
            Y.submatrix id (Fin.cast (Nat.add_sub_of_le hk) ∘ Fin.natAdd k)) := fun hX hY => by
    rw [subspaceDist, gap_range_eq_l2_opNorm_conjTranspose_mul
      (hcol hX (Fin.castLE_injective hk)) (hcol hY (Fin.castLE_injective hk))
      (hcol hY (cast_natAdd_injective hk)) (orthogonal_range_castLE_eq hY hk).symm,
      conjTranspose_eq_transpose_of_trivial, lpOpNorm_two]
  refine ⟨hgap hW hZ, ?_⟩
  rw [subspaceDist, Submodule.gap_comm, ← subspaceDist]
  exact hgap hZ hW

/-- **Section 2.5.3** of [golub2013matrix]. For subspaces $S_1$ and $S_2$ of $\mathbb{R}^n$,
$$0 \le \operatorname{dist}(S_1, S_2) \le 1.$$

**Generalization.** The source states the bounds for equal-dimensional subspaces. The bounds
hold for arbitrary $S_1$ and $S_2$. -/
theorem subspaceDist_mem_Icc (S₁ S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    subspaceDist S₁ S₂ ∈ Set.Icc 0 1 :=
  ⟨S₁.gap_nonneg S₂, S₁.gap_le_one S₂⟩

/-- **Section 2.5.3** of [golub2013matrix]. For subspaces $S_1$ and $S_2$ of $\mathbb{R}^n$,
$\operatorname{dist}(S_1, S_2) = 0$ if and only if $S_1 = S_2$.

**Generalization.** The source states the implication from left to right. The theorem is an
equivalence, and it needs no hypothesis on the dimensions. -/
theorem subspaceDist_eq_zero {S₁ S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))} :
    subspaceDist S₁ S₂ = 0 ↔ S₁ = S₂ :=
  S₁.gap_eq_zero_iff S₂

/-- **Section 2.5.3** of [golub2013matrix]. Let $S_1$ and $S_2$ be subspaces of $\mathbb{R}^n$ with
$\dim S_1 = \dim S_2$. Then $\operatorname{dist}(S_1, S_2) = 1$ if and only if
$S_1 \cap S_2^\perp \neq \{0\}$.

**Generalization.** The source states the implication from left to right. The theorem is an
equivalence. -/
theorem subspaceDist_eq_one {S₁ S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (h : Module.finrank ℝ S₁ = Module.finrank ℝ S₂) :
    subspaceDist S₁ S₂ = 1 ↔ S₁ ⊓ S₂ᗮ ≠ ⊥ :=
  S₁.gap_eq_one_iff_of_finrank_eq S₂ h

/-! ### §2.5.4 The CS decomposition -/

/-- **Theorem 2.5.2** of [golub2013matrix] (the CS decomposition, thin version). Let
$Q_1 \in \mathbb{R}^{m_1 \times n_1}$ and $Q_2 \in \mathbb{R}^{m_2 \times n_1}$ with
$m_1 \ge n_1$ and $m_2 \ge n_1$, and assume that $Q = \begin{bmatrix} Q_1 \\ Q_2 \end{bmatrix}$
has orthonormal columns. Then there are orthogonal matrices
$U_1 \in \mathbb{R}^{m_1 \times m_1}$, $U_2 \in \mathbb{R}^{m_2 \times m_2}$ and
$V_1 \in \mathbb{R}^{n_1 \times n_1}$ with
$$\begin{bmatrix} U_1 & 0 \\ 0 & U_2 \end{bmatrix}^T \begin{bmatrix} Q_1 \\ Q_2 \end{bmatrix}
  V_1 = \begin{bmatrix} C_0 \\ S_0 \end{bmatrix},$$
where $C_0 = \operatorname{diag}(\cos\theta_1, \dots, \cos\theta_{n_1}) \in \mathbb{R}^{m_1
\times n_1}$, $S_0 = \operatorname{diag}(\sin\theta_1, \dots, \sin\theta_{n_1}) \in
\mathbb{R}^{m_2 \times n_1}$ and $0 \le \theta_1 \le \dots \le \theta_{n_1} \le \pi/2$.

**Typo.** The source labels the stacked blocks $C$ and $S$ in the display and defines them as
$C_0$ and $S_0$ immediately below. The theorem uses the rectangular diagonals $C_0$ and $S_0$.

The angles are a monotone function `θ : ℕ → ℝ` with values in $[0, \pi/2]$, and $C_0$ and $S_0$
are each a `Matrix.rectDiagonal`, of the cosines and of the sines. The proof applies
`Matrix.exists_isThinCSD`, which does not need $m_2 \ge n_1$; under that hypothesis its shift
$p = n_1 - \min\{n_1, m_2\}$ is $0$. -/
theorem theorem_2_5_2 {m₁ m₂ n₁ : ℕ} (Q₁ : Matrix (Fin m₁) (Fin n₁) ℝ)
    (Q₂ : Matrix (Fin m₂) (Fin n₁) ℝ) (h₁ : n₁ ≤ m₁) (h₂ : n₁ ≤ m₂)
    (hQ : (fromRows Q₁ Q₂)ᵀ * fromRows Q₁ Q₂ = 1) :
    ∃ U₁ ∈ orthogonalGroup (Fin m₁) ℝ, ∃ U₂ ∈ orthogonalGroup (Fin m₂) ℝ,
      ∃ V₁ ∈ orthogonalGroup (Fin n₁) ℝ, ∃ θ : ℕ → ℝ,
        (fromBlocks U₁ 0 0 U₂)ᵀ * fromRows Q₁ Q₂ * V₁ =
            fromRows (rectDiagonal fun i => Real.cos (θ i))
              (rectDiagonal fun i => Real.sin (θ i)) ∧
          Monotone θ ∧ ∀ i, θ i ∈ Set.Icc 0 (Real.pi / 2) := by
  rw [transpose_fromRows, fromCols_mul_fromRows] at hQ
  simp only [← conjTranspose_eq_transpose_of_trivial] at hQ
  obtain ⟨U₁, U₂, V, θ, hc⟩ := exists_isThinCSD Q₁ Q₂ hQ h₁
  have hp : n₁ - min n₁ m₂ = 0 := by omega
  have hl := hc.star_mul_mul₁
  have hr := hc.star_mul_mul₂
  rw [hp, shiftedRectDiagonal_zero] at hr
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, id] at hl hr
  refine ⟨U₁, hc.mem_unitaryGroup_left₁, U₂, hc.mem_unitaryGroup_left₂, V,
    hc.mem_unitaryGroup_right, θ, ?_, hc.monotone, hc.mem_Icc⟩
  rw [fromBlocks_transpose, fromBlocks_mul_fromRows, fromRows_mul]
  simp only [transpose_zero, Matrix.zero_mul, add_zero, zero_add, hl, hr]

/-- **Theorem 2.5.3** of [golub2013matrix] (the CS decomposition). Let
$$Q = \begin{bmatrix} Q_{11} & Q_{12} \\ Q_{21} & Q_{22} \end{bmatrix}$$
with $Q_{11} \in \mathbb{R}^{m_1 \times n_1}$, $Q_{12} \in \mathbb{R}^{m_1 \times n_2}$,
$Q_{21} \in \mathbb{R}^{m_2 \times n_1}$ and $Q_{22} \in \mathbb{R}^{m_2 \times n_2}$, where
$m_1 + m_2 = n_1 + n_2$, $m_1 \ge n_1$ and $Q^T Q = I$. Let $p = \max\{0, n_1 - m_2\}$ and
$q = \max\{0, m_2 - n_1\}$. Then there are orthogonal matrices
$U_1 \in \mathbb{R}^{m_1 \times m_1}$, $U_2 \in \mathbb{R}^{m_2 \times m_2}$,
$V_1 \in \mathbb{R}^{n_1 \times n_1}$ and $V_2 \in \mathbb{R}^{n_2 \times n_2}$ with
$$\begin{bmatrix} U_1 & 0 \\ 0 & U_2 \end{bmatrix}^T Q \begin{bmatrix} V_1 & 0 \\ 0 & V_2
  \end{bmatrix} = \begin{bmatrix} I & 0 & 0 & 0 & 0 \\ 0 & C & S & 0 & 0 \\ 0 & 0 & 0 & 0 & I \\
  0 & S & -C & 0 & 0 \\ 0 & 0 & 0 & I & 0 \end{bmatrix},$$
where the row blocks have sizes $p, n_1 - p, m_1 - n_1, n_1 - p, q$, the column blocks have
sizes $p, n_1 - p, n_1 - p, q, m_1 - n_1$, $C = \operatorname{diag}(\cos\theta_{p+1}, \dots,
\cos\theta_{n_1})$, $S = \operatorname{diag}(\sin\theta_{p+1}, \dots, \sin\theta_{n_1})$ and $0
\le \theta_{p+1} \le \dots \le \theta_{n_1} \le \pi/2$.

**Generalization.** The source assumes $m_1 \ge m_2$. The decomposition holds without that
inequality. For square $Q$, the hypothesis $Q^T Q = I$ expresses orthogonality.

The angles are a monotone function `θ : ℕ → ℝ` with values in $[0, \pi/2]$ whose first $p$
values (0-based) are $0$; these give the leading identity block, with $\cos\theta_i = 1$. In
Lean, $p$ is $n_1 - \min\{n_1, m_2\}$ and $q$ is $m_2 - \min\{n_1, m_2\}$. The upper left block of
the right side is a `Matrix.rectDiagonal` of the cosines, the upper right block is a
`Matrix.csdUpperRight`, the lower left block is a `Matrix.shiftedRectDiagonal` of the sines, and
the lower right block is a `Matrix.rectDiagonal` with the negated cosines followed by ones. This
is the layout of the backbone predicate `Matrix.IsCSD`. The proof applies `Matrix.exists_isCSD`.
-/
theorem theorem_2_5_3 {m₁ m₂ n₁ n₂ : ℕ} (Q₁₁ : Matrix (Fin m₁) (Fin n₁) ℝ)
    (Q₁₂ : Matrix (Fin m₁) (Fin n₂) ℝ) (Q₂₁ : Matrix (Fin m₂) (Fin n₁) ℝ)
    (Q₂₂ : Matrix (Fin m₂) (Fin n₂) ℝ) (hsq : m₁ + m₂ = n₁ + n₂)
    (hQ : (fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂)ᵀ * fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂ = 1) (h₁ : n₁ ≤ m₁) :
    ∃ U₁ ∈ orthogonalGroup (Fin m₁) ℝ, ∃ U₂ ∈ orthogonalGroup (Fin m₂) ℝ,
      ∃ V₁ ∈ orthogonalGroup (Fin n₁) ℝ, ∃ V₂ ∈ orthogonalGroup (Fin n₂) ℝ, ∃ θ : ℕ → ℝ,
        (fromBlocks U₁ 0 0 U₂)ᵀ * fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂ * fromBlocks V₁ 0 0 V₂ =
            fromBlocks (rectDiagonal fun i => Real.cos (θ i))
              (csdUpperRight n₁ (n₁ - min n₁ m₂) (m₂ - min n₁ m₂) fun i => Real.sin (θ i))
              (shiftedRectDiagonal (n₁ - min n₁ m₂) fun i => Real.sin (θ i))
              (rectDiagonal fun i =>
                if i < n₁ - (n₁ - min n₁ m₂) then -Real.cos (θ (i + (n₁ - min n₁ m₂))) else 1) ∧
          Monotone θ ∧ (∀ i, θ i ∈ Set.Icc 0 (Real.pi / 2)) ∧
          ∀ i < n₁ - min n₁ m₂, θ i = 0 := by
  rw [← conjTranspose_eq_transpose_of_trivial] at hQ
  obtain ⟨U₁, U₂, V₁, V₂, θ, hc⟩ := exists_isCSD hsq hQ h₁
  have h11 := hc.star_mul_mul₁
  have h12 := hc.star_mul_mul₁₂
  have h21 := hc.star_mul_mul₂
  have h22 := hc.star_mul_mul₂₂
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, id] at h11 h12 h21 h22
  refine ⟨U₁, hc.mem_unitaryGroup_left₁, U₂, hc.mem_unitaryGroup_left₂, V₁,
    hc.mem_unitaryGroup_right, V₂, hc.mem_unitaryGroup_right₂, θ, ?_, hc.monotone, hc.mem_Icc,
    hc.eq_zero_of_lt⟩
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, h11, h12, h21,
    h22]

end GolubVanLoan.Chapter02
