/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.RankRevealing`.
The exception is `Numlib/Analysis/Matrix/SingularValues` (interlacing of the singular values of
submatrices, for Stewart's bounds and subset selection), which is not a candidate and would have
to go upstream first; keep it free of any other dependency on the rest of `Numlib` than other
upstreaming candidates.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv

/-!
# Rank-revealing orthogonal factorizations

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $A \in \mathbb{K}^{M \times N}$. This
module studies factorizations $A = UTW$ in which $U$ is unitary, $W$ is invertible, the rows of $T$
from the $r$-th on vanish, and the leading $r \times r$ block of $T$ is invertible. Such a
factorization reveals the rank $r$ of $A$, the range of $A$ and the least-squares solutions of
$Ax = b$. The main instance is QR factorization with column pivoting in its rank-revealing form,
$A\Pi = QR$, which always exists with $r = \operatorname{rank} A$. The module also proves Chan's
bound on the last diagonal entry of $R$ after a suitable column permutation, defines the URV and ULV
decompositions of Stewart and proves his bounds on the distance between a trailing column span and
the trailing right singular subspace, describes the basic and the minimum-norm least-squares
solutions of a rank-deficient problem, and bounds the error of subset selection based on the
singular value decomposition. The presentation follows [golub2013matrix], §5.4.2–§5.4.6, §5.5.5 and
§5.6.2, which in turn follow Businger and Golub (1965), Chan (1987), Stewart (1993) and Golub and
Pereyra.

Indices start at $0$. For $T \in \mathbb{K}^{M \times N}$ and $r \le M, N$, the block $T_{11}$
consists of the first $r$ rows and columns, $T_{12}$ of the first $r$ rows and the last $N - r$
columns, $T_{21}$ of the last $M - r$ rows and the first $r$ columns, and $T_{22}$ of the last
$M - r$ rows and the last $N - r$ columns. For $y \in \mathbb{K}^r$ and $z \in \mathbb{K}^{N - r}$,
$[y; z] \in \mathbb{K}^N$ is the stacked vector. A permutation $\sigma$ of the column indices has
the permutation matrix $\Pi$ with $(A\Pi)_{ij} = A_{i\sigma(j)}$, so that
$\Pi^T v = v \circ \sigma$. Singular values $\sigma_0(A) \ge \sigma_1(A) \ge \dots$ are numbered
from $0$, the norm of a matrix is the $2$-norm, and the gap between two subspaces $K$ and $L$ is
$\|P_K - P_L\|$, the norm of the difference of the orthogonal projections.

## Main definitions

* `Matrix.HasRevealingBlock`: the rows of $T$ from the $r$-th on vanish and $T_{11}$ is invertible.
* `Matrix.IsPivotedQR.IsRankRevealing`: a pivoted QR factorization $A\Pi = QR$ in which $R$ has a
  revealing block of size $r$, as in (5.4.6) of [golub2013matrix].
* `Matrix.IsURV`, `Matrix.IsULV`: the decompositions $U^H A V = R$ with $R$ upper triangular and
  $U^H A V = L$ with $L$ lower triangular, for unitary $U$ and $V$.
* `Matrix.pivotedBasicSolution`: the basic solution $x_B = \Pi [R_{11}^{-1} c; 0]$ of §5.5.5 of
  [golub2013matrix], with $c$ the first $r$ entries of $Q^H b$.

## Main results

* `Matrix.HasRevealingBlock.rank_eq`: a matrix with a revealing block of size $r$ has rank $r$.
* `Matrix.HasRevealingBlock.range_toEuclideanLin_eq_span`: if $A = UTW$ with $W$ invertible and $T$
  has a revealing block of size $r$, then the range of $A$ is spanned by the first $r$ columns of
  $U$.
* `Matrix.HasRevealingBlock.isLeastSquaresSolution_iff`: if moreover $U$ is unitary, then $x$ is a
  least-squares solution of $Ax = b$ if and only if the first $r$ equations of $TWx = U^H b$ hold.
* `Matrix.exists_isPivotedQR_rank`: every matrix has a rank-revealing pivoted QR factorization with
  $r = \operatorname{rank} A$; no pivoting rule is needed for existence.
* `Matrix.IsPivotedQR.IsRankRevealing.rank_eq`, `Matrix.IsPivotedQR.IsRankRevealing.range_eq_span`:
  a rank-revealing pivoted QR factorization has $r = \operatorname{rank} A$ and $\operatorname{ran}
  A = \operatorname{span}\{q_0, \dots, q_{r-1}\}$.
* `Matrix.exists_perm_isQR_abs_le`: Theorem 5.4.1 of [golub2013matrix] (Chan): for a unit vector
  $v$, some column permutation makes the last diagonal entry of every QR factor $R$ of $A\Pi$ at
  most $\sqrt{n} \|Av\|$ in modulus.
* `Matrix.gap_le_of_urv`, `Matrix.gap_le_of_ulv`: Stewart's bounds (5.4.10) and (5.4.11) of
  [golub2013matrix] on the gap between the span of the trailing columns of $V$ in a URV or ULV
  decomposition and the trailing right singular subspace.
* `Matrix.IsPivotedQR.IsRankRevealing.isLeastSquaresSolution_iff`,
  `Matrix.IsPivotedQR.IsRankRevealing.isLeastSquaresSolution_basic`: the least-squares solutions of
  a rank-deficient problem, and the basic solution among them.
* `Matrix.IsPivotedQR.IsRankRevealing.norm_minNorm_eq_iInf`,
  `Matrix.IsPivotedQR.IsRankRevealing.norm_basic_le`: (5.5.4) and (5.5.5) of [golub2013matrix], the
  minimum-norm solution as a minimum over a free parameter and the bound $\|x_B\| \le \sqrt{1 +
  \|R_{11}^{-1} R_{12}\|^2} \, \|A^+ b\|$.
* `Matrix.IsPivotedQR.IsRankRevealing.mulVec_basic_eq`: Algorithm 5.6.1 of [golub2013matrix], the
  basic solution of an underdetermined system of full row rank.
* `Matrix.norm_residual_subset_sub_le`: Theorem 5.5.3 of [golub2013matrix], the residual of subset
  selection against that of the nearest rank-$r$ problem.

## Implementation notes

* Blocks are expressed by index maps, not by `Matrix.fromBlocks` and a reindexing. The leading block
  of $R$ is `R.submatrix (Fin.castLE _) (Fin.castLE _)`, the trailing indices are `Matrix.tailIdx`,
  and the vector $[y; z]$ on `Fin N` is `Matrix.blockVec`. Where a `Matrix.fromBlocks` form is
  needed, as for Stewart's bounds, `Matrix.blockEquiv : Fin r ⊕ Fin (N - r) ≃ Fin N` reindexes to
  it.
* The column permutation $\Pi$ acts through `A.submatrix id σ`, so that
  $(A\Pi)x = A(x \circ \sigma^{-1})$. The matrix $\Pi$ is `(1 : Matrix _ _ 𝕜).submatrix id σ` and
  $\Pi^T$ is `(1 : Matrix _ _ 𝕜).submatrix σ id`.
* The singular value $\sigma_i(A)$ is `A.sortedSingularValues i`, which is $\sigma_{i+1}$ in the
  1-based numbering of [golub2013matrix]. The matrix norm is the $2$-norm of
  `Matrix.Norms.L2Operator`, and the gap is `Submodule.gap`.
* The inverse $R_{11}^{-1}$ is `Matrix.inv`, which is $0$ for a singular matrix. In a rank-revealing
  factorization $R_{11}$ is invertible.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {M N : ℕ}

/-!
### Factorizations $A = UTW$ with a revealing block

The rank-revealing pivoted QR factorization, with $W = \Pi^T$, and the complete orthogonal
decomposition of `Numlib.LinearAlgebra.Matrix.CompleteOrthogonal`, with $W = V^H$, are both
factorizations $A = UTW$ in which $U$ is unitary, $W$ is invertible, the rows of $T$ from the $r$-th
on vanish and $T_{11}$ is invertible. This section derives the rank, the range and the least-squares
solutions of $A$ from such a factorization, once for both.
-/

section RevealingBlock

variable {r : ℕ}

/-- Let $\alpha$ be a semiring, let $T \in \alpha^{M \times N}$ and let $r \in \mathbb{N}$. The
matrix $T$ has a **revealing block** of size $r$ if $r \le M$, $r \le N$, every row of $T$ with
index $i \ge r$ is zero, and the leading $r \times r$ block $T_{11}$ is invertible. Thus
$$T = \begin{bmatrix} T_{11} & T_{12} \\ 0 & 0 \end{bmatrix},$$
which is the shape of a rank-revealing factorization in (5.4.6) of [golub2013matrix].

Such a matrix has rank $r$ (`Matrix.HasRevealingBlock.rank_eq`). A factorization $A = UTW$ with
$U$ unitary and $W$ invertible then gives the range and the least-squares solutions of $A$
(`Matrix.HasRevealingBlock.range_toEuclideanLin_eq_span`,
`Matrix.HasRevealingBlock.isLeastSquaresSolution_iff`). -/
structure HasRevealingBlock {α : Type*} [Semiring α] (T : Matrix (Fin M) (Fin N) α) (r : ℕ) :
    Prop where
  /-- The block size satisfies $r \le M$. -/
  le_rows : r ≤ M
  /-- The block size satisfies $r \le N$. -/
  le_cols : r ≤ N
  /-- Every entry $T_{ij}$ with row index $i \ge r$ is zero. -/
  apply_eq_zero : ∀ (i : Fin M) (j : Fin N), r ≤ (i : ℕ) → T i j = 0
  /-- The leading $r \times r$ block $T_{11}$ is invertible. -/
  isUnit_block : IsUnit (T.submatrix (Fin.castLE le_rows) (Fin.castLE le_cols))

/-- Let $T \in \mathbb{K}^{M \times N}$ with $r \le M$ and $r \le N$, and let $y \in \mathbb{K}^r$
and $z \in \mathbb{K}^{N - r}$. Then the first $r$ entries of $T[y; z]$ are the entries of
$T_{11} y + T_{12} z$. -/
theorem mulVec_blockVec_castLE (T : Matrix (Fin M) (Fin N) 𝕜) (hM : r ≤ M) (hN : r ≤ N)
    (y : Fin r → 𝕜) (z : Fin (N - r) → 𝕜) (i : Fin r) :
    (T *ᵥ blockVec hN y z) (Fin.castLE hM i) =
      (T.submatrix (Fin.castLE hM) (Fin.castLE hN) *ᵥ y) i +
        (T.submatrix (Fin.castLE hM) (tailIdx hN) *ᵥ z) i := by
  rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx hN]
  simp [mulVec, dotProduct]

/-- Let $T \in \mathbb{K}^{M \times N}$ have a revealing block of size $r$. Then
$\operatorname{rank} T = r$.

The rank is at most $r$ because $T$ has at most $r$ nonzero rows, and at least $r$ because $T$
has the invertible $r \times r$ submatrix $T_{11}$. -/
theorem HasRevealingBlock.rank_eq {T : Matrix (Fin M) (Fin N) 𝕜} (h : T.HasRevealingBlock r) :
    T.rank = r := by
  obtain ⟨hM, hN, hz, hu⟩ := h
  classical
  refine le_antisymm ?_ ?_
  · refine (rank_le_card_of_support_subset T ((Finset.univ.filter fun i : Fin M => (i : ℕ) < r))
      fun i hi => ?_).trans ?_
    · by_contra hir
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, not_lt] at hir
      exact hi (funext fun j => hz i j hir)
    · calc (Finset.univ.filter fun i : Fin M => (i : ℕ) < r).card
          ≤ (Finset.univ.image (Fin.castLE hM : Fin r → Fin M)).card := by
            refine Finset.card_le_card fun i hi => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_univ _, Fin.ext rfl⟩
        _ ≤ r := Finset.card_image_le.trans (by simp)
  · have := rank_submatrix_le T (Fin.castLE hM) (Fin.castLE hN)
    rwa [rank_of_isUnit _ hu, Fintype.card_fin] at this

variable {A : Matrix (Fin M) (Fin N) 𝕜} {U : Matrix (Fin M) (Fin M) 𝕜}
  {T : Matrix (Fin M) (Fin N) 𝕜} {W : Matrix (Fin N) (Fin N) 𝕜}

/-- Let $A, T \in \mathbb{K}^{M \times N}$, let $U \in \mathbb{K}^{M \times M}$, and let
$W \in \mathbb{K}^{N \times N}$ be invertible, with $A = UTW$. If $T$ has a revealing block of
size $r$, then the range of $A$ is spanned by the first $r$ columns $u_0, \dots, u_{r-1}$ of
$U$:
$$\operatorname{ran} A = \operatorname{span}\{u_0, \dots, u_{r-1}\}.$$

The matrix $U$ need not be unitary. The vector $TWx$ has zero entries from the $r$-th on, which
gives one inclusion, and $u_i = A W^{-1} [T_{11}^{-1} e_i; 0]$ gives the other. The range is
that of `Matrix.toEuclideanLin A`. -/
theorem HasRevealingBlock.range_toEuclideanLin_eq_span (h : T.HasRevealingBlock r)
    (hA : A = U * T * W) (hW : IsUnit W) :
    LinearMap.range (toEuclideanLin A) =
      Submodule.span 𝕜 (Set.range fun i : Fin r =>
        (WithLp.toLp 2 (U.col (Fin.castLE h.le_rows i)) : EuclideanSpace 𝕜 (Fin M))) := by
  classical
  obtain ⟨hM, hN, hz, hu⟩ := h
  have hA' : ∀ x : Fin N → 𝕜, A *ᵥ x = U *ᵥ (T *ᵥ (W *ᵥ x)) := fun x => by
    rw [hA, ← mulVec_mulVec, ← mulVec_mulVec]
  have hU : ∀ y : Fin M → 𝕜, (WithLp.toLp 2 (U *ᵥ y) : EuclideanSpace 𝕜 (Fin M)) =
      ∑ i, y i • (WithLp.toLp 2 (U.col i) : EuclideanSpace 𝕜 (Fin M)) := fun y => by
    rw [← toEuclideanLin_toLp, toEuclideanLin_apply_eq_sum]
    rfl
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [toEuclideanLin_apply, hA', hU, sum_eq_sum_castLE_add_sum_tailIdx hM]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      (Submodule.sum_mem _ fun j _ => ?_)
    rw [show (T *ᵥ (W *ᵥ WithLp.ofLp x)) (tailIdx hM j) = 0 by
      simp only [mulVec, dotProduct]
      exact Finset.sum_eq_zero fun k _ => by
        rw [hz _ _ (by simp), zero_mul], zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    set B := T.submatrix (Fin.castLE hM) (Fin.castLE hN)
    set y : Fin r → 𝕜 := B⁻¹ *ᵥ Pi.single i 1
    have hBy : B *ᵥ y = Pi.single i 1 := by
      rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det B).1 hu), one_mulVec]
    set v : Fin N → 𝕜 := blockVec hN y 0
    refine ⟨WithLp.toLp 2 (W⁻¹ *ᵥ v), ?_⟩
    have hTv : T *ᵥ v = Pi.single (Fin.castLE hM i) 1 := by
      ext k
      rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx hN]
      simp only [v, blockVec_castLE, blockVec_tailIdx, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, add_zero]
      by_cases hk : (k : ℕ) < r
      · have := congrFun hBy ⟨k, hk⟩
        simp only [mulVec, dotProduct, B, submatrix_apply] at this
        rw [show k = Fin.castLE hM ⟨k, hk⟩ from Fin.ext rfl, this]
        simp [Pi.single_apply, Fin.ext_iff]
      · rw [Finset.sum_eq_zero fun l _ => by rw [hz _ _ (by omega), zero_mul]]
        rw [Pi.single_apply, ite_eq_right fun e => hk (by rw [e]; simp)]
    rw [toEuclideanLin_toLp, hA', mulVec_mulVec (M := W),
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det W).1 hW), one_mulVec, hTv]
    ext l
    simp [mulVec, dotProduct, Pi.single_apply, Matrix.col]

/-- Let $A = UTW$ with $U \in \mathbb{K}^{M \times M}$ unitary, let $r \le M$, and let every row of
$T$ with index $i \ge r$ be zero. Then for all $b \in \mathbb{K}^M$ and $x \in \mathbb{K}^N$,
the squared residual splits as
$$\|Ax - b\|^2 = \sum_{i < r} |(TWx)_i - (U^H b)_i|^2 + \sum_{r \le i < M} |(U^H b)_i|^2.$$
-/
theorem norm_toEuclideanLin_sub_sq_eq_of_eq_mul (hU : U ∈ unitaryGroup (Fin M) 𝕜) (hM : r ≤ M)
    (hA : A = U * T * W) (hz : ∀ (i : Fin M) (j : Fin N), r ≤ (i : ℕ) → T i j = 0)
    (b : EuclideanSpace 𝕜 (Fin M)) (x : EuclideanSpace 𝕜 (Fin N)) :
    ‖toEuclideanLin A x - b‖ ^ 2 =
      ∑ i : Fin r, ‖(T *ᵥ (W *ᵥ WithLp.ofLp x)) (Fin.castLE hM i) -
        (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE hM i)‖ ^ 2 +
      ∑ j : Fin (M - r), ‖(Uᴴ *ᵥ WithLp.ofLp b) (tailIdx hM j)‖ ^ 2 := by
  have e1 : toEuclideanLin A x = toEuclideanLin U (WithLp.toLp 2 (T *ᵥ (W *ᵥ WithLp.ofLp x))) := by
    rw [toEuclideanLin_apply, hA, ← mulVec_mulVec, ← mulVec_mulVec, toEuclideanLin_toLp]
  have e2 : b = toEuclideanLin U (toEuclideanLin Uᴴ b) := by
    rw [← toEuclideanLin_mul_apply, ← star_eq_conjTranspose, Unitary.mul_star_self_of_mem hU,
      toEuclideanLin_one, LinearMap.id_apply]
  rw [e1]
  conv_lhs => rw [e2]
  rw [← map_sub, norm_toEuclideanLin_apply_of_mem_unitaryGroup hU, EuclideanSpace.norm_sq_eq,
    sum_eq_sum_castLE_add_sum_tailIdx hM]
  have htail : ∀ j, (T *ᵥ (W *ᵥ WithLp.ofLp x)) (tailIdx hM j) = 0 := fun j => by
    simp only [mulVec, dotProduct]
    exact Finset.sum_eq_zero fun k _ => by rw [hz _ _ (by simp), zero_mul]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => rfl)
    (Finset.sum_congr rfl fun j _ => ?_)
  change ‖(T *ᵥ (W *ᵥ WithLp.ofLp x)) (tailIdx hM j) - (Uᴴ *ᵥ WithLp.ofLp b) (tailIdx hM j)‖ ^ 2
    = _
  rw [htail, zero_sub, norm_neg]

/-- Let $A = UTW$ with $U \in \mathbb{K}^{M \times M}$ unitary and $W \in \mathbb{K}^{N \times N}$
invertible, and let $T$ have a revealing block of size $r$. Then $x \in \mathbb{K}^N$ is a
least-squares solution of $Ax = b$ if and only if the first $r$ equations of $TWx = U^H b$ hold:
$$(TWx)_i = (U^H b)_i \quad \text{for all } i < r.$$

By `Matrix.norm_toEuclideanLin_sub_sq_eq_of_eq_mul`, the squared residual of every $x$ is at
least the squared norm of the last $M - r$ entries of $U^H b$, and
$x = W^{-1} [T_{11}^{-1} c; 0]$, with $c$ the first $r$ entries of $U^H b$, attains this value.
A least-squares solution is `Matrix.IsLeastSquaresSolution`. -/
theorem HasRevealingBlock.isLeastSquaresSolution_iff (h : T.HasRevealingBlock r)
    (hU : U ∈ unitaryGroup (Fin M) 𝕜) (hA : A = U * T * W) (hW : IsUnit W)
    {b : EuclideanSpace 𝕜 (Fin M)} {x : EuclideanSpace 𝕜 (Fin N)} :
    IsLeastSquaresSolution A b x ↔ ∀ i : Fin r,
      (T *ᵥ (W *ᵥ WithLp.ofLp x)) (Fin.castLE h.le_rows i) =
        (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i) := by
  obtain ⟨hM, hN, hz, hu⟩ := h
  set B := T.submatrix (Fin.castLE hM) (Fin.castLE hN)
  set x₀ : EuclideanSpace 𝕜 (Fin N) := WithLp.toLp 2 (W⁻¹ *ᵥ blockVec hN
    (B⁻¹ *ᵥ fun i => (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE hM i)) 0)
  have hx₀ : ∀ i : Fin r, (T *ᵥ (W *ᵥ WithLp.ofLp x₀)) (Fin.castLE hM i) =
      (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE hM i) := fun i => by
    rw [show WithLp.ofLp x₀ = W⁻¹ *ᵥ blockVec hN
      (B⁻¹ *ᵥ fun i => (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE hM i)) 0 from rfl, mulVec_mulVec (M := W),
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det W).1 hW), one_mulVec, mulVec_blockVec_castLE,
      mulVec_zero, Pi.zero_apply, add_zero, mulVec_mulVec,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det B).1 hu), one_mulVec]
  have hres : ∀ x' : EuclideanSpace 𝕜 (Fin N), (∀ i : Fin r,
      (T *ᵥ (W *ᵥ WithLp.ofLp x')) (Fin.castLE hM i) = (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE hM i)) →
      ‖toEuclideanLin A x' - b‖ ^ 2 =
        ∑ j : Fin (M - r), ‖(Uᴴ *ᵥ WithLp.ofLp b) (tailIdx hM j)‖ ^ 2 := fun x' hx' => by
    rw [norm_toEuclideanLin_sub_sq_eq_of_eq_mul hU hM hA hz, Finset.sum_eq_zero fun i _ => by
      rw [hx' i, sub_self, norm_zero, zero_pow two_ne_zero], zero_add]
  constructor
  · intro hls i
    have hle := pow_le_pow_left₀ (norm_nonneg _) (hls x₀) 2
    rw [hres _ hx₀, norm_toEuclideanLin_sub_sq_eq_of_eq_mul hU hM hA hz] at hle
    have hz0 : ∑ i : Fin r, ‖(T *ᵥ (W *ᵥ WithLp.ofLp x)) (Fin.castLE hM i) -
        (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE hM i)‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hz0 i
      (Finset.mem_univ _)
    rwa [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at this
  · intro hx y
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [hres x hx, norm_toEuclideanLin_sub_sq_eq_of_eq_mul hU hM hA hz]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end RevealingBlock

/-! ### Rank-revealing pivoted QR -/

section RankRevealing

/-- Let $A \in \mathbb{K}^{M \times N}$, $Q \in \mathbb{K}^{M \times M}$ and
$R \in \mathbb{K}^{M \times N}$, let $\sigma$ be a permutation of the column indices with
permutation matrix $\Pi$, and let $r \in \mathbb{N}$. A **rank-revealing pivoted QR
factorization** is a pivoted QR factorization $A\Pi = QR$, with $Q$ unitary and $R$ upper
trapezoidal (`Matrix.IsPivotedQR`), in which $R$ has a revealing block of size $r$
(`Matrix.HasRevealingBlock`):
$$A\Pi = Q \begin{bmatrix} R_{11} & R_{12} \\ 0 & 0 \end{bmatrix}, \qquad R_{11} \in
  \mathbb{K}^{r \times r} \text{ invertible}.$$
This is (5.4.6) of [golub2013matrix].

Then $r = \operatorname{rank} A$ (`Matrix.IsPivotedQR.IsRankRevealing.rank_eq`), and a
factorization with $r = \operatorname{rank} A$ always exists (`Matrix.exists_isPivotedQR_rank`).
It is the only hypothesis of the least-squares results of this module. -/
structure IsPivotedQR.IsRankRevealing (A : Matrix (Fin M) (Fin N) 𝕜)
    (Q : Matrix (Fin M) (Fin M) 𝕜) (R : Matrix (Fin M) (Fin N) 𝕜) (σ : Equiv.Perm (Fin N))
    (r : ℕ) : Prop extends IsPivotedQR A Q R σ, HasRevealingBlock R r

/-- For a permutation $\sigma$ of the column indices, the matrix $\Pi^T$, which is
`(1 : Matrix _ _ 𝕜).submatrix σ id`, acts on a vector by $\Pi^T v = v \circ \sigma$. -/
theorem one_submatrix_mulVec (σ : Equiv.Perm (Fin N)) (v : Fin N → 𝕜) :
    (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix σ id *ᵥ v = v ∘ σ := by
  funext k
  simp [mulVec, dotProduct, Matrix.one_apply]

/-- For a permutation $\sigma$ of the column indices, the matrix $\Pi^T$ is invertible. -/
theorem isUnit_one_submatrix (σ : Equiv.Perm (Fin N)) :
    IsUnit ((1 : Matrix (Fin N) (Fin N) 𝕜).submatrix σ id) :=
  (isUnit_submatrix_equiv (A := (1 : Matrix (Fin N) (Fin N) 𝕜)) σ (Equiv.refl _)).2 isUnit_one

namespace IsPivotedQR.IsRankRevealing

variable {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
  {R : Matrix (Fin M) (Fin N) 𝕜} {σ : Equiv.Perm (Fin N)} {r : ℕ}

/-- A rank-revealing pivoted QR factorization $A\Pi = QR$ gives $A = QR\Pi^T$. -/
theorem eq_mul (h : IsRankRevealing A Q R σ r) :
    A = Q * R * (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix σ id := by
  rw [h.isQR.mul_eq, mul_submatrix_one, submatrix_submatrix]
  simp

/-- Let $A\Pi = QR$ be a rank-revealing pivoted QR factorization in which $R$ has a revealing block
of size $r$. Then $\operatorname{rank} A = r$.

The rank does not change under multiplication by the invertible matrices $Q$ and $\Pi$, and $R$
has rank $r$ by `Matrix.HasRevealingBlock.rank_eq`. -/
theorem rank_eq (h : IsRankRevealing A Q R σ r) : A.rank = r := by
  classical
  rw [h.eq_mul, rank_mul_eq_left_of_isUnit_det _ _
      ((isUnit_iff_isUnit_det _).1 (isUnit_one_submatrix σ)),
    rank_mul_eq_right_of_isUnit_det _ _
      ((isUnit_iff_isUnit_det Q).1 (isUnit_of_mem_unitaryGroup h.isQR.mem_unitaryGroup))]
  exact h.toHasRevealingBlock.rank_eq

/-- Let $A\Pi = QR$ be a rank-revealing pivoted QR factorization in which $R$ has a revealing block
of size $r$. Then the range of $A$ is spanned by the first $r$ columns of $Q$:
$$\operatorname{ran} A = \operatorname{span}\{q_0, \dots, q_{r-1}\}.$$
This is stated in §5.4.2 of [golub2013matrix], with the 1-based columns $q_1, \dots, q_r$.

The proof specializes `Matrix.HasRevealingBlock.range_toEuclideanLin_eq_span` to $A = QR\Pi^T$:
the vector $R\Pi^T x$ has zero entries from the $r$-th on, and
$q_i = A\Pi [R_{11}^{-1} e_i; 0]$. -/
theorem range_eq_span (h : IsRankRevealing A Q R σ r) :
    LinearMap.range (toEuclideanLin A) =
      Submodule.span 𝕜 (Set.range fun i : Fin r =>
        (WithLp.toLp 2 (Q.col (Fin.castLE h.le_rows i)) : EuclideanSpace 𝕜 (Fin M))) :=
  h.toHasRevealingBlock.range_toEuclideanLin_eq_span h.eq_mul (isUnit_one_submatrix σ)

end IsPivotedQR.IsRankRevealing

/-- Every matrix $A \in \mathbb{K}^{M \times N}$ has a rank-revealing pivoted QR factorization
$A\Pi = QR$ in which $R$ has a revealing block of size $r = \operatorname{rank} A$, in the sense
of (5.4.6) of [golub2013matrix].

No pivoting rule is needed for existence. The proof chooses $r$ linearly independent columns of
$A$, a permutation $\sigma$ that puts them first, and any QR factorization of $A\Pi$. The first
$r$ columns of $A\Pi$ span its column space and $R$ is upper triangular, so the rows of $R$ from
the $r$-th on vanish; the independence of the first $r$ columns makes $R_{11}$ invertible. -/
theorem exists_isPivotedQR_rank (A : Matrix (Fin M) (Fin N) 𝕜) :
    ∃ σ Q R, IsPivotedQR.IsRankRevealing A Q R σ A.rank := by
  classical
  set r := A.rank with hr
  obtain ⟨c, hc⟩ := exists_linearIndependent_col A hr.symm
  have hrN : r ≤ N := by simpa using A.rank_le_card_width
  have hrM : r ≤ M := A.rank_le_height
  have hcinj : Function.Injective c := hc.injective.of_comp
  let e : Set.range (Fin.castLE hrN) ≃ Set.range c :=
    (Equiv.ofInjective _ (Fin.castLE_injective hrN)).symm.trans (Equiv.ofInjective c hcinj)
  let σ : Equiv.Perm (Fin N) := e.extendSubtype
  have hσ : ∀ i : Fin r, σ (Fin.castLE hrN i) = c i := fun i => by
    have := Equiv.extendSubtype_apply_of_mem e (Fin.castLE hrN i) ⟨i, rfl⟩
    rw [this]
    simp [e, Equiv.ofInjective_symm_apply]
  obtain ⟨Q, R, hQR⟩ := exists_isQR (A.submatrix id σ)
  set A' := A.submatrix id σ with hA'
  have hcol : ∀ i : Fin r, A'.col (Fin.castLE hrN i) = A.col (c i) := fun i => by
    funext k
    simp [A', Matrix.col, hσ]
  have hli : LinearIndependent 𝕜 fun i : Fin r => A'.col (Fin.castLE hrN i) := by
    have e : (fun i : Fin r => A'.col (Fin.castLE hrN i)) = A.col ∘ c := funext hcol
    rw [e]
    exact hc
  -- the first `r` columns of `A Π` span its column space
  set W := Submodule.span 𝕜 (Set.range fun i : Fin r => A'.col (Fin.castLE hrN i))
  have hWV : W = Submodule.span 𝕜 (Set.range A.col) := by
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨c i, (hcol i).symm⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin, ← rank_eq_finrank_span_cols]
  have hmem : ∀ j, A'.col j ∈ W := fun j => by
    rw [hWV]
    exact Submodule.subset_span ⟨σ j, rfl⟩
  have hR : Qᴴ * A' = R := by
    rw [← hQR.mul_eq, ← Matrix.mul_assoc, ← star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem hQR.mem_unitaryGroup, Matrix.one_mul]
  have hRe : ∀ i j, R i j = (Qᴴ *ᵥ A'.col j) i := fun i j => by
    rw [← hR]
    rfl
  have hzero : ∀ (i : Fin M) (j : Fin N), r ≤ (i : ℕ) → R i j = 0 := by
    intro i j hi
    let f : (Fin M → 𝕜) →ₗ[𝕜] 𝕜 := (LinearMap.proj i).comp (Qᴴ).mulVecLin
    have hW : W ≤ LinearMap.ker f := Submodule.span_le.2 (by
      rintro _ ⟨l, rfl⟩
      change (Qᴴ *ᵥ A'.col (Fin.castLE hrN l)) i = 0
      rw [← hRe]
      exact hQR.apply_eq_zero _ _ (by simp; omega))
    rw [hRe]
    exact hW (hmem j)
  refine ⟨σ, Q, R, ⟨hQR⟩, hrM, hrN, hzero, ?_⟩
  -- the leading block is injective
  set B := R.submatrix (Fin.castLE hrM) (Fin.castLE hrN)
  rw [← mulVec_injective_iff_isUnit]
  intro y y' hyy
  rw [← sub_eq_zero]
  have hy : B *ᵥ (y - y') = 0 := by rw [mulVec_sub, hyy, sub_self]
  set v : Fin N → 𝕜 := blockVec hrN (y - y') 0
  have hRv : R *ᵥ v = 0 := by
    ext k
    rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx hrN]
    simp only [v, blockVec_castLE, blockVec_tailIdx, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
    by_cases hk : (k : ℕ) < r
    · have := congrFun hy ⟨k, hk⟩
      simpa [mulVec, dotProduct, B] using this
    · exact Finset.sum_eq_zero fun l _ => by rw [hzero _ _ (by omega), zero_mul]
  have hAv : A' *ᵥ v = 0 := by rw [← hQR.mul_eq, ← mulVec_mulVec, hRv, mulVec_zero]
  have hsum : ∑ i : Fin r, (y - y') i • A'.col (Fin.castLE hrN i) = 0 := by
    rw [← hAv]
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Matrix.col]
    rw [sum_eq_sum_castLE_add_sum_tailIdx hrN]
    simp [v, mul_comm]
  funext i
  exact Fintype.linearIndependent_iff.1 hli _ hsum i

end RankRevealing

/-! ### Column-norm downdating and Chan's theorem -/

section Chan

/-- The **column-norm downdating** identity: let $Q \in \mathbb{K}^{(s+1) \times (s+1)}$ be unitary
and let $z \in \mathbb{K}^{s+1}$. Then the entries of $Q^H z$ after the first satisfy
$$\sum_{i=1}^{s} |(Q^H z)_i|^2 = \|z\|^2 - |(Q^H z)_0|^2.$$

This identity is behind the update $c(i) = c(i) - A(r, i)^2$ of the column norms in Algorithm
5.4.1 of [golub2013matrix], §5.4.2. -/
theorem norm_sq_tail_eq_of_mem_unitaryGroup {s : ℕ} {Q : Matrix (Fin (s + 1)) (Fin (s + 1)) 𝕜}
    (hQ : Q ∈ unitaryGroup (Fin (s + 1)) 𝕜) (z : Fin (s + 1) → 𝕜) :
    ∑ i : Fin s, ‖(Qᴴ *ᵥ z) i.succ‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 - ‖(Qᴴ *ᵥ z) 0‖ ^ 2 := by
  have hQ' : Qᴴ ∈ unitaryGroup (Fin (s + 1)) 𝕜 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mem hQ
  rw [← sum_norm_sq_mulVec_of_mem_unitaryGroup hQ' z, Fin.sum_univ_succ]
  ring

/-- **Chan's theorem**: let $A \in \mathbb{K}^{M \times n}$ with $n = N + 1 \le M$, and let
$v \in \mathbb{K}^n$ with $\|v\| = 1$. Then there is a column permutation $\sigma$ such that
every QR factorization $A\Pi = QR$ satisfies
$$|r_{nn}| \le \sqrt{n} \, \|Av\|$$
for the last diagonal entry $r_{nn}$ of $R$. This is Theorem 5.4.1 of [golub2013matrix], due to
Chan (1987).

The permutation moves an entry $v_p$ of largest modulus, which has $|v_p| \ge 1/\sqrt{n}$, to
the last position; then $\|Av\| = \|R\Pi^T v\| \ge |r_{nn}| \, |v_p|$. In Lean, $r_{nn}$ is the
entry `R ⟨N, _⟩ (Fin.last N)`, and a QR factorization of $A\Pi$ is
`Matrix.IsQR (A.submatrix id σ) Q R`. -/
theorem exists_perm_isQR_abs_le (A : Matrix (Fin M) (Fin (N + 1)) 𝕜) (hNM : N + 1 ≤ M)
    (v : EuclideanSpace 𝕜 (Fin (N + 1))) (hv : ‖v‖ = 1) :
    ∃ σ : Equiv.Perm (Fin (N + 1)), ∀ Q R, IsQR (A.submatrix id σ) Q R →
      ‖R ⟨N, by omega⟩ (Fin.last N)‖ ≤ √(N + 1 : ℝ) * ‖toEuclideanLin A v‖ := by
  classical
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖) Finset.univ_nonempty
  refine ⟨Equiv.swap p (Fin.last N), fun Q R hQR => ?_⟩
  set σ := Equiv.swap p (Fin.last N)
  -- `A v = (A Π) w` with `w = v ∘ σ`
  set w : Fin (N + 1) → 𝕜 := fun k => v (σ k) with hw
  have hAv : toEuclideanLin A v = toEuclideanLin (A.submatrix id σ) (WithLp.toLp 2 w) := by
    ext i
    simp only [toEuclideanLin_apply, mulVec, dotProduct, submatrix_apply, id_eq, hw]
    exact (Equiv.sum_comp σ fun j => A i j * v j).symm
  have hRw : ‖toEuclideanLin A v‖ = ‖toEuclideanLin R (WithLp.toLp 2 w)‖ := by
    rw [hAv, ← hQR.mul_eq, toEuclideanLin_mul_apply,
      norm_toEuclideanLin_apply_of_mem_unitaryGroup hQR.mem_unitaryGroup]
  -- the last coordinate of `R w`
  set ℓ : Fin M := ⟨N, by omega⟩
  have hlast : (R *ᵥ w) ℓ = R ℓ (Fin.last N) * v p := by
    rw [mulVec, dotProduct, Fin.sum_univ_castSucc, Finset.sum_eq_zero (fun j _ => by
      rw [hQR.apply_eq_zero ℓ _ (by simp [ℓ]), zero_mul]), zero_add]
    simp [hw, σ]
  have hge : ‖R ℓ (Fin.last N) * v p‖ ≤ ‖toEuclideanLin R (WithLp.toLp 2 w)‖ := by
    have e : (R *ᵥ w) ℓ = (toEuclideanLin R (WithLp.toLp 2 w)) ℓ := rfl
    rw [← hlast, e]
    exact PiLp.norm_apply_le _ ℓ
  -- `|v_p| ≥ 1/√(N + 1)`
  have hvp : 1 ≤ (N + 1 : ℝ) * ‖v p‖ ^ 2 := by
    have h1 : ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := EuclideanSpace.norm_sq_eq v
    rw [hv, one_pow] at h1
    calc (1 : ℝ) = ∑ i, ‖v i‖ ^ 2 := h1
      _ ≤ ∑ _i : Fin (N + 1), ‖v p‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hp i (by simp)) 2
      _ = (N + 1 : ℝ) * ‖v p‖ ^ 2 := by simp
  have hs : 0 < √(N + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hvp' : 1 ≤ √(N + 1 : ℝ) * ‖v p‖ := by
    have hx : 0 ≤ √(N + 1 : ℝ) * ‖v p‖ := by positivity
    have hsq : 1 ≤ (√(N + 1 : ℝ) * ‖v p‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      exact hvp
    exact ((one_le_sq_iff_one_le_abs _).1 hsq).trans_eq (abs_of_nonneg hx)
  rw [hRw]
  calc ‖R ℓ (Fin.last N)‖ ≤ ‖R ℓ (Fin.last N)‖ * (√(N + 1 : ℝ) * ‖v p‖) :=
        le_mul_of_one_le_right (norm_nonneg _) hvp'
    _ = √(N + 1 : ℝ) * ‖R ℓ (Fin.last N) * v p‖ := by rw [norm_mul]; ring
    _ ≤ √(N + 1 : ℝ) * ‖toEuclideanLin R (WithLp.toLp 2 w)‖ :=
        mul_le_mul_of_nonneg_left hge hs.le

end Chan

/-! ### URV and ULV decompositions -/

section UTV

/-- Let $A \in \mathbb{K}^{M \times N}$, $U \in \mathbb{K}^{M \times M}$,
$R \in \mathbb{K}^{M \times N}$ and $V \in \mathbb{K}^{N \times N}$. These form a **URV
decomposition** of $A$ if $U$ and $V$ are unitary, $U^H A V = R$, and $R$ is upper triangular in
the rectangular sense: $R_{ij} = 0$ for $j < i$. This is the decomposition of Stewart (1993) in
§5.4.5 of [golub2013matrix].

Its trailing block reveals the small singular values of $A$ (`Matrix.gap_le_of_urv`). A pivoted
QR factorization is a URV decomposition in which $V$ is the permutation matrix
(`Matrix.IsPivotedQR.isURV`). The structure extends `Matrix.IsUnitaryEquiv` by the shape
condition. -/
structure IsURV (A : Matrix (Fin M) (Fin N) 𝕜) (U : Matrix (Fin M) (Fin M) 𝕜)
    (R : Matrix (Fin M) (Fin N) 𝕜) (V : Matrix (Fin N) (Fin N) 𝕜) : Prop
    extends IsUnitaryEquiv A U R V where
  /-- The middle factor is upper triangular: $R_{ij} = 0$ for $j < i$. -/
  apply_eq_zero : ∀ (i : Fin M) (j : Fin N), (j : ℕ) < i → R i j = 0

/-- Let $A \in \mathbb{K}^{M \times N}$, $U \in \mathbb{K}^{M \times M}$,
$L \in \mathbb{K}^{M \times N}$ and $V \in \mathbb{K}^{N \times N}$. These form a **ULV
decomposition** of $A$ if $U$ and $V$ are unitary, $U^H A V = L$, and $L$ is lower triangular in
the rectangular sense: $L_{ij} = 0$ for $i < j$. This is the lower triangular counterpart of
`Matrix.IsURV`, from Stewart (1993) in §5.4.5 of [golub2013matrix]. -/
structure IsULV (A : Matrix (Fin M) (Fin N) 𝕜) (U : Matrix (Fin M) (Fin M) 𝕜)
    (L : Matrix (Fin M) (Fin N) 𝕜) (V : Matrix (Fin N) (Fin N) 𝕜) : Prop
    extends IsUnitaryEquiv A U L V where
  /-- The middle factor is lower triangular: $L_{ij} = 0$ for $i < j$. -/
  apply_eq_zero : ∀ (i : Fin M) (j : Fin N), (i : ℕ) < j → L i j = 0

/-- For a permutation $\sigma$ of the column indices, the permutation matrix $\Pi$, which is the
identity matrix with its columns permuted by $\sigma$, is unitary. -/
theorem one_submatrix_mem_unitaryGroup (σ : Equiv.Perm (Fin N)) :
    (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix id σ ∈ unitaryGroup (Fin N) 𝕜 :=
  submatrix_equiv_mem_unitaryGroup (one_mem _) (Equiv.refl _) σ

/-- Let $A\Pi = QR$ be a pivoted QR factorization of $A \in \mathbb{K}^{M \times N}$. Then
$Q^H A \Pi = R$ is a URV decomposition of $A$, with $U = Q$ and $V = \Pi$.

The matrices `(1 : Matrix _ _ 𝕜).submatrix id σ` and `A.submatrix id σ` are $\Pi$ and $A\Pi$. -/
theorem IsPivotedQR.isURV {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
    {R : Matrix (Fin M) (Fin N) 𝕜} {σ : Equiv.Perm (Fin N)} (h : IsPivotedQR A Q R σ) :
    IsURV A Q R ((1 : Matrix (Fin N) (Fin N) 𝕜).submatrix id σ) where
  mem_unitaryGroup_left := h.isQR.mem_unitaryGroup
  mem_unitaryGroup_right := one_submatrix_mem_unitaryGroup σ
  star_mul_mul := by
    rw [Matrix.mul_assoc, show A * (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix id σ =
      A.submatrix id σ by simpa using mul_submatrix_one (Equiv.refl (Fin N)) σ A,
      ← h.isQR.mul_eq, ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem h.isQR.mem_unitaryGroup,
      Matrix.one_mul]
  apply_eq_zero := h.isQR.apply_eq_zero

end UTV

/-! ### Stewart's bounds for the URV and ULV decompositions -/

section Stewart

open scoped Matrix.Norms.L2Operator

variable {r : ℕ}

omit [RCLike 𝕜] in
/-- The trailing indices $r, \dots, N - 1$ and the leading indices $0, \dots, r - 1$ together
enumerate the indices $0, \dots, N - 1$, each once. -/
private theorem bijective_sum_elim_tailIdx_castLE (h : r ≤ N) :
    Function.Bijective (Sum.elim (tailIdx h) (Fin.castLE h)) := by
  convert ((Equiv.sumComm _ _).trans (blockEquiv h)).bijective using 1
  funext x
  cases x <;> simp

/-- Let $V, Z \in \mathbb{K}^{N \times N}$ be unitary, let $r \le N$, and let $V_2$ and $Z_2$ be the
last $N - r$ columns of $V$ and of $Z$. Then the gap between their ranges is the $2$-norm of the
block of $V^H Z$ in the first $r$ rows and the last $N - r$ columns:
$$\operatorname{gap}(\operatorname{ran} V_2, \operatorname{ran} Z_2) = \|(V^H Z)_{12}\|.$$
This is Theorem 2.5.1 of [golub2013matrix] in the form that Stewart's bounds use. -/
theorem gap_range_tailIdx_eq {V Z : Matrix (Fin N) (Fin N) 𝕜}
    (hV : V ∈ unitaryGroup (Fin N) 𝕜) (hZ : Z ∈ unitaryGroup (Fin N) 𝕜) (h : r ≤ N) :
    (LinearMap.range (toEuclideanLin (V.submatrix id (tailIdx h)))).gap
        (LinearMap.range (toEuclideanLin (Z.submatrix id (tailIdx h)))) =
      ‖(star V * Z).submatrix (Fin.castLE h) (tailIdx h)‖ := by
  rw [Submodule.gap_comm, gap_range_eq_l2_opNorm_conjTranspose_mul
    (by rw [conjTranspose_submatrix_mul_submatrix_of_mem_unitaryGroup hZ,
      submatrix_one _ (tailIdx_injective h)])
    (by rw [conjTranspose_submatrix_mul_submatrix_of_mem_unitaryGroup hV,
      submatrix_one _ (tailIdx_injective h)])
    (by rw [conjTranspose_submatrix_mul_submatrix_of_mem_unitaryGroup hV,
      submatrix_one _ (Fin.castLE_injective h)])
    (range_submatrix_eq_orthogonal hV (bijective_sum_elim_tailIdx_castLE h)),
    ← l2_opNorm_conjTranspose ((Z.submatrix id (tailIdx h))ᴴ * V.submatrix id (Fin.castLE h)),
    conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_submatrix,
    ← submatrix_mul _ _ _ id _ Function.bijective_id, star_eq_conjTranspose]

/-- Let $A, T \in \mathbb{K}^{M \times N}$ with $T = U^H A V$ for unitary $U$ and $V$, let
$A = W \Sigma Z^H$ be a singular value decomposition, let $r \le N$, and let $Y$ be the last
$N - r$ columns of $V^H Z$, which are trailing right singular vectors of $T$. Then:

* there is $D \in \mathbb{K}^{(N-r) \times (N-r)}$ with $T^H T Y = Y D$ and
  $\|Dw\| \le \sigma_r(T)^2 \|w\|$ for all $w$;
* $Y$ is an isometry: $\|Yw\| = \|w\|$ for all $w$;
* $\|TYw\| \le \sigma_r(T) \|w\|$ for all $w$;
* the gap between the spans of the last $N - r$ columns of $V$ and of $Z$ is $\|Y_1\|$, the
  $2$-norm of the first $r$ rows of $Y$.

This is the common setting of Stewart's bounds in §5.4.6 of [golub2013matrix].

The value $\sigma_r(T)$ is `T.sortedSingularValues r`, the $(r+1)$-th largest singular value of
$T$. In the proof, $D$ is the diagonal matrix of the squared trailing singular values; the
statement records only the bound on $D$. -/
theorem stewart_setting {A T : Matrix (Fin M) (Fin N) 𝕜} {U W : Matrix (Fin M) (Fin M) 𝕜}
    {V Z : Matrix (Fin N) (Fin N) 𝕜} {σ : ℕ → ℝ} (hU : U ∈ unitaryGroup (Fin M) 𝕜)
    (hV : V ∈ unitaryGroup (Fin N) 𝕜) (hT : star U * A * V = T) (hA : IsSVD A W σ Z)
    (h : r ≤ N) :
    ∃ D : Matrix (Fin (N - r)) (Fin (N - r)) 𝕜,
      Tᴴ * T * (star V * Z).submatrix id (tailIdx h) = (star V * Z).submatrix id (tailIdx h) * D ∧
      (∀ w, ‖toEuclideanLin D w‖ ≤ T.sortedSingularValues r ^ 2 * ‖w‖) ∧
      (∀ w, ‖toEuclideanLin ((star V * Z).submatrix id (tailIdx h)) w‖ = ‖w‖) ∧
      (∀ w, ‖toEuclideanLin T (toEuclideanLin ((star V * Z).submatrix id (tailIdx h)) w)‖ ≤
        T.sortedSingularValues r * ‖w‖) ∧
      (LinearMap.range (toEuclideanLin (V.submatrix id (tailIdx h)))).gap
          (LinearMap.range (toEuclideanLin (Z.submatrix id (tailIdx h)))) =
        ‖(star V * Z).submatrix (Fin.castLE h) (tailIdx h)‖ := by
  obtain ⟨G, hGdef⟩ : ∃ G, G = star V * Z := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = star U * W := ⟨_, rfl⟩
  have hG : G ∈ unitaryGroup (Fin N) 𝕜 := by
    rw [hGdef]
    exact mul_mem (Unitary.star_mem hV) hA.mem_unitaryGroup_right
  have hP : P ∈ unitaryGroup (Fin M) 𝕜 := by
    rw [hPdef]
    exact mul_mem (Unitary.star_mem hU) hA.mem_unitaryGroup_left
  -- the SVD of `T`
  have hTsvd : IsSVD T P σ G := by
    refine ⟨⟨hP, hG, ?_⟩, hA.antitone, hA.nonneg⟩
    rw [hPdef, hGdef, ← hT, ← hA.star_mul_mul]
    simp only [star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U (star U), mem_unitaryGroup_iff.1 hU, Matrix.one_mul,
      ← Matrix.mul_assoc V (star V), mem_unitaryGroup_iff.1 hV, Matrix.one_mul]
  have hgap := gap_range_tailIdx_eq hV hA.mem_unitaryGroup_right h
  rw [← hGdef] at hgap ⊢
  -- `Tᴴ T G = G Σᴴ Σ`
  have hPP : Pᴴ * P = 1 := by
    rw [← star_eq_conjTranspose]
    exact mem_unitaryGroup_iff'.1 hP
  have hGG : Gᴴ * G = 1 := by
    rw [← star_eq_conjTranspose]
    exact mem_unitaryGroup_iff'.1 hG
  have hTG : Tᴴ * T * G = G *
      ((rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin M) (Fin N) 𝕜)ᴴ *
        rectDiagonal fun i => ((σ i : ℝ) : 𝕜)) := by
    rw [hTsvd.eq_mul_mul_star, star_eq_conjTranspose]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [hGG, Matrix.mul_one, ← Matrix.mul_assoc Pᴴ P, hPP, Matrix.one_mul]
  rw [conjTranspose_rectDiagonal_mul_self] at hTG
  set D : Matrix (Fin (N - r)) (Fin (N - r)) 𝕜 := diagonal fun j =>
    if ((tailIdx h j : ℕ) < M) then star ((σ (tailIdx h j) : ℝ) : 𝕜) * ((σ (tailIdx h j) : ℝ) : 𝕜)
    else 0 with hD
  -- the diagonal entries
  have hdle : ∀ j : Fin (N - r), ‖(if ((tailIdx h j : ℕ) < M) then
      star ((σ (tailIdx h j) : ℝ) : 𝕜) * ((σ (tailIdx h j) : ℝ) : 𝕜) else 0)‖ ≤
        T.sortedSingularValues r ^ 2 := by
    intro j
    split_ifs with hj
    · have hrM : r < M := lt_of_le_of_lt (by simp) hj
      have hrN : r < N := lt_of_le_of_lt (by simp) (tailIdx h j).isLt
      rw [norm_mul, norm_star, RCLike.norm_ofReal, abs_of_nonneg (hA.nonneg _), ← sq,
        ← hTsvd.singularValues_eq (i := r) hrM hrN]
      exact pow_le_pow_left₀ (hA.nonneg _) (hA.antitone (by simp)) 2
    · rw [norm_zero]
      positivity
  have hDw : ∀ w, ‖toEuclideanLin D w‖ ≤ T.sortedSingularValues r ^ 2 * ‖w‖ := by
    intro w
    refine (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (sq_nonneg _) (norm_nonneg _)) two_ne_zero).1 ?_
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [toEuclideanLin_apply, PiLp.toLp_apply, hD, mulVec_diagonal, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hdle j) 2)
      (sq_nonneg _)
  have hY : Tᴴ * T * G.submatrix id (tailIdx h) = G.submatrix id (tailIdx h) * D := by
    have := congrArg (fun X => X.submatrix id (tailIdx h)) hTG
    refine this.trans ?_
    ext i j
    simp only [hD, submatrix_apply, id_eq, mul_diagonal]
  have hYY : (G.submatrix id (tailIdx h))ᴴ * G.submatrix id (tailIdx h) = 1 := by
    rw [conjTranspose_submatrix_mul_submatrix_of_mem_unitaryGroup hG,
      submatrix_one _ (tailIdx_injective h)]
  have hiso : ∀ w, ‖toEuclideanLin (G.submatrix id (tailIdx h)) w‖ = ‖w‖ :=
    fun w => (toEuclideanLinearIsometry hYY).norm_map w
  refine ⟨D, hY, hDw, hiso, fun w => ?_, hgap⟩
  -- `‖T Y w‖² = re ⟪w, D w⟫`
  set Y := G.submatrix id (tailIdx h) with hYdef
  have s1 : toEuclideanLin Tᴴ (toEuclideanLin T (toEuclideanLin Y w)) =
      toEuclideanLin Y (toEuclideanLin D w) := by
    rw [← toEuclideanLin_mul_apply T Y, ← toEuclideanLin_mul_apply Tᴴ (T * Y),
      ← Matrix.mul_assoc, hY, toEuclideanLin_mul_apply]
  have s2 : (inner 𝕜 (toEuclideanLin Y w) (toEuclideanLin Y (toEuclideanLin D w)) : 𝕜) =
      inner 𝕜 w (toEuclideanLin D w) := by
    rw [← toEuclideanLin_conjTranspose_inner_right Y, ← toEuclideanLin_mul_apply Yᴴ Y, hYY,
      toEuclideanLin_one, LinearMap.id_apply]
  have e1 : (inner 𝕜 (toEuclideanLin T (toEuclideanLin Y w))
      (toEuclideanLin T (toEuclideanLin Y w)) : 𝕜) = inner 𝕜 w (toEuclideanLin D w) := by
    rw [← toEuclideanLin_conjTranspose_inner_right T, s1, s2]
  have e2 : ‖toEuclideanLin T (toEuclideanLin Y w)‖ ^ 2 =
      RCLike.re (inner 𝕜 w (toEuclideanLin D w)) := by
    rw [← e1, inner_self_eq_norm_sq]
  have e3 : RCLike.re (inner 𝕜 w (toEuclideanLin D w)) ≤
      ‖w‖ * (T.sortedSingularValues r ^ 2 * ‖w‖) :=
    (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hDw w) (norm_nonneg _)))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (sortedSingularValues_nonneg _ _) (norm_nonneg _)) two_ne_zero).1 ?_
  rw [e2, mul_pow]
  linarith

/-- For $B \in \mathbb{K}^{p \times r}$ with $r \ge 1$, the least singular value bounds the stretch
from below: $\sigma_{r-1}(B) \|x\| \le \|Bx\|$. -/
private theorem sortedSingularValues_mul_norm_le {p : Type*} [Fintype p] (B : Matrix p (Fin r) 𝕜)
    (hr : 0 < r) (x : EuclideanSpace 𝕜 (Fin r)) :
    B.sortedSingularValues (r - 1) * ‖x‖ ≤ ‖toEuclideanLin B x‖ := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have := B.iInf_colSingularValues_mul_norm_le x
  rwa [← sortedSingularValues_eq_iInf_colSingularValues, Fintype.card_fin] at this

/-- The first $r$ entries of $Tv$ are those of $T_{11} v_1 + T_{12} v_2$, where $v_1$ and $v_2$ are
the first $r$ and the last $N - r$ entries of $v$. -/
private theorem mulVec_castLE (T : Matrix (Fin M) (Fin N) 𝕜) (hM : r ≤ M) (hN : r ≤ N)
    (v : Fin N → 𝕜) (i : Fin r) :
    (T *ᵥ v) (Fin.castLE hM i) =
      (T.submatrix (Fin.castLE hM) (Fin.castLE hN) *ᵥ fun l => v (Fin.castLE hN l)) i +
        (T.submatrix (Fin.castLE hM) (tailIdx hN) *ᵥ fun l => v (tailIdx hN l)) i := by
  rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx hN]
  rfl

/-- The first $r$ entries of $T^H u$ are those of $T_{11}^H u_1 + T_{21}^H u_2$, where $u_1$ and
$u_2$ are the first $r$ and the last $M - r$ entries of $u$. -/
private theorem conjTranspose_mulVec_castLE (T : Matrix (Fin M) (Fin N) 𝕜) (hM : r ≤ M)
    (hN : r ≤ N) (u : Fin M → 𝕜) (i : Fin r) :
    (Tᴴ *ᵥ u) (Fin.castLE hN i) =
      ((T.submatrix (Fin.castLE hM) (Fin.castLE hN))ᴴ *ᵥ fun l => u (Fin.castLE hM l)) i +
        ((T.submatrix (tailIdx hM) (Fin.castLE hN))ᴴ *ᵥ fun l => u (tailIdx hM l)) i := by
  rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx hM]
  rfl

/-- For real numbers with $s > 0$, the inequality $s^2 y \le (s a + t^2 Y) w$ implies
$y \le (a / s + (t / s)^2 Y) w$. -/
private theorem le_mul_of_sq_mul_le {y w a t Y s : ℝ} (hs : 0 < s)
    (h : s ^ 2 * y ≤ (s * a + t ^ 2 * Y) * w) : y ≤ (a / s + (t / s) ^ 2 * Y) * w := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hs' : s ≠ 0 := hs.ne'
  have e : (a / s + (t / s) ^ 2 * Y) * w * s ^ 2 = (s * a + t ^ 2 * Y) * w := by
    field_simp
  exact le_of_mul_le_mul_right (by rw [e]; linarith) hs2

/-- For real numbers with $s > 0$ and $0 \le \rho < 1$, the inequality $x \le a / s + \rho^2 x$
implies $x \le a / ((1 - \rho^2) s)$. -/
private theorem le_div_of_le_add_sq_mul {x a s ρ : ℝ} (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : x ≤ a / s + ρ ^ 2 * x) : x ≤ a / ((1 - ρ ^ 2) * s) := by
  have h1 : 0 < 1 - ρ ^ 2 := by nlinarith
  rw [le_div_iff₀ (mul_pos h1 hs)]
  have := mul_le_mul_of_nonneg_left h hs.le
  rw [mul_add, mul_div_cancel₀ _ hs.ne'] at this
  nlinarith

/-- **Stewart's bound for a URV decomposition**: let $U^H A V = R$ be a URV decomposition of
$A \in \mathbb{K}^{M \times N}$, let $A = W \Sigma Z^H$ be a singular value decomposition, and
let $k \le M$ and $k \le N$. Split $R$ at $k$,
$$R = \begin{bmatrix} R_{11} & R_{12} \\ 0 & R_{22} \end{bmatrix}, \qquad R_{11} \in
  \mathbb{K}^{k \times k},$$
and let $V_2$ and $Z_2$ be the last $N - k$ columns of $V$ and of $Z$. If
$\|R_{22}\| < \sigma_{\min}(R_{11})$, then with $\rho = \|R_{22}\| / \sigma_{\min}(R_{11})$,
$$\operatorname{gap}(\operatorname{ran} V_2, \operatorname{ran} Z_2) \le \frac{\|R_{12}\|}{(1 -
  \rho^2) \, \sigma_{\min}(R_{11})}.$$
This is (5.4.10) of [golub2013matrix], due to Stewart (1993).

The space $\operatorname{ran} Z_2$ is the span of the last $N - k$ right singular vectors of
$A$, and $\sigma_{\min}(R_{11})$ is `R₁₁.sortedSingularValues (k - 1)`. With $Y$ as in
`Matrix.stewart_setting`, the gap is $\|Y_1\|$, and the first block row of $R^H R Y = Y D$
together with $\sigma_k(R) \le \|R_{22}\|$ (`Matrix.sortedSingularValues_le_l2_opNorm_trailing`)
gives $\sigma_{\min} (\sigma_{\min} \|Y_1\| - \|R_{12}\|) \le \|R_{22}\|^2 \|Y_1\|$. -/
theorem gap_le_of_urv {A : Matrix (Fin M) (Fin N) 𝕜} {U : Matrix (Fin M) (Fin M) 𝕜}
    {R : Matrix (Fin M) (Fin N) 𝕜} {V : Matrix (Fin N) (Fin N) 𝕜} (h : IsURV A U R V)
    {W : Matrix (Fin M) (Fin M) 𝕜} {σ : ℕ → ℝ} {Z : Matrix (Fin N) (Fin N) 𝕜}
    (hA : IsSVD A W σ Z) {k : ℕ} (hkM : k ≤ M) (hkN : k ≤ N)
    (hρ : ‖R.submatrix (tailIdx hkM) (tailIdx hkN)‖ <
      (R.submatrix (Fin.castLE hkM) (Fin.castLE hkN)).sortedSingularValues (k - 1)) :
    (LinearMap.range (toEuclideanLin (V.submatrix id (tailIdx hkN)))).gap
        (LinearMap.range (toEuclideanLin (Z.submatrix id (tailIdx hkN)))) ≤
      ‖R.submatrix (Fin.castLE hkM) (tailIdx hkN)‖ /
        ((1 - (‖R.submatrix (tailIdx hkM) (tailIdx hkN)‖ /
            (R.submatrix (Fin.castLE hkM) (Fin.castLE hkN)).sortedSingularValues (k - 1)) ^ 2) *
          (R.submatrix (Fin.castLE hkM) (Fin.castLE hkN)).sortedSingularValues (k - 1)) := by
  set R₁₁ := R.submatrix (Fin.castLE hkM) (Fin.castLE hkN) with hR₁₁
  set R₁₂ := R.submatrix (Fin.castLE hkM) (tailIdx hkN) with hR₁₂
  set R₂₂ := R.submatrix (tailIdx hkM) (tailIdx hkN) with hR₂₂
  set s := R₁₁.sortedSingularValues (k - 1) with hs
  have hs0 : 0 < s := lt_of_le_of_lt (norm_nonneg _) hρ
  have hk : 0 < k := Nat.pos_of_ne_zero fun hk0 => by
    have := R₁₁.sortedSingularValues_eq_zero_of_min_le (k := k - 1) (by simp [hk0])
    linarith
  obtain ⟨D, hY, hD, hiso, -, hgap⟩ :=
    stewart_setting h.mem_unitaryGroup_left h.mem_unitaryGroup_right h.star_mul_mul hA hkN
  set Y := (star V * Z).submatrix id (tailIdx hkN) with hYdef
  set Y₁ := (star V * Z).submatrix (Fin.castLE hkN) (tailIdx hkN) with hY₁def
  set Y₂ := (star V * Z).submatrix (tailIdx hkN) (tailIdx hkN) with hY₂def
  rw [hgap]
  -- `σ_k(R) ≤ ‖R₂₂‖₂`
  have hτ : R.sortedSingularValues k ≤ ‖R₂₂‖ := by
    have hblk : R.submatrix (blockEquiv hkM) (blockEquiv hkN) = fromBlocks R₁₁ R₁₂ 0 R₂₂ := by
      ext (i | i) (j | j)
      · rfl
      · rfl
      · rw [submatrix_apply, blockEquiv_inr, blockEquiv_inl, fromBlocks_apply₂₁, Matrix.zero_apply]
        exact h.apply_eq_zero _ _ (by simp only [val_tailIdx, Fin.val_castLE]; omega)
      · rfl
    have := sortedSingularValues_le_l2_opNorm_trailing R₁₁ R₁₂ R₂₂
    rwa [← hblk, sortedSingularValues_submatrix_equiv, Fintype.card_fin] at this
  -- the first block row of `Rᴴ R Y = Y D`
  have hrel : ∀ w : EuclideanSpace 𝕜 (Fin (N - k)),
      toEuclideanLin R₁₁ᴴ (toEuclideanLin R₁₁ (toEuclideanLin Y₁ w) +
        toEuclideanLin R₁₂ (toEuclideanLin Y₂ w)) = toEuclideanLin Y₁ (toEuclideanLin D w) := by
    intro w
    ext i
    have := congrFun (congrArg (· *ᵥ WithLp.ofLp w) hY) (Fin.castLE hkN i)
    simp only [← mulVec_mulVec] at this
    rw [conjTranspose_mulVec_castLE R hkM hkN,
      show R.submatrix (tailIdx hkM) (Fin.castLE hkN) = 0 by
        ext a b
        exact h.apply_eq_zero _ _ (by simp only [val_tailIdx, Fin.val_castLE]; omega),
      conjTranspose_zero, zero_mulVec, Pi.zero_apply, add_zero] at this
    have e : (fun l => (R *ᵥ (Y *ᵥ WithLp.ofLp w)) (Fin.castLE hkM l)) =
        R₁₁ *ᵥ (Y₁ *ᵥ WithLp.ofLp w) + R₁₂ *ᵥ (Y₂ *ᵥ WithLp.ofLp w) := by
      funext l
      rw [mulVec_castLE R hkM hkN]
      rfl
    rw [e] at this
    exact this
  -- the pointwise estimate
  have hkey : ∀ w : EuclideanSpace 𝕜 (Fin (N - k)), ‖toEuclideanLin Y₁ w‖ ≤
      (‖R₁₂‖ / s + (‖R₂₂‖ / s) ^ 2 * ‖Y₁‖) * ‖w‖ := by
    intro w
    have hY₂ : ‖toEuclideanLin Y₂ w‖ ≤ ‖w‖ :=
      (PiLp.norm_toLp_comp_le 2 (tailIdx_injective hkN) (Y *ᵥ WithLp.ofLp w)).trans (hiso w).le
    have h1 : s * ‖toEuclideanLin R₁₁ (toEuclideanLin Y₁ w) +
        toEuclideanLin R₁₂ (toEuclideanLin Y₂ w)‖ ≤ ‖toEuclideanLin R₁₁ᴴ
          (toEuclideanLin R₁₁ (toEuclideanLin Y₁ w) +
            toEuclideanLin R₁₂ (toEuclideanLin Y₂ w))‖ := by
      have := sortedSingularValues_mul_norm_le R₁₁ᴴ hk
        (toEuclideanLin R₁₁ (toEuclideanLin Y₁ w) + toEuclideanLin R₁₂ (toEuclideanLin Y₂ w))
      rwa [sortedSingularValues_conjTranspose] at this
    rw [hrel] at h1
    have h2 : ‖toEuclideanLin Y₁ (toEuclideanLin D w)‖ ≤ ‖Y₁‖ * (‖R₂₂‖ ^ 2 * ‖w‖) :=
      (norm_toEuclideanLin_apply_le _ _).trans (mul_le_mul_of_nonneg_left ((hD w).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sortedSingularValues_nonneg _ _) hτ 2)
          (norm_nonneg _))) (norm_nonneg _))
    have h3 : s * ‖toEuclideanLin Y₁ w‖ ≤ ‖toEuclideanLin R₁₁ (toEuclideanLin Y₁ w)‖ :=
      sortedSingularValues_mul_norm_le R₁₁ hk (toEuclideanLin Y₁ w)
    have h4 : ‖toEuclideanLin R₁₂ (toEuclideanLin Y₂ w)‖ ≤ ‖R₁₂‖ * ‖w‖ :=
      (norm_toEuclideanLin_apply_le _ _).trans (mul_le_mul_of_nonneg_left hY₂ (norm_nonneg _))
    have h5 := norm_sub_le (toEuclideanLin R₁₁ (toEuclideanLin Y₁ w) +
      toEuclideanLin R₁₂ (toEuclideanLin Y₂ w)) (toEuclideanLin R₁₂ (toEuclideanLin Y₂ w))
    rw [add_sub_cancel_right] at h5
    have hz : s * ‖toEuclideanLin Y₁ w‖ - ‖R₁₂‖ * ‖w‖ ≤ ‖toEuclideanLin R₁₁
        (toEuclideanLin Y₁ w) + toEuclideanLin R₁₂ (toEuclideanLin Y₂ w)‖ := by
      linarith
    have hmain := (mul_le_mul_of_nonneg_left hz hs0.le).trans (h1.trans h2)
    exact le_mul_of_sq_mul_le hs0 (by linarith)
  have hY₁ := l2_opNorm_le_of_forall_norm_toEuclideanLin_le Y₁
    (add_nonneg (div_nonneg (norm_nonneg _) hs0.le) (mul_nonneg (sq_nonneg _) (norm_nonneg _)))
    hkey
  exact le_div_of_le_add_sq_mul hs0 (div_nonneg (norm_nonneg _) hs0.le)
    ((div_lt_one hs0).2 hρ) hY₁

/-- **Stewart's bound for a ULV decomposition**: let $U^H A V = L$ be a ULV decomposition of
$A \in \mathbb{K}^{M \times N}$, let $A = W \Sigma Z^H$ be a singular value decomposition, and
let $k \le M$ and $k \le N$. Split $L$ at $k$,
$$L = \begin{bmatrix} L_{11} & 0 \\ L_{21} & L_{22} \end{bmatrix}, \qquad L_{11} \in
  \mathbb{K}^{k \times k},$$
and let $V_2$ and $Z_2$ be the last $N - k$ columns of $V$ and of $Z$. If
$\|L_{22}\| < \sigma_{\min}(L_{11})$, then with $\rho = \|L_{22}\| / \sigma_{\min}(L_{11})$,
$$\operatorname{gap}(\operatorname{ran} V_2, \operatorname{ran} Z_2) \le \frac{\rho \,
  \|L_{21}\|}{(1 - \rho^2) \, \sigma_{\min}(L_{11})}.$$
This is (5.4.11) of [golub2013matrix], due to Stewart (1993).

The source prints $L_{12}$ in (5.4.11). The only nonzero off-diagonal block of the lower
triangular $L$ is $L_{21}$, and the statement here reads the bound with $L_{21}$.

With $Y$ as in `Matrix.stewart_setting`, the first block row of $L^H L Y = Y D$ is
$L_{11}^H L_{11} Y_1 + L_{21}^H (LY)_2 = Y_1 D$, and $\|LY\| \le \sigma_k(L) \le \|L_{22}\|$
(`Matrix.sortedSingularValues_le_l2_opNorm_trailing_lower`), so that $\sigma_{\min}^2 \|Y_1\|
\le \|L_{22}\|^2 \|Y_1\| + \|L_{22}\| \, \|L_{21}\|$. -/
theorem gap_le_of_ulv {A : Matrix (Fin M) (Fin N) 𝕜} {U : Matrix (Fin M) (Fin M) 𝕜}
    {L : Matrix (Fin M) (Fin N) 𝕜} {V : Matrix (Fin N) (Fin N) 𝕜} (h : IsULV A U L V)
    {W : Matrix (Fin M) (Fin M) 𝕜} {σ : ℕ → ℝ} {Z : Matrix (Fin N) (Fin N) 𝕜}
    (hA : IsSVD A W σ Z) {k : ℕ} (hkM : k ≤ M) (hkN : k ≤ N)
    (hρ : ‖L.submatrix (tailIdx hkM) (tailIdx hkN)‖ <
      (L.submatrix (Fin.castLE hkM) (Fin.castLE hkN)).sortedSingularValues (k - 1)) :
    (LinearMap.range (toEuclideanLin (V.submatrix id (tailIdx hkN)))).gap
        (LinearMap.range (toEuclideanLin (Z.submatrix id (tailIdx hkN)))) ≤
      ‖L.submatrix (tailIdx hkM) (tailIdx hkN)‖ /
          (L.submatrix (Fin.castLE hkM) (Fin.castLE hkN)).sortedSingularValues (k - 1) *
          ‖L.submatrix (tailIdx hkM) (Fin.castLE hkN)‖ /
        ((1 - (‖L.submatrix (tailIdx hkM) (tailIdx hkN)‖ /
            (L.submatrix (Fin.castLE hkM) (Fin.castLE hkN)).sortedSingularValues (k - 1)) ^ 2) *
          (L.submatrix (Fin.castLE hkM) (Fin.castLE hkN)).sortedSingularValues (k - 1)) := by
  set L₁₁ := L.submatrix (Fin.castLE hkM) (Fin.castLE hkN) with hL₁₁
  set L₂₁ := L.submatrix (tailIdx hkM) (Fin.castLE hkN) with hL₂₁
  set L₂₂ := L.submatrix (tailIdx hkM) (tailIdx hkN) with hL₂₂
  set s := L₁₁.sortedSingularValues (k - 1) with hs
  have hs0 : 0 < s := lt_of_le_of_lt (norm_nonneg _) hρ
  have hk : 0 < k := Nat.pos_of_ne_zero fun hk0 => by
    have := L₁₁.sortedSingularValues_eq_zero_of_min_le (k := k - 1) (by simp [hk0])
    linarith
  obtain ⟨D, hY, hD, -, hLY, hgap⟩ :=
    stewart_setting h.mem_unitaryGroup_left h.mem_unitaryGroup_right h.star_mul_mul hA hkN
  set Y := (star V * Z).submatrix id (tailIdx hkN) with hYdef
  set Y₁ := (star V * Z).submatrix (Fin.castLE hkN) (tailIdx hkN) with hY₁def
  rw [hgap]
  -- `σ_k(L) ≤ ‖L₂₂‖₂`
  have hτ : L.sortedSingularValues k ≤ ‖L₂₂‖ := by
    have hblk : L.submatrix (blockEquiv hkM) (blockEquiv hkN) = fromBlocks L₁₁ 0 L₂₁ L₂₂ := by
      ext (i | i) (j | j)
      · rfl
      · rw [submatrix_apply, blockEquiv_inl, blockEquiv_inr, fromBlocks_apply₁₂, Matrix.zero_apply]
        exact h.apply_eq_zero _ _ (by simp only [val_tailIdx, Fin.val_castLE]; omega)
      · rfl
      · rfl
    have := sortedSingularValues_le_l2_opNorm_trailing_lower L₁₁ L₂₁ L₂₂
    rwa [← hblk, sortedSingularValues_submatrix_equiv, Fintype.card_fin] at this
  -- the first block row of `Lᴴ L Y = Y D`
  have hrel : ∀ w : EuclideanSpace 𝕜 (Fin (N - k)),
      toEuclideanLin L₁₁ᴴ (toEuclideanLin L₁₁ (toEuclideanLin Y₁ w)) +
        toEuclideanLin L₂₁ᴴ (WithLp.toLp 2
          ((WithLp.ofLp (toEuclideanLin L (toEuclideanLin Y w))) ∘ tailIdx hkM)) =
        toEuclideanLin Y₁ (toEuclideanLin D w) := by
    intro w
    ext i
    have := congrFun (congrArg (· *ᵥ WithLp.ofLp w) hY) (Fin.castLE hkN i)
    simp only [← mulVec_mulVec] at this
    rw [conjTranspose_mulVec_castLE L hkM hkN] at this
    have e : (fun l => (L *ᵥ (Y *ᵥ WithLp.ofLp w)) (Fin.castLE hkM l)) =
        L₁₁ *ᵥ (Y₁ *ᵥ WithLp.ofLp w) := by
      funext l
      rw [mulVec_castLE L hkM hkN,
        show L.submatrix (Fin.castLE hkM) (tailIdx hkN) = 0 by
          ext a b
          exact h.apply_eq_zero _ _ (by simp only [val_tailIdx, Fin.val_castLE]; omega),
        zero_mulVec, Pi.zero_apply, add_zero]
      rfl
    rw [e] at this
    exact this
  -- the pointwise estimate
  have hkey : ∀ w : EuclideanSpace 𝕜 (Fin (N - k)), ‖toEuclideanLin Y₁ w‖ ≤
      (‖L₂₂‖ / s * ‖L₂₁‖ / s + (‖L₂₂‖ / s) ^ 2 * ‖Y₁‖) * ‖w‖ := by
    intro w
    set q := toEuclideanLin L (toEuclideanLin Y w) with hq
    have hq₂ : ‖(WithLp.toLp 2 ((WithLp.ofLp q) ∘ tailIdx hkM) :
        EuclideanSpace 𝕜 (Fin (M - k)))‖ ≤ ‖L₂₂‖ * ‖w‖ :=
      (PiLp.norm_toLp_comp_le 2 (tailIdx_injective hkM) (WithLp.ofLp q)).trans
        ((hLY w).trans (mul_le_mul_of_nonneg_right hτ (norm_nonneg _)))
    have h1 : s * ‖toEuclideanLin L₁₁ (toEuclideanLin Y₁ w)‖ ≤
        ‖toEuclideanLin L₁₁ᴴ (toEuclideanLin L₁₁ (toEuclideanLin Y₁ w))‖ := by
      have := sortedSingularValues_mul_norm_le L₁₁ᴴ hk
        (toEuclideanLin L₁₁ (toEuclideanLin Y₁ w))
      rwa [sortedSingularValues_conjTranspose] at this
    rw [eq_sub_of_add_eq (hrel w)] at h1
    have h2 : ‖toEuclideanLin Y₁ (toEuclideanLin D w)‖ ≤ ‖Y₁‖ * (‖L₂₂‖ ^ 2 * ‖w‖) :=
      (norm_toEuclideanLin_apply_le _ _).trans (mul_le_mul_of_nonneg_left ((hD w).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sortedSingularValues_nonneg _ _) hτ 2)
          (norm_nonneg _))) (norm_nonneg _))
    have h3 : ‖toEuclideanLin L₂₁ᴴ (WithLp.toLp 2 ((WithLp.ofLp q) ∘ tailIdx hkM))‖ ≤
        ‖L₂₁‖ * (‖L₂₂‖ * ‖w‖) :=
      (norm_toEuclideanLin_apply_le _ _).trans (by
        rw [l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_left hq₂ (norm_nonneg _))
    have h4 := norm_sub_le (toEuclideanLin Y₁ (toEuclideanLin D w))
      (toEuclideanLin L₂₁ᴴ (WithLp.toLp 2 ((WithLp.ofLp q) ∘ tailIdx hkM)))
    have h5 : s * ‖toEuclideanLin Y₁ w‖ ≤ ‖toEuclideanLin L₁₁ (toEuclideanLin Y₁ w)‖ :=
      sortedSingularValues_mul_norm_le L₁₁ hk (toEuclideanLin Y₁ w)
    have hmain : s * (s * ‖toEuclideanLin Y₁ w‖) ≤
        ‖Y₁‖ * (‖L₂₂‖ ^ 2 * ‖w‖) + ‖L₂₁‖ * (‖L₂₂‖ * ‖w‖) :=
      (mul_le_mul_of_nonneg_left h5 hs0.le).trans (h1.trans (h4.trans (add_le_add h2 h3)))
    have hsa : s * (‖L₂₂‖ / s * ‖L₂₁‖) = ‖L₂₂‖ * ‖L₂₁‖ := by
      rw [← mul_assoc, mul_div_cancel₀ _ hs0.ne']
    exact le_mul_of_sq_mul_le hs0 (by rw [hsa]; linarith)
  have hY₁ := l2_opNorm_le_of_forall_norm_toEuclideanLin_le Y₁
    (add_nonneg (div_nonneg (mul_nonneg (div_nonneg (norm_nonneg _) hs0.le) (norm_nonneg _))
      hs0.le) (mul_nonneg (sq_nonneg _) (norm_nonneg _))) hkey
  exact le_div_of_le_add_sq_mul hs0 (div_nonneg (norm_nonneg _) hs0.le)
    ((div_lt_one hs0).2 hρ) hY₁

end Stewart

/-! ### Least squares from a rank-revealing factorization -/

section LeastSquares

variable {r : ℕ}

/-- Let $Q \in \mathbb{K}^{M \times M}$ and $R \in \mathbb{K}^{M \times N}$, let $\sigma$ be a
permutation of the column indices with permutation matrix $\Pi$, let $r \le M$ and $r \le N$,
and let $b \in \mathbb{K}^M$. Let $c \in \mathbb{K}^r$ be the first $r$ entries of $Q^H b$. The
**basic solution** is
$$x_B = \Pi \begin{bmatrix} R_{11}^{-1} c \\ 0 \end{bmatrix},$$
the vector whose permuted coordinates $\Pi^T x_B = x_B \circ \sigma$ are $R_{11}^{-1} c$ on the
first $r$ indices and $0$ on the others. This is the basic solution of §5.5.5 of
[golub2013matrix].

The inverse $R_{11}^{-1}$ is `Matrix.inv`, which is $0$ when $R_{11}$ is singular. In a
rank-revealing pivoted QR factorization, $R_{11}$ is invertible. -/
noncomputable def pivotedBasicSolution (Q : Matrix (Fin M) (Fin M) 𝕜)
    (R : Matrix (Fin M) (Fin N) 𝕜) (σ : Equiv.Perm (Fin N)) (hM : r ≤ M) (hN : r ≤ N)
    (b : EuclideanSpace 𝕜 (Fin M)) : EuclideanSpace 𝕜 (Fin N) :=
  WithLp.toLp 2 (blockVec hN ((R.submatrix (Fin.castLE hM) (Fin.castLE hN))⁻¹ *ᵥ
    fun i => (Qᴴ *ᵥ WithLp.ofLp b) (Fin.castLE hM i)) 0 ∘ σ.symm)

namespace IsPivotedQR.IsRankRevealing

variable {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
  {R : Matrix (Fin M) (Fin N) 𝕜} {σ : Equiv.Perm (Fin N)}

/-- The permuted coordinates $\Pi^T x_B$ of the basic solution are $[R_{11}^{-1} c; 0]$. -/
private theorem basic_comp (h : IsRankRevealing A Q R σ r) (b : EuclideanSpace 𝕜 (Fin M)) :
    WithLp.ofLp (pivotedBasicSolution Q R σ h.le_rows h.le_cols b) ∘ σ =
      blockVec h.le_cols ((R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *ᵥ
        fun i => (Qᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i)) 0 := by
  funext k
  simp [pivotedBasicSolution]

/-- Let $A\Pi = QR$ be a rank-revealing pivoted QR factorization in which $R$ has a revealing block
of size $r$, and let $b \in \mathbb{K}^M$. Then $x \in \mathbb{K}^N$ is a least-squares solution
of $Ax = b$ if and only if the first $r$ equations of $R\Pi^T x = Q^H b$ hold. With
$\Pi^T x = [y; z]$ and $c$ the first $r$ entries of $Q^H b$, these equations are
$$R_{11} y + R_{12} z = c.$$
This is the description of the least-squares solutions in §5.5.5 of [golub2013matrix].

Since $R_{11}$ is invertible, the solutions are the vectors with
$\Pi^T x = [R_{11}^{-1} (c - R_{12} z); z]$ for a free $z \in \mathbb{K}^{N - r}$. With
$Q^H b = [c; d]$, the residual is $\|Ax - b\|^2 = \|R_{11} y + R_{12} z - c\|^2 + \|d\|^2$
(`Matrix.norm_toEuclideanLin_sub_sq_eq_of_eq_mul`). The proof specializes
`Matrix.HasRevealingBlock.isLeastSquaresSolution_iff`, and `WithLp.ofLp x ∘ σ` is the vector
$\Pi^T x$. -/
theorem isLeastSquaresSolution_iff (h : IsRankRevealing A Q R σ r)
    {b : EuclideanSpace 𝕜 (Fin M)} {x : EuclideanSpace 𝕜 (Fin N)} :
    IsLeastSquaresSolution A b x ↔ ∀ i : Fin r,
      (R *ᵥ (WithLp.ofLp x ∘ σ)) (Fin.castLE h.le_rows i) =
        (Qᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i) := by
  rw [h.toHasRevealingBlock.isLeastSquaresSolution_iff h.isQR.mem_unitaryGroup h.eq_mul
    (isUnit_one_submatrix σ), one_submatrix_mulVec]

/-- Let $A\Pi = QR$ be a rank-revealing pivoted QR factorization in which $R$ has a revealing block
of size $r$, and let $b \in \mathbb{K}^M$. Then the basic solution $x_B$ is a least-squares
solution of $Ax = b$, and its permuted coordinates $(x_B)_{\sigma(j)}$ vanish for $j \ge r$, so
that $x_B$ has at most $r$ nonzero entries. This is a statement of §5.5.5 of [golub2013matrix]. -/
theorem isLeastSquaresSolution_basic (h : IsRankRevealing A Q R σ r)
    (b : EuclideanSpace 𝕜 (Fin M)) :
    IsLeastSquaresSolution A b (pivotedBasicSolution Q R σ h.le_rows h.le_cols b) ∧
      ∀ j : Fin (N - r),
        pivotedBasicSolution Q R σ h.le_rows h.le_cols b (σ (tailIdx h.le_cols j)) = 0 := by
  refine ⟨h.isLeastSquaresSolution_iff.2 fun i => ?_, fun j => ?_⟩
  · rw [basic_comp h b, mulVec_blockVec_castLE, mulVec_zero, Pi.zero_apply, add_zero,
      mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 h.isUnit_block), one_mulVec]
  · have := congrFun (basic_comp h b) (tailIdx h.le_cols j)
    simpa using this

/-- The first $r$ permuted coordinates of a least-squares solution $x$ are $R_{11}^{-1} c - S z$,
where $S = R_{11}^{-1} R_{12}$ and $z$ is the vector of the last $N - r$ permuted coordinates of
$x$. -/
private theorem head_eq_of_isLeastSquaresSolution (h : IsRankRevealing A Q R σ r)
    {b : EuclideanSpace 𝕜 (Fin M)} {x : EuclideanSpace 𝕜 (Fin N)}
    (hx : IsLeastSquaresSolution A b x) :
    (fun i => (WithLp.ofLp x ∘ σ) (Fin.castLE h.le_cols i)) =
      (R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *ᵥ
          (fun i => (Qᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i)) -
        ((R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *
          R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols)) *ᵥ
          (fun j => (WithLp.ofLp x ∘ σ) (tailIdx h.le_cols j)) := by
  set B := R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols)
  have hB : B⁻¹ * B = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det B).1 h.isUnit_block)
  have heq : B *ᵥ (fun i => (WithLp.ofLp x ∘ σ) (Fin.castLE h.le_cols i)) +
      R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols) *ᵥ
        (fun j => (WithLp.ofLp x ∘ σ) (tailIdx h.le_cols j)) =
      fun i => (Qᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i) := by
    funext i
    rw [← h.isLeastSquaresSolution_iff.1 hx i, ← blockVec_head_tail h.le_cols
      (WithLp.ofLp x ∘ σ), mulVec_blockVec_castLE, blockVec_head_tail]
    rfl
  rw [← heq, mulVec_add, mulVec_mulVec, hB, one_mulVec, ← mulVec_mulVec, add_sub_cancel_right]

/-- Let $A\Pi = QR$ be a rank-revealing pivoted QR factorization in which $R$ has a revealing block
of size $r$, and let $b \in \mathbb{K}^M$. Then the minimum-norm least-squares solution $A^+ b$
has the least norm on the set of least-squares solutions, written with a free parameter:
$$\|A^+ b\| = \inf_{z \in \mathbb{K}^{N - r}} \left\| x_B - \Pi \begin{bmatrix} R_{11}^{-1}
  R_{12} z \\ -z \end{bmatrix} \right\|.$$
This is (5.5.4) of [golub2013matrix].

The source writes $z \in \mathbb{R}^{n-2}$ where $z \in \mathbb{R}^{n-r}$ is meant. The vectors
$x_B - \Pi [R_{11}^{-1} R_{12} z; -z]$ are exactly the least-squares solutions
(`Matrix.IsPivotedQR.IsRankRevealing.isLeastSquaresSolution_iff`). The pseudoinverse $A^+$ is
`Matrix.pinv`. -/
theorem norm_minNorm_eq_iInf (h : IsRankRevealing A Q R σ r) (b : EuclideanSpace 𝕜 (Fin M)) :
    ‖toEuclideanLin A.pinv b‖ = ⨅ z : Fin (N - r) → 𝕜,
      ‖pivotedBasicSolution Q R σ h.le_rows h.le_cols b - WithLp.toLp 2 (blockVec h.le_cols
        (((R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *
          R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols)) *ᵥ z) (-z) ∘ σ.symm)‖ := by
  set B := R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols)
  set S := B⁻¹ * R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols)
  set c : Fin r → 𝕜 := fun i => (Qᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i)
  set xz : (Fin (N - r) → 𝕜) → EuclideanSpace 𝕜 (Fin N) := fun z =>
    pivotedBasicSolution Q R σ h.le_rows h.le_cols b -
      WithLp.toLp 2 (blockVec h.le_cols (S *ᵥ z) (-z) ∘ σ.symm)
  have hxz : ∀ z, WithLp.ofLp (xz z) ∘ σ = blockVec h.le_cols (B⁻¹ *ᵥ c - S *ᵥ z) z :=
    fun z => by
    funext k
    have := congrFun (basic_comp h b) k
    simp only [Function.comp_apply] at this
    simp only [xz, Function.comp_apply, WithLp.ofLp_sub, Pi.sub_apply, this,
      Equiv.symm_apply_apply]
    unfold blockVec
    split_ifs <;> first | (simp; done) | (simp; rfl)
  -- every `xz z` is a least-squares solution
  have hls : ∀ z, IsLeastSquaresSolution A b (xz z) := fun z =>
    h.isLeastSquaresSolution_iff.2 fun i => by
      have hBB : B * B⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det B).1 h.isUnit_block)
      rw [hxz, mulVec_blockVec_castLE, mulVec_sub, mulVec_mulVec, hBB, one_mulVec,
        mulVec_mulVec, ← Matrix.mul_assoc, hBB, Matrix.one_mul]
      simp [c]
  -- and `A⁺ b` is one of them
  set x₀ := toEuclideanLin A.pinv b
  set z₀ : Fin (N - r) → 𝕜 := fun j => (WithLp.ofLp x₀ ∘ σ) (tailIdx h.le_cols j)
  have hx₀ : xz z₀ = x₀ := by
    have h1 := head_eq_of_isLeastSquaresSolution h (isLeastSquaresSolution_pinv A b)
    have h2 : WithLp.ofLp (xz z₀) ∘ σ = WithLp.ofLp x₀ ∘ σ := by
      rw [hxz, ← h1]
      exact blockVec_head_tail h.le_cols _
    have h3 : WithLp.ofLp (xz z₀) = WithLp.ofLp x₀ := by
      funext k
      simpa using congrFun h2 (σ.symm k)
    exact WithLp.ofLp_injective 2 h3
  refine le_antisymm (le_ciInf fun z => (isMinNormLeastSquaresSolution_pinv A b).2 _ (hls z)) ?_
  rw [← hx₀]
  exact ciInf_le ⟨0, fun _ ⟨z, hz⟩ => hz ▸ norm_nonneg _⟩ z₀

/-- The squared norm of $v \in \mathbb{K}^N$ is the sum of the squared norms of the first $r$ and of
the last $N - r$ entries of $\Pi^T v$. -/
private theorem norm_sq_eq_head_add_tail (h : IsRankRevealing A Q R σ r)
    (v : EuclideanSpace 𝕜 (Fin N)) :
    ‖v‖ ^ 2 = ‖(WithLp.toLp 2 fun i => (WithLp.ofLp v ∘ σ) (Fin.castLE h.le_cols i) :
        EuclideanSpace 𝕜 (Fin r))‖ ^ 2 +
      ‖(WithLp.toLp 2 fun j => (WithLp.ofLp v ∘ σ) (tailIdx h.le_cols j) :
        EuclideanSpace 𝕜 (Fin (N - r)))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Equiv.sum_comp σ, sum_eq_sum_castLE_add_sum_tailIdx h.le_cols]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- The **Golub–Pereyra bound**: let $A\Pi = QR$ be a rank-revealing pivoted QR factorization in
which $R$ has a revealing block of size $r$, and let $b \in \mathbb{K}^M$. Then the basic
solution $x_B$ and the minimum-norm least-squares solution $A^+ b$ satisfy
$$\|A^+ b\| \le \|x_B\| \le \sqrt{1 + \|R_{11}^{-1} R_{12}\|^2} \, \|A^+ b\|.$$
This is (5.5.5) of [golub2013matrix].

The lower bound is the minimality of $A^+ b$. The upper bound follows from $\|x_B\| = \|y + Sz\|
\le \|y\| + \|S\| \, \|z\|$, where $S = R_{11}^{-1} R_{12}$ and $\Pi^T A^+ b = [y; z]$, and the
Cauchy–Schwarz inequality in $\mathbb{R}^2$. -/
theorem norm_basic_le (h : IsRankRevealing A Q R σ r) (b : EuclideanSpace 𝕜 (Fin M)) :
    ‖toEuclideanLin A.pinv b‖ ≤ ‖pivotedBasicSolution Q R σ h.le_rows h.le_cols b‖ ∧
      ‖pivotedBasicSolution Q R σ h.le_rows h.le_cols b‖ ≤
        √(1 + ‖(R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *
          R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols)‖ ^ 2) *
          ‖toEuclideanLin A.pinv b‖ := by
  refine ⟨(isMinNormLeastSquaresSolution_pinv A b).2 _ (h.isLeastSquaresSolution_basic b).1, ?_⟩
  set B := R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols)
  set S := B⁻¹ * R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols)
  set c : Fin r → 𝕜 := fun i => (Qᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i)
  set x₀ := toEuclideanLin A.pinv b
  set y : Fin r → 𝕜 := fun i => (WithLp.ofLp x₀ ∘ σ) (Fin.castLE h.le_cols i)
  set z : Fin (N - r) → 𝕜 := fun j => (WithLp.ofLp x₀ ∘ σ) (tailIdx h.le_cols j)
  have hy : y = B⁻¹ *ᵥ c - S *ᵥ z :=
    head_eq_of_isLeastSquaresSolution h (isLeastSquaresSolution_pinv A b)
  have hB : ‖pivotedBasicSolution Q R σ h.le_rows h.le_cols b‖ =
      ‖(WithLp.toLp 2 (B⁻¹ *ᵥ c) : EuclideanSpace 𝕜 (Fin r))‖ := by
    have := norm_sq_eq_head_add_tail h (pivotedBasicSolution Q R σ h.le_rows h.le_cols b)
    rw [basic_comp h b] at this
    simp only [blockVec_castLE, blockVec_tailIdx, Pi.zero_apply] at this
    have h0 : ‖(WithLp.toLp 2 fun _ : Fin (N - r) => (0 : 𝕜) :
        EuclideanSpace 𝕜 (Fin (N - r)))‖ = 0 := by
      simp [EuclideanSpace.norm_eq]
    rw [h0, zero_pow two_ne_zero, add_zero] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  set a := ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 (Fin r))‖
  set t := ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (Fin (N - r)))‖
  have hx₀ : ‖x₀‖ = √(a ^ 2 + t ^ 2) := by
    rw [← norm_sq_eq_head_add_tail h, Real.sqrt_sq (norm_nonneg _)]
  have htri : ‖(WithLp.toLp 2 (B⁻¹ *ᵥ c) : EuclideanSpace 𝕜 (Fin r))‖ ≤ a + ‖S‖ * t := by
    have e : (WithLp.toLp 2 (B⁻¹ *ᵥ c) : EuclideanSpace 𝕜 (Fin r)) =
        WithLp.toLp 2 y + toEuclideanLin S (WithLp.toLp 2 z) := by
      rw [hy, toEuclideanLin_toLp]
      ext i
      simp
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_toEuclideanLin_apply_le S _))
  rw [hB, hx₀, ← Real.sqrt_mul (by positivity)]
  refine htri.trans (Real.le_sqrt_of_sq_le ?_)
  nlinarith [sq_nonneg (‖S‖ * a - t), norm_nonneg S]

/-- Let $A\Pi = QR$ be a rank-revealing pivoted QR factorization in which $R$ has a revealing block
of size $M$, so that no row of $R$ vanishes and its leading $M \times M$ block $R_1$ is
invertible. Then for every $b \in \mathbb{K}^M$ the basic solution
$$x = \Pi \begin{bmatrix} R_1^{-1} Q^H b \\ 0 \end{bmatrix}$$
solves $Ax = b$. This is the solution of an underdetermined system of full row rank in §5.6.2 of
[golub2013matrix], Algorithm 5.6.1.

A factorization with a revealing block of size $M$ exists exactly when $A$ has linearly
independent rows, by `Matrix.IsPivotedQR.IsRankRevealing.rank_eq` and
`Matrix.exists_isPivotedQR_rank`. -/
theorem mulVec_basic_eq (h : IsRankRevealing A Q R σ M) (b : EuclideanSpace 𝕜 (Fin M)) :
    toEuclideanLin A (pivotedBasicSolution Q R σ h.le_rows h.le_cols b) = b := by
  have hls := (h.isLeastSquaresSolution_basic b).1
  have hR : R *ᵥ (WithLp.ofLp (pivotedBasicSolution Q R σ h.le_rows h.le_cols b) ∘ σ) =
      Qᴴ *ᵥ WithLp.ofLp b := by
    funext i
    exact h.isLeastSquaresSolution_iff.1 hls i
  have hA : ∀ x : Fin N → 𝕜, A *ᵥ x = Q *ᵥ (R *ᵥ (x ∘ σ)) := fun x => by
    rw [mulVec_mulVec, h.isQR.mul_eq]
    ext i
    simp only [mulVec, dotProduct, submatrix_apply, id_eq, Function.comp_apply]
    exact (Equiv.sum_comp σ fun j => A i j * x j).symm
  rw [toEuclideanLin_apply, hA, hR, mulVec_mulVec, ← star_eq_conjTranspose,
    Unitary.mul_star_self_of_mem h.isQR.mem_unitaryGroup, one_mulVec]

end IsPivotedQR.IsRankRevealing

end LeastSquares

/-! ### Subset selection -/

section SubsetSelection

open scoped Matrix.Norms.L2Operator

variable {A : Matrix (Fin M) (Fin N) 𝕜} {U : Matrix (Fin M) (Fin M) 𝕜} {σ : ℕ → ℝ}
  {V : Matrix (Fin N) (Fin N) 𝕜} {r : ℕ}

/-- For a singular value decomposition $A = U \Sigma V^H$ and the first $r$ columns $U_1$ of $U$,
the matrix $U_1 U_1^H A$ is the rank-$r$ truncation $A_r$ of the decomposition. -/
private theorem mul_conjTranspose_mul_eq_svdTruncation (h : IsSVD A U σ V) (hrM : r ≤ M) :
    U.submatrix id (Fin.castLE hrM) * (U.submatrix id (Fin.castLE hrM))ᴴ * A =
      svdTruncation U σ V r := by
  have hUU : (U.submatrix id (Fin.castLE hrM))ᴴ * U =
      (1 : Matrix (Fin M) (Fin M) 𝕜).submatrix (Fin.castLE hrM) id := by
    rw [conjTranspose_submatrix, ← mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_left,
      star_eq_conjTranspose]
    rfl
  have hdiag : U.submatrix id (Fin.castLE hrM) * (U.submatrix id (Fin.castLE hrM))ᴴ * U =
      U * diagonal fun i : Fin M => if (i : ℕ) < r then (1 : 𝕜) else 0 := by
    rw [Matrix.mul_assoc, hUU]
    ext a j
    rw [mul_diagonal, Matrix.mul_apply]
    change ∑ x : Fin r, U a (Fin.castLE hrM x) *
      (1 : Matrix (Fin M) (Fin M) 𝕜) (Fin.castLE hrM x) j = _
    rw [Fin.sum_castLE_eq_sum_ite hrM (fun i => U a i * (1 : Matrix (Fin M) (Fin M) 𝕜) i j),
      Finset.sum_eq_single j (fun i _ hij => by rw [one_apply_ne hij, mul_zero, ite_self])
        (fun hj => absurd (Finset.mem_univ j) hj), one_apply_eq, mul_one]
    split_ifs <;> simp
  have hmask : (diagonal fun i : Fin M => if (i : ℕ) < r then (1 : 𝕜) else 0) *
      (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin M) (Fin N) 𝕜) =
        rectDiagonal fun i => if i < r then ((σ i : ℝ) : 𝕜) else 0 := by
    ext i j
    rw [diagonal_mul, rectDiagonal_apply, rectDiagonal_apply]
    split_ifs <;> simp
  conv_lhs => rw [h.eq_mul_mul_star]
  rw [svdTruncation, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hdiag, Matrix.mul_assoc U, hmask]

/-- Let $A = U \Sigma V^H$ be a singular value decomposition of $A \in \mathbb{K}^{M \times N}$, let
$0 < r$ with $r \le M$, $r \le N$ and $r \le \operatorname{rank} A$, and let $\pi$ be a column
permutation with permutation matrix $\Pi$. Let $B_1$ be the first $r$ columns of $A\Pi$, let
$\tilde V_{11}$ be the leading $r \times r$ block of $\Pi^T V$, and assume that $\tilde V_{11}$
is invertible. Let $U_1$ be the first $r$ columns of $U$. Then for every $b \in \mathbb{K}^M$
the residual $r_x = (I - U_1 U_1^H) b$ of the nearest rank-$r$ problem and the residual
$r_y = (I - B_1 B_1^+) b$ of the subset satisfy
$$\|r_x - r_y\| \le \frac{\sigma_r(A)}{\sigma_{r-1}(A)} \, \|\tilde V_{11}^{-1}\| \, \|b\|.$$
This is Theorem 5.5.3 of [golub2013matrix], which compares subset selection with the nearest
rank-$r$ problem.

Singular values are numbered from $0$, so the quotient $\sigma_r(A) / \sigma_{r-1}(A)$ is
$\sigma_{\tilde r + 1} / \sigma_{\tilde r}$ of the source. The hypothesis
$r \le \operatorname{rank} A$ is implicit in the source and is necessary: for $A = 0$ the right
side is $0$, because $0 / 0 = 0$ in Lean, but the left side need not vanish. The proof writes
$r_x - r_y$ as $(P_{B_1} - P_{U_1}) b$ and bounds the gap between the two $r$-dimensional ranges
with $\|P_{U_1^\perp} B_1 z\| \le \sigma_r(A) \|z\|$ and with Theorem 5.5.2 of
[golub2013matrix], $\sigma_{r-1}(A) \le \|\tilde V_{11}^{-1}\| \, \sigma_{r-1}(B_1)$
(`Matrix.IsSVD.sortedSingularValues_le_mul_submatrix`). -/
theorem norm_residual_subset_sub_le (h : IsSVD A U σ V) (π : Equiv.Perm (Fin N)) (hr0 : 0 < r)
    (hrM : r ≤ M) (hrN : r ≤ N) (hrank : r ≤ A.rank)
    (hV : IsUnit ((V.submatrix π id).submatrix (Fin.castLE hrN) (Fin.castLE hrN)))
    (b : EuclideanSpace 𝕜 (Fin M)) :
    ‖(b - toEuclideanLin (U.submatrix id (Fin.castLE hrM) *
          (U.submatrix id (Fin.castLE hrM))ᴴ) b) -
        (b - toEuclideanLin ((A.submatrix id π).submatrix id (Fin.castLE hrN) *
          ((A.submatrix id π).submatrix id (Fin.castLE hrN)).pinv) b)‖ ≤
      A.sortedSingularValues r / A.sortedSingularValues (r - 1) *
        ‖((V.submatrix π id).submatrix (Fin.castLE hrN) (Fin.castLE hrN))⁻¹‖ * ‖b‖ := by
  have hlow := h.sortedSingularValues_le_mul_submatrix π hr0 hrM hrN hV
  have hsA0 : 0 < A.sortedSingularValues (r - 1) :=
    lt_of_le_of_ne (A.sortedSingularValues_nonneg _)
      (Ne.symm ((A.sortedSingularValues_eq_zero_iff_rank_le _).not.2 (by omega)))
  have hUU : (U.submatrix id (Fin.castLE hrM))ᴴ * U.submatrix id (Fin.castLE hrM) = 1 := by
    rw [conjTranspose_submatrix_mul_submatrix_of_mem_unitaryGroup h.mem_unitaryGroup_left,
      submatrix_one _ (Fin.castLE_injective hrM)]
  have hPA : (1 - U.submatrix id (Fin.castLE hrM) * (U.submatrix id (Fin.castLE hrM))ᴴ) * A =
      A - svdTruncation U σ V r := by
    rw [Matrix.sub_mul, Matrix.one_mul, mul_conjTranspose_mul_eq_svdTruncation h hrM]
  set U₁ := U.submatrix id (Fin.castLE hrM) with hU₁
  set B₁ := (A.submatrix id π).submatrix id (Fin.castLE hrN) with hB₁
  set V₁₁ := (V.submatrix π id).submatrix (Fin.castLE hrN) (Fin.castLE hrN) with hV₁₁
  set sA := A.sortedSingularValues (r - 1) with hsA
  set sB := B₁.sortedSingularValues (r - 1) with hsB
  set K := LinearMap.range (toEuclideanLin B₁) with hK
  set L := LinearMap.range (toEuclideanLin U₁) with hL
  have hsB0 : 0 < sB := lt_of_le_of_ne (B₁.sortedSingularValues_nonneg _) fun h0 => by
    rw [← h0, mul_zero] at hlow
    linarith
  have hPU : ∀ y, toEuclideanLin (U₁ * U₁ᴴ) y = L.starProjection y := fun y => by
    rw [LinearMap.congr_fun (toEuclideanLin_mul_conjTranspose_eq_starProjection hUU) y]
    rfl
  have hPB : ∀ y, toEuclideanLin (B₁ * B₁.pinv) y = K.starProjection y := fun y => by
    rw [LinearMap.congr_fun (mul_pinv_eq_starProjection B₁) y]
    rfl
  -- both ranges have dimension `r`
  have hBinj : Function.Injective (toEuclideanLin B₁) := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    have : sB * ‖z‖ ≤ ‖toEuclideanLin B₁ z‖ := sortedSingularValues_mul_norm_le B₁ hr0 z
    rw [hz, norm_zero] at this
    have h0 : ‖z‖ ≤ 0 := by nlinarith [norm_nonneg z]
    exact norm_eq_zero.1 (le_antisymm h0 (norm_nonneg z))
  have hfin : Module.finrank 𝕜 K = Module.finrank 𝕜 L := by
    rw [hK, hL, LinearMap.finrank_range_of_inj hBinj,
      LinearMap.finrank_range_of_inj (f := toEuclideanLin U₁)
        (toEuclideanLinearIsometry hUU).injective]
  -- the one-sided gap
  have hone : ‖(1 - U₁ * U₁ᴴ) * B₁‖ ≤ A.sortedSingularValues r := by
    have hsub : (1 - U₁ * U₁ᴴ) * B₁ = ((1 - U₁ * U₁ᴴ) * A).submatrix id
        (⟨fun i => π (Fin.castLE hrN i), π.injective.comp (Fin.castLE_injective hrN)⟩ :
          Fin r ↪ Fin N) := rfl
    rw [hsub, ← sortedSingularValues_zero_eq_l2_opNorm]
    refine (sortedSingularValues_submatrix_le _ Function.injective_id
      (Function.Embedding.injective _) 0).trans ?_
    rw [sortedSingularValues_zero_eq_l2_opNorm, hPA, l2_opNorm_sub_svdTruncation h]
  have hgap : K.gap L ≤ A.sortedSingularValues r / sB := by
    rw [Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq K L hfin]
    refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (sortedSingularValues_nonneg _ _)
      hsB0.le) fun y => ?_
    set z := toEuclideanLin B₁.pinv y
    have hKy : K.starProjection y = toEuclideanLin B₁ z := by
      rw [← hPB, toEuclideanLin_mul_apply]
    have hz : sB * ‖z‖ ≤ ‖y‖ := by
      have : sB * ‖z‖ ≤ ‖toEuclideanLin B₁ z‖ := sortedSingularValues_mul_norm_le B₁ hr0 z
      rw [← hKy] at this
      exact this.trans (K.norm_starProjection_apply_le y)
    have hLz : Lᗮ.starProjection (toEuclideanLin B₁ z) =
        toEuclideanLin ((1 - U₁ * U₁ᴴ) * B₁) z := by
      rw [Submodule.starProjection_orthogonal_val, ← hPU,
        toEuclideanLin_mul_apply (1 - U₁ * U₁ᴴ) B₁, map_sub, toEuclideanLin_one,
        LinearMap.sub_apply, LinearMap.id_apply]
    change ‖Lᗮ.starProjection (K.starProjection y)‖ ≤ _
    rw [hKy, hLz]
    refine (norm_toEuclideanLin_apply_le _ _).trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hsB0]
    calc ‖(1 - U₁ * U₁ᴴ) * B₁‖ * ‖z‖ * sB = ‖(1 - U₁ * U₁ᴴ) * B₁‖ * (sB * ‖z‖) := by ring
      _ ≤ A.sortedSingularValues r * ‖y‖ :=
        mul_le_mul hone hz (mul_nonneg hsB0.le (norm_nonneg _)) (sortedSingularValues_nonneg _ _)
  -- the comparison `1 / sB ≤ ‖Ṽ₁₁⁻¹‖ / sA`
  have hcmp : A.sortedSingularValues r / sB ≤ A.sortedSingularValues r / sA * ‖V₁₁⁻¹‖ := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hsB0 hsA0]
    have := mul_le_mul_of_nonneg_left hlow (sortedSingularValues_nonneg A r)
    linarith
  have hdiff : (b - toEuclideanLin (U₁ * U₁ᴴ) b) - (b - toEuclideanLin (B₁ * B₁.pinv) b) =
      K.starProjection b - L.starProjection b := by
    rw [hPU, hPB]
    abel
  rw [hdiff]
  refine (K.norm_starProjection_sub_le_gap_mul L b).trans ?_
  exact mul_le_mul_of_nonneg_right (hgap.trans hcmp) (norm_nonneg _)

end SubsetSelection

end Matrix
