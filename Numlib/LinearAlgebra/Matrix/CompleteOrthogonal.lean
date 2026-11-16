/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.CompleteOrthogonal`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Matrix.RankRevealing
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv

/-!
# Complete orthogonal decompositions

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $A \in \mathbb{K}^{M \times N}$. A
**complete orthogonal decomposition** of $A$ is a factorization
$$U^H A V = \begin{bmatrix} T_{11} & 0 \\ 0 & 0 \end{bmatrix}$$
with $U$ and $V$ unitary and $T_{11}$ a nonsingular $r \times r$ block ((5.4.12) in §5.4.7 and
§5.5.1 of [golub2013matrix]; the decomposition is due to Hanson and Lawson, 1969). Then
$r = \operatorname{rank} A$, the first $r$ columns of $U$ span the range of $A$, and the last
$N - r$ columns of $V$ span the kernel of $A$. If $U^H b = (c, d)$ with $c \in \mathbb{K}^r$, then
$$x_{LS} = V \begin{bmatrix} T_{11}^{-1} c \\ 0 \end{bmatrix}$$
is the least-squares solution of least norm of $Ax \approx b$, and its residual has the norm
$\|d\|$.

## Main definitions

* `Matrix.IsCompleteOrthogonal`: the specification (5.4.12) of [golub2013matrix], a two-sided
  unitary equivalence $U^H A V = T$ whose middle factor $T$ is zero outside a nonsingular leading
  $r \times r$ block.

## Main results

* `Matrix.IsCompleteOrthogonal.hasRevealingBlock`: the middle factor $U^H A V$ has a revealing block
  of size $r$ (`Matrix.HasRevealingBlock`).
* `Matrix.IsCompleteOrthogonal.rank_eq`: the block size $r$ is the rank of $A$.
* `Matrix.IsCompleteOrthogonal.range_eq_span`: the first $r$ columns of $U$ span the range of $A$.
* `Matrix.IsCompleteOrthogonal.ker_eq_span`: the last $N - r$ columns of $V$ span the kernel of $A$.
* `Matrix.IsCompleteOrthogonal.isMinNormLeastSquaresSolution`: the formula for the least-squares
  solution of least norm, and its residual (§5.5.1 of [golub2013matrix]).
* `Matrix.isCompleteOrthogonal_of_svd`: a singular value decomposition is a complete orthogonal
  decomposition.
* `Matrix.exists_isCompleteOrthogonal`: every matrix has a complete orthogonal decomposition with
  $r = \operatorname{rank} A$.

## Implementation notes

* The middle factor $T = U^H A V$ is determined by $U$ and $V$. So it is not a parameter, and the
  structure does not extend `Matrix.IsUnitaryEquiv`. `Matrix.IsCompleteOrthogonal.isUnitaryEquiv` is
  the projection to it, and the facts of unitary algebra ($A = U T V^H$, the invariance of the rank)
  come from there.
* The block structure is stated entrywise: $(U^H A V)_{ij} = 0$ whenever $i \ge r$ or $j \ge r$,
  with the indices $0, 1, \dots$. The leading block is `(Uᴴ * A * V).submatrix (Fin.castLE _)
  (Fin.castLE _)`, as for `Matrix.IsPivotedQR.IsRankRevealing`.
* The rank, the range and the least-squares solution come from the lemmas on
  `Matrix.HasRevealingBlock` in `Numlib.LinearAlgebra.Matrix.RankRevealing`, for $A = U T W$ with
  $W = V^H$.
* Existence is proved from the singular value decomposition. The construction of the source by two
  QR factorizations (a rank-revealing pivoted QR factorization, then a QR factorization of
  $[R_{11} \; R_{12}]^H$) gives another complete orthogonal decomposition.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {M N : ℕ}

/-- A **complete orthogonal decomposition** of $A \in \mathbb{K}^{M \times N}$, (5.4.12) of
[golub2013matrix]. The proposition `Matrix.IsCompleteOrthogonal A U V r` holds if
$U \in \mathbb{K}^{M \times M}$ and $V \in \mathbb{K}^{N \times N}$ are unitary, $r \le M$ and
$r \le N$, the matrix $U^H A V$ is zero outside its leading $r \times r$ block $T_{11}$, and
$T_{11}$ is nonsingular:
$$U^H A V = \begin{bmatrix} T_{11} & 0 \\ 0 & 0 \end{bmatrix}.$$
-/
structure IsCompleteOrthogonal (A : Matrix (Fin M) (Fin N) 𝕜) (U : Matrix (Fin M) (Fin M) 𝕜)
    (V : Matrix (Fin N) (Fin N) 𝕜) (r : ℕ) : Prop where
  /-- The left factor $U$ is unitary. -/
  mem_unitaryGroup_left : U ∈ unitaryGroup (Fin M) 𝕜
  /-- The right factor $V$ is unitary. -/
  mem_unitaryGroup_right : V ∈ unitaryGroup (Fin N) 𝕜
  /-- The block size $r$ is at most the number $M$ of rows. -/
  le_rows : r ≤ M
  /-- The block size $r$ is at most the number $N$ of columns. -/
  le_cols : r ≤ N
  /-- The matrix $U^H A V$ is zero outside its leading $r \times r$ block: its entry $(i, j)$ is $0$
  whenever $i \ge r$ or $j \ge r$. -/
  apply_eq_zero : ∀ (i : Fin M) (j : Fin N), r ≤ (i : ℕ) ∨ r ≤ (j : ℕ) → (Uᴴ * A * V) i j = 0
  /-- The leading $r \times r$ block $T_{11}$ of $U^H A V$ is nonsingular. -/
  isUnit_block : IsUnit ((Uᴴ * A * V).submatrix (Fin.castLE le_rows) (Fin.castLE le_cols))

namespace IsCompleteOrthogonal

variable {A : Matrix (Fin M) (Fin N) 𝕜} {U : Matrix (Fin M) (Fin M) 𝕜}
  {V : Matrix (Fin N) (Fin N) 𝕜} {r : ℕ}

/-- A complete orthogonal decomposition is a two-sided unitary equivalence $U^H A V = T$
(`Matrix.IsUnitaryEquiv`) with the middle factor $T = U^H A V$. -/
theorem isUnitaryEquiv (h : IsCompleteOrthogonal A U V r) :
    IsUnitaryEquiv A U (Uᴴ * A * V) V :=
  isUnitaryEquiv_star_mul_mul h.mem_unitaryGroup_left h.mem_unitaryGroup_right

/-- For a complete orthogonal decomposition, the middle factor $T = U^H A V$ has a revealing block
of size $r$ (`Matrix.HasRevealingBlock`): its rows from the $r$-th on are zero, and its leading
block $T_{11}$ is nonsingular. -/
theorem hasRevealingBlock (h : IsCompleteOrthogonal A U V r) : (Uᴴ * A * V).HasRevealingBlock r :=
  ⟨h.le_rows, h.le_cols, fun i j hi => h.apply_eq_zero i j (Or.inl hi), h.isUnit_block⟩

/-- For a complete orthogonal decomposition, $A = U T V^H$ with $T = U^H A V$. -/
theorem eq_mul (h : IsCompleteOrthogonal A U V r) : A = U * (Uᴴ * A * V) * Vᴴ :=
  h.isUnitaryEquiv.eq_mul_mul

/-- For a complete orthogonal decomposition, the matrix $V^H$ is nonsingular. -/
theorem isUnit_conjTranspose_right (h : IsCompleteOrthogonal A U V r) : IsUnit Vᴴ :=
  isUnit_of_mem_unitaryGroup (conjTranspose_mem_unitaryGroup h.mem_unitaryGroup_right)

/-- **The block size is the rank**. Let $U^H A V$ be a complete orthogonal decomposition of
$A \in \mathbb{K}^{M \times N}$ with the block size $r$. Then $\operatorname{rank} A = r$. This
is in §5.4.7 of [golub2013matrix].

The rank does not change under the unitary factors (`Matrix.IsUnitaryEquiv.rank_eq`), and
$U^H A V$ has a revealing block of size $r$. -/
theorem rank_eq (h : IsCompleteOrthogonal A U V r) : A.rank = r := by
  rw [h.isUnitaryEquiv.rank_eq]
  exact h.hasRevealingBlock.rank_eq

/-- **The range of $A$ is spanned by the first $r$ columns of $U$**. Let $U^H A V$ be a complete
orthogonal decomposition of $A \in \mathbb{K}^{M \times N}$ with the block size $r$. Then the
range of $A$, as a linear map $\mathbb{K}^N \to \mathbb{K}^M$, is the span of the columns
$u_0, \dots, u_{r-1}$ of $U$. This is in §5.4.7 of [golub2013matrix].

The linear map is `Matrix.toEuclideanLin A`, and the columns are vectors of
`EuclideanSpace 𝕜 (Fin M)`. -/
theorem range_eq_span (h : IsCompleteOrthogonal A U V r) :
    LinearMap.range (toEuclideanLin A) =
      Submodule.span 𝕜 (Set.range fun i : Fin r =>
        (WithLp.toLp 2 (U.col (Fin.castLE h.le_rows i)) : EuclideanSpace 𝕜 (Fin M))) :=
  h.hasRevealingBlock.range_toEuclideanLin_eq_span h.eq_mul h.isUnit_conjTranspose_right

/-- For $T = U^H A V$ and a vector $w$, the entry $i$ of $Tw$ is the entry $i$ of $T_{11}$ times the
first $r$ entries of $w$ if $i < r$, and $0$ otherwise. -/
private theorem mulVec_apply (h : IsCompleteOrthogonal A U V r) (w : Fin N → 𝕜) (i : Fin M) :
    ((Uᴴ * A * V) *ᵥ w) i = if hi : (i : ℕ) < r then
      ((Uᴴ * A * V).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols) *ᵥ
        fun k => w (Fin.castLE h.le_cols k)) ⟨i, hi⟩ else 0 := by
  rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx h.le_cols]
  have htail : ∑ j : Fin (N - r), (Uᴴ * A * V) i (tailIdx h.le_cols j) *
      w (tailIdx h.le_cols j) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [h.apply_eq_zero _ _ (Or.inr (by simp)), zero_mul]
  rw [htail, add_zero]
  split_ifs with hi
  · rfl
  · exact Finset.sum_eq_zero fun k _ => by
      rw [h.apply_eq_zero _ _ (Or.inl (by omega)), zero_mul]

/-- **The kernel of $A$ is spanned by the last $N - r$ columns of $V$**. Let $U^H A V$ be a complete
orthogonal decomposition of $A \in \mathbb{K}^{M \times N}$ with the block size $r$. Then the
kernel of $A$, as a linear map $\mathbb{K}^N \to \mathbb{K}^M$, is the span of the columns
$v_r, \dots, v_{N-1}$ of $V$. This is in §5.4.7 of [golub2013matrix].

The proof: $Ax = 0$ if and only if $T_{11}$ maps the first $r$ entries of $V^H x$ to $0$, that
is, if and only if these entries are $0$. The trailing indices are `Matrix.tailIdx`. -/
theorem ker_eq_span (h : IsCompleteOrthogonal A U V r) :
    LinearMap.ker (toEuclideanLin A) =
      Submodule.span 𝕜 (Set.range fun j : Fin (N - r) =>
        (WithLp.toLp 2 (V.col (tailIdx h.le_cols j)) : EuclideanSpace 𝕜 (Fin N))) := by
  classical
  set T := Uᴴ * A * V
  set B := T.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols)
  have hA : ∀ x : Fin N → 𝕜, A *ᵥ x = U *ᵥ (T *ᵥ (Vᴴ *ᵥ x)) := fun x => by
    conv_lhs => rw [h.eq_mul]
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  have hVV := mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_right
  have hVV' := conjTranspose_mul_self_of_mem_unitaryGroup h.mem_unitaryGroup_right
  have hUinj : ∀ y : Fin M → 𝕜, U *ᵥ y = 0 → y = 0 := fun y hy => by
    rw [← one_mulVec y, ← Unitary.star_mul_self_of_mem h.mem_unitaryGroup_left, ← mulVec_mulVec,
      hy, mulVec_zero]
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, toEuclideanLin_apply, hA] at hx
    have hT := hUinj (T *ᵥ (Vᴴ *ᵥ WithLp.ofLp x)) (congrArg WithLp.ofLp hx)
    set w := Vᴴ *ᵥ WithLp.ofLp x
    have hhead : (fun k => w (Fin.castLE h.le_cols k)) = 0 := by
      have hB : B *ᵥ (fun k => w (Fin.castLE h.le_cols k)) = 0 := by
        funext i
        have := congrFun hT (Fin.castLE h.le_rows i)
        rw [mulVec_apply h, dite_eq_left (by simp)] at this
        simpa using this
      rw [← one_mulVec (fun k => w (Fin.castLE h.le_cols k)),
        ← nonsing_inv_mul _ ((isUnit_iff_isUnit_det B).1 h.isUnit_block), ← mulVec_mulVec, hB,
        mulVec_zero]
    have hx' : x = WithLp.toLp 2 (V *ᵥ w) := by
      rw [mulVec_mulVec, hVV, one_mulVec]
    rw [hx', ← toEuclideanLin_toLp, toEuclideanLin_apply_eq_sum,
      sum_eq_sum_castLE_add_sum_tailIdx h.le_cols]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    rw [show w (Fin.castLE h.le_cols i) = 0 from congrFun hhead i, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have hVe : Vᴴ *ᵥ V.col (tailIdx h.le_cols j) = Pi.single (tailIdx h.le_cols j) 1 := by
      funext k
      have := congrFun (congrFun hVV' k) (tailIdx h.le_cols j)
      simpa [mulVec, dotProduct, Matrix.mul_apply, Matrix.col, Pi.single_apply,
          Matrix.one_apply] using this
    change toEuclideanLin A _ = 0
    rw [toEuclideanLin_toLp, hA, hVe]
    have : T *ᵥ Pi.single (tailIdx h.le_cols j) 1 = 0 := by
      funext i
      rw [mulVec_apply h]
      split_ifs
      · rw [mulVec, dotProduct]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Pi.single_apply, ite_eq_right fun e => by
          have := congrArg Fin.val e
          simp at this
          omega, mul_zero]
      · rfl
    rw [this, mulVec_zero]
    rfl

/-- **The least-squares solution of least norm**. Let $U^H A V$ be a complete orthogonal
decomposition of $A \in \mathbb{K}^{M \times N}$ with the block size $r$, let
$b \in \mathbb{K}^M$, and write
$$U^H b = \begin{bmatrix} c \\ d \end{bmatrix}, \qquad c \in \mathbb{K}^r, \; d \in
  \mathbb{K}^{M - r}.$$
Then
$$x_{LS} = V \begin{bmatrix} T_{11}^{-1} c \\ 0 \end{bmatrix}$$
is the least-squares solution of $Ax \approx b$ of least norm
(`Matrix.IsMinNormLeastSquaresSolution`), and its residual has the norm
$\|A x_{LS} - b\| = \|d\|$. This is in §5.5.1 of [golub2013matrix].

With $V^H x = (w, y)$, the proof uses $\|Ax - b\|^2 = \|T_{11} w - c\|^2 + \|d\|^2$ and
$\|x\|^2 = \|w\|^2 + \|y\|^2$. The vector $(T_{11}^{-1} c, 0)$ is `Matrix.blockVec`. -/
theorem isMinNormLeastSquaresSolution (h : IsCompleteOrthogonal A U V r)
    (b : EuclideanSpace 𝕜 (Fin M)) :
    IsMinNormLeastSquaresSolution A b (WithLp.toLp 2 (V *ᵥ blockVec h.le_cols
      (((Uᴴ * A * V).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *ᵥ
        fun i => (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i)) 0)) ∧
    ‖toEuclideanLin A (WithLp.toLp 2 (V *ᵥ blockVec h.le_cols
      (((Uᴴ * A * V).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *ᵥ
        fun i => (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i)) 0)) - b‖ =
      ‖(WithLp.toLp 2 fun j => (Uᴴ *ᵥ WithLp.ofLp b) (tailIdx h.le_rows j) :
        EuclideanSpace 𝕜 (Fin (M - r)))‖ := by
  classical
  set T := Uᴴ * A * V
  set B := T.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols)
  set c : Fin r → 𝕜 := fun i => (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i)
  set y₀ : Fin r → 𝕜 := B⁻¹ *ᵥ c
  set x₀ : EuclideanSpace 𝕜 (Fin N) := WithLp.toLp 2 (V *ᵥ blockVec h.le_cols y₀ 0)
  have hVV' := conjTranspose_mul_self_of_mem_unitaryGroup h.mem_unitaryGroup_right
  have hlsq := fun {x : EuclideanSpace 𝕜 (Fin N)} =>
    h.hasRevealingBlock.isLeastSquaresSolution_iff (b := b) (x := x) h.mem_unitaryGroup_left
      h.eq_mul h.isUnit_conjTranspose_right
  -- the head of `Vᴴ x` for a least-squares solution
  have hhead : ∀ x : EuclideanSpace 𝕜 (Fin N), IsLeastSquaresSolution A b x →
      (fun k => (Vᴴ *ᵥ WithLp.ofLp x) (Fin.castLE h.le_cols k)) = y₀ := fun x hx => by
    have hB : B *ᵥ (fun k => (Vᴴ *ᵥ WithLp.ofLp x) (Fin.castLE h.le_cols k)) = c := by
      funext i
      have := (hlsq.1 hx) i
      rw [mulVec_apply h, dite_eq_left (by simp)] at this
      exact this
    rw [← one_mulVec (fun k => (Vᴴ *ᵥ WithLp.ofLp x) (Fin.castLE h.le_cols k)),
      ← nonsing_inv_mul _ ((isUnit_iff_isUnit_det B).1 h.isUnit_block), ← mulVec_mulVec, hB]
  have hx₀V : Vᴴ *ᵥ WithLp.ofLp x₀ = blockVec h.le_cols y₀ 0 := by
    change Vᴴ *ᵥ (V *ᵥ _) = _
    rw [mulVec_mulVec, hVV', one_mulVec]
  have hx₀ : IsLeastSquaresSolution A b x₀ := hlsq.2 fun i => by
    rw [hx₀V, mulVec_blockVec_castLE, mulVec_zero, Pi.zero_apply, add_zero, mulVec_mulVec,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det B).1 h.isUnit_block), one_mulVec]
  -- norms through `Vᴴ`
  have hnorm : ∀ x : EuclideanSpace 𝕜 (Fin N), ‖x‖ ^ 2 =
      ‖(WithLp.toLp 2 fun k => (Vᴴ *ᵥ WithLp.ofLp x) (Fin.castLE h.le_cols k) :
        EuclideanSpace 𝕜 (Fin r))‖ ^ 2 +
      ‖(WithLp.toLp 2 fun j => (Vᴴ *ᵥ WithLp.ofLp x) (tailIdx h.le_cols j) :
        EuclideanSpace 𝕜 (Fin (N - r)))‖ ^ 2 := fun x => by
    rw [← norm_toEuclideanLin_apply_of_mem_unitaryGroup
        (conjTranspose_mem_unitaryGroup h.mem_unitaryGroup_right) x, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      sum_eq_sum_castLE_add_sum_tailIdx h.le_cols]
    rfl
  refine ⟨⟨hx₀, fun x hx => ?_⟩, ?_⟩
  · refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [hnorm x, hnorm x₀, hhead x hx, hhead x₀ hx₀]
    exact add_le_add le_rfl (by
      rw [hx₀V]
      simp only [blockVec_tailIdx, Pi.zero_apply]
      rw [show (WithLp.toLp 2 fun _ : Fin (N - r) => (0 : 𝕜) : EuclideanSpace 𝕜 (Fin (N - r))) =
        0 from rfl, norm_zero, zero_pow two_ne_zero]
      exact sq_nonneg _)
  · have := norm_toEuclideanLin_sub_sq_eq_of_eq_mul h.mem_unitaryGroup_left h.le_rows h.eq_mul
      (fun i j hi => h.apply_eq_zero i j (Or.inl hi)) b x₀
    have e : ‖(WithLp.toLp 2 fun j => (Uᴴ *ᵥ WithLp.ofLp b) (tailIdx h.le_rows j) :
        EuclideanSpace 𝕜 (Fin (M - r)))‖ ^ 2 =
        ∑ j : Fin (M - r), ‖(Uᴴ *ᵥ WithLp.ofLp b) (tailIdx h.le_rows j)‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    rw [Finset.sum_eq_zero fun i _ => by rw [(hlsq.1 hx₀) i, sub_self, norm_zero,
      zero_pow two_ne_zero], zero_add, ← e] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

end IsCompleteOrthogonal

/-- **A singular value decomposition is a complete orthogonal decomposition**. Let
$U^H A V = \Sigma$ be a singular value decomposition of $A \in \mathbb{K}^{M \times N}$
(`Matrix.IsSVD`). Then $U^H A V$ is a complete orthogonal decomposition of $A$ with the block
size $r = \operatorname{rank} A$. This is in §5.4.7 of [golub2013matrix].

The entries outside the leading $r \times r$ block are zero, because $\sigma_i = 0$ for
$i \ge r$. The leading block is $\operatorname{diag}(\sigma_0, \dots, \sigma_{r-1})$, with
$\sigma_i > 0$ for $i < r$ (`Matrix.sortedSingularValues_eq_zero_iff_rank_le`). -/
theorem isCompleteOrthogonal_of_svd {A : Matrix (Fin M) (Fin N) 𝕜} {U : Matrix (Fin M) (Fin M) 𝕜}
    {σ : ℕ → ℝ} {V : Matrix (Fin N) (Fin N) 𝕜} (h : IsSVD A U σ V) :
    IsCompleteOrthogonal A U V A.rank := by
  classical
  have hrM : A.rank ≤ M := A.rank_le_height
  have hrN : A.rank ≤ N := by simpa using A.rank_le_card_width
  have hT : Uᴴ * A * V = rectDiagonal fun i => ((σ i : ℝ) : 𝕜) := h.star_mul_mul
  have hσ : ∀ i, i < M → i < N → (σ i = 0 ↔ A.rank ≤ i) := fun i hiM hiN => by
    rw [h.singularValues_eq hiM hiN, sortedSingularValues_eq_zero_iff_rank_le]
  refine ⟨h.mem_unitaryGroup_left, h.mem_unitaryGroup_right, hrM, hrN, fun i j hij => ?_, ?_⟩
  · rw [hT, rectDiagonal_apply]
    split_ifs with hij'
    · have hi : A.rank ≤ (i : ℕ) := by omega
      rw [(hσ i i.isLt (by omega)).2 hi, RCLike.ofReal_zero]
    · rfl
  · rw [hT]
    have : (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin M) (Fin N) 𝕜).submatrix
        (Fin.castLE hrM) (Fin.castLE hrN) = diagonal fun i : Fin A.rank => ((σ i : ℝ) : 𝕜) := by
      ext i j
      simp [rectDiagonal_apply, diagonal_apply, Fin.ext_iff]
    rw [this, isUnit_iff_isUnit_det, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    rw [Ne, RCLike.ofReal_eq_zero, hσ i (by omega) (by omega)]
    omega

/-- **Every matrix has a complete orthogonal decomposition**. For every
$A \in \mathbb{K}^{M \times N}$, there are unitary matrices $U$ and $V$ such that $U^H A V$ is a
complete orthogonal decomposition of $A$ with the block size $r = \operatorname{rank} A$. This
is in §5.4.7 of [golub2013matrix].

A singular value decomposition is one (`Matrix.isCompleteOrthogonal_of_svd`). -/
theorem exists_isCompleteOrthogonal (A : Matrix (Fin M) (Fin N) 𝕜) :
    ∃ U V, IsCompleteOrthogonal A U V A.rank := by
  obtain ⟨U, σ, V, h⟩ := exists_isSVD A
  exact ⟨U, V, isCompleteOrthogonal_of_svd h⟩

end Matrix
