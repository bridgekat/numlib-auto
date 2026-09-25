/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.CompleteOrthogonal`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Matrix.RankRevealing

/-!
# Complete orthogonal decompositions

A complete orthogonal decomposition of `A : Matrix (Fin M) (Fin N) 𝕜` is `Uᴴ A V = [T₁₁ 0; 0 0]`
with `U`, `V` unitary and `T₁₁` an invertible `r × r` block ([golub2013matrix] §5.4.7 (5.4.12),
§5.5.1; Hanson–Lawson 1969). Then `r = rank A`, the first `r` columns of `U` span the range of
`A`, the last `N − r` columns of `V` span its kernel, and `x_LS = V [T₁₁⁻¹ c; 0]` (`Uᴴ b = [c; d]`)
is the minimal-norm least-squares solution, with residual `‖d‖`.

## Main definitions

* `Matrix.IsCompleteOrthogonal A U V r`: the specification (5.4.12).

## Main results

* `Matrix.IsCompleteOrthogonal.rank_eq`, `…range_eq_span`, `…ker_eq_span`.
* `Matrix.isCompleteOrthogonal_of_svd`: an SVD is a complete orthogonal decomposition, so every
  matrix has one (`Matrix.exists_isCompleteOrthogonal`).
* `Matrix.IsCompleteOrthogonal.isMinNormLeastSquaresSolution` ([golub2013matrix] §5.5.1).

## Implementation notes

The block structure is expressed entrywise, `(Uᴴ A V) i j = 0` whenever `r ≤ i` or `r ≤ j`, and
the leading block is `(Uᴴ A V).submatrix (Fin.castLE _) (Fin.castLE _)`, as for
`Matrix.IsPivotedQR.IsRankRevealing`; rank, range and least squares go through the shared
`A = U T W` lemmas of `Numlib/LinearAlgebra/Matrix/RankRevealing` with `W = Vᴴ`. Existence is
proved from the SVD; the book's construction by two QR factorizations (a rank-revealing pivoted
QR, then a QR of `[R₁₁ R₁₂]ᴴ`) produces another instance.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {M N : ℕ}

/-- **A complete orthogonal decomposition** ([golub2013matrix] (5.4.12)): `U` and `V` unitary,
`Uᴴ A V` zero outside its leading `r × r` block `T₁₁`, and `T₁₁` invertible. -/
structure IsCompleteOrthogonal (A : Matrix (Fin M) (Fin N) 𝕜) (U : Matrix (Fin M) (Fin M) 𝕜)
    (V : Matrix (Fin N) (Fin N) 𝕜) (r : ℕ) : Prop where
  /-- The left factor is unitary. -/
  mem_unitaryGroup_left : U ∈ unitaryGroup (Fin M) 𝕜
  /-- The right factor is unitary. -/
  mem_unitaryGroup_right : V ∈ unitaryGroup (Fin N) 𝕜
  /-- The block size does not exceed the number of rows. -/
  le_rows : r ≤ M
  /-- The block size does not exceed the number of columns. -/
  le_cols : r ≤ N
  /-- `Uᴴ A V` vanishes outside its leading `r × r` block. -/
  apply_eq_zero : ∀ (i : Fin M) (j : Fin N), r ≤ (i : ℕ) ∨ r ≤ (j : ℕ) → (Uᴴ * A * V) i j = 0
  /-- The leading block `T₁₁` is invertible. -/
  isUnit_block : IsUnit ((Uᴴ * A * V).submatrix (Fin.castLE le_rows) (Fin.castLE le_cols))

namespace IsCompleteOrthogonal

variable {A : Matrix (Fin M) (Fin N) 𝕜} {U : Matrix (Fin M) (Fin M) 𝕜}
  {V : Matrix (Fin N) (Fin N) 𝕜} {r : ℕ}

/-- `A = U T Vᴴ` with `T = Uᴴ A V`. -/
theorem eq_mul (h : IsCompleteOrthogonal A U V r) : A = U * (Uᴴ * A * V) * Vᴴ := by
  rw [← star_eq_conjTranspose, ← star_eq_conjTranspose]
  simp only [← Matrix.mul_assoc, Unitary.mul_star_self_of_mem h.mem_unitaryGroup_left,
    Matrix.one_mul]
  rw [Matrix.mul_assoc, Unitary.mul_star_self_of_mem h.mem_unitaryGroup_right, Matrix.mul_one]

/-- The adjoint of the right factor is invertible. -/
theorem isUnit_conjTranspose_right (h : IsCompleteOrthogonal A U V r) : IsUnit Vᴴ := by
  rw [← star_eq_conjTranspose]
  exact isUnit_of_mem_unitaryGroup (Unitary.star_mem h.mem_unitaryGroup_right)

/-- **The block size is the rank** ([golub2013matrix] §5.4.7): rank is invariant under the unitary
factors, and `Uᴴ A V` has a revealing block. -/
theorem rank_eq (h : IsCompleteOrthogonal A U V r) : A.rank = r := by
  classical
  rw [h.eq_mul, rank_mul_eq_left_of_isUnit_det _ _
      ((isUnit_iff_isUnit_det _).1 h.isUnit_conjTranspose_right),
    rank_mul_eq_right_of_isUnit_det _ _
      ((isUnit_iff_isUnit_det U).1 (isUnit_of_mem_unitaryGroup h.mem_unitaryGroup_left))]
  exact rank_eq_of_apply_eq_zero_of_isUnit h.le_rows h.le_cols
    (fun i j hi => h.apply_eq_zero i j (Or.inl hi)) h.isUnit_block

/-- **The range of `A` is spanned by the first `r` columns of `U`** ([golub2013matrix] §5.4.7). -/
theorem range_eq_span (h : IsCompleteOrthogonal A U V r) :
    LinearMap.range (toEuclideanLin A) =
      Submodule.span 𝕜 (Set.range fun i : Fin r =>
        (WithLp.toLp 2 (U.col (Fin.castLE h.le_rows i)) : EuclideanSpace 𝕜 (Fin M))) :=
  range_toEuclideanLin_eq_span_of_eq_mul h.le_rows h.le_cols h.eq_mul
    h.isUnit_conjTranspose_right (fun i j hi => h.apply_eq_zero i j (Or.inl hi)) h.isUnit_block

/-- `T w` for `T = Uᴴ A V`: the leading block acts on the head of `w`, and nothing else
survives. -/
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

/-- **The kernel of `A` is spanned by the last `N − r` columns of `V`** ([golub2013matrix]
§5.4.7): `A x = 0` iff `T₁₁` kills the head of `Vᴴ x`, i.e. iff the head vanishes. -/
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
  have hVV : V * Vᴴ = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem h.mem_unitaryGroup_right
  have hVV' : Vᴴ * V = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem h.mem_unitaryGroup_right
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
      simpa [mulVec, dotProduct, mul_apply, Matrix.col, Pi.single_apply, one_apply] using this
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

/-- **The minimal-norm least-squares solution** ([golub2013matrix] §5.5.1): with `Uᴴ b = [c; d]`
and `T₁₁` the leading block, `x_LS = V [T₁₁⁻¹ c; 0]` is the least-squares solution of least
norm, and the least residual is `‖d‖`. Writing `Vᴴ x = [w; y]`,
`‖A x − b‖² = ‖T₁₁ w − c‖² + ‖d‖²` and `‖x‖² = ‖w‖² + ‖y‖²`. -/
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
  have hVV' : Vᴴ * V = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem h.mem_unitaryGroup_right
  have hlsq := fun {x : EuclideanSpace 𝕜 (Fin N)} =>
    isLeastSquaresSolution_iff_of_eq_mul (b := b) (x := x) h.mem_unitaryGroup_left h.le_rows
      h.le_cols h.eq_mul h.isUnit_conjTranspose_right
      (fun i j hi => h.apply_eq_zero i j (Or.inl hi)) h.isUnit_block
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
    have hVu : Vᴴ ∈ unitaryGroup (Fin N) 𝕜 := by
      rw [← star_eq_conjTranspose]
      exact Unitary.star_mem h.mem_unitaryGroup_right
    rw [← norm_toEuclideanLin_apply_of_mem_unitaryGroup hVu x, EuclideanSpace.norm_sq_eq,
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

/-- **An SVD is a complete orthogonal decomposition** ([golub2013matrix] §5.4.7): if
`Uᴴ A V = rectDiagonal σ` is an SVD, then with `r = rank A` the entries outside the leading
`r × r` block vanish (`σ i = 0` from the `r`-th on) and the leading block is `diagonal σ` with
`σ i > 0` for `i < r` (`Matrix.sortedSingularValues_eq_zero_iff_rank_le`). -/
theorem isCompleteOrthogonal_of_svd {A : Matrix (Fin M) (Fin N) 𝕜} {U : Matrix (Fin M) (Fin M) 𝕜}
    {σ : ℕ → ℝ} {V : Matrix (Fin N) (Fin N) 𝕜} (h : IsSVD A U σ V) :
    IsCompleteOrthogonal A U V A.rank := by
  classical
  have hrM : A.rank ≤ M := A.rank_le_height
  have hrN : A.rank ≤ N := by simpa using A.rank_le_card_width
  have hT : Uᴴ * A * V = rectDiagonal fun i => ((σ i : ℝ) : 𝕜) := by
    rw [← star_eq_conjTranspose]
    exact h.star_mul_mul
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

/-- **Every matrix has a complete orthogonal decomposition** with `r = rank A`
([golub2013matrix] §5.4.7), for instance an SVD (`Matrix.isCompleteOrthogonal_of_svd`). -/
theorem exists_isCompleteOrthogonal (A : Matrix (Fin M) (Fin N) 𝕜) :
    ∃ U V, IsCompleteOrthogonal A U V A.rank := by
  obtain ⟨U, σ, V, h⟩ := exists_isSVD A
  exact ⟨U, V, isCompleteOrthogonal_of_svd h⟩

end Matrix
