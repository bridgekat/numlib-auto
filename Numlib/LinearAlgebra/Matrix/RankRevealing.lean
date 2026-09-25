/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.RankRevealing`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.Rank

/-!
# Rank-revealing orthogonal factorizations

QR factorization with column pivoting in its rank-revealing form, the `UTV` decompositions of
Stewart, and the least-squares solutions they produce ([golub2013matrix] §5.4.2–§5.4.6,
§5.5.5, §5.6.2; Businger–Golub 1965, Chan 1987, Stewart 1993, Golub–Pereyra).

## Main definitions

* `Matrix.IsPivotedQR.IsRankRevealing A Q R σ r`: a pivoted QR factorization `A Π = Q R` whose
  rows from the `r`-th on vanish and whose leading `r × r` block `R₁₁` is invertible
  ([golub2013matrix] (5.4.6)); then `r = rank A`.
* `Matrix.IsURV A U R V`, `Matrix.IsULV A U L V`: the two-sided orthogonal decompositions
  `Uᴴ A V = R` (upper triangular) and `Uᴴ A V = L` (lower triangular) of Stewart (1993).
* `Matrix.pivotedBasicSolution`: the basic solution `x_B = Π [R₁₁⁻¹ c; 0]` of §5.5.5.

## Main results

* `Matrix.exists_isPivotedQR_rank`: every matrix has a rank-revealing pivoted QR factorization
  with `r = rank A` — permute a basis of the column space to the front; then *any* QR
  factorization of the permuted matrix has the shape, no pivoting rule is needed for existence.
* `Matrix.IsPivotedQR.IsRankRevealing.range_eq_span`: `ran A = span {q₁, …, q_r}`.
* `Matrix.exists_perm_isQR_abs_le` ([golub2013matrix] Theorem 5.4.1, Chan): some column
  permutation makes the last diagonal entry of every QR factor at most `√n ‖A v‖`.
* `Matrix.IsPivotedQR.IsRankRevealing.isLeastSquaresSolution_iff`,
  `…norm_minNorm_eq_iInf`, `…norm_basic_le` ((5.5.4), (5.5.5)) and `…mulVec_basic_eq`
  (Algorithm 5.6.1): the least-squares solutions of a rank-deficient problem read off a
  rank-revealing factorization.

## Implementation notes

Blocks are expressed by index maps rather than `fromBlocks` and a reindexing: the leading block is
`R.submatrix (Fin.castLE _) (Fin.castLE _)`, the trailing indices are `Matrix.tailIdx`, and a
vector split `[y; z]` on `Fin N` is `Matrix.blockVec`. The column permutation `Π` acts through
`A.submatrix id σ`, i.e. `(A Π) x = A (x ∘ σ⁻¹)`.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {M N : ℕ}

/-! ### Block indices -/

section Blocks

variable {α : Type*} {r : ℕ}

/-- The trailing indices `r, r + 1, …, N − 1` of `Fin N`, indexed by `Fin (N − r)`. -/
def tailIdx (h : r ≤ N) (j : Fin (N - r)) : Fin N := ⟨r + j, by omega⟩

omit [RCLike 𝕜] in
/-- The value of a trailing index. -/
@[simp]
theorem val_tailIdx (h : r ≤ N) (j : Fin (N - r)) : (tailIdx h j : ℕ) = r + j := rfl

/-- The vector `[y; z]` on `Fin N`, with `y` on the first `r` indices and `z` on the rest. -/
def blockVec (h : r ≤ N) (y : Fin r → α) (z : Fin (N - r) → α) : Fin N → α :=
  fun k => if hk : (k : ℕ) < r then y ⟨k, hk⟩ else z ⟨k - r, by omega⟩

/-- The head of `[y; z]` is `y`. -/
@[simp]
theorem blockVec_castLE (h : r ≤ N) (y : Fin r → α) (z : Fin (N - r) → α) (i : Fin r) :
    blockVec h y z (Fin.castLE h i) = y i := by
  simp [blockVec]

/-- The tail of `[y; z]` is `z`. -/
@[simp]
theorem blockVec_tailIdx (h : r ≤ N) (y : Fin r → α) (z : Fin (N - r) → α) (j : Fin (N - r)) :
    blockVec h y z (tailIdx h j) = z j := by
  simp [blockVec, tailIdx]

/-- A sum over `Fin N` splits into the leading `r` and the trailing `N − r` indices. -/
theorem sum_eq_sum_castLE_add_sum_tailIdx {β : Type*} [AddCommMonoid β] (h : r ≤ N)
    (f : Fin N → β) :
    ∑ k, f k = ∑ i : Fin r, f (Fin.castLE h i) + ∑ j : Fin (N - r), f (tailIdx h j) := by
  classical
  set g : ℕ → β := fun k => if hk : k < N then f ⟨k, hk⟩ else 0 with hg
  have h1 : ∑ k, f k = ∑ k ∈ Finset.range N, g k := by
    rw [← Fin.sum_univ_eq_sum_range g N]
    exact Finset.sum_congr rfl fun k _ => by simp [hg]
  have h2 : ∑ i : Fin r, f (Fin.castLE h i) = ∑ k ∈ Finset.range r, g k := by
    rw [← Fin.sum_univ_eq_sum_range g r]
    exact Finset.sum_congr rfl fun i _ => by simp [hg, Fin.castLE, show (i : ℕ) < N by omega]
  have h3 : ∑ j : Fin (N - r), f (tailIdx h j) = ∑ k ∈ Finset.range (N - r), g (r + k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => g (r + k)) (N - r)]
    exact Finset.sum_congr rfl fun j _ => by simp [hg, tailIdx, show r + (j : ℕ) < N by omega]
  rw [h1, h2, h3, ← Finset.sum_range_add, Nat.add_sub_cancel' h]

/-- Every vector on `Fin N` is the block vector of its head and tail. -/
theorem blockVec_head_tail (h : r ≤ N) (x : Fin N → α) :
    blockVec h (fun i => x (Fin.castLE h i)) (fun j => x (tailIdx h j)) = x := by
  funext k
  unfold blockVec
  split_ifs with hk
  · rfl
  · exact congrArg x (Fin.ext (by simp; omega))

end Blocks

/-! ### Factorizations `A = U T W` with a revealing block

The rank-revealing pivoted QR factorization (`W = Πᵀ`) and the complete orthogonal decomposition
(`W = Vᴴ`, in `Numlib/LinearAlgebra/Matrix/CompleteOrthogonal`) are both factorizations
`A = U T W` with `U` unitary, `W` invertible, the rows of `T` from the `r`-th on zero and the
leading `r × r` block `T₁₁` invertible. Rank, range and least-squares solutions are read off
such a factorization once, here. -/

section RevealingBlock

variable {r : ℕ}

/-- The rows of `T [y; z]` above the `r`-th: `T₁₁ y + T₁₂ z`. -/
theorem mulVec_blockVec_castLE (T : Matrix (Fin M) (Fin N) 𝕜) (hM : r ≤ M) (hN : r ≤ N)
    (y : Fin r → 𝕜) (z : Fin (N - r) → 𝕜) (i : Fin r) :
    (T *ᵥ blockVec hN y z) (Fin.castLE hM i) =
      (T.submatrix (Fin.castLE hM) (Fin.castLE hN) *ᵥ y) i +
        (T.submatrix (Fin.castLE hM) (tailIdx hN) *ᵥ z) i := by
  rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx hN]
  simp [mulVec, dotProduct]

/-- **A revealing block has the rank**: a matrix whose rows from the `r`-th on vanish and whose
leading `r × r` block is invertible has rank `r` — at most `r` nonzero rows, and an invertible
`r × r` submatrix. -/
theorem rank_eq_of_apply_eq_zero_of_isUnit {T : Matrix (Fin M) (Fin N) 𝕜} (hM : r ≤ M)
    (hN : r ≤ N) (hz : ∀ (i : Fin M) (j : Fin N), r ≤ (i : ℕ) → T i j = 0)
    (hu : IsUnit (T.submatrix (Fin.castLE hM) (Fin.castLE hN))) : T.rank = r := by
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

/-- **The range of `A = U T W` is spanned by the first `r` columns of `U`**, when `W` is
invertible, the rows of `T` from the `r`-th on vanish and `T₁₁` is invertible: `A x = U (T W x)`
has zero coordinates from the `r`-th on, and `u_i = A W⁻¹ [T₁₁⁻¹ e_i; 0]`. -/
theorem range_toEuclideanLin_eq_span_of_eq_mul (hM : r ≤ M) (hN : r ≤ N) (hA : A = U * T * W)
    (hW : IsUnit W) (hz : ∀ (i : Fin M) (j : Fin N), r ≤ (i : ℕ) → T i j = 0)
    (hu : IsUnit (T.submatrix (Fin.castLE hM) (Fin.castLE hN))) :
    LinearMap.range (toEuclideanLin A) =
      Submodule.span 𝕜 (Set.range fun i : Fin r =>
        (WithLp.toLp 2 (U.col (Fin.castLE hM i)) : EuclideanSpace 𝕜 (Fin M))) := by
  classical
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

/-- **The residual splits**: for `A = U T W` with `U` unitary and the rows of `T` from the `r`-th
on zero, `‖A x − b‖²` is the squared residual of the first `r` equations of `T (W x) = Uᴴ b`
plus the squared norm of the trailing part of `Uᴴ b`. -/
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

/-- **The least-squares solutions of `A = U T W`**: when `U` is unitary, `W` invertible, the rows
of `T` from the `r`-th on zero and `T₁₁` invertible, `x` is a least-squares solution of `A x = b`
exactly when the first `r` equations of `T (W x) = Uᴴ b` hold. The residual is then the trailing
part of `Uᴴ b`, and `W⁻¹ [T₁₁⁻¹ c; 0]` attains it. -/
theorem isLeastSquaresSolution_iff_of_eq_mul (hU : U ∈ unitaryGroup (Fin M) 𝕜) (hM : r ≤ M)
    (hN : r ≤ N) (hA : A = U * T * W) (hW : IsUnit W)
    (hz : ∀ (i : Fin M) (j : Fin N), r ≤ (i : ℕ) → T i j = 0)
    (hu : IsUnit (T.submatrix (Fin.castLE hM) (Fin.castLE hN))) {b : EuclideanSpace 𝕜 (Fin M)}
    {x : EuclideanSpace 𝕜 (Fin N)} :
    IsLeastSquaresSolution A b x ↔ ∀ i : Fin r,
      (T *ᵥ (W *ᵥ WithLp.ofLp x)) (Fin.castLE hM i) = (Uᴴ *ᵥ WithLp.ofLp b) (Fin.castLE hM i) := by
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

/-- **A rank-revealing pivoted QR factorization** ([golub2013matrix] (5.4.6)): `A Π = Q R`
(`Matrix.IsPivotedQR`) with the rows of `R` from the `r`-th on zero and the leading `r × r`
block `R₁₁` invertible, `R = [R₁₁ R₁₂; 0 0]`. Then `r = rank A`
(`Matrix.IsPivotedQR.IsRankRevealing.rank_eq`); it always exists with `r = rank A`
(`Matrix.exists_isPivotedQR_rank`). The one hypothesis of the least-squares statements below. -/
structure IsPivotedQR.IsRankRevealing (A : Matrix (Fin M) (Fin N) 𝕜)
    (Q : Matrix (Fin M) (Fin M) 𝕜) (R : Matrix (Fin M) (Fin N) 𝕜) (σ : Equiv.Perm (Fin N))
    (r : ℕ) : Prop extends IsPivotedQR A Q R σ where
  /-- The rank does not exceed the number of rows. -/
  le_rows : r ≤ M
  /-- The rank does not exceed the number of columns. -/
  le_cols : r ≤ N
  /-- The rows of `R` from the `r`-th on vanish. -/
  apply_eq_zero : ∀ (i : Fin M) (j : Fin N), r ≤ (i : ℕ) → R i j = 0
  /-- The leading `r × r` block of `R` is invertible. -/
  isUnit_block : IsUnit (R.submatrix (Fin.castLE le_rows) (Fin.castLE le_cols))

/-- The inverse permutation matrix `Πᵀ` acts on a vector by `v ↦ v ∘ σ`. -/
theorem one_submatrix_mulVec (σ : Equiv.Perm (Fin N)) (v : Fin N → 𝕜) :
    (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix σ id *ᵥ v = v ∘ σ := by
  funext k
  simp [mulVec, dotProduct, one_apply]

/-- The inverse permutation matrix `Πᵀ` is invertible. -/
theorem isUnit_one_submatrix (σ : Equiv.Perm (Fin N)) :
    IsUnit ((1 : Matrix (Fin N) (Fin N) 𝕜).submatrix σ id) :=
  (isUnit_submatrix_equiv (A := (1 : Matrix (Fin N) (Fin N) 𝕜)) σ (Equiv.refl _)).2 isUnit_one

namespace IsPivotedQR.IsRankRevealing

variable {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
  {R : Matrix (Fin M) (Fin N) 𝕜} {σ : Equiv.Perm (Fin N)} {r : ℕ}

/-- A pivoted QR factorization `A Π = Q R` is `A = Q R Πᵀ`. -/
theorem eq_mul (h : IsRankRevealing A Q R σ r) :
    A = Q * R * (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix σ id := by
  rw [h.isQR.mul_eq, mul_submatrix_one, submatrix_submatrix]
  simp

/-- **The rank is revealed**: a rank-revealing pivoted QR factorization has `r = rank A`. The
rank is invariant under `Q` and `Π`, and `R` has a revealing block
(`Matrix.rank_eq_of_apply_eq_zero_of_isUnit`). -/
theorem rank_eq (h : IsRankRevealing A Q R σ r) : A.rank = r := by
  classical
  rw [h.eq_mul, rank_mul_eq_left_of_isUnit_det _ _
      ((isUnit_iff_isUnit_det _).1 (isUnit_one_submatrix σ)),
    rank_mul_eq_right_of_isUnit_det _ _
      ((isUnit_iff_isUnit_det Q).1 (isUnit_of_mem_unitaryGroup h.isQR.mem_unitaryGroup))]
  exact rank_eq_of_apply_eq_zero_of_isUnit h.le_rows h.le_cols h.apply_eq_zero h.isUnit_block

/-- **The range of `A` is spanned by the first `r` columns of `Q`** ([golub2013matrix] §5.4.2,
`ran(A) = span{q_1, …, q_r}`): `A x = Q R (Πᵀ x)` has zero coordinates from the `r`-th on, and
conversely `q_i = A Π [R₁₁⁻¹ e_i; 0]`. -/
theorem range_eq_span (h : IsRankRevealing A Q R σ r) :
    LinearMap.range (toEuclideanLin A) =
      Submodule.span 𝕜 (Set.range fun i : Fin r =>
        (WithLp.toLp 2 (Q.col (Fin.castLE h.le_rows i)) : EuclideanSpace 𝕜 (Fin M))) :=
  range_toEuclideanLin_eq_span_of_eq_mul h.le_rows h.le_cols h.eq_mul (isUnit_one_submatrix σ)
    h.apply_eq_zero h.isUnit_block

end IsPivotedQR.IsRankRevealing

/-- **Every matrix has a rank-revealing pivoted QR factorization** ([golub2013matrix] (5.4.6)):
`∃ σ Q R, IsPivotedQR.IsRankRevealing A Q R σ (rank A)`. Choose `r = rank A` linearly independent
columns, a permutation `σ` putting them first, and any QR factorization `A Π = Q R`. The first `r`
columns of `A Π` span its column space; the coordinates of index `≥ r` in `Qᴴ (·)` vanish on them
(`R` is upper triangular), hence on every column, so the rows of `R` from the `r`-th on vanish;
and `R₁₁ y = 0` gives `A Π [y; 0] = 0`, so `y = 0` by independence. -/
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

/-- **Column-norm downdating** ([golub2013matrix] §5.4.2): for `Q` unitary and `z`, the tail of
`Qᴴ z` has squared norm `‖z‖² − |(Qᴴ z)₀|²` — the identity behind Algorithm 5.4.1's updated
`c(i) = c(i) − A(r, i)²`. -/
theorem norm_sq_tail_eq_of_mem_unitaryGroup {s : ℕ} {Q : Matrix (Fin (s + 1)) (Fin (s + 1)) 𝕜}
    (hQ : Q ∈ unitaryGroup (Fin (s + 1)) 𝕜) (z : Fin (s + 1) → 𝕜) :
    ∑ i : Fin s, ‖(Qᴴ *ᵥ z) i.succ‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 - ‖(Qᴴ *ᵥ z) 0‖ ^ 2 := by
  have hQ' : Qᴴ ∈ unitaryGroup (Fin (s + 1)) 𝕜 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mem hQ
  rw [← sum_norm_sq_mulVec_of_mem_unitaryGroup hQ' z, Fin.sum_univ_succ]
  ring

/-- **Chan's theorem** ([golub2013matrix] Theorem 5.4.1, Chan 1987): for
`A : Matrix (Fin M) (Fin (N + 1)) 𝕜` with `N + 1 ≤ M` and a unit vector `v`, some column
permutation `σ` makes every QR factorization `A Π = Q R` satisfy
`|r_nn| ≤ √(N + 1) ‖A v‖₂` for the last diagonal entry. Move an entry of `v` of largest modulus
(`|v_p| ≥ 1/√(N + 1)`) to the last position; then `‖A v‖ = ‖R Πᵀ v‖ ≥ |r_nn| |v_p|`. -/
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

/-- **A URV decomposition** (Stewart 1993; [golub2013matrix] §5.4.5): `U`, `V` unitary and
`Uᴴ A V = R` upper triangular in the rectangular sense. The two-sided orthogonal factorization
whose trailing block reveals the small singular values; a pivoted QR factorization is one with
`V` the permutation matrix (`Matrix.IsPivotedQR.isURV`). -/
structure IsURV (A : Matrix (Fin M) (Fin N) 𝕜) (U : Matrix (Fin M) (Fin M) 𝕜)
    (R : Matrix (Fin M) (Fin N) 𝕜) (V : Matrix (Fin N) (Fin N) 𝕜) : Prop where
  /-- The left factor is unitary. -/
  mem_unitaryGroup_left : U ∈ unitaryGroup (Fin M) 𝕜
  /-- The right factor is unitary. -/
  mem_unitaryGroup_right : V ∈ unitaryGroup (Fin N) 𝕜
  /-- The factorization `Uᴴ A V = R`. -/
  star_mul_mul : star U * A * V = R
  /-- The middle factor is upper triangular. -/
  apply_eq_zero : ∀ (i : Fin M) (j : Fin N), (j : ℕ) < i → R i j = 0

/-- **A ULV decomposition** (Stewart 1993; [golub2013matrix] §5.4.5), the lower triangular twin
of `Matrix.IsURV`: `U`, `V` unitary and `Uᴴ A V = L` lower triangular in the rectangular sense. -/
structure IsULV (A : Matrix (Fin M) (Fin N) 𝕜) (U : Matrix (Fin M) (Fin M) 𝕜)
    (L : Matrix (Fin M) (Fin N) 𝕜) (V : Matrix (Fin N) (Fin N) 𝕜) : Prop where
  /-- The left factor is unitary. -/
  mem_unitaryGroup_left : U ∈ unitaryGroup (Fin M) 𝕜
  /-- The right factor is unitary. -/
  mem_unitaryGroup_right : V ∈ unitaryGroup (Fin N) 𝕜
  /-- The factorization `Uᴴ A V = L`. -/
  star_mul_mul : star U * A * V = L
  /-- The middle factor is lower triangular. -/
  apply_eq_zero : ∀ (i : Fin M) (j : Fin N), (i : ℕ) < j → L i j = 0

/-- The permutation matrix `Π` of a column permutation `σ`, the identity with its columns
permuted, is unitary. -/
theorem one_submatrix_mem_unitaryGroup (σ : Equiv.Perm (Fin N)) :
    (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix id σ ∈ unitaryGroup (Fin N) 𝕜 := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_submatrix, conjTranspose_one,
    show (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix id σ *
        (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix σ id =
      (1 * 1 : Matrix (Fin N) (Fin N) 𝕜).submatrix id id from
      submatrix_mul_equiv _ _ _ σ _, Matrix.one_mul, submatrix_id_id]

/-- **A pivoted QR factorization is a URV decomposition** with `V = Π`, the permutation matrix of
`σ` (`A Π = A.submatrix id σ`). -/
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

/-! ### Least squares from a rank-revealing factorization -/

section LeastSquares

variable {r : ℕ}

/-- **The basic solution** ([golub2013matrix] §5.5.5, `x_B = Π [R₁₁⁻¹ c; 0]`): with
`c = (Qᴴ b)₁:r` and `R₁₁` the leading `r × r` block of `R`, the vector whose permuted coordinates
are `R₁₁⁻¹ c` on the first `r` indices and `0` on the rest. -/
noncomputable def pivotedBasicSolution (Q : Matrix (Fin M) (Fin M) 𝕜)
    (R : Matrix (Fin M) (Fin N) 𝕜) (σ : Equiv.Perm (Fin N)) (hM : r ≤ M) (hN : r ≤ N)
    (b : EuclideanSpace 𝕜 (Fin M)) : EuclideanSpace 𝕜 (Fin N) :=
  WithLp.toLp 2 (blockVec hN ((R.submatrix (Fin.castLE hM) (Fin.castLE hN))⁻¹ *ᵥ
    fun i => (Qᴴ *ᵥ WithLp.ofLp b) (Fin.castLE hM i)) 0 ∘ σ.symm)

namespace IsPivotedQR.IsRankRevealing

variable {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
  {R : Matrix (Fin M) (Fin N) 𝕜} {σ : Equiv.Perm (Fin N)}

/-- The permuted coordinates of the basic solution. -/
private theorem basic_comp (h : IsRankRevealing A Q R σ r) (b : EuclideanSpace 𝕜 (Fin M)) :
    WithLp.ofLp (pivotedBasicSolution Q R σ h.le_rows h.le_cols b) ∘ σ =
      blockVec h.le_cols ((R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *ᵥ
        fun i => (Qᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i)) 0 := by
  funext k
  simp [pivotedBasicSolution]

/-- **The least-squares solutions of a rank-revealing factorization** ([golub2013matrix] §5.5.5):
`x` is a least-squares solution of `A x = b` exactly when the first `r` equations of
`R (Πᵀ x) = Qᴴ b` hold, `R₁₁ y + R₁₂ z = c` for `Πᵀ x = [y; z]` — equivalently
`Πᵀ x = [R₁₁⁻¹ (c − R₁₂ z); z]` for a free `z` (`R₁₁` is invertible). The residual is
`‖A x − b‖² = ‖R₁₁ y + R₁₂ z − c‖² + ‖d‖²` (`Qᴴ b = [c; d]`). -/
theorem isLeastSquaresSolution_iff (h : IsRankRevealing A Q R σ r)
    {b : EuclideanSpace 𝕜 (Fin M)} {x : EuclideanSpace 𝕜 (Fin N)} :
    IsLeastSquaresSolution A b x ↔ ∀ i : Fin r,
      (R *ᵥ (WithLp.ofLp x ∘ σ)) (Fin.castLE h.le_rows i) =
        (Qᴴ *ᵥ WithLp.ofLp b) (Fin.castLE h.le_rows i) := by
  rw [isLeastSquaresSolution_iff_of_eq_mul h.isQR.mem_unitaryGroup h.le_rows h.le_cols h.eq_mul
    (isUnit_one_submatrix σ) h.apply_eq_zero h.isUnit_block, one_submatrix_mulVec]

/-- **The basic solution is a least-squares solution** ([golub2013matrix] §5.5.5), and its
coordinates `Πᵀ x_B` vanish from the `r`-th on: it has at most `r` nonzero entries. -/
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

/-- A least-squares solution has `Πᵀ x = [R₁₁⁻¹ c − S z; z]` with `S = R₁₁⁻¹ R₁₂` and `z` the
trailing coordinates. -/
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

/-- **The minimal-norm solution as a minimum over the free parameter** ([golub2013matrix]
(5.5.4); the book writes `z ∈ ℝ^{n−2}` for `ℝ^{n−r}`): the solution set is
`x_B − Π [R₁₁⁻¹ R₁₂ z; −z]`, and `‖A⁺ b‖` is its least norm. -/
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

/-- The norm of a vector through its permuted head and tail coordinates. -/
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
/-- **Golub–Pereyra** ([golub2013matrix] (5.5.5)): the basic solution is at most a factor
`√(1 + ‖R₁₁⁻¹ R₁₂‖₂²)` longer than the minimal-norm solution,
`‖A⁺ b‖ ≤ ‖x_B‖ ≤ √(1 + ‖R₁₁⁻¹ R₁₂‖₂²) ‖A⁺ b‖`. With `S = R₁₁⁻¹ R₁₂` and `Πᵀ A⁺ b = [y; z]`,
`y = R₁₁⁻¹ c − S z` and `Πᵀ x_B = [R₁₁⁻¹ c; 0]`, so `‖x_B‖ = ‖y + S z‖ ≤ ‖y‖ + ‖S‖ ‖z‖`, and
Cauchy–Schwarz in `ℝ²` gives `≤ √(1 + ‖S‖²) √(‖y‖² + ‖z‖²)`. The lower bound is minimality. -/
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

/-- **Underdetermined systems of full row rank** ([golub2013matrix] §5.6.2, Algorithm 5.6.1): if
`IsPivotedQR.IsRankRevealing A Q R σ M` — no row of `R` vanishes and its leading `M × M` block
`R₁` is invertible, which is the case exactly when `A` has independent rows — then the basic
solution `x = Π [R₁⁻¹ Qᴴ b; 0]` solves `A x = b`. -/
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

end Matrix
