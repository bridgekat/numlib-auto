/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.RankRevealing`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Matrix.SingularValues
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
* `Matrix.gap_le_of_urv`, `Matrix.gap_le_of_ulv` ([golub2013matrix] (5.4.10), (5.4.11), Stewart
  1993): how close the trailing columns of `V` in a URV or ULV decomposition come to the trailing
  right singular subspace.
* `Matrix.norm_residual_subset_sub_le` ([golub2013matrix] Theorem 5.5.3): the residual of SVD-based
  subset selection against that of the nearest rank-`r` problem.

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

omit [RCLike 𝕜] in
/-- The trailing indices are distinct. -/
theorem tailIdx_injective (h : r ≤ N) : Function.Injective (tailIdx h) := fun a b e =>
  Fin.ext (by have := congrArg Fin.val e; simp only [val_tailIdx] at this; omega)

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

/-! ### Stewart's bounds for the URV and ULV decompositions -/

section Stewart

open scoped Matrix.Norms.L2Operator

variable {r : ℕ}

omit [RCLike 𝕜] in
/-- The leading and trailing indices together: `Fin r ⊕ Fin (N − r) ≃ Fin N`. -/
private def blockEquiv (h : r ≤ N) : Fin r ⊕ Fin (N - r) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))

omit [RCLike 𝕜] in
private theorem blockEquiv_inl (h : r ≤ N) (i : Fin r) :
    blockEquiv h (Sum.inl i) = Fin.castLE h i := Fin.ext rfl

omit [RCLike 𝕜] in
private theorem blockEquiv_inr (h : r ≤ N) (j : Fin (N - r)) :
    blockEquiv h (Sum.inr j) = tailIdx h j := Fin.ext rfl

/-- The column blocks of a unitary matrix: `(V_f)ᴴ V_g` is the `(f, g)` block of the identity. -/
private theorem conjTranspose_submatrix_mul_submatrix {V : Matrix (Fin N) (Fin N) 𝕜}
    (hV : V ∈ unitaryGroup (Fin N) 𝕜) {p q : Type*} (f : p → Fin N) (g : q → Fin N) :
    (V.submatrix id f)ᴴ * V.submatrix id g = (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix f g := by
  rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hV]

/-- The leading `r` columns of a unitary matrix span the orthogonal complement of the span of the
trailing ones. -/
private theorem range_submatrix_castLE_eq_orthogonal {V : Matrix (Fin N) (Fin N) 𝕜}
    (hV : V ∈ unitaryGroup (Fin N) 𝕜) (h : r ≤ N) :
    LinearMap.range (toEuclideanLin (V.submatrix id (Fin.castLE h))) =
      (LinearMap.range (toEuclideanLin (V.submatrix id (tailIdx h))))ᗮ := by
  have hcross : (V.submatrix id (tailIdx h))ᴴ * V.submatrix id (Fin.castLE h) = 0 := by
    rw [conjTranspose_submatrix_mul_submatrix hV]
    ext i j
    rw [submatrix_apply, zero_apply, one_apply_ne]
    intro e
    have := congrArg Fin.val e
    simp only [val_tailIdx, Fin.val_castLE] at this
    omega
  have h1 : (V.submatrix id (Fin.castLE h))ᴴ * V.submatrix id (Fin.castLE h) = 1 := by
    rw [conjTranspose_submatrix_mul_submatrix hV, submatrix_one _ (Fin.castLE_injective h)]
  have h2 : (V.submatrix id (tailIdx h))ᴴ * V.submatrix id (tailIdx h) = 1 := by
    rw [conjTranspose_submatrix_mul_submatrix hV, submatrix_one _ (tailIdx_injective h)]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨y, rfl⟩
    rw [← toEuclideanLin_conjTranspose_inner_right, ← toEuclideanLin_mul_apply, hcross, map_zero,
      LinearMap.zero_apply, inner_zero_right]
  · have hsum := Submodule.finrank_add_finrank_orthogonal
      (LinearMap.range (toEuclideanLin (V.submatrix id (tailIdx h))))
    rw [LinearMap.finrank_range_of_inj (f := toEuclideanLin (V.submatrix id (tailIdx h)))
        (toEuclideanLinearIsometry h2).injective,
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at hsum
    rw [LinearMap.finrank_range_of_inj (f := toEuclideanLin (V.submatrix id (Fin.castLE h)))
        (toEuclideanLinearIsometry h1).injective,
      finrank_euclideanSpace_fin]
    omega

/-- **The gap between trailing column spans** ([golub2013matrix] Theorem 2.5.1): for unitary `V`,
`Z`, the gap between the spans of their last `N − r` columns is the `2`-norm of the block of
`Vᴴ Z` in the leading `r` rows and the trailing `N − r` columns. -/
private theorem gap_range_tailIdx_eq {V Z : Matrix (Fin N) (Fin N) 𝕜}
    (hV : V ∈ unitaryGroup (Fin N) 𝕜) (hZ : Z ∈ unitaryGroup (Fin N) 𝕜) (h : r ≤ N) :
    (LinearMap.range (toEuclideanLin (V.submatrix id (tailIdx h)))).gap
        (LinearMap.range (toEuclideanLin (Z.submatrix id (tailIdx h)))) =
      ‖(star V * Z).submatrix (Fin.castLE h) (tailIdx h)‖ := by
  rw [Submodule.gap_comm, gap_range_eq_l2_opNorm_conjTranspose_mul
    (by rw [conjTranspose_submatrix_mul_submatrix hZ, submatrix_one _ (tailIdx_injective h)])
    (by rw [conjTranspose_submatrix_mul_submatrix hV, submatrix_one _ (tailIdx_injective h)])
    (by rw [conjTranspose_submatrix_mul_submatrix hV, submatrix_one _ (Fin.castLE_injective h)])
    (range_submatrix_castLE_eq_orthogonal hV h),
    ← l2_opNorm_conjTranspose ((Z.submatrix id (tailIdx h))ᴴ * V.submatrix id (Fin.castLE h)),
    conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_submatrix,
    ← submatrix_mul _ _ _ id _ Function.bijective_id, star_eq_conjTranspose]

/-- **Stewart's setting** ([golub2013matrix] §5.4.6): for `T = Uᴴ A V` with `U`, `V` unitary and
an SVD `A = W Σ Zᴴ`, let `Y` be the last `N − r` columns of `Vᴴ Z` (the trailing right singular
vectors of `T`). Then `Tᴴ T Y = Y D` for a diagonal `D` of the squared trailing singular values,
all at most `σ_r(T)²`; `Y` is an isometry; `‖T Y w‖ ≤ σ_r(T) ‖w‖`; and the gap between the trailing
column spans of `V` and `Z` is the norm of the leading `r` rows of `Y`. -/
private theorem stewart_setting {A T : Matrix (Fin M) (Fin N) 𝕜} {U W : Matrix (Fin M) (Fin M) 𝕜}
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
    refine ⟨hP, hG, hA.antitone, hA.nonneg, ?_⟩
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
    rw [conjTranspose_submatrix_mul_submatrix hG, submatrix_one _ (tailIdx_injective h)]
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

/-- The least singular value bounds the stretch from below: `σ_{r-1}(B) ‖x‖ ≤ ‖B x‖` for a
matrix with `r ≥ 1` columns. -/
private theorem sortedSingularValues_mul_norm_le {p : Type*} [Fintype p] (B : Matrix p (Fin r) 𝕜)
    (hr : 0 < r) (x : EuclideanSpace 𝕜 (Fin r)) :
    B.sortedSingularValues (r - 1) * ‖x‖ ≤ ‖toEuclideanLin B x‖ := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have := B.iInf_singularValues_mul_norm_le x
  rwa [← sortedSingularValues_eq_iInf_singularValues, Fintype.card_fin] at this

/-- The rows above the `r`-th of `T v`: `(T v)₁ = T₁₁ v₁ + T₁₂ v₂`. -/
private theorem mulVec_castLE (T : Matrix (Fin M) (Fin N) 𝕜) (hM : r ≤ M) (hN : r ≤ N)
    (v : Fin N → 𝕜) (i : Fin r) :
    (T *ᵥ v) (Fin.castLE hM i) =
      (T.submatrix (Fin.castLE hM) (Fin.castLE hN) *ᵥ fun l => v (Fin.castLE hN l)) i +
        (T.submatrix (Fin.castLE hM) (tailIdx hN) *ᵥ fun l => v (tailIdx hN l)) i := by
  rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx hN]
  rfl

/-- The rows above the `r`-th of `Tᴴ u`: `(Tᴴ u)₁ = T₁₁ᴴ u₁ + T₂₁ᴴ u₂`. -/
private theorem conjTranspose_mulVec_castLE (T : Matrix (Fin M) (Fin N) 𝕜) (hM : r ≤ M)
    (hN : r ≤ N) (u : Fin M → 𝕜) (i : Fin r) :
    (Tᴴ *ᵥ u) (Fin.castLE hN i) =
      ((T.submatrix (Fin.castLE hM) (Fin.castLE hN))ᴴ *ᵥ fun l => u (Fin.castLE hM l)) i +
        ((T.submatrix (tailIdx hM) (Fin.castLE hN))ᴴ *ᵥ fun l => u (tailIdx hM l)) i := by
  rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx hM]
  rfl

/-- From `s² y ≤ (s a + t² Y) w` to `y ≤ (a / s + (t / s)² Y) w`. -/
private theorem le_mul_of_sq_mul_le {y w a t Y s : ℝ} (hs : 0 < s)
    (h : s ^ 2 * y ≤ (s * a + t ^ 2 * Y) * w) : y ≤ (a / s + (t / s) ^ 2 * Y) * w := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hs' : s ≠ 0 := hs.ne'
  have e : (a / s + (t / s) ^ 2 * Y) * w * s ^ 2 = (s * a + t ^ 2 * Y) * w := by
    field_simp
  exact le_of_mul_le_mul_right (by rw [e]; linarith) hs2

/-- From `x ≤ a / s + ρ² x` with `0 ≤ ρ < 1` to `x ≤ a / ((1 − ρ²) s)`. -/
private theorem le_div_of_le_add_sq_mul {x a s ρ : ℝ} (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : x ≤ a / s + ρ ^ 2 * x) : x ≤ a / ((1 - ρ ^ 2) * s) := by
  have h1 : 0 < 1 - ρ ^ 2 := by nlinarith
  rw [le_div_iff₀ (mul_pos h1 hs)]
  have := mul_le_mul_of_nonneg_left h hs.le
  rw [mul_add, mul_div_cancel₀ _ hs.ne'] at this
  nlinarith

/-- **Stewart's bound for a URV decomposition** ([golub2013matrix] (5.4.10), Stewart 1993): let
`Uᴴ A V = R = [R₁₁ R₁₂; 0 R₂₂]` be a URV decomposition split at `k` (`R₁₁` of size `k × k`),
`Uᴴ … Z` any SVD of `A` (`hA`), `S` the span of the last `n − k` right singular vectors and `V₂` the
last `n − k` columns of `V`. If `‖R₂₂‖₂ < σ_min(R₁₁)` (`σ_min(R₁₁) = R₁₁.sortedSingularValues
(k − 1)`), then with `ρ = ‖R₂₂‖₂ / σ_min(R₁₁)`,
`gap(ran V₂, S) ≤ ‖R₁₂‖₂ / ((1 − ρ²) σ_min(R₁₁))`. In the coordinates of `R`, with `Y = [Y₁; Y₂]`
the trailing right singular vectors of `R`, the gap is `‖Y₁‖₂`, and the first block row of
`Rᴴ R Y = Y Σ₂²` is `R₁₁ᴴ (R₁₁ Y₁ + R₁₂ Y₂) = Y₁ Σ₂²`; with `σ_k(R) ≤ ‖R₂₂‖₂`
(`Matrix.sortedSingularValues_le_l2_opNorm_trailing`) this gives
`σ_min (σ_min ‖Y₁‖ − ‖R₁₂‖) ≤ ‖R₂₂‖² ‖Y₁‖`. -/
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
      · rw [submatrix_apply, blockEquiv_inr, blockEquiv_inl, fromBlocks_apply₂₁, zero_apply]
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

/-- **Stewart's bound for a ULV decomposition** ([golub2013matrix] (5.4.11), Stewart 1993, with the
book's `L₁₂` read as `L₂₁`, the only nonzero off-diagonal block of the lower triangular `L`): let
`Uᴴ A V = L = [L₁₁ 0; L₂₁ L₂₂]` be a ULV decomposition split at `k`, and `S`, `V₂` as in
`Matrix.gap_le_of_urv`. If `‖L₂₂‖₂ < σ_min(L₁₁)`, then with `ρ = ‖L₂₂‖₂ / σ_min(L₁₁)`,
`gap(ran V₂, S) ≤ ρ ‖L₂₁‖₂ / ((1 − ρ²) σ_min(L₁₁))`. With `Y = [Y₁; Y₂]` the trailing right
singular vectors of `L`, the first block row of `Lᴴ L Y = Y Σ₂²` is
`L₁₁ᴴ L₁₁ Y₁ + L₂₁ᴴ (L Y)₂ = Y₁ Σ₂²`, and `‖L Y‖₂ ≤ σ_k(L) ≤ ‖L₂₂‖₂`
(`Matrix.sortedSingularValues_le_l2_opNorm_trailing_lower`), so
`σ_min² ‖Y₁‖ ≤ ‖L₂₂‖² ‖Y₁‖ + ‖L₂₂‖ ‖L₂₁‖`. -/
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
      · rw [submatrix_apply, blockEquiv_inl, blockEquiv_inr, fromBlocks_apply₁₂, zero_apply]
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

/-! ### Subset selection -/

section SubsetSelection

open scoped Matrix.Norms.L2Operator

variable {A : Matrix (Fin M) (Fin N) 𝕜} {U : Matrix (Fin M) (Fin M) 𝕜} {σ : ℕ → ℝ}
  {V : Matrix (Fin N) (Fin N) 𝕜} {r : ℕ}

/-- **The truncated SVD through the leading left singular vectors**: `U₁ U₁ᴴ A = A_r` for an SVD
`A = U Σ Vᴴ` and `U₁` the first `r` columns of `U`. -/
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
    rw [mul_diagonal, mul_apply]
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

/-- **[golub2013matrix] Theorem 5.5.3** (subset selection against the nearest rank-`r` problem): in
the setting of `Matrix.IsSVD.sortedSingularValues_le_mul_submatrix` (`IsSVD A U σ V`, a column
permutation `π`, `B₁` the first `r` columns of `A Π`, `Ṽ₁₁` the leading `r × r` block of `Πᵀ V`,
assumed invertible) and with `r ≤ rank A`, the residuals `r_x = (1 − U₁ U₁ᴴ) b` of the nearest
rank-`r` problem (`U₁` the first `r` columns of `U`) and `r_y = (1 − B₁ B₁⁺) b` of the subset
satisfy `‖r_x − r_y‖₂ ≤ (σ_r(A) / σ_{r-1}(A)) ‖Ṽ₁₁⁻¹‖₂ ‖b‖₂` (0-based: the book's
`σ_{r̃+1}/σ_{r̃}`). The difference is `(P_{B₁} − P_{U₁}) b`, at most the gap between the two
`r`-dimensional ranges, which is `‖P_{U₁⊥} P_{B₁}‖₂`; on the range of `B₁`,
`P_{U₁⊥} B₁ z = (A − A_r) Π [z; 0]` has norm at most `σ_r(A) ‖z‖`, and
`σ_{r-1}(B₁) ‖z‖ ≤ ‖B₁ z‖` with `σ_{r-1}(A) ≤ ‖Ṽ₁₁⁻¹‖₂ σ_{r-1}(B₁)` (Theorem 5.5.2). The rank
hypothesis, implicit in the book, is needed: for `A = 0` the left side need not vanish. -/
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
    rw [conjTranspose_submatrix_mul_submatrix h.mem_unitaryGroup_left,
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
    refine (sortedSingularValues_submatrix_le _ _ 0).trans ?_
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
