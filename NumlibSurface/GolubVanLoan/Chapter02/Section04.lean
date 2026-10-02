import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.Polar
import NumlibSurface.GolubVanLoan.Chapter02.Section01
import NumlibSurface.GolubVanLoan.Chapter02.Section03

/-!
# Golub–Van Loan §2.4: the singular value decomposition

Surface file for [golub2013matrix] §2.4: existence of the SVD (Theorem 2.4.1), the largest and
smallest singular values `σ_max`, `σ_min`, the corollaries 2.4.2–2.4.7 with (2.4.1)–(2.4.2), the
Eckart–Young theorem 2.4.8 with (2.4.3)–(2.4.4) and the two remarks after it (the distance to the
rank-deficient matrices, the Frobenius-norm version), the thin SVD (§2.4.3) and the complex SVD
(§2.4.4).

## Conventions

Matrices are `Matrix (Fin m) (Fin n) ℝ`, 0-based. The book's `σ_i(A)` (`1 ≤ i ≤ p = min{m, n}`) is
the backbone's sorted singular value `A.sortedSingularValues (i - 1)`, defined for every shape and
zero from the rank on. "An SVD `Uᵀ A V = Σ` of `A`" is the hypothesis `Matrix.IsSVD A U σ V`: `U`,
`V` orthogonal (the unitary group over `ℝ`, where `star` is the transpose),
`Uᵀ A V = Matrix.rectDiagonal σ` and `σ` antitone and nonnegative; its diagonal is the sorted
singular values below `p` (`Matrix.IsSVD.singularValues_eq`). The singular vectors `u_i`, `v_i` are
the columns `U.col i`, `V.col i`. The `2`-norm is `Matrix.lpOpNorm 2`, the Frobenius norm the scoped
`Matrix.Norms.Frobenius` norm; ranges and null spaces are those of `Matrix.toEuclideanLin`, as in
§2.1. The truncation `A_k` of (2.4.3) is the backbone's `Matrix.svdTruncation U σ V k`, built from
the factors because the SVD is not unique.

## Sources

Backbone `Numlib/LinearAlgebra/Matrix/SVD` (existence, `IsSVD`, kernel and range, `svdTruncation`,
the least singular value as least stretch), `Numlib/Analysis/Matrix/SingularValues` (Weyl's
inequality, column deletion, Eckart–Young in the `2`- and Frobenius norms) and
`Numlib/LinearAlgebra/Matrix/Polar` (the first columns of a unitary matrix, for the thin SVD). The
backbone's SVD comes from an eigenbasis of `AᵀA`, not from the book's induction through `‖A‖₂`; the
lower bound of Eckart–Young is Weyl's inequality, whose proof is the book's kernel-intersection
argument.

## Readings

`σ_min` of an `m × 0` matrix is not defined in the book (`p = 0`); the backbone's junk value `0`
would make the second half of Corollary 2.4.5 false for `n = 0`, so that corollary assumes `n ≥ 1`.
The remark after Theorem 2.4.8 on the rank-deficient matrices needs `m, n ≥ 1` (there are none
otherwise). The hyperellipsoid picture after Corollary 2.4.2 and the pointer to §8.6 are prose.
-/

open Matrix WithLp

namespace GolubVanLoan.Chapter02

variable {m n : ℕ}

/-! ### §2.4.1 Derivation -/

/-- **§2.4.1, `σ_max(A)`**: the largest singular value of `A`, `σ₁ = A.sortedSingularValues 0`. -/
noncomputable def sigmaMax (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  A.sortedSingularValues 0

/-- **§2.4.1, `σ_min(A)`**: the smallest of the `p = min{m, n}` singular values of `A`,
`σ_p = A.sortedSingularValues (p - 1)` (zero when `A` is rank deficient). -/
noncomputable def sigmaMin (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  A.sortedSingularValues (min m n - 1)

/-- `σ_max(A)` is the largest of the backbone's column-indexed singular values
`Matrix.colSingularValues` (both `0` when `n = 0`). -/
theorem sigmaMax_eq_iSup_colSingularValues (A : Matrix (Fin m) (Fin n) ℝ) :
    sigmaMax A = ⨆ i, A.colSingularValues i := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [Real.iSup_of_isEmpty, sigmaMax]
    exact sortedSingularValues_eq_zero_of_min_le A (by simp)
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact (sortedSingularValues_zero_eq_l2_opNorm A).trans (l2_opNorm_eq_iSup_colSingularValues A)

/-- For `n ≤ m`, `σ_min(A)` is the least of the backbone's column-indexed singular values
`Matrix.colSingularValues` (both `0` when `n = 0`). -/
theorem sigmaMin_eq_iInf_colSingularValues (A : Matrix (Fin m) (Fin n) ℝ) (hmn : n ≤ m) :
    sigmaMin A = ⨅ i, A.colSingularValues i := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [Real.iInf_of_isEmpty, sigmaMin]
    exact sortedSingularValues_eq_zero_of_min_le A (by simp)
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [sigmaMin, min_eq_right hmn, ← sortedSingularValues_eq_iInf_colSingularValues,
      Fintype.card_fin]

/-- **Theorem 2.4.1 (Singular Value Decomposition).** For `A ∈ ℝ^{m×n}` there are orthogonal
`U ∈ ℝ^{m×m}`, `V ∈ ℝ^{n×n}` with `Uᵀ A V = Σ = diag(σ₁, …, σ_p)`, `σ₁ ≥ ⋯ ≥ σ_p ≥ 0`: an SVD
whose diagonal is the sorted singular values (backbone `Matrix.exists_svd`). -/
theorem theorem_2_4_1 (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U V, IsSVD A U A.sortedSingularValues V := by
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  exact ⟨U, V, ⟨hU, hV, h⟩, A.sortedSingularValues_antitone, A.sortedSingularValues_nonneg⟩

/-! ### §2.4.2 Properties -/

/-- The columns of an SVD: `A v_j = σ_j u_j` for `j < m`. -/
private theorem mulVec_col_of_isSVD {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (j : Fin n)
    (hj : (j : ℕ) < m) : A *ᵥ V.col j = σ j • U.col ⟨j, hj⟩ := by
  have hVV : star V * V = 1 := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
  have hAV : A * V = U * (rectDiagonal fun i => σ i : Matrix (Fin m) (Fin n) ℝ) := by
    conv_lhs => rw [h.eq_mul_mul_star]
    rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
    simp only [RCLike.ofReal_real_eq_id, id]
  funext a
  change (A * V) a j = σ j * U a ⟨j, hj⟩
  rw [hAV, mul_rectDiagonal_apply]
  simp [hj, mul_comm]

/-- **Corollary 2.4.2.** If `Uᵀ A V = Σ` is the SVD of `A ∈ ℝ^{m×n}` and `m ≥ n`, then for
`i = 1:n`, `A v_i = σ_i u_i` and `Aᵀ u_i = σ_i v_i`. -/
theorem corollary_2_4_2 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (hmn : n ≤ m) (i : Fin n) :
    A *ᵥ V.col i = σ i • U.col (Fin.castLE hmn i) ∧
      Aᵀ *ᵥ U.col (Fin.castLE hmn i) = σ i • V.col i := by
  refine ⟨mulVec_col_of_isSVD h i (lt_of_lt_of_le i.isLt hmn), ?_⟩
  have h' := h.conjTranspose
  rw [conjTranspose_eq_transpose_of_trivial] at h'
  exact mulVec_col_of_isSVD h' (Fin.castLE hmn i) i.isLt

/-- **(2.4.1)**: `Aᵀ A v_i = σ_i² v_i` for `i = 1:n` (SVD of `A ∈ ℝ^{m×n}`, `m ≥ n`). -/
theorem equation_2_4_1 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (hmn : n ≤ m) (i : Fin n) :
    (Aᵀ * A) *ᵥ V.col i = σ i ^ 2 • V.col i := by
  obtain ⟨h1, h2⟩ := corollary_2_4_2 h hmn i
  rw [← mulVec_mulVec, h1, mulVec_smul, h2, smul_smul, sq]

/-- **(2.4.2)**: `A Aᵀ u_i = σ_i² u_i` for `i = 1:n` (SVD of `A ∈ ℝ^{m×n}`, `m ≥ n`). -/
theorem equation_2_4_2 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (hmn : n ≤ m) (i : Fin n) :
    (A * Aᵀ) *ᵥ U.col (Fin.castLE hmn i) = σ i ^ 2 • U.col (Fin.castLE hmn i) := by
  obtain ⟨h1, h2⟩ := corollary_2_4_2 h hmn i
  rw [← mulVec_mulVec, h2, mulVec_smul, h1, smul_smul, sq]

/-- `σ₁(A) = ‖A‖₂`. -/
private theorem sortedSingularValues_zero_eq_lpOpNorm (A : Matrix (Fin m) (Fin n) ℝ) :
    A.sortedSingularValues 0 = lpOpNorm 2 A :=
  (sortedSingularValues_zero_eq_l2_opNorm A).trans (lpOpNorm_two A).symm

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Corollary 2.4.3.** For `A ∈ ℝ^{m×n}`, `‖A‖₂ = σ₁` and `‖A‖_F = √(σ₁² + ⋯ + σ_p²)`,
`p = min{m, n}`. -/
theorem corollary_2_4_3 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 2 A = A.sortedSingularValues 0 ∧
      ‖A‖ = √(∑ i ∈ Finset.range (min m n), A.sortedSingularValues i ^ 2) := by
  refine ⟨(sortedSingularValues_zero_eq_lpOpNorm A).symm, ?_⟩
  rw [← Real.sqrt_sq (norm_nonneg A), frobenius_norm_sq_eq_sum_sq_sortedSingularValues,
    Fintype.card_fin]
  congr 1
  refine (Finset.sum_subset (Finset.range_mono (min_le_right m n)) fun i _ hi => ?_).symm
  rw [Finset.mem_range, not_lt] at hi
  rw [sortedSingularValues_eq_zero_of_min_le A (by simpa using hi), zero_pow two_ne_zero]

end Frobenius

/-- **Corollary 2.4.4.** For `A, E ∈ ℝ^{m×n}`, `σ_max(A + E) ≤ σ_max(A) + ‖E‖₂` and
`σ_min(A + E) ≥ σ_min(A) - ‖E‖₂`: two instances of Weyl's inequality
`σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)` (backbone `Matrix.sortedSingularValues_add_le`), which needs no
`m ≥ n`. -/
theorem corollary_2_4_4 (A E : Matrix (Fin m) (Fin n) ℝ) :
    sigmaMax (A + E) ≤ sigmaMax A + lpOpNorm 2 E ∧
      sigmaMin A - lpOpNorm 2 E ≤ sigmaMin (A + E) := by
  refine ⟨?_, ?_⟩
  · have h := sortedSingularValues_add_le A E 0 0
    rwa [sortedSingularValues_zero_eq_lpOpNorm E] at h
  · have h := sortedSingularValues_add_le (A + E) (-E) (min m n - 1) 0
    rw [add_zero, add_neg_cancel_right, sortedSingularValues_zero_eq_lpOpNorm,
      lpOpNorm_neg] at h
    rw [sigmaMin, sigmaMin]
    linarith

/-- **Corollary 2.4.5.** If `A ∈ ℝ^{m×n}`, `m > n` (and `n ≥ 1`, so that `σ_min(A)` exists), and
`z ∈ ℝ^m`, then `σ_max([A | z]) ≥ σ_max(A)` and `σ_min([A | z]) ≤ σ_min(A)`. The first is column
deletion (`Matrix.sortedSingularValues_submatrix_le`); for the second both matrices are tall, so
`σ_min` is the least stretch `min_{‖x‖₂ = 1} ‖A x‖₂` (`Matrix.iInf_colSingularValues_eq_iInf_norm`)
and `[A | z] [x; 0] = A x`. -/
theorem corollary_2_4_5 (A : Matrix (Fin m) (Fin n) ℝ) (hmn : n < m) (hn : 1 ≤ n)
    (z : Fin m → ℝ) :
    sigmaMax A ≤ sigmaMax (Matrix.of fun i => Fin.snoc (α := fun _ => ℝ) (A i) (z i) :
      Matrix (Fin m) (Fin (n + 1)) ℝ) ∧
    sigmaMin (Matrix.of fun i => Fin.snoc (α := fun _ => ℝ) (A i) (z i) :
      Matrix (Fin m) (Fin (n + 1)) ℝ) ≤ sigmaMin A := by
  set Ã : Matrix (Fin m) (Fin (n + 1)) ℝ :=
    Matrix.of fun i => Fin.snoc (α := fun _ => ℝ) (A i) (z i) with hÃ
  have hsub : Ã.submatrix id Fin.castSucc = A := by
    ext i j
    simp [hÃ]
  refine ⟨?_, ?_⟩
  · calc sigmaMax A = (Ã.submatrix id Fin.castSucc).sortedSingularValues 0 := by rw [hsub]; rfl
      _ ≤ Ã.sortedSingularValues 0 := sortedSingularValues_submatrix_le Ã Function.injective_id
        (Fin.castSucc_injective _) 0
  · have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨x, hx1, hx⟩ := A.exists_norm_eq_iInf_colSingularValues
    have hmin1 : min m n - 1 = Fintype.card (Fin n) - 1 := by
      rw [Fintype.card_fin, min_eq_right hmn.le]
    have hmin2 : min m (n + 1) - 1 = Fintype.card (Fin (n + 1)) - 1 := by
      rw [Fintype.card_fin, min_eq_right hmn]
    rw [sigmaMin, sigmaMin, hmin1, hmin2, sortedSingularValues_eq_iInf_colSingularValues,
      sortedSingularValues_eq_iInf_colSingularValues, iInf_colSingularValues_eq_iInf_norm, ← hx]
    set y : EuclideanSpace ℝ (Fin (n + 1)) :=
      toLp 2 (Function.extend Fin.castSucc (ofLp x) 0) with hy
    have hy1 : ‖y‖ = 1 := by
      rw [← hx1, hy, PiLp.norm_toLp_extend 2 (Fin.castSucc_injective n), toLp_ofLp]
    have hAy : toEuclideanLin Ã y = toEuclideanLin A x := by
      have h := submatrix_mulVec_eq_comp_mulVec_extend Ã id (Fin.castSucc_injective n) (ofLp x)
      rw [hsub, Function.comp_id] at h
      rw [hy, toEuclideanLin_toLp, toEuclideanLin_apply, h]
    have hbdd : BddBelow (Set.range fun v : {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} =>
        ‖toEuclideanLin Ã v‖) := ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩
    calc (⨅ v : {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1}, ‖toEuclideanLin Ã v‖)
        ≤ ‖toEuclideanLin Ã y‖ := ciInf_le hbdd ⟨y, hy1⟩
      _ = ‖toEuclideanLin A x‖ := by rw [hAy]

/-- Membership in a span of vectors transported to `EuclideanSpace`. -/
private theorem mem_span_toLp_image_iff {k : ℕ} (s : Set (Fin k → ℝ))
    (x : EuclideanSpace ℝ (Fin k)) :
    x ∈ Submodule.span ℝ (toLp 2 '' s) ↔ ofLp x ∈ Submodule.span ℝ s := by
  have h : (toLp 2 '' s : Set (EuclideanSpace ℝ (Fin k))) =
      (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm '' s := rfl
  rw [h, Submodule.span_image_linearEquiv, Submodule.mem_map_equiv]
  rfl

/-- **Corollary 2.4.6.** If the SVD `Uᵀ A V = Σ` has exactly `r` positive singular values
(`σ_i > 0 ↔ i < r` for `i < p`, 0-based), then `rank(A) = r`,
`null(A) = span{v_{r+1}, …, v_n}` and `ran(A) = span{u₁, …, u_r}` (0-based: the columns `j ≥ r`
of `V`, `i < r` of `U`). Backbone `Matrix.IsSVD.ker_mulVecLin_eq_span`,
`Matrix.IsSVD.range_mulVecLin_eq_span` and `Matrix.sortedSingularValues_eq_zero_iff_rank_le`. -/
theorem corollary_2_4_6 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {r : ℕ} (hr : r ≤ min m n)
    (hσ : ∀ i < min m n, 0 < σ i ↔ i < r) :
    A.rank = r ∧
      LinearMap.ker (toEuclideanLin A) =
        Submodule.span ℝ ((fun j => toLp 2 (V.col j)) '' {j : Fin n | r ≤ (j : ℕ)}) ∧
      LinearMap.range (toEuclideanLin A) =
        Submodule.span ℝ ((fun i => toLp 2 (U.col i)) '' {i : Fin m | (i : ℕ) < r}) := by
  have hs : ∀ i < min m n, σ i = A.sortedSingularValues i := fun i hi =>
    h.singularValues_eq (lt_of_lt_of_le hi (min_le_left _ _))
      (lt_of_lt_of_le hi (min_le_right _ _))
  refine ⟨le_antisymm ?_ ?_, ?_, ?_⟩
  · rcases lt_or_eq_of_le hr with hlt | heq
    · have h0 : σ r = 0 :=
        le_antisymm (not_lt.1 fun hpos => lt_irrefl r ((hσ r hlt).1 hpos)) (h.nonneg r)
      rwa [hs r hlt, sortedSingularValues_eq_zero_iff_rank_le] at h0
    · rw [heq]
      exact le_min A.rank_le_height A.rank_le_width
  · by_contra hlt
    push Not at hlt
    have hr1 : r - 1 < min m n := by omega
    have hpos := (hσ (r - 1) hr1).2 (by omega)
    rw [hs _ hr1, (sortedSingularValues_eq_zero_iff_rank_le A (r - 1)).2 (by omega)] at hpos
    exact lt_irrefl 0 hpos
  · have hset : {j : Fin n | m ≤ (j : ℕ) ∨ σ j = 0} = {j : Fin n | r ≤ (j : ℕ)} := by
      ext j
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro (hj | hj)
        · exact le_trans (le_trans hr (min_le_left _ _)) hj
        · by_contra hjr
          push Not at hjr
          have hjp : (j : ℕ) < min m n := lt_of_lt_of_le hjr hr
          exact lt_irrefl 0 (hj ▸ (hσ j hjp).2 hjr)
      · intro hj
        by_cases hjm : m ≤ (j : ℕ)
        · exact Or.inl hjm
        · refine Or.inr (le_antisymm (not_lt.1 fun hpos => ?_) (h.nonneg j))
          have := (hσ j (lt_min (not_le.1 hjm) j.isLt)).1 hpos
          omega
    ext x
    rw [← Set.image_image (toLp 2) (fun j => V.col j), mem_span_toLp_image_iff, ← hset,
      show (fun j => V.col j) = Vᵀ from rfl, ← h.ker_mulVecLin_eq_span, LinearMap.mem_ker,
      LinearMap.mem_ker, mulVecLin_apply, toEuclideanLin_apply, WithLp.toLp_eq_zero]
  · have hset : {i : Fin m | (i : ℕ) < n ∧ σ i ≠ 0} = {i : Fin m | (i : ℕ) < r} := by
      ext i
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hin, hi⟩
        exact (hσ i (lt_min i.isLt hin)).1 (lt_of_le_of_ne (h.nonneg i) (Ne.symm hi))
      · intro hi
        have hip : (i : ℕ) < min m n := lt_of_lt_of_le hi hr
        exact ⟨lt_of_lt_of_le hip (min_le_right _ _), ((hσ i hip).2 hi).ne'⟩
    ext x
    rw [← Set.image_image (toLp 2) (fun i => U.col i), mem_span_toLp_image_iff, ← hset,
      show (fun i => U.col i) = Uᵀ from rfl, ← h.range_mulVecLin_eq_span]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨ofLp y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨toLp 2 y, by rw [toEuclideanLin_toLp]; exact congrArg (toLp 2) hy⟩

/-- The truncation (2.4.3) as a sum of rank-one matrices: `U Σ_k Vᵀ = ∑_{i<k} σ_i u_i v_iᵀ`. -/
private theorem svdTruncation_eq_sum (U : Matrix (Fin m) (Fin m) ℝ) (σ : ℕ → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    svdTruncation U σ V k =
      ∑ i : Fin k, σ i • vecMulVec (U.col (Fin.castLE hkm i)) (V.col (Fin.castLE hkn i)) := by
  ext a b
  simp only [svdTruncation, RCLike.ofReal_real_eq_id, id]
  rw [mul_apply, Matrix.sum_apply]
  have hg : ∀ j : Fin n,
      (U * (rectDiagonal (fun i => if i < k then σ i else 0) :
        Matrix (Fin m) (Fin n) ℝ)) a j * star V j b =
        if (j : ℕ) < k then (if h : (j : ℕ) < m then U a ⟨j, h⟩ * σ j else 0) * V b j
        else 0 := by
    intro j
    rw [mul_rectDiagonal_apply]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => hg j, ← Fin.sum_castLE_eq_sum_ite hkn]
  refine Finset.sum_congr rfl fun i _ => ?_
  have him : (i : ℕ) < m := lt_of_lt_of_le i.isLt hkm
  simp only [Fin.val_castLE, him, ↓reduceDIte, Matrix.smul_apply, vecMulVec_apply, col_apply,
    smul_eq_mul]
  rw [show (⟨i, him⟩ : Fin m) = Fin.castLE hkm i from rfl]
  ring

open scoped Matrix.Norms.L2Operator in
/-- **Corollary 2.4.7.** If `A ∈ ℝ^{m×n}` has rank `r`, then `A = ∑_{i=1}^r σ_i u_i v_iᵀ` for
any SVD of `A`. The truncation at the rank has residual norm `σ_{r+1} = 0`
(`Matrix.l2_opNorm_sub_svdTruncation`). -/
theorem corollary_2_4_7 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) :
    A = ∑ i : Fin A.rank, σ i • vecMulVec (U.col (Fin.castLE A.rank_le_height i))
      (V.col (Fin.castLE A.rank_le_width i)) := by
  rw [← svdTruncation_eq_sum]
  have h0 := l2_opNorm_sub_svdTruncation h A.rank
  rw [(sortedSingularValues_eq_zero_iff_rank_le A A.rank).2 le_rfl, norm_eq_zero,
    sub_eq_zero] at h0
  exact h0

/-- **Theorem 2.4.8 (Eckart–Young), (2.4.3)–(2.4.4).** If `k < r = rank(A)` and
`A_k = ∑_{i=1}^k σ_i u_i v_iᵀ` (2.4.3), then `rank(A_k) = k` and
`min_{rank(B) = k} ‖A - B‖₂ = ‖A - A_k‖₂ = σ_{k+1}` (2.4.4) (0-based `σ k`). Backbone
`Matrix.rank_svdTruncation`, `Matrix.l2_opNorm_sub_svdTruncation` and the lower bound
`Matrix.sortedSingularValues_le_l2_opNorm_sub_of_rank_le`. -/
theorem theorem_2_4_8 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {k : ℕ} (hk : k < A.rank) :
    svdTruncation U σ V k =
        ∑ i : Fin k, σ i • vecMulVec (U.col (Fin.castLE (hk.le.trans A.rank_le_height) i))
          (V.col (Fin.castLE (hk.le.trans A.rank_le_width) i)) ∧
      (svdTruncation U σ V k).rank = k ∧
      lpOpNorm 2 (A - svdTruncation U σ V k) = σ k ∧
      IsLeast ((fun B => lpOpNorm 2 (A - B)) '' {B | B.rank = k}) (σ k) := by
  have hσk : σ k = A.sortedSingularValues k :=
    h.singularValues_eq (lt_of_lt_of_le hk A.rank_le_height)
      (lt_of_lt_of_le hk A.rank_le_width)
  have hnorm : lpOpNorm 2 (A - svdTruncation U σ V k) = σ k := by
    rw [lpOpNorm_two, l2_opNorm_sub_svdTruncation h k, hσk]
  have hrank := rank_svdTruncation h hk.le
  refine ⟨svdTruncation_eq_sum U σ V _ _, hrank, hnorm, ⟨⟨_, hrank, hnorm⟩, ?_⟩⟩
  rintro _ ⟨B, hB, rfl⟩
  rw [hσk]
  dsimp only
  rw [lpOpNorm_two]
  exact sortedSingularValues_le_l2_opNorm_sub_of_rank_le (le_of_eq hB)

/-- **§2.4.2, after Theorem 2.4.8**: "the smallest singular value of `A` is the 2-norm distance of
`A` to the set of all rank-deficient matrices" (`m, n ≥ 1`): Eckart–Young at `k = p - 1`
(`Matrix.isLeast_l2_opNorm_sub_of_rank_le`). -/
theorem sigmaMin_eq_dist_rankDeficient (A : Matrix (Fin m) (Fin n) ℝ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    IsLeast ((fun B => lpOpNorm 2 (A - B)) '' {B | IsRankDeficient B}) (sigmaMin A) := by
  have hset : {B : Matrix (Fin m) (Fin n) ℝ | IsRankDeficient B} =
      {B | B.rank ≤ min m n - 1} := by
    ext B
    change B.rank < min m n ↔ B.rank ≤ min m n - 1
    have : 1 ≤ min m n := le_min hm hn
    omega
  have hfun : (fun B : Matrix (Fin m) (Fin n) ℝ => lpOpNorm 2 (A - B)) =
      fun B => lpOpNorm 2 (A - B) := rfl
  rw [hset, hfun]
  have h := isLeast_l2_opNorm_sub_of_rank_le A (min m n - 1)
  simp only [← lpOpNorm_two] at h
  exact h

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **§2.4.2, after Theorem 2.4.8**: the matrix `A_k` of (2.4.3) is the closest rank-`k` matrix to
`A` in the Frobenius norm (`k < rank(A)`), at distance `√(σ_{k+1}² + ⋯ + σ_p²)` (stated without
proof in the book; Mirsky). Backbone `Matrix.isLeast_frobenius_norm_sub_of_rank_le` and
`Matrix.frobenius_norm_sub_svdTruncation`. -/
theorem svdTruncation_isLeast_frobenius {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V)
    {k : ℕ} (hk : k < A.rank) :
    IsLeast ((fun B => ‖A - B‖) '' {B | B.rank = k}) ‖A - svdTruncation U σ V k‖ ∧
      ‖A - svdTruncation U σ V k‖ = √(∑ i ∈ Finset.Ico k (min m n), σ i ^ 2) := by
  have hval : ‖A - svdTruncation U σ V k‖ = √(∑ i ∈ Finset.Ico k (min m n), σ i ^ 2) := by
    rw [frobenius_norm_sub_svdTruncation h k]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := (Finset.mem_Ico.1 hi).2
    rw [h.singularValues_eq (lt_of_lt_of_le hi' (min_le_left _ _))
      (lt_of_lt_of_le hi' (min_le_right _ _))]
  refine ⟨⟨⟨_, rank_svdTruncation h hk.le, rfl⟩, ?_⟩, hval⟩
  rintro _ ⟨B, hB, rfl⟩
  have hlb := (isLeast_frobenius_norm_sub_of_rank_le A k).2 ⟨B, le_of_eq hB, rfl⟩
  rw [frobenius_norm_sub_svdTruncation h k]
  simpa only [Fintype.card_fin] using hlb

end Frobenius

/-! ### §2.4.3 The thin SVD -/

/-- **§2.4.3, the thin SVD.** If `A = U Σ Vᵀ` is the SVD of `A ∈ ℝ^{m×n}` and `m ≥ n`, then
`A = U₁ Σ₁ Vᵀ` with `U₁ = U(:, 1:n)` (orthonormal columns) and `Σ₁ = Σ(1:n, 1:n) =
diag(σ₁, …, σ_n)`. -/
theorem thin_svd {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (hmn : n ≤ m) :
    (U.submatrix id (Fin.castLE hmn))ᵀ * U.submatrix id (Fin.castLE hmn) = 1 ∧
      A = U.submatrix id (Fin.castLE hmn) * diagonal (fun i : Fin n => σ i) * Vᵀ := by
  refine ⟨?_, ?_⟩
  · have h1 := conjTranspose_submatrix_castLE_mul_self hmn h.mem_unitaryGroup_left
    rwa [conjTranspose_eq_transpose_of_trivial] at h1
  · conv_lhs => rw [h.eq_mul_mul_star, mul_rectDiagonal_eq_submatrix_mul_diagonal hmn]
    simp [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-! ### §2.4.4 Unitary matrices and the complex SVD -/

section Complex

open scoped Matrix.Norms.Frobenius

/-- **§2.4.4, the complex SVD.** For `A ∈ ℂ^{m×n}` there are unitary `U`, `V` with
`Uᴴ A V = diag(σ₁, …, σ_p) ∈ ℝ^{m×n}`, `σ₁ ≥ ⋯ ≥ σ_p ≥ 0`; and unitary transformations preserve
both the 2-norm and the Frobenius norm. (The book's "all of the real SVD properties have obvious
complex analogs" is the `RCLike` generality of the backbone.) -/
theorem complex_svd (A : Matrix (Fin m) (Fin n) ℂ) :
    (∃ U V, IsSVD A U A.sortedSingularValues V) ∧
      ∀ {Q : Matrix (Fin m) (Fin m) ℂ} {Z : Matrix (Fin n) (Fin n) ℂ},
        Q ∈ unitaryGroup (Fin m) ℂ → Z ∈ unitaryGroup (Fin n) ℂ →
          lpOpNorm 2 (Q * A * Z) = lpOpNorm 2 A ∧ ‖Q * A * Z‖ = ‖A‖ := by
  refine ⟨?_, fun hQ hZ => ⟨?_, frobenius_norm_unitary_mul_mul_unitary hQ A hZ⟩⟩
  · obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
    exact ⟨U, V, ⟨hU, hV, h⟩, A.sortedSingularValues_antitone, A.sortedSingularValues_nonneg⟩
  · rw [lpOpNorm_two, lpOpNorm_two]
    exact l2_opNorm_unitary_mul_mul_unitary hQ A hZ

end Complex

end GolubVanLoan.Chapter02
