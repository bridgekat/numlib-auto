import Numlib.Analysis.InnerProductSpace.Projection.Gap
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.CSDecomposition
import NumlibSurface.GolubVanLoan.Chapter02.Section04

/-!
# Golub–Van Loan §2.5: subspace metrics

Surface file for [golub2013matrix] §2.5: orthogonal projections as matrices (§2.5.1), the
projections of the SVD (§2.5.2), the distance between subspaces (2.5.1), its block form
(Theorem 2.5.1) and its basic properties (§2.5.3), and the CS decomposition in its thin and full
forms (Theorems 2.5.2–2.5.3).

## Conventions

Subspaces of `ℝⁿ` are `Submodule ℝ (EuclideanSpace ℝ (Fin n))`, `ran(P)` is
`LinearMap.range (Matrix.toEuclideanLin P)`, and `span{v}` is `ℝ ∙ WithLp.toLp 2 v`. The book's
orthogonal projection matrix is the predicate `IsOrthogonalProjection P S`, identified with
Mathlib's `S.starProjection` by `IsOrthogonalProjection.iff_toEuclideanLin_eq`. The distance
`dist(S₁, S₂) = ‖P₁ - P₂‖₂` of (2.5.1) is the backbone's `Submodule.gap` (the operator norm of the
difference of the orthogonal projections), restated as `subspaceDist`; the book defines it only for
`dim S₁ = dim S₂`, and the theorems that need it carry that hypothesis.

The column blocks `W(:, 1:k)` and `W(:, k+1:n)` of an `n × n` matrix are `W.submatrix id` along
`Fin.castLE` and along `Fin.cast _ ∘ Fin.natAdd k`. The CS decomposition is stated in the book's
block form with `Matrix.fromRows`/`Matrix.fromBlocks`; its diagonal-like blocks are the backbone's
`Matrix.rectDiagonal`, `Matrix.shiftedRectDiagonal` and `Matrix.csdUpperRight` of the angles
`θ : ℕ → ℝ` (0-based; the first `p` angles are `0`, giving the identity blocks).

## Sources

Backbone `Numlib/Analysis/InnerProductSpace/Projection/Gap`; Mathlib's orthogonal projections
(`Submodule.starProjection`, `LinearMap.IsSymmetricProjection`); the matrix form of Theorem 2.5.1,
`Matrix.gap_range_eq_l2_opNorm_conjTranspose_mul` (whose proof is not the book's `Q₁₂`/`Q₂₁`
argument but the one-sided gap of equal-dimensional subspaces); and
`Numlib/LinearAlgebra/Matrix/CSDecomposition` (`Matrix.exists_isThinCSD`, `Matrix.exists_isCSD`,
which need neither the book's `m₂ ≥ n₁` in Theorem 2.5.2 nor its `m₁ ≥ m₂` in Theorem 2.5.3). The
two illustrative CS patterns after Theorem 2.5.3 are examples; (2.5.2) only names `Q = Wᵀ Z`
inside a proof.

## Readings

The display of Theorem 2.5.3 has its row labels mangled (`n₁ - n₁`); the block sizes that add up
are rows `p, n₁ - p, m₁ - n₁ | n₁ - p, q` and columns `p, n₁ - p | n₁ - p, q, m₁ - n₁`, the layout
of the backbone's predicate `Matrix.IsCSD`, which the statement below reproduces.
-/

open Matrix WithLp

namespace GolubVanLoan.Chapter02

variable {m n k : ℕ}

/-! ### §2.5.1 Orthogonal projections -/

/-- **§2.5.1, orthogonal projection.** `P ∈ ℝ^{n×n}` is the orthogonal projection onto the
subspace `S ⊆ ℝⁿ` if `ran(P) = S`, `P² = P` and `Pᵀ = P`. -/
structure IsOrthogonalProjection (P : Matrix (Fin n) (Fin n) ℝ)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop where
  /-- The range of `P` is `S`. -/
  range_eq : LinearMap.range (toEuclideanLin P) = S
  /-- `P` is idempotent. -/
  mul_self : P * P = P
  /-- `P` is symmetric. -/
  transpose_eq : Pᵀ = P

/-- The orthogonal projection onto `S` is a symmetric projection of `EuclideanSpace`. -/
private theorem isSymmetricProjection_starProjection' (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    (S.starProjection : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _).IsSymmetricProjection :=
  ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap S.isIdempotentElem_starProjection,
    S.starProjection_isSymmetric⟩

/-- **§2.5.1**: `P` is the orthogonal projection onto `S` exactly when it acts as Mathlib's
orthogonal projection `S.starProjection`. -/
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

/-- **§2.5.1**: if `P` is the orthogonal projection onto `S`, then `P x ∈ S` and
`(I - P) x ∈ S⊥` for every `x` (the book's "easy to show"). -/
theorem IsOrthogonalProjection.mem_and_sub_mem_orthogonal {P : Matrix (Fin n) (Fin n) ℝ}
    {S : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (hP : IsOrthogonalProjection P S)
    (x : EuclideanSpace ℝ (Fin n)) :
    toEuclideanLin P x ∈ S ∧ toEuclideanLin (1 - P) x ∈ Sᗮ := by
  have h := IsOrthogonalProjection.iff_toEuclideanLin_eq.1 hP
  rw [map_sub, toEuclideanLin_one, LinearMap.sub_apply, h]
  exact ⟨S.starProjection_apply_mem x, S.sub_starProjection_mem_orthogonal x⟩

/-- **§2.5.1, the display**: for orthogonal projections `P₁`, `P₂` and any `z`,
`‖(P₁ - P₂) z‖₂² = (P₁ z)ᵀ (I - P₂) z + (P₂ z)ᵀ (I - P₁) z`. -/
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

/-- **§2.5.1**: the orthogonal projection onto a subspace is unique. -/
theorem IsOrthogonalProjection.unique {P₁ P₂ : Matrix (Fin n) (Fin n) ℝ}
    {S : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h₁ : IsOrthogonalProjection P₁ S)
    (h₂ : IsOrthogonalProjection P₂ S) : P₁ = P₂ :=
  toEuclideanLin.injective ((IsOrthogonalProjection.iff_toEuclideanLin_eq.1 h₁).trans
    (IsOrthogonalProjection.iff_toEuclideanLin_eq.1 h₂).symm)

/-- **§2.5.1**: if the columns of `V = [v₁ | ⋯ | v_k]` are an orthonormal basis of `S`
(`VᵀV = I`, `ran(V) = S`), then `P = V Vᵀ` is the orthogonal projection onto `S`. -/
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

/-- **§2.5.1**: for `v ≠ 0`, `P = v vᵀ / vᵀv` is the orthogonal projection onto `span{v}`. -/
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

/-- The columns of an orthogonal matrix selected along an injection are orthonormal. -/
private theorem transpose_mul_submatrix_eq_one {k : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W ∈ orthogonalGroup (Fin n) ℝ) {e : Fin k → Fin n} (he : Function.Injective e) :
    (W.submatrix id e)ᵀ * W.submatrix id e = 1 := by
  rw [transpose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
    (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hW]
  exact submatrix_one e he

/-- The trailing column block `W(:, k+1:n)`: `Fin (n - k) → Fin n`, `j ↦ k + j`. -/
private theorem cast_natAdd_injective {k : ℕ} (hk : k ≤ n) :
    Function.Injective (Fin.cast (Nat.add_sub_of_le hk) ∘ Fin.natAdd k : Fin (n - k) → Fin n) :=
  (Fin.cast_injective _).comp (Fin.natAdd_injective _ k)

/-- The leading and trailing column blocks `W(:, 1:k)`, `W(:, k+1:n)` of an orthogonal `W` have
complementary ranges (§2.1.5). -/
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

/-- The span of the columns `j ≥ k` of `W` is the range of the trailing block `W(:, k+1:n)`. -/
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

/-- The span of the columns `i < k` of `W` is the range of the leading block `W(:, 1:k)`. -/
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

/-- **§2.5.2, SVD-related projections.** If `A = U Σ Vᵀ` is the SVD of `A ∈ ℝ^{m×n}`,
`r = rank(A)`, and `U = [U_r | Ũ_r]`, `V = [V_r | Ṽ_r]` (the first `r` columns and the rest), then
`V_r V_rᵀ` is the orthogonal projection onto `null(A)⊥ = ran(Aᵀ)`, `Ṽ_r Ṽ_rᵀ` onto `null(A)`,
`U_r U_rᵀ` onto `ran(A)` and `Ũ_r Ũ_rᵀ` onto `ran(A)⊥ = null(Aᵀ)`. From Corollary 2.4.6 and
§2.5.1. -/
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

/-- **(2.5.1), the distance between subspaces** `dist(S₁, S₂) = ‖P₁ - P₂‖₂`, `Pᵢ` the orthogonal
projection onto `Sᵢ`: the backbone's gap `Submodule.gap`. The book defines it for
`dim(S₁) = dim(S₂)`, which the theorems below assume where they need it. -/
noncomputable def subspaceDist (S₁ S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  S₁.gap S₂

/-- **(2.5.1), with projection matrices**: if `P₁`, `P₂` are the orthogonal projections onto `S₁`,
`S₂`, then `dist(S₁, S₂) = ‖P₁ - P₂‖₂`. -/
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

/-- **Theorem 2.5.1.** If `W = [W₁ | W₂]`, `Z = [Z₁ | Z₂]` are `n × n` orthogonal matrices with
`W₁`, `Z₁` of `k` columns, `S₁ = ran(W₁)` and `S₂ = ran(Z₁)`, then
`dist(S₁, S₂) = ‖W₁ᵀ Z₂‖₂ = ‖Z₁ᵀ W₂‖₂`. Backbone `Matrix.gap_range_eq_l2_opNorm_conjTranspose_mul`
twice (with `W`, `Z` exchanged and `Submodule.gap_comm`); the blocks of an orthogonal matrix have
orthonormal columns and complementary ranges (§2.1.5). -/
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

/-- **§2.5.3**: `0 ≤ dist(S₁, S₂) ≤ 1` (no dimension hypothesis is needed). -/
theorem subspaceDist_mem_Icc (S₁ S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    subspaceDist S₁ S₂ ∈ Set.Icc 0 1 :=
  ⟨S₁.gap_nonneg S₂, S₁.gap_le_one S₂⟩

/-- **§2.5.3**: `dist(S₁, S₂) = 0 ⇒ S₁ = S₂` (in fact `⇔`). -/
theorem subspaceDist_eq_zero {S₁ S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))} :
    subspaceDist S₁ S₂ = 0 ↔ S₁ = S₂ :=
  S₁.gap_eq_zero_iff S₂

/-- **§2.5.3**: for `dim(S₁) = dim(S₂)`, `dist(S₁, S₂) = 1 ⇒ S₁ ∩ S₂⊥ ≠ {0}` (in fact `⇔`). -/
theorem subspaceDist_eq_one {S₁ S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (h : Module.finrank ℝ S₁ = Module.finrank ℝ S₂) :
    subspaceDist S₁ S₂ = 1 ↔ S₁ ⊓ S₂ᗮ ≠ ⊥ :=
  S₁.gap_eq_one_iff_of_finrank_eq S₂ h

/-! ### §2.5.4 The CS decomposition -/

/-- **Theorem 2.5.2 (the CS decomposition, thin version).** If `Q₁ ∈ ℝ^{m₁×n₁}`,
`Q₂ ∈ ℝ^{m₂×n₁}` with `m₁ ≥ n₁`, `m₂ ≥ n₁`, and the columns of `Q = [Q₁; Q₂]` are orthonormal,
then there are orthogonal `U₁ ∈ ℝ^{m₁×m₁}`, `U₂ ∈ ℝ^{m₂×m₂}`, `V₁ ∈ ℝ^{n₁×n₁}` with
`diag(U₁, U₂)ᵀ [Q₁; Q₂] V₁ = [C₀; S₀]`, `C₀ = diag(cos θ₁, …, cos θ_{n₁}) ∈ ℝ^{m₁×n₁}`,
`S₀ = diag(sin θ₁, …, sin θ_{n₁}) ∈ ℝ^{m₂×n₁}` and `0 ≤ θ₁ ≤ ⋯ ≤ θ_{n₁} ≤ π/2`. Backbone
`Matrix.exists_isThinCSD`, whose shift `p = n₁ - min n₁ m₂` vanishes here. -/
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
  have hl := hc.star_mul_mul_left
  have hr := hc.star_mul_mul_right
  rw [hp, shiftedRectDiagonal_zero] at hr
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, id] at hl hr
  refine ⟨U₁, hc.mem_unitaryGroup_left₁, U₂, hc.mem_unitaryGroup_left₂, V,
    hc.mem_unitaryGroup_right, θ, ?_, hc.monotone, hc.mem_Icc⟩
  rw [fromBlocks_transpose, fromBlocks_mul_fromRows, fromRows_mul]
  simp only [transpose_zero, Matrix.zero_mul, add_zero, zero_add, hl, hr]

/-- **Theorem 2.5.3 (the CS decomposition).** If `Q = [Q₁₁ Q₁₂; Q₂₁ Q₂₂]` (row blocks `m₁, m₂`,
column blocks `n₁, n₂`) is square and orthogonal and `m₁ ≥ n₁`, then with
`p = max{0, n₁ - m₂}` and `q = max{0, m₂ - n₁}` there are orthogonal `U₁, U₂, V₁, V₂` such that
`diag(U₁, U₂)ᵀ Q diag(V₁, V₂)` has the block form
`[I 0 0 0 0; 0 C S 0 0; 0 0 0 0 I; 0 S -C 0 0; 0 0 0 I 0]` with `C = diag(c_{p+1}, …, c_{n₁})`,
`S = diag(s_{p+1}, …, s_{n₁})`, `c_i = cos θ_i`, `s_i = sin θ_i` and
`0 ≤ θ_{p+1} ≤ ⋯ ≤ θ_{n₁} ≤ π/2` (0-based: the angles `θ i` are monotone in `[0, π/2]` with the
first `p` of them `0`, which produces the identity block). The four blocks are the backbone's
`Matrix.rectDiagonal`, `Matrix.csdUpperRight`, `Matrix.shiftedRectDiagonal` patterns of the
predicate `Matrix.IsCSD` (`Matrix.exists_isCSD`); the book's hypothesis `m₁ ≥ m₂` is not needed. -/
theorem theorem_2_5_3 {m₁ m₂ n₁ n₂ : ℕ} (Q₁₁ : Matrix (Fin m₁) (Fin n₁) ℝ)
    (Q₁₂ : Matrix (Fin m₁) (Fin n₂) ℝ) (Q₂₁ : Matrix (Fin m₂) (Fin n₁) ℝ)
    (Q₂₂ : Matrix (Fin m₂) (Fin n₂) ℝ) (hsq : m₁ + m₂ = n₁ + n₂)
    (hQ : (fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂)ᵀ * fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂ = 1)
    (_hQ' : fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂ * (fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂)ᵀ = 1) (h₁ : n₁ ≤ m₁) :
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
  have h11 := hc.star_mul_mul₁₁
  have h12 := hc.star_mul_mul₁₂
  have h21 := hc.star_mul_mul₂₁
  have h22 := hc.star_mul_mul₂₂
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, id] at h11 h12 h21 h22
  refine ⟨U₁, hc.mem_unitaryGroup_left₁, U₂, hc.mem_unitaryGroup_left₂, V₁,
    hc.mem_unitaryGroup_right₁, V₂, hc.mem_unitaryGroup_right₂, θ, ?_, hc.monotone, hc.mem_Icc,
    hc.eq_zero_of_lt⟩
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, h11, h12, h21,
    h22]

end GolubVanLoan.Chapter02
