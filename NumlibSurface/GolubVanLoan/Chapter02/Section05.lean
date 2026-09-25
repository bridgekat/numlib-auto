import Numlib.Analysis.InnerProductSpace.Projection.Gap
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Matrix.ToEuclideanLin

/-!
# Golub–Van Loan §2.5: subspace metrics

Surface file for [golub2013matrix] §2.5: orthogonal projections as matrices (§2.5.1), the distance
between subspaces (2.5.1) and its basic properties (§2.5.3).

## Conventions

Subspaces of `ℝⁿ` are `Submodule ℝ (EuclideanSpace ℝ (Fin n))`, `ran(P)` is
`LinearMap.range (Matrix.toEuclideanLin P)`, and `span{v}` is `ℝ ∙ WithLp.toLp 2 v`. The book's
orthogonal projection matrix is the predicate `IsOrthogonalProjection P S`, identified with
Mathlib's `S.starProjection` by `IsOrthogonalProjection.iff_toEuclideanLin_eq`. The distance
`dist(S₁, S₂) = ‖P₁ - P₂‖₂` of (2.5.1) is the backbone's `Submodule.gap` (the operator norm of the
difference of the orthogonal projections), restated as `subspaceDist`; the book defines it only for
`dim S₁ = dim S₂`, and the theorems that need it carry that hypothesis.

The SVD projections of §2.5.2, Theorem 2.5.1 and the CS decomposition (Theorems 2.5.2–2.5.3) wait
for their backbone (the SVD predicate `Matrix.IsSVD` and Corollary 2.4.6, the matrix form
`Matrix.gap_range_eq_l2_opNorm_conjTranspose_mul`, `Numlib/LinearAlgebra/Matrix/CSDecomposition`)
and are planned in this group.

## Sources

Backbone `Numlib/Analysis/InnerProductSpace/Projection/Gap`; Mathlib's orthogonal projections
(`Submodule.starProjection`, `LinearMap.IsSymmetricProjection`). The two illustrative CS patterns
after Theorem 2.5.3 are examples; (2.5.2) only names `Q = Wᵀ Z` inside a proof.
-/

open Matrix WithLp

namespace GolubVanLoan.Chapter02

variable {n k : ℕ}

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

end GolubVanLoan.Chapter02
