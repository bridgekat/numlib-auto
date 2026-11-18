/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter02.Section04
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Orthogonal projectors

Section 2.7 of [benIsrael2003generalized] describes the orthogonal projector by an
orthonormal basis for its range. An oblique projector is Hermitian precisely when
its kernel is the orthogonal complement of its range.
-/

namespace BenIsraelGreville.Chapter02

open Matrix
open scoped InnerProductSpace BigOperators

variable {n k : Type*} [Fintype n]

/-- **Section 2.7** of [benIsrael2003generalized]. The orthogonal projector onto $L$ is
the matrix of the orthogonal projection to $L$. -/
noncomputable def orthogonalProjector [DecidableEq n] (L : Submodule ℂ (EuclideanSpace ℂ n)) :
    Matrix n n ℂ :=
  toEuclideanLin.symm (L.starProjection : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)

/-- The operator of the orthogonal projector matrix onto $L$ is the orthogonal projection to $L$. -/
@[simp] theorem toEuclideanLin_orthogonalProjector [DecidableEq n]
    (L : Submodule ℂ (EuclideanSpace ℂ n)) :
    toEuclideanLin (orthogonalProjector L) =
      (L.starProjection : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) :=
  toEuclideanLin.apply_symm_apply _

/-- An orthogonal projector matrix is idempotent. -/
theorem isIdempotentElem_orthogonalProjector [DecidableEq n]
    (L : Submodule ℂ (EuclideanSpace ℂ n)) : IsIdempotentElem (orthogonalProjector L) := by
  change orthogonalProjector L * orthogonalProjector L = orthogonalProjector L
  apply toEuclideanLin.injective
  rw [toEuclideanLin_mul, toEuclideanLin_orthogonalProjector]
  exact (Submodule.isSymmetricProjection_starProjection L).isIdempotentElem

/-- **Equation (65)** of [benIsrael2003generalized], Chapter 2. If the columns of $V$ form an
orthonormal basis of $L$, then the projector onto $L$ is the sum of their rank-one projectors. -/
theorem orthogonalProjector_apply_eq_sum [Fintype k] [DecidableEq n] [DecidableEq k]
    (L : Submodule ℂ (EuclideanSpace ℂ n)) (V : Matrix n k ℂ)
    (hV : Vᴴ * V = 1) (hL : LinearMap.range (toEuclideanLin V) = L) (i j : n) :
    orthogonalProjector L i j = ∑ l, V i l * star (V j l) := by
  have h : orthogonalProjector L = V * Vᴴ := by
    apply toEuclideanLin.injective
    rw [toEuclideanLin_orthogonalProjector,
      toEuclideanLin_mul_conjTranspose_eq_starProjection hV]
    exact congrArg (fun S : Submodule ℂ (EuclideanSpace ℂ n) =>
      (S.starProjection : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)) hL.symm
  rw [h]
  rfl

/-- **Lemma 3** of [benIsrael2003generalized], Chapter 2. For complementary subspaces
$L$ and $M$, the projector onto $L$ along $M$ is Hermitian as a linear operator exactly
when $M=L^\perp$. -/
theorem lemma_3 {L M : Submodule ℂ (EuclideanSpace ℂ n)} (h : IsCompl L M) :
    (projector h).IsSymmetric ↔ M = Lᗮ := by
  constructor
  · intro hSymm
    have hProj : (projector h).IsSymmetricProjection :=
      ⟨Submodule.isIdempotentElem_projection h, hSymm⟩
    obtain ⟨_, he⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hProj
    have hk := congrArg LinearMap.ker he
    simpa only [Submodule.ker_projection, Submodule.ker_starProjection,
      Submodule.range_projection] using hk
  · rintro rfl
    exact L.starProjection_isSymmetric

end BenIsraelGreville.Chapter02
