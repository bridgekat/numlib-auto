/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter02.Section04
import Numlib.Eigen.Normal
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

/-- The orthogonal projector matrix onto a subspace is Hermitian. -/
theorem isHermitian_orthogonalProjector [DecidableEq n]
    (L : Submodule ℂ (EuclideanSpace ℂ n)) : (orthogonalProjector L).IsHermitian := by
  apply toEuclideanLin.injective
  rw [toEuclideanLin_conjTranspose_eq_adjoint, toEuclideanLin_orthogonalProjector]
  exact L.starProjection_isSymmetric.adjoint_eq

/-- In the spectral decomposition of a normal matrix, the idempotents are the
orthogonal projectors onto its eigenspaces. -/
theorem theorem_15_eigenspaces [DecidableEq n] {A : Matrix n n ℂ} (hA : IsStarNormal A) :
    IsDiagonalSpectralDecomposition A
      (fun z => orthogonalProjector (Module.End.eigenspace (toEuclideanLin A) z)) := by
  let f : Module.End ℂ (EuclideanSpace ℂ n) := toEuclideanLin A
  let E (z : ℂ) := orthogonalProjector (f.eigenspace z)
  have hN : IsStarNormal f := isStarNormal_toEuclideanLin_iff.mpr hA
  have hTop := LinearMap.IsStarNormal.iSup_eigenspace_eq_top hN
  have hOrth := LinearMap.IsStarNormal.orthogonalFamily_eigenspaces hN
  have hSpec : spectrum ℂ f = spectrum ℂ A :=
    AlgEquiv.spectrum_eq (toLpLinAlgEquiv (R := ℂ) (n := n) 2) A
  have hBot (z : ℂ) (hz : z ∉ spectralValues A) : f.eigenspace z = ⊥ := by
    by_contra h
    have hz' : f.HasEigenvalue z := Module.End.hasEigenvalue_iff.mpr h
    exact hz ((mem_spectralValues_iff A z).mpr (hSpec ▸ hz'.mem_spectrum))
  have hApply (z w : ℂ) {x : EuclideanSpace ℂ n} (hx : x ∈ f.eigenspace w) :
      toEuclideanLin (E z) x = if w = z then x else 0 := by
    change toEuclideanLin (orthogonalProjector (f.eigenspace z)) x = _
    rw [toEuclideanLin_orthogonalProjector]
    split_ifs with h
    · subst w
      exact Submodule.starProjection_eq_self_iff.mpr hx
    · apply (Submodule.starProjection_apply_eq_zero_iff (K := f.eigenspace z)).mpr
      exact (Submodule.mem_orthogonal' _ _).mpr fun y hy => hOrth h ⟨x, hx⟩ ⟨y, hy⟩
  have hExt {B C : Matrix n n ℂ}
      (h : ∀ z (x : EuclideanSpace ℂ n), x ∈ f.eigenspace z →
        toEuclideanLin B x = toEuclideanLin C x) : B = C := by
    apply toEuclideanLin.injective
    apply LinearMap.eqLocus_eq_top.mp
    apply top_unique
    rw [← hTop]
    exact iSup_le fun z x hx => h z x hx
  have hSum (c : ℂ → ℂ) (w : ℂ) {x : EuclideanSpace ℂ n} (hx : x ∈ f.eigenspace w) :
      toEuclideanLin (∑ z ∈ spectralValues A, c z • E z) x = c w • x := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    by_cases hw : w ∈ spectralValues A
    · rw [Finset.sum_eq_single_of_mem w hw]
      · simp [hApply w w hx]
      · intro z _ hz
        simp [hApply z w hx, Ne.symm hz]
    · have h0 : x = 0 := by rwa [hBot w hw, Submodule.mem_bot] at hx
      simp [h0]
  change IsDiagonalSpectralDecomposition A E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    apply toEuclideanLin.injective
    simp [E, hBot z hz, Submodule.starProjection_bot]
  · intro z w
    apply toEuclideanLin.injective
    apply LinearMap.ext
    intro x
    rw [toEuclideanLin_mul_apply]
    have hx : toEuclideanLin (E w) x ∈ f.eigenspace w := by
      change toEuclideanLin (orthogonalProjector (f.eigenspace w)) x ∈ _
      rw [toEuclideanLin_orthogonalProjector]
      exact (f.eigenspace w).starProjection_apply_mem x
    rw [hApply z w hx]
    by_cases h : z = w
    · subst w
      simp
    · simp [h, Ne.symm h]
  · apply hExt
    intro w x hx
    have h := hSum (fun _ => 1) w hx
    simp only [one_smul] at h
    change toEuclideanLin (∑ z ∈ spectralValues A, E z) x =
      toLpLinAlgEquiv (R := ℂ) (n := n) 2 (1 : Matrix n n ℂ) x
    rw [map_one]
    exact h
  · apply hExt
    intro w x hx
    exact (Module.End.mem_eigenspace_iff.mp hx).trans (hSum id w hx).symm

/-- **Theorem 15** of [benIsrael2003generalized], Chapter 2. A complex matrix is
normal precisely when its spectral decomposition uses orthogonal projectors. -/
theorem theorem_15 [DecidableEq n] (A : Matrix n n ℂ) :
    IsStarNormal A ↔ ∃ E, IsDiagonalSpectralDecomposition A E ∧ ∀ z, (E z).IsHermitian := by
  constructor
  · intro hA
    exact ⟨_, theorem_15_eigenspaces hA, fun z =>
      isHermitian_orthogonalProjector (Module.End.eigenspace (toEuclideanLin A) z)⟩
  · rintro ⟨E, hE, hH⟩
    have hAdj : Aᴴ = ∑ z ∈ spectralValues A, star z • E z := by
      have h := congrArg Matrix.conjTranspose hE.weightedSum
      simpa only [conjTranspose_sum, conjTranspose_smul, fun z => (hH z).eq] using h
    have hComm (z w : ℂ) : Commute (E z) (E w) := by
      by_cases h : z = w
      · subst w
        exact Commute.refl _
      · change E z * E w = E w * E z
        rw [hE.mul, hE.mul w z, ite_eq_right h, ite_eq_right (Ne.symm h)]
    have h : Commute (∑ z ∈ spectralValues A, star z • E z) (∑ w ∈ spectralValues A, w • E w) := by
      apply Commute.sum_left
      intro z _
      apply Commute.sum_right
      intro w _
      exact ((hComm z w).smul_left (star z)).smul_right w
    rw [← hAdj, ← hE.weightedSum] at h
    exact ⟨h⟩

/-- **Exercise 54** of [benIsrael2003generalized], Chapter 2. A normal matrix and
its adjoint have the same eigenvectors, with conjugate eigenvalues. -/
theorem exercise_54 {A : Matrix n n ℂ} (hA : IsStarNormal A) (z : ℂ) (x : n → ℂ) :
    A *ᵥ x = z • x ↔ Aᴴ *ᵥ x = star z • x := by
  classical
  have hMem (B : Matrix n n ℂ) (w : ℂ) :
      B *ᵥ x = w • x ↔
        WithLp.toLp 2 x ∈ Module.End.eigenspace (toEuclideanLin B) w := by
    rw [Module.End.mem_eigenspace_iff, toEuclideanLin_toLp]
    change _ ↔ WithLp.toLp 2 (B *ᵥ x) = WithLp.toLp 2 (w • x)
    exact (WithLp.toLp_injective 2).eq_iff.symm
  rw [hMem A z, hMem Aᴴ (star z), toEuclideanLin_conjTranspose_eq_adjoint]
  exact SetLike.ext_iff.mp
    (LinearMap.IsStarNormal.eigenspace_adjoint (isStarNormal_toEuclideanLin_iff.mpr hA) z).symm _

/-- **Exercise 55** of [benIsrael2003generalized], Chapter 2. A basis matrix $F$
gives the orthogonal projector onto its column space as $FF^\dagger$ or as
$F(F^HF)^{-1}F^H$. -/
theorem exercise_55 [Fintype k] [DecidableEq k] [DecidableEq n]
    (F : Matrix n k ℂ) (L : Submodule ℂ (EuclideanSpace ℂ n))
    (hF : LinearIndependent ℂ Fᵀ) (hL : (toEuclideanLin F).range = L) :
    orthogonalProjector L = F * F.pinv ∧
      orthogonalProjector L = F * (Fᴴ * F)⁻¹ * Fᴴ := by
  have h : orthogonalProjector L = F * F.pinv := by
    apply toEuclideanLin.injective
    rw [toEuclideanLin_orthogonalProjector, F.mul_pinv_eq_starProjection]
    exact congrArg (fun S : Submodule ℂ (EuclideanSpace ℂ n) =>
      (S.starProjection : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)) hL.symm
  refine ⟨h, ?_⟩
  rw [h, F.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hF, Matrix.mul_assoc]

/-- **Exercise 56** of [benIsrael2003generalized], Chapter 2. The projectors
onto a subspace and its orthogonal complement add to the identity. -/
theorem exercise_56 [DecidableEq n] (L : Submodule ℂ (EuclideanSpace ℂ n)) :
    orthogonalProjector Lᗮ = 1 - orthogonalProjector L := by
  apply toEuclideanLin.injective
  change toEuclideanLin (orthogonalProjector Lᗮ) =
    toLpLinAlgEquiv (R := ℂ) (n := n) 2 (1 - orthogonalProjector L)
  rw [map_sub, map_one, toEuclideanLin_orthogonalProjector]
  change (Lᗮ.starProjection : Module.End ℂ (EuclideanSpace ℂ n)) =
    1 - toEuclideanLin (orthogonalProjector L)
  rw [toEuclideanLin_orthogonalProjector, Submodule.starProjection_orthogonal']
  rfl

end BenIsraelGreville.Chapter02
