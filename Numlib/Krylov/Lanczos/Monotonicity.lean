import Numlib.Krylov.Compression
import Numlib.Krylov.Lanczos.Residual
import Numlib.Analysis.Matrix.ToEuclideanLin
import Mathlib.Tactic
/-!
# Norm comparison for genuine shifted Lanczos solves

The projected matrix represents the actual compressed shifted quadratic form.
Its positive definiteness gives coercivity only where needed, so nested solve
radii can be compared even for indefinite ambient operators.
-/

open scoped Matrix ComplexOrder
namespace Lanczos
open Krylov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The shifted Lanczos matrix is the actual bilinear form of the shifted operator on its
Krylov space. -/
theorem inner_shifted_apply_basisEmbedding (A : E →ₗ[ℝ] E) (g : E)
    (hA : A.IsSymmetric) {m : ℕ} (hm : m + 1 ≤ grade A g)
    (y z : EuclideanSpace ℝ (Fin (m + 1))) (τ : ℝ) :
    inner ℝ ((A + τ • (LinearMap.id : E →ₗ[ℝ] E)) (basisEmbedding A g hm y))
      (basisEmbedding A g hm z) =
      inner ℝ (Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y) z := by
  have hn : inner ℝ (Arnoldi.vec A g (m + 1)) (basisEmbedding A g hm z) = 0 :=
    Submodule.inner_left_of_mem_orthogonal (basisEmbedding_mem A g hm z)
      (Arnoldi.vec_mem_orthogonal A g (m + 1))
  change inner ℝ (A (basisEmbedding A g hm y) + τ • basisEmbedding A g hm y) _ = _
  rw [shifted_apply_basisEmbedding A g hA hm y τ, inner_add_left,
    real_inner_smul_left, hn, mul_zero, add_zero,
    (basisEmbedding A g hm).inner_map_map]

/-- Positive definiteness of the genuine shifted Lanczos matrix is coercivity of the
shifted operator compressed to its actual Krylov space. -/
theorem compression_isSymmetricCoercive_of_shifted_posDef (A : E →ₗ[ℝ] E) (g : E)
    (hA : A.IsSymmetric) {m : ℕ} (hm : m + 1 ≤ grade A g) (τ : ℝ)
    (hPD : (tridiag A g (m + 1) + τ • 1).PosDef) :
    (compression (A + τ • (LinearMap.id : E →ₗ[ℝ] E))
      (subspace A g (m + 1))).IsSymmetricCoercive := by
  let B := Arnoldi.orthonormalBasis A g hm
  have hshift : (A + τ • (LinearMap.id : E →ₗ[ℝ] E)).IsSymmetric :=
    hA.add (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id)
  obtain ⟨c, hc, hcmap⟩ := ((Matrix.posDef_iff_isSymmetricCoercive _).mp hPD).isCoercive
  refine ⟨compression.isSymmetric _ _ hshift, c, hc, fun z => ?_⟩
  have he : basisEmbedding A g hm (B.repr z) = (z : E) := by
    change ((B.repr.symm (B.repr z) : subspace A g (m + 1)) : E) = (z : E)
    rw [B.repr.symm_apply_apply]
  have hh := hcmap (B.repr z)
  rw [B.repr.norm_map] at hh
  rw [compression.inner_apply]
  change c * ‖z‖ ^ 2 ≤
    inner ℝ ((A + τ • (LinearMap.id : E →ₗ[ℝ] E)) (z : E)) (z : E)
  rw [← he, inner_shifted_apply_basisEmbedding A g hA hm]
  exact hh

/-- A genuine shifted Lanczos solve is a Galerkin iterate of the shifted ambient system. -/
theorem isGalerkinIterate_of_shifted_solve (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.IsSymmetric) {m : ℕ} (hm : m + 1 ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (τ : ℝ)
    (hsolve : Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) :
    IsGalerkinIterate (A + τ • (LinearMap.id : E →ₗ[ℝ] E)) (-g) 0 (m + 1)
      (basisEmbedding A g hm y) := by
  have hspace : subspace (A + τ • (LinearMap.id : E →ₗ[ℝ] E)) (-g) (m + 1) =
      subspace A g (m + 1) := by
    rw [show τ • (LinearMap.id : E →ₗ[ℝ] E) = algebraMap ℝ (E →ₗ[ℝ] E) τ by
      rfl]
    rw [subspace_add_algebraMap]
    simpa only [neg_one_smul] using
      subspace_smul_of_ne_zero A g (by norm_num : (-1 : ℝ) ≠ 0) (m + 1)
  constructor
  · simpa only [map_zero, sub_zero, hspace] using basisEmbedding_mem A g hm y
  · simp only [map_zero, sub_zero, hspace]
    have hr := residual_eq A hg hA hm y τ hsolve
    have he : -g - (A + τ • (LinearMap.id : E →ₗ[ℝ] E)) (basisEmbedding A g hm y) =
        -(Lanczos.beta A g m * y (Fin.last m)) • Arnoldi.vec A g (m + 1) := by
      change -g - (A (basisEmbedding A g hm y) + τ • basisEmbedding A g hm y) = _
      rw [neg_smul]
      rw [← hr]
      abel
    rw [he]
    exact Submodule.smul_mem _ _ (Arnoldi.vec_mem_orthogonal A g (m + 1))

/-- Actual shifted Lanczos solves have nondecreasing radii along nested Krylov spaces,
provided the later shifted projected matrix is positive definite. -/
theorem norm_le_norm_of_nested_shifted_solve (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.IsSymmetric) {m l : ℕ} (hml : m ≤ l) (hl : l + 1 ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (z : EuclideanSpace ℝ (Fin (l + 1)))
    (τ : ℝ) (hPD : (tridiag A g (l + 1) + τ • 1).PosDef)
    (hy : Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)))
    (hz : Matrix.toEuclideanLin (tridiag A g (l + 1) + τ • 1) z =
      -(‖g‖ • PiLp.single 2 (0 : Fin (l + 1)) (1 : ℝ))) : ‖y‖ ≤ ‖z‖ := by
  have hm : m + 1 ≤ grade A g := (Nat.add_le_add_right hml 1).trans hl
  have hspace : subspace (A + τ • (LinearMap.id : E →ₗ[ℝ] E)) (-g) (l + 1) =
      subspace A g (l + 1) := by
    rw [show τ • (LinearMap.id : E →ₗ[ℝ] E) = algebraMap ℝ (E →ₗ[ℝ] E) τ by rfl,
      subspace_add_algebraMap]
    simpa only [neg_one_smul] using
      subspace_smul_of_ne_zero A g (by norm_num : (-1 : ℝ) ≠ 0) (l + 1)
  have hcomp : (compression (A + τ • (LinearMap.id : E →ₗ[ℝ] E))
      (subspace (A + τ • (LinearMap.id : E →ₗ[ℝ] E))
        (-g) (l + 1))).IsSymmetricCoercive := by
    have hc := compression_isSymmetricCoercive_of_shifted_posDef A g hA hl τ hPD
    obtain ⟨c, hcpos, hbound⟩ := hc.isCoercive
    refine ⟨compression.isSymmetric _ _
      (hA.add (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id)),
        c, hcpos, fun v => ?_⟩
    have hv : (v : E) ∈ subspace A g (l + 1) := by
      rw [← hspace]
      exact v.property
    have hh := hbound ⟨(v : E), hv⟩
    rw [compression.inner_apply] at hh ⊢
    exact hh
  have hh := norm_le_norm_of_compression_isSymmetricCoercive _ (-g)
    (Nat.succ_pos l) (Nat.add_le_add_right hml 1) hcomp
    (isGalerkinIterate_of_shifted_solve A hg hA hm y τ hy)
    (isGalerkinIterate_of_shifted_solve A hg hA hl z τ hz)
  simpa only [(basisEmbedding A g hm).norm_map, (basisEmbedding A g hl).norm_map] using hh
end Lanczos
