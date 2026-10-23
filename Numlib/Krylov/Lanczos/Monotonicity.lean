import Numlib.Krylov.Compression
import Numlib.Krylov.Lanczos.Residual
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.InnerProductSpace.Positive.ShiftedSolve
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
/-- Positive definiteness of a later shifted Lanczos matrix passes to every earlier one. -/
theorem shifted_posDef_of_le (A : E →ₗ[ℝ] E) (g : E) (hA : A.IsSymmetric)
    {m l : ℕ} (hml : m ≤ l) (hl : l + 1 ≤ grade A g) (τ : ℝ)
    (hPD : (tridiag A g (l + 1) + τ • 1).PosDef) :
    (tridiag A g (m + 1) + τ • 1).PosDef := by
  have hm : m + 1 ≤ grade A g := (Nat.add_le_add_right hml 1).trans hl
  have hc := compression_isSymmetricCoercive_of_shifted_posDef A g hA hl τ hPD
  apply (Matrix.posDef_iff_isSymmetricCoercive _).mpr
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (shifted_tridiag_isHermitian A g (m + 1) τ),
    (LinearMap.isCoercive_iff_forall_pos _).mpr ?_⟩
  intro y hy
  let s := basisEmbedding A g hm y
  have hs : s ∈ subspace A g (l + 1) :=
    subspace_mono A g (Nat.add_le_add_right hml 1) (basisEmbedding_mem A g hm y)
  have hs0 : (⟨s, hs⟩ : subspace A g (l + 1)) ≠ 0 := by
    intro he
    have h0 : basisEmbedding A g hm y = 0 := congrArg Subtype.val he
    exact hy ((basisEmbedding A g hm).injective (by simpa using h0))
  have hp := hc.isCoercive.inner_self_pos hs0
  rw [compression.inner_apply] at hp
  change 0 < inner ℝ ((A + τ • (LinearMap.id : E →ₗ[ℝ] E)) s) s at hp
  simpa only [s, inner_shifted_apply_basisEmbedding A g hA hm, RCLike.re_to_real] using hp

omit [FiniteDimensional ℝ E] in
/-- A positive-definite shifted projected Lanczos system has an actual solution. -/
theorem exists_shifted_solve (A : E →ₗ[ℝ] E) (g : E) (m : ℕ) (τ : ℝ)
    (hPD : (tridiag A g (m + 1) + τ • 1).PosDef) :
    ∃ y : EuclideanSpace ℝ (Fin (m + 1)),
      Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y =
        -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) := by
  have hr := Matrix.range_toEuclideanLin_eq_top_of_isUnit hPD.isUnit
  have hm : -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) ∈
      LinearMap.range (Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1)) := by
    rw [hr]
    trivial
  exact hm

/-- A complementary multiplier at an earlier feasible solve cannot exceed the shift of
any feasible later solve with positive-definite shifted projected matrix. -/
theorem multiplier_le_of_nested_shifted_solve (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.IsSymmetric) {m l : ℕ} (hml : m ≤ l) (hl : l + 1 ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (z : EuclideanSpace ℝ (Fin (l + 1)))
    {τ μ Δ : ℝ} (hμ : 0 ≤ μ) (hz : ‖z‖ ≤ Δ)
    (hcomp : τ * (‖y‖ ^ 2 - Δ ^ 2) = 0)
    (hPD : (tridiag A g (l + 1) + μ • 1).PosDef)
    (hy : Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)))
    (hsolve : Matrix.toEuclideanLin (tridiag A g (l + 1) + μ • 1) z =
      -(‖g‖ • PiLp.single 2 (0 : Fin (l + 1)) (1 : ℝ))) : τ ≤ μ := by
  by_contra hnot
  have hlt : μ < τ := lt_of_not_ge hnot
  have hτ : 0 < τ := lt_of_le_of_lt hμ hlt
  have hn : ‖y‖ = Δ := by
    have hsq := (mul_eq_zero.mp hcomp).resolve_left hτ.ne'
    have hd : 0 ≤ Δ := (norm_nonneg z).trans hz
    nlinarith [norm_nonneg y]
  have hPDm := shifted_posDef_of_le A g hA hml hl μ hPD
  obtain ⟨w, hw⟩ := exists_shifted_solve A g m μ hPDm
  have hy0 : y ≠ 0 := by
    intro he
    have hb := hy
    rw [he, map_zero] at hb
    have hb0 := congrArg (fun v : EuclideanSpace ℝ (Fin (m + 1)) => v 0) hb
    have hg0 : ‖g‖ = 0 := by simpa [PiLp.single_apply] using hb0
    exact (norm_ne_zero_iff.mpr hg) hg0
  have he : Matrix.toEuclideanLin (tridiag A g (m + 1) + μ • 1) w =
      Matrix.toEuclideanLin (tridiag A g (m + 1) + μ • 1) y + (τ - μ) • y := by
    rw [hw, ← hy]
    simp only [map_add, map_smul, Matrix.toEuclideanLin_one, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    module
  have hstrict := LinearMap.norm_lt_norm_of_shifted_solve
    (A := Matrix.toEuclideanLin (tridiag A g (m + 1) + μ • 1))
    (fun v => by simpa only [RCLike.re_to_real] using
      ((Matrix.posDef_iff_isSymmetricCoercive _).mp hPDm).isPositive.2 v)
    (sub_pos.mpr hlt) hy0 he
  have hnorm := norm_le_norm_of_nested_shifted_solve A hg hA hml hl w z μ hPD hw hsolve
  linarith
end Lanczos
