import Numlib.Krylov.Lanczos.Monotonicity
import Numlib.Analysis.InnerProductSpace.Projection.Invariant
import Numlib.LinearAlgebra.Matrix.Tridiagonal.Kernel
import Mathlib.Tactic
/-!
# Projection of compatible shifted systems at the actual Krylov grade

The orthogonal projection of a genuine ambient solution provides an actual
projected solve. Positive semidefiniteness and cyclic forcing make the shifted
Lanczos matrix positive definite, even when the ambient shifted system is singular.
-/

open scoped Matrix ComplexOrder
namespace Lanczos
open Krylov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An actual compatible positive-semidefinite shifted ambient system projects at the true
Krylov grade to a positive-definite solve, with norm no larger than the ambient solution. -/
theorem exists_grade_shifted_solve_le_norm (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.IsSymmetric) {m : ℕ} (hm : m + 1 = grade A g) (τ : ℝ) (x : E)
    (hx : (A + τ • (LinearMap.id : E →ₗ[ℝ] E)) x = -g)
    (hPSD : ∀ v, 0 ≤ inner ℝ ((A + τ • (LinearMap.id : E →ₗ[ℝ] E)) v) v) :
    ∃ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ ≤ ‖x‖ ∧
      Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y =
        -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) ∧
      (tridiag A g (m + 1) + τ • 1).PosDef := by
  let K := subspace A g (m + 1)
  let B := Arnoldi.orthonormalBasis A g hm.le
  let y := B.repr (K.orthogonalProjectionOnto x)
  have hsym : (A + τ • (LinearMap.id : E →ₗ[ℝ] E)).IsSymmetric :=
    hA.add (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id)
  have hAK : ∀ v ∈ K, A v ∈ K := by
    change ∀ v ∈ subspace A g (m + 1), A v ∈ subspace A g (m + 1)
    rw [hm]
    exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp
      (subspace_grade_mem_invtSubmodule A g)
  have hK : ∀ v ∈ K, (A + τ • (LinearMap.id : E →ₗ[ℝ] E)) v ∈ K := by
    intro v hv
    exact K.add_mem (hAK v hv) (K.smul_mem τ hv)
  have he : basisEmbedding A g hm.le y = K.starProjection x := by
    change ((B.repr.symm (B.repr (K.orthogonalProjectionOnto x)) : K) : E) = _
    rw [B.repr.symm_apply_apply]
    rfl
  have hsolveK := compression.apply_orthogonalProjectionOnto _ hsym K hK x
  rw [hx, map_neg] at hsolveK
  have hgK : g ∈ K := self_mem_subspace A g (Nat.succ_pos m)
  have hPg : K.orthogonalProjectionOnto g = ⟨g, hgK⟩ :=
    K.orthogonalProjectionOnto_mem_subspace_eq_self ⟨g, hgK⟩
  rw [hPg] at hsolveK
  have hsolve : Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) := by
    apply ext_inner_right ℝ
    intro z
    have hh := congrArg (fun w : K => inner ℝ w (B.repr.symm z)) hsolveK
    rw [compression.inner_apply] at hh
    change inner ℝ ((A + τ • (LinearMap.id : E →ₗ[ℝ] E)) (K.starProjection x))
      (basisEmbedding A g hm.le z) = inner ℝ (-g) (basisEmbedding A g hm.le z) at hh
    rw [← he, inner_shifted_apply_basisEmbedding A g hA hm.le] at hh
    have hb : basisEmbedding A g hm.le
        (-(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) = -g := by
      rw [map_neg, basisEmbedding_initial A hg hm.le]
    rw [← hb, (basisEmbedding A g hm.le).inner_map_map] at hh
    exact hh
  have hPSDm : (tridiag A g (m + 1) + τ • 1).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact shifted_tridiag_isHermitian A g (m + 1) τ
    · intro v
      have hh := hPSD (basisEmbedding A g hm.le (WithLp.toLp 2 v))
      rw [inner_shifted_apply_basisEmbedding A g hA hm.le] at hh
      rw [star_trivial, ← EuclideanSpace.inner_toLp_toLp_real, real_inner_comm]
      exact hh
  refine ⟨y, ?_, hsolve, ?_⟩
  · change ‖B.repr (K.orthogonalProjectionOnto x)‖ ≤ ‖x‖
    rw [B.repr.norm_map]
    exact K.norm_orthogonalProjectionOnto_apply_le x
  · apply Matrix.posDef_of_tridiagonal_solve (shifted_tridiag A g (m + 1) τ)
      (shifted_tridiag_offdiag_ne A g hm.le τ) hPSDm
      (neg_ne_zero.mpr (norm_ne_zero_iff.mpr hg)) y
    simpa only [neg_smul] using hsolve
end Lanczos
