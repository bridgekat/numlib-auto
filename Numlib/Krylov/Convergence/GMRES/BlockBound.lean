/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Iterate
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.Aeval
import Numlib.LinearAlgebra.Matrix.WeightedAdjoint

/-!
# The block-diagonal GMRES convergence bound

A block-diagonal similarity bounds the relative GMRES residual by the
spectral condition number of the similarity times the block minimax
polynomial value. The blocks may have different sizes.
-/

open scoped Matrix.Norms.L2Operator
open Matrix Polynomial

namespace Krylov

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → Type*}
variable [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- Suppose $A=Y\operatorname{diag}(J_i)Y^{-1}$ with nonsingular $Y$. For a
nonzero initial residual $r_0$, the relative GMRES residual at step $n$
is bounded by the spectral condition number of $Y$ times the infimum of
$\max_i\|p(J_i)\|_2$ over $\deg p\le n$ and $p(0)=1$. -/
theorem IsMinResidualIterate.norm_residual_le_iInf_conj_blockDiagonal
    {J : ∀ i, Matrix (m i) (m i) 𝕜} {A Y : Matrix (Σ i, m i) (Σ i, m i) 𝕜}
    (hY : IsUnit Y) (hA : A = Y * blockDiagonal' J * Y⁻¹)
    {b x₀ x : EuclideanSpace 𝕜 (Σ i, m i)} {n : ℕ}
    (hr : b - toEuclideanLin A x₀ ≠ 0)
    (hx : IsMinResidualIterate (toEuclideanLin A) b x₀ n x) :
    ‖b - toEuclideanLin A x‖ / ‖b - toEuclideanLin A x₀‖ ≤
      ‖Y‖ * ‖Y⁻¹‖ *
        (⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1}, ⨆ i, ‖aeval (J i) p.1‖) := by
  have : Nonempty {p : 𝕜[X] // p.degree ≤ (n : WithBot ℕ) ∧ p.eval 0 = 1} :=
    ⟨⟨1, by simp, by simp⟩⟩
  rw [Real.mul_iInf_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  refine le_ciInf fun p => ?_
  let e := (similarityAlgEquiv Y hY).symm
  have hconj : A = e (blockDiagonal' J) := by
    rw [show e (blockDiagonal' J) = Y * blockDiagonal' J * Y⁻¹ from
      similarityAlgEquiv_symm_apply Y hY _]
    exact hA
  have hpol : aeval A p.1 = Y * blockDiagonal' (fun i => aeval (J i) p.1) * Y⁻¹ := by
    rw [hconj, aeval_algHom_apply e (blockDiagonal' J) p.1, aeval_blockDiagonal']
    exact similarityAlgEquiv_symm_apply Y hY _
  have hB : ‖aeval A p.1‖ ≤ ‖Y‖ * ‖Y⁻¹‖ * (⨆ i, ‖aeval (J i) p.1‖) := by
    rw [hpol, ← Matrix.l2_opNorm_blockDiagonal']
    calc
      _ ≤ ‖Y * blockDiagonal' (fun i => aeval (J i) p.1)‖ * ‖Y⁻¹‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Y‖ * ‖blockDiagonal' (fun i => aeval (J i) p.1)‖) * ‖Y⁻¹‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = _ := by ac_rfl
  let r := b - toEuclideanLin A x₀
  have hres := hx.norm_residual_le_norm_aeval p.1 p.2.1 p.2.2
  rw [← Matrix.toEuclideanLin_aeval, Matrix.toEuclideanLin_apply] at hres
  have hh := Matrix.l2_opNorm_mulVec (aeval A p.1) r
  exact (div_le_iff₀ (norm_pos_iff.mpr hr)).2
    (hres.trans (hh.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))))

end Krylov
