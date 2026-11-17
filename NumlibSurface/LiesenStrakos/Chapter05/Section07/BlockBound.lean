/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.GMRES.BlockBound
import Numlib.LinearAlgebra.Matrix.Jordan

/-!
# Liesen and Strakoš, §5.7.2: The Jordan-block GMRES bound

The first assertion of Theorem 5.7.4 estimates the relative residual using the
individual Jordan blocks and the condition number of the Jordan basis.
-/

open Krylov Matrix Polynomial
open scoped Matrix.Norms.L2Operator

namespace LiesenStrakos.Chapter05

/-- **Theorem 5.7.4** of [liesen2013krylov], Jordan-block bound (5.7.10).
For a Jordan decomposition $A=Y\operatorname{diag}(J_i)Y^{-1}$ with
$r_0=b-Ax_0\ne0$, the step-$n$ GMRES iterate satisfies
$$\frac{\|b-Ax_n\|}{\|r_0\|}\le
\kappa_2(Y)\inf_{\deg p\le n,\ p(0)=1}\max_i\|p(J_i)\|_2.$$ -/
theorem theorem_5_7_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (μ : ι → ℂ)
    {A Y : Matrix (Σ i, Fin (m i)) (Σ i, Fin (m i)) ℂ}
    (hY : IsUnit Y) (hA : A = Y * jordanForm m μ * Y⁻¹)
    {b x₀ xₙ : EuclideanSpace ℂ (Σ i, Fin (m i))} {n : ℕ}
    (hr : b - toEuclideanLin A x₀ ≠ 0)
    (hx : IsMinResidualIterate (toEuclideanLin A) b x₀ n xₙ) :
    ‖b - toEuclideanLin A xₙ‖ / ‖b - toEuclideanLin A x₀‖ ≤
      Matrix.condNumberLp 2 Y *
        (⨅ p : {p : ℂ[X] // p.degree ≤ n ∧ p.eval 0 = 1},
          ⨆ i, ‖aeval (jordanBlock (m i) (μ i)) p.1‖) := by
  rw [Matrix.condNumberLp, Matrix.lpOpNorm_two, Matrix.lpOpNorm_two]
  exact hx.norm_residual_le_iInf_conj_blockDiagonal hY hA hr

end LiesenStrakos.Chapter05
