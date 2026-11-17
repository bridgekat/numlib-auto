/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.GMRES.Sharpness

/-!
# Liesen and Strakoš, §5.7.2: Sharpness of the normal GMRES bound

For each fixed step, there is an initial approximation for which the
relative GMRES residual equals the spectral polynomial minimax value.
-/

open Krylov Polynomial

namespace LiesenStrakos.Chapter05

/-- **Theorem 5.7.4** of [liesen2013krylov], sharpness of (5.7.11).
Let $A$ be invertible and unitarily diagonalizable, with an orthonormal
eigenbasis and eigenvalues $\mu_i$. At each fixed step $n$, some initial
approximation $x_0$ with nonzero residual attains the normal-matrix bound.
This includes the steps through one less than the grade in the source. -/
theorem theorem_5_7_4_normal_sharp
    {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Fintype ι] [Nonempty ι] {A : E →ₗ[𝕜] E}
    (basis : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜)
    (hμ : ∀ i, A (basis i) = μ i • basis i) (hA : Function.Surjective A) (b : E) (n : ℕ) :
    ∃ x₀ xₙ : E, b - A x₀ ≠ 0 ∧ IsMinResidualIterate A b x₀ n xₙ ∧
      ‖b - A xₙ‖ / ‖b - A x₀‖ =
        ⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1}, ⨆ i, ‖p.1.eval (μ i)‖ :=
  exists_norm_residual_eq_spectralMinimax basis μ hμ hA b n

end LiesenStrakos.Chapter05
