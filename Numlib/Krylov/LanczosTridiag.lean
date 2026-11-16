/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Lanczos
import Numlib.LinearAlgebra.Matrix.TridiagonalLDL

/-!
# The Lanczos matrix as a symmetric tridiagonal matrix

The Lanczos matrix $T_m$ (`Lanczos.tridiag`) has the diagonal $\alpha_0, \dots, \alpha_{m-1}$, and
the coefficient $\beta_j$ couples rows $j$ and $j + 1$. This file identifies $T_m$ with the
symmetric tridiagonal matrix `Matrix.symTridiag` $\alpha$ $\gamma$ $m$, whose off-diagonal entry
$\gamma_i$ couples rows $i - 1$ and $i$, for the shifted sequence $\gamma_i = \beta_{i-1}$. Through
this identification the $LDL^T$ factorization, the pivot test for positive definiteness and the
tridiagonal solver of `Numlib.LinearAlgebra.Matrix.TridiagonalLDL` apply to the shifted Lanczos
systems $(T_k + \lambda I) x = b$ of [cartis2022evaluation], §10.2.1.

## Main results

* `Lanczos.tridiag_eq_symTridiag`: $T_m$ is `Matrix.symTridiag` of the Lanczos coefficients with the
  off-diagonal sequence $\gamma_i = \beta_{i-1}$.
-/

namespace Lanczos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $A$ be a linear operator on an inner product space $E$ over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, let $b \in E$ and $m \in \mathbb{N}$. The Lanczos matrix $T_m$ of $(A, b)$ is the
symmetric tridiagonal matrix with diagonal $\alpha_0, \dots, \alpha_{m-1}$ and off-diagonal
entries $\gamma_i = \beta_{i-1}$ at the positions $(i, i - 1)$ and $(i - 1, i)$, for
$1 \le i < m$.

The identity holds for every operator $A$; symmetry is not needed. The right-hand side is
`Matrix.symTridiag (Lanczos.alpha A b) (fun i => Lanczos.beta A b (i - 1)) m`. At $i = 0$ the
natural-number subtraction gives $\gamma_0 = \beta_0$, but `Matrix.symTridiag` does not use
$\gamma_0$. -/
theorem tridiag_eq_symTridiag (A : E →ₗ[𝕜] E) (b : E) (m : ℕ) :
    tridiag A b m = Matrix.symTridiag (alpha A b) (fun i => beta A b (i - 1)) m := by
  ext i j
  rw [tridiag_apply, Matrix.symTridiag_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

end Lanczos
