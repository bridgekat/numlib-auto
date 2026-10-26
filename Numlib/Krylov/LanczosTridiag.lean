import Numlib.Krylov.Lanczos
import Numlib.LinearAlgebra.Matrix.TridiagonalLDL

/-!
# The Lanczos tridiagonal matrix as a symmetric tridiagonal matrix

The Lanczos matrix `T_m = Lanczos.tridiag A b m` (diagonal `α_j`, off-diagonal `β_j` coupling rows
`j` and `j + 1`) is the symmetric tridiagonal matrix `Matrix.symTridiag α γ m` with the shifted
off-diagonal sequence `γ i = β_{i-1}` (`γ i` couples rows `i - 1` and `i`). Through this bridge the
`LDLᵀ` factorization, the pivot test for positive definiteness and the tridiagonal solver of
`Numlib/LinearAlgebra/Matrix/TridiagonalLDL` apply to the shifted Lanczos systems
`(T_k + λ I) x = b` of Cartis–Gould–Toint §10.2.1.
-/

namespace Lanczos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Lanczos matrix is `Matrix.symTridiag` of the Lanczos coefficients, with off-diagonal
`γ i = β_{i-1}`. -/
theorem tridiag_eq_symTridiag (A : E →ₗ[𝕜] E) (b : E) (m : ℕ) :
    tridiag A b m = Matrix.symTridiag (alpha A b) (fun i => beta A b (i - 1)) m := by
  ext i j
  rw [tridiag_apply, Matrix.symTridiag_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

end Lanczos
