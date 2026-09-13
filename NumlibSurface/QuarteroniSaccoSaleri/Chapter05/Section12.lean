import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Quarteroni–Sacco–Saleri §5.12: applications

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §5.12.

The section works two engineering eigenvalue problems. The buckling of a beam (§5.12.1) reduces,
after a centred finite difference discretization, to the smallest eigenvalue of the tridiagonal
symmetric positive definite matrix `A = tridiag_n(-1, 2, -1)`, whose eigenvalues (5.69) are the
discrete sine spectrum of `Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz`; that is the section's
one numbered result. The free vibration of a bridge (§5.12.2) is a generalized eigenvalue problem
(5.70) with a diagonal positive mass matrix, reduced to a standard one by the change of variable
`z = M^{1/2} x`; it states no numbered result, and its numerical experiments are not nodes.

## Main results

* `equation_5_69` — the eigenvalues of `tridiag_n(-1, 2, -1)` are `λ_j = 2 (1 - cos (j θ))`,
  `θ = π/(n + 1)`, `j = 1, …, n`, and nothing else.

## Conventions

The book's matrix `tridiag_n(-1, 2, -1)` is `Matrix.symmTridiagonalToeplitz n (-1) 2`, read as
the operator `Matrix.toEuclideanLin` on `ℝⁿ`; its eigenvalues are stated through
`Module.End.HasEigenvalue`. The book's index `j = 1, …, n` is `j : Fin n` shifted by one, so `j θ`
reads `(j + 1) θ`.
-/

open scoped Real

namespace QuarteroniSaccoSaleri.Chapter05

/-- **(5.69).** Letting `θ = π/(n + 1)`, the eigenvalues of the matrix
`A = tridiag_n(-1, 2, -1) ∈ ℝⁿˣⁿ` of the buckling problem (§5.12.1) are

`λ_j = 2 (1 - cos (j θ))`, `j = 1, …, n`

(here `j : Fin n`, so the book's `j` is `j + 1`). The book refers to Exercise 3 of Chapter 4 for
the proof; the statement is the discrete sine spectrum of the backbone,
`Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff`, which also says that these are *all* the
eigenvalues. The critical load is then `P_cr^h = λ_min E J / h²` with `λ_min = 2 (1 - cos θ)`. -/
theorem equation_5_69 (n : ℕ) (μ : ℝ) :
    Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (Matrix.symmTridiagonalToeplitz n (-1) 2)) μ ↔
      ∃ j : Fin n, μ = 2 * (1 - Real.cos ((((j : ℕ) : ℝ) + 1) * (π / ((n : ℝ) + 1)))) := by
  rw [Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff]
  refine exists_congr fun j => ?_
  rw [mul_div_assoc]
  constructor <;> intro h <;> linarith

end QuarteroniSaccoSaleri.Chapter05
