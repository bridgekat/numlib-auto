import NumlibSurface.GolubVanLoan.Chapter10.Section01
import NumlibSurface.GolubVanLoan.Chapter10.Section02
import NumlibSurface.GolubVanLoan.Chapter10.Section03
import NumlibSurface.GolubVanLoan.Chapter10.Section04
import NumlibSurface.GolubVanLoan.Chapter10.Section05
import NumlibSurface.GolubVanLoan.Chapter10.Section06

/-!
# Golub–Van Loan, Chapter 10: large sparse eigenvalue problems

The surface of Chapter 10 of Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th
edition: the symmetric Lanczos process and its convergence (§10.1), Lanczos and Gauss quadrature
for `uᵀ f(A) u` (§10.2), practical Lanczos — the two-vector implementation, reorthogonalization,
block Lanczos (§10.3), Golub–Kahan and Paige–Saunders bidiagonalization and a CUR sketch (§10.4),
Arnoldi, implicit and Krylov–Schur restarting, unsymmetric Lanczos (§10.5), and the
approximate-Newton family JOCC, Davidson, Jacobi–Davidson, trace-min (§10.6). This module imports
the section modules and adds nothing of its own.

## Correspondence

Most of the mathematics is backbone: `Numlib/Krylov/{Subspace, Arnoldi, Lanczos, Block, BiLanczos,
Hessenberg, OrthogonalPolynomials}` (Krylov subspaces, the Arnoldi and Lanczos vectors as
Gram–Schmidt of the Krylov sequence, `T_m`, the Lanczos polynomials, the spectral measure),
`Numlib/Eigen/{RayleighRitz, KrylovEigen, Perturbation, MinMax}` (Ritz pairs, Kaniel–Paige–Saad,
the residual bound, Courant–Fischer), the quadrature layer `Numlib/Approximation/{Quadrature,
GaussLobatto, OrthogonalPolynomial}`, and the modules planned for this chapter:
`Numlib/Krylov/Decomposition` with `Numlib/LinearAlgebra/Matrix/KrylovDecomposition` (the matrix
reading `A Q_k = Q_k H_k + r_k e_kᵀ` and Arnoldi decompositions), `Numlib/Krylov/Bidiagonalization`
(Golub–Kahan, Paige–Saunders as its dual, the Jordan–Wielandt connection),
`Numlib/Krylov/Quadrature` (`uᵀ f(A) u` as an integral, the Gauss and Gauss–Radau rules from
Lanczos), `Numlib/Eigen/ImplicitRestart` (shifted-QR chains, Theorem 10.5.1, implicit restart and
Krylov–Schur) and `Numlib/Eigen/JacobiDavidson` (the eigenproblem as a nonlinear system, the
bordered Newton correction, the projected Jacobi–Davidson equation).

## Conventions of the chapter's surface files

* Scalars and shapes: the book is real. `A : Matrix (Fin n) (Fin n) ℝ` (`Fin m`, `Fin n` for the
  rectangular `A` of §10.4), acting on `EuclideanSpace ℝ (Fin n)` through `Matrix.toEuclideanLin`.
* Indices are `0`-based: the book's `q_{j+1}`, `α_{j+1}`, `β_{j+1}` are
  `Arnoldi.vec (toEuclideanLin A) q₁ j`, `Lanczos.alpha _ q₁ j`, `Lanczos.beta _ q₁ j`; `T_k` is
  `Lanczos.tridiag _ q₁ k`, `Q_k` is `Arnoldi.basisMatrix A q₁ k`, `H_k` is
  `Arnoldi.hessenbergSq _ q₁ k`, `r_k` is `(Arnoldi.w _ q₁ (k − 1)).ofLp`, `e_k` is
  `Krylov.lastVec 1 k`. The Golub–Kahan quantities are `GolubKahan.rightVec/leftVec/alpha/beta`.
* Eigenvalues `λ_1 ≥ ⋯ ≥ λ_n` of a symmetric `A` are `(hA.isSymmetric_toEuclideanLin).eigenvalues
  finrank_euclideanSpace_fin`; the Ritz values `θ_1 ≥ ⋯ ≥ θ_k` are `Lanczos.ritzValues`.
* Matrix functions `f(A)` of symmetric `A` are Mathlib's `cfc f A` (§10.2); Riemann–Stieltjes
  integrals are Lebesgue–Stieltjes integrals against `StieltjesFunction.measure`.
* Algorithms follow conventions 1–14 of `NumlibSurface/GolubVanLoan`: every numbered algorithm is
  a monadic program with a rounding hook and an exact-semantics theorem; a numbered display that
  writes out an algorithm is a content-named program (`twoVectorLanczos`, `unsymmetricLanczos`,
  `joccIteration`) whose exact-semantics theorem carries the display's number. The `while` loops
  run over `List.range fuel` with a `done` flag; inner products and matrix–vector products are
  chapter 1's Algorithms 1.1.1 and 1.1.3, saxpys its Algorithm 1.1.2. The chapter has no
  rounding-error theorem of its own (Paige's analysis is quoted), so the floating-point semantics
  is carried by the definitions only.

## Not formalized

Operation counts and storage; numerical examples and Figure 10.1.1; Notes and References;
Problems (except P10.5.2, a backbone helper); prose algorithms without a numbered display or a
claim (block Lanczos with restarting, look-ahead, the trace-min iteration); motivation and notation
displays that are not propositions ((10.1.2)–(10.1.3), (10.1.5), (10.2.1), the eigen-expansion of
(10.5.3)); the floating-point analysis of §10.3 ((10.3.2)–(10.3.3), (10.3.5)–(10.3.6) and the `≈`
estimates, quoted from Paige); the §10.3.2 application of Theorem 8.1.16 (invalid as printed); the
probabilistic CUR bound of §10.4.5; the exact-shift heuristic and the block-size trade-offs.
-/
