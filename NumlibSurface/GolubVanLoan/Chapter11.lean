import NumlibSurface.GolubVanLoan.Chapter11.Section01
import NumlibSurface.GolubVanLoan.Chapter11.Section02
import NumlibSurface.GolubVanLoan.Chapter11.Section03
import NumlibSurface.GolubVanLoan.Chapter11.Section04
import NumlibSurface.GolubVanLoan.Chapter11.Section05
import NumlibSurface.GolubVanLoan.Chapter11.Section06

/-!
# Golub–Van Loan, Chapter 11: Large Sparse Linear System Problems

The surface of Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition,
Chapter 11: §11.1 direct methods (storage, ordering, fill), §11.2 the classical iterations, §11.3
conjugate gradients, §11.4 other Krylov methods, §11.5 preconditioning, §11.6 multigrid. Namespace
`GolubVanLoan.Chapter11`, one module per section; this module imports them and adds nothing.

## Conventions (all sections)

* Real matrices `Matrix (Fin n) (Fin n) ℝ` and vectors `Fin n → ℝ`, 0-based: the book's `x_i`,
  `a_ij` (`i, j = 1:n`) are `x (i−1)`, `A (i−1) (j−1)`; iterate superscripts and subscripts `x⁽ᵏ⁾`,
  `x_k` keep their `k ≥ 0`. Krylov statements are about `T := Matrix.toEuclideanLin A` on
  `EuclideanSpace ℝ (Fin n)`, vectors transported by `WithLp.toLp 2`.
* The book's `L_A, D_A, U_A` are `strictLower A`, `diagPart A`, `strictUpper A` (Saad's `E = −L_A`,
  `F = −U_A`, used by the book itself in §11.5.3); splittings are `Stationary.Splitting`, and the
  spectral radius `ρ(G)` of a real matrix is `Matrix.complexSpectralRadius G` (complexification).
* Lanczos and CG indices: the book's `q_j, α_j, β_j` (`j ≥ 1`) are the backbone's
  `Arnoldi.vec T r₀ (j−1)`, `Lanczos.alpha T r₀ (j−1)`, `Lanczos.beta T r₀ (j−1)`; the book's
  Hestenes–Stiefel `p_k, μ_k` (`k ≥ 1`) are `(CG.iterate (k−1)).p` and `CG.alpha` at `k − 1`.
  `κ₂(A)` is `NormedRing.condNumber A` under `Matrix.Norms.L2Operator`; `φ(x) = ½xᵀAx − xᵀb` is
  `energyFunctional`, `‖v‖_A` is `energyNorm`.
* Cholesky: the book's lower `G` with `A = GGᵀ` is `Hᵀ` for the backbone's `Matrix.IsCholesky A H`
  (`H` upper, `Hᴴ H = A`).

## Algorithms

Every numbered algorithm — Algorithms 11.3.1, 11.3.2, 11.3.3, 11.4.2, 11.5.1, 11.5.2 — and every
algorithm written out as a numbered display or figure with a claim attached is a monadic program
over a rounding hook `rnd : ℝ → M ℝ` in the book's operation order, built from Chapter 1's
Algorithms 1.1.1–1.1.3 (the conventions 1–14 of `NumlibSurface/GolubVanLoan`). `while` loops take
`fuel : ℕ` as the last explicit argument and carry a `done` flag; solves with a preconditioner or a
small matrix are routine arguments whose exact meaning is the inverse. Programs written out as
displays are content-named (`sparseGaxpy`, `jacobiSweep`, `gaussSeidelSweep`, `sorSweep`,
`practicalCG`, `concusGolubOLearyPCG`, `twoGridCycle`, …) and their exact-semantics theorems keep
the display number. Specifications are exact-arithmetic identifications with the backbone
recurrences (`CG.iterate`, `Krylov.PCG.iterate`, `Krylov.CGNR.iterate`, `BCG.iterate`, the sweeps
of `Numlib/Stationary/Sweep`, the Arnoldi/Givens layer of `Numlib/Krylov/Hessenberg`). The book
analyses no rounding error in this chapter (§11.3.8 says only that orthogonality is lost). There is
no Algorithm 11.4.1 in the source.

Exceptions: the ADI step (11.2.16) is the exact map `adiStep` (two `mulVecStep`s of the two
splittings) with exact semantics `adi_error_eq`, not a rounded program; the smoother of the
two-grid cycle (11.6.16) is a routine argument (exact meaning: one weighted Jacobi step), since
§11.2 has no weighted-Jacobi program to call; the tridiagonal solve of (11.3.14) is chapter 4's
Algorithm 4.3.6; and the first Lanczos/Arnoldi normalization of (11.3.14) and Algorithm 11.4.2
rounds `q₁ = r₀/β₀` once more than the book (chapter 10's loop divides again by its `β₀ = 1`).

## Correspondence

* §11.1 → `Numlib/LinearAlgebra/Sparse/{Pattern,Reordering,Fill}`,
  `Numlib/LinearAlgebra/Matrix/{Cholesky,SchurComplement,LU/Elimination}`.
* §11.2 → `Numlib/Stationary/*`, `Numlib/LinearAlgebra/Matrix/{TridiagonalToeplitz,KroneckerSum,
  Complexify}`.
* §11.3 → `Numlib/Krylov/{Iterate,CG,Lanczos,Arnoldi,Hessenberg,Singular,NormalEquations,
  Convergence/CG}`, `Numlib/Projection/OneDimensional`, `Numlib/Analysis/InnerProductSpace/Energy`.
* §11.4 → `Numlib/Krylov/{Iterate,Hessenberg,BiLanczos,QuasiMinRes,NormalEquations,Monotonicity,
  Bidiagonalization,TransposeFree}`.
* §11.5 → `Numlib/Krylov/Preconditioned`, `Numlib/Preconditioner/{ILU,Polynomial,
  ApproximateInverse}`, `Numlib/LinearAlgebra/Matrix/MMatrix`, `Numlib/DomainDecomposition/*`.
* §11.6 → the sine eigenbasis of `Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz`,
  `Numlib/Multigrid/{Basic,ModelProblem}`.

## Not formalized (by class)

* Operation counts, flop and memory estimates and complexity claims.
* Numerical examples and illustrations (the 9×9 matrix (11.1.5) and its profiles, the e-tree
  example, the `n = 7` matrices (11.6.13)); Problems; Notes and References.
* Heuristics without a precise statement: the sparse "challenges", fill-minimizing orderings,
  Markowitz and threshold pivoting, the elimination tree, "the more dominant the diagonal the
  faster", the method advice of §11.4, Criteria 1–2 of §11.5.1, the Toeplitz/circulant
  preconditioners of §11.5.4, drop-tolerance incomplete Cholesky and `ILU(ℓ)`, the HSS
  preconditioner, §11.6.5.
* "Assuming no numerical cancellation" statements (the nonzero direction of Facts 1–2 and the
  literal claim of §11.1.9; the exact halves are formalized, and the literal §11.1.9 claim has a
  counterexample).
* Claims quoted but not proved in the text: Björck's accuracy of the seminormal equations, the
  `n`-independence of the multigrid rate, "CGS typically outperforms BiCG", reverse Cuthill–McKee.
* The PDE (11.6.1), the L-shaped domain of §11.5.11 and all "discretizes" claims; the V-cycle and
  full multigrid; storage formats as such.

## The outline

| § | module | subject |
|---|---|---|
| 11.1 | `Chapter11.Section01` | Direct methods |
| 11.2 | `Chapter11.Section02` | The classical iterations |
| 11.3 | `Chapter11.Section03` | The conjugate gradient method |
| 11.4 | `Chapter11.Section04` | Other Krylov methods |
| 11.5 | `Chapter11.Section05` | Preconditioning |
| 11.6 | `Chapter11.Section06` | The multigrid framework |
-/
