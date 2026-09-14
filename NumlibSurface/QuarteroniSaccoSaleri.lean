import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Basics
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section07
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section08
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section09
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section10
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section11
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section12
import NumlibSurface.QuarteroniSaccoSaleri.Chapter02.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter02.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter02.Section05
import NumlibSurface.QuarteroniSaccoSaleri.Chapter02.Section06
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section06
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section03
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section05
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section06
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section07
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section08
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section09
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section10
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section11
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section12
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section13
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Basics
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section03
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section05
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section06
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section03
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section05
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section06
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section07
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section08
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section03
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section05
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section06
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section07
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section09
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section03
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section05
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section07
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section08
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section03
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section05
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section06
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section07
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section08
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section09
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section10
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section12
import NumlibSurface.QuarteroniSaccoSaleri.Chapter12.Section01

/-!
# Quarteroni, Sacco and Saleri, *Numerical Mathematics*

The surface library for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical
Mathematics* [quarteroni2000numerical]: one module per section of the book that states a numbered
result, in `NumlibSurface/QuarteroniSaccoSaleri/ChapterNN/SectionMM.lean` (`ChapterNN/Basics.lean`
where a run of definition-only sections is merged). Each module states the book's results in the
book's own terms — real matrices `Matrix (Fin n) (Fin n) ℝ`, vectors of `ℝⁿ`, functions on an
interval `[a, b]`, every method written as the book writes it — and proves them by specializing the
general backbone under `Numlib/`. Almost nothing is proved here that is not proved there: the
surface exists to test the backbone against a published account of the subject, and to give a
reader of the book a Lean name for every result in it. This module imports the section modules and
adds nothing of its own.

Plan and per-result book alignment: the groups under `plans/NumlibSurface/QuarteroniSaccoSaleri/`,
one file per section, where every numbered result of the book is a node carrying its source and,
when it is not formalized, the reason.

## Naming

A declaration is named for the result it states, so the name is the index: `theorem_3_4` is
Theorem 3.4, `property_1_13` is Property 1.13, `definition_2_1`, `lemma_11_2`, `corollary_4_1`,
`proposition_2_1`, `example_2_1` and `remark_1_1` likewise, `equation_3_51` is (3.51) and
`exercise_3_5` is Exercise 5 of chapter 3. Where one numbered result needs several declarations —
its separate clauses, or the two directions of an equivalence — a trailing word tells them apart
(`theorem_4_1_mp`, `property_1_18_minors`). Objects the book names but does not number keep a
descriptive lowerCamelCase name, and each such definition carries an equivalence lemma to its
backbone counterpart; those lemmas are the load-bearing part of the library.

Declarations live in `QuarteroniSaccoSaleri.ChapterNN` for the chapter. Within the library the
dependencies run forwards in the direction of the chapter numbering: where an earlier chapter has
already restated something, a later chapter uses that restatement rather than reaching past it to
the backbone or Mathlib original.

## The outline

| § | module | subject |
|---|---|---|
| **1** | | *Foundations of Matrix Analysis* |
| 1.1–1.6 | `Chapter01.Basics` | Vector spaces, matrices, trace, determinant, rank, special shapes |
| 1.7 | `Chapter01.Section07` | Eigenvalues and eigenvectors, the spectral radius |
| 1.8 | `Chapter01.Section08` | Similarity transformations, Schur and Jordan forms |
| 1.9 | `Chapter01.Section09` | The singular value decomposition |
| 1.10 | `Chapter01.Section10` | Scalar products and vector norms |
| 1.11 | `Chapter01.Section11` | Matrix norms, the spectral radius and consistent norms |
| 1.12 | `Chapter01.Section12` | Positive definite, diagonally dominant and M-matrices |
| **2** | | *Principles of Numerical Mathematics* |
| 2.1 | `Chapter02.Section01` | Well-posedness and the condition number of a problem |
| 2.2 | `Chapter02.Section02` | Consistency, stability and convergence of a numerical method |
| 2.5 | `Chapter02.Section05` | Machine representation of numbers, rounding, machine arithmetic |
| 2.6 | `Chapter02.Section06` | Exercises |
| **3** | | *Direct Methods for the Solution of Linear Systems* |
| 3.1 | `Chapter03.Section01` | Stability of linear systems: condition number, perturbations |
| 3.2 | `Chapter03.Section02` | Triangular systems and forward/backward substitution |
| 3.3 | `Chapter03.Section03` | Gaussian elimination and the LU factorization; Theorem 3.4 |
| 3.4 | `Chapter03.Section04` | `LDMᵀ`, `LDLᵀ`, Cholesky, QR and Gram–Schmidt |
| 3.5 | `Chapter03.Section05` | Pivoting |
| 3.6 | `Chapter03.Section06` | Computing the inverse |
| 3.7 | `Chapter03.Section07` | Banded and tridiagonal systems, the Thomas algorithm |
| 3.8 | `Chapter03.Section08` | Block systems and block LU |
| 3.9 | `Chapter03.Section09` | Sparse matrices: fill-in, envelopes and reorderings |
| 3.10 | `Chapter03.Section10` | Accuracy of GEM: growth factor and backward error |
| 3.11 | `Chapter03.Section11` | Estimating the condition number |
| 3.12 | `Chapter03.Section12` | Scaling and iterative refinement |
| 3.13 | `Chapter03.Section13` | Underdetermined and least-squares systems |
| 3.14 | `Chapter03.Section14` | Applications |
| 3.15 | `Chapter03.Section15` | Exercises |
| **4** | | *Iterative Methods for Solving Linear Systems* |
| 4.1 | `Chapter04.Section01` | Consistency, convergence and convergence factors |
| 4.2 | `Chapter04.Section02` | Jacobi, Gauss–Seidel, SOR, SSOR and their convergence theory |
| 4.3 | `Chapter04.Section03` | Richardson, gradient and conjugate gradient methods, ADI |
| 4.4 | `Chapter04.Section04` | Krylov methods: Arnoldi, FOM, GMRES, Lanczos |
| 4.5 | `Chapter04.Section05` | The Lanczos method for unsymmetric systems |
| 4.6 | `Chapter04.Section06` | Stopping criteria |
| **5** | | *Approximation of Eigenvalues and Eigenvectors* |
| 5.1 | `Chapter05.Section01` | Localization: Hirsch, the Gershgorin theorems |
| 5.2 | `Chapter05.Section02` | Conditioning of the eigenproblem: Bauer–Fike, perturbations |
| 5.3 | `Chapter05.Section03` | The power method and inverse iteration |
| 5.4–5.5 | `Chapter05.Section04`, `Section05` | The QR iteration |
| 5.6 | `Chapter05.Section06` | Hessenberg form, Householder and Givens transformations |
| 5.7 | `Chapter05.Section07` | Shifted QR |
| 5.8 | `Chapter05.Section08` | Eigenvectors and the SVD |
| 5.9 | `Chapter05.Section09` | The generalized eigenvalue problem |
| 5.10 | `Chapter05.Section10` | Symmetric matrices: Jacobi, Sturm sequences, Givens' bisection |
| 5.11 | `Chapter05.Section11` | The Lanczos method |
| 5.12–5.13 | `Chapter05.Section12`, `Section13` | Applications and exercises |
| **6** | | *Rootfinding for Nonlinear Equations* |
| 6 | `Chapter06.Basics` | Order of convergence |
| 6.1 | `Chapter06.Section01` | Conditioning of a nonlinear equation, multiple roots |
| 6.2 | `Chapter06.Section02` | Bisection, chord, secant, regula falsi, Newton |
| 6.3 | `Chapter06.Section03` | Fixed-point iterations, Ostrowski's theorem |
| 6.4 | `Chapter06.Section04` | Zeros of polynomials: Horner, deflation, Descartes, Cauchy's bound |
| 6.5 | `Chapter06.Section05` | Stopping criteria |
| 6.6 | `Chapter06.Section06` | Aitken's acceleration, Steffensen, multiple roots |
| **7** | | *Nonlinear Systems and Numerical Optimization* |
| 7.1 | `Chapter07.Section01` | Newton's method in `ℝⁿ`, inexact and quasi-Newton variants |
| 7.2 | `Chapter07.Section02` | Unconstrained optimization: descent, line search, BFGS, CG |
| 7.3 | `Chapter07.Section03` | Constrained optimization: Lagrange multipliers, Kuhn–Tucker |
| 7.4 | `Chapter07.Section04` | Applications |
| **8** | | *Polynomial Interpolation* |
| 8.1 | `Chapter08.Section01` | Lagrange interpolation, error, Lebesgue constant |
| 8.2 | `Chapter08.Section02` | The Newton form and divided differences |
| 8.3 | `Chapter08.Section03` | Piecewise Lagrange interpolation |
| 8.4 | `Chapter08.Section04` | Hermite–Birkhoff interpolation |
| 8.5 | `Chapter08.Section05` | The two-dimensional case |
| 8.6 | `Chapter08.Section06` | Splines |
| 8.7 | `Chapter08.Section07` | Parametric splines, Bézier curves, B-splines |
| 8.8 | `Chapter08.Section08` | Applications |
| **9** | | *Numerical Integration* |
| 9.1 | `Chapter09.Section01` | Quadrature formulae |
| 9.2 | `Chapter09.Section02` | Interpolatory quadratures: midpoint, trapezoidal, Simpson |
| 9.3 | `Chapter09.Section03` | Newton–Cotes formulae |
| 9.4 | `Chapter09.Section04` | Composite Newton–Cotes formulae |
| 9.5 | `Chapter09.Section05` | Hermite quadrature |
| 9.6 | `Chapter09.Section06` | Richardson extrapolation and Romberg integration |
| 9.7 | `Chapter09.Section07` | Automatic integration |
| 9.8 | `Chapter09.Section08` | Singular integrals |
| 9.9 | `Chapter09.Section09` | Multidimensional integration, Monte Carlo |
| **10** | | *Orthogonal Polynomials in Approximation Theory* |
| 10.1 | `Chapter10.Section01` | Generalized Fourier series, orthogonal polynomials |
| 10.2 | `Chapter10.Section02` | Gaussian integration and interpolation |
| 10.3 | `Chapter10.Section03` | Chebyshev integration and interpolation |
| 10.4 | `Chapter10.Section04` | Legendre integration and interpolation |
| 10.5 | `Chapter10.Section05` | Gaussian integration over unbounded intervals |
| 10.7 | `Chapter10.Section07` | Least-squares approximation |
| 10.8 | `Chapter10.Section08` | The polynomial of best approximation |
| 10.9 | `Chapter10.Section09` | Fourier trigonometric polynomials and the DFT |
| 10.10 | `Chapter10.Section10` | Approximation of derivatives |
| 10.11 | `Chapter10.Section11` | Fourier, Laplace and Z transforms |
| 10.12 | `Chapter10.Section12` | The wavelet transform |
| **11** | | *Numerical Solution of Ordinary Differential Equations* |
| 11.1 | `Chapter11.Section01` | The Cauchy problem, Liapunov stability, Gronwall's lemma |
| 11.2–11.3 | `Chapter11.Section02`, `Section03` | One-step methods and their analysis |
| 11.4 | `Chapter11.Section04` | Linear difference equations |
| 11.5–11.6 | `Chapter11.Section05`, `Section06` | Multistep methods and their analysis |
| 11.7 | `Chapter11.Section07` | Predictor–corrector methods |
| 11.8 | `Chapter11.Section08` | Runge–Kutta methods |
| 11.9–11.10 | `Chapter11.Section09`, `Section10` | Systems of ODEs, stiff problems |
| 11.12 | `Chapter11.Section12` | Exercises |
| **12** | | *Two-Point Boundary Value Problems* |
| 12.1 | `Chapter12.Section01` | The model problem |
| 12.2 | `Chapter12.Section02` | Finite differences: stability, maximum principle, convergence |
| 12.3 | `Chapter12.Section03` | Spectral collocation |
| 12.4 | `Chapter12.Section04` | The Galerkin method and finite elements |
| 12.5 | `Chapter12.Section05` | Advection–diffusion equations and stabilization |
| 12.6 | `Chapter12.Section06` | The two-dimensional case |
| **13** | | *Parabolic and Hyperbolic Initial Boundary Value Problems* |
| 13.1 | `Chapter13.Section01` | The heat equation |
| 13.2 | `Chapter13.Section02` | Finite differences for the heat equation |
| 13.3 | `Chapter13.Section03` | Finite elements for the heat equation, the θ-method |
| 13.4 | `Chapter13.Section04` | Space–time finite elements |
| 13.5 | `Chapter13.Section05` | The scalar transport problem |
| 13.6 | `Chapter13.Section06` | Systems of linear hyperbolic equations |
| 13.7 | `Chapter13.Section07` | Finite differences for hyperbolic equations |
| 13.8 | `Chapter13.Section08` | Analysis: consistency, von Neumann stability, CFL |
| 13.9 | `Chapter13.Section09` | Dissipation and dispersion |
| 13.10 | `Chapter13.Section10` | Finite elements for hyperbolic equations |
-/
