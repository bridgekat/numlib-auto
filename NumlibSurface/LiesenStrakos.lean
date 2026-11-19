/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.LiesenStrakos.Chapter01.Section03
import NumlibSurface.LiesenStrakos.Chapter02
import NumlibSurface.LiesenStrakos.Chapter03
import NumlibSurface.LiesenStrakos.Chapter04
import NumlibSurface.LiesenStrakos.Chapter05

set_option linter.style.longLine false in
/-!
# Liesen and Strakoš, *Krylov Subspace Methods: Principles and Analysis*

This library formalizes results from [liesen2013krylov]. The book develops Krylov solvers from
projection methods, studies their connections to moments and quadrature, characterizes short
recurrences, and analyzes convergence and the effects of rounding errors.

## Coverage

The formalizations span all five chapters. They include the projection and optimality
characterizations of Krylov methods, Gauss quadrature and the CG energy error, Arnoldi
recurrence bandwidth, Riesz projections, and convergence and backward-error results.
Proofs use the projection, Krylov, approximation and spectral theory in `Numlib`.

## Contents

| Source | Module | Subject |
|---|---|---|
| §1.3 Basic notation | `Chapter01.Section03` | energy inner products and their norms |
| Chapter 2 Krylov Subspace Methods | `Chapter02` | projection, CG, Arnoldi and Lanczos |
| Chapter 3 Matching Moments and Model Reduction View | `Chapter03` | spectral moments and Gauss quadrature |
| Chapter 4 Short Recurrences for Generating Orthogonal Krylov Subspace Bases | `Chapter04` | cyclic subspaces, Arnoldi bandwidth, Riesz projections |
| Chapter 5 Cost of Computations Using Krylov Subspace Methods | `Chapter05` | convergence and backward error |

## Conventions

* The section number appears in the module name. Theorem 2.1.2 is
  `LiesenStrakos.theorem_2_1_2`.
* A square matrix acts as a linear endomorphism on a finite-dimensional real or complex inner
  product space. A Hermitian positive definite operator is symmetric and coercive in Lean.
* Inner products in Lean are conjugate-linear in their first argument, so $(v,w)_B$ in the
  book is `LiesenStrakos.energyInnerProduct` with value $\langle w,Bv\rangle$.
* Krylov, Arnoldi and Lanczos vectors use zero-based indices.

## Deviations from the source

* **Sections 5.1 and 5.5** (reading). The backward error and stationary convergence expressions
  use total division and logarithms. The energy and iteration statements admit broader operator
  and interval hypotheses.
* **Section 5.7.3** (reading). The closed pseudospectrum agrees with the matrix definition in
  finite dimension. On infinite-dimensional spaces, an attained unit-vector residual condition
  can omit spectral points.
* **Theorem 4.5.1** (reading). The spectral criterion for a given degree includes the least
  degree of the polynomial interpolating complex conjugation.
* **Theorem 4.6.2** (reading). The full equivalence uses complex starting vectors, and the
  sufficient direction also covers real starting vectors.
* **Sections 4.1–4.2** (generalization). The descent equivalence uses the ambient error norm,
  and grade and minimal-polynomial definitions admit arbitrary scalar fields and dimensions
  where stated.
* **Theorem 3.4.11** (correction). The polynomial quotient gives the removable value when the
  smaller leading block and larger Jacobi matrix share an eigenvalue.
* **Remark 3.8.2** (correction). The three CG characterizations use complementary projections
  and the residual scaling from Theorem 3.8.1.
* **Section 3.9** (generalization). Transfer-function and moment formulas allow complex data,
  with explicit norm bounds for the series expansions.
* **Sections 3.1–3.3** (reading). Quadrature and continued fraction definitions use total
  integrals. The divided-difference and sign-change results use direct exactness and
  integrability hypotheses.
* **Sections 1.3 and 2.1–2.3** (generalization). The energy pairings, projection predicates, and
  many best approximation properties take operators on general spaces. The stabilization result
  includes grade zero.
* **Sections 2.4–2.5** (reading). Arnoldi uses zero padding, the Lanczos tridiagonal model is
  defined for general operators, and the CG recurrence uses a prescribed iteration count.
* **Equations (2.1.6) and (2.1.10)** (reading). The direct-sum predicate can be used without
  matching dimensions for the search and constraint spaces. The coordinate formula returns
  $x_0$ for a singular projected matrix. See `LiesenStrakos.ProjectionWellDefined` and
  `LiesenStrakos.projectedIterate`.
* **Section 2.2, grade and vector minimal polynomial** (generalization). The definitions
  extend to arbitrary vector spaces. An infinite-dimensional cyclic span gives grade $0$
  and minimal polynomial $0$. See `LiesenStrakos.grade` and
  `LiesenStrakos.krylovVectorMinimalPolynomial`.
* **Theorem 2.3.1** (generalization). The CG, SYMMLQ and minimal-residual characterizations
  include step zero, zero initial residual, and steps after the grade. See
  `LiesenStrakos.theorem_2_3_1_cg`,
  `LiesenStrakos.theorem_2_3_1_symmlq`,
  `LiesenStrakos.theorem_2_3_1_minres`.
* **Algorithm 2.4.4** (generalization). The recurrence takes an independent left operator
  $B$. The printed two-sided Lanczos algorithm is the case $B=A^*$. See
  `LiesenStrakos.biLanczosVector`.
* **Theorem 2.5.2** (generalization). The conforming finite-element decomposition is stated
  for a Galerkin synthesis map in an energy inner product. See `LiesenStrakos.theorem_2_5_2`.
* **Theorem 2.5.3** (generalization). The quadratic minimization result applies on any
  finite-dimensional affine Galerkin trial space with a symmetric coercive operator. See
  `LiesenStrakos.theorem_2_5_3`.
* **Theorem 3.2.8** (reading). The existence and uniqueness statement uses the rule
  predicate with nodes in $(a,b]$. Interior location and the node and weight formulas
  are treated separately. See `LiesenStrakos.Chapter03.theorem_3_2_8`.
* **Theorem 3.4.6** (correction). A rational two-node Gauss rule can have an irrational Jacobi
  subdiagonal. The positive-arithmetic claim must allow square roots of the computed squared
  subdiagonals. See `LiesenStrakos.Chapter03.theorem_3_4_6_irrational_offDiagonal`.
* **Proposition 3.4.8** (generalization). The weighted average holds for real orthogonal
  diagonalizations of any matrix and its leading block. See
  `LiesenStrakos.Chapter03.proposition_3_4_8`.
* **Definition 3.4.10** (reading). The distance inequality is the criterion for stabilisation.
  See `LiesenStrakos.Chapter03.IsStabilisedJacobiEigenvalue`.
* **Theorem 3.7.2** (generalization). The moment identity needs only the normalization and
  the oblique Krylov projection hypotheses. See `LiesenStrakos.Chapter03.theorem_3_7_2`.
* **Lemma 4.2.9** (generalization). The summands may be zero.
  See `LiesenStrakos.lemma_4_2_9`.
* **Corollary 4.2.10** (generalization). The zero space admits the empty cyclic decomposition. See
  `LiesenStrakos.corollary_4_2_10`.
* **Remark 4.3.2** (correction). Full rank on the column space requires an invertible
  companion matrix. See `LiesenStrakos.remark_4_3_2`.
* **Sections 4.3–4.4** (generalization). The recurrence predicates and sufficient conditions
  apply over both the real and complex numbers.
* **Theorem 4.7.1** (reading). The unconditional result covers $s=2$ over the complex
  numbers. The general bound assumes the sharp harmonic root bound. Both statements
  deduce diagonalizability from the recurrence. See `LiesenStrakos.theorem_4_7_1_two` and
  `LiesenStrakos.theorem_4_7_1_of_harmonic_root_bound`.
* **Theorem 4.8.1(1)** (generalization). The McMillan degree depends on the interpolation data
  on the spectrum, so the statement applies to every finite-dimensional complex operator with
  the stated spectrum. See `LiesenStrakos.theorem_4_8_1_one`.
* **Theorem 4.9.1** (reading). The contour is piecewise $C^1$, and the eigenvalues are
  selected by winding indices. The same formula permits self-intersecting contours with
  the specified indices. See `LiesenStrakos.theorem_4_9_1`.
* **Theorem 5.5.1** (generalization). The interval endpoints may be any positive bounds on
  the quadratic form. See `LiesenStrakos.Chapter05.theorem_5_5_1`.
* **Theorem 5.6.3** (correction). The inverse-eigenvalue factors go outside the products
  over Ritz values. See `LiesenStrakos.Chapter05.theorem_5_6_3`.
* **Corollary 5.6.2** (generalization). The grade may be smaller than the ambient dimension.
  See `LiesenStrakos.Chapter05.corollary_5_6_2_spectral`.
* **Equation (5.6.20)** (correction). The maximum on the left uses the full spectrum, as in
  (5.6.19). The product and sum on the right use the selected eigenvalues. See
  `LiesenStrakos.Chapter05.theorem_5_6_6_certificate`.
* **Corollary 5.6.7** (generalization). The interval endpoints may be spectral bounds in an
  inner product space. See `LiesenStrakos.Chapter05.corollary_5_6_7`.
* **Theorem 5.7.4, sharpness** (generalization). The normal-matrix bound is attained for every
  step, including step zero and steps at or beyond the grade. See
  `LiesenStrakos.Chapter05.theorem_5_7_4_normal_sharp`.
* **§5.7.6** (reading). The asymptotic factor is defined by the upper limit and agrees with
  the ordinary limit when that limit exists. See
  `LiesenStrakos.Chapter05.asymptoticSetConvergenceFactor`.
* **Equation (5.8.16)** (reading). The Hegedüs scaling is stated over the reals. Over
  the complex numbers the printed numerator must be conjugated to minimize the residual.
  See `LiesenStrakos.Chapter05.hegedusScale`.

## Not formalized

**Chapter 3**

* Theorem 3.4.6 remains open for the corrected inverse Jacobi algorithm, its operation count,
  and its stability and sensitivity bounds.

**Chapter 4**

* The real necessity direction of Theorem 4.6.2 remains open.
* Theorem 4.7.1 is proved for $s=2$ over the complex numbers. The general case requires
  the sharp bound on the number of harmonic polynomial zeros.
* Theorem 4.8.1(2) remains open for the McMillan degree lower bound.

**Chapter 5**

* Equation (5.10.7) and the finite-precision analyses of CG and GMRES remain open.

Historical notes and numerical experiments are outside the mathematical coverage.
-/
