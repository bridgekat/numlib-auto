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

* **Theorem 2.5.2** (generalization). The conforming finite-element decomposition is stated
  for a Galerkin synthesis map in an energy inner product. See `LiesenStrakos.theorem_2_5_2`.
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
* **Remark 4.3.2** (correction). Full rank on the column space requires an invertible
  companion matrix. See `LiesenStrakos.remark_4_3_2`.
* **Sections 4.3–4.4** (generalization). The recurrence predicates and sufficient conditions
  apply over both the real and complex numbers.
* **Theorem 4.8.1(1)** (generalization). The McMillan degree depends on the interpolation data
  on the spectrum, so the statement applies to every finite-dimensional complex operator with
  the stated spectrum. See `LiesenStrakos.theorem_4_8_1_one`.
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
* **§5.7.6** (reading). The asymptotic factor is defined by the upper limit and agrees with
  the ordinary limit when that limit exists. See
  `LiesenStrakos.Chapter05.asymptoticSetConvergenceFactor`.

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
