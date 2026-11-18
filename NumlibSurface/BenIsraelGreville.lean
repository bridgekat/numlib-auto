/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Introduction
import NumlibSurface.BenIsraelGreville.Chapter00.Section01
import NumlibSurface.BenIsraelGreville.Chapter00.Section02
import NumlibSurface.BenIsraelGreville.Chapter00.Section03
import NumlibSurface.BenIsraelGreville.Chapter00.Section04
import NumlibSurface.BenIsraelGreville.Chapter00.Section05
import NumlibSurface.BenIsraelGreville.Chapter00.Section06
import NumlibSurface.BenIsraelGreville.Chapter00.Section07
import NumlibSurface.BenIsraelGreville.Chapter00.Section08
import NumlibSurface.BenIsraelGreville.Chapter00.Section09
import NumlibSurface.BenIsraelGreville.Chapter01.Section01
import NumlibSurface.BenIsraelGreville.Chapter01.Section02
import NumlibSurface.BenIsraelGreville.Chapter01.Section03
import NumlibSurface.BenIsraelGreville.Chapter01.Section04
import NumlibSurface.BenIsraelGreville.Chapter01.Section05
import NumlibSurface.BenIsraelGreville.Chapter01.Section06
import NumlibSurface.BenIsraelGreville.Chapter01.Section07
import NumlibSurface.BenIsraelGreville.Chapter02.Section01
import NumlibSurface.BenIsraelGreville.Chapter02.Section02
import NumlibSurface.BenIsraelGreville.Chapter02.Section03
import NumlibSurface.BenIsraelGreville.Chapter02.Section04
import NumlibSurface.BenIsraelGreville.Chapter02.Section05
import NumlibSurface.BenIsraelGreville.Chapter02.Section06
import NumlibSurface.BenIsraelGreville.Chapter02.Section07
import NumlibSurface.BenIsraelGreville.Chapter02.Section09
import NumlibSurface.BenIsraelGreville.Chapter02.Section10
import NumlibSurface.BenIsraelGreville.Chapter03.Section01
import NumlibSurface.BenIsraelGreville.Chapter03.Section02
import NumlibSurface.BenIsraelGreville.Chapter03.Section03
import NumlibSurface.BenIsraelGreville.Chapter04.Section01
import NumlibSurface.BenIsraelGreville.Chapter04.Section02
import NumlibSurface.BenIsraelGreville.Chapter04.Section03
import NumlibSurface.BenIsraelGreville.Chapter04.Section04
import NumlibSurface.BenIsraelGreville.Chapter04.Section06
import NumlibSurface.BenIsraelGreville.Chapter05.Section02
import NumlibSurface.BenIsraelGreville.Chapter05.Section03
import NumlibSurface.BenIsraelGreville.Chapter05.Section04
import NumlibSurface.BenIsraelGreville.Chapter05.Section05
import NumlibSurface.BenIsraelGreville.Chapter06.Section01
import NumlibSurface.BenIsraelGreville.Chapter06.Section02
import NumlibSurface.BenIsraelGreville.Chapter06.Section03
import NumlibSurface.BenIsraelGreville.Chapter06.Section04
import NumlibSurface.BenIsraelGreville.Chapter06.Section05
import NumlibSurface.BenIsraelGreville.Chapter06.Section06
import NumlibSurface.BenIsraelGreville.Chapter06.Section07
import NumlibSurface.BenIsraelGreville.Chapter06.Section08
import NumlibSurface.BenIsraelGreville.Chapter07.Section01
import NumlibSurface.BenIsraelGreville.Chapter07.Section02
import NumlibSurface.BenIsraelGreville.Chapter07.Section03
import NumlibSurface.BenIsraelGreville.Chapter07.Section04
import NumlibSurface.BenIsraelGreville.Chapter07.Section05
import NumlibSurface.BenIsraelGreville.Chapter07.Section06
import NumlibSurface.BenIsraelGreville.Chapter07.Section07
import NumlibSurface.BenIsraelGreville.Chapter08.Section02
import NumlibSurface.BenIsraelGreville.Chapter08.Section03
import NumlibSurface.BenIsraelGreville.Chapter08.Section04
import NumlibSurface.BenIsraelGreville.Chapter08.Section05
import NumlibSurface.BenIsraelGreville.Chapter08.Section06
import NumlibSurface.BenIsraelGreville.Chapter08.Section07
import NumlibSurface.BenIsraelGreville.Chapter08.Section08

/-!
# Ben-Israel and Greville, *Generalized Inverses: Theory and Applications*

This library follows the second edition of [benIsrael2003generalized]. It studies inverse
relations for rectangular and singular matrices, their constructions, and their roles in
solving linear systems and least-squares problems.

## Coverage

The formalized material includes scalar and vector preliminaries, elementary operations,
determinants and matrix volume, the algebra of the Penrose inverse classes, the ordinary
inverse, projectors and constrained linear systems, minimum-norm and regularized least-squares
solutions, group and Drazin inverses, and reduced normal equations.

## Contents

| Source | Module | Subject |
|---|---|---|
| Introduction | `Introduction` | Ordinary and generalized inverses, solution of linear systems |
| §0.1 | `Chapter00.Section01` | Scalars and vectors |
| §0.2 | `Chapter00.Section02` | Matrix representations, adjoints, spectra, and singular values |
| §0.3 | `Chapter00.Section03` | Elementary operations and permutations |
| §0.4 | `Chapter00.Section04` | Reduced row-echelon form and rank factorization |
| §0.5 | `Chapter00.Section05` | Determinants, Gram matrices, Schur complements, and volume |
| §0.6 | `Chapter00.Section06` | Exterior powers, compound matrices, and compound volumes |
| §0.7 | `Chapter00.Section07` | Jordan form, principal vectors, and polynomial formulas |
| §0.8 | `Chapter00.Section08` | Integral equivalence and Smith normal form |
| §0.9 | `Chapter00.Section09` | Block reducibility and the Perron–Frobenius theorem |
| §1.1 | `Chapter01.Section01` | Penrose equations |
| §1.2 | `Chapter01.Section02` | Inner inverses of prescribed rank from Hermite form |
| §1.3 | `Chapter01.Section03` | Properties of inner inverses |
| §1.4 | `Chapter01.Section04` | Reflexive inverses and the rank criterion |
| §1.5 | `Chapter01.Section05` | Gram matrices and Urquhart’s constructions |
| §1.6 | `Chapter01.Section06` | MacDuffee’s rank-factorization formula |
| §1.7 | `Chapter01.Section07` | Outer inverses with prescribed rank |
| §2.1 | `Chapter02.Section01` | Consistency and solutions of two-sided matrix equations |
| §2.2 | `Chapter02.Section02` | Characterizations by one Hermitian product |
| §2.3 | `Chapter02.Section03` | Outer inverses of fixed rank |
| §2.4 | `Chapter02.Section04` | Idempotents and oblique projectors |
| §2.5 | `Chapter02.Section05` | Primary decomposition and matrix functions |
| §2.6 | `Chapter02.Section06` | Prescribed range and null space |
| §2.7 | `Chapter02.Section07` | Orthogonal projectors |
| §2.9 | `Chapter02.Section09` | Restricted inverses |
| §2.10 | `Chapter02.Section10` | Bott–Duffin inverse |
| §3.1 | `Chapter03.Section01` | Least-squares solutions |
| §3.2 | `Chapter03.Section02` | Minimum-norm solutions |
| §3.3 | `Chapter03.Section03` | Tikhonov regularization |
| §4.1 | `Chapter04.Section01` | Spectral inverse equations |
| §4.2 | `Chapter04.Section02` | Matrix index and rank stabilization |
| §4.3 | `Chapter04.Section03` | Spectral inverse of a diagonalizable matrix |
| §4.4 | `Chapter04.Section04` | Group inverse |
| §4.6 | `Chapter04.Section06` | Drazin inverse |
| §5.2 | `Chapter05.Section02` | Rank-adapted partitions, block solves, and block inverses |
| §5.3 | `Chapter05.Section03` | Affine intersections and their orthogonal representatives |
| §5.4 | `Chapter05.Section04` | Common solutions and inverses of stacked matrices |
| §5.5 | `Chapter05.Section05` | Bordered inverses and least-squares determinants |
| §6.1 | `Chapter06.Section01` | Singular values, extrema, and conditioning |
| §6.2 | `Chapter06.Section02` | SVD, pseudoinverse, and finite expansions |
| §6.3 | `Chapter06.Section03` | Low-rank approximation, uniqueness, and total least squares |
| §6.4 | `Chapter06.Section04` | Partial isometries and canonical polar factors |
| §6.5 | `Chapter06.Section05` | Reciprocal subspaces, principal angles, and volume |
| §6.6 | `Chapter06.Section06` | Acute perturbations and pseudoinverse continuity |
| §6.7 | `Chapter06.Section07` | Rectangular spectral calculus and resolvents |
| §6.8 | `Chapter06.Section08` | Generalized and weighted singular value decompositions |
| §7.1 | `Chapter07.Section01` | Outer inverses with prescribed ranges and kernels |
| §7.2 | `Chapter07.Section02` | Inner and reflexive inverses by elimination and column updates |
| §7.3 | `Chapter07.Section03` | Inverses from rank factorizations and thin QR |
| §7.4 | `Chapter07.Section04` | Computation of prescribed outer inverses |
| §7.5 | `Chapter07.Section05` | Greville updates, column deletion, and least squares |
| §7.6 | `Chapter07.Section06` | Reduced normal equations and thin QR |
| §7.7 | `Chapter07.Section07` | Iterations for the pseudoinverse and its projections |
| §8.2 | `Chapter08.Section02` | Parallel sums, intersection projectors, and convex conjugacy |
| §8.3 | `Chapter08.Section03` | Linear statistical models, Gauss–Markov estimators, and whitening |
| §8.4 | `Chapter08.Section04` | Ridge estimation and mean squared error |
| §8.5 | `Chapter08.Section05` | Generalized Newton iterations and nonlinear least squares |
| §8.6 | `Chapter08.Section06` | Differential systems in real-rational Laplace coordinates |
| §8.7 | `Chapter08.Section07` | Markov chains, first passage, and the stationary projection |
| §8.8 | `Chapter08.Section08` | Singular difference equations and regular pencils |

## Conventions

* The chapter namespaces follow the numbering of the book. Within each chapter, names such
  as `theorem_2` and `lemma_3` inherit the printed label.
* Matrices have finite row and column index types and complex entries. Their Moore–Penrose
  inverse is `Matrix.pinv`. The book's class $A\{i,j,\dots\}$ is
  `BenIsraelGreville.Chapter01.definition_1`.

## Deviations from the source

* **Chapter 0, §2.6** (correction). The diagonal inner product identity for all complex
  vectors implies that the matrix is Hermitian.
* **Chapter 0, Equation (30)** (typo). The spectrum of $AA^H$ is indexed by the rows of $A$.
* **Chapter 0, Equation (87)** (typo). Cauchy–Binet selects columns of the left factor
  and rows of the right factor.
* **Chapter 0, Exercise 83** (correction). Integral equivalence can change the sign of a
  single entry in size $1\times 1$. The printed elementary operations preserve it.
* **Chapter 0, Theorem 5(a)** (correction). The spectral radius is positive for nonzero
  irreducible nonnegative matrices. The size-one zero matrix has spectral radius zero.
* **Chapter 1, Exercise 9** (typo). The kernel equality concerns $XA$ and $A$.
* **Chapter 1, Corollary 2** (typo). The kernel of $AA^H$ equals the kernel of $A^H$.
* **Chapter 2, Lemma 1(b)** (reading). The spectrum is contained in $\{0,1\}$.
* **Chapter 4, Lemma 1(d)** (reading). The earlier exponents in the comparison are positive.
* **Chapter 4, Theorem 8** (generalization). The block formula applies to any nonsingular
  and nilpotent diagonal blocks in a similarity decomposition.
* **Chapter 5, Exercise 6** (typo). The nonsingularity criterion uses $I_r+TS$.
* **Chapter 5, Theorem 7(b) and Corollary 5** (typos). The kernel basis is given by
  $V$. The right-hand side is indexed by the rows of $A$.
* **Chapter 7, Equation (65)** (correction). The equation in the full unitary coordinates
  also imposes consistency. The leading rows in Equation (66) give the criterion for
  least-squares solutions for every right-hand side.

## Not formalized

* The remaining results include further prescribed-rank constructions, projector characterizations,
  weighted and other extremal properties, further spectral and partitioned-matrix results,
  rectangular spectral theory, computational methods, applications, and generalized inverses
  on Hilbert spaces.
-/
