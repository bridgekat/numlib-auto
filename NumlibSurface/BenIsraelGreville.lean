/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Introduction
import NumlibSurface.BenIsraelGreville.Chapter00.Section01
import NumlibSurface.BenIsraelGreville.Chapter01.Section01
import NumlibSurface.BenIsraelGreville.Chapter01.Section02
import NumlibSurface.BenIsraelGreville.Chapter01.Section03
import NumlibSurface.BenIsraelGreville.Chapter01.Section04
import NumlibSurface.BenIsraelGreville.Chapter01.Section05
import NumlibSurface.BenIsraelGreville.Chapter01.Section06
import NumlibSurface.BenIsraelGreville.Chapter01.Section07
import NumlibSurface.BenIsraelGreville.Chapter02.Section01
import NumlibSurface.BenIsraelGreville.Chapter02.Section02
import NumlibSurface.BenIsraelGreville.Chapter03.Section01
import NumlibSurface.BenIsraelGreville.Chapter03.Section02
import NumlibSurface.BenIsraelGreville.Chapter03.Section03
import NumlibSurface.BenIsraelGreville.Chapter07.Section06

/-!
# Ben-Israel and Greville, *Generalized Inverses: Theory and Applications*

This library follows the second edition of [benIsrael2003generalized]. It studies inverse
relations for rectangular and singular matrices, their constructions, and their roles in
solving linear systems and least-squares problems.

## Coverage

The formalized material includes the algebra of the Penrose inverse classes, the ordinary
inverse and consistent linear systems, scalar and vector preliminaries, minimum-norm and
regularized least-squares solutions, and reduced normal equations.

## Contents

| Source | Module | Subject |
|---|---|---|
| Introduction | `Introduction` | Ordinary and generalized inverses, solution of linear systems |
| §0.1 | `Chapter00.Section01` | Scalars and vectors |
| §1.1 | `Chapter01.Section01` | Penrose equations |
| §1.2 | `Chapter01.Section02` | Inner inverse construction from Hermite form |
| §1.3 | `Chapter01.Section03` | Properties of inner inverses |
| §1.4 | `Chapter01.Section04` | Reflexive inverses and the rank criterion |
| §1.5 | `Chapter01.Section05` | Gram matrices and Urquhart’s constructions |
| §1.6 | `Chapter01.Section06` | MacDuffee’s rank-factorization formula |
| §1.7 | `Chapter01.Section07` | Outer inverses with prescribed rank |
| §2.1 | `Chapter02.Section01` | Consistency and solutions of two-sided matrix equations |
| §2.2 | `Chapter02.Section02` | Characterizations by one Hermitian product |
| §3.1 | `Chapter03.Section01` | Least-squares solutions |
| §3.2 | `Chapter03.Section02` | Minimum-norm solutions |
| §3.3 | `Chapter03.Section03` | Tikhonov regularization |
| §7.6 | `Chapter07.Section06` | Reduced normal equations and thin QR |

## Conventions

* The chapter namespaces follow the numbering of the book. Within each chapter, names such
  as `theorem_2` and `lemma_3` inherit the printed label.
* Matrices have finite row and column index types and complex entries. Their Moore–Penrose
  inverse is `Matrix.pinv`. The book's class $A\{i,j,\dots\}$ is
  `BenIsraelGreville.Chapter01.definition_1`.

## Deviations from the source

* **Chapter 1, Corollary 2** (typo). The kernel of $AA^H$ equals the kernel of $A^H$.
* **Chapter 7, Equation (65)** (correction). The equation in the full unitary coordinates
  also imposes consistency. The leading rows in Equation (66) give the criterion for
  least-squares solutions for every right-hand side.

## Not formalized

* The remaining results include prescribed-rank constructions, projector characterizations,
  extremal properties, spectral inverses, partitioned matrices, rectangular spectral theory,
  computational methods, applications, and generalized inverses on Hilbert spaces.
-/
