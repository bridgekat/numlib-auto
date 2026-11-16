/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Subspace

/-!
# Krylov subspaces of a matrix

For a square matrix $A \in \mathbb{K}^{n \times n}$ and a vector $v \in \mathbb{K}^n$, this file
shows that the Krylov subspace $\mathcal{K}_m(A, v)$ of the linear map $v \mapsto Av$ is the span of
the vectors $A^i v$ with $0 \le i < m$, where $A^i$ is the matrix power. Every statement of a Krylov
method in matrix form meets the general definition `Krylov.subspace` through this result.

## Main results

* `Matrix.krylov_subspace_toEuclideanLin`: $\mathcal{K}_m(A, v) = \operatorname{span}\{A^i v : i <
  m\}$ for the matrix powers $A^i$.

## Implementation notes

* The result is in its own module because of the import order. The module
  `Numlib.Analysis.Matrix.ToEuclideanLin` is a candidate for Mathlib and therefore cannot depend on
  `Numlib.Krylov.Subspace`. The module `Numlib.Krylov.Subspace` cannot contain it either, because
  the Krylov modules import the matrix modules and not the other way round.
-/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Let $A \in \mathbb{K}^{n \times n}$, $v \in \mathbb{K}^n$ and $m \in \mathbb{N}$. The Krylov
subspace of the linear map of $A$ is spanned by the images of $v$ under the matrix powers:
$$\mathcal{K}_m(A, v) = \operatorname{span}\{A^i v : 0 \le i < m\}.$$

On the left, the operator is `Matrix.toEuclideanLin A` on `EuclideanSpace 𝕜 n`. On the right,
$A^i v$ is `Matrix.toEuclideanLin (A ^ i) v`, the action of the matrix power $A^i$, and not the
power of the linear map. -/
theorem krylov_subspace_toEuclideanLin (A : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n) (m : ℕ) :
    Krylov.subspace (toEuclideanLin A) v m =
      Submodule.span 𝕜 (Set.range fun i : Fin m => toEuclideanLin (A ^ (i : ℕ)) v) := by
  simp only [Krylov.subspace, toEuclideanLin_pow]

end Matrix
